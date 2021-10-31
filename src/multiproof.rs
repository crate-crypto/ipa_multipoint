// We get given multiple polynomials evaluated at different points
#![allow(non_snake_case)]

use std::collections::HashMap;

use crate::ipa::{self, NoZK};
use crate::lagrange_basis::{LagrangeBasis, PrecomputedWeights};
use crate::math_utils::inner_product;
use crate::math_utils::powers_of;
use crate::slow_vartime_multiscalar_mul;
use crate::transcript::TranscriptProtocol;
use ark_ec::ProjectiveCurve;
use ark_ff::PrimeField;
use ark_ff::{batch_inversion, Field};
use ark_ff::{One, Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{Polynomial, UVPolynomial};
use bandersnatch::multi_scalar_mul;
use bandersnatch::EdwardsAffine;
use bandersnatch::EdwardsProjective;
use bandersnatch::Fr;
use merlin::Transcript;
pub struct CRS {
    n: usize,
    G: Vec<EdwardsProjective>,
    Q: EdwardsProjective,
}

impl CRS {
    pub fn new(n: usize) -> CRS {
        use ark_std::rand::SeedableRng;
        use ark_std::UniformRand;
        use rand_chacha::ChaCha20Rng;

        let mut rng = ChaCha20Rng::from_seed([0u8; 32]);

        let G: Vec<EdwardsProjective> = (0..n).map(|_| EdwardsProjective::rand(&mut rng)).collect();

        let Q = EdwardsProjective::rand(&mut rng);

        CRS { n, G, Q }
    }

    pub fn commit_lagrange_poly(&self, polynomial: &LagrangeBasis) -> EdwardsProjective {
        slow_vartime_multiscalar_mul(polynomial.values().iter(), self.G.iter())
    }
}

pub struct MultiOpen;

#[derive(Clone, Debug)]
pub struct ProverQueryLagrange {
    pub comm: EdwardsProjective,
    pub poly: LagrangeBasis,
    // x_i is z_i in the hackmd. Maybe change the hackmd as f(x_i) = y_i is more intuitive
    pub x_i: usize,
    pub y_i: Fr,
}

impl From<ProverQueryLagrange> for VerifierQuery {
    fn from(pq: ProverQueryLagrange) -> Self {
        VerifierQuery {
            comm: pq.comm,
            x_i: Fr::from(pq.x_i as u128),
            y_i: pq.y_i,
        }
    }
}
pub struct VerifierQuery {
    comm: EdwardsProjective,
    // x_i is z_i in the hackmd. Maybe change the hackmd as f(x_i) = y_i is more intuitive
    x_i: Fr,
    y_i: Fr,
}

fn group_prover_queries<'a>(
    prover_queries: &'a [ProverQueryLagrange],
    challenges: &'a [Fr],
) -> HashMap<usize, Vec<(&'a ProverQueryLagrange, &'a Fr)>> {
    // We want to group all of the polynomials which are evaluated at the same point together
    use itertools::Itertools;
    prover_queries
        .iter()
        .zip(challenges.iter())
        .into_group_map_by(|x| x.0.x_i)
}

impl MultiOpen {
    pub fn open_multiple_lagrange(
        crs: &CRS,
        precomp: &PrecomputedWeights,
        transcript: &mut Transcript,
        queries: Vec<ProverQueryLagrange>,
    ) -> MultiOpenProof {
        // 1. Compute `r`
        //
        // Add points and evaluations
        for query in queries.iter() {
            transcript.append_point(b"C_i", &query.comm)
        }
        for query in queries.iter() {
            transcript.append_scalar(b"x_i", &Fr::from(query.x_i as u128))
        }
        // XXX: note that since we are always opening on the domain
        // the prover does not need to pass y_i explicitly
        // It's just an index operation on the lagrange basis
        for query in queries.iter() {
            transcript.append_scalar(b"y_i", &query.y_i)
        }
        let r = transcript.challenge_scalar(b"r");
        let powers_of_r = powers_of(r, queries.len());

        let grouped_queries = group_prover_queries(&queries, &powers_of_r);

        // aggregate all of the queries evaluated at the same point
        let aggregated_queries: Vec<_> = grouped_queries
            .into_iter()
            .map(|(point, queries_challenges)| {
                let mut aggregated_polynomial = vec![Fr::zero(); crs.n];

                let scaled_lagrange_polynomials =
                    queries_challenges.into_iter().map(|(query, challenge)| {
                        // scale the polynomial by the challenge
                        query.poly.values().iter().map(move |x| *x * challenge)
                    });

                for poly_mul_challenge in scaled_lagrange_polynomials {
                    for (result, scaled_poly) in
                        aggregated_polynomial.iter_mut().zip(poly_mul_challenge)
                    {
                        *result += scaled_poly;
                    }
                }

                (point, LagrangeBasis::new(aggregated_polynomial))
            })
            .collect();

        // Compute g(X)

        let g_x: LagrangeBasis = aggregated_queries
            .iter()
            .map(|(point, agg_f_x)| (agg_f_x).divide_by_linear_vanishing(precomp, *point))
            .fold(LagrangeBasis::zero(), |mut res, val| {
                res = res + val;
                res
            });

        let g_x_comm = crs.commit_lagrange_poly(&g_x);
        transcript.append_point(b"g_x", &g_x_comm);

        // 2. Compute g_1(t)
        //
        //
        let t = transcript.challenge_scalar(b"t");
        //
        //

        let mut g1_den: Vec<_> = aggregated_queries
            .iter()
            .map(|(x_i, _)| t - Fr::from(*x_i as u128))
            .collect();
        batch_inversion(&mut g1_den);

        let g1_x = aggregated_queries
            .into_iter()
            .zip(g1_den.into_iter())
            .map(|((_, agg_f_x), den_inv)| {
                let term: Vec<_> = agg_f_x
                    .values()
                    .iter()
                    .map(|coeff| den_inv * coeff)
                    .collect();

                LagrangeBasis::new(term)
            })
            .fold(LagrangeBasis::zero(), |mut res, val| {
                res = res + val;
                res
            });

        let g1_t = g1_x.evaluate_outside_domain(precomp, t);

        let g1_comm = crs.commit_lagrange_poly(&g1_x);
        transcript.append_point(b"g1_x", &g1_comm);

        //3. Compute g_1(X) - g(X)
        // This is the polynomial, we will create an opening for
        let g_3_x = &g1_x - &g_x;
        let g_3_x_comm = g1_comm - g_x_comm;

        // 4. Compute the IPAs

        let g_3_ipa = MultiOpen::open_single_lagrange_out_of_domain(
            crs, precomp, transcript, g_3_x, g_3_x_comm, t,
        );
        MultiOpenProof {
            open_proof: g_3_ipa,
            g_x_comm: g_x_comm,
        }
    }
}

pub struct MultiOpenProof {
    open_proof: NoZK,
    g_x_comm: EdwardsProjective,
}

impl MultiOpenProof {
    pub fn check_single_lagrange(
        &self,
        crs: &CRS,
        precomp: &PrecomputedWeights,
        queries: &[VerifierQuery],
        transcript: &mut Transcript,
        n: usize,
    ) -> bool {
        // 1. Compute `r`
        //
        // Add points and evaluations
        for query in queries.iter() {
            transcript.append_point(b"C_i", &query.comm)
        }
        for query in queries.iter() {
            transcript.append_scalar(b"x_i", &query.x_i)
        }
        for query in queries.iter() {
            transcript.append_scalar(b"y_i", &query.y_i)
        }
        let r = transcript.challenge_scalar(b"r");
        let powers_of_r = powers_of(r, queries.len());

        // 2. Compute `t`
        transcript.append_point(b"g_x", &self.g_x_comm);
        let t = transcript.challenge_scalar(b"t");

        // 3. Compute g_2(t)
        //
        let mut g2_den: Vec<_> = queries.iter().map(|query| t - query.x_i).collect();
        batch_inversion(&mut g2_den);

        let helper_scalars: Vec<_> = powers_of_r
            .iter()
            .zip(g2_den.into_iter())
            .map(|(r_i, den_inv)| den_inv * r_i)
            .collect();

        let g2_t: Fr = helper_scalars
            .iter()
            .zip(queries.iter())
            .map(|(r_i_den_inv, query)| *r_i_den_inv * query.y_i)
            .sum();

        //4. Compute [g_1(X)] = E
        let comms: Vec<_> = queries.into_iter().map(|query| query.comm).collect();
        let g1_comm = slow_vartime_multiscalar_mul(helper_scalars.iter(), comms.iter());

        transcript.append_point(b"g1_x", &g1_comm);

        // E - D
        let g3_comm = g1_comm - self.g_x_comm;

        // Check IPA
        let b = LagrangeBasis::evaluate_lagrange_coefficients(&precomp, crs.n, t);

        self.open_proof
            .verify(transcript, &crs.G, &crs.Q, crs.n, b, g3_comm, t, g2_t)
    }
}

// TODO: we could probably get rid of this method altogether and just do this in the multiproof
// TODO method
impl MultiOpen {
    pub fn open_single_lagrange_out_of_domain(
        crs: &CRS,
        precomp: &PrecomputedWeights,
        transcript: &mut Transcript,
        polynomial: LagrangeBasis,
        commitment: EdwardsProjective,
        x_i: Fr,
    ) -> NoZK {
        let a = polynomial.values().to_vec();
        let b = LagrangeBasis::evaluate_lagrange_coefficients(precomp, crs.n, x_i);
        crate::ipa::create(transcript, crs.G.clone(), &crs.Q, a, commitment, b, x_i)
    }
}

#[test]
fn open_multiproof_lagrange() {
    let poly = LagrangeBasis::new(vec![
        Fr::one(),
        Fr::from(10u128),
        Fr::from(200u128),
        Fr::from(78u128),
    ]);
    let n = poly.values().len();

    let point = 1;
    let y_i = poly.evaluate_in_domain(point);

    let crs = CRS::new(n);
    let poly_comm = crs.commit_lagrange_poly(&poly);

    let prover_query = ProverQueryLagrange {
        comm: poly_comm,
        poly: poly,
        x_i: point,
        y_i,
    };

    let precomp = PrecomputedWeights::new(n);

    let mut transcript = Transcript::new(b"foo");
    let multiproof = MultiOpen::open_multiple_lagrange(
        &crs,
        &precomp,
        &mut transcript,
        vec![prover_query.clone()],
    );

    let mut transcript = Transcript::new(b"foo");
    let verifier_query: VerifierQuery = prover_query.into();
    assert!(multiproof.check_single_lagrange(
        &crs,
        &precomp,
        &[verifier_query],
        &mut transcript,
        n
    ));
}

#[test]
fn open_multiproof_lagrange_2_polys() {
    let poly = LagrangeBasis::new(vec![
        Fr::one(),
        Fr::from(10u128),
        Fr::from(200u128),
        Fr::from(78u128),
    ]);
    let n = poly.values().len();

    let x_i = 1;
    let y_i = poly.evaluate_in_domain(x_i);
    let x_j = 2;
    let y_j = poly.evaluate_in_domain(x_j);

    let crs = CRS::new(n);
    let poly_comm = crs.commit_lagrange_poly(&poly);

    let prover_query_i = ProverQueryLagrange {
        comm: poly_comm,
        poly: poly.clone(),
        x_i: x_i,
        y_i: y_i,
    };
    let prover_query_j = ProverQueryLagrange {
        comm: poly_comm,
        poly: poly,
        x_i: x_j,
        y_i: y_j,
    };

    let precomp = PrecomputedWeights::new(n);

    let mut transcript = Transcript::new(b"foo");
    let multiproof = MultiOpen::open_multiple_lagrange(
        &crs,
        &precomp,
        &mut transcript,
        vec![prover_query_i.clone(), prover_query_j.clone()],
    );

    let mut transcript = Transcript::new(b"foo");
    let verifier_query_i: VerifierQuery = prover_query_i.into();
    let verifier_query_j: VerifierQuery = prover_query_j.into();
    assert!(multiproof.check_single_lagrange(
        &crs,
        &precomp,
        &[verifier_query_i, verifier_query_j],
        &mut transcript,
        n
    ));
}
