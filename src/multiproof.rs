// We get given multiple polynomials evaluated at different points
#![allow(non_snake_case)]

use std::collections::HashMap;

use crate::ipa::{self, IPAProof};
use crate::lagrange_basis::{LagrangeBasis, PrecomputedWeights};
use crate::math_utils::inner_product;
use crate::math_utils::powers_of;
use crate::slow_vartime_multiscalar_mul;
use crate::transcript::Transcript;
use crate::transcript::TranscriptProtocol;
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::PrimeField;
use ark_ff::{batch_inversion, Field};
use ark_ff::{One, Zero};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{Polynomial, UVPolynomial};
use bandersnatch::multi_scalar_mul;
use bandersnatch::EdwardsAffine;
use bandersnatch::EdwardsProjective;
use bandersnatch::Fr;
#[derive(Clone)]
pub struct CRS {
    pub n: usize,
    pub G: Vec<EdwardsProjective>,
    pub Q: EdwardsProjective,
}

impl CRS {
    pub fn new(n: usize, seed: &'static [u8]) -> CRS {
        let G: Vec<_> = generate_random_elements(n, seed)
            .into_iter()
            .map(|affine_point| affine_point.into_projective())
            .collect();
        let Q = EdwardsProjective::prime_subgroup_generator();
        CRS { n, G, Q }
    }

    pub fn commit_lagrange_poly(&self, polynomial: &LagrangeBasis) -> EdwardsProjective {
        slow_vartime_multiscalar_mul(polynomial.values().iter(), self.G.iter())
    }
}

fn generate_random_elements(num_required_points: usize, seed: &'static [u8]) -> Vec<EdwardsAffine> {
    use bandersnatch::Fq;
    use sha2::{Digest, Sha256};

    let mut hasher = Sha256::new();

    hasher.update(seed);
    let bytes = hasher.finalize().to_vec();

    let u = bandersnatch::Fq::from_be_bytes_mod_order(&bytes);
    let choose_largest = false;

    (0..)
        .into_iter()
        .map(|i| Fq::from(i as u128) + u)
        .map(|x| EdwardsAffine::get_point_from_x(x, choose_largest))
        .filter_map(|point| point)
        .filter(|point| point.is_in_correct_subgroup_assuming_on_curve())
        .take(num_required_points)
        .collect()
}

pub struct MultiPoint;

#[derive(Clone, Debug)]
pub struct ProverQuery {
    pub comm: EdwardsProjective,
    pub poly: LagrangeBasis,
    // Given a function f, we use z_i to denote the input point and y_i to denote the output, ie f(z_i) = y_i
    pub z_i: usize,
    pub y_i: Fr,
}

impl From<ProverQuery> for VerifierQuery {
    fn from(pq: ProverQuery) -> Self {
        VerifierQuery {
            comm: pq.comm,
            z_i: Fr::from(pq.z_i as u128),
            y_i: pq.y_i,
        }
    }
}
pub struct VerifierQuery {
    comm: EdwardsProjective,
    z_i: Fr,
    y_i: Fr,
}

//XXX: change to group_prover_queries_by_point
fn group_prover_queries<'a>(
    prover_queries: &'a [ProverQuery],
    challenges: &'a [Fr],
) -> HashMap<usize, Vec<(&'a ProverQuery, &'a Fr)>> {
    // We want to group all of the polynomials which are evaluated at the same point together
    use itertools::Itertools;
    prover_queries
        .iter()
        .zip(challenges.iter())
        .into_group_map_by(|x| x.0.z_i)
}

impl MultiPoint {
    pub fn open(
        crs: CRS,
        precomp: &PrecomputedWeights,
        transcript: &mut Transcript,
        queries: Vec<ProverQuery>,
    ) -> MultiPointProof {
        transcript.domain_sep(b"multiproof");
        // 1. Compute `r`
        //
        // Add points and evaluations
        for query in queries.iter() {
            transcript.append_point(b"C", &query.comm);
            transcript.append_scalar(b"z", &Fr::from(query.z_i as u128));
            // XXX: note that since we are always opening on the domain
            // the prover does not need to pass y_i explicitly
            // It's just an index operation on the lagrange basis
            transcript.append_scalar(b"y", &query.y_i)
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
        //
        let g_x: LagrangeBasis = aggregated_queries
            .iter()
            .map(|(point, agg_f_x)| (agg_f_x).divide_by_linear_vanishing(precomp, *point))
            .fold(LagrangeBasis::zero(), |mut res, val| {
                res = res + val;
                res
            });

        let g_x_comm = crs.commit_lagrange_poly(&g_x);
        transcript.append_point(b"D", &g_x_comm);

        // 2. Compute g_1(t)
        //
        //
        let t = transcript.challenge_scalar(b"t");
        //
        //

        let mut g1_den: Vec<_> = aggregated_queries
            .iter()
            .map(|(z_i, _)| t - Fr::from(*z_i as u128))
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

        let g1_comm = crs.commit_lagrange_poly(&g1_x);
        transcript.append_point(b"E", &g1_comm);

        //3. Compute g_1(X) - g(X)
        // This is the polynomial, we will create an opening for
        let g_3_x = &g1_x - &g_x;
        let g_3_x_comm = g1_comm - g_x_comm;

        // 4. Compute the IPA for g_3
        let g_3_ipa = open_point_outside_of_domain(crs, precomp, transcript, g_3_x, g_3_x_comm, t);

        MultiPointProof {
            open_proof: g_3_ipa,
            g_x_comm: g_x_comm,
        }
    }
}

pub struct MultiPointProof {
    open_proof: IPAProof,
    g_x_comm: EdwardsProjective,
}

impl MultiPointProof {
    pub fn check(
        &self,
        crs: &CRS,
        precomp: &PrecomputedWeights,
        queries: &[VerifierQuery],
        transcript: &mut Transcript,
    ) -> bool {
        transcript.domain_sep(b"multiproof");
        // 1. Compute `r`
        //
        // Add points and evaluations
        for query in queries.iter() {
            transcript.append_point(b"C", &query.comm);
            transcript.append_scalar(b"z", &query.z_i);
            transcript.append_scalar(b"y", &query.y_i);
        }

        let r = transcript.challenge_scalar(b"r");
        let powers_of_r = powers_of(r, queries.len());

        // 2. Compute `t`
        transcript.append_point(b"D", &self.g_x_comm);
        let t = transcript.challenge_scalar(b"t");

        // 3. Compute g_2(t)
        //
        let mut g2_den: Vec<_> = queries.iter().map(|query| t - query.z_i).collect();
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

        transcript.append_point(b"E", &g1_comm);

        // E - D
        let g3_comm = g1_comm - self.g_x_comm;

        // Check IPA
        let b = LagrangeBasis::evaluate_lagrange_coefficients(&precomp, crs.n, t); // TODO: we could put this as a method on PrecomputedWeights

        self.open_proof
            .verify_multiexp(transcript, crs, b, g3_comm, t, g2_t)
    }
}

// TODO: we could probably get rid of this method altogether and just do this in the multiproof
// TODO method
pub(crate) fn open_point_outside_of_domain(
    crs: CRS,
    precomp: &PrecomputedWeights,
    transcript: &mut Transcript,
    polynomial: LagrangeBasis,
    commitment: EdwardsProjective,
    z_i: Fr,
) -> IPAProof {
    let a = polynomial.values().to_vec();
    let b = LagrangeBasis::evaluate_lagrange_coefficients(precomp, crs.n, z_i);
    crate::ipa::create(transcript, crs, a, commitment, b, z_i)
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

    let crs = CRS::new(n, b"random seed");
    let poly_comm = crs.commit_lagrange_poly(&poly);

    let prover_query = ProverQuery {
        comm: poly_comm,
        poly: poly,
        z_i: point,
        y_i,
    };

    let precomp = PrecomputedWeights::new(n);

    let mut transcript = Transcript::new(b"foo");
    let multiproof = MultiPoint::open(
        crs.clone(),
        &precomp,
        &mut transcript,
        vec![prover_query.clone()],
    );

    let mut transcript = Transcript::new(b"foo");
    let verifier_query: VerifierQuery = prover_query.into();
    assert!(multiproof.check(&crs, &precomp, &[verifier_query], &mut transcript));
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

    let z_i = 1;
    let y_i = poly.evaluate_in_domain(z_i);
    let x_j = 2;
    let y_j = poly.evaluate_in_domain(x_j);

    let crs = CRS::new(n, b"random seed");
    let poly_comm = crs.commit_lagrange_poly(&poly);

    let prover_query_i = ProverQuery {
        comm: poly_comm,
        poly: poly.clone(),
        z_i: z_i,
        y_i: y_i,
    };
    let prover_query_j = ProverQuery {
        comm: poly_comm,
        poly: poly,
        z_i: x_j,
        y_i: y_j,
    };

    let precomp = PrecomputedWeights::new(n);

    let mut transcript = Transcript::new(b"foo");
    let multiproof = MultiPoint::open(
        crs.clone(),
        &precomp,
        &mut transcript,
        vec![prover_query_i.clone(), prover_query_j.clone()],
    );

    let mut transcript = Transcript::new(b"foo");
    let verifier_query_i: VerifierQuery = prover_query_i.into();
    let verifier_query_j: VerifierQuery = prover_query_j.into();
    assert!(multiproof.check(
        &crs,
        &precomp,
        &[verifier_query_i, verifier_query_j],
        &mut transcript,
    ));
}
#[test]
fn test_ipa_consistency() {
    use ark_serialize::CanonicalSerialize;
    let n = 256;
    let crs = CRS::new(n, b"eth_verkle_oct_2021");
    let precomp = PrecomputedWeights::new(n);
    let input_point = Fr::from(2101 as u128);

    let poly: Vec<Fr> = (0..n).map(|i| Fr::from(((i % 32) + 1) as u128)).collect();
    let polynomial = LagrangeBasis::new(poly.clone());
    let commitment = crs.commit_lagrange_poly(&polynomial);
    let mut prover_transcript = Transcript::new(b"test");

    let proof = open_point_outside_of_domain(
        crs.clone(),
        &precomp,
        &mut prover_transcript,
        polynomial,
        commitment,
        input_point,
    );

    let p_challenge = prover_transcript.challenge_scalar(b"state");
    let mut bytes = [0u8; 32];
    p_challenge.serialize(&mut bytes[..]).unwrap();
    assert_eq!(
        hex::encode(&bytes),
        "50d7f61175ffcfefc0dd603943ec8da7568608564d509cd0d1fa71cc48dc3515"
    );

    let mut verifier_transcript = Transcript::new(b"test");
    let b = LagrangeBasis::evaluate_lagrange_coefficients(&precomp, crs.n, input_point);
    let output_point = inner_product(&poly, &b);
    assert!(proof.verify_multiexp(
        &mut verifier_transcript,
        &crs,
        b,
        commitment,
        input_point,
        output_point,
    ));

    let v_challenge = verifier_transcript.challenge_scalar(b"state");
    assert_eq!(p_challenge, v_challenge)
}

#[test]
fn multiproof_consistency() {
    use ark_serialize::CanonicalSerialize;
    let n = 256;
    let crs = CRS::new(n, b"eth_verkle_oct_2021");
    let precomp = PrecomputedWeights::new(n);

    // 1 to 32 repeated 8 times
    let poly_a: Vec<Fr> = (0..n).map(|i| Fr::from(((i % 32) + 1) as u128)).collect();
    let polynomial_a = LagrangeBasis::new(poly_a.clone());
    // 32 to 1 repeated 8 times
    let poly_b: Vec<Fr> = (0..n)
        .rev()
        .map(|i| Fr::from(((i % 32) + 1) as u128))
        .collect();
    let polynomial_b = LagrangeBasis::new(poly_b.clone());

    let point_a = 0;
    let y_a = Fr::one();

    let point_b = 0;
    let y_b = Fr::from(32 as u128);

    let poly_comm_a = crs.commit_lagrange_poly(&polynomial_a);
    let poly_comm_b = crs.commit_lagrange_poly(&polynomial_b);

    let prover_query_a = ProverQuery {
        comm: poly_comm_a,
        poly: polynomial_a,
        z_i: point_a,
        y_i: y_a,
    };
    let prover_query_b = ProverQuery {
        comm: poly_comm_b,
        poly: polynomial_b,
        z_i: point_b,
        y_i: y_b,
    };

    let mut prover_transcript = Transcript::new(b"test");
    let multiproof = MultiPoint::open(
        crs.clone(),
        &precomp,
        &mut prover_transcript,
        vec![prover_query_a.clone(), prover_query_b.clone()],
    );

    let p_challenge = prover_transcript.challenge_scalar(b"state");
    let mut bytes = [0u8; 32];
    p_challenge.serialize(&mut bytes[..]).unwrap();
    assert_eq!(
        hex::encode(&bytes),
        "f9c48313d1af5e069386805b966ce53a3d95794b82da3aac6d68fd629062a31c"
    );

    let mut verifier_transcript = Transcript::new(b"test");
    let verifier_query_a: VerifierQuery = prover_query_a.into();
    let verifier_query_b: VerifierQuery = prover_query_b.into();
    assert!(multiproof.check(
        &crs,
        &precomp,
        &[verifier_query_a, verifier_query_b],
        &mut verifier_transcript
    ));
}

#[test]
fn crs_consistency() {
    // See: https://hackmd.io/1RcGSMQgT4uREaq1CCx_cg#Methodology
    use ark_serialize::CanonicalSerialize;
    use bandersnatch::Fq;
    use sha2::{Digest, Sha256};

    let points = generate_random_elements(256, b"eth_verkle_oct_2021");
    for point in &points {
        let on_curve = point.is_on_curve();
        let in_correct_subgroup = point.is_in_correct_subgroup_assuming_on_curve();
        if !on_curve {
            panic!("generated a point which is not on the curve")
        }
        if !in_correct_subgroup {
            panic!("generated a point which is not in the prime subgroup")
        }
    }

    let mut bytes = [0u8; 32];
    points[0].serialize(&mut bytes[..]).unwrap();
    assert_eq!(
        hex::encode(&bytes),
        "22ac968a98ab6c50379fc8b039abc8fd9aca259f4746a05bfbdf12c86463c208",
        "the first point is incorrect"
    );
    let mut bytes = [0u8; 32];
    points[255].serialize(&mut bytes[..]).unwrap();
    assert_eq!(
        hex::encode(&bytes),
        "c8b4968a98ab6c50379fc8b039abc8fd9aca259f4746a05bfbdf12c86463c208",
        "the 256th (last) point is incorrect"
    );

    let mut hasher = Sha256::new();
    for point in &points {
        let mut bytes = [0u8; 32];
        point.serialize(&mut bytes[..]).unwrap();
        hasher.update(&bytes);
    }
    let bytes = hasher.finalize().to_vec();
    assert_eq!(
        hex::encode(&bytes),
        "c390cbb4bc42019685d5a01b2fb8a536d4332ea4e128934d0ae7644163089e76",
        "unexpected point encountered"
    );
}
