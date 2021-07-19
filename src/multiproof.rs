// We get given multiple polynomials evaluated at different points
#![allow(non_snake_case)]

use crate::ipa::{self, NoZK};
use crate::lagrange_basis::{LagrangeBasis, PrecomputedWeights};
use crate::math_utils::inner_product;
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
use bandersnatch::EdwardsParameters;
use bandersnatch::EdwardsProjective;
use bandersnatch::Fr;
use merlin::Transcript;
use sha3::Sha3_512;

struct CRS {
    n: usize,
    G: Vec<EdwardsProjective>,
    H: Vec<EdwardsProjective>,
    Q: EdwardsProjective,
}

impl CRS {
    pub fn new(n: usize) -> CRS {
        let G: Vec<EdwardsProjective> = (0..n)
            .map(|_| EdwardsProjective::prime_subgroup_generator())
            .collect();
        let H: Vec<EdwardsProjective> = (0..n)
            .map(|_| EdwardsProjective::prime_subgroup_generator())
            .collect();
        let Q = EdwardsProjective::prime_subgroup_generator();

        CRS { n, G, H, Q }
    }

    pub fn commit_poly(&self, polynomial: &DensePolynomial<Fr>) -> EdwardsProjective {
        slow_vartime_multiscalar_mul(polynomial.coeffs.iter(), self.G.iter())
    }
    pub fn commit_lagrange_poly(&self, polynomial: &LagrangeBasis) -> EdwardsProjective {
        slow_vartime_multiscalar_mul(polynomial.values().iter(), self.G.iter())
    }

    // Convert C = <a, G> into C' = <a, G> + <b, H> + <a, b>Q
    pub fn augment_commitment(
        &self,
        comm: EdwardsProjective,
        b: Vec<Fr>,
        inner_prod: Fr,
    ) -> EdwardsProjective {
        slow_vartime_multiscalar_mul(
            b.iter().chain(std::iter::once(&inner_prod)),
            self.H.iter().chain(std::iter::once(&self.Q)),
        ) + comm
    }
}

/// Divides a [`Polynomial`] by x-z using Ruffinis method.
pub fn ruffini(polynomial: &DensePolynomial<Fr>, z: &Fr) -> DensePolynomial<Fr> {
    let mut quotient: Vec<Fr> = Vec::with_capacity(polynomial.degree());
    let mut k = Fr::zero();

    // Reverse the results and use Ruffini's method to compute the quotient
    // The coefficients must be reversed as Ruffini's method
    // starts with the leading coefficient, while Polynomials
    // are stored in increasing order i.e. the leading coefficient is the
    // last element
    for coeff in polynomial.coeffs.iter().rev() {
        let t = k + coeff;
        quotient.push(t);
        k = t * z;
    }

    // Pop off the last element, it is the remainder term
    // we expect there to be no remainder
    quotient.pop();

    // Reverse the results for storage in the Polynomial struct
    quotient.reverse();
    DensePolynomial::from_coefficients_vec(quotient)
}
struct MultiOpen;

#[derive(Clone, Debug)]
struct ProverQuery {
    comm: EdwardsProjective,
    poly: DensePolynomial<Fr>,
    // x_i is z_i in the hackmd. Maybe change the hackmd as f(x_i) = y_i is more intuitive
    x_i: Fr,
    y_i: Fr,
}

#[derive(Clone, Debug)]
struct ProverQueryLagrange {
    comm: EdwardsProjective,
    poly: LagrangeBasis,
    // x_i is z_i in the hackmd. Maybe change the hackmd as f(x_i) = y_i is more intuitive
    x_i: usize,
    y_i: Fr,
}

impl From<ProverQuery> for VerifierQuery {
    fn from(pq: ProverQuery) -> Self {
        VerifierQuery {
            comm: pq.comm,
            x_i: pq.x_i,
            y_i: pq.y_i,
        }
    }
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
struct VerifierQuery {
    comm: EdwardsProjective,
    // x_i is z_i in the hackmd. Maybe change the hackmd as f(x_i) = y_i is more intuitive
    x_i: Fr,
    y_i: Fr,
}

impl MultiOpen {
    pub fn open_multiple(
        crs: &CRS,
        transcript: &mut Transcript,
        queries: Vec<ProverQuery>,
    ) -> MultiOpenProof {
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

        // Compute g(X)
        let mut g_x: DensePolynomial<Fr> = powers_of_r
            .iter()
            .zip(queries.iter())
            .map(|(r_i, query)| {
                let f_x = &query.poly;
                // We apply an optimisation only available for monomial basis
                // f(x) - y / X - z gives the same quotient as f(x) / X - z
                // This means we can drop the `y`
                let _y = &query.y_i;
                let x = &query.x_i;

                // XXX(arkworks) : WE cannot make r_i a poly and mul to quotient
                // because the field is not FFT friendly
                // panics on registry/src/github.com-1ecc6299db9ec823/ark-poly-0.3.0/src/domain/radix2/mod.rs:69:9
                let mut quotient = ruffini(f_x, x);
                for q in quotient.coeffs.iter_mut() {
                    *q *= r_i;
                }
                quotient
            })
            .fold(DensePolynomial::zero(), |mut res, val| {
                res += &val;
                res
            });

        let g_x_comm = crs.commit_poly(&g_x);
        transcript.append_point(b"g_x", &g_x_comm);

        // 2. Compute g_1(t)
        //
        //
        let t = transcript.challenge_scalar(b"t");
        //
        //
        let mut g1_den: Vec<_> = queries.iter().map(|query| t - query.x_i).collect();
        batch_inversion(&mut g1_den);

        let g1_x = powers_of_r
            .into_iter()
            .zip(queries.iter())
            .zip(g1_den.into_iter())
            .map(|((r_i, query), den_inv)| {
                let f_x = &query.poly;

                let term: Vec<_> = f_x.iter().map(|coeff| r_i * coeff * den_inv).collect();

                DensePolynomial::from_coefficients_vec(term)
            })
            .fold(DensePolynomial::zero(), |mut res, val| {
                res += &val;
                res
            });

        let g1_t = g1_x.evaluate(&t);

        let g1_comm = crs.commit_poly(&g1_x);
        transcript.append_point(b"g1_x", &g1_comm);

        // 3. Compute the IPAs

        let q = transcript.challenge_scalar(b"q");

        for term in g_x.iter_mut() {
            *term *= q;
        }
        let g_3_x = g1_x + g_x;
        let g_3_ipa = MultiOpen::open_single(crs, transcript, g_3_x, t);
        MultiOpenProof {
            open_proof: g_3_ipa,
            g_1_eval: g1_t,
            g_x_comm: g_x_comm,
        }
    }
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
        for query in queries.iter() {
            transcript.append_scalar(b"y_i", &query.y_i)
        }
        let r = transcript.challenge_scalar(b"r");
        let powers_of_r = powers_of(r, queries.len());

        // Compute g(X)
        let g_x: LagrangeBasis = powers_of_r
            .iter()
            .zip(queries.iter())
            .map(|(r_i, query)| {
                let f_x = &query.poly;
                // We apply an optimisation only available for monomial basis
                // f(x) - y / X - z gives the same quotient as f(x) / X - z
                // This means we can drop the `y`
                let _y = &query.y_i;
                let x = &query.x_i;

                (f_x.clone() - _y).divide_by_linear_vanishing(precomp, *x) * *r_i
            })
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
        let mut g1_den: Vec<_> = queries
            .iter()
            .map(|query| t - Fr::from(query.x_i as u128))
            .collect();
        batch_inversion(&mut g1_den);

        let g1_x = powers_of_r
            .into_iter()
            .zip(queries.iter())
            .zip(g1_den.into_iter())
            .map(|((r_i, query), den_inv)| {
                let f_x = &query.poly;

                let term: Vec<_> = f_x
                    .values()
                    .iter()
                    .map(|coeff| r_i * coeff * den_inv)
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

        // 3. Compute the IPAs

        dbg!(g_x.evaluate_outside_domain(precomp, t));

        let q = transcript.challenge_scalar(b"q");

        let g_3_x = g1_x + (g_x * q);

        let g_3_ipa =
            MultiOpen::open_single_lagrange_out_of_domain(crs, precomp, transcript, g_3_x, t);
        MultiOpenProof {
            open_proof: g_3_ipa,
            g_1_eval: g1_t,
            g_x_comm: g_x_comm,
        }
    }
}

struct MultiOpenProof {
    open_proof: OpeningProof,

    g_1_eval: Fr,

    g_x_comm: EdwardsProjective,
}

impl MultiOpenProof {
    pub fn check_single(
        self,
        crs: &CRS,
        queries: Vec<VerifierQuery>,
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

        //4. Compute g(t)
        let g_t = self.g_1_eval - g2_t;

        //5. Compute [g_1(X)]
        let g1_comm: EdwardsProjective = helper_scalars
            .into_iter()
            .zip(queries)
            .map(|(r_i_den_inv, query)| query.comm.mul(r_i_den_inv.into_repr()))
            .sum();

        transcript.append_point(b"g1_x", &g1_comm);

        let q = transcript.challenge_scalar(b"q");

        let g3_t = self.g_1_eval + q * g_t;
        let g3_comm = g1_comm + self.g_x_comm.mul(q.into_repr());

        // augment g3_comm
        let g3_augmented = crs.augment_commitment(g3_comm, powers_of(t, crs.n), g3_t);

        assert_eq!(g3_augmented, self.open_proof.P);

        self.open_proof.check_single(crs, transcript, n)
    }
    pub fn check_single_lagrange(
        self,
        crs: &CRS,
        precomp: &PrecomputedWeights,
        queries: Vec<VerifierQuery>,
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

        //4. Compute g(t)
        let g_t = self.g_1_eval - g2_t;

        //5. Compute [g_1(X)]
        let g1_comm: EdwardsProjective = helper_scalars
            .into_iter()
            .zip(queries)
            .map(|(r_i_den_inv, query)| query.comm.mul(r_i_den_inv.into_repr()))
            .sum();

        transcript.append_point(b"g1_x", &g1_comm);

        let q = transcript.challenge_scalar(b"q");

        let g3_t = self.g_1_eval + q * g_t;
        let g3_comm = g1_comm + self.g_x_comm.mul(q.into_repr());

        // augment g3_comm
        let powers = LagrangeBasis::evaluate_lagrange_coefficients(&precomp, crs.n, t);
        let g3_augmented = crs.augment_commitment(g3_comm, powers, g3_t);

        assert_eq!(g3_augmented, self.open_proof.P);

        self.open_proof.check_single(crs, transcript, n)
    }
}

struct OpeningProof {
    // This is the commitment to the statement
    P: EdwardsProjective,

    t: Fr,

    ipa: NoZK,
}

impl OpeningProof {
    pub fn check_single(self, crs: &CRS, transcript: &mut Transcript, n: usize) -> bool {
        transcript.append_point(b"P", &self.P);

        self.ipa
            .verify(transcript, &crs.G, &crs.H, &crs.Q, n, self.P, self.t)
    }
}

impl MultiOpen {
    pub fn open_single(
        crs: &CRS,
        transcript: &mut Transcript,
        polynomial: DensePolynomial<Fr>,
        point: Fr,
    ) -> OpeningProof {
        let t = polynomial.evaluate(&point);
        let a = polynomial.coeffs;
        let b = powers_of(point, crs.n);

        let P = slow_vartime_multiscalar_mul(
            a.iter().chain(b.iter()).chain(std::iter::once(&t)),
            crs.G
                .iter()
                .chain(crs.H.iter())
                .chain(std::iter::once(&crs.Q)),
        );

        // We add the compressed point to the transcript, because we need some non-trivial input to generate alpha
        // If this is not done, then the prover always will be able to predict what the first challenge will be
        transcript.append_point(b"P", &P);

        let no_zk = ipa::create(transcript, crs.G.clone(), crs.H.clone(), &crs.Q, a, b);

        OpeningProof { P, t, ipa: no_zk }
    }
    // We assume that you only want to open points on the domain
    // with this method
    pub fn open_single_lagrange(
        crs: &CRS,
        transcript: &mut Transcript,
        polynomial: LagrangeBasis,
        point: usize,
    ) -> OpeningProof {
        let t = polynomial.evaluate_in_domain(point);
        let a = polynomial.values().to_vec();
        let mut b = vec![Fr::zero(); crs.n];
        b[point] = Fr::one();

        let P = slow_vartime_multiscalar_mul(
            a.iter().chain(b.iter()).chain(std::iter::once(&t)),
            crs.G
                .iter()
                .chain(crs.H.iter())
                .chain(std::iter::once(&crs.Q)),
        );

        // // We add the compressed point to the transcript, because we need some non-trivial input to generate alpha
        // // If this is not done, then the prover always will be able to predict what the first challenge will be
        transcript.append_point(b"P", &P);

        let no_zk = ipa::create(transcript, crs.G.clone(), crs.H.clone(), &crs.Q, a, b);

        OpeningProof { P, t, ipa: no_zk }
    }
    pub fn open_single_lagrange_out_of_domain(
        crs: &CRS,
        precomp: &PrecomputedWeights,
        transcript: &mut Transcript,
        polynomial: LagrangeBasis,
        x_i: Fr,
    ) -> OpeningProof {
        let a = polynomial.values().to_vec();
        let b = LagrangeBasis::evaluate_lagrange_coefficients(precomp, crs.n, x_i);

        let t = b.iter().zip(a.iter()).map(|(l_i, f_i)| *f_i * l_i).sum();

        let P = slow_vartime_multiscalar_mul(
            a.iter().chain(b.iter()).chain(std::iter::once(&t)),
            crs.G
                .iter()
                .chain(crs.H.iter())
                .chain(std::iter::once(&crs.Q)),
        );

        // // We add the compressed point to the transcript, because we need some non-trivial input to generate alpha
        // // If this is not done, then the prover always will be able to predict what the first challenge will be
        transcript.append_point(b"P", &P);

        let no_zk = ipa::create(transcript, crs.G.clone(), crs.H.clone(), &crs.Q, a, b);

        OpeningProof { P, t, ipa: no_zk }
    }
}

fn powers_of(point: Fr, n: usize) -> Vec<Fr> {
    let mut powers = Vec::with_capacity(n);
    powers.push(Fr::one());

    for i in 1..n {
        powers.push(powers[i - 1] * point);
    }
    powers
}

#[test]
fn open_single_proof() {
    let poly = DensePolynomial {
        coeffs: vec![Fr::one(), Fr::one()],
    };

    let point = Fr::from(5u128);
    let n = poly.coeffs.len();

    let crs = CRS::new(n);

    let mut transcript = Transcript::new(b"foo");
    let mut proof = MultiOpen::open_single(&crs, &mut transcript, poly, point);

    let mut transcript = Transcript::new(b"foo");
    assert!(proof.check_single(&crs, &mut transcript, n))
}
#[test]
fn open_single_lagrange_proof() {
    let poly = LagrangeBasis::new(vec![
        Fr::from(200),
        Fr::one(),
        Fr::from(25u128),
        Fr::from(28u128),
    ]);

    let point = 1;
    let n = poly.values().len();

    let crs = CRS::new(n);

    let mut transcript = Transcript::new(b"foo");
    let mut proof = MultiOpen::open_single_lagrange(&crs, &mut transcript, poly, point);

    let mut transcript = Transcript::new(b"foo");
    assert!(proof.check_single(&crs, &mut transcript, n))
}
#[test]
fn open_multiproof_proof() {
    let poly = DensePolynomial {
        coeffs: vec![Fr::one(), Fr::one()],
    };
    let n = poly.coeffs.len();

    let point = Fr::from(5u128);
    let y_i = poly.evaluate(&point);

    let crs = CRS::new(n);
    let poly_comm = crs.commit_poly(&poly);

    let prover_query = ProverQuery {
        comm: poly_comm,
        poly: poly,
        x_i: point,
        y_i,
    };

    let mut transcript = Transcript::new(b"foo");
    let multiproof = MultiOpen::open_multiple(&crs, &mut transcript, vec![prover_query.clone()]);

    let mut transcript = Transcript::new(b"foo");
    let verifier_query: VerifierQuery = prover_query.into();
    assert!(multiproof.check_single(&crs, vec![verifier_query], &mut transcript, n));
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
        vec![verifier_query],
        &mut transcript,
        n
    ));
}
