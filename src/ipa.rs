#![allow(non_snake_case)]
use crate::math_utils::inner_product;
use crate::transcript::TranscriptProtocol;
use ark_ec::group::Group;
use ark_ec::ProjectiveCurve;

use ark_ff::Field;
use ark_ff::PrimeField;
use ark_ff::{One, Zero};
use bandersnatch::multi_scalar_mul;
use bandersnatch::EdwardsAffine;
use bandersnatch::EdwardsParameters;
use bandersnatch::EdwardsProjective;
use bandersnatch::Fr;
use bandersnatch::GLVParameters;
use itertools::Itertools;
use merlin::Transcript;
use std::borrow::Borrow;
use std::iter;

#[derive(Clone)]
pub struct NoZK {
    // From the literature this would be u_{-1}
    pub(crate) L_vec: Vec<EdwardsProjective>,
    // From the literature this would be u_{+1}
    pub(crate) R_vec: Vec<EdwardsProjective>,
    // From the literature, this would be w'
    pub(crate) a: Fr,
}

pub fn create(
    transcript: &mut Transcript,
    mut G_Vec: Vec<EdwardsProjective>,
    Q: &EdwardsProjective,
    mut a_vec: Vec<Fr>,
    a_comm: EdwardsProjective,
    mut b_vec: Vec<Fr>,
    // This is the z in f(z)
    input_point: Fr,
) -> NoZK {
    let mut a = &mut a_vec[..];
    let mut b = &mut b_vec[..];
    let mut G = &mut G_Vec[..];

    let n = G.len();

    // All of the input vectors must have the same length.
    assert_eq!(G.len(), n);
    assert_eq!(a.len(), n);
    assert_eq!(b.len(), n);

    // All of the input vectors must have a length that is a power of two.
    assert!(n.is_power_of_two());

    transcript.append_u64(b"n", n as u64);
    let output_point = inner_product(a, b);
    transcript.append_scalar(b"input point", &input_point);
    transcript.append_scalar(b"output point", &output_point);
    transcript.append_point(b"poly commit", &a_comm);

    let z = transcript.challenge_scalar(b"z");
    let Q = Q.mul(&z); // XXX: It would not hurt to add this augmented point into the transcript

    let num_rounds = log2(n);

    let mut L_vec: Vec<EdwardsProjective> = Vec::with_capacity(num_rounds as usize);
    let mut R_vec: Vec<EdwardsProjective> = Vec::with_capacity(num_rounds as usize);

    for k in 0..num_rounds {
        let (a_L, a_R) = halve(a);
        let (b_L, b_R) = halve(b);
        let (G_L, G_R) = halve(G);

        let z_L = inner_product(a_R, b_L);
        let z_R = inner_product(a_L, b_R);

        let L = slow_vartime_multiscalar_mul(
            a_R.iter().chain(iter::once(&z_L)),
            G_L.iter().chain(iter::once(&Q)),
        );
        let R = slow_vartime_multiscalar_mul(
            a_L.iter().chain(iter::once(&z_R)),
            G_R.iter().chain(iter::once(&Q)),
        );

        L_vec.push(L);
        R_vec.push(R);

        transcript.append_point(b"L", &L);
        transcript.append_point(b"R", &R);

        let x = transcript.challenge_scalar(b"folding challenge");
        let x_inv = x.inverse().unwrap();
        for i in 0..a_L.len() {
            a_L[i] = a_L[i] + x * a_R[i];
            b_L[i] = b_L[i] + x_inv * b_R[i];
            G_L[i] = G_L[i] + G_R[i].mul(x_inv.into_repr());
        }

        a = a_L;
        b = b_L;
        G = G_L;
    }

    NoZK {
        L_vec,
        R_vec,
        a: a[0],
    }
}
// Halves the slice that is passed in
// Assumes that the slice has an even length
fn halve<T>(scalars: &mut [T]) -> (&mut [T], &mut [T]) {
    let len = scalars.len();
    scalars.split_at_mut(len / 2)
}
fn log2(n: usize) -> u32 {
    n.next_power_of_two().trailing_zeros()
}

impl NoZK {
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        G_Vec: &[EdwardsProjective],
        Q: &EdwardsProjective,
        n: usize,
        mut b: Vec<Fr>,
        a_comm: EdwardsProjective,
        input_point: Fr,
        output_point: Fr,
    ) -> bool {
        let mut G = G_Vec.to_owned();
        let mut G = &mut G[..];
        let mut b = &mut b[..];

        let num_rounds = self.L_vec.len();

        // Check that the prover computed an inner proof
        // over a vector of size n
        if n != 1 << num_rounds {
            return false;
        }

        transcript.append_u64(b"n", n as u64);
        transcript.append_scalar(b"input point", &input_point);
        transcript.append_scalar(b"output point", &output_point);
        transcript.append_point(b"poly commit", &a_comm);

        let z = transcript.challenge_scalar(b"z");
        let Q = Q.mul(&z);

        let num_rounds = self.L_vec.len();

        let mut a_comm = a_comm + (Q.mul(output_point.into_repr()));

        let challenges = generate_challenges(self, transcript);
        let mut challenges_inv = challenges.clone();
        ark_ff::batch_inversion(&mut challenges_inv);

        // Compute the expected commitment
        // TODO use a multizip from itertools
        for i in 0..num_rounds {
            let x = challenges[i];
            let x_inv = challenges_inv[i];
            let L = self.L_vec[i];
            let R = self.R_vec[i];

            a_comm = a_comm + L.mul(x.into_repr()) + R.mul(x_inv.into_repr());
        }

        for x_inv in challenges_inv.iter() {
            let (G_L, G_R) = halve(G);
            let (b_L, b_R) = halve(b);

            for i in 0..G_L.len() {
                G_L[i] = G_L[i] + G_R[i].mul(x_inv.into_repr());
                b_L[i] = b_L[i] + b_R[i] * x_inv;
            }
            G = G_L;
            b = b_L;
        }
        assert_eq!(G.len(), 1);
        assert_eq!(b.len(), 1);

        let exp_P = G[0].mul(self.a.into_repr()) + Q.mul((self.a * b[0]).into_repr());

        exp_P == a_comm
    }
    pub fn verify_multiexp(
        &self,
        transcript: &mut Transcript,
        G_Vec: &[EdwardsProjective],
        Q: &EdwardsProjective,
        n: usize,
        b_vec: Vec<Fr>,
        a_comm: EdwardsProjective,
        input_point: Fr,
        output_point: Fr,
    ) -> bool {
        let logn = self.L_vec.len();

        // Check that the prover computed an inner proof
        // over a vector of size n
        if n != (1 << logn) {
            return false;
        }

        transcript.append_u64(b"n", n as u64);
        transcript.append_scalar(b"input point", &input_point);
        transcript.append_scalar(b"output point", &output_point);
        transcript.append_point(b"poly commit", &a_comm);

        // Compute the scalar which will augment the point corresponding
        // to the inner product
        let z = transcript.challenge_scalar(b"z");

        // Generate all of the necessary challenges and their inverses
        let challenges = generate_challenges(self, transcript);
        let mut challenges_inv = challenges.clone();
        ark_ff::batch_inversion(&mut challenges_inv);

        // Generate the coefficients for the `G` vector and the `b` vector
        // {-g_i}{-b_i}
        let mut g_i: Vec<Fr> = Vec::with_capacity(1 << logn);
        let mut b_i: Vec<Fr> = Vec::with_capacity(1 << logn);

        for index in 0..n {
            let mut b = -Fr::one();
            for (bit, x_inv) in to_bits(index, logn).zip_eq(&challenges_inv) {
                if bit == 1 {
                    b *= x_inv;
                }
            }
            b_i.push(b);
            g_i.push(self.a * b);
        }

        let b_0 = inner_product(&b_vec, &b_i);
        let q_i = z * (output_point + self.a * b_0);

        slow_vartime_multiscalar_mul(
            challenges
                .iter()
                .chain(challenges_inv.iter())
                .chain(iter::once(&Fr::one()))
                .chain(iter::once(&q_i))
                .chain(g_i.iter()),
            self.L_vec
                .iter()
                .chain(self.R_vec.iter())
                .chain(iter::once(&a_comm))
                .chain(iter::once(Q))
                // XXX: note that we can do a Halo style optimisation here also
                // but instead of being (m log(d)) it will be O(mn) which is still good
                // because the verifier will be doing m*n field operations instead of m size n multi-exponentiations
                // This is done by interpreting g_i as coefficients in monomial basis
                // TODO: Optimise the majority of the time is spent on this vector, precompute
                .chain(G_Vec.iter()),
        )
        .is_zero()
    }
    // It's only semi unrolled.
    // This is being committed incase someone goes through the git history
    // The fully unrolled code is not that intuitive, but maybe this semi
    // unrolled version can help you to figure out the gap
    pub fn verify_semi_multiexp(
        &self,
        transcript: &mut Transcript,
        G_Vec: &[EdwardsProjective],
        Q: &EdwardsProjective,
        n: usize,
        b_Vec: Vec<Fr>,
        a_comm: EdwardsProjective,
        input_point: Fr,
        output_point: Fr,
    ) -> bool {
        let logn = self.L_vec.len();

        // Check that the prover computed an inner proof
        // over a vector of size n
        if n != (1 << logn) {
            return false;
        }

        transcript.append_u64(b"n", n as u64);
        transcript.append_scalar(b"input point", &input_point);
        transcript.append_scalar(b"output point", &output_point);
        transcript.append_point(b"poly commit", &a_comm);

        let z = transcript.challenge_scalar(b"z");
        let Q = Q.mul(&z);

        let a_comm = a_comm + (Q.mul(output_point.into_repr()));

        let challenges = generate_challenges(self, transcript);
        let mut challenges_inv = challenges.clone();
        ark_ff::batch_inversion(&mut challenges_inv);

        let P = slow_vartime_multiscalar_mul(
            challenges
                .iter()
                .chain(challenges_inv.iter())
                .chain(iter::once(&Fr::one())),
            self.L_vec
                .iter()
                .chain(self.R_vec.iter())
                .chain(iter::once(&a_comm)),
        );

        // {g_i}
        let mut g_i: Vec<Fr> = Vec::with_capacity(1 << logn);

        for index in 0..n {
            let mut g = Fr::one();
            for (bit, x_inv) in to_bits(index, logn).zip_eq(&challenges_inv) {
                if bit == 1 {
                    g *= x_inv;
                }
            }
            g_i.push(g);
        }

        let b_0 = inner_product(&b_Vec, &g_i);
        let G_0 = slow_vartime_multiscalar_mul(g_i.iter(), G_Vec.iter()); // TODO: Optimise the majority of the time is spent on this vector, precompute

        let exp_P = G_0.mul(self.a.into_repr()) + Q.mul((self.a * b_0).into_repr());

        exp_P == P
    }
}
fn to_bits(n: usize, bits_needed: usize) -> impl Iterator<Item = u8> {
    (0..bits_needed).map(move |i| ((n >> i) & 1) as u8).rev()
}

// TODO: use pippenger with endomorphism
// We allocate unnecessarily here because the multi_scalar_mul algorithm requires scalars
// TODO: in the unrolled version, we can collect points and scalars and then call
// TODO VariableBaseMSM::multi_scalar_mul(&points, &scalars) directly
// TODO check performance of that versus the current method
pub fn slow_vartime_multiscalar_mul<'a>(
    scalars: impl Iterator<Item = &'a Fr>,
    points: impl Iterator<Item = &'a EdwardsProjective>,
) -> EdwardsProjective {
    use ark_ec::group::Group;
    use ark_ec::msm::VariableBaseMSM;

    let scalars: Vec<_> = scalars.into_iter().map(|s| s.into_repr()).collect();
    let points: Vec<_> = points.map(|p| p.into_affine()).collect();
    VariableBaseMSM::multi_scalar_mul(&points, &scalars)
}

fn generate_challenges(proof: &NoZK, transcript: &mut Transcript) -> Vec<Fr> {
    let mut challenges: Vec<Fr> = Vec::with_capacity(proof.L_vec.len());

    for (L, R) in proof.L_vec.iter().zip(proof.R_vec.iter()) {
        transcript.append_point(b"L", L);
        transcript.append_point(b"R", R);

        let x_i = transcript.challenge_scalar(b"folding challenge");
        challenges.push(x_i);
    }

    challenges
}

use ark_serialize::CanonicalSerialize;
fn dbg_print<T: CanonicalSerialize>(s: T, label: &str) {
    let mut bytes = [0u8; 32];
    s.serialize(&mut bytes[..]).unwrap();
    println!("{} :{}", label, hex::encode(&bytes))
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::math_utils::{inner_product, powers_of};
    use ark_std::rand;
    use ark_std::rand::SeedableRng;
    use ark_std::UniformRand;
    use rand_chacha::ChaCha20Rng;
    use std::iter;
    #[test]
    fn test_create_nozk_proof() {
        let n = 8;

        let mut rng = ChaCha20Rng::from_seed([0u8; 32]);

        let a: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();

        let input_point = Fr::rand(&mut rng);
        let b = powers_of(input_point, n);
        let output_point = inner_product(&a, &b);
        let G: Vec<EdwardsProjective> = (0..n).map(|_| EdwardsProjective::rand(&mut rng)).collect();
        let Q = EdwardsProjective::rand(&mut rng);

        let mut prover_transcript = Transcript::new(b"ip_no_zk");

        let P = slow_vartime_multiscalar_mul(a.iter(), G.iter());

        let proof = create(
            &mut prover_transcript,
            G.clone(),
            &Q,
            a,
            P,
            b.clone(),
            input_point,
        );

        let mut verifier_transcript = Transcript::new(b"ip_no_zk");

        assert!(proof.verify_semi_multiexp(
            &mut verifier_transcript,
            &G,
            &Q,
            n,
            b,
            P,
            input_point,
            output_point
        ));
    }
}
