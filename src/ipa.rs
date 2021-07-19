#![allow(non_snake_case)]
use crate::math_utils::inner_product;
use crate::transcript::TranscriptProtocol;
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
use merlin::Transcript;
use std::borrow::Borrow;
use std::iter;

/// NoZK is an optimisation over the bulletproofs IPA.
#[derive(Clone)]
pub struct NoZK {
    // From the literature this would be u_{-1}
    pub(crate) L_vec: Vec<EdwardsProjective>,
    // From the literature this would be u_{+1}
    pub(crate) R_vec: Vec<EdwardsProjective>,
    // From the literature, this would be w'
    pub(crate) a: Fr,
    // From the literature, this would be w''
    pub(crate) b: Fr,
}

// a and b are the witness prime and witness prime prime respectively
// G_Vec, H_Vec and Q is g prime, g prime prime and Q of the crs respectively
// This implementation will intentionally try to mirror the dalek-cryptography implementation in design choices and variable naming
// making it easier to draw comparisons between the two and provide benchmarks
pub fn create(
    transcript: &mut Transcript,
    mut G_Vec: Vec<EdwardsProjective>,
    mut H_Vec: Vec<EdwardsProjective>,
    Q: &EdwardsProjective,
    mut a_vec: Vec<Fr>,
    mut b_vec: Vec<Fr>,
) -> NoZK {
    let mut a = &mut a_vec[..];
    let mut b = &mut b_vec[..];
    let mut G = &mut G_Vec[..];
    let mut H = &mut H_Vec[..];

    let mut n = G.len();

    // All of the input vectors must have the same length.
    assert_eq!(G.len(), n);
    assert_eq!(H.len(), n);
    assert_eq!(a.len(), n);
    assert_eq!(b.len(), n);

    // All of the input vectors must have a length that is a power of two.
    assert!(n.is_power_of_two());

    transcript.append_u64(b"n", n as u64);

    let lg_n = n.next_power_of_two().trailing_zeros() as usize;
    let mut L_vec: Vec<EdwardsProjective> = Vec::with_capacity(lg_n);
    let mut R_vec: Vec<EdwardsProjective> = Vec::with_capacity(lg_n);

    let alpha = transcript.challenge_scalar(b"alpha");

    let Q = Q.mul(alpha.inverse().unwrap().into_repr());

    while n != 1 {
        n = n / 2;

        let (a_L, a_R) = a.split_at_mut(n);
        let (b_L, b_R) = b.split_at_mut(n);
        let (G_L, G_R) = G.split_at_mut(n);
        let (H_L, H_R) = H.split_at_mut(n);

        let c_R = inner_product(a_R, b_L);
        let c_L = inner_product(a_L, b_R);
        let L = slow_vartime_multiscalar_mul(
            a_L.iter().chain(b_R.iter()).chain(iter::once(&c_L)),
            G_R.iter().chain(H_L.iter()).chain(iter::once(&Q)),
        );
        let R = slow_vartime_multiscalar_mul(
            a_R.iter().chain(b_L.iter()).chain(iter::once(&c_R)),
            G_L.iter().chain(H_R.iter().chain(iter::once(&Q))),
        );

        L_vec.push(L);
        R_vec.push(R);

        transcript.append_point(b"L", &L);
        transcript.append_point(b"R", &R);

        let x_i: Fr = transcript.challenge_scalar(b"x_i");
        for i in 0..n {
            a_L[i] = a_L[i] * x_i + a_R[i];
            b_L[i] = b_L[i] + x_i * b_R[i];
            G_L[i] = G_L[i] + G_R[i].mul(x_i.into_repr());
            H_L[i] = H_L[i].mul(x_i.into_repr()) + &H_R[i];
        }

        a = a_L;
        b = b_L;
        G = G_L;
        H = H_L;
    }

    NoZK {
        L_vec: L_vec,
        R_vec: R_vec,
        a: a[0],
        b: b[0],
    }
}
impl NoZK {
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        G_Vec: &[EdwardsProjective],
        H_Vec: &[EdwardsProjective],
        Q: &EdwardsProjective,
        mut n: usize,
        mut P: EdwardsProjective,
        t: Fr,
    ) -> bool {
        let mut G = G_Vec.to_owned();
        let mut H = H_Vec.to_owned();

        let Ls = self.L_vec.clone();
        let Rs = self.R_vec.clone();

        assert_eq!(n, 1 << Ls.len());

        transcript.append_u64(b"n", n as u64);

        let alpha = transcript.challenge_scalar(b"alpha");
        let Q = Q.mul(&alpha.inverse().unwrap().into_repr());

        // P - (alpha - 1) * t * Q

        P = P - Q.mul(((alpha - Fr::one()) * t).into_repr());

        let challenges = generate_challenges(self, transcript);

        for ((L, R), challenge) in Ls.iter().zip(Rs.iter()).zip(challenges.iter()) {
            let challenge_sq = challenge.square();
            P = L.mul(challenge_sq.into_repr()) + P.mul(challenge.into_repr()) + R;
        }

        for challenge in challenges.iter() {
            n = n / 2;

            let (G_L, G_R) = G.split_at_mut(n);
            let (H_L, H_R) = H.split_at_mut(n);

            G = vector_vector_add(G_L, &mut vector_scalar_mul(G_R, challenge));
            H = vector_vector_add(&mut vector_scalar_mul(H_L, challenge), H_R);
        }

        let exp_P = G[0].mul(self.a.into_repr())
            + H[0].mul(self.b.into_repr())
            + Q.mul((self.a * self.b).into_repr());

        exp_P == P
    }
    pub fn verify_multiexp(
        &self,
        transcript: &mut Transcript,
        G_Vec: &[EdwardsProjective],
        H_Vec: &[EdwardsProjective],
        Q: &EdwardsProjective,
        n: usize,
        P: EdwardsProjective,
        t: Fr,
    ) -> bool {
        // decode L,R
        let Ls = self.L_vec.clone();
        let Rs = self.R_vec.clone();
        assert_eq!(n, 1 << Ls.len());

        let n = 1 << Ls.len();

        // challenge data
        transcript.append_u64(b"n", n as u64);
        let alpha = transcript.challenge_scalar(b"alpha");
        let challenges = generate_challenges(self, transcript);

        let logn = challenges.len();

        // {g_i},{h_i}
        let mut g_i: Vec<Fr> = Vec::with_capacity(n);
        let mut h_i: Vec<Fr> = Vec::with_capacity(n);
        for x in 0..n {
            let mut i: usize = 1;
            let mut j: usize = 0;
            let mut g = self.a;
            let mut h = self.b;
            while i < n {
                if i & x != 0 {
                    g *= challenges[logn - j - 1];
                } else {
                    h *= challenges[logn - j - 1];
                }
                i <<= 1;
                j += 1;
            }
            g_i.push(g);
            h_i.push(h);
        }

        // {l_j},{r_j}
        let mut l_j: Vec<Fr> = Vec::with_capacity(n);
        let mut r_j: Vec<Fr> = Vec::with_capacity(n);
        let mut p = Fr::one();
        for i in 0..logn {
            let mut l = -challenges[i] * challenges[i];
            let mut r = -Fr::one();
            for j in (i + 1)..logn {
                l *= challenges[j];
                r *= challenges[j];
            }
            l_j.push(l);
            r_j.push(r);
            p *= challenges[i];
        }

        // return value goes here
        let q = alpha.inverse().unwrap() * ((alpha - Fr::one()) * t * p + self.a * self.b);

        let R = slow_vartime_multiscalar_mul(
            g_i.iter()
                .chain(h_i.iter())
                .chain(l_j.iter())
                .chain(r_j.iter())
                .chain(iter::once(&q))
                .chain(iter::once(&-p)),
            G_Vec
                .iter()
                .chain(H_Vec.iter())
                .chain(Ls.iter())
                .chain(Rs.iter())
                .chain(iter::once(Q))
                .chain(iter::once(&P)),
        );

        R.is_zero()
    }
}

// TODO: use pippenger with endomorphism
pub fn slow_vartime_multiscalar_mul<'a>(
    scalars: impl Iterator<Item = &'a Fr>,
    points: impl Iterator<Item = &'a EdwardsProjective>,
) -> EdwardsProjective {
    let mut res = EdwardsProjective::default();
    for (point, scalar) in points.into_iter().zip(scalars.into_iter()) {
        let point_aff = point.into_affine();
        let psi_point = EdwardsParameters::endomorphism(&point_aff);
        let (s1, s2) = EdwardsParameters::scalar_decomposition(scalar);

        let partial_res = multi_scalar_mul(&point_aff, &s1, &psi_point, &s2);
        res += partial_res;
    }

    res
}

fn generate_challenges(proof: &NoZK, transcript: &mut Transcript) -> Vec<Fr> {
    let mut challenges: Vec<Fr> = Vec::new();

    for (L, R) in proof.L_vec.iter().zip(proof.R_vec.iter()) {
        transcript.append_point(b"L", L);
        transcript.append_point(b"R", R);

        let x_i = transcript.challenge_scalar(b"x_i");
        challenges.push(x_i);
    }

    challenges
}

fn vector_scalar_mul(vec_p: &mut [EdwardsProjective], challenge: &Fr) -> Vec<EdwardsProjective> {
    vec_p.iter().map(|p| p.mul(challenge.into_repr())).collect()
}
fn vector_vector_add(
    a: &mut [EdwardsProjective],
    b: &mut [EdwardsProjective],
) -> Vec<EdwardsProjective> {
    a.iter().zip(b.iter()).map(|(a, b)| *a + *b).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math_utils::inner_product;
    use ark_std::rand;
    use ark_std::rand::SeedableRng;
    use ark_std::UniformRand;
    use rand_chacha::ChaCha20Rng;
    use sha3::Sha3_512;
    use std::iter;
    #[test]
    fn test_create_nozk_proof() {
        let n = 512;

        let mut rng = ChaCha20Rng::from_seed([0u8; 32]);

        let a: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();
        let b: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();

        let t = inner_product(&a, &b);

        let G: Vec<EdwardsProjective> = (0..n).map(|_| EdwardsProjective::rand(&mut rng)).collect();
        let H: Vec<EdwardsProjective> = (0..n).map(|_| EdwardsProjective::rand(&mut rng)).collect();

        let Q = EdwardsProjective::rand(&mut rng);

        let mut prover_transcript = Transcript::new(b"ip_no_zk");

        let P = slow_vartime_multiscalar_mul(
            a.iter().chain(b.iter()).chain(iter::once(&t)),
            G.iter().chain(H.iter()).chain(iter::once(&Q)),
        );

        // We add the compressed point to the transcript, because we need some non-trivial input to generate alpha
        // If this is not done, then the prover always will be able to predict what the first challenge will be
        // also because `P` is in the statement, we are proving over.
        prover_transcript.append_point(b"P", &P);

        let proof = create(&mut prover_transcript, G.clone(), H.clone(), &Q, a, b);

        let mut verifier_transcript = Transcript::new(b"ip_no_zk");
        verifier_transcript.append_point(b"P", &P);

        assert!(proof.verify(&mut verifier_transcript, &G, &H, &Q, n, P, t));
    }
}
