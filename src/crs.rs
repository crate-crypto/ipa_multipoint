pub mod basic;
pub mod precomputed;

use crate::lagrange_basis::LagrangeBasis;
use ark_ec::{AffineCurve, ProjectiveCurve};
use ark_ff::PrimeField;
use bandersnatch::{EdwardsAffine, EdwardsProjective, Fr};

use self::{basic::BasicCommit, precomputed::PrecomputeLagrange};

#[derive(Debug, Clone)]
pub struct CRS<C: CRSCommitter> {
    pub n: usize,
    pub G: Vec<EdwardsProjective>,
    pub Q: EdwardsProjective,
    precomp: C,
}

pub type BasicCRS = CRS<BasicCommit>;
pub type PrecomputedCRS = CRS<PrecomputeLagrange>;

impl BasicCRS {
    pub fn new(n: usize, seed: &'static [u8]) -> Self {
        let G: Vec<_> = generate_random_elements(n, seed)
            .into_iter()
            .map(|affine_point| affine_point.into_projective())
            .collect();
        let Q = EdwardsProjective::prime_subgroup_generator();
        CRS {
            n,
            G,
            Q,
            precomp: BasicCommit,
        }
    }
}
impl PrecomputedCRS {
    pub fn new(n: usize, seed: &'static [u8]) -> Self {
        let G_aff: Vec<_> = generate_random_elements(n, seed);
        let committer = PrecomputeLagrange::precompute(&G_aff);
        let G = G_aff
            .into_iter()
            .map(|affine_point| affine_point.into_projective())
            .collect();
        let Q = EdwardsProjective::prime_subgroup_generator();
        CRS {
            n,
            G,
            Q,
            precomp: committer,
        }
    }
}

impl<C: CRSCommitter> CRS<C> {
    pub fn commit_lagrange_poly(&self, polynomial: &LagrangeBasis) -> EdwardsProjective {
        self.precomp
            .commit_full_lagrange(&polynomial.values(), &self.G)
    }
    pub fn commit_full(&self, values: &[Fr]) -> EdwardsProjective {
        self.precomp.commit_full_lagrange(values, &self.G)
    }
}

impl<C: CRSCommitter> std::ops::Index<usize> for CRS<C> {
    type Output = EdwardsProjective;

    fn index(&self, index: usize) -> &Self::Output {
        &self.G[index]
    }
}
impl<C: CRSCommitter> std::ops::Index<usize> for &CRS<C> {
    type Output = EdwardsProjective;

    fn index(&self, index: usize) -> &Self::Output {
        &self.G[index]
    }
}

pub trait CRSCommitter {
    // Commit to a lagrange polynomial, evaluations.len() must equal the size of the SRS
    fn commit_full_lagrange(
        &self,
        evaluations: &[Fr],
        points: &[EdwardsProjective],
    ) -> EdwardsProjective;
    // compute value * G for a specific generator in the SRS
    // fn scalar_mul(&self, value: Fr, lagrange_index: usize) -> EdwardsProjective;

    // fn commit_sparse(&self, val_indices: Vec<(Fr, usize)>) -> EdwardsProjective {
    //     let mut result = EdwardsProjective::default();

    //     for (value, lagrange_index) in val_indices {
    //         result += self.scalar_mul(value, lagrange_index)
    //     }

    //     return result;
    // }
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
