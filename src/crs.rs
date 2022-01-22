use ark_serialize::CanonicalSerialize;
use bandersnatch::{EdwardsAffine, EdwardsProjective};
use banderwagon::Element;

use crate::{ipa::slow_vartime_multiscalar_mul, lagrange_basis::LagrangeBasis};

#[derive(Debug, Clone)]
pub struct CRS {
    pub n: usize,
    pub G: Vec<Element>,
    pub Q: Element,
}

impl CRS {
    pub fn new(n: usize, seed: &'static [u8]) -> CRS {
        // TODO generate the Q value from the seed also
        // TODO: this will also make assert_dedup work as expected
        // TODO: since we should take in `Q` too
        let G: Vec<_> = generate_random_elements(n, seed).into_iter().collect();
        let Q = Element::prime_subgroup_generator();

        CRS::assert_dedup(&G);

        CRS { n, G, Q }
    }
    // Asserts that not of the points generated are the same
    fn assert_dedup(points: &[Element]) {
        use std::collections::HashMap;
        let mut map = HashMap::new();
        for point in points {
            assert!(
                map.insert(point.to_bytes(), ()).is_none(),
                "crs has duplicated points"
            )
        }
    }
    pub fn commit_lagrange_poly(&self, polynomial: &LagrangeBasis) -> Element {
        slow_vartime_multiscalar_mul(polynomial.values().iter(), self.G.iter())
    }
}

impl std::ops::Index<usize> for CRS {
    type Output = Element;

    fn index(&self, index: usize) -> &Self::Output {
        &self.G[index]
    }
}

fn generate_random_elements(num_required_points: usize, seed: &'static [u8]) -> Vec<Element> {
    use ark_ec::group::Group;
    use ark_ff::PrimeField;
    use bandersnatch::Fq;
    use sha2::{Digest, Sha256};

    let mut hasher = Sha256::new();
    let choose_largest = false;

    (0u32..)
        .into_iter()
        // Hash the seed + i to get a possible x value
        .map(|i| {
            let mut hasher = Sha256::new();
            hasher.update(seed);
            hasher.update(&i.to_be_bytes());
            let bytes: Vec<u8> = hasher.finalize().to_vec();
            bytes
        })
        // The from_bytes method does not reduce the bytes, it expects the
        // input to be in a canonical format, so we must do the reduction ourselves
        .map(|hash_bytes| bandersnatch::Fq::from_be_bytes_mod_order(&hash_bytes))
        // Using the x co-ordinate fetch a possible y co-ordinate
        .map(|x_coord| EdwardsAffine::get_point_from_x(x_coord, choose_largest))
        .filter_map(|point| point)
        // Double the point incase its not in the prime order subgroup
        .map(|point| point.double())
        // Serialise x co-ordinate of point
        .map(|point| {
            let mut bytes = [0u8; 32];
            point.x.serialize(&mut bytes[..]).unwrap();
            // TODO: this reverse is hacky, and its because there is no way to specify the endianness in arkworks
            // TODO So we reverse it here, to be interopable with the banderwagon specs which needs big endian bytes
            bytes.reverse();
            bytes
        })
        // Using banderwagon deserialise the x-cordinate to get a valid banderwagon element
        .map(|bytes| Element::from_bytes(&bytes))
        .filter_map(|point| point)
        .take(num_required_points)
        .collect()
}

// TODO: update hackmd as we are now using banderwagon
// TODO then redo this test
// #[test]
// fn crs_consistency() {
//     // See: https://hackmd.io/1RcGSMQgT4uREaq1CCx_cg#Methodology
//     use ark_serialize::CanonicalSerialize;
//     use bandersnatch::Fq;
//     use sha2::{Digest, Sha256};

//     let points = generate_random_elements(256, b"eth_verkle_oct_2021");
//     for point in &points {
//         let on_curve = point.is_on_curve();
//         let in_correct_subgroup = point.is_in_correct_subgroup_assuming_on_curve();
//         if !on_curve {
//             panic!("generated a point which is not on the curve")
//         }
//         if !in_correct_subgroup {
//             panic!("generated a point which is not in the prime subgroup")
//         }
//     }

//     let mut bytes = [0u8; 32];
//     points[0].serialize(&mut bytes[..]).unwrap();
//     assert_eq!(
//         hex::encode(&bytes),
//         "22ac968a98ab6c50379fc8b039abc8fd9aca259f4746a05bfbdf12c86463c208",
//         "the first point is incorrect"
//     );
//     let mut bytes = [0u8; 32];
//     points[255].serialize(&mut bytes[..]).unwrap();
//     assert_eq!(
//         hex::encode(&bytes),
//         "c8b4968a98ab6c50379fc8b039abc8fd9aca259f4746a05bfbdf12c86463c208",
//         "the 256th (last) point is incorrect"
//     );

//     let mut hasher = Sha256::new();
//     for point in &points {
//         let mut bytes = [0u8; 32];
//         point.serialize(&mut bytes[..]).unwrap();
//         hasher.update(&bytes);
//     }
//     let bytes = hasher.finalize().to_vec();
//     assert_eq!(
//         hex::encode(&bytes),
//         "c390cbb4bc42019685d5a01b2fb8a536d4332ea4e128934d0ae7644163089e76",
//         "unexpected point encountered"
//     );
// }
