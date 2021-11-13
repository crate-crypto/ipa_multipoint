use ark_std::rand;
use ark_std::rand::SeedableRng;
use ark_std::UniformRand;
use bandersnatch::{EdwardsProjective, Fr};
use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use ipa_multipoint::crs::{BasicCRS, PrecomputedCRS};
use ipa_multipoint::ipa::create;
use ipa_multipoint::math_utils::{inner_product, powers_of};
use ipa_multipoint::slow_vartime_multiscalar_mul;
use ipa_multipoint::transcript::{Transcript, TranscriptProtocol};

use rand_chacha::ChaCha20Rng;
use std::iter;

pub fn criterion_benchmark(c: &mut Criterion) {
    let n = 256;

    let mut rng = ChaCha20Rng::from_seed([0u8; 32]);

    let a: Vec<Fr> = (0..n).map(|_| Fr::rand(&mut rng)).collect();

    let input_point = Fr::rand(&mut rng);
    let b_vec = powers_of(input_point, n);
    let output_point = inner_product(&a, &b_vec);

    let crs = PrecomputedCRS::new(n, b"seed word");

    let G: Vec<EdwardsProjective> = (0..n).map(|_| EdwardsProjective::rand(&mut rng)).collect();
    let Q = EdwardsProjective::rand(&mut rng);

    let mut prover_transcript = Transcript::new(b"ip_no_zk");

    let P = slow_vartime_multiscalar_mul(a.iter(), G.iter());

    let proof = create(
        &mut prover_transcript,
        crs.clone(),
        a,
        P,
        b_vec.clone(),
        input_point,
    );

    let mut verifier_transcript = Transcript::new(b"ip_no_zk");

    c.bench_function("verify multi exp2 256", |b| {
        b.iter(|| {
            proof.verify_semi_multiexp(
                &mut verifier_transcript,
                &crs,
                b_vec.clone(),
                P,
                input_point,
                output_point,
            )
        })
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
