use ark_std::rand;
use ark_std::rand::SeedableRng;
use ark_std::UniformRand;
use bandersnatch::{EdwardsProjective, Fr};
use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use ipa_bandersnatch::ipa::create;
use ipa_bandersnatch::math_utils::inner_product;
use ipa_bandersnatch::slow_vartime_multiscalar_mul;
use ipa_bandersnatch::transcript::TranscriptProtocol;
use merlin::Transcript;
use rand_chacha::ChaCha20Rng;
use sha3::Sha3_512;
use std::iter;

pub fn criterion_benchmark(c: &mut Criterion) {
    let n = 256;

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
    prover_transcript.append_point(b"P", &P);

    let proof = create(&mut prover_transcript, G.clone(), H.clone(), &Q, a, b);

    let mut verifier_transcript = Transcript::new(b"ip_no_zk");
    verifier_transcript.append_point(b"P", &P);

    c.bench_function("verify 256", |b| {
        b.iter(|| proof.verify(&mut verifier_transcript, &G, &H, &Q, n, P, t))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
