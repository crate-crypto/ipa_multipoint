use ark_ff::PrimeField;
use bandersnatch::{EdwardsProjective, Fr};
use merlin::Transcript;
pub trait TranscriptProtocol {
    /// Compute a `label`ed challenge variable.
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Fr;
    fn append_point(&mut self, label: &'static [u8], point: &EdwardsProjective);
    fn append_scalar(&mut self, label: &'static [u8], point: &Fr);
}

impl TranscriptProtocol for Transcript {
    fn challenge_scalar(&mut self, label: &'static [u8]) -> Fr {
        let mut buf = [0u8; 64];
        self.challenge_bytes(label, &mut buf);

        Fr::from_be_bytes_mod_order(&buf)
    }

    fn append_point(&mut self, label: &'static [u8], point: &EdwardsProjective) {
        use ark_serialize::CanonicalSerialize;
        let mut buf = vec![0u8; point.serialized_size()];
        point.serialize(&mut buf).unwrap();
        self.append_message(label, &buf)
    }

    fn append_scalar(&mut self, label: &'static [u8], scalar: &Fr) {
        use ark_serialize::CanonicalSerialize;
        let mut buf = vec![0u8; scalar.serialized_size()];
        scalar.serialize(&mut buf).unwrap();
        self.append_message(label, &buf)
    }
}
