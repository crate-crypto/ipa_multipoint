use super::CRSCommitter;
use crate::slow_vartime_multiscalar_mul;
use bandersnatch::{EdwardsProjective, Fr};

#[derive(Debug, Clone)]
pub struct BasicCommit;

impl CRSCommitter for BasicCommit {
    fn commit_full_lagrange(
        &self,
        evaluations: &[Fr],
        points: &[EdwardsProjective],
    ) -> EdwardsProjective {
        assert_eq!(
            evaluations.len(),
            points.len(),
            "number of points equal {}, number of scalars equal {}",
            points.len(),
            evaluations.len()
        );
        slow_vartime_multiscalar_mul(evaluations.iter(), points.iter())
    }
}
