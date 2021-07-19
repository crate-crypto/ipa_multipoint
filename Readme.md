## IPA Multipoint

A polynomial commitment scheme for opening multiple polynomials at different points using the inner product argument.

**Do not use in production.**

### Security 

- The CRS is not being generated in a secure manner. The relative DLOG is known. In actuality, we want to use a hash_to_group algorithm. Try and increment would be the easiest one to implement as we do not care about timing attacks.

- Even with this, the code has not been reviewed, so should not be used in production.

## Efficiency

- Parallelism is not being used
- We have not modified pippenger to take benefit of the GLV endomorphism
- The IPA argument assumes that `b` in P = <a, G> + <b,H> + <a,b>Q needs to be commited to. We can change it to P = <a, G> + <a,b>Q and `b` can be computed by the verifier.