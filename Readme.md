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

## API

- The OpeningProof should not carry `P` as the verifier re-computes it.
- We should wrap the IPA proof in a poly commit struct, so that users cannot mix up the `a_vec` and `b_vec`, we will not commit to `b_vec` as a poly-commit

## Tentative benchmarks



Machine : 2.4 GHz 8-Core Intel Core i9

- To verify the opening of a polynomial of degree 255 (256 points in lagrange basis): `11.92ms`

- To verify a multi-opening proof of 10,000 polynomials: `232.12ms`

- To verify a multi-opening proof of 20,000 polynomials: `405.87ms`

- To prove a multi-opening proof of 10,000 polynomials: `266.49ms`

- To prove a multi-opening proof of 20,000 polynomials: `422.94ms`


These benchmarks are tentative because on one hand, the machine being used may not be the what the average user uses, while on the other hand, we have not optimised the verifier algorithm to remove `bH` and the pippenger algorithm does not take into consideration GLV. 
