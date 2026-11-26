# Paper I — Lean verification
Companion algebraic proof source for the research manuscript on multiscale amplitude–phase covariance.

Status: pending actual CI execution. Fourteen candidate theorems cover scalar weighted variance, componentwise covariance, finite hierarchical increments, a single-covector causal energy flux identity, a one-component complex Gram identity, and the algebraic closure obstruction. These do not establish the full projective geometry, differential stress conservation, analytic number theory, or physical unification. The manuscript remains outside this repository.

## Reproduce
Use the toolchain specified in lean-toolchain.
```sh
lake update
lake exe cache get
lake build
lake env lean Covariance.lean
```
CI checks all printed dependencies against the standard Lean axioms and archives the resolved manifest and logs. No claim of kernel verification is made before CI evidence exists.
