# Intrinsic geometry, local connection and eventual counting estimate

Baseline: 57 declarations verified at 2a46f65cad0b7290bbf234e3fe8a96c9b1be3a9d, run 45885129255; standard axioms only. This branch adds 15 candidates, pending CI.

Geometry: actual Hilbert-space inner product and gauge invariance of the horizontal pullback, tangent condition of differentiable normalized curves and gauge law from actual derivatives. This does not yet construct the smooth projective quotient or identify its full curvature tensor with the finite covariance.

Conservation: explicit connection on covectors and rank-two tensors in a chart, with actual derivative product rules, linearity and metric compatibility. The scalar kinetic trace derivative and full global Levi-Civita construction remain to be formalized. No new physical axioms are introduced.

Number theory: extends the eventual von Koch-type estimate to the global zero-extended count, then proves a uniform-in-tau heat-trace bound. The actual implication from Mathlib's RiemannHypothesis to the eventual strict counting estimate is still external. Do not replace that obligation with a custom axiom or a circular hypothesis. Alpöge/Claude proof developments and their Mathlib compatibility require separate audit. The arithmetic spectrum is not identified with spacetime.

No unverified manuscript is published. All theorem declarations are included in the audit.
