# Step 3D — curvature and geometric conservation

Starting baseline: main c590b4cbbf417506fe60e5eaf23d8268fea5e120, successful main run 46124949894, 323 certified declarations. All nine prior Lean modules and all five ledgers remain frozen.

## First checkpoint
Step3D.lean introduces actual coordinate derivatives of connection coefficients, Riemann curvature with convention R(X,Y)Z = ∇X∇YZ − ∇Y∇XZ − ∇[X,Y]Z, Ricci and scalar contractions, Einstein tensor expression, skew symmetry in curvature directions and flat Minkowski regression. 7 theorem candidates and 5 definitions; 335 total targets. Await both CI runs. Coordinate formulas are not yet intrinsic tensors.

## Remaining gates
1. Derive curvature from the actual Step 3C covariant derivative and prove multilinearity, germ locality and chart independence; impose and track sufficient differentiability.
2. First Bianchi identity from torsion freedom; metric-lowered curvature symmetries and Ricci symmetry.
3. Intrinsic covariant derivative of curvature and second Bianchi identity; derive contracted Bianchi and divergence-free Einstein tensor, with no conservation assumption.
4. Verify nonflat benchmark and flat limit; review actual tensor contraction and signs.
5. Audit all declarations against all five frozen ledgers; independent mathematical scope review and owner-approved consolidation.

Einstein field equations, a physical quantum-to-Lorentzian map, stress-energy sourcing, and empirical claims are not consequences of the geometric identities alone. No Step 3E or main merge without approval.
