# Step 3B — Coordinate Levi-Civita existence and uniqueness

Candidate extension of certified Step 3A main 2202005bd35376cc4695ff6547b97c8ba23215a8. Both prior modules and both permanent ledgers are unchanged. Lean 4.24.0 and Mathlib v4.24.0 are unchanged.

New module: 17 theorem candidates, 2 definitions, 217 total audit targets. The objective is to derive trivial kernel from the signature witness, nonzero determinant, the symmetric smooth inverse by adjugate/determinant, the full Step 3A metric-data hypotheses from smooth symmetric Lorentzian metric alone, uniqueness of torsion-free metric-compatible coordinate coefficients, their smoothness, and actual inverse differentiation dA = -A(dg)A with inverse metric compatibility. Reuses Step 3A and the existing kinetic-trace convention. No custom axioms or admitted proofs are intended. Candidate status until both CI runs and the complete expanded audit succeed.

Scope is the whole four-dimensional coordinate model, not a general smooth manifold. Existence/uniqueness concerns coefficient arrays satisfying the coordinate identities, not yet an intrinsic connection on tangent-bundle sections. Chart transformation, arbitrary chart domains, gluing, actual scalar Hessian, global conservation and physical claims remain later obligations. Do not start Step 3C before Step 3B certification.

CI rechecks the exact frozen source blobs and both permanent ledgers, builds all three modules and audits every named declaration. Main is not modified.
