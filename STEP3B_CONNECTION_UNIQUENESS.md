# Step 3B — Coordinate Levi-Civita existence and uniqueness

Certified mathematical extension of certified Step 3A main 2202005bd35376cc4695ff6547b97c8ba23215a8. Both prior modules and both permanent ledgers are unchanged. Lean 4.24.0 and Mathlib v4.24.0 are unchanged.

New module: 17 verified theorems, 2 verified definitions, 217 audited declarations. The verified results derive trivial kernel from the signature witness, nonzero determinant, the symmetric smooth inverse by adjugate/determinant, the full Step 3A metric-data hypotheses from smooth symmetric Lorentzian metric alone, uniqueness of torsion-free metric-compatible coordinate coefficients, their smoothness, and actual inverse differentiation dA = -A(dg)A with inverse metric compatibility. Reuses Step 3A and the existing kinetic-trace convention. Both corrected runs passed; all 217 declarations have clean dependency reports. See [Step 3B v1.0 baseline](STEP3B_BASELINE_V1.0.md) and [permanent ledger](STEP3B_AXIOM_AUDIT.tsv). Consolidation CI and owner approval remain pending.

Scope is the whole four-dimensional coordinate model, not a general smooth manifold. Existence/uniqueness concerns coefficient arrays satisfying the coordinate identities, not yet an intrinsic connection on tangent-bundle sections. Chart transformation, arbitrary chart domains, gluing, actual scalar Hessian, global conservation and physical claims remain later obligations. Do not start Step 3C during consolidation.

CI rechecks the exact frozen source blobs and all three permanent ledgers, builds all three modules and audits every named declaration. Main is not modified.
