# Paper I — Step 3B v1.0 certified coordinate Levi-Civita foundations

**Status:** Mathematical certification passed on 27 November 2026. Consolidation on the existing development branch preserves all three certified modules and both earlier permanent ledgers. Fresh integration CI and explicit owner approval of [PR #19](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/pull/19) are required before merging. Step 3C has not started.

## Frozen mathematical checkpoint

- Certified mathematical commit: `968fcced30d9d075f43086e5853e88fca9915356`.
- Parent certified Step 3A main: `2202005bd35376cc4695ff6547b97c8ba23215a8`.
- Covariance.lean: `8481ef5c36f41b016b9fe5d99c9747fea0cbb71e`.
- Step3A.lean: `c3ff5a4b4a4f23ee79bfa2342a68d35780fae98e`.
- Step3B.lean: `c68a9e0892b80328c265a69d10e2ce3d00ceccef`.
- STEP2_AXIOM_AUDIT.tsv: `039482d1eaae0d6291a31bc582f3b20dafda11cb`.
- STEP3A_AXIOM_AUDIT.tsv: `bb169a74488b7b0c92621c2b95657d6a9e08074d`.
- 179 theorems and 38 definitions: 217 total named declarations (174 in Covariance.lean, 24 in Step3A.lean, 19 in Step3B.lean).
- Lean 4.24.0, compiler revision 797c613eb9b6d4ec95db23e3e00af9ac6657f24b. Mathlib v4.24.0 resolved at f897ebcf72cd16f89ab4577d0c826cd14afaafc7.
- Every audited declaration in both successful runs depends exactly on Classical.choice, Quot.sound, propext; no sorryAx or other axioms. All 174 Step 2 and 198 Step 3A records match their respective ledgers.

## Certified mathematical scope

On the whole real four-dimensional coordinate model, a pointwise Lorentzian frame witness implies trivial kernel and nonzero determinant. Smooth entries imply smooth determinant and adjugate; the nonsingular inverse is constructed, symmetric when the metric is symmetric, and smooth for nonzero determinant. The full Step 3A metric-data structure is derived from a smooth symmetric metric with Lorentzian signature at every point. The actual Christoffel coefficients exist uniquely among arrays satisfying torsion-freeness and metric compatibility and are smooth. Actual coordinate differentiation of the inverse identity yields dA = -A(dg)A and the contravariant metric compatibility identity in the existing kinetic-trace convention.

| Verified objective | Declarations |
|---|---|
| Pairing, nondegeneracy, determinant | coordinate_pair_factor, lorentz_signature_no_kernel, coordinate_det_ne_zero |
| Smooth inverse construction | coordinate_det_smooth, coordinate_adjugate_smooth, coordinate_inverse_smooth, coordinate_inverse_symmetric, coordinate_constructed_inverse, lorentz_data_from_metric |
| Unique existence of coefficient array | coordinate_lc_lower_unique, coordinate_lc_unique, lorentz_coordinate_lc_exists_unique |
| Smoothness | metric_partial_smooth, metric_christoffel_smooth |
| Actual inverse differentiation and compatibility | coordinate_inverse_product_derivative, coordinate_inverse_derivative, coordinate_inverse_metric_compatible |
| Definitions | coordinateMetricInverse, coordinateLC |

## Explicit limitations

This is a coordinate-level theorem about coefficient arrays on the entire real model space, not the intrinsic fundamental theorem on an arbitrary smooth manifold. Pointwise signature and metric symmetry and smoothness remain hypotheses. Coordinate changes, open chart domains, chart gluing, connection on tangent-bundle sections, actual scalar Hessian and global stress conservation remain future obligations. No claim of physical unification, novel physics, quantum gravity or RH proof is made.

## Reproducible certification evidence

| Workflow | Run | Artifact | SHA-256 |
|---|---|---|---|
| Push | [45971179929](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45971179929) | [15184923609](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45971179929/artifacts/15184923609) | 88469b8a267d699e90c904645f9b65c470bfcec58eba4a26b469e8c58d0f7b9f |
| PR | [45971186228](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45971186228) | [15185227424](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45971186228/artifacts/15185227424) | 517c9af7f18492df869fb3e1a05d6bd2aaa6ecfad0bd48bd348247a20407779b |

Both logs record a successful 7356-job build, exact regression against the 198-declaration ledger, and 217 unique declarations (434 dependency reports per run). All records agree across runs and with both prior ledgers. The [permanent 217-declaration ledger](STEP3B_AXIOM_AUDIT.tsv) is extracted from both actual logs, not populated from an assumed dependency set. Raw artifacts expire in February 2027; their published digests are recorded, not independently rehashed. Node.js runtime deprecation warnings are unrelated to Lean verification.

Initial runs 45970199345 and 45970223128 failed during compilation with three direct errors and four affected declarations. The corrected revision fixes proof parenthesization, explicitly binds both product-rule summands (correcting a malformed free-index statement to the intended identity), and adjusts finite-sum and simplification tactics. No hypothesis was added and no intended statement was weakened. Both corrected runs passed. Consolidation changes no mathematical source.

## Reproduction and integration gates

```sh
lake update
lake exe cache get
lake build
lake env lean Covariance.lean
lake env lean Step3A.lean
lake env lean Step3B.lean
```

CI checks all five frozen file hashes, every declaration name/kind/module, both historical ledgers, all 217 exact dependencies against the new permanent ledger and the standard axiom whitelist. Both fresh integration workflows must pass. Keep PR #19 draft until explicit owner approval; preserve history with a regular merge and verify main after merging. Step 3C is not started.
