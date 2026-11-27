# Step 3C baseline v1.0 — verified 27 November 2026

Mathematical source commit: `9f174c8fde55d87b76eb8faa3861d153d22f8b90`
Branch: `paper-i-step3c-chart-compatibility`
Main observed before consolidation: `8da22c096eda3ee2df5c5ef834cf59cc71b999e5`
Status: verified source baseline; documentation consolidation only; merge requires owner approval.

## Reproducibility
- Push [46048362407](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/46048362407), job 140673181557: success.
- PR [46048372589](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/46048372589), job 140673215203: success.
- Lean 4.24.0 (797c613eb9b6d4ec95db23e3e00af9ac6657f24b); Mathlib v4.24.0; Lake 5.0.0-src+797c613.
- 268 theorems + 55 definitions = 323 explicit audit targets. Both runs passed compilation and dependency audit.
- Exact cross-run dependency agreement; zero forbidden axioms; 174/174, 198/198, 217/217 and 309/309 historical ledger matches.
- Dependency distribution: 319 (Classical.choice;Quot.sound;propext); 2 (Classical.choice); 2 (Classical.choice;Quot.sound).
- Axiom ledger: [STEP3C_AXIOM_AUDIT.tsv](STEP3C_AXIOM_AUDIT.tsv).
- Scope and limitations: [mathematical review](STEP3C_MATHEMATICAL_REVIEW.md).
- CI artifacts retain resolved dependency manifest and axiom logs.

## Frozen mathematical source and toolchain Git blob IDs

| Path | Git blob SHA |
|---|---|
| Covariance.lean | `8481ef5c36f41b016b9fe5d99c9747fea0cbb71e` |
| Step3A.lean | `c3ff5a4b4a4f23ee79bfa2342a68d35780fae98e` |
| Step3B.lean | `c68a9e0892b80328c265a69d10e2ce3d00ceccef` |
| Step3C.lean | `25b402a6b02162e40eb0be70c58259c8327d7822` |
| Step3CAtlas.lean | `7064bd7cd8094e191a6a710e16c3b0fbb930a340` |
| Step3CIntrinsic.lean | `31b3505564fbba2a52d77e9d64e453a70103ee96` |
| Step3CLeviCivita.lean | `a4ce60ffff2f7619d04c4a4ccffa61ded28883a4` |
| Step3CManifold.lean | `4121d3efe10ccb38f62e8f20f008bc505ebfa006` |
| Step3CSmooth.lean | `62085d8fb1b7ddc790d45db32426d6da6868b50c` |
| lakefile.toml | `75d3260342a8f871eb1335c95eb6e4a3c78b8c10` |
| lean-toolchain | `c00a53503cc3cc776c290056ed21ce7e5d80b083` |

## Accepted claim
For the assumed symmetric Lorentz-signature metric on the stated real four-dimensional manifold, the constructed intrinsic operator has the proven connection laws, actual manifold torsion freedom and metric compatibility, smooth closure under chartwise smoothness hypotheses, and uniqueness among arbitrary pointwise admissible operators on locally differentiable fields. It is not a proof of emergence of a physical Lorentzian spacetime, nor a bundled Mathlib connection theorem.

No mathematical source, prior ledger, main branch or Step 3D change is included in this consolidation.
