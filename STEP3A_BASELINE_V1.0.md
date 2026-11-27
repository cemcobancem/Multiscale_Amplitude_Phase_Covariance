# Paper I — Step 3A v1.0 certified coordinate foundations

**Status:** The mathematical checkpoint and both consolidation workflows passed. Owner-approved [PR #18](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/pull/18) was merged into main on 27 November 2026 using a regular merge. The exact mathematical modules are preserved. Fresh main verification is the final release-verification gate; see the linked run below. Step 3B is not started.

## Frozen source and dependency inventory

- Certified mathematical commit: `998ba9d458368e983eec67dfe66226ff88e24009`.
- Parent Step 2 main baseline: `5602165bc44d2cb75691c6326549f38f7219ee96`.
- Approved consolidation commit: `c9c12e946c7a5719a2d8d2b1092164d7bdaada24`.
- Official mathematical baseline merge: `74579c4d78c6adc37a507e20b111ef279056be20` (regular merge with both parent histories retained).
- Exact verified integration and merge tree: `c54f012427673cb753cd686c688d3670fb89feb2`.
- Covariance.lean Git blob: `8481ef5c36f41b016b9fe5d99c9747fea0cbb71e` (146 theorems, 28 definitions).
- Step3A.lean Git blob: `c3ff5a4b4a4f23ee79bfa2342a68d35780fae98e` (16 theorems, 8 definitions).
- Total: 162 theorems, 36 definitions, 198 unique audited declarations.
- Lean 4.24.0, compiler revision 797c613eb9b6d4ec95db23e3e00af9ac6657f24b; Mathlib v4.24.0 resolved at f897ebcf72cd16f89ab4577d0c826cd14afaafc7.
- All 198 declarations in both runs depend exclusively on Classical.choice, Quot.sound, propext. No sorryAx or custom axioms. All original 174 dependencies match the unchanged Step 2 ledger exactly.

## Mathematical scope

The coordinate model is the whole real four-dimensional vector space. Signature is defined by congruence to the explicit Minkowski metric through an invertible real linear frame. The metric data require symmetry, a smooth symmetric inverse and a signature witness at every point.

The certified module proves both inverse identities and nondegeneracy under the supplied inverse identity; actual metric derivatives via fderiv and the coordinate-line chain rule; the Christoffel formula of the first and second kinds, lower-index contraction, torsion-free coefficients and coordinate metric compatibility. It reuses inverse_metric_contraction, tensorConnection and local_metric_stress_on_shell. The Minkowski example satisfies all coordinate-data conditions, has explicit diagonal (-1,+1,+1,+1), is its own inverse, and has vanishing Cartesian metric partials and Christoffel coefficients.

| Verified claim | Key declarations |
|---|---|
| Inverse identity and nondegeneracy | coordinate_inverse_left, coordinate_metric_no_kernel |
| Actual differentiation | metric_partial_symmetric, metric_partial_line_derivative |
| Christoffel identities | christoffel_jet_torsion_free, christoffel_lower_index, christoffel_jet_metric_compatible, lorentz_coordinate_connection |
| Minkowski witness | minkowski_signature, minkowski_symmetric, minkowski_inverse, minkowski_diagonal_signature, minkowski_coordinate_data, minkowski_partial_zero, minkowski_christoffel_zero |
| Reuse of local stress expression | lorentz_coordinate_stress_on_shell_jet |

## Explicit limitations

Inverse smoothness and Lorentzian frame existence are hypotheses, not derived from nondegeneracy alone. No global manifold, coordinate transformation law, global intrinsic connection, or general Levi-Civita existence/uniqueness theorem is supplied. The local stress result is still a jet identity under explicit Hessian symmetry and on-shell trace assumptions, not a global conservation theorem for actual fields. No physical unification, novelty, quantum gravity or RH proof is claimed. These are later research obligations; no new mathematics is introduced in this consolidation.

## Verification evidence

| Workflow | Run | Artifact | SHA-256 |
|---|---|---|---|
| Push | [45957818623](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45957818623) | [15179114611](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45957818623/artifacts/15179114611) | be48cf98b53d1db67f23824c5cb8a43fc7554719fc97f258876a19f3ad2a0d33 |
| Pull request | [45957824531](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45957824531) | [15180070315](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45957824531/artifacts/15180070315) | b95aa7c94f5eab98812f2879e8ce10646ea05304daf3b78714b4afb8b20142ce |

Both logs record a successful 7354-job build and a successful audit of all 162 theorems and 36 definitions. Each has 396 actual axiom dependency records, 198 unique declarations, no disagreement or missing/extra declarations. The [permanent expanded ledger](STEP3A_AXIOM_AUDIT.tsv) is derived from both actual logs and includes module and declaration type. [Step 2 ledger](STEP2_AXIOM_AUDIT.tsv) remains byte-for-byte unchanged. The raw CI artifacts expire in February 2027; archive separately for long-term raw evidence.

Initial runs 45957055683 and 45957070228 failed on four elaboration obligations. The corrected commit preserves all intended statements (one explicit coordinate-vector type annotation); both corrected runs passed. No further mathematical code is changed during consolidation.

## Consolidation and main verification evidence

| Workflow | Run | Result | Artifact |
|---|---|---|---|
| Consolidation push | [45963972578](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45963972578) | Passed, 198/198 | [15182412574](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45963972578/artifacts/15182412574) |
| Consolidation PR | [45963979722](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45963979722) | Passed, 198/198 | [15181738297](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45963979722/artifacts/15181738297) |
| Post-merge main | [45968623539](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45968623539) | Consult run for final result | See run |

The two consolidation runs independently matched all 198 expanded ledger rows and all 174 original ledger rows. Artifact SHA-256 digests respectively: `08e1841b398da752b52ae887d2b2843c4bc0e22f3b612f2ea928cfc7d4ee6aa3` and `840d90d739649d888562587e81dddef2b0dae29d334893fb234c8636d526918d`. Both mathematical modules, both ledgers, the toolchain, and the entire verified integration tree are unchanged at the official merge. The raw integration artifacts expire in February 2027.

## Reproduce

```sh
lake update
lake exe cache get
lake build
lake env lean Covariance.lean
lake env lean Step3A.lean
```

Consolidation CI checks the two frozen module blob IDs, exact complete inventory, original Step 2 ledger and exact expanded ledger dependency sets, plus the standard axiom whitelist. Both fresh integration runs passed; owner approval was received and PR #18 was merged regularly. Final release verification additionally requires successful post-merge main CI. Proposed milestone tag: `paper-i-step3a-v1.0`, targeting the official mathematical merge commit above after successful main CI. The available GitHub interface does not expose tag creation. Lake package version remains 0.2.0, distinct from the milestone. Step 3B is not started.
