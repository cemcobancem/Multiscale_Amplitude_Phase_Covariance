# Paper I — Step 2 v1.0 consolidation candidate

**Status:** The 174-declaration source checkpoint is verified; integration CI and explicit owner approval are required before merging into main or creating the final release tag. Step 3 is out of scope.

## Frozen mathematical baseline

- Verified proof commit: `ad2cf37bae34970a403d5782f8b613bd6c446828`.
- Exact Covariance.lean Git blob: `8481ef5c36f41b016b9fe5d99c9747fea0cbb71e` (must be unchanged by consolidation).
- Main baseline: `15017f681226a6755dde8a95c2e8253d0ee3bc2c`.
- Lean 4.24.0; Mathlib v4.24.0 resolved at `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- 146 named theorems, 28 named definitions, 174 unique explicit axiom-audit commands. All 174 have the same dependency set: Classical.choice, Quot.sound, propext. No sorryAx or custom axioms in either successful checkpoint run.

## Dependency chain

PRs #11–#16 cover the progressive projective geometry, charts, zero-safe atlas, global manifold/polar identities, topology/global tensor, and tangent-fiber field. The certified source contains the repairs from the divergent branch tips `2dd1df1159f05808bf646b49dad5620b79974103`, `1b239fada36c6d26d4352a2c8337b5888814e479`, and `d4f85c6319798512148faacd1402984bb3fbab68`. Their histories are retained as additional parents of the consolidation commit, without replaying or changing certified mathematical code. PRs #13 and #14 are already ancestors. Earlier PRs #3–#9 belong to the Step 1 chain consolidated by #10; do not merge them again.

## Mathematical scope

Finite covariance and Gram identities, normalized projective pullbacks, gauge invariance, actual Frechet/Berry derivative identities, affine charts, quotient topology, fixed-model ChartedSpace/IsManifold, Hausdorffness and second-countability, polar covariance with positive component probabilities at the point, zero-safe intrinsic normalization, actual tangent-fiber real bilinearity, chart transition compatibility and jointly smooth preferred-chart tensor coefficients. See the theorem statements in Covariance.lean and the historical STEP2_*.md files.

The chartwise smooth field is not a separately bundled ContMDiff theorem on a fiber-product total space. The polar logarithm/phase expressions are not asserted at vanishing components. This is a formalization of stated finite-dimensional mathematical results, not an experimental validation, a quantum gravity derivation, a proof of RH, or a proof of global Lorentzian conservation. No further theorem is added in consolidation.

## Verified checkpoint evidence

| Workflow | Run | Artifact | SHA256 |
|---|---|---|---|
| Push | [45945169306](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45945169306) | [15174567210](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45945169306/artifacts/15174567210) | 8bc22cfa319168c3edc125342a2ecb3b689a41b60706196f5d7d55ae65daa177 |
| Pull request | [45945174330](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45945174330) | [15174322475](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45945174330/artifacts/15174322475) | 5bc6188c973902d591eeb77d25f9254734536d20262c1ca433578f38fa4feffb |

Both logs independently report 174 clean unique declarations; the permanent [declaration dependency ledger](STEP2_AXIOM_AUDIT.tsv) records their exact sets, extracted from both successful logs. The original CI artifacts contain the raw axiom log, Lean/Lake versions and resolved manifest and expire in February 2027; archive externally before expiry if long-term raw artifacts are needed.

## Reproduce and approve

```sh
lake update
lake exe cache get
lake build
lake env lean Covariance.lean
```

CI checks exactly 146 theorems and 28 definitions, complete unique audit coverage, allowed axioms and absence of sorryAx; uploads evidence. Consolidation CI must succeed on both push and PR. Confirm source blob, unchanged main, and owner approval before merging. Proposed final tag: `paper-i-step2-v1.0` (not created by this candidate). Lake package version remains 0.2.0; the Step 2 milestone version is distinct.

**Do not begin Step 3 in this branch.**
