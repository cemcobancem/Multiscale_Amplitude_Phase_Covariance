# Paper I — Lean verification

Companion formal algebra for the research manuscript on multiscale amplitude–phase covariance.

## Verified baseline (14 theorems)
Commit `27ba94aa7ab2bf9df44ece5fe239adb028d82fd7` passed both the push and pull-request workflows on 2026-11-26. Actual Lean 4.24.0 logs confirm all 14 declarations and the axiom audit, with only `propext`, `Classical.choice`, `Quot.sound`. See [run 45881278544](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45881278544) and its proof-verification artifact.

## Extension (9 additional statements; verification pending)
The candidate additions formalize finite amplitude/phase tensor reconstruction and positivity, pointwise trace reversal, null energy, real and imaginary horizontal Gram components, the summed projective block identity, the Fisher splitting algebra and a conditional curvature inequality. Their precise hypotheses are in the source. The last result assumes the Gram bound and the curvature identification; it does not formally prove those differential-geometric steps.

Full differential geometry, covariant conservation, the on-shell field construction, and the analytic RH heat-trace theorem are still outside the verified scope. These are mathematical identities for classical scalar-field ensembles, not a proof of physical unification. The unpublished manuscript is not in this public repository.

## Reproduce
```sh
lake update
lake exe cache get
lake build
lake env lean Covariance.lean
```
CI audits every listed theorem against standard Lean axioms and archives the resolved manifest and logs. The extension is verified only when its own commit passes.
