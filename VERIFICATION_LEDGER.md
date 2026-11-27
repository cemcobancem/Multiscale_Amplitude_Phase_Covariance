# Paper I verification ledger

## Current checkpoint — 27 November 2026

146 theorems and 28 definitions at ad2cf37bae34970a403d5782f8b613bd6c446828 passed both push and PR verification. See [baseline and evidence](STEP2_BASELINE_V1.0.md) and [individual dependencies](STEP2_AXIOM_AUDIT.tsv). Both consolidation runs (45948547155 and 45948556704) also passed with identical declaration dependencies. Owner-approved PR #17 was merged at 8bd9a1bcaeb2f297a890f364d75ede9ac9fb5c1a. Fresh main verification: [45955201543](https://github.com/cemcobancem/Multiscale_Amplitude_Phase_Covariance/actions/runs/45955201543).

## Historical ledger (26 November 2026; superseded status)

The 30-theorem geometry extension passed at commit 5d98659ed9d562a86d4cb5219eda2483c631817f (run 45882532312). The 34-theorem extension passed at bbdeef2a585abb02c926049b08eda8dd9586b45b (run 45882680413). Both used Lean 4.24.0 and Mathlib v4.24.0; all theorem dependencies were restricted to propext, Classical.choice, Quot.sound. No Lean errors or warnings were reported. The proof-verification artifacts contain the axiom logs and resolved manifest.

## Manuscript-to-proof correspondence

| Claim | Verified 34-theorem checkpoint | New extension (pending CI) | Remaining scope |
|---|---|---|---|
| Weighted covariance and nested coarse-graining | weighted_covariance, weighted_cross_covariance, nested_shift, nested_monotonicity, amplitude_phase_tensor | — | Package as intrinsic tensors / arbitrary partitions |
| Projective geometry and Fisher score | projective_block_gram, fisher_quarter_split, ensemble_normalized_weight_derivative | normalized_log_score | Construct normalized smooth projective map and differential intrinsically |
| Phase curvature and bound | finite_complex_gram_bound, finite_curvature_bound, phase_curvature_line_derivative | — | Compose the horizontal Gram and actual exterior derivative into manifold theorem |
| Residual stress and energy conditions | stress_reconstruction, residual_null_energy, ensemble_energy_flux_causal | — | Coordinate-free tensor and observer formulation |
| Conservation | flat_scalar_divergence_jet, flat_scalar_on_shell_jet | covariant_scalar_divergence_jet, covariant_ensemble_on_shell_jet | Establish product-rule expansion for Levi-Civita connection on Lorentzian manifold |
| Closure obstruction | no_mean_only_closure | affine_plane_wave_derivatives, plane_wave_mass_shell, plane_wave_kinetic_component, counterpropagating_stress_witness | Integrate explicit fields, mean inputs and stress into a single universal counterexample theorem |
| Arithmetic heat-trace benchmark | not formalized | finite_heat_trace_tail, laplace_remainder_interval | Prime counting, summation by parts, infinite limits, RH implication, asymptotic remainder |

The new extension has nine candidate declarations, for 43 total. Verification is pending. The verified baseline does not prove the physical hypothesis, spacetime emergence, or Riemann Hypothesis. The arithmetic theorem in the manuscript is conditional on the RH prime-counting estimate and remains separate from the scalar-field results. No unpublished manuscript is included in this public repo.
