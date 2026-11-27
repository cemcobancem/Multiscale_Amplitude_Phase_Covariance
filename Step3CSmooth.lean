import Step3CManifold

/-! Step 3C: ordinary C-infinity regularity, not analytic order.
The transition law in fact only requires C². Local regularity of
constructed coefficients is derived at nondegenerate metric points,
without requiring a globally nondegenerate ambient extension. -/
namespace MicroMacro
open scoped BigOperators Topology Manifold ContDiff
open Filter Set Bundle
local notation "E4" => (Fin 4 → ℝ)
local notation "I4" => 𝓘(ℝ, E4)

section C2
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem chart_hessian_symmetric_c2 (f : E → F) (x u v : E)
    (hf : ContDiffAt ℝ (2 : WithTop ℕ∞) f x) :
    chartHessian f x u v = chartHessian f x v u := by
  exact (hf.isSymmSndFDerivAt (by simp)) u v

theorem chart_pullback_connection_lc_c2 (f : E → F) (r : F → E)
    (g : F → F →L[ℝ] F →L[ℝ] ℝ) (C : F → F → F → F) (x : E)
    (hf : ContDiffAt ℝ (2 : WithTop ℕ∞) f x)
    (hg : DifferentiableAt ℝ g (f x))
    (hr : ∀ z : F, fderiv ℝ f x (fderiv ℝ r (f x) z) = z)
    (hc : chartLCAt (fun y a b => g y a b) (f x) (C (f x))) :
    chartLCAt (chartPullbackMetric f g) x (chartPullbackConnection f r C x) := by
  constructor
  · intro u v
    unfold chartPullbackConnection
    rw [hc.1 (fderiv ℝ f x u) (fderiv ℝ f x v),
      chart_hessian_symmetric_c2 f x u v hf]
  · intro w u v
    have hJ : DifferentiableAt ℝ (fderiv ℝ f) x :=
      (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    rw [chart_pullback_metric_derivative f g x w u v
      (hf.differentiableAt (by norm_num)) hJ hg,
      hc.2 (fderiv ℝ f x w) (fderiv ℝ f x u) (fderiv ℝ f x v)]
    unfold chartPullbackMetric
    rw [chart_pullback_connection_forward f r C x w u hr,
      chart_pullback_connection_forward f r C x w v hr, map_add,
      ContinuousLinearMap.add_apply, map_add]
    ring

theorem chart_connection_transformation_c2 (f : E → F) (r : F → E)
    (g : F → F →L[ℝ] F →L[ℝ] ℝ) (G : E → E → E → ℝ)
    (C : F → F → F → F) (D : E → E → E) (x : E)
    (hf : ContDiffAt ℝ (2 : WithTop ℕ∞) f x)
    (hr : DifferentiableAt ℝ r (f x)) (h0 : r (f x) = x)
    (hl : r ∘ f =ᶠ[𝓝 x] id) (hh : f ∘ r =ᶠ[𝓝 (f x)] id)
    (hg : DifferentiableAt ℝ g (f x))
    (hs : ∀ u v, g (f x) u v = g (f x) v u)
    (hn : ∀ u : F, (∀ v, g (f x) u v = 0) → u = 0)
    (he : ∀ u v, (fun y => G y u v) =ᶠ[𝓝 x]
      (fun y => chartPullbackMetric f g y u v))
    (hc : chartLCAt (fun y a b => g y a b) (f x) (C (f x)))
    (hd : chartLCAt G x D) (u v : E) :
    fderiv ℝ f x (D u v) =
      C (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) + chartHessian f x u v := by
  have hj := chart_inverse_jacobians f r x (hf.differentiableAt (by norm_num)) hr h0 hl hh
  have hL (z : E) : fderiv ℝ r (f x) (fderiv ℝ f x z) = z := by
    have h := congrArg (fun L : E →L[ℝ] E => L z) hj.1
    exact h
  have hR (z : F) : fderiv ℝ f x (fderiv ℝ r (f x) z) = z := by
    have h := congrArg (fun L : F →L[ℝ] F => L z) hj.2
    exact h
  let b : E →L[ℝ] E →L[ℝ] ℝ :=
    (g (f x)).bilinearComp (fderiv ℝ f x) (fderiv ℝ f x)
  have hb (a c : E) : chartPullbackMetric f g x a c = b a c := rfl
  have hsym (a c : E) :
      chartPullbackMetric f g x a c = chartPullbackMetric f g x c a :=
    hs _ _
  have hnon (a : E) : (∀ c, b a c = 0) → a = 0 := by
    intro ha
    apply chart_pullback_metric_nondegenerate f r g x hL hR hn a
    intro c
    rw [hb]
    exact ha c
  have hd' := chart_lc_metric_germ G (chartPullbackMetric f g) x D he hd
  have hp := chart_pullback_connection_lc_c2 f r g C x hf hg hR hc
  have huniq := chart_lc_pointwise_unique (chartPullbackMetric f g) x b hb
    hsym hnon D (chartPullbackConnection f r C x) hd' hp
  rw [huniq]
  exact chart_pullback_connection_forward f r C x u v hR

end C2

theorem chart_constructed_covariant_overlap_c2
    (g h : E4 → Fin 4 → Fin 4 → ℝ)
    (s t : Set E4) (hs : IsOpen s) (ht : IsOpen t)
    (f r X Y : E4 → E4) (x w : E4)
    (hx : x ∈ s) (hy : f x ∈ t)
    (hgs : ∀ z ∈ s, ∀ i j, g z i j = g z j i)
    (hhs : ∀ z ∈ t, ∀ i j, h z i j = h z j i)
    (hgd : ∀ i j, DifferentiableAt ℝ (fun z => g z i j) x)
    (hhd : ∀ i j, DifferentiableAt ℝ (fun z => h z i j) (f x))
    (hgsig : hasLorentzSignature (g x))
    (hhsig : hasLorentzSignature (h (f x)))
    (hf : ContDiffAt ℝ (2 : WithTop ℕ∞) f x)
    (hr : DifferentiableAt ℝ r (f x)) (h0 : r (f x) = x)
    (hl : r ∘ f =ᶠ[𝓝 x] id) (hh : f ∘ r =ᶠ[𝓝 (f x)] id)
    (hm : ∀ u v, (fun z => chartMetricBundle (g z) u v) =ᶠ[𝓝 x]
      (fun z => chartPullbackMetric f (fun q => chartMetricBundle (h q)) z u v))
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y (f x))
    (he : (fun z => fderiv ℝ f z (X z)) =ᶠ[𝓝 x] (fun z => Y (f z))) :
    fderiv ℝ f x (chartCovariantDerivative
      (fun z u v => chartConstructedCoefficients g z u v) X x w) =
    chartCovariantDerivative
      (fun z u v => chartConstructedCoefficients h z u v) Y (f x)
      (fderiv ℝ f x w) := by
  have hJ : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  apply chart_covariant_derivative_natural f _ _ X Y x w
    (hf.differentiableAt (by norm_num)) hJ hX hY he
  intro u v
  exact chart_connection_transformation_c2 f r (fun q => chartMetricBundle (h q))
    (fun q a b => chartMetricBundle (g q) a b)
    (fun q a b => chartConstructedCoefficients h q a b)
    (fun a b => chartConstructedCoefficients g x a b) x
    hf hr h0 hl hh (chart_metric_bundle_differentiable_at h (f x) hhd)
    (chart_bundle_symmetry (h (f x)) (hhs (f x) hy))
    (chart_metric_bundle_nondegenerate (h (f x)) (hhs (f x) hy) hhsig)
    hm (chart_open_domain_directional_lift h t ht (f x) hy hhs hhd hhsig)
    (chart_open_domain_directional_lift g s hs x hx hgs hgd hgsig) u v

/-- Ordinary smoothness implies the weaker C² transition hypothesis. -/
theorem chart_smooth_transition_c2 {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ 2 f x :=
  hf.of_le (by simp)

/-- The determinant inherits local regularity at any order. -/
theorem chart_det_regular_at {d : Type*} [Fintype d] [DecidableEq d]
    (g : E4 → Matrix d d ℝ) (x : E4) (n : WithTop ℕ∞)
    (hg : ∀ i j, ContDiffAt ℝ n (fun y => g y i j) x) :
    ContDiffAt ℝ n (fun y => (g y).det) x := by
  classical
  simp_rw [Matrix.det_apply']
  apply ContDiffAt.sum
  intro σ hσ
  apply contDiffAt_const.mul
  apply contDiffAt_prod
  intro i hi
  exact hg (σ i) i

theorem chart_adjugate_regular_at
    (g : E4 → Fin 4 → Fin 4 → ℝ) (x : E4) (n : WithTop ℕ∞)
    (hg : ∀ i j, ContDiffAt ℝ n (fun y => g y i j) x) (i j : Fin 4) :
    ContDiffAt ℝ n (fun y => (Matrix.of (g y)).adjugate i j) x := by
  simp_rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  apply contDiffAt_const.mul
  apply chart_det_regular_at
  intro a b
  exact hg (j.succAbove a) (i.succAbove b)

theorem chart_inverse_regular_at
    (g : E4 → Fin 4 → Fin 4 → ℝ) (x : E4) (n : WithTop ℕ∞)
    (hg : ∀ i j, ContDiffAt ℝ n (fun y => g y i j) x)
    (hsig : hasLorentzSignature (g x)) (i j : Fin 4) :
    ContDiffAt ℝ n (fun y => coordinateMetricInverse g y i j) x := by
  have hd := coordinate_det_ne_zero (g x) (lorentz_signature_no_kernel (g x) hsig)
  simp only [coordinateMetricInverse, Matrix.inv_def, Ring.inverse_eq_inv']
  change ContDiffAt ℝ n (fun y =>
    ((Matrix.of (g y)).det)⁻¹ * (Matrix.of (g y)).adjugate i j) x
  exact ((chart_det_regular_at (fun y => Matrix.of (g y)) x n hg).inv hd).mul
    (chart_adjugate_regular_at g x n hg i j)

theorem chart_partial_regular_at
    (g : E4 → Fin 4 → Fin 4 → ℝ) (x : E4) (n m : WithTop ℕ∞)
    (hn : n + 1 ≤ m)
    (hg : ∀ i j, ContDiffAt ℝ m (fun y => g y i j) x)
    (k i j : Fin 4) :
    ContDiffAt ℝ n (fun y => metricPartial g y k i j) x := by
  unfold metricPartial
  exact ((hg i j).fderiv_right hn).clm_apply contDiffAt_const

theorem chart_christoffel_regular_at
    (g : E4 → Fin 4 → Fin 4 → ℝ) (x : E4) (n m : WithTop ℕ∞)
    (hn : n + 1 ≤ m)
    (hg : ∀ i j, ContDiffAt ℝ m (fun y => g y i j) x)
    (hsig : hasLorentzSignature (g x)) (k i l : Fin 4) :
    ContDiffAt ℝ n (fun y => metricChristoffel g (coordinateMetricInverse g) y k i l) x := by
  have hle : n ≤ m := le_trans (by simp) hn
  unfold metricChristoffel christoffelFromJet christoffelFirst
  apply ContDiffAt.sum
  intro r hr
  exact (chart_inverse_regular_at g x n (fun a b => (hg a b).of_le hle) hsig r l).mul
    ((((chart_partial_regular_at g x n m hn hg k i r).add
       (chart_partial_regular_at g x n m hn hg i k r)).sub
       (chart_partial_regular_at g x n m hn hg r k i)).div_const 2)

theorem chart_constructed_coefficients_regular_at
    (g : E4 → Fin 4 → Fin 4 → ℝ) (x : E4) (n m : WithTop ℕ∞)
    (hn : n + 1 ≤ m)
    (hg : ∀ i j, ContDiffAt ℝ m (fun y => g y i j) x)
    (hsig : hasLorentzSignature (g x)) :
    ContDiffAt ℝ n (chartConstructedCoefficients g) x := by
  unfold chartConstructedCoefficients chartCoefficientBundle
  apply ContDiffAt.sum
  intro i hi
  apply ContDiffAt.sum
  intro j hj
  apply contDiffAt_const.smulRight
  apply contDiffAt_const.smulRight
  apply contDiffAt_pi.2
  intro l
  exact chart_christoffel_regular_at g x n m hn hg hsig i j l

/-- Local output regularity follows from regular metric and vector
representatives, not an assumed regular covariant derivative. -/
theorem chart_constructed_output_regular_at
    (g : E4 → Fin 4 → Fin 4 → ℝ) (X W : E4 → E4)
    (x : E4) (n m : WithTop ℕ∞) (hn : n + 1 ≤ m)
    (hg : ∀ i j, ContDiffAt ℝ m (fun y => g y i j) x)
    (hsig : hasLorentzSignature (g x))
    (hX : ContDiffAt ℝ m X x) (hW : ContDiffAt ℝ n W x) :
    ContDiffAt ℝ n (fun y => chartCovariantDerivative
      (fun z u v => chartConstructedCoefficients g z u v) X y (W y)) x := by
  have hle : n ≤ m := le_trans (by simp) hn
  have hC := chart_constructed_coefficients_regular_at g x n m hn hg hsig
  unfold chartCovariantDerivative
  exact ((hX.fderiv_right hn).clm_apply hW).add
    ((hC.clm_apply hW).clm_apply (hX.of_le hle))

/-- In particular C-infinity inputs give C-infinity output. -/
theorem chart_constructed_output_smooth_at
    (g : E4 → Fin 4 → Fin 4 → ℝ) (X W : E4 → E4) (x : E4)
    (hg : ∀ i j, ContDiffAt ℝ ∞ (fun y => g y i j) x)
    (hsig : hasLorentzSignature (g x))
    (hX : ContDiffAt ℝ ∞ X x) (hW : ContDiffAt ℝ ∞ W x) :
    ContDiffAt ℝ ∞ (fun y => chartCovariantDerivative
      (fun z u v => chartConstructedCoefficients g z u v) X y (W y)) x :=
  chart_constructed_output_regular_at g X W x ∞ ∞ (by simp) hg hsig hX hW

end MicroMacro

#print axioms MicroMacro.chart_hessian_symmetric_c2
#print axioms MicroMacro.chart_pullback_connection_lc_c2
#print axioms MicroMacro.chart_connection_transformation_c2
#print axioms MicroMacro.chart_constructed_covariant_overlap_c2
#print axioms MicroMacro.chart_smooth_transition_c2
#print axioms MicroMacro.chart_det_regular_at
#print axioms MicroMacro.chart_adjugate_regular_at
#print axioms MicroMacro.chart_inverse_regular_at
#print axioms MicroMacro.chart_partial_regular_at
#print axioms MicroMacro.chart_christoffel_regular_at
#print axioms MicroMacro.chart_constructed_coefficients_regular_at
#print axioms MicroMacro.chart_constructed_output_regular_at
#print axioms MicroMacro.chart_constructed_output_smooth_at
