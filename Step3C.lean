import Step3B
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Step 3C, first checkpoint: actual local chart transition laws.
The proofs use ambient representatives smooth at the overlap point and
local inverse identities on neighborhoods, not formal independent jets.
The intrinsic tangent-bundle connection and atlas gluing remain later
obligations within Step 3C. -/

namespace MicroMacro

open scoped BigOperators Topology
open Filter

section Transition

variable {E F W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Actual directional derivative of a scalar metric pairing. -/
noncomputable def chartDirectional (G : E → E → E → ℝ)
    (x w u v : E) : ℝ :=
  fderiv ℝ (fun y => G y u v) x w

/-- Actual second derivative of the chart transition. -/
noncomputable def chartHessian (f : E → F) (x u v : E) : F :=
  fderiv ℝ (fderiv ℝ f) x u v

/-- Metric pullback by the actual first derivative of a transition. -/
noncomputable def chartPullbackMetric (f : E → F)
    (g : F → F →L[ℝ] F →L[ℝ] ℝ) (x u v : E) : ℝ :=
  g (f x) (fderiv ℝ f x u) (fderiv ℝ f x v)

/-- The proposed coefficient transformation, using the actual derivative
of the inverse transition and the inhomogeneous second derivative. -/
noncomputable def chartPullbackConnection (f : E → F) (r : F → E)
    (C : F → F → F → F) (x u v : E) : E :=
  fderiv ℝ r (f x)
    (C (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) + chartHessian f x u v)

/-- Pointwise directional torsion-free and metric-compatible conditions.
C is the coefficient term for constant coordinate directions, not the
covariant derivative of arbitrary fields. -/
def chartLCAt (G : E → E → E → ℝ) (x : E)
    (C : E → E → E) : Prop :=
  (∀ u v, C u v = C v u) ∧
  (∀ w u v, chartDirectional G x w u v =
    G x (C w u) v + G x u (C w v))

/-- Coordinate expression of the covariant derivative of a vector field. -/
noncomputable def chartCovariantDerivative (C : E → E → E → E)
    (X : E → E) (x w : E) : E :=
  fderiv ℝ X x w + C x w (X x)

/-- A genuine derivative along a line is the Frechet derivative
evaluated on the line direction. -/
theorem chart_line_derivative (q : E → W) (x w : E)
    (hq : DifferentiableAt ℝ q x) :
    HasDerivAt (fun t : ℝ => q (x + t • w)) (fderiv ℝ q x w) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
    simpa only [zero_add, one_smul] using
      (hasDerivAt_const (0 : ℝ) x).add
        ((hasDerivAt_id' (0 : ℝ)).smul_const w)
  have hc := hq.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl
    (by simp : x = x + (0 : ℝ) • w)
  simpa only [Function.comp_def] using hc

/-- The inverse Jacobians are derived from local inverse identities. -/
theorem chart_inverse_jacobians (f : E → F) (r : F → E) (x : E)
    (hf : DifferentiableAt ℝ f x) (hr : DifferentiableAt ℝ r (f x))
    (h0 : r (f x) = x)
    (hl : r ∘ f =ᶠ[𝓝 x] id) (hh : f ∘ r =ᶠ[𝓝 (f x)] id) :
    (fderiv ℝ r (f x)).comp (fderiv ℝ f x) = ContinuousLinearMap.id ℝ E ∧
    (fderiv ℝ f x).comp (fderiv ℝ r (f x)) = ContinuousLinearMap.id ℝ F := by
  have hleft := hr.hasFDerivAt.comp x hf.hasFDerivAt
  have hleft' := hleft.congr_of_eventuallyEq hl.symm
  have hf' : HasFDerivAt f (fderiv ℝ f x) (r (f x)) := by
    rw [h0]
    exact hf.hasFDerivAt
  have hright := hf'.comp (f x) hr.hasFDerivAt
  have hright' := hright.congr_of_eventuallyEq hh.symm
  exact ⟨hleft'.unique (hasFDerivAt_id x),
    hright'.unique (hasFDerivAt_id (f x))⟩

/-- Mixed second derivatives commute for actual C-infinity transitions. -/
theorem chart_hessian_symmetric (f : E → F) (x u v : E)
    (hf : ContDiffAt ℝ (⊤ : WithTop ℕ∞) f x) :
    chartHessian f x u v = chartHessian f x v u := by
  exact (hf.isSymmSndFDerivAt (by simp)) u v

/-- Differentiation of a bundled metric with fixed tangent arguments. -/
theorem chart_directional_bilinear
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x w u v : E)
    (hg : DifferentiableAt ℝ g x) :
    chartDirectional (fun y a b => g y a b) x w u v =
      fderiv ℝ g x w u v := by
  have h := chart_line_derivative g x w hg
  have h1 := h.clm_apply (hasDerivAt_const (0 : ℝ) u)
  have h2 := h1.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hd : DifferentiableAt ℝ (fun y => g y u v) x :=
    (hg.clm_apply (differentiableAt_const u)).clm_apply (differentiableAt_const v)
  have h3 := chart_line_derivative (fun y => g y u v) x w hd
  unfold chartDirectional
  apply h3.unique
  simpa only [zero_smul, add_zero, map_zero, ContinuousLinearMap.add_apply] using h2

/-- Actual metric pullback derivative: chain rule plus both Jacobian
derivative terms. No derivative transformation is a hypothesis. -/
theorem chart_pullback_metric_derivative (f : E → F)
    (g : F → F →L[ℝ] F →L[ℝ] ℝ) (x w u v : E)
    (hf : DifferentiableAt ℝ f x)
    (hJ : DifferentiableAt ℝ (fderiv ℝ f) x)
    (hg : DifferentiableAt ℝ g (f x)) :
    chartDirectional (chartPullbackMetric f g) x w u v =
      chartDirectional (fun y a b => g y a b) (f x)
        (fderiv ℝ f x w) (fderiv ℝ f x u) (fderiv ℝ f x v) +
      g (f x) (chartHessian f x w u) (fderiv ℝ f x v) +
      g (f x) (fderiv ℝ f x u) (chartHessian f x w v) := by
  have hl := chart_line_derivative f x w hf
  have hG' := chart_line_derivative (fun y => g (f y)) x w (hg.comp x hf)
  rw [fderiv_comp' x hg hf, ContinuousLinearMap.comp_apply] at hG'
  have hj := chart_line_derivative (fderiv ℝ f) x w hJ
  have hu := hj.clm_apply (hasDerivAt_const (0 : ℝ) u)
  have hv := hj.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hu' : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • w) u)
      (chartHessian f x w u) 0 := by
    simpa only [chartHessian, zero_smul, add_zero, map_zero] using hu
  have hv' : HasDerivAt (fun t : ℝ => fderiv ℝ f (x + t • w) v)
      (chartHessian f x w v) 0 := by
    simpa only [chartHessian, zero_smul, add_zero, map_zero] using hv
  have hfull := (hG'.clm_apply hu').clm_apply hv'
  have hdiff : DifferentiableAt ℝ (fun y => chartPullbackMetric f g y u v) x :=
    ((hg.comp x hf).clm_apply (hJ.clm_apply (differentiableAt_const u))).clm_apply
      (hJ.clm_apply (differentiableAt_const v))
  have hactual := chart_line_derivative (fun y => chartPullbackMetric f g y u v) x w hdiff
  rw [chart_directional_bilinear g (f x) (fderiv ℝ f x w)
    (fderiv ℝ f x u) (fderiv ℝ f x v) hg]
  unfold chartDirectional
  apply hactual.unique
  simpa only [chartPullbackMetric, zero_smul, add_zero, ContinuousLinearMap.add_apply] using hfull

/-- The directional Koszul identity follows from the two LC conditions. -/
theorem chart_lc_lowered (G : E → E → E → ℝ) (x : E)
    (C : E → E → E) (hs : ∀ u v, G x u v = G x v u)
    (hc : chartLCAt G x C) (u v w : E) :
    2 * G x (C u v) w =
      chartDirectional G x u v w + chartDirectional G x v u w -
      chartDirectional G x w u v := by
  have h1 := hc.2 u v w
  have h2 := hc.2 v u w
  have h3 := hc.2 w u v
  rw [hc.1 v u] at h2
  rw [hc.1 w u, hc.1 w v] at h3
  rw [hs u (C v w)] at h2
  rw [hs u (C v w)] at h3
  rw [hs v (C u w)] at h1
  linarith

/-- A symmetric nondegenerate bilinear metric forces unique pointwise
coefficients, with no assumed transformation law. -/
theorem chart_lc_pointwise_unique (G : E → E → E → ℝ) (x : E)
    (b : E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ u v, G x u v = b u v)
    (hs : ∀ u v, G x u v = G x v u)
    (hn : ∀ u : E, (∀ v, b u v = 0) → u = 0)
    (C D : E → E → E) (hc : chartLCAt G x C) (hd : chartLCAt G x D) :
    C = D := by
  funext u v
  apply sub_eq_zero.mp
  apply hn
  intro w
  rw [map_sub, ContinuousLinearMap.sub_apply, ← hb, ← hb]
  linarith [chart_lc_lowered G x C hs hc u v w,
    chart_lc_lowered G x D hs hd u v w]

/-- A pulled-back nondegenerate symmetric metric remains so, using the
actual inverse Jacobians. -/
theorem chart_pullback_metric_nondegenerate (f : E → F) (r : F → E)
    (g : F → F →L[ℝ] F →L[ℝ] ℝ) (x : E)
    (hl : ∀ u : E, fderiv ℝ r (f x) (fderiv ℝ f x u) = u)
    (hr : ∀ v : F, fderiv ℝ f x (fderiv ℝ r (f x) v) = v)
    (hn : ∀ u : F, (∀ v, g (f x) u v = 0) → u = 0)
    (u : E) (hu : ∀ v, chartPullbackMetric f g x u v = 0) : u = 0 := by
  have hz : fderiv ℝ f x u = 0 := by
    apply hn
    intro v
    have h := hu (fderiv ℝ r (f x) v)
    unfold chartPullbackMetric at h
    rw [hr] at h
    exact h
  calc
    u = fderiv ℝ r (f x) (fderiv ℝ f x u) := (hl u).symm
    _ = 0 := by rw [hz, map_zero]

/-- Pushforward of the candidate coefficient term has the correct
inhomogeneous Hessian term, by the inverse Jacobian. -/
theorem chart_pullback_connection_forward (f : E → F) (r : F → E)
    (C : F → F → F → F) (x u v : E)
    (hr : ∀ z : F, fderiv ℝ f x (fderiv ℝ r (f x) z) = z) :
    fderiv ℝ f x (chartPullbackConnection f r C x u v) =
      C (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) + chartHessian f x u v := by
  unfold chartPullbackConnection
  exact hr _

/-- The transformed coefficients satisfy both LC conditions for the
actual pullback metric. This derives rather than assumes covariance. -/
theorem chart_pullback_connection_lc (f : E → F) (r : F → E)
    (g : F → F →L[ℝ] F →L[ℝ] ℝ) (C : F → F → F → F) (x : E)
    (hf : ContDiffAt ℝ (⊤ : WithTop ℕ∞) f x)
    (hg : DifferentiableAt ℝ g (f x))
    (hr : ∀ z : F, fderiv ℝ f x (fderiv ℝ r (f x) z) = z)
    (hc : chartLCAt (fun y a b => g y a b) (f x) (C (f x))) :
    chartLCAt (chartPullbackMetric f g) x (chartPullbackConnection f r C x) := by
  constructor
  · intro u v
    unfold chartPullbackConnection
    rw [hc.1 (fderiv ℝ f x u) (fderiv ℝ f x v),
      chart_hessian_symmetric f x u v hf]
  · intro w u v
    have hJ : DifferentiableAt ℝ (fderiv ℝ f) x :=
      (hf.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
    rw [chart_pullback_metric_derivative f g x w u v
      (hf.differentiableAt (by simp)) hJ hg,
      hc.2 (fderiv ℝ f x w) (fderiv ℝ f x u) (fderiv ℝ f x v)]
    unfold chartPullbackMetric
    rw [chart_pullback_connection_forward f r C x w u hr,
      chart_pullback_connection_forward f r C x w v hr, map_add,
      ContinuousLinearMap.add_apply, map_add]
    ring

/-- LC conditions depend only on the local metric germ. -/
theorem chart_lc_metric_germ (G H : E → E → E → ℝ) (x : E)
    (C : E → E → E)
    (he : ∀ u v, (fun y => G y u v) =ᶠ[𝓝 x] (fun y => H y u v)) :
    chartLCAt G x C → chartLCAt H x C := by
  intro hc
  refine ⟨hc.1, ?_⟩
  intro w u v
  have hder : chartDirectional G x w u v = chartDirectional H x w u v := by
    unfold chartDirectional
    rw [(he u v).fderiv_eq]
  have hval (a b : E) : G x a b = H x a b :=
    show (fun y => G y a b) x = (fun y => H y a b) x from (he a b).eq_of_nhds
  rw [← hder, hc.2 w u v, hval, hval]

/-- Actual nonlinear chart overlap law, proved by pointwise uniqueness.
Both metrics agree on a neighborhood after pullback; local inverse
identities provide the two inverse Jacobians. -/
theorem chart_connection_transformation (f : E → F) (r : F → E)
    (g : F → F →L[ℝ] F →L[ℝ] ℝ) (G : E → E → E → ℝ)
    (C : F → F → F → F) (D : E → E → E) (x : E)
    (hf : ContDiffAt ℝ (⊤ : WithTop ℕ∞) f x)
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
  have hj := chart_inverse_jacobians f r x (hf.differentiableAt (by simp)) hr h0 hl hh
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
  have hp := chart_pullback_connection_lc f r g C x hf hg hR hc
  have huniq := chart_lc_pointwise_unique (chartPullbackMetric f g) x b hb
    hsym hnon D (chartPullbackConnection f r C x) hd' hp
  rw [huniq]
  exact chart_pullback_connection_forward f r C x u v hR

/-- Differentiate a genuinely related vector field on an overlap. -/
theorem chart_related_vector_derivative (f : E → F)
    (X : E → E) (Y : F → F) (x w : E)
    (hf : DifferentiableAt ℝ f x)
    (hJ : DifferentiableAt ℝ (fderiv ℝ f) x)
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y (f x))
    (he : (fun z => fderiv ℝ f z (X z)) =ᶠ[𝓝 x] (fun z => Y (f z))) :
    fderiv ℝ Y (f x) (fderiv ℝ f x w) =
      fderiv ℝ f x (fderiv ℝ X x w) + chartHessian f x w (X x) := by
  have h := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_clm_apply hJ hX, fderiv_comp' x hY hf] at h
  have hw := congrArg (fun L : E →L[ℝ] F => L w) h
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, chartHessian] using hw.symm

/-- Actual covariant derivatives of related vector fields transform
tensorially when the coefficient overlap law holds. -/
theorem chart_covariant_derivative_natural (f : E → F)
    (C : E → E → E → E) (D : F → F → F → F)
    (X : E → E) (Y : F → F) (x w : E)
    (hf : DifferentiableAt ℝ f x)
    (hJ : DifferentiableAt ℝ (fderiv ℝ f) x)
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y (f x))
    (he : (fun z => fderiv ℝ f z (X z)) =ᶠ[𝓝 x] (fun z => Y (f z)))
    (hc : ∀ u v, fderiv ℝ f x (C x u v) =
      D (f x) (fderiv ℝ f x u) (fderiv ℝ f x v) + chartHessian f x u v) :
    fderiv ℝ f x (chartCovariantDerivative C X x w) =
      chartCovariantDerivative D Y (f x) (fderiv ℝ f x w) := by
  have hval : fderiv ℝ f x (X x) = Y (f x) :=
    Filter.EventuallyEq.eq_of_nhds he
  unfold chartCovariantDerivative
  rw [map_add, hc, chart_related_vector_derivative f X Y x w hf hJ hX hY he,
    hval]
  abel

end Transition

/-- Bridge to the existing finite-coordinate metric pairing on basis
vectors. -/
theorem chart_coordinate_pair_basis (g : Fin 4 → Fin 4 → ℝ) (i j : Fin 4) :
    coordinateMetricPair g (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) =
      g i j := by
  simp [coordinateMetricPair, Pi.single_apply, mul_ite]

/-- The actual scalar directional derivative of the coordinate metric
on basis vectors is the existing Step 3A partial derivative. -/
theorem chart_coordinate_directional_basis
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (x : Fin 4 → ℝ) (k i j : Fin 4) :
    chartDirectional (fun y u v => coordinateMetricPair (g y) u v)
      x (Pi.single k (1 : ℝ)) (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) =
      metricPartial g x k i j := by
  unfold chartDirectional metricPartial
  have he : (fun y => coordinateMetricPair (g y)
      (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ))) = fun y => g y i j := by
    funext y
    exact chart_coordinate_pair_basis (g y) i j
  rw [he]

end MicroMacro

#print axioms MicroMacro.chart_line_derivative
#print axioms MicroMacro.chart_inverse_jacobians
#print axioms MicroMacro.chart_hessian_symmetric
#print axioms MicroMacro.chart_directional_bilinear
#print axioms MicroMacro.chart_pullback_metric_derivative
#print axioms MicroMacro.chart_lc_lowered
#print axioms MicroMacro.chart_lc_pointwise_unique
#print axioms MicroMacro.chart_pullback_metric_nondegenerate
#print axioms MicroMacro.chart_pullback_connection_forward
#print axioms MicroMacro.chart_pullback_connection_lc
#print axioms MicroMacro.chart_lc_metric_germ
#print axioms MicroMacro.chart_connection_transformation
#print axioms MicroMacro.chart_related_vector_derivative
#print axioms MicroMacro.chart_covariant_derivative_natural
#print axioms MicroMacro.chart_coordinate_pair_basis
#print axioms MicroMacro.chart_coordinate_directional_basis
#print axioms MicroMacro.chartDirectional
#print axioms MicroMacro.chartHessian
#print axioms MicroMacro.chartPullbackMetric
#print axioms MicroMacro.chartPullbackConnection
#print axioms MicroMacro.chartLCAt
#print axioms MicroMacro.chartCovariantDerivative
