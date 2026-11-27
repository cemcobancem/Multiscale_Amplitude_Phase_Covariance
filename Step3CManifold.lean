import Step3CAtlas
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! Actual local connection composition and Mathlib tangent-bundle descent.
Top of WithTop ENat is analytic order, not merely C-infinity.
Local metric/field representatives and local regularity remain explicit
premises. No global intrinsic Levi-Civita theorem is claimed. -/
namespace MicroMacro
open scoped BigOperators Topology Manifold ContDiff
open Filter Set Bundle
local notation "E4" => (Fin 4 → ℝ)
local notation "I4" => 𝓘(ℝ, E4)

noncomputable def chartConstructedCoefficients
    (g : E4 → Fin 4 → Fin 4 → ℝ) (x : E4) :
    E4 →L[ℝ] E4 →L[ℝ] E4 :=
  chartCoefficientBundle (metricChristoffel g (coordinateMetricInverse g) x)

/-- Compose the open-domain LC construction with actual overlap naturality. -/
theorem chart_constructed_covariant_overlap
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
    (hf : ContDiffAt ℝ (⊤ : WithTop ℕ∞) f x)
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
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  apply chart_covariant_derivative_natural f _ _ X Y x w
    (hf.differentiableAt (by simp)) hJ hX hY he
  intro u v
  exact chart_connection_transformation f r (fun q => chartMetricBundle (h q))
    (fun q a b => chartMetricBundle (g q) a b)
    (fun q a b => chartConstructedCoefficients h q a b)
    (fun a b => chartConstructedCoefficients g x a b) x
    hf hr h0 hl hh (chart_metric_bundle_differentiable_at h (f x) hhd)
    (chart_bundle_symmetry (h (f x)) (hhs (f x) hy))
    (chart_metric_bundle_nondegenerate (h (f x)) (hhs (f x) hy) hhsig)
    hm (chart_open_domain_directional_lift h t ht (f x) hy hhs hhd hhsig)
    (chart_open_domain_directional_lift g s hs x hx hgs hgd hgsig) u v

section LocalAxioms
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem chart_covariant_direction_add (C : E → E →L[ℝ] E →L[ℝ] E)
    (X : E → E) (x u v : E) :
    chartCovariantDerivative (fun z a b => C z a b) X x (u + v) =
      chartCovariantDerivative (fun z a b => C z a b) X x u +
      chartCovariantDerivative (fun z a b => C z a b) X x v := by
  simp only [chartCovariantDerivative, map_add, ContinuousLinearMap.add_apply]
  abel

theorem chart_covariant_direction_smul (C : E → E →L[ℝ] E →L[ℝ] E)
    (X : E → E) (x u : E) (a : ℝ) :
    chartCovariantDerivative (fun z b c => C z b c) X x (a • u) =
      a • chartCovariantDerivative (fun z b c => C z b c) X x u := by
  simp only [chartCovariantDerivative, map_smul, ContinuousLinearMap.smul_apply, smul_add]

theorem chart_covariant_field_add (C : E → E →L[ℝ] E →L[ℝ] E)
    (X Y : E → E) (x w : E)
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x) :
    chartCovariantDerivative (fun z a b => C z a b) (X + Y) x w =
      chartCovariantDerivative (fun z a b => C z a b) X x w +
      chartCovariantDerivative (fun z a b => C z a b) Y x w := by
  simp only [chartCovariantDerivative, fderiv_add hX hY, Pi.add_apply,
    ContinuousLinearMap.add_apply, map_add]
  abel

theorem chart_covariant_leibniz (C : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → ℝ) (X : E → E) (x w : E)
    (ha : DifferentiableAt ℝ a x) (hX : DifferentiableAt ℝ X x) :
    chartCovariantDerivative (fun z b c => C z b c) (a • X) x w =
      (fderiv ℝ a x w) • X x +
        a x • chartCovariantDerivative (fun z b c => C z b c) X x w := by
  simp only [chartCovariantDerivative, fderiv_smul ha hX,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_add]
  rw [show (a • X) x = a x • X x from rfl, map_smul]
  abel

theorem chart_covariant_torsion (C : E → E →L[ℝ] E →L[ℝ] E)
    (X Y : E → E) (x : E)
    (hs : ∀ u v, C x u v = C x v u) :
    chartCovariantDerivative (fun z a b => C z a b) Y x (X x) -
      chartCovariantDerivative (fun z a b => C z a b) X x (Y x) =
        fderiv ℝ Y x (X x) - fderiv ℝ X x (Y x) := by
  simp only [chartCovariantDerivative]
  rw [hs (X x) (Y x)]
  abel

theorem chart_covariant_metric_fields
    (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (C : E → E →L[ℝ] E →L[ℝ] E)
    (X Y : E → E) (x w : E)
    (hg : DifferentiableAt ℝ g x)
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x)
    (hc : chartLCAt (fun z u v => g z u v) x (fun u v => C x u v)) :
    fderiv ℝ (fun z => g z (X z) (Y z)) x w =
      g x (chartCovariantDerivative (fun z a b => C z a b) X x w) (Y x) +
      g x (X x) (chartCovariantDerivative (fun z a b => C z a b) Y x w) := by
  rw [fderiv_clm_apply (hg.clm_apply hX) hY, fderiv_clm_apply hg hX]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [← chart_directional_bilinear g x w (X x) (Y x) hg,
    hc.2 w (X x) (Y x)]
  simp only [chartCovariantDerivative, map_add, ContinuousLinearMap.add_apply]
  ring
end LocalAxioms

section Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
  [IsManifold I4 (⊤ : WithTop ℕ∞) M] [IsManifold I4 1 M]

noncomputable def chartManifoldTransition (a b : M) : E4 → E4 :=
  extChartAt I4 b ∘ (extChartAt I4 a).symm

theorem chart_manifold_transition_value (a b p : M)
    (ha : p ∈ (extChartAt I4 a).source) :
    chartManifoldTransition a b (extChartAt I4 a p) = extChartAt I4 b p := by
  unfold chartManifoldTransition
  rw [Function.comp_apply, (extChartAt I4 a).left_inv ha]

theorem chart_manifold_transition_regular (a b p : M)
    (ha : p ∈ (extChartAt I4 a).source)
    (hb : p ∈ (extChartAt I4 b).source) :
    ContDiffAt ℝ (⊤ : WithTop ℕ∞) (chartManifoldTransition a b)
      (extChartAt I4 a p) := by
  have ha' : p ∈ (chartAt E4 a).source := by simpa only [extChartAt_source] using ha
  have hb' : p ∈ (chartAt E4 b).source := by simpa only [extChartAt_source] using hb
  have h := OpenPartialHomeomorph.contDiffWithinAt_extend_coord_change'
    (I := I4) (n := (⊤ : WithTop ℕ∞))
    (IsManifold.chart_mem_maximalAtlas (I := I4) (n := (⊤ : WithTop ℕ∞)) b)
    (IsManifold.chart_mem_maximalAtlas (I := I4) (n := (⊤ : WithTop ℕ∞)) a) hb' ha'
  simpa [chartManifoldTransition, extChartAt, ModelWithCorners.range_eq_univ,
    contDiffWithinAt_univ] using h

theorem chart_manifold_inverse_germ (a b p : M)
    (ha : p ∈ (extChartAt I4 a).source)
    (hb : p ∈ (extChartAt I4 b).source) :
    chartManifoldTransition b a ∘ chartManifoldTransition a b =ᶠ[
      𝓝 (extChartAt I4 a p)] id := by
  have hm : map (extChartAt I4 a) (𝓝 p) = 𝓝 (extChartAt I4 a p) := by
    rw [map_extChartAt_nhds' ha, ModelWithCorners.range_eq_univ, nhdsWithin_univ]
  rw [← hm]
  change ∀ᶠ q in 𝓝 p,
    (chartManifoldTransition b a ∘ chartManifoldTransition a b)
      (extChartAt I4 a q) = id (extChartAt I4 a q)
  filter_upwards [show ∀ᶠ q in 𝓝 p, q ∈ (extChartAt I4 a).source from
      (isOpen_extChartAt_source a).mem_nhds ha,
    show ∀ᶠ q in 𝓝 p, q ∈ (extChartAt I4 b).source from
      (isOpen_extChartAt_source b).mem_nhds hb] with q hqa hqb
  rw [Function.comp_apply, chart_manifold_transition_value a b q hqa,
    chart_manifold_transition_value b a q hqb]
  rfl

theorem chart_manifold_tangent_jacobian (a b p : M) :
    tangentCoordChange I4 a b p =
      fderiv ℝ (chartManifoldTransition a b) (extChartAt I4 a p) := by
  rw [tangentCoordChange_def, ModelWithCorners.range_eq_univ, fderivWithin_univ]
  rfl

theorem chart_manifold_tangent_cocycle (a b c p : M) (v : E4)
    (ha : p ∈ (extChartAt I4 a).source)
    (hb : p ∈ (extChartAt I4 b).source)
    (hc : p ∈ (extChartAt I4 c).source) :
    tangentCoordChange I4 b c p (tangentCoordChange I4 a b p v) =
      tangentCoordChange I4 a c p v :=
  tangentCoordChange_comp (I := I4) ⟨⟨ha, hb⟩, hc⟩

/- Actual smooth tangent-section descent from compatible local values. -/
omit [IsManifold I4 (⊤ : WithTop ℕ∞) M] in
theorem chart_manifold_smooth_glue (n : WithTop ℕ∞)
    (value : M → M → E4)
    (overlap : ∀ a b p, p ∈ (extChartAt I4 a).source →
      p ∈ (extChartAt I4 b).source →
      tangentCoordChange I4 a b p (value a p) = value b p)
    (hreg : ∀ a, ContMDiffOn I4 I4 n (value a) (extChartAt I4 a).source) :
    ∃! S : ∀ p : M, TangentSpace I4 p,
      (∀ a p, p ∈ (extChartAt I4 a).source →
        tangentCoordChange I4 p a p (S p) = value a p) ∧
      ContMDiff I4 (ModelWithCorners.prod I4 I4) n (fun p => TotalSpace.mk' E4 p (S p)) := by
  let S : ∀ p : M, TangentSpace I4 p := fun p => value p p
  have hS (a p : M) (hp : p ∈ (extChartAt I4 a).source) :
      tangentCoordChange I4 p a p (S p) = value a p :=
    overlap p a p (mem_extChartAt_source p) hp
  refine ⟨S, ⟨hS, ?_⟩, ?_⟩
  · intro p
    apply (Bundle.contMDiffAt_section (n := n) (s := S) p).2
    have he : (fun q => (trivializationAt E4 (TangentSpace I4) p
      (TotalSpace.mk' E4 q (S q))).2) =ᶠ[𝓝 p] value p := by
      filter_upwards [show ∀ᶠ q in 𝓝 p, q ∈ (extChartAt I4 p).source from
        (isOpen_extChartAt_source p).mem_nhds (mem_extChartAt_source p)] with q hq
      change tangentCoordChange I4 q p q (S q) = value p q
      exact hS p q hq
    exact (he.contMDiffAt_iff).2
      ((hreg p p (mem_extChartAt_source p)).contMDiffAt
        ((isOpen_extChartAt_source p).mem_nhds (mem_extChartAt_source p)))
  · intro T hT
    funext p
    have ht := hT.1 p p (mem_extChartAt_source p)
    rw [tangentCoordChange_self (mem_extChartAt_source p)] at ht
    simpa using ht

/-- Compose the open-coordinate result with the actual Mathlib transition
and tangent Jacobian. Only metric and vector-field germ relations remain
as representation hypotheses; no connection covariance is assumed. -/
theorem chart_manifold_constructed_overlap
    (a b p : M) (ha : p ∈ (extChartAt I4 a).source)
    (hb : p ∈ (extChartAt I4 b).source)
    (g h : E4 → Fin 4 → Fin 4 → ℝ)
    (s t : Set E4) (hs : IsOpen s) (ht : IsOpen t)
    (hx : extChartAt I4 a p ∈ s) (hy : extChartAt I4 b p ∈ t)
    (hgs : ∀ z ∈ s, ∀ i j, g z i j = g z j i)
    (hhs : ∀ z ∈ t, ∀ i j, h z i j = h z j i)
    (hgd : ∀ i j, DifferentiableAt ℝ (fun z => g z i j) (extChartAt I4 a p))
    (hhd : ∀ i j, DifferentiableAt ℝ (fun z => h z i j) (extChartAt I4 b p))
    (hgsig : hasLorentzSignature (g (extChartAt I4 a p)))
    (hhsig : hasLorentzSignature (h (extChartAt I4 b p)))
    (X Y : E4 → E4) (w : E4)
    (hm : ∀ u v, (fun z => chartMetricBundle (g z) u v) =ᶠ[𝓝 (extChartAt I4 a p)]
      (fun z => chartPullbackMetric (chartManifoldTransition a b)
        (fun q => chartMetricBundle (h q)) z u v))
    (hX : DifferentiableAt ℝ X (extChartAt I4 a p))
    (hY : DifferentiableAt ℝ Y (extChartAt I4 b p))
    (he : (fun z => fderiv ℝ (chartManifoldTransition a b) z (X z)) =ᶠ[
      𝓝 (extChartAt I4 a p)] (fun z => Y (chartManifoldTransition a b z))) :
    tangentCoordChange I4 a b p (chartCovariantDerivative
      (fun z u v => chartConstructedCoefficients g z u v) X (extChartAt I4 a p) w) =
    chartCovariantDerivative (fun z u v => chartConstructedCoefficients h z u v)
      Y (extChartAt I4 b p) (tangentCoordChange I4 a b p w) := by
  let F := chartManifoldTransition a b
  let R := chartManifoldTransition b a
  let x := extChartAt I4 a p
  let y := extChartAt I4 b p
  have hF : F x = y := chart_manifold_transition_value a b p ha
  have hR : R y = x := chart_manifold_transition_value b a p hb
  have hf : ContDiffAt ℝ (⊤ : WithTop ℕ∞) F x :=
    chart_manifold_transition_regular a b p ha hb
  have hr : DifferentiableAt ℝ R (F x) := by
    rw [hF]
    exact (chart_manifold_transition_regular b a p hb ha).differentiableAt (by simp)
  have h0 : R (F x) = x := by rw [hF, hR]
  have hl : R ∘ F =ᶠ[𝓝 x] id := chart_manifold_inverse_germ a b p ha hb
  have hh : F ∘ R =ᶠ[𝓝 (F x)] id := by
    rw [hF]
    exact chart_manifold_inverse_germ b a p hb ha
  have hy' : F x ∈ t := by rw [hF]; exact hy
  have hhd' : ∀ i j, DifferentiableAt ℝ (fun z => h z i j) (F x) := by
    rw [hF]
    exact hhd
  have hhsig' : hasLorentzSignature (h (F x)) := by rw [hF]; exact hhsig
  have hY' : DifferentiableAt ℝ Y (F x) := by rw [hF]; exact hY
  have H := chart_constructed_covariant_overlap g h s t hs ht F R X Y x w
    hx hy' hgs hhs hgd hhd' hgsig hhsig' hf hr h0 hl hh hm hX hY' he
  rw [hF] at H
  rw [chart_manifold_tangent_jacobian a b p]
  exact H

/-- Glue the actual covariant derivative computed from chartwise metrics
and field representatives. Compatibility is derived using the preceding
overlap theorem and Mathlib tangent cocycle, not supplied for the result.
The local regularity premise still needs to be discharged from intrinsic
smooth metric and field data in a subsequent proof. -/
theorem chart_manifold_constructed_descent (n : WithTop ℕ∞)
    (g : M → E4 → Fin 4 → Fin 4 → ℝ)
    (s : M → Set E4) (hs : ∀ a, IsOpen (s a))
    (X : M → E4 → E4) (W : ∀ p : M, TangentSpace I4 p)
    (hdom : ∀ a p, p ∈ (extChartAt I4 a).source → extChartAt I4 a p ∈ s a)
    (hgs : ∀ a z, z ∈ s a → ∀ i j, g a z i j = g a z j i)
    (hgd : ∀ a p, p ∈ (extChartAt I4 a).source → ∀ i j,
      DifferentiableAt ℝ (fun z => g a z i j) (extChartAt I4 a p))
    (hgsig : ∀ a p, p ∈ (extChartAt I4 a).source →
      hasLorentzSignature (g a (extChartAt I4 a p)))
    (hX : ∀ a p, p ∈ (extChartAt I4 a).source →
      DifferentiableAt ℝ (X a) (extChartAt I4 a p))
    (hm : ∀ a b p, p ∈ (extChartAt I4 a).source →
      p ∈ (extChartAt I4 b).source → ∀ u v,
      (fun z => chartMetricBundle (g a z) u v) =ᶠ[𝓝 (extChartAt I4 a p)]
        (fun z => chartPullbackMetric (chartManifoldTransition a b)
          (fun q => chartMetricBundle (g b q)) z u v))
    (he : ∀ a b p, p ∈ (extChartAt I4 a).source →
      p ∈ (extChartAt I4 b).source →
      (fun z => fderiv ℝ (chartManifoldTransition a b) z (X a z)) =ᶠ[
        𝓝 (extChartAt I4 a p)] (fun z => X b (chartManifoldTransition a b z)))
    (hreg : ∀ a, ContMDiffOn I4 I4 n
      (fun p => chartCovariantDerivative
        (fun z u v => chartConstructedCoefficients (g a) z u v)
        (X a) (extChartAt I4 a p) (tangentCoordChange I4 p a p (W p)))
      (extChartAt I4 a).source) :
    ∃! S : ∀ p : M, TangentSpace I4 p,
      (∀ a p, p ∈ (extChartAt I4 a).source →
        tangentCoordChange I4 p a p (S p) =
          chartCovariantDerivative
            (fun z u v => chartConstructedCoefficients (g a) z u v)
            (X a) (extChartAt I4 a p) (tangentCoordChange I4 p a p (W p))) ∧
      ContMDiff I4 (ModelWithCorners.prod I4 I4) n (fun p => TotalSpace.mk' E4 p (S p)) := by
  let value : M → M → E4 := fun a p => chartCovariantDerivative
    (fun z u v => chartConstructedCoefficients (g a) z u v)
    (X a) (extChartAt I4 a p) (tangentCoordChange I4 p a p (W p))
  apply chart_manifold_smooth_glue n value _ hreg
  intro a b p ha hb
  have H := chart_manifold_constructed_overlap a b p ha hb (g a) (g b)
    (s a) (s b) (hs a) (hs b) (hdom a p ha) (hdom b p hb)
    (hgs a) (hgs b) (hgd a p ha) (hgd b p hb)
    (hgsig a p ha) (hgsig b p hb) (X a) (X b)
    (tangentCoordChange I4 p a p (W p)) (hm a b p ha hb)
    (hX a p ha) (hX b p hb) (he a b p ha hb)
  rw [chart_manifold_tangent_cocycle p a b p (W p)
    (mem_extChartAt_source p) ha hb] at H
  exact H

end Manifold
end MicroMacro

#print axioms MicroMacro.chart_constructed_covariant_overlap
#print axioms MicroMacro.chart_covariant_direction_add
#print axioms MicroMacro.chart_covariant_direction_smul
#print axioms MicroMacro.chart_covariant_field_add
#print axioms MicroMacro.chart_covariant_leibniz
#print axioms MicroMacro.chart_covariant_torsion
#print axioms MicroMacro.chart_covariant_metric_fields
#print axioms MicroMacro.chart_manifold_transition_value
#print axioms MicroMacro.chart_manifold_transition_regular
#print axioms MicroMacro.chart_manifold_inverse_germ
#print axioms MicroMacro.chart_manifold_tangent_jacobian
#print axioms MicroMacro.chart_manifold_tangent_cocycle
#print axioms MicroMacro.chart_manifold_smooth_glue
#print axioms MicroMacro.chartConstructedCoefficients
#print axioms MicroMacro.chartManifoldTransition

#print axioms MicroMacro.chart_manifold_constructed_overlap
#print axioms MicroMacro.chart_manifold_constructed_descent
