import Step3CIntrinsic
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-! Intrinsic Levi-Civita laws and uniqueness. All comparisons are on
fields differentiable at the point under consideration, not on junk
values of total derivatives of nondifferentiable fields. The smooth
output theorem is the previously verified intrinsic descent theorem.
The uniqueness proof uses only the two geometric laws, not an assumed
coordinate coefficient representation of a competing operator. -/
namespace MicroMacro
open scoped BigOperators Topology Manifold ContDiff
open Filter Set Bundle
local notation "E4" => (Fin 4 → ℝ)
local notation "I4" => 𝓘(ℝ, E4)

section Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
  [IsManifold I4 2 M] [IsManifold I4 1 M]
local notation "Field4" => (∀ p : M, TangentSpace I4 p)
local notation "Metric4" => (∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
local notation "Local4" p => { X : Field4 //
  DifferentiableAt ℝ (chartIntrinsicField X p) (extChartAt I4 p p) }

/-- Actual manifold derivative of an extended chart agrees with the tangent frame. -/
theorem chart_intrinsic_mfderiv_chart (a p : M)
    (ha : p ∈ (extChartAt I4 a).source) :
    (mfderiv I4 I4 (extChartAt I4 a) p : E4 →L[ℝ] E4) =
      tangentCoordChange I4 p a p := by
  have h : p ∈ (chartAt E4 a).source := by simpa only [extChartAt_source] using ha
  rw [(hasMFDerivAt_extChartAt (I := I4) h).mfderiv]
  exact mfderiv_chartAt_eq_tangentCoordChange (I := I4) h

/-- The actual Mathlib pullback of a field along an inverse chart
agrees as a germ with the intrinsic field representative. -/
theorem chart_intrinsic_pullback_germ (X : Field4) (p : M) :
    (fun z : E4 => VectorField.mpullbackWithin I4 I4
      (extChartAt I4 p).symm X (range I4) z) =ᶠ[𝓝 (extChartAt I4 p p)]
      chartIntrinsicField X p := by
  filter_upwards [show ∀ᶠ z in 𝓝 (extChartAt I4 p p), z ∈ (extChartAt I4 p).target from
    extChartAt_target_mem_nhds (I := I4) p] with z hz
  let q := (extChartAt I4 p).symm z
  have hq : q ∈ (extChartAt I4 p).source := (extChartAt I4 p).map_target hz
  have hz' : extChartAt I4 p q = z := (extChartAt I4 p).right_inv hz
  have hInv := ContinuousLinearMap.inverse_eq
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I4) hz)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I4) hz)
  rw [VectorField.mpullbackWithin_apply, hInv]
  change (mfderiv I4 I4 (extChartAt I4 p) q) (X q) =
    chartIntrinsicField X p z
  rw [chart_intrinsic_mfderiv_chart p q hq]
  rfl

/-- Identify the canonical chart bracket with Mathlib's manifold Lie bracket. -/
theorem chart_intrinsic_bracket (X Y : Field4) (p : M) :
    VectorField.mlieBracket I4 X Y p =
      fderiv ℝ (chartIntrinsicField Y p) (extChartAt I4 p p) (X p) -
      fderiv ℝ (chartIntrinsicField X p) (extChartAt I4 p p) (Y p) := by
  have heX := chart_intrinsic_pullback_germ X p
  have heY := chart_intrinsic_pullback_germ Y p
  have hself : (mfderiv I4 I4 (extChartAt I4 p) p : E4 →L[ℝ] E4) =
      ContinuousLinearMap.id ℝ E4 := by
    rw [chart_intrinsic_mfderiv_chart p p (mem_extChartAt_source p)]
    ext v
    exact tangentCoordChange_self (mem_extChartAt_source p)
  simp only [VectorField.mlieBracket, VectorField.mlieBracketWithin_apply,
    Set.preimage_univ, Set.univ_inter, ModelWithCorners.range_eq_univ] at *
  rw [hself, ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply]
  simp only [VectorField.lieBracketWithin, fderivWithin_univ]
  rw [heX.fderiv_eq, heY.fderiv_eq, heX.eq_of_nhds, heY.eq_of_nhds,
    chart_intrinsic_field_value X p p (mem_extChartAt_source p),
    chart_intrinsic_field_value Y p p (mem_extChartAt_source p)]
  simp only [tangentCoordChange_self (mem_extChartAt_source p)]

theorem chart_intrinsic_metric_at_self (G : Metric4) (p : M) (u v : E4) :
    chartMetricBundle (chartIntrinsicComponents G p (extChartAt I4 p p)) u v =
      G p u v := by
  rw [chart_intrinsic_components_bundle, chart_intrinsic_form_value G p p
    (mem_extChartAt_source p)]
  simp only [tangentCoordChange_self (mem_extChartAt_source p)]

/-- A scalar metric pairing of actual fields agrees locally with its
coordinate expression. No overlap identity is assumed. -/
theorem chart_intrinsic_metric_field_germ (G : Metric4) (X Y : Field4) (p : M) :
    (fun z => G ((extChartAt I4 p).symm z)
      (X ((extChartAt I4 p).symm z)) (Y ((extChartAt I4 p).symm z))) =ᶠ[
      𝓝 (extChartAt I4 p p)]
    (fun z => chartMetricBundle (chartIntrinsicComponents G p z)
      (chartIntrinsicField X p z) (chartIntrinsicField Y p z)) := by
  filter_upwards [show ∀ᶠ z in 𝓝 (extChartAt I4 p p), z ∈ (extChartAt I4 p).target from
    extChartAt_target_mem_nhds (I := I4) p] with z hz
  let q := (extChartAt I4 p).symm z
  have hq : q ∈ (extChartAt I4 p).source := (extChartAt I4 p).map_target hz
  have hz' : extChartAt I4 p q = z := (extChartAt I4 p).right_inv hz
  change G q (X q) (Y q) = chartMetricBundle (chartIntrinsicComponents G p z)
    (chartIntrinsicField X p z) (chartIntrinsicField Y p z)
  rw [← hz', chart_intrinsic_components_bundle, chart_intrinsic_form_value G p q hq,
    chart_intrinsic_field_value X p q hq, chart_intrinsic_field_value Y p q hq,
    chart_manifold_tangent_cocycle q p q q (X q) (mem_extChartAt_source q) hq
      (mem_extChartAt_source q),
    chart_manifold_tangent_cocycle q p q q (Y q) (mem_extChartAt_source q) hq
      (mem_extChartAt_source q)]
  simp only [tangentCoordChange_self (mem_extChartAt_source q)]

/-- Scalar coordinate differentiation agrees with the actual manifold differential. -/
theorem chart_intrinsic_scalar_mfderiv (c : M → ℝ) (p : M) (w : E4)
    (hc : DifferentiableAt ℝ (fun z => c ((extChartAt I4 p).symm z))
      (extChartAt I4 p p)) :
    (mfderiv I4 𝓘(ℝ, ℝ) c p) w =
      fderiv ℝ (fun z => c ((extChartAt I4 p).symm z)) (extChartAt I4 p p) w := by
  let f : E4 → ℝ := fun z => c ((extChartAt I4 p).symm z)
  have h : MDifferentiableAt I4 𝓘(ℝ, ℝ) (f ∘ extChartAt I4 p) p :=
    hc.mdifferentiableAt.comp p (mdifferentiableAt_extChartAt (I := I4)
      (by simpa only [extChartAt_source] using mem_extChartAt_source (I := I4) p))
  have he : c =ᶠ[𝓝 p] f ∘ extChartAt I4 p := by
    filter_upwards [extChartAt_source_mem_nhds (I := I4) p] with q hq
    change c q = c ((extChartAt I4 p).symm (extChartAt I4 p q))
    rw [(extChartAt I4 p).left_inv hq]
  have hd := h.congr_of_eventuallyEq he
  rw [hd.mfderiv, ModelWithCorners.range_eq_univ, fderivWithin_univ]
  rfl

/-- Torsion-free identity using the actual manifold Lie bracket. -/
theorem chart_intrinsic_torsion (G : Metric4)
    (hs : ∀ p u v, G p u v = G p v u)
    (hsig : ∀ p, ∃ e : E4 ≃ₗ[ℝ] E4, ∀ u v, G p (e u) (e v) =
      coordinateMetricPair minkowskiMetric u v)
    (p : M) (X Y : Field4)
    (hd : ∀ i j, DifferentiableAt ℝ (fun z => chartIntrinsicComponents G p z i j)
      (extChartAt I4 p p)) :
    chartIntrinsicCovariantDerivative G X Y p -
      chartIntrinsicCovariantDerivative G Y X p = VectorField.mlieBracket I4 X Y p := by
  let x := extChartAt I4 p p
  let g := chartIntrinsicComponents G p
  let C := chartConstructedCoefficients g
  have hLC := chart_open_domain_directional_lift g Set.univ isOpen_univ x
    (Set.mem_univ _) (fun z _ => chart_intrinsic_components_symmetric G hs p z)
    hd (chart_intrinsic_signature G hsig p p (mem_extChartAt_source p))
  rw [chart_intrinsic_bracket]
  unfold chartIntrinsicCovariantDerivative
  have hX := chart_intrinsic_field_value X p p (mem_extChartAt_source p)
  have hY := chart_intrinsic_field_value Y p p (mem_extChartAt_source p)
  rw [tangentCoordChange_self (mem_extChartAt_source p)] at hX hY
  have h := chart_covariant_torsion C (chartIntrinsicField X p) (chartIntrinsicField Y p) x hLC.1
  rw [hX, hY] at h
  exact h

/-- Metric compatibility on actual tangent fields, with the actual manifold differential. -/
theorem chart_intrinsic_metric_compatible (G : Metric4)
    (hs : ∀ p u v, G p u v = G p v u)
    (hsig : ∀ p, ∃ e : E4 ≃ₗ[ℝ] E4, ∀ u v, G p (e u) (e v) =
      coordinateMetricPair minkowskiMetric u v)
    (p : M) (W X Y : Field4)
    (hd : ∀ i j, DifferentiableAt ℝ (fun z => chartIntrinsicComponents G p z i j)
      (extChartAt I4 p p))
    (hX : DifferentiableAt ℝ (chartIntrinsicField X p) (extChartAt I4 p p))
    (hY : DifferentiableAt ℝ (chartIntrinsicField Y p) (extChartAt I4 p p)) :
    (mfderiv I4 𝓘(ℝ, ℝ) (fun q => G q (X q) (Y q)) p) (W p) =
      G p (chartIntrinsicCovariantDerivative G W X p) (Y p) +
        G p (X p) (chartIntrinsicCovariantDerivative G W Y p) := by
  let x := extChartAt I4 p p
  let g := chartIntrinsicComponents G p
  let B := fun z => chartMetricBundle (g z)
  let C := chartConstructedCoefficients g
  have hLC := chart_open_domain_directional_lift g Set.univ isOpen_univ x
    (Set.mem_univ _) (fun z _ => chart_intrinsic_components_symmetric G hs p z)
    hd (chart_intrinsic_signature G hsig p p (mem_extChartAt_source p))
  have hB := chart_metric_bundle_differentiable_at g x hd
  have he := chart_intrinsic_metric_field_germ G X Y p
  have hc := ((hB.clm_apply hX).clm_apply hY).congr_of_eventuallyEq he
  rw [chart_intrinsic_scalar_mfderiv _ p (W p) hc, he.fderiv_eq]
  have H := chart_covariant_metric_fields B C (chartIntrinsicField X p)
    (chartIntrinsicField Y p) x (W p) hB hX hY hLC
  have hXp := chart_intrinsic_field_value X p p (mem_extChartAt_source p)
  have hYp := chart_intrinsic_field_value Y p p (mem_extChartAt_source p)
  rw [tangentCoordChange_self (mem_extChartAt_source p)] at hXp hYp
  rw [hXp, hYp] at H
  change _ = _ at H
  unfold B g x at H
  rw [chart_intrinsic_metric_at_self, chart_intrinsic_metric_at_self] at H
  exact H

/-- Any tangent value has a locally differentiable representative field.
No global partition of unity is needed for a pointwise uniqueness proof. -/
theorem chart_intrinsic_local_field_exists (p : M) (v : E4) :
    ∃ X : Local4 p, X.val p = v := by
  let X : Field4 := fun q => tangentCoordChange I4 p q q v
  have he : chartIntrinsicField X p =ᶠ[𝓝 (extChartAt I4 p p)] (fun _ : E4 => v) := by
    filter_upwards [show ∀ᶠ z in 𝓝 (extChartAt I4 p p), z ∈ (extChartAt I4 p).target from
      extChartAt_target_mem_nhds (I := I4) p] with z hz
    let q := (extChartAt I4 p).symm z
    have hq : q ∈ (extChartAt I4 p).source := (extChartAt I4 p).map_target hz
    change tangentCoordChange I4 q p q (tangentCoordChange I4 p q q v) = v
    rw [chart_manifold_tangent_cocycle p q p q v hq (mem_extChartAt_source q) hq]
    exact tangentCoordChange_self hq
  have h : DifferentiableAt ℝ (fun _ : E4 => v) (extChartAt I4 p p) :=
    (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : E4 => v) (extChartAt I4 p p)).differentiableAt (by simp)
  refine ⟨⟨X, he.differentiableAt_iff.mpr h⟩, ?_⟩
  exact tangentCoordChange_self (mem_extChartAt_source p)

/-- Intrinsic LC laws on locally differentiable fields at a point.
This imposes no coordinate coefficient form on the competing operator. -/
def chartPointLC (G : Metric4) (p : M)
    (D : Local4 p → Local4 p → TangentSpace I4 p) : Prop :=
  (∀ X Y, D X Y - D Y X = VectorField.mlieBracket I4 X.val Y.val p) ∧
  (∀ W X Y, (mfderiv I4 𝓘(ℝ, ℝ) (fun q => G q (X.val q) (Y.val q)) p) (W.val p) =
    G p (D W X) (Y.val p) + G p (X.val p) (D W Y))

/-- Existence for the constructed operator, using the intrinsic laws. -/
theorem chart_intrinsic_point_lc (G : Metric4)
    (hs : ∀ p u v, G p u v = G p v u)
    (hsig : ∀ p, ∃ e : E4 ≃ₗ[ℝ] E4, ∀ u v, G p (e u) (e v) =
      coordinateMetricPair minkowskiMetric u v)
    (p : M) (hd : ∀ i j, DifferentiableAt ℝ
      (fun z => chartIntrinsicComponents G p z i j) (extChartAt I4 p p)) :
    chartPointLC G p (fun X Y => chartIntrinsicCovariantDerivative G X.val Y.val p) := by
  constructor
  · intro X Y
    exact chart_intrinsic_torsion G hs hsig p X.val Y.val hd
  · intro W X Y
    exact chart_intrinsic_metric_compatible G hs hsig p W.val X.val Y.val hd X.property Y.property

/-- Uniqueness among arbitrary operators satisfying the intrinsic
torsion and metric laws, without assuming their linearity or a local
Christoffel representation. The difference is symmetric in its first
two slots and skew in its last two lowered slots, hence vanishes. -/
theorem chart_intrinsic_point_lc_unique (G : Metric4)
    (hs : ∀ p u v, G p u v = G p v u)
    (hsig : ∀ p, ∃ e : E4 ≃ₗ[ℝ] E4, ∀ u v, G p (e u) (e v) =
      coordinateMetricPair minkowskiMetric u v)
    (p : M) (P Q : Local4 p → Local4 p → TangentSpace I4 p)
    (hP : chartPointLC G p P) (hQ : chartPointLC G p Q) : P = Q := by
  let D := fun X Y => P X Y - Q X Y
  have hsym (X Y : Local4 p) : D X Y = D Y X := by
    dsimp [D]
    calc
      P X Y - Q X Y = (P X Y - P Y X) - (Q X Y - Q Y X) +
        (P Y X - Q Y X) := by abel
      _ = P Y X - Q Y X := by rw [hP.1 X Y, hQ.1 X Y, sub_self, zero_add]
  let A := fun X Y Z : Local4 p => G p (D X Y) (Z.val p)
  have ha (X Y Z : Local4 p) : A X Y Z = A Y X Z :=
    congrArg (fun w => G p w (Z.val p)) (hsym X Y)
  have hb (X Y Z : Local4 p) : A X Y Z = - A X Z Y := by
    have hp := hP.2 X Y Z
    have hq := hQ.2 X Y Z
    rw [hs p (Y.val p) (P X Z)] at hp
    rw [hs p (Y.val p) (Q X Z)] at hq
    dsimp [A, D]
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    linarith
  have hz (X Y Z : Local4 p) : A X Y Z = 0 := by
    linarith [ha X Y Z, hb Y X Z, ha Y Z X, hb Z Y X, ha Z X Y, hb X Z Y]
  funext X Y
  have hzero : (D X Y : E4) = 0 := by
    apply chart_metric_bundle_nondegenerate
      (chartIntrinsicComponents G p (extChartAt I4 p p))
      (chart_intrinsic_components_symmetric G hs p _)
      (chart_intrinsic_signature G hsig p p (mem_extChartAt_source p))
    intro v
    obtain ⟨Z, hZ⟩ := chart_intrinsic_local_field_exists p v
    rw [chart_intrinsic_metric_at_self, ← hZ]
    exact hz X Y Z
  exact sub_eq_zero.mp hzero

/-- Existence and uniqueness on the intrinsic pointwise domain of
locally differentiable fields, with no assumed chart formula for D. -/
theorem chart_intrinsic_global_lc_exists_unique (G : Metric4)
    (hs : ∀ p u v, G p u v = G p v u)
    (hsig : ∀ p, ∃ e : E4 ≃ₗ[ℝ] E4, ∀ u v, G p (e u) (e v) =
      coordinateMetricPair minkowskiMetric u v)
    (hd : ∀ p i j, DifferentiableAt ℝ
      (fun z => chartIntrinsicComponents G p z i j) (extChartAt I4 p p)) :
    ∃! D : ∀ p : M, Local4 p → Local4 p → TangentSpace I4 p,
      ∀ p, chartPointLC G p (D p) := by
  refine ⟨fun p X Y => chartIntrinsicCovariantDerivative G X.val Y.val p, ?_, ?_⟩
  · intro p
    exact chart_intrinsic_point_lc G hs hsig p (hd p)
  · intro D hD
    funext p
    exact chart_intrinsic_point_lc_unique G hs hsig p (D p) _
      (hD p) (chart_intrinsic_point_lc G hs hsig p (hd p))

/-- Smooth closure of the globally defined operator, using verified
intrinsic section gluing, not an additional regularity assumption. -/
theorem chart_intrinsic_operator_smooth (G : Metric4) (W X : Field4)
    (hs : ∀ p u v, G p u v = G p v u)
    (hsig : ∀ p, ∃ e : E4 ≃ₗ[ℝ] E4, ∀ u v, G p (e u) (e v) =
      coordinateMetricPair minkowskiMetric u v)
    [IsManifold I4 ∞ M]
    (hg : ∀ a p, p ∈ (extChartAt I4 a).source → ∀ i j,
      ContDiffAt ℝ ∞ (fun z => chartIntrinsicComponents G a z i j) (extChartAt I4 a p))
    (hX : ∀ a p, p ∈ (extChartAt I4 a).source →
      ContDiffAt ℝ ∞ (chartIntrinsicField X a) (extChartAt I4 a p))
    (hW : ∀ a p, p ∈ (extChartAt I4 a).source →
      ContDiffAt ℝ ∞ (chartIntrinsicField W a) (extChartAt I4 a p)) :
    ContMDiff I4 (ModelWithCorners.prod I4 I4) ∞
      (fun p => TotalSpace.mk' E4 p (chartIntrinsicCovariantDerivative G W X p)) := by
  obtain ⟨S, ⟨hS, hreg⟩, _⟩ := chart_intrinsic_global_section G X W hs hsig hg hX hW
  rw [chart_intrinsic_operator_identification G W X S hS] at hreg
  exact hreg

end Manifold
end MicroMacro

#print axioms MicroMacro.chart_intrinsic_mfderiv_chart
#print axioms MicroMacro.chart_intrinsic_pullback_germ
#print axioms MicroMacro.chart_intrinsic_bracket
#print axioms MicroMacro.chart_intrinsic_metric_at_self
#print axioms MicroMacro.chart_intrinsic_metric_field_germ
#print axioms MicroMacro.chart_intrinsic_scalar_mfderiv
#print axioms MicroMacro.chart_intrinsic_torsion
#print axioms MicroMacro.chart_intrinsic_metric_compatible
#print axioms MicroMacro.chart_intrinsic_local_field_exists
#print axioms MicroMacro.chart_intrinsic_point_lc
#print axioms MicroMacro.chart_intrinsic_point_lc_unique
#print axioms MicroMacro.chart_intrinsic_global_lc_exists_unique
#print axioms MicroMacro.chart_intrinsic_operator_smooth
#print axioms MicroMacro.chartPointLC
