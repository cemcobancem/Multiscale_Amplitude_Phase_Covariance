import Step3DBianchi

/-! Actual local curvature expansion, without an independent curvature jet.
The first two derivatives of the vector fields cancel by the product rule
and Hessian symmetry. The resulting expression is linear in each input. -/
namespace MicroMacro
open scoped BigOperators Topology Manifold ContDiff
open Filter Set Bundle
local notation "E4" => (Fin 4 → ℝ)
local notation "I4" => 𝓘(ℝ, E4)
local notation "Coeff4" => (E4 → E4 →L[ℝ] E4 →L[ℝ] E4)

/-- Pointwise curvature action of a bundled coordinate coefficient field. -/
noncomputable def chartLocalCurvature (C : Coeff4) (x u v w : E4) : E4 :=
  fderiv ℝ C x u v w - fderiv ℝ C x v u w +
    C x u (C x v w) - C x v (C x u w)

theorem chart_local_curvature_add_left (C : Coeff4) (x u u' v w : E4) :
    chartLocalCurvature C x (u + u') v w =
      chartLocalCurvature C x u v w + chartLocalCurvature C x u' v w := by
  simp only [chartLocalCurvature, map_add, ContinuousLinearMap.add_apply]
  abel

theorem chart_local_curvature_add_middle (C : Coeff4) (x u v v' w : E4) :
    chartLocalCurvature C x u (v + v') w =
      chartLocalCurvature C x u v w + chartLocalCurvature C x u v' w := by
  simp only [chartLocalCurvature, map_add, ContinuousLinearMap.add_apply]
  abel

theorem chart_local_curvature_add_right (C : Coeff4) (x u v w w' : E4) :
    chartLocalCurvature C x u v (w + w') =
      chartLocalCurvature C x u v w + chartLocalCurvature C x u v w' := by
  simp only [chartLocalCurvature, map_add]
  abel

theorem chart_local_curvature_smul_left (C : Coeff4) (x u v w : E4) (a : ℝ) :
    chartLocalCurvature C x (a • u) v w = a • chartLocalCurvature C x u v w := by
  simp only [chartLocalCurvature, map_smul, ContinuousLinearMap.smul_apply,
    smul_add, smul_sub]

theorem chart_local_curvature_smul_middle (C : Coeff4) (x u v w : E4) (a : ℝ) :
    chartLocalCurvature C x u (a • v) w = a • chartLocalCurvature C x u v w := by
  simp only [chartLocalCurvature, map_smul, ContinuousLinearMap.smul_apply,
    smul_add, smul_sub]

theorem chart_local_curvature_smul_right (C : Coeff4) (x u v w : E4) (a : ℝ) :
    chartLocalCurvature C x u v (a • w) = a • chartLocalCurvature C x u v w := by
  simp only [chartLocalCurvature, map_smul, smul_add, smul_sub]

/-- Product rule for one actual covariant derivative of a field. -/
theorem chart_curvature_nested_derivative (C : Coeff4) (Z V : E4 → E4)
    (x u : E4) (hC : DifferentiableAt ℝ C x)
    (hZ : ContDiffAt ℝ (2 : WithTop ℕ∞) Z x)
    (hV : DifferentiableAt ℝ V x) :
    fderiv ℝ (fun y => chartCovariantDerivative (fun z a b => C z a b) Z y (V y)) x u =
      chartHessian Z x u (V x) + fderiv ℝ Z x (fderiv ℝ V x u) +
      fderiv ℝ C x u (V x) (Z x) +
      C x (fderiv ℝ V x u) (Z x) + C x (V x) (fderiv ℝ Z x u) := by
  have hDZ : DifferentiableAt ℝ (fderiv ℝ Z) x :=
    (hZ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hz := hZ.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  unfold chartCovariantDerivative
  rw [fderiv_add (hDZ.clm_apply hV) ((hC.clm_apply hV).clm_apply hz),
    fderiv_clm_apply hDZ hV, fderiv_clm_apply (hC.clm_apply hV) hz,
    fderiv_clm_apply hC hV]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply, chartHessian]
  abel

/-- Actual coordinate covariant commutator reduces to the pointwise
trilinear curvature action, for arbitrary differentiable directions and
a twice continuously differentiable transported field. -/
theorem chart_local_curvature_commutator (C : Coeff4) (X Y Z : E4 → E4)
    (x : E4) (hC : DifferentiableAt ℝ C x)
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x)
    (hZ : ContDiffAt ℝ (2 : WithTop ℕ∞) Z x) :
    chartCovariantDerivative (fun z a b => C z a b)
      (fun y => chartCovariantDerivative (fun z a b => C z a b) Z y (Y y)) x (X x) -
    chartCovariantDerivative (fun z a b => C z a b)
      (fun y => chartCovariantDerivative (fun z a b => C z a b) Z y (X y)) x (Y x) -
    chartCovariantDerivative (fun z a b => C z a b) Z x
      (fderiv ℝ Y x (X x) - fderiv ℝ X x (Y x)) =
      chartLocalCurvature C x (X x) (Y x) (Z x) := by
  change
    (fderiv ℝ (fun y => chartCovariantDerivative (fun z a b => C z a b) Z y (Y y)) x (X x) +
      C x (X x) (chartCovariantDerivative (fun z a b => C z a b) Z x (Y x))) -
    (fderiv ℝ (fun y => chartCovariantDerivative (fun z a b => C z a b) Z y (X y)) x (Y x) +
      C x (Y x) (chartCovariantDerivative (fun z a b => C z a b) Z x (X x))) - _ = _
  rw [chart_curvature_nested_derivative C Z Y x (X x) hC hZ hY,
    chart_curvature_nested_derivative C Z X x (Y x) hC hZ hX,
    chart_hessian_symmetric_c2 Z x (X x) (Y x) hZ]
  simp only [chartCovariantDerivative, chartLocalCurvature, map_add, map_sub,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  abel

/-- A basis evaluation of the derivative uses the actual derivative
of the coefficient function, not an independent array. -/
theorem chart_curvature_coefficient_partial
    (Γ : E4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (x : E4)
    (hC : DifferentiableAt ℝ (fun y => chartCoefficientBundle (Γ y)) x)
    (i j k l : Fin 4) :
    (fderiv ℝ (fun y => chartCoefficientBundle (Γ y)) x (Pi.single i (1 : ℝ))
      (Pi.single j (1 : ℝ)) (Pi.single k (1 : ℝ))) l =
      curvatureConnectionPartial Γ x i j k l := by
  have hd := chart_line_derivative (fun y => chartCoefficientBundle (Γ y)) x
    (Pi.single i (1 : ℝ)) hC
  have h1 := hd.clm_apply (hasDerivAt_const (0 : ℝ) (Pi.single j (1 : ℝ) : E4))
  have h2 := h1.clm_apply (hasDerivAt_const (0 : ℝ) (Pi.single k (1 : ℝ) : E4))
  have h3 := (ContinuousLinearMap.proj (R := ℝ) l : E4 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) h2
  have hfun : (fun t : ℝ => (chartCoefficientBundle (Γ (x + t • Pi.single i (1 : ℝ)))
      (Pi.single j (1 : ℝ)) (Pi.single k (1 : ℝ))) l) =
      fun t : ℝ => Γ (x + t • Pi.single i (1 : ℝ)) j k l := by
    funext t
    rw [chart_coefficient_bundle_basis]
  have hscalar : DifferentiableAt ℝ (fun y => Γ y j k l) x := by
    have hh := (hC.clm_apply (differentiableAt_const (c := (Pi.single j (1 : ℝ) : E4)))).clm_apply
      (differentiableAt_const (c := (Pi.single k (1 : ℝ) : E4)))
    have he : (fun y => Γ y j k l) = fun y => (chartCoefficientBundle (Γ y)
        (Pi.single j (1 : ℝ)) (Pi.single k (1 : ℝ))) l := by
      funext y
      rw [chart_coefficient_bundle_basis]
    rw [he]
    exact ((ContinuousLinearMap.proj (R := ℝ) l : E4 →L[ℝ] ℝ).differentiableAt.comp x hh)
  have h4 := chart_line_derivative (fun y => Γ y j k l) x (Pi.single i (1 : ℝ)) hscalar
  unfold curvatureConnectionPartial
  apply HasDerivAt.unique _ h4
  simpa only [Function.comp_def, ContinuousLinearMap.proj_apply, zero_smul,
    add_zero, map_zero, ContinuousLinearMap.add_apply, hfun] using h3

theorem chart_coefficient_basis_left
    (A : Fin 4 → Fin 4 → Fin 4 → ℝ) (i l : Fin 4) (v : E4) :
    (chartCoefficientBundle A (Pi.single i (1 : ℝ)) v) l =
      ∑ m : Fin 4, v m * A i m l := by
  classical
  simp [chartCoefficientBundle, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, Pi.single_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

/-- The pointwise curvature action agrees on coordinate basis vectors
with the previously verified component expression. -/
theorem chart_local_curvature_coordinate
    (Γ : E4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (x : E4)
    (hC : DifferentiableAt ℝ (fun y => chartCoefficientBundle (Γ y)) x)
    (i j k l : Fin 4) :
    chartLocalCurvature (fun y => chartCoefficientBundle (Γ y)) x
      (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) (Pi.single k (1 : ℝ)) l =
      coordinateRiemann Γ x i j k l := by
  simp only [chartLocalCurvature, Pi.add_apply, Pi.sub_apply,
    chart_curvature_coefficient_partial Γ x hC, chart_coefficient_bundle_basis,
    chart_coefficient_basis_left, coordinateRiemann, Finset.sum_sub_distrib]
  ring

section Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
  [IsManifold I4 2 M] [IsManifold I4 1 M]
set_option quotPrecheck false in
local notation "Field4" => (∀ p : M, TangentSpace I4 p)
set_option quotPrecheck false in
local notation "Metric4" => (∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)

/-- A field agreement on a neighborhood induces agreement of its actual
coordinate representatives, using the extended chart neighborhood map. -/
theorem chart_curvature_field_locality (X Y : Field4) (p : M)
    (h : ∀ᶠ q in 𝓝 p, X q = Y q) :
    chartIntrinsicField X p =ᶠ[𝓝 (extChartAt I4 p p)] chartIntrinsicField Y p := by
  have hm : map (extChartAt I4 p) (𝓝 p) = 𝓝 (extChartAt I4 p p) := by
    rw [map_extChartAt_nhds' (mem_extChartAt_source p), ModelWithCorners.range_eq_univ,
      nhdsWithin_univ]
  rw [← hm]
  change ∀ᶠ q in 𝓝 p, chartIntrinsicField X p (extChartAt I4 p q) =
    chartIntrinsicField Y p (extChartAt I4 p q)
  filter_upwards [h, extChartAt_source_mem_nhds (I := I4) p] with q hq hs
  rw [chart_intrinsic_field_value X p q hs, chart_intrinsic_field_value Y p q hs, hq]

theorem chart_curvature_covariant_locality (G : Metric4) (X X' Y Y' : Field4) (p : M)
    (hx : X p = X' p) (hy : ∀ᶠ q in 𝓝 p, Y q = Y' q) :
    chartIntrinsicCovariantDerivative G X Y p = chartIntrinsicCovariantDerivative G X' Y' p := by
  have he := chart_curvature_field_locality Y Y' p hy
  unfold chartIntrinsicCovariantDerivative chartCovariantDerivative
  rw [he.fderiv_eq, he.eq_of_nhds, hx]

/-- The canonical chart formula holds as a germ for the actual globally
constructed covariant derivative. The output need not be assumed smooth. -/
theorem chart_curvature_covariant_germ (G : Metric4) (X Y : Field4)
    (hs : ∀ p u v, G p u v = G p v u)
    (hsig : ∀ p, ∃ e : E4 ≃ₗ[ℝ] E4, ∀ u v, G p (e u) (e v) =
      coordinateMetricPair minkowskiMetric u v)
    [IsManifold I4 ∞ M]
    (hg : ∀ a p, p ∈ (extChartAt I4 a).source → ∀ i j,
      ContDiffAt ℝ ∞ (fun z => chartIntrinsicComponents G a z i j) (extChartAt I4 a p))
    (hX : ∀ a p, p ∈ (extChartAt I4 a).source →
      ContDiffAt ℝ ∞ (chartIntrinsicField X a) (extChartAt I4 a p))
    (hY : ∀ a p, p ∈ (extChartAt I4 a).source →
      ContDiffAt ℝ ∞ (chartIntrinsicField Y a) (extChartAt I4 a p))
    (a p : M) (ha : p ∈ (extChartAt I4 a).source) :
    chartIntrinsicField (chartIntrinsicCovariantDerivative G X Y) a =ᶠ[𝓝 (extChartAt I4 a p)]
      (fun z => chartCovariantDerivative
        (fun t u v => chartConstructedCoefficients (chartIntrinsicComponents G a) t u v)
        (chartIntrinsicField Y a) z (chartIntrinsicField X a z)) := by
  obtain ⟨S, ⟨hS, _⟩, _⟩ := chart_intrinsic_global_section G Y X hs hsig hg hY hX
  have hid := chart_intrinsic_operator_identification G X Y S hS
  rw [hid] at hS
  have hm : map (extChartAt I4 a) (𝓝 p) = 𝓝 (extChartAt I4 a p) := by
    rw [map_extChartAt_nhds' ha, ModelWithCorners.range_eq_univ, nhdsWithin_univ]
  rw [← hm]
  change ∀ᶠ q in 𝓝 p, chartIntrinsicField (chartIntrinsicCovariantDerivative G X Y) a
    (extChartAt I4 a q) = _
  filter_upwards [(isOpen_extChartAt_source a).mem_nhds ha] with q hq
  rw [chart_intrinsic_field_value _ a q hq, hS a q hq,
    chart_intrinsic_field_value X a q hq]

/-- Smoothness of the actual coordinate representatives of the
covariant output, obtained from the verified global construction. -/
theorem chart_curvature_covariant_chart_smooth (G : Metric4) (X Y : Field4)
    (hs : ∀ p u v, G p u v = G p v u)
    (hsig : ∀ p, ∃ e : E4 ≃ₗ[ℝ] E4, ∀ u v, G p (e u) (e v) =
      coordinateMetricPair minkowskiMetric u v)
    [IsManifold I4 ∞ M]
    (hg : ∀ a p, p ∈ (extChartAt I4 a).source → ∀ i j,
      ContDiffAt ℝ ∞ (fun z => chartIntrinsicComponents G a z i j) (extChartAt I4 a p))
    (hX : ∀ a p, p ∈ (extChartAt I4 a).source →
      ContDiffAt ℝ ∞ (chartIntrinsicField X a) (extChartAt I4 a p))
    (hY : ∀ a p, p ∈ (extChartAt I4 a).source →
      ContDiffAt ℝ ∞ (chartIntrinsicField Y a) (extChartAt I4 a p))
    (a p : M) (ha : p ∈ (extChartAt I4 a).source) :
    ContDiffAt ℝ ∞ (chartIntrinsicField (chartIntrinsicCovariantDerivative G X Y) a)
      (extChartAt I4 a p) := by
  have he := chart_curvature_covariant_germ G X Y hs hsig hg hX hY a p ha
  have h := chart_constructed_output_smooth_at (chartIntrinsicComponents G a)
    (chartIntrinsicField Y a) (chartIntrinsicField X a) (extChartAt I4 a p)
    (hg a p ha) (chart_intrinsic_signature G hsig a p ha) (hY a p ha) (hX a p ha)
  exact h.congr_of_eventuallyEq he

/-- Actual intrinsic curvature is the coordinate pointwise action in
the canonical tangent chart. This removes all derivatives of the field
extensions from the final expression. -/
theorem chart_intrinsic_curvature_pointwise (G : Metric4) (X Y Z : Field4)
    (hs : ∀ p u v, G p u v = G p v u)
    (hsig : ∀ p, ∃ e : E4 ≃ₗ[ℝ] E4, ∀ u v, G p (e u) (e v) =
      coordinateMetricPair minkowskiMetric u v)
    [IsManifold I4 ∞ M]
    (hg : ∀ a p, p ∈ (extChartAt I4 a).source → ∀ i j,
      ContDiffAt ℝ ∞ (fun z => chartIntrinsicComponents G a z i j) (extChartAt I4 a p))
    (hX : ∀ a p, p ∈ (extChartAt I4 a).source →
      ContDiffAt ℝ ∞ (chartIntrinsicField X a) (extChartAt I4 a p))
    (hY : ∀ a p, p ∈ (extChartAt I4 a).source →
      ContDiffAt ℝ ∞ (chartIntrinsicField Y a) (extChartAt I4 a p))
    (hZ : ∀ a p, p ∈ (extChartAt I4 a).source →
      ContDiffAt ℝ ∞ (chartIntrinsicField Z a) (extChartAt I4 a p))
    (p : M) :
    chartIntrinsicRiemann G X Y Z p =
      chartLocalCurvature (chartConstructedCoefficients (chartIntrinsicComponents G p))
        (extChartAt I4 p p) (X p) (Y p) (Z p) := by
  let x := extChartAt I4 p p
  let C := chartConstructedCoefficients (chartIntrinsicComponents G p)
  have hp := mem_extChartAt_source (I := I4) p
  have heY := chart_curvature_covariant_germ G Y Z hs hsig hg hY hZ p p hp
  have heX := chart_curvature_covariant_germ G X Z hs hsig hg hX hZ p p hp
  have hvX := chart_intrinsic_field_value X p p hp
  have hvY := chart_intrinsic_field_value Y p p hp
  have hvZ := chart_intrinsic_field_value Z p p hp
  rw [tangentCoordChange_self hp] at hvX hvY hvZ
  have hC : DifferentiableAt ℝ C x :=
    (chart_constructed_coefficients_regular_at (chartIntrinsicComponents G p) x 1 ∞
      (by simp) (hg p p hp) (chart_intrinsic_signature G hsig p p hp)).differentiableAt (by simp)
  have H := chart_local_curvature_commutator C (chartIntrinsicField X p)
    (chartIntrinsicField Y p) (chartIntrinsicField Z p) x hC
    ((hX p p hp).differentiableAt (by simp)) ((hY p p hp).differentiableAt (by simp))
    ((hZ p p hp).of_le (by simp))
  change chartIntrinsicRiemann G X Y Z p = chartLocalCurvature C x (X p) (Y p) (Z p)
  unfold chartIntrinsicRiemann chartIntrinsicCovariantDerivative
  simp only [chartCovariantDerivative] at H ⊢
  rw [heY.fderiv_eq, heY.eq_of_nhds, heX.fderiv_eq, heX.eq_of_nhds,
    chart_intrinsic_bracket X Y p]
  rw [hvX, hvY, hvZ] at H
  exact H

end Manifold
end MicroMacro

#print axioms MicroMacro.chartLocalCurvature
#print axioms MicroMacro.chart_local_curvature_add_left
#print axioms MicroMacro.chart_local_curvature_add_middle
#print axioms MicroMacro.chart_local_curvature_add_right
#print axioms MicroMacro.chart_local_curvature_smul_left
#print axioms MicroMacro.chart_local_curvature_smul_middle
#print axioms MicroMacro.chart_local_curvature_smul_right
#print axioms MicroMacro.chart_curvature_nested_derivative
#print axioms MicroMacro.chart_local_curvature_commutator
#print axioms MicroMacro.chart_curvature_coefficient_partial
#print axioms MicroMacro.chart_coefficient_basis_left
#print axioms MicroMacro.chart_local_curvature_coordinate
#print axioms MicroMacro.chart_curvature_field_locality
#print axioms MicroMacro.chart_curvature_covariant_locality
#print axioms MicroMacro.chart_curvature_covariant_germ
#print axioms MicroMacro.chart_curvature_covariant_chart_smooth
#print axioms MicroMacro.chart_intrinsic_curvature_pointwise
