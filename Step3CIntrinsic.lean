import Step3CSmooth

/-! Actual tangent-fiber metric and vector representatives. The
metric is given as a family of bilinear forms on actual tangent spaces,
and regularity is measured by its chart component functions. -/
namespace MicroMacro
open scoped BigOperators Topology Manifold ContDiff
open Filter Set Bundle
local notation "E4" => (Fin 4 → ℝ)
local notation "I4" => 𝓘(ℝ, E4)

theorem chart_metric_bundle_reconstruct
    (B : E4 →L[ℝ] E4 →L[ℝ] ℝ) :
    chartMetricBundle (fun i j => B (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ))) = B := by
  apply chart_basis_ext
  intro i
  apply chart_basis_ext
  intro j
  rw [chart_metric_bundle_eval, chart_coordinate_pair_basis]

section Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
  [IsManifold I4 2 M] [IsManifold I4 1 M]

theorem chart_manifold_transition_regular_c2 (a b p : M)
    (ha : p ∈ (extChartAt I4 a).source)
    (hb : p ∈ (extChartAt I4 b).source) :
    ContDiffAt ℝ (2 : WithTop ℕ∞) (chartManifoldTransition a b)
      (extChartAt I4 a p) := by
  have ha' : p ∈ (chartAt E4 a).source := by simpa only [extChartAt_source] using ha
  have hb' : p ∈ (chartAt E4 b).source := by simpa only [extChartAt_source] using hb
  have h := OpenPartialHomeomorph.contDiffWithinAt_extend_coord_change'
    (I := I4) (n := (2 : WithTop ℕ∞))
    (IsManifold.chart_mem_maximalAtlas (I := I4) (n := (2 : WithTop ℕ∞)) b)
    (IsManifold.chart_mem_maximalAtlas (I := I4) (n := (2 : WithTop ℕ∞)) a) hb' ha'
  simpa [chartManifoldTransition, extChartAt, ModelWithCorners.range_eq_univ,
    contDiffWithinAt_univ] using h

theorem chart_manifold_constructed_overlap_c2
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
  have hf : ContDiffAt ℝ (2 : WithTop ℕ∞) F x :=
    chart_manifold_transition_regular_c2 a b p ha hb
  have hr : DifferentiableAt ℝ R (F x) := by
    rw [hF]
    exact (chart_manifold_transition_regular_c2 b a p hb ha).differentiableAt (by norm_num)
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
  have H := chart_constructed_covariant_overlap_c2 g h s t hs ht F R X Y x w
    hx hy' hgs hhs hgd hhd' hgsig hhsig' hf hr h0 hl hh hm hX hY' he
  rw [hF] at H
  rw [chart_manifold_tangent_jacobian a b p]
  exact H

/-- Actual coordinate representative of an intrinsic tangent field. -/
noncomputable def chartIntrinsicField
    (X : ∀ p : M, TangentSpace I4 p) (a : M) (z : E4) : E4 :=
  let p := (extChartAt I4 a).symm z
  tangentCoordChange I4 p a p (X p)

/-- Pull back an intrinsic metric along the inverse tangent frame. -/
noncomputable def chartIntrinsicForm
    (G : ∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
    (a : M) (z : E4) : E4 →L[ℝ] E4 →L[ℝ] ℝ :=
  let p := (extChartAt I4 a).symm z
  let B : E4 →L[ℝ] E4 →L[ℝ] ℝ := G p
  B.bilinearComp (tangentCoordChange I4 a p p) (tangentCoordChange I4 a p p)

noncomputable def chartIntrinsicComponents
    (G : ∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
    (a : M) (z : E4) (i j : Fin 4) : ℝ :=
  chartIntrinsicForm G a z (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ))

theorem chart_intrinsic_field_value
    (X : ∀ p : M, TangentSpace I4 p) (a p : M)
    (ha : p ∈ (extChartAt I4 a).source) :
    chartIntrinsicField X a (extChartAt I4 a p) = tangentCoordChange I4 p a p (X p) := by
  unfold chartIntrinsicField
  rw [(extChartAt I4 a).left_inv ha]

theorem chart_intrinsic_form_value
    (G : ∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
    (a p : M) (ha : p ∈ (extChartAt I4 a).source) (u v : E4) :
    chartIntrinsicForm G a (extChartAt I4 a p) u v =
      G p (tangentCoordChange I4 a p p u) (tangentCoordChange I4 a p p v) := by
  unfold chartIntrinsicForm
  rw [(extChartAt I4 a).left_inv ha] <;> rfl

theorem chart_intrinsic_components_bundle
    (G : ∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
    (a : M) (z : E4) :
    chartMetricBundle (chartIntrinsicComponents G a z) = chartIntrinsicForm G a z :=
  chart_metric_bundle_reconstruct _

theorem chart_intrinsic_field_germ
    (X : ∀ p : M, TangentSpace I4 p) (a b p : M)
    (ha : p ∈ (extChartAt I4 a).source)
    (hb : p ∈ (extChartAt I4 b).source) :
    (fun z => fderiv ℝ (chartManifoldTransition a b) z (chartIntrinsicField X a z)) =ᶠ[
      𝓝 (extChartAt I4 a p)] (fun z => chartIntrinsicField X b (chartManifoldTransition a b z)) := by
  have hm : map (extChartAt I4 a) (𝓝 p) = 𝓝 (extChartAt I4 a p) := by
    rw [map_extChartAt_nhds' ha, ModelWithCorners.range_eq_univ, nhdsWithin_univ]
  rw [← hm]
  change ∀ᶠ q in 𝓝 p, fderiv ℝ (chartManifoldTransition a b) (extChartAt I4 a q)
    (chartIntrinsicField X a (extChartAt I4 a q)) =
      chartIntrinsicField X b (chartManifoldTransition a b (extChartAt I4 a q))
  filter_upwards [show ∀ᶠ q in 𝓝 p, q ∈ (extChartAt I4 a).source from
      (isOpen_extChartAt_source a).mem_nhds ha,
    show ∀ᶠ q in 𝓝 p, q ∈ (extChartAt I4 b).source from
      (isOpen_extChartAt_source b).mem_nhds hb] with q hqa hqb
  rw [← chart_manifold_tangent_jacobian a b q, chart_manifold_transition_value a b q hqa,
    chart_intrinsic_field_value X a q hqa, chart_intrinsic_field_value X b q hqb]
  exact chart_manifold_tangent_cocycle q a b q (X q) (mem_extChartAt_source q) hqa hqb

theorem chart_intrinsic_metric_germ
    (G : ∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
    (a b p : M) (ha : p ∈ (extChartAt I4 a).source)
    (hb : p ∈ (extChartAt I4 b).source) (u v : E4) :
    (fun z => chartMetricBundle (chartIntrinsicComponents G a z) u v) =ᶠ[
      𝓝 (extChartAt I4 a p)] (fun z => chartPullbackMetric (chartManifoldTransition a b)
        (fun q => chartMetricBundle (chartIntrinsicComponents G b q)) z u v) := by
  have hm : map (extChartAt I4 a) (𝓝 p) = 𝓝 (extChartAt I4 a p) := by
    rw [map_extChartAt_nhds' ha, ModelWithCorners.range_eq_univ, nhdsWithin_univ]
  rw [← hm]
  change ∀ᶠ q in 𝓝 p, chartMetricBundle (chartIntrinsicComponents G a (extChartAt I4 a q)) u v =
    chartPullbackMetric (chartManifoldTransition a b)
      (fun z => chartMetricBundle (chartIntrinsicComponents G b z)) (extChartAt I4 a q) u v
  filter_upwards [show ∀ᶠ q in 𝓝 p, q ∈ (extChartAt I4 a).source from
      (isOpen_extChartAt_source a).mem_nhds ha,
    show ∀ᶠ q in 𝓝 p, q ∈ (extChartAt I4 b).source from
      (isOpen_extChartAt_source b).mem_nhds hb] with q hqa hqb
  simp only [chartPullbackMetric]
  rw [chart_intrinsic_components_bundle, chart_intrinsic_components_bundle,
    chart_manifold_transition_value a b q hqa, ← chart_manifold_tangent_jacobian a b q,
    chart_intrinsic_form_value G a q hqa, chart_intrinsic_form_value G b q hqb,
    chart_manifold_tangent_cocycle a b q q u hqa hqb (mem_extChartAt_source q),
    chart_manifold_tangent_cocycle a b q q v hqa hqb (mem_extChartAt_source q)]

theorem chart_intrinsic_components_symmetric
    (G : ∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
    (hs : ∀ p u v, G p u v = G p v u) (a : M) (z : E4) (i j : Fin 4) :
    chartIntrinsicComponents G a z i j = chartIntrinsicComponents G a z j i := by
  unfold chartIntrinsicComponents chartIntrinsicForm
  exact hs _ _ _

/-- Tangent transition and its reverse constitute a linear equivalence. -/
noncomputable def chartTangentFrame (a p : M)
    (ha : p ∈ (extChartAt I4 a).source) : E4 ≃ₗ[ℝ] E4 :=
  { (tangentCoordChange I4 a p p).toLinearMap with
    invFun := tangentCoordChange I4 p a p
    left_inv := by
      intro u
      change tangentCoordChange I4 p a p (tangentCoordChange I4 a p p u) = u
      rw [chart_manifold_tangent_cocycle a p a p u ha (mem_extChartAt_source p) ha]
      exact tangentCoordChange_self ha
    right_inv := by
      intro u
      change tangentCoordChange I4 a p p (tangentCoordChange I4 p a p u) = u
      rw [chart_manifold_tangent_cocycle p a p p u (mem_extChartAt_source p) ha (mem_extChartAt_source p)]
      exact tangentCoordChange_self (mem_extChartAt_source p) }

theorem chart_intrinsic_signature
    (G : ∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
    (h : ∀ p, ∃ e : E4 ≃ₗ[ℝ] E4, ∀ u v, G p (e u) (e v) =
      coordinateMetricPair minkowskiMetric u v)
    (a p : M) (ha : p ∈ (extChartAt I4 a).source) :
    hasLorentzSignature (chartIntrinsicComponents G a (extChartAt I4 a p)) := by
  obtain ⟨e, he⟩ := h p
  let L := chartTangentFrame a p ha
  refine ⟨e.trans L.symm, ?_⟩
  intro u v
  rw [← chart_metric_bundle_eval, chart_intrinsic_components_bundle,
    chart_intrinsic_form_value G a p ha]
  change G p (L (L.symm (e u))) (L (L.symm (e v))) = _
  rw [L.apply_symm_apply, L.apply_symm_apply]
  exact he u v

/-- Global output from an intrinsic metric and tangent fields. Local
regularity of metric components and actual field representatives is
assumed (the usual chartwise regularity condition), but the output
regularity and all metric/field overlap laws are derived. -/
theorem chart_intrinsic_global_section
    (G : ∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
    (X W : ∀ p : M, TangentSpace I4 p)
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
    ∃! S : ∀ p : M, TangentSpace I4 p,
      (∀ a p, p ∈ (extChartAt I4 a).source →
        tangentCoordChange I4 p a p (S p) =
          chartCovariantDerivative
            (fun z u v => chartConstructedCoefficients (chartIntrinsicComponents G a) z u v)
            (chartIntrinsicField X a) (extChartAt I4 a p)
            (tangentCoordChange I4 p a p (W p))) ∧
      ContMDiff I4 (ModelWithCorners.prod I4 I4) ∞ (fun p => TotalSpace.mk' E4 p (S p)) := by
  let value : M → M → E4 := fun a p => chartCovariantDerivative
    (fun z u v => chartConstructedCoefficients (chartIntrinsicComponents G a) z u v)
    (chartIntrinsicField X a) (extChartAt I4 a p) (tangentCoordChange I4 p a p (W p))
  apply chart_manifold_smooth_glue ∞ value
  · intro a b p ha hb
    have H := chart_manifold_constructed_overlap_c2 a b p ha hb
      (chartIntrinsicComponents G a) (chartIntrinsicComponents G b)
      Set.univ Set.univ isOpen_univ isOpen_univ (Set.mem_univ _) (Set.mem_univ _)
      (fun z _ i j => chart_intrinsic_components_symmetric G hs a z i j)
      (fun z _ i j => chart_intrinsic_components_symmetric G hs b z i j)
      (fun i j => (hg a p ha i j).differentiableAt (by simp))
      (fun i j => (hg b p hb i j).differentiableAt (by simp))
      (chart_intrinsic_signature G hsig a p ha) (chart_intrinsic_signature G hsig b p hb)
      (chartIntrinsicField X a) (chartIntrinsicField X b) (tangentCoordChange I4 p a p (W p))
      (chart_intrinsic_metric_germ G a b p ha hb)
      ((hX a p ha).differentiableAt (by simp)) ((hX b p hb).differentiableAt (by simp))
      (chart_intrinsic_field_germ X a b p ha hb)
    rw [chart_manifold_tangent_cocycle p a b p (W p) (mem_extChartAt_source p) ha hb] at H
    exact H
  · intro a p ha
    let q : E4 → E4 := fun z => chartCovariantDerivative
      (fun y u v => chartConstructedCoefficients (chartIntrinsicComponents G a) y u v)
      (chartIntrinsicField X a) z (chartIntrinsicField W a z)
    have hq : ContDiffAt ℝ ∞ q (extChartAt I4 a p) :=
      chart_constructed_output_smooth_at (chartIntrinsicComponents G a)
        (chartIntrinsicField X a) (chartIntrinsicField W a) (extChartAt I4 a p)
        (hg a p ha) (chart_intrinsic_signature G hsig a p ha) (hX a p ha) (hW a p ha)
    have hq' : ContMDiffAt I4 I4 ∞ q (extChartAt I4 a p) :=
      contMDiffAt_iff_contDiffAt.mpr hq
    have hc := hq'.comp p (contMDiffAt_extChartAt' (I := I4) (n := ∞)
      (x := a) (by simpa only [extChartAt_source] using ha))
    apply hc.contMDiffWithinAt.congr
    · intro b hb
      change value a b = q (extChartAt I4 a b)
      exact congrArg (fun w : E4 => chartCovariantDerivative
        (fun z u v => chartConstructedCoefficients (chartIntrinsicComponents G a) z u v)
        (chartIntrinsicField X a) (extChartAt I4 a b) w)
        (chart_intrinsic_field_value W a b hb).symm
    · change value a p = q (extChartAt I4 a p)
      exact congrArg (fun w : E4 => chartCovariantDerivative
        (fun z u v => chartConstructedCoefficients (chartIntrinsicComponents G a) z u v)
        (chartIntrinsicField X a) (extChartAt I4 a p) w)
        (chart_intrinsic_field_value W a p ha).symm


/-- Globally defined operator in the canonical chart of each point.
The global-section theorem supplies chart independence and smoothness
for regular inputs; this definition itself is total. -/
noncomputable def chartIntrinsicCovariantDerivative
    (G : ∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
    (W X : ∀ p : M, TangentSpace I4 p) (p : M) : TangentSpace I4 p :=
  chartCovariantDerivative (E := E4)
    (fun z u v => chartConstructedCoefficients (chartIntrinsicComponents G p) z u v)
    (chartIntrinsicField X p) (extChartAt I4 p p) (W p)

/-- Any section satisfying the local covariant formula equals the
globally defined operator, by the identity chart transition. -/
theorem chart_intrinsic_operator_identification
    (G : ∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
    (W X S : ∀ p : M, TangentSpace I4 p)
    (hS : ∀ a p, p ∈ (extChartAt I4 a).source →
      tangentCoordChange I4 p a p (S p) =
        chartCovariantDerivative
          (fun z u v => chartConstructedCoefficients (chartIntrinsicComponents G a) z u v)
          (chartIntrinsicField X a) (extChartAt I4 a p)
          (tangentCoordChange I4 p a p (W p))) :
    S = chartIntrinsicCovariantDerivative G W X := by
  funext p
  have h := hS p p (mem_extChartAt_source p)
  rw [tangentCoordChange_self (mem_extChartAt_source p),
    tangentCoordChange_self (mem_extChartAt_source p)] at h
  exact h

theorem chart_intrinsic_direction_add
    (G : ∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
    (W V X : ∀ p : M, TangentSpace I4 p) :
    chartIntrinsicCovariantDerivative G (fun p => W p + V p) X =
      fun p => chartIntrinsicCovariantDerivative G W X p +
        chartIntrinsicCovariantDerivative G V X p := by
  funext p
  exact chart_covariant_direction_add (chartConstructedCoefficients (chartIntrinsicComponents G p))
    (chartIntrinsicField X p) (extChartAt I4 p p) (W p) (V p)

theorem chart_intrinsic_direction_smul
    (G : ∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
    (a : M → ℝ) (W X : ∀ p : M, TangentSpace I4 p) :
    chartIntrinsicCovariantDerivative G (fun p => a p • W p) X =
      fun p => a p • chartIntrinsicCovariantDerivative G W X p := by
  funext p
  exact chart_covariant_direction_smul (chartConstructedCoefficients (chartIntrinsicComponents G p))
    (chartIntrinsicField X p) (extChartAt I4 p p) (W p) (a p)

theorem chart_intrinsic_field_add_rep
    (X Y : ∀ p : M, TangentSpace I4 p) (a : M) :
    chartIntrinsicField (fun p => X p + Y p) a =
      chartIntrinsicField X a + chartIntrinsicField Y a := by
  funext z
  simp [chartIntrinsicField, map_add]

theorem chart_intrinsic_field_smul_rep
    (c : M → ℝ) (X : ∀ p : M, TangentSpace I4 p) (a : M) :
    chartIntrinsicField (fun p => c p • X p) a =
      (fun z => c ((extChartAt I4 a).symm z)) • chartIntrinsicField X a := by
  funext z
  simp [chartIntrinsicField, map_smul]

theorem chart_intrinsic_field_add
    (G : ∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
    (W X Y : ∀ p : M, TangentSpace I4 p)
    (hX : ∀ p, DifferentiableAt ℝ (chartIntrinsicField X p) (extChartAt I4 p p))
    (hY : ∀ p, DifferentiableAt ℝ (chartIntrinsicField Y p) (extChartAt I4 p p)) :
    chartIntrinsicCovariantDerivative G W (fun p => X p + Y p) =
      fun p => chartIntrinsicCovariantDerivative G W X p +
        chartIntrinsicCovariantDerivative G W Y p := by
  funext p
  unfold chartIntrinsicCovariantDerivative
  rw [chart_intrinsic_field_add_rep]
  exact chart_covariant_field_add (chartConstructedCoefficients (chartIntrinsicComponents G p))
    (chartIntrinsicField X p) (chartIntrinsicField Y p) (extChartAt I4 p p) (W p) (hX p) (hY p)

theorem chart_intrinsic_leibniz
    (G : ∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
    (c : M → ℝ) (W X : ∀ p : M, TangentSpace I4 p)
    (hc : ∀ p, DifferentiableAt ℝ (fun z => c ((extChartAt I4 p).symm z))
      (extChartAt I4 p p))
    (hX : ∀ p, DifferentiableAt ℝ (chartIntrinsicField X p) (extChartAt I4 p p)) :
    chartIntrinsicCovariantDerivative G W (fun p => c p • X p) =
      fun p => (fderiv ℝ (fun z => c ((extChartAt I4 p).symm z))
        (extChartAt I4 p p) (W p)) • X p + c p • chartIntrinsicCovariantDerivative G W X p := by
  funext p
  unfold chartIntrinsicCovariantDerivative
  rw [chart_intrinsic_field_smul_rep, chart_covariant_leibniz _
    (fun z => c ((extChartAt I4 p).symm z)) (chartIntrinsicField X p)
    (extChartAt I4 p p) (W p) (hc p) (hX p)]
  rw [(extChartAt I4 p).left_inv (mem_extChartAt_source p),
    chart_intrinsic_field_value X p p (mem_extChartAt_source p),
    tangentCoordChange_self (mem_extChartAt_source p)]

/-- Uniqueness of any locally LC coefficient field, in each actual
chart, follows from the directional Koszul uniqueness theorem. -/
theorem chart_intrinsic_coefficient_unique
    (G : ∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)
    (hs : ∀ p u v, G p u v = G p v u)
    (hsig : ∀ p, ∃ e : E4 ≃ₗ[ℝ] E4, ∀ u v, G p (e u) (e v) =
      coordinateMetricPair minkowskiMetric u v)
    (a p : M) (ha : p ∈ (extChartAt I4 a).source)
    (hd : ∀ i j, DifferentiableAt ℝ (fun z => chartIntrinsicComponents G a z i j)
      (extChartAt I4 a p))
    (D : E4 → E4 → E4)
    (hD : chartLCAt (fun z u v => chartMetricBundle (chartIntrinsicComponents G a z) u v)
      (extChartAt I4 a p) D) :
    D = fun u v => chartConstructedCoefficients (chartIntrinsicComponents G a)
      (extChartAt I4 a p) u v := by
  have hsym := chart_intrinsic_components_symmetric G hs a (extChartAt I4 a p)
  have hsig' := chart_intrinsic_signature G hsig a p ha
  apply chart_lc_pointwise_unique
    (fun z u v => chartMetricBundle (chartIntrinsicComponents G a z) u v)
    (extChartAt I4 a p) (chartMetricBundle (chartIntrinsicComponents G a (extChartAt I4 a p)))
    (fun u v => rfl)
    (chart_bundle_symmetry _ hsym)
    (chart_metric_bundle_nondegenerate _ hsym hsig') D _ hD
  exact chart_open_domain_directional_lift (chartIntrinsicComponents G a) Set.univ
    isOpen_univ (extChartAt I4 a p) (Set.mem_univ _)
    (fun z _ => chart_intrinsic_components_symmetric G hs a z) hd hsig'

end Manifold
end MicroMacro

#print axioms MicroMacro.chart_metric_bundle_reconstruct
#print axioms MicroMacro.chart_manifold_transition_regular_c2
#print axioms MicroMacro.chart_manifold_constructed_overlap_c2
#print axioms MicroMacro.chart_intrinsic_field_value
#print axioms MicroMacro.chart_intrinsic_form_value
#print axioms MicroMacro.chart_intrinsic_components_bundle
#print axioms MicroMacro.chart_intrinsic_field_germ
#print axioms MicroMacro.chart_intrinsic_metric_germ
#print axioms MicroMacro.chart_intrinsic_components_symmetric
#print axioms MicroMacro.chart_intrinsic_signature
#print axioms MicroMacro.chart_intrinsic_global_section
#print axioms MicroMacro.chartIntrinsicField
#print axioms MicroMacro.chartIntrinsicForm
#print axioms MicroMacro.chartIntrinsicComponents
#print axioms MicroMacro.chartTangentFrame

#print axioms MicroMacro.chart_intrinsic_operator_identification
#print axioms MicroMacro.chart_intrinsic_direction_add
#print axioms MicroMacro.chart_intrinsic_direction_smul
#print axioms MicroMacro.chart_intrinsic_field_add_rep
#print axioms MicroMacro.chart_intrinsic_field_smul_rep
#print axioms MicroMacro.chart_intrinsic_field_add
#print axioms MicroMacro.chart_intrinsic_leibniz
#print axioms MicroMacro.chart_intrinsic_coefficient_unique
#print axioms MicroMacro.chartIntrinsicCovariantDerivative
