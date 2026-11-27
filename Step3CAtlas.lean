import Step3C

/-! Step 3C extension: finite-coordinate directional lift, pointwise
open-domain existence, and atlas descent of compatible vector values.
The descent interface is not yet an intrinsic smooth tangent-bundle
connection on a Mathlib manifold. -/

namespace MicroMacro
open scoped BigOperators Topology
open Filter

noncomputable def chartMetricBundle (g : Fin 4 → Fin 4 → ℝ) :
    (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ∑ i, ∑ j, g i j •
    ((ContinuousLinearMap.proj (R := ℝ) i : (Fin 4 → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj (R := ℝ) j : (Fin 4 → ℝ) →L[ℝ] ℝ))

noncomputable def chartCoefficientBundle (C : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  ∑ i, ∑ j,
    (ContinuousLinearMap.proj (R := ℝ) i : (Fin 4 → ℝ) →L[ℝ] ℝ).smulRight
      ((ContinuousLinearMap.proj (R := ℝ) j : (Fin 4 → ℝ) →L[ℝ] ℝ).smulRight
        (C i j))

theorem chart_metric_bundle_eval (g : Fin 4 → Fin 4 → ℝ) (u v : Fin 4 → ℝ) :
    chartMetricBundle g u v = coordinateMetricPair g u v := by
  simp only [chartMetricBundle, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, coordinateMetricPair]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem chart_coefficient_bundle_basis (C : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (i j : Fin 4) :
    chartCoefficientBundle C (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) = C i j := by
  classical
  simp [chartCoefficientBundle, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, Pi.single_apply]

theorem chart_metric_bundle_smooth
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (h : ∀ i j, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => g x i j)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => chartMetricBundle (g x)) := by
  unfold chartMetricBundle
  apply ContDiff.sum
  intro i hi
  apply ContDiff.sum
  intro j hj
  exact (h i j).smul contDiff_const

theorem chart_metric_bundle_differentiable_at
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (x : Fin 4 → ℝ)
    (h : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) :
    DifferentiableAt ℝ (fun y => chartMetricBundle (g y)) x := by
  unfold chartMetricBundle
  refine DifferentiableAt.fun_sum (𝕜 := ℝ) (u := Finset.univ) (A := fun i y =>
    ∑ j : Fin 4, g y i j •
      ((ContinuousLinearMap.proj (R := ℝ) i : (Fin 4 → ℝ) →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj (R := ℝ) j : (Fin 4 → ℝ) →L[ℝ] ℝ))) ?_
  intro i hi
  refine DifferentiableAt.fun_sum (𝕜 := ℝ) (u := Finset.univ) (A := fun j y =>
    g y i j • ((ContinuousLinearMap.proj (R := ℝ) i : (Fin 4 → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj (R := ℝ) j : (Fin 4 → ℝ) →L[ℝ] ℝ))) ?_
  intro j hj
  let B : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) i : (Fin 4 → ℝ) →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj (R := ℝ) j : (Fin 4 → ℝ) →L[ℝ] ℝ)
  have hB : DifferentiableAt ℝ (fun _ : Fin 4 → ℝ => B) x :=
    differentiableAt_const B
  exact (h i j).smul hB

/-- Linear maps out of the coordinate model are determined on its basis. -/
theorem chart_basis_ext {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L M : (Fin 4 → ℝ) →L[ℝ] W)
    (h : ∀ i : Fin 4, L (Pi.single i (1 : ℝ)) = M (Pi.single i (1 : ℝ))) :
    L = M := by
  ext v
  have hv : (∑ i : Fin 4, v i • (Pi.single i (1 : ℝ) : Fin 4 → ℝ)) = v := by
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite]
  rw [← hv, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, map_smul, h]

theorem chart_bundle_symmetry (g : Fin 4 → Fin 4 → ℝ)
    (hs : ∀ i j, g i j = g j i) (u v : Fin 4 → ℝ) :
    chartMetricBundle g u v = chartMetricBundle g v u := by
  rw [chart_metric_bundle_eval, chart_metric_bundle_eval]
  unfold coordinateMetricPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hs i j]
  ring

theorem chart_metric_bundle_nondegenerate (g : Fin 4 → Fin 4 → ℝ)
    (hs : ∀ i j, g i j = g j i) (hsig : hasLorentzSignature g)
    (u : Fin 4 → ℝ) (hu : ∀ v, chartMetricBundle g u v = 0) : u = 0 := by
  apply lorentz_signature_no_kernel g hsig u
  intro i
  have h := hu (Pi.single i (1 : ℝ))
  rw [chart_bundle_symmetry g hs] at h
  rw [chart_metric_bundle_eval, coordinate_pair_factor] at h
  simpa [Pi.single_apply, ite_mul] using h

/-- Directional LC compatibility is established from component identities,
not postulated for arbitrary directions. -/
theorem chart_coordinate_lift_lc
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (x : Fin 4 → ℝ)
    (C : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hd : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (ht : ∀ k i l, C k i l = C i k l)
    (hm : ∀ k i j, tensorConnection Finset.univ (C k)
      (g x) (metricPartial g x k) i j = 0) :
    chartLCAt (fun y u v => chartMetricBundle (g y) u v) x
      (fun u v => chartCoefficientBundle C u v) := by
  let B := chartMetricBundle (g x)
  let K := chartCoefficientBundle C
  let dB := fderiv ℝ (fun y => chartMetricBundle (g y)) x
  let e : Fin 4 → Fin 4 → ℝ := fun i => Pi.single i (1 : ℝ)
  have hdiff := chart_metric_bundle_differentiable_at g x hd
  have hdir (w u v : Fin 4 → ℝ) :
      chartDirectional (fun y a b => chartMetricBundle (g y) a b) x w u v =
        dB w u v := chart_directional_bilinear (fun y => chartMetricBundle (g y)) x w u v hdiff
  have hbase (k i j : Fin 4) : dB (e k) (e i) (e j) =
      B (K (e k) (e i)) (e j) + B (e i) (K (e k) (e j)) := by
    have he : (fun y a b => chartMetricBundle (g y) a b) =
        fun y a b => coordinateMetricPair (g y) a b := by
      funext y a b
      exact chart_metric_bundle_eval (g y) a b
    have hD := hdir (e k) (e i) (e j)
    rw [he, chart_coordinate_directional_basis] at hD
    rw [← hD]
    dsimp only [B, K, e]
    rw [chart_coefficient_bundle_basis, chart_coefficient_bundle_basis,
      chart_metric_bundle_eval, chart_metric_bundle_eval]
    have h := hm k i j
    unfold tensorConnection at h
    have h1 : coordinateMetricPair (g x) (C k i) (Pi.single j (1 : ℝ)) =
        ∑ l, C k i l * g x l j := by
      simp [coordinateMetricPair, Pi.single_apply, mul_ite, mul_comm]
    have h2 : coordinateMetricPair (g x) (Pi.single i (1 : ℝ)) (C k j) =
        ∑ l, C k j l * g x i l := by
      simp [coordinateMetricPair, Pi.single_apply, ite_mul, mul_comm]
    rw [h1, h2]
    linarith
  constructor
  · intro u v
    have hK : K = K.flip := by
      apply chart_basis_ext
      intro i
      apply chart_basis_ext
      intro j
      change K (e i) (e j) = K (e j) (e i)
      dsimp only [K, e]
      rw [chart_coefficient_bundle_basis, chart_coefficient_bundle_basis]
      funext l
      exact ht i j l
    exact congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) => L u v) hK
  · intro w u v
    rw [hdir]
    change dB w u v = B (K w u) v + B u (K w v)
    have hW (i j : Fin 4) :
        (dB.flip (e i)).flip (e j) =
          ((B.flip (e j)).comp (K.flip (e i))) +
            ((B (e i)).comp (K.flip (e j))) := by
      apply chart_basis_ext
      intro k
      exact hbase k i j
    have hU (w : Fin 4 → ℝ) (j : Fin 4) :
        (dB w).flip (e j) =
          ((B.flip (e j)).comp (K w)) + B.flip (K w (e j)) := by
      apply chart_basis_ext
      intro i
      exact congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L w) (hW i j)
    have hV : dB w u = B (K w u) + (B u).comp (K w) := by
      apply chart_basis_ext
      intro j
      exact congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L u) (hU w j)
    exact congrArg (fun L : (Fin 4 → ℝ) →L[ℝ] ℝ => L v) hV

theorem chart_step3b_directional_lift
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ x i j, g x i j = g x j i)
    (hd : ∀ i j, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y i j))
    (hsig : ∀ x, hasLorentzSignature (g x)) (x : Fin 4 → ℝ) :
    chartLCAt (fun y u v => chartMetricBundle (g y) u v) x
      (fun u v => chartCoefficientBundle
        (metricChristoffel g (coordinateMetricInverse g) x) u v) := by
  have h := lorentz_data_from_metric g hs hd hsig
  apply chart_coordinate_lift_lc g x _
    (fun i j => (hd i j).contDiffAt.differentiableAt (by simp))
  · intro k i l
    exact (lorentz_coordinate_connection g (coordinateMetricInverse g) h x k i l).1
  · intro k i j
    exact (lorentz_coordinate_connection g (coordinateMetricInverse g) h x k i j).2

/-- Open-domain existence: only local symmetry, smoothness at the point
and signature there are needed; ambient extensions need not be Lorentzian
outside the open set. -/
theorem chart_open_domain_directional_lift
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (s : Set (Fin 4 → ℝ)) (ho : IsOpen s) (x : Fin 4 → ℝ) (hx : x ∈ s)
    (hs : ∀ y ∈ s, ∀ i j, g y i j = g y j i)
    (hd : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hsig : hasLorentzSignature (g x)) :
    chartLCAt (fun y u v => chartMetricBundle (g y) u v) x
      (fun u v => chartCoefficientBundle
        (metricChristoffel g (coordinateMetricInverse g) x) u v) := by
  have hdet := coordinate_det_ne_zero (g x) (lorentz_signature_no_kernel (g x) hsig)
  have hi (i j : Fin 4) : (∑ l, coordinateMetricInverse g x i l * g x l j) =
      if i = j then 1 else 0 := by
    have h := Matrix.nonsing_inv_mul (Matrix.of (g x)) (isUnit_iff_ne_zero.mpr hdet)
    have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) h
    simpa [Matrix.mul_apply, Matrix.one_apply, coordinateMetricInverse] using he
  have hsym (k i j : Fin 4) : metricPartial g x k i j = metricPartial g x k j i := by
    have he : (fun y => g y i j) =ᶠ[𝓝 x] (fun y => g y j i) :=
      Filter.Eventually.mono (show ∀ᶠ y in 𝓝 x, y ∈ s from ho.mem_nhds hx)
        (fun y hy => hs y hy i j)
    unfold metricPartial
    rw [he.fderiv_eq]
  apply chart_coordinate_lift_lc g x _ hd
  · intro k i l
    exact christoffel_jet_torsion_free (coordinateMetricInverse g x)
      (metricPartial g x) hsym k i l
  · intro k i j
    exact christoffel_jet_metric_compatible (g x) (coordinateMetricInverse g x)
      (metricPartial g x) (hs x hx) hsym hi k i j

/-- Descent on a covering family, with values in the actual chosen fibers.
This is set-theoretic gluing, not a bundled smooth section construction. -/
noncomputable def chartAtlasGlue {P I : Type*} {V : P → Type*}
    (U : I → Set P) (cover : ∀ p, ∃ i, p ∈ U i)
    (localValue : ∀ (i : I) (p : P), V p) (p : P) : V p :=
  localValue (Classical.choose (cover p)) p

theorem chart_atlas_glue_agrees {P I : Type*} {V : P → Type*}
    (U : I → Set P) (cover : ∀ p, ∃ i, p ∈ U i)
    (localValue : ∀ (i : I) (p : P), V p)
    (overlap : ∀ i j p, p ∈ U i → p ∈ U j → localValue i p = localValue j p)
    (i : I) (p : P) (hp : p ∈ U i) :
    chartAtlasGlue U cover localValue p = localValue i p := by
  exact overlap _ i p (Classical.choose_spec (cover p)) hp

theorem chart_atlas_glue_unique {P I : Type*} {V : P → Type*}
    (U : I → Set P) (cover : ∀ p, ∃ i, p ∈ U i)
    (localValue : ∀ (i : I) (p : P), V p) (S : ∀ p, V p)
    (hS : ∀ i p, p ∈ U i → S p = localValue i p) :
    S = chartAtlasGlue U cover localValue := by
  funext p
  exact hS _ p (Classical.choose_spec (cover p))

/-- Coordinate values that obey the tangent transition law descend
uniquely to a fiberwise value; the frame interface is explicit. -/
theorem chart_atlas_frame_descent {P I E : Type*} {V : P → Type*}
    (U : I → Set P) (cover : ∀ p, ∃ i, p ∈ U i)
    (frame : ∀ (i : I) (p : P), V p ≃ E)
    (value : I → P → E)
    (overlap : ∀ i j p, p ∈ U i → p ∈ U j →
      frame j p ((frame i p).symm (value i p)) = value j p) :
    ∃! S : ∀ p, V p, ∀ i p, p ∈ U i → frame i p (S p) = value i p := by
  let localValue : ∀ (i : I) (p : P), V p := fun i p => (frame i p).symm (value i p)
  have hlocal (i j : I) (p : P) (hi : p ∈ U i) (hj : p ∈ U j) :
      localValue i p = localValue j p := by
    apply (frame j p).injective
    simpa [localValue] using overlap i j p hi hj
  refine ⟨chartAtlasGlue U cover localValue, ?_, ?_⟩
  · intro i p hp
    rw [chart_atlas_glue_agrees U cover localValue hlocal i p hp]
    exact (frame i p).apply_symm_apply (value i p)
  · intro S hS
    apply chart_atlas_glue_unique U cover localValue S
    intro i p hp
    apply (frame i p).injective
    simpa [localValue] using hS i p hp

end MicroMacro

#print axioms MicroMacro.chart_metric_bundle_eval
#print axioms MicroMacro.chart_coefficient_bundle_basis
#print axioms MicroMacro.chart_metric_bundle_smooth
#print axioms MicroMacro.chart_metric_bundle_differentiable_at
#print axioms MicroMacro.chart_basis_ext
#print axioms MicroMacro.chart_bundle_symmetry
#print axioms MicroMacro.chart_metric_bundle_nondegenerate
#print axioms MicroMacro.chart_coordinate_lift_lc
#print axioms MicroMacro.chart_step3b_directional_lift
#print axioms MicroMacro.chart_open_domain_directional_lift
#print axioms MicroMacro.chart_atlas_glue_agrees
#print axioms MicroMacro.chart_atlas_glue_unique
#print axioms MicroMacro.chart_atlas_frame_descent
#print axioms MicroMacro.chartMetricBundle
#print axioms MicroMacro.chartCoefficientBundle
#print axioms MicroMacro.chartAtlasGlue
