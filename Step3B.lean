import Step3A

/-! Step 3B: existence and uniqueness of local coordinate Levi-Civita
coefficients, construction of a smooth inverse, and actual inverse
differentiation. The domain remains the whole real coordinate model.
Global chart gluing is explicitly outside this checkpoint. -/

namespace MicroMacro

open scoped BigOperators

/-- The matrix inverse supplied by the nonsingular inverse construction. -/
noncomputable def coordinateMetricInverse
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (x : Fin 4 → ℝ) (i j : Fin 4) : ℝ :=
  ((Matrix.of (g x))⁻¹) i j

/-- A connection coefficient array is torsion-free and metric compatible
with the actual coordinate derivatives. -/
def coordinateLC
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (C : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ) : Prop :=
  (∀ x k i l, C x k i l = C x i k l) ∧
  (∀ x k i j, tensorConnection Finset.univ (C x k)
    (g x) (metricPartial g x k) i j = 0)

/-- Factoring a coordinate bilinear pairing by its first argument. -/
theorem coordinate_pair_factor
    (g : Fin 4 → Fin 4 → ℝ) (u v : Fin 4 → ℝ) :
    coordinateMetricPair g u v = ∑ i, u i * (∑ j, g i j * v j) := by
  unfold coordinateMetricPair
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The signature witness implies nondegeneracy, independently of any
supplied inverse metric. -/
theorem lorentz_signature_no_kernel
    (g : Fin 4 → Fin 4 → ℝ) (h : hasLorentzSignature g)
    (v : Fin 4 → ℝ) (hv : ∀ i, (∑ j, g i j * v j) = 0) : v = 0 := by
  rcases h with ⟨e, he⟩
  let w : Fin 4 → ℝ := e.symm v
  have hev : e w = v := e.apply_symm_apply v
  have hp (u : Fin 4 → ℝ) : coordinateMetricPair g u v = 0 := by
    rw [coordinate_pair_factor]
    simp [hv]
  have hw : ∀ i, (∑ j, minkowskiMetric i j * w j) = 0 := by
    intro i
    have hq := he (Pi.single i (1 : ℝ)) w
    rw [hev, hp, coordinate_pair_factor] at hq
    simpa [Pi.single_apply, ite_mul] using hq.symm
  have hz := coordinate_metric_no_kernel minkowskiMetric minkowskiMetric
    minkowski_inverse w hw
  rw [← hev, hz, map_zero]

/-- A trivial matrix kernel implies nonzero determinant. -/
theorem coordinate_det_ne_zero
    (g : Fin 4 → Fin 4 → ℝ)
    (hk : ∀ v : Fin 4 → ℝ, (∀ i, (∑ j, g i j * v j) = 0) → v = 0) :
    (Matrix.of g).det ≠ 0 := by
  let G : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of g
  have hi : Function.Injective G.mulVec := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hk
    have hz : G.mulVec (u - v) = 0 := by
      rw [Matrix.mulVec_sub, huv, sub_self]
    intro i
    simpa [G, Matrix.mulVec, dotProduct] using congrFun hz i
  exact ((Matrix.isUnit_iff_isUnit_det G).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero

/-- Determinants of smooth real matrix-entry functions are smooth. -/
theorem coordinate_det_smooth {d : Type*} [Fintype d] [DecidableEq d]
    (g : (Fin 4 → ℝ) → Matrix d d ℝ)
    (hg : ∀ i j, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => g x i j)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => (g x).det) := by
  classical
  simp_rw [Matrix.det_apply']
  apply ContDiff.sum
  intro σ hσ
  apply contDiff_const.mul
  apply contDiff_prod
  intro i hi
  exact hg (σ i) i

/-- Each adjugate entry is smooth by its determinant-minor formula. -/
theorem coordinate_adjugate_smooth
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (hg : ∀ i j, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => g x i j))
    (i j : Fin 4) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => (Matrix.of (g x)).adjugate i j) := by
  simp_rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  apply contDiff_const.mul
  apply coordinate_det_smooth
  intro a b
  exact hg (j.succAbove a) (i.succAbove b)

/-- Smoothness of the inverse is derived, not assumed, from smooth
entries and the pointwise nonzero determinant. -/
theorem coordinate_inverse_smooth
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (hg : ∀ i j, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => g x i j))
    (hd : ∀ x, (Matrix.of (g x)).det ≠ 0) (i j : Fin 4) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => coordinateMetricInverse g x i j) := by
  simp only [coordinateMetricInverse, Matrix.inv_def, Ring.inverse_eq_inv']
  change ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x =>
    ((Matrix.of (g x)).det)⁻¹ * (Matrix.of (g x)).adjugate i j)
  exact ((coordinate_det_smooth (fun x => Matrix.of (g x)) hg).inv hd).mul
    (coordinate_adjugate_smooth g hg i j)

/-- The constructed inverse is symmetric when the original metric is. -/
theorem coordinate_inverse_symmetric
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (hg : ∀ x i j, g x i j = g x j i)
    (x : Fin 4 → ℝ) (i j : Fin 4) :
    coordinateMetricInverse g x i j = coordinateMetricInverse g x j i := by
  have ht : (Matrix.of (g x)).transpose = Matrix.of (g x) := by
    ext a b
    exact hg x b a
  have hi : ((Matrix.of (g x))⁻¹).transpose = (Matrix.of (g x))⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, ht]
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) hi
  exact h.symm

/-- The constructed inverse satisfies the exact component inverse identity. -/
theorem coordinate_constructed_inverse
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (hd : ∀ x, (Matrix.of (g x)).det ≠ 0) (x : Fin 4 → ℝ) (i j : Fin 4) :
    (∑ l, coordinateMetricInverse g x i l * g x l j) =
      if i = j then 1 else 0 := by
  have h := Matrix.nonsing_inv_mul (Matrix.of (g x)) (isUnit_iff_ne_zero.mpr (hd x))
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) h
  simpa [Matrix.mul_apply, Matrix.one_apply, coordinateMetricInverse] using he

/-- A smooth symmetric Lorentzian metric alone yields the full Step 3A
metric/inverse data, including the formerly assumed inverse smoothness. -/
theorem lorentz_data_from_metric
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (hg : ∀ x i j, g x i j = g x j i)
    (hs : ∀ i j, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => g x i j))
    (hsig : ∀ x, hasLorentzSignature (g x)) :
    lorentzCoordinateData g (coordinateMetricInverse g) := by
  have hd (x : Fin 4 → ℝ) : (Matrix.of (g x)).det ≠ 0 :=
    coordinate_det_ne_zero (g x) (lorentz_signature_no_kernel (g x) (hsig x))
  exact ⟨hg, coordinate_inverse_symmetric g hg, coordinate_constructed_inverse g hd,
    hs, coordinate_inverse_smooth g hs hd, hsig⟩

/-- The Koszul-type coordinate identity forces the lowered coefficients
of any torsion-free metric-compatible array. -/
theorem coordinate_lc_lower_unique
    (g A : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (h : lorentzCoordinateData g A)
    (C : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hc : coordinateLC g C) (x : Fin 4 → ℝ) (k i j : Fin 4) :
    (∑ l, C x k i l * g x l j) = christoffelFirst (metricPartial g x) k i j := by
  let L : Fin 4 → Fin 4 → Fin 4 → ℝ := fun a b c => ∑ l, C x a b l * g x l c
  have ht (a b c : Fin 4) : L a b c = L b a c := by
    unfold L
    apply Finset.sum_congr rfl
    intro l hl
    rw [hc.1 x a b l]
  have hm (a b c : Fin 4) :
      metricPartial g x a b c = L a b c + L a c b := by
    have hh := hc.2 x a b c
    unfold tensorConnection at hh
    have he : (∑ l, C x a c l * g x b l) = L a c b := by
      unfold L
      apply Finset.sum_congr rfl
      intro l hl
      rw [h.1 x b l]
    rw [he] at hh
    change metricPartial g x a b c - L a b c - L a c b = 0 at hh
    linarith
  change L k i j = _
  unfold christoffelFirst
  linarith [hm k i j, hm i k j, hm j k i, ht k i j, ht k j i, ht i j k]

/-- No other array can satisfy the coordinate Levi-Civita identities. -/
theorem coordinate_lc_unique
    (g A : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (h : lorentzCoordinateData g A)
    (C : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hc : coordinateLC g C) : C = metricChristoffel g A := by
  rcases h with ⟨hg, hA, hinv, hs, hAs, hsig⟩
  have hd : lorentzCoordinateData g A := ⟨hg, hA, hinv, hs, hAs, hsig⟩
  funext x k i l
  let v : Fin 4 → ℝ := fun a => C x k i a - metricChristoffel g A x k i a
  have hv (j : Fin 4) : (∑ a, g x j a * v a) = 0 := by
    calc
      _ = (∑ a, C x k i a * g x a j) -
          (∑ a, metricChristoffel g A x k i a * g x a j) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a ha
        dsimp only [v]
        rw [hg x j a]
        ring
      _ = 0 := by
        rw [coordinate_lc_lower_unique g A hd C hc x k i j]
        change christoffelFirst (metricPartial g x) k i j -
          (∑ a, christoffelFromJet (A x) (metricPartial g x) k i a * g x a j) = 0
        rw [christoffel_lower_index (g x) (A x) (metricPartial g x) (hinv x)]
        ring
  have hz := coordinate_metric_no_kernel (g x) (A x) (hinv x) v hv
  exact sub_eq_zero.mp (congrFun hz l)

/-- Existence and uniqueness of the coordinate coefficients, with no
independently supplied inverse metric or connection. -/
theorem lorentz_coordinate_lc_exists_unique
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (hg : ∀ x i j, g x i j = g x j i)
    (hs : ∀ i j, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => g x i j))
    (hsig : ∀ x, hasLorentzSignature (g x)) :
    ∃! C : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ, coordinateLC g C := by
  let A := coordinateMetricInverse g
  have hd : lorentzCoordinateData g A := lorentz_data_from_metric g hg hs hsig
  refine ⟨metricChristoffel g A, ⟨?_, ?_⟩, ?_⟩
  · intro x k i l
    exact (lorentz_coordinate_connection g A hd x k i l).1
  · intro x k i j
    exact (lorentz_coordinate_connection g A hd x k i j).2
  · intro C hc
    exact coordinate_lc_unique g A hd C hc

/-- Smooth metric components have smooth partial derivatives. -/
theorem metric_partial_smooth
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (hs : ∀ i j, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => g x i j))
    (k i j : Fin 4) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => metricPartial g x k i j) := by
  unfold metricPartial
  have hd : ContDiff ℝ (⊤ : WithTop ℕ∞) (fderiv ℝ (fun x => g x i j)) :=
    (hs i j).fderiv_right (by simp)
  exact hd.clm_apply contDiff_const

/-- The actual coordinate connection coefficients are smooth. -/
theorem metric_christoffel_smooth
    (g A : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (h : lorentzCoordinateData g A) (k i l : Fin 4) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => metricChristoffel g A x k i l) := by
  rcases h with ⟨hg, hA, hinv, hs, hAs, hsig⟩
  unfold metricChristoffel christoffelFromJet christoffelFirst
  apply ContDiff.sum
  intro r hr
  exact (hAs r l).mul (((metric_partial_smooth g hs k i r).add
    (metric_partial_smooth g hs i k r)).sub
    (metric_partial_smooth g hs r k i)).div_const 2

/-- Differentiate the actual inverse identity along a coordinate line. -/
theorem coordinate_inverse_product_derivative
    (g A : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (h : lorentzCoordinateData g A) (x : Fin 4 → ℝ) (k i j : Fin 4) :
    (∑ l, metricPartial A x k i l * g x l j +
      A x i l * metricPartial g x k l j) = 0 := by
  rcases h with ⟨hg, hA, hinv, hs, hAs, hsig⟩
  let v : Fin 4 → ℝ := Pi.single k (1 : ℝ)
  have hder : HasDerivAt
      (fun t : ℝ => ∑ l, A (x + t • v) i l * g (x + t • v) l j)
      (∑ l, metricPartial A x k i l * g x l j +
        A x i l * metricPartial g x k l j) 0 := by
    apply HasDerivAt.fun_sum
    intro l hl
    have ha := metric_partial_line_derivative A x k i l
      ((hAs i l).contDiffAt.differentiableAt (by simp))
    have hb := metric_partial_line_derivative g x k l j
      ((hs l j).contDiffAt.differentiableAt (by simp))
    simpa [v] using ha.mul hb
  have he : (fun t : ℝ => ∑ l, A (x + t • v) i l * g (x + t • v) l j) =
      fun _ => if i = j then (1 : ℝ) else 0 := by
    funext t
    exact hinv (x + t • v) i j
  rw [he] at hder
  exact hder.unique (hasDerivAt_const (0 : ℝ) (if i = j then (1 : ℝ) else 0))

/-- Actual inverse derivative: dA = -A (dg) A, in matrix form. -/
theorem coordinate_inverse_derivative
    (g A : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (h : lorentzCoordinateData g A) (x : Fin 4 → ℝ) (k : Fin 4) :
    Matrix.of (metricPartial A x k) =
      -(Matrix.of (A x) * Matrix.of (metricPartial g x k) * Matrix.of (A x)) := by
  let G : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (g x)
  let B : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (A x)
  let DG : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (metricPartial g x k)
  let DB : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (metricPartial A x k)
  rcases h with ⟨hg, hA, hinv, hs, hAs, hsig⟩
  have hd : lorentzCoordinateData g A := ⟨hg, hA, hinv, hs, hAs, hsig⟩
  have hGB : G * B = 1 := by
    ext i j
    simpa [G, B, Matrix.mul_apply, Matrix.one_apply] using
      coordinate_inverse_left (g x) (A x) (hg x) (hA x) (hinv x) i j
  have hp : DB * G + B * DG = 0 := by
    ext i j
    simpa [DB, G, B, DG, Matrix.mul_apply, ← Finset.sum_add_distrib] using
      coordinate_inverse_product_derivative g A hd x k i j
  have he : DB * G = -(B * DG) := by
    calc
      DB * G = (DB * G + B * DG) - B * DG := by abel
      _ = -(B * DG) := by rw [hp, zero_sub]
  change DB = -(B * DG * B)
  calc
    DB = DB * (G * B) := by rw [hGB, mul_one]
    _ = (DB * G) * B := by rw [mul_assoc]
    _ = -(B * DG * B) := by rw [he, neg_mul]

/-- Metric compatibility for the inverse, in the exact index convention
required by the previously verified kinetic-trace derivative. -/
theorem coordinate_inverse_metric_compatible
    (g A : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (h : lorentzCoordinateData g A) (x : Fin 4 → ℝ) (k i j : Fin 4) :
    metricPartial A x k i j =
      -(∑ l, metricChristoffel g A x k l i * A x l j) -
      (∑ l, metricChristoffel g A x k l j * A x i l) := by
  let G : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (g x)
  let B : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (A x)
  let DG : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (metricPartial g x k)
  let C : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (metricChristoffel g A x k)
  have hd := coordinate_inverse_derivative g A h x k
  rcases h with ⟨hg, hA, hinv, hs, hAs, hsig⟩
  have hh : lorentzCoordinateData g A := ⟨hg, hA, hinv, hs, hAs, hsig⟩
  have hBG : B * G = 1 := by
    ext a b
    simpa [B, G, Matrix.mul_apply, Matrix.one_apply] using hinv x a b
  have hGB : G * B = 1 := by
    ext a b
    simpa [B, G, Matrix.mul_apply, Matrix.one_apply] using
      coordinate_inverse_left (g x) (A x) (hg x) (hA x) (hinv x) a b
  have hDG : DG = C * G + G * C.transpose := by
    ext a b
    have hc := (lorentz_coordinate_connection g A hh x k a b).2
    unfold tensorConnection at hc
    simp only [DG, C, G, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    change metricPartial g x k a b =
      (∑ l, metricChristoffel g A x k a l * g x l b) +
      (∑ l, g x a l * metricChristoffel g A x k b l)
    have hsum : (∑ l, g x a l * metricChristoffel g A x k b l) =
        ∑ l, metricChristoffel g A x k b l * g x a l := by
      apply Finset.sum_congr rfl
      intro l hl
      ring
    rw [hsum]
    linarith
  have he : B * DG * B = B * C + C.transpose * B := by
    rw [hDG, mul_add, add_mul]
    calc
      B * (C * G) * B + B * (G * C.transpose) * B =
          (B * C) * (G * B) + ((B * G) * C.transpose) * B := by
        simp only [mul_assoc]
      _ = _ := by rw [hGB, hBG, mul_one, one_mul]
  change Matrix.of (metricPartial A x k) = -(B * DG * B) at hd
  rw [he] at hd
  have hz := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i j) hd
  have hz' : metricPartial A x k i j =
      -((∑ l, A x i l * metricChristoffel g A x k l j) +
        (∑ l, metricChristoffel g A x k l i * A x l j)) := by
    simpa [B, C, Matrix.mul_apply, Matrix.transpose_apply] using hz
  rw [hz']
  have hsum : (∑ l, A x i l * metricChristoffel g A x k l j) =
      ∑ l, metricChristoffel g A x k l j * A x i l := by
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hsum]
  ring

end MicroMacro

#print axioms MicroMacro.coordinate_pair_factor
#print axioms MicroMacro.lorentz_signature_no_kernel
#print axioms MicroMacro.coordinate_det_ne_zero
#print axioms MicroMacro.coordinate_det_smooth
#print axioms MicroMacro.coordinate_adjugate_smooth
#print axioms MicroMacro.coordinate_inverse_smooth
#print axioms MicroMacro.coordinate_inverse_symmetric
#print axioms MicroMacro.coordinate_constructed_inverse
#print axioms MicroMacro.lorentz_data_from_metric
#print axioms MicroMacro.coordinate_lc_lower_unique
#print axioms MicroMacro.coordinate_lc_unique
#print axioms MicroMacro.lorentz_coordinate_lc_exists_unique
#print axioms MicroMacro.metric_partial_smooth
#print axioms MicroMacro.metric_christoffel_smooth
#print axioms MicroMacro.coordinate_inverse_product_derivative
#print axioms MicroMacro.coordinate_inverse_derivative
#print axioms MicroMacro.coordinate_inverse_metric_compatible
#print axioms MicroMacro.coordinateMetricInverse
#print axioms MicroMacro.coordinateLC
