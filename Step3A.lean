import Covariance

/-! Step 3A: coordinate Lorentzian foundations on the real four-dimensional
model space. No global connection, chart-transition law or field equation
is assumed or claimed in this module. -/

namespace MicroMacro

open scoped BigOperators

/-- The standard Lorentzian matrix, with the time coordinate first. -/
noncomputable def minkowskiMetric (i j : Fin 4) : ℝ :=
  if i = j then (if i = 0 then -1 else 1) else 0

/-- The bilinear pairing of a coordinate metric. -/
noncomputable def coordinateMetricPair (g : Fin 4 → Fin 4 → ℝ)
    (u v : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, g i j * u i * v j

/-- Signature (-,+,+,+) means congruence to the standard Lorentz form
by an invertible real linear change of frame. -/
def hasLorentzSignature (g : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∃ e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ),
    ∀ u v, coordinateMetricPair g (e u) (e v) =
      coordinateMetricPair minkowskiMetric u v

/-- Coordinate metric data: symmetric smooth metric and symmetric smooth
inverse, a right inverse identity, and a Lorentzian frame at every point.
Inverse smoothness is an explicit hypothesis, not an existence theorem.
The domain is the whole model space in this initial checkpoint. -/
def lorentzCoordinateData
    (g A : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) : Prop :=
  (∀ x i j, g x i j = g x j i) ∧
  (∀ x i j, A x i j = A x j i) ∧
  (∀ x i j, (∑ l, A x i l * g x l j) = if i = j then 1 else 0) ∧
  (∀ i j, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => g x i j)) ∧
  (∀ i j, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun x => A x i j)) ∧
  (∀ x, hasLorentzSignature (g x))

/-- An actual coordinate partial derivative, not an independent jet. -/
noncomputable def metricPartial
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (x : Fin 4 → ℝ) (k i j : Fin 4) : ℝ :=
  fderiv ℝ (fun y => g y i j) x (Pi.single k (1 : ℝ))

/-- The Christoffel expression of the first kind. -/
noncomputable def christoffelFirst
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (k i j : Fin 4) : ℝ :=
  (dg k i j + dg i k j - dg j k i) / 2

/-- The connection coefficient with lower indices k,i and upper index l.
The symmetric inverse is written A r l for the contraction convention
used in the previously verified inverse_metric_contraction theorem. -/
noncomputable def christoffelFromJet
    (A : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (k i l : Fin 4) : ℝ :=
  ∑ r, A r l * christoffelFirst dg k i r

/-- The actual Christoffel formula obtained from metric derivatives. -/
noncomputable def metricChristoffel
    (g A : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (x : Fin 4 → ℝ) (k i l : Fin 4) : ℝ :=
  christoffelFromJet (A x) (metricPartial g x) k i l

/-- The two matrix inverse equations follow from one and symmetry. -/
theorem coordinate_inverse_left
    (g A : Fin 4 → Fin 4 → ℝ)
    (hg : ∀ i j, g i j = g j i) (hA : ∀ i j, A i j = A j i)
    (hinv : ∀ i j, (∑ l, A i l * g l j) = if i = j then 1 else 0)
    (i j : Fin 4) :
    (∑ l, g i l * A l j) = if i = j then 1 else 0 := by
  calc
    (∑ l, g i l * A l j) = ∑ l, A j l * g l i := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [hg i l, hA l j, mul_comm]
    _ = if j = i then 1 else 0 := hinv j i
    _ = _ := by rw [eq_comm]

/-- A vector annihilated by the metric matrix is zero.
This supplies nondegeneracy independently of the signature witness. -/
theorem coordinate_metric_no_kernel
    (g A : Fin 4 → Fin 4 → ℝ)
    (hinv : ∀ i j, (∑ l, A i l * g l j) = if i = j then 1 else 0)
    (v : Fin 4 → ℝ) (hv : ∀ i, (∑ j, g i j * v j) = 0) : v = 0 := by
  funext i
  have h : (∑ l, A i l * (∑ j, g l j * v j)) = 0 := by
    simp [hv]
  calc
    v i = ∑ j, (if i = j then 1 else 0) * v j := by
      simp [ite_mul]
    _ = ∑ j, (∑ l, A i l * g l j) * v j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hinv]
    _ = ∑ j, ∑ l, A i l * (g l j * v j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = ∑ l, ∑ j, A i l * (g l j * v j) := Finset.sum_comm
    _ = ∑ l, A i l * (∑ j, g l j * v j) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.mul_sum]
    _ = 0 := h

/-- Matrix symmetry propagates to actual multivariable derivatives. -/
theorem metric_partial_symmetric
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (hg : ∀ x i j, g x i j = g x j i)
    (x : Fin 4 → ℝ) (k i j : Fin 4) :
    metricPartial g x k i j = metricPartial g x k j i := by
  have he : (fun y => g y i j) = (fun y => g y j i) := by
    funext y
    exact hg y i j
  unfold metricPartial
  rw [he]

/-- The directional derivative is the derivative along the coordinate
line through x, by the actual Frechet chain rule. -/
theorem metric_partial_line_derivative
    (g : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (x : Fin 4 → ℝ) (k i j : Fin 4)
    (hg : DifferentiableAt ℝ (fun y => g y i j) x) :
    HasDerivAt (fun t : ℝ => g (x + t • Pi.single k (1 : ℝ)) i j)
      (metricPartial g x k i j) 0 := by
  let v : Fin 4 → ℝ := Pi.single k 1
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa only [zero_add, one_smul] using
      (hasDerivAt_const (0 : ℝ) x).add
        ((hasDerivAt_id' (0 : ℝ)).smul_const v)
  have hc := hg.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl
    (by simp : x = x + (0 : ℝ) • v)
  simpa only [Function.comp_def, metricPartial, v] using hc

/-- Torsion-free coefficients follow from the metric derivative symmetry. -/
theorem christoffel_jet_torsion_free
    (A : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hd : ∀ k i j, dg k i j = dg k j i)
    (k i l : Fin 4) :
    christoffelFromJet A dg k i l = christoffelFromJet A dg i k l := by
  unfold christoffelFromJet
  apply Finset.sum_congr rfl
  intro r hr
  unfold christoffelFirst
  rw [hd r k i]
  ring

/-- Lowering the upper index recovers the Christoffel expression of
the first kind, using the verified Step 1 inverse contraction. -/
theorem christoffel_lower_index
    (g A : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hinv : ∀ i j, (∑ l, A i l * g l j) = if i = j then 1 else 0)
    (k i j : Fin 4) :
    (∑ l, christoffelFromJet A dg k i l * g l j) =
      christoffelFirst dg k i j := by
  calc
    (∑ l, christoffelFromJet A dg k i l * g l j) =
        ∑ l, ∑ r, A r l * (g l j * christoffelFirst dg k i r) := by
      apply Finset.sum_congr rfl
      intro l hl
      unfold christoffelFromJet
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = ∑ r, ∑ l, A r l * (g l j * christoffelFirst dg k i r) :=
      Finset.sum_comm
    _ = _ := inverse_metric_contraction Finset.univ A g
      (christoffelFirst dg k i) j (Finset.mem_univ j) (fun r => hinv r j)

/-- The constructed connection is metric compatible, in the actual
tensorConnection convention of the certified Step 2 module. -/
theorem christoffel_jet_metric_compatible
    (g A : Fin 4 → Fin 4 → ℝ) (dg : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hg : ∀ i j, g i j = g j i)
    (hd : ∀ k i j, dg k i j = dg k j i)
    (hinv : ∀ i j, (∑ l, A i l * g l j) = if i = j then 1 else 0)
    (k i j : Fin 4) :
    tensorConnection Finset.univ (christoffelFromJet A dg k) g (dg k) i j = 0 := by
  have h₂ : (∑ l, christoffelFromJet A dg k j l * g i l) =
      christoffelFirst dg k j i := by
    calc
      _ = ∑ l, christoffelFromJet A dg k j l * g l i := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [hg i l]
      _ = _ := christoffel_lower_index g A dg hinv k j i
  unfold tensorConnection
  rw [christoffel_lower_index g A dg hinv k i j, h₂]
  unfold christoffelFirst
  rw [hd k j i]
  ring

/-- Smooth Lorentzian coordinate data yields an actual torsion-free,
metric-compatible connection expression, not a free connection jet. -/
theorem lorentz_coordinate_connection
    (g A : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (h : lorentzCoordinateData g A) (x : Fin 4 → ℝ) (k i j : Fin 4) :
    metricChristoffel g A x k i j = metricChristoffel g A x i k j ∧
    tensorConnection Finset.univ (metricChristoffel g A x k)
      (g x) (metricPartial g x k) i j = 0 := by
  rcases h with ⟨hg, hA, hinv, hs, hAs, hsig⟩
  exact ⟨christoffel_jet_torsion_free (A x) (metricPartial g x)
      (metric_partial_symmetric g hg x) k i j,
    christoffel_jet_metric_compatible (g x) (A x) (metricPartial g x)
      (hg x) (metric_partial_symmetric g hg x) (hinv x) k i j⟩

/-- Minkowski space supplies a nonvacuous instance of the signature. -/
theorem minkowski_signature : hasLorentzSignature minkowskiMetric := by
  exact ⟨LinearEquiv.refl ℝ (Fin 4 → ℝ), fun u v => rfl⟩

theorem minkowski_symmetric (i j : Fin 4) :
    minkowskiMetric i j = minkowskiMetric j i := by
  by_cases h : i = j
  · subst j
    rfl
  · simp [minkowskiMetric, h, Ne.symm h]

theorem minkowski_inverse (i j : Fin 4) :
    (∑ l, minkowskiMetric i l * minkowskiMetric l j) =
      if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [minkowskiMetric, Fin.sum_univ_succ]

/-- The explicit diagonal has one negative and three positive entries. -/
theorem minkowski_diagonal_signature :
    minkowskiMetric 0 0 = -1 ∧ minkowskiMetric 1 1 = 1 ∧
    minkowskiMetric 2 2 = 1 ∧ minkowskiMetric 3 3 = 1 := by
  norm_num [minkowskiMetric]

theorem minkowski_coordinate_data :
    lorentzCoordinateData (fun _ => minkowskiMetric) (fun _ => minkowskiMetric) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x i j
    exact minkowski_symmetric i j
  · intro x i j
    exact minkowski_symmetric i j
  · intro x i j
    exact minkowski_inverse i j
  · intro i j
    exact contDiff_const
  · intro i j
    exact contDiff_const
  · intro x
    exact minkowski_signature

theorem minkowski_partial_zero (x : Fin 4 → ℝ) (k i j : Fin 4) :
    metricPartial (fun _ => minkowskiMetric) x k i j = 0 := by
  unfold metricPartial
  have h : fderiv ℝ (fun _ : Fin 4 → ℝ => minkowskiMetric i j) x = 0 :=
    (hasFDerivAt_const (minkowskiMetric i j) x).fderiv
  rw [h]
  rfl

/-- In Cartesian Minkowski coordinates the constructed connection is zero. -/
theorem minkowski_christoffel_zero (x : Fin 4 → ℝ) (k i j : Fin 4) :
    metricChristoffel (fun _ => minkowskiMetric) (fun _ => minkowskiMetric)
      x k i j = 0 := by
  simp [metricChristoffel, christoffelFromJet, christoffelFirst,
    minkowski_partial_zero]

/-- Reuse the certified local metric stress divergence theorem with
the inverse and symmetry now supplied by coordinate metric data.
The symmetric Hessian and on-shell trace remain explicit hypotheses;
their realization by actual fields is reserved for the next phases. -/
theorem lorentz_coordinate_stress_on_shell_jet
    (g A : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (h : lorentzCoordinateData g A) (x : Fin 4 → ℝ)
    (p : Fin 4 → ℝ) (H : Fin 4 → Fin 4 → ℝ)
    (m2 u : ℝ) (ν : Fin 4)
    (hH : ∀ i j, H i j = H j i)
    (hkg : (∑ i, ∑ j, A x i j * H i j) = m2*u) :
    (∑ i, ∑ j, A x i j *
      (2*(H i j*p ν+p j*H i ν)-g x j ν*
        ((∑ a, ∑ b, A x a b*(H i a*p b+p a*H i b))+
          2*m2*u*p i))) = 0 := by
  rcases h with ⟨hg, hA, hinv, hs, hAs, hsig⟩
  exact local_metric_stress_on_shell Finset.univ (A x) (g x) p H m2 u ν
    (Finset.mem_univ ν) (hA x) hH (fun i => hinv i ν) hkg

end MicroMacro

#print axioms MicroMacro.coordinate_inverse_left
#print axioms MicroMacro.coordinate_metric_no_kernel
#print axioms MicroMacro.metric_partial_symmetric
#print axioms MicroMacro.metric_partial_line_derivative
#print axioms MicroMacro.christoffel_jet_torsion_free
#print axioms MicroMacro.christoffel_lower_index
#print axioms MicroMacro.christoffel_jet_metric_compatible
#print axioms MicroMacro.lorentz_coordinate_connection
#print axioms MicroMacro.minkowski_signature
#print axioms MicroMacro.minkowski_symmetric
#print axioms MicroMacro.minkowski_inverse
#print axioms MicroMacro.minkowski_diagonal_signature
#print axioms MicroMacro.minkowski_coordinate_data
#print axioms MicroMacro.minkowski_partial_zero
#print axioms MicroMacro.minkowski_christoffel_zero
#print axioms MicroMacro.lorentz_coordinate_stress_on_shell_jet
#print axioms MicroMacro.minkowskiMetric
#print axioms MicroMacro.coordinateMetricPair
#print axioms MicroMacro.hasLorentzSignature
#print axioms MicroMacro.lorentzCoordinateData
#print axioms MicroMacro.metricPartial
#print axioms MicroMacro.christoffelFirst
#print axioms MicroMacro.christoffelFromJet
#print axioms MicroMacro.metricChristoffel
