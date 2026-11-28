import Step3CLeviCivita

/-! Step 3D first checkpoint: actual coordinate curvature of a
connection coefficient field. The convention is R(U,V)W =
∇_U ∇_V W - ∇_V ∇_U W - ∇_[U,V] W.
Tensoriality and intrinsic chart independence are later obligations. -/

namespace MicroMacro
open scoped BigOperators

/-- Actual directional partial of the connection coefficient field. -/
noncomputable def curvatureConnectionPartial
    (Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Fin 4 → ℝ) (i j k l : Fin 4) : ℝ :=
  fderiv ℝ (fun y => Γ y j k l) x (Pi.single i (1 : ℝ))

/-- R(∂i,∂j)∂k, component l, with actual coefficient derivatives. -/
noncomputable def coordinateRiemann
    (Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Fin 4 → ℝ) (i j k l : Fin 4) : ℝ :=
  curvatureConnectionPartial Γ x i j k l -
  curvatureConnectionPartial Γ x j i k l +
  (∑ m : Fin 4, (Γ x j k m * Γ x i m l - Γ x i k m * Γ x j m l))

theorem coordinate_riemann_skew
    (Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Fin 4 → ℝ) (i j k l : Fin 4) :
    coordinateRiemann Γ x i j k l = - coordinateRiemann Γ x j i k l := by
  unfold coordinateRiemann
  have h : (∑ m : Fin 4, (Γ x j k m * Γ x i m l - Γ x i k m * Γ x j m l)) =
      ∑ m : Fin 4, -(Γ x i k m * Γ x j m l - Γ x j k m * Γ x i m l) := by
    apply Finset.sum_congr rfl
    intro m hm
    ring
  rw [h, Finset.sum_neg_distrib]
  ring

theorem coordinate_riemann_diagonal
    (Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Fin 4 → ℝ) (i k l : Fin 4) :
    coordinateRiemann Γ x i i k l = 0 := by
  simp [coordinateRiemann]

/-- Ricci contraction with the fixed curvature sign convention. -/
noncomputable def coordinateRicci
    (Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Fin 4 → ℝ) (j k : Fin 4) : ℝ :=
  ∑ i : Fin 4, coordinateRiemann Γ x i j k i

/-- Scalar curvature from the inverse metric and Ricci contraction. -/
noncomputable def coordinateScalarCurvature
    (A : Fin 4 → Fin 4 → ℝ)
    (Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Fin 4 → ℝ) : ℝ :=
  ∑ j : Fin 4, ∑ k : Fin 4, A j k * coordinateRicci Γ x j k

/-- Einstein tensor candidate; conservation is not asserted here. -/
noncomputable def coordinateEinstein
    (g A : Fin 4 → Fin 4 → ℝ)
    (Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (x : Fin 4 → ℝ) (j k : Fin 4) : ℝ :=
  coordinateRicci Γ x j k - (1 / 2 : ℝ) * g j k * coordinateScalarCurvature A Γ x

theorem coordinate_riemann_zero_connection
    (Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h : ∀ x i j k, Γ x i j k = 0)
    (x : Fin 4 → ℝ) (i j k l : Fin 4) :
    coordinateRiemann Γ x i j k l = 0 := by
  have he (a b c : Fin 4) : (fun y => Γ y a b c) = fun _ => (0 : ℝ) := by
    funext y
    exact h y a b c
  simp [coordinateRiemann, curvatureConnectionPartial, he, h]

theorem minkowski_riemann_zero (x : Fin 4 → ℝ) (i j k l : Fin 4) :
    coordinateRiemann (metricChristoffel (fun _ => minkowskiMetric)
      (fun _ => minkowskiMetric)) x i j k l = 0 := by
  exact coordinate_riemann_zero_connection _ minkowski_christoffel_zero x i j k l

theorem minkowski_ricci_zero (x : Fin 4 → ℝ) (j k : Fin 4) :
    coordinateRicci (metricChristoffel (fun _ => minkowskiMetric)
      (fun _ => minkowskiMetric)) x j k = 0 := by
  simp [coordinateRicci, minkowski_riemann_zero]

theorem minkowski_scalar_curvature_zero (x : Fin 4 → ℝ) :
    coordinateScalarCurvature minkowskiMetric
      (metricChristoffel (fun _ => minkowskiMetric) (fun _ => minkowskiMetric)) x = 0 := by
  simp [coordinateScalarCurvature, minkowski_ricci_zero]

theorem minkowski_einstein_zero (x : Fin 4 → ℝ) (j k : Fin 4) :
    coordinateEinstein minkowskiMetric minkowskiMetric
      (metricChristoffel (fun _ => minkowskiMetric) (fun _ => minkowskiMetric)) x j k = 0 := by
  simp [coordinateEinstein, minkowski_ricci_zero, minkowski_scalar_curvature_zero]

end MicroMacro

#print axioms MicroMacro.curvatureConnectionPartial
#print axioms MicroMacro.coordinateRiemann
#print axioms MicroMacro.coordinate_riemann_skew
#print axioms MicroMacro.coordinate_riemann_diagonal
#print axioms MicroMacro.coordinateRicci
#print axioms MicroMacro.coordinateScalarCurvature
#print axioms MicroMacro.coordinateEinstein
#print axioms MicroMacro.coordinate_riemann_zero_connection
#print axioms MicroMacro.minkowski_riemann_zero
#print axioms MicroMacro.minkowski_ricci_zero
#print axioms MicroMacro.minkowski_scalar_curvature_zero
#print axioms MicroMacro.minkowski_einstein_zero
