import Step3D

/-! Second checkpoint: algebraic first Bianchi identity derived from
actual coordinate connection derivatives and torsion symmetry, plus the
intrinsic commutator definition built from the Step 3C operator.
No coordinate/intrinsic equivalence or tensoriality is asserted yet. -/
namespace MicroMacro
open scoped BigOperators Topology Manifold ContDiff

theorem curvature_partial_torsion_symmetry
    (Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h : ∀ x i j l, Γ x i j l = Γ x j i l)
    (x : Fin 4 → ℝ) (i j k l : Fin 4) :
    curvatureConnectionPartial Γ x i j k l =
      curvatureConnectionPartial Γ x i k j l := by
  have he : (fun y => Γ y j k l) = fun y => Γ y k j l := by
    funext y
    exact h y j k l
  unfold curvatureConnectionPartial
  rw [he]

/-- The algebraic first Bianchi identity for an actual torsion-free
coordinate connection. Symmetry is imposed on the coefficient field,
not on an independent curvature array. -/
theorem coordinate_first_bianchi
    (Γ : (Fin 4 → ℝ) → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h : ∀ x i j l, Γ x i j l = Γ x j i l)
    (x : Fin 4 → ℝ) (i j k l : Fin 4) :
    coordinateRiemann Γ x i j k l +
      coordinateRiemann Γ x j k i l +
      coordinateRiemann Γ x k i j l = 0 := by
  have hs (a b c : Fin 4) := curvature_partial_torsion_symmetry Γ h x a b c l
  have hsum :
      (∑ m : Fin 4, (Γ x j k m * Γ x i m l - Γ x i k m * Γ x j m l)) +
      (∑ m : Fin 4, (Γ x k i m * Γ x j m l - Γ x j i m * Γ x k m l)) +
      (∑ m : Fin 4, (Γ x i j m * Γ x k m l - Γ x k j m * Γ x i m l)) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro m hm
    rw [h x k i m, h x j i m, h x k j m]
    ring
  unfold coordinateRiemann
  rw [hs i j k, hs j k i, hs k i j]
  calc
    _ = (∑ m : Fin 4, (Γ x j k m * Γ x i m l - Γ x i k m * Γ x j m l)) +
        (∑ m : Fin 4, (Γ x k i m * Γ x j m l - Γ x j i m * Γ x k m l)) +
        (∑ m : Fin 4, (Γ x i j m * Γ x k m l - Γ x k j m * Γ x i m l)) := by ring
    _ = 0 := hsum

theorem metric_christoffel_torsion_symmetry
    (g A : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (h : ∀ x i j, g x i j = g x j i)
    (x : Fin 4 → ℝ) (i j l : Fin 4) :
    metricChristoffel g A x i j l = metricChristoffel g A x j i l := by
  have hm (a b c : Fin 4) : metricPartial g x a b c = metricPartial g x a c b := by
    have he : (fun y => g y b c) = fun y => g y c b := by
      funext y
      exact h y b c
    unfold metricPartial
    rw [he]
  unfold metricChristoffel christoffelFromJet
  apply Finset.sum_congr rfl
  intro m hm'
  unfold christoffelFirst
  rw [hm m j i]
  ring

theorem metric_coordinate_first_bianchi
    (g A : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (h : ∀ x i j, g x i j = g x j i)
    (x : Fin 4 → ℝ) (i j k l : Fin 4) :
    coordinateRiemann (metricChristoffel g A) x i j k l +
      coordinateRiemann (metricChristoffel g A) x j k i l +
      coordinateRiemann (metricChristoffel g A) x k i j l = 0 := by
  exact coordinate_first_bianchi _ (metric_christoffel_torsion_symmetry g A h) x i j k l

local notation "E4" => (Fin 4 → ℝ)
local notation "I4" => 𝓘(ℝ, E4)
section Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
  [IsManifold I4 2 M] [IsManifold I4 1 M]
set_option quotPrecheck false in
local notation "Field4" => (∀ p : M, TangentSpace I4 p)
set_option quotPrecheck false in
local notation "Metric4" => (∀ p : M, TangentSpace I4 p →L[ℝ] TangentSpace I4 p →L[ℝ] ℝ)

/-- Intrinsic curvature commutator built from the certified covariant
derivative and Mathlib manifold Lie bracket. Total outside the regular
domain; subsequent tensoriality results must state regularity. -/
noncomputable def chartIntrinsicRiemann (G : Metric4) (X Y Z : Field4)
    (p : M) : TangentSpace I4 p :=
  chartIntrinsicCovariantDerivative G X (chartIntrinsicCovariantDerivative G Y Z) p -
  chartIntrinsicCovariantDerivative G Y (chartIntrinsicCovariantDerivative G X Z) p -
  chartIntrinsicCovariantDerivative G (VectorField.mlieBracket I4 X Y) Z p

/-- Torsion-free curvature skew symmetry, via direction additivity and
the actual intrinsic torsion identity. -/
theorem chart_intrinsic_riemann_skew (G : Metric4)
    (hs : ∀ p u v, G p u v = G p v u)
    (hsig : ∀ p, ∃ e : E4 ≃ₗ[ℝ] E4, ∀ u v, G p (e u) (e v) =
      coordinateMetricPair minkowskiMetric u v)
    (hd : ∀ p i j, DifferentiableAt ℝ (fun z => chartIntrinsicComponents G p z i j)
      (extChartAt I4 p p))
    (X Y Z : Field4) (p : M) :
    chartIntrinsicRiemann G X Y Z p = -chartIntrinsicRiemann G Y X Z p := by
  have hb : (fun q => VectorField.mlieBracket I4 X Y q) =
      fun q => (-1 : ℝ) • VectorField.mlieBracket I4 Y X q := by
    funext q
    rw [← chart_intrinsic_torsion G hs hsig q X Y (hd q),
        ← chart_intrinsic_torsion G hs hsig q Y X (hd q)]
    rw [neg_one_smul]
    abel
  have hc : chartIntrinsicCovariantDerivative G (VectorField.mlieBracket I4 X Y) Z =
      fun q => (-1 : ℝ) • chartIntrinsicCovariantDerivative G
        (VectorField.mlieBracket I4 Y X) Z q := by
    rw [show VectorField.mlieBracket I4 X Y =
      (fun q => (-1 : ℝ) • VectorField.mlieBracket I4 Y X q) from hb]
    exact chart_intrinsic_direction_smul G (fun _ => -1) (VectorField.mlieBracket I4 Y X) Z
  have hcp := congrFun hc p
  unfold chartIntrinsicRiemann
  rw [hcp, neg_one_smul]
  abel

end Manifold
end MicroMacro

#print axioms MicroMacro.curvature_partial_torsion_symmetry
#print axioms MicroMacro.coordinate_first_bianchi
#print axioms MicroMacro.metric_christoffel_torsion_symmetry
#print axioms MicroMacro.metric_coordinate_first_bianchi
#print axioms MicroMacro.chartIntrinsicRiemann
#print axioms MicroMacro.chart_intrinsic_riemann_skew
