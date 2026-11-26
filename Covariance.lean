import Mathlib

/-! Paper I: finite algebraic foundations. These statements are not a
formalization of differential geometry, general relativity, or the RH
analytic benchmark. -/

namespace MicroMacro

theorem centered_shift {ι : Type*} (s : Finset ι)
    (q x : ι → ℝ) (d : ℝ)
    (h : (s.sum fun i => q i * x i) = 0) :
    (s.sum fun i => q i * (x i + d)^2) =
      (s.sum fun i => q i * x i^2) + (s.sum q) * d^2 := by
  calc
    (s.sum fun i => q i * (x i + d)^2) =
        (s.sum fun i => (q i * x i^2 + (2*d) * (q i*x i)) + q i*d^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (s.sum fun i => q i*x i^2) + (2*d)*(s.sum fun i => q i*x i)
          + (s.sum q)*d^2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul]
    _ = _ := by rw [h]; ring

theorem residual_nonnegative {ι : Type*} (s : Finset ι)
    (q x : ι → ℝ) (a : ℝ) (hq : ∀ i ∈ s, 0 ≤ q i) :
    0 ≤ (s.sum fun i => q i * (x i - a)^2) := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hq i hi) (sq_nonneg (x i - a))

theorem weighted_covariance {ι : Type*} (s : Finset ι)
    (q x : ι → ℝ) (a : ℝ)
    (ha : (s.sum fun i => q i*x i) = (s.sum q)*a) :
    (s.sum fun i => q i*x i^2) =
      (s.sum fun i => q i*(x i-a)^2) + (s.sum q)*a^2 := by
  have h : (s.sum fun i => q i*(x i-a)) = 0 := by
    calc
      (s.sum fun i => q i*(x i-a)) =
          (s.sum fun i => q i*x i - q i*a) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ha]; ring
  calc
    (s.sum fun i => q i*x i^2) =
        (s.sum fun i => q i*((x i-a)+a)^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := centered_shift s q (fun i => x i-a) a h

theorem two_block_variance (q₁ q₂ a₁ a₂ : ℝ) :
    (q₁+q₂)*(q₁*a₁^2+q₂*a₂^2) - (q₁*a₁+q₂*a₂)^2 =
      q₁*q₂*(a₁-a₂)^2 := by
  ring

theorem two_block_hierarchy (q₁ q₂ a₁ a₂ a : ℝ)
    (h : q₁*a₁ + q₂*a₂ = (q₁+q₂)*a) :
    q₁*a₁^2 + q₂*a₂^2 =
      (q₁+q₂)*a^2 + q₁*(a₁-a)^2 + q₂*(a₂-a)^2 := by
  linear_combination 2*a*h

theorem two_block_increment_nonnegative (q₁ q₂ a₁ a₂ a : ℝ)
    (h₁ : 0 ≤ q₁) (h₂ : 0 ≤ q₂) :
    0 ≤ q₁*(a₁-a)^2 + q₂*(a₂-a)^2 := by
  exact add_nonneg (mul_nonneg h₁ (sq_nonneg _))
    (mul_nonneg h₂ (sq_nonneg _))

theorem nested_shift {ι κ : Type*} (s : Finset ι) (blocks : ι → Finset κ)
    (q x : ι → κ → ℝ) (a : ι → ℝ) (b : ℝ)
    (h : ∀ j ∈ s, (blocks j).sum (fun i => q j i * (x j i - a j)) = 0) :
    (s.sum fun j => (blocks j).sum fun i => q j i * (x j i - b)^2) =
      (s.sum fun j => (blocks j).sum fun i => q j i * (x j i - a j)^2) +
      (s.sum fun j => ((blocks j).sum (q j)) * (a j - b)^2) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (blocks j).sum (fun i => q j i * (x j i - b)^2) =
        (blocks j).sum (fun i => q j i * ((x j i - a j) + (a j - b))^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := centered_shift (blocks j) (q j) (fun i => x j i - a j) (a j - b) (h j hj)

theorem energy_flux_gap (t x y z : ℝ) :
    (t^2 + x^2 + y^2 + z^2)^2 -
      ((2*t*x)^2 + (2*t*y)^2 + (2*t*z)^2) =
      (t^2 - x^2 - y^2 - z^2)^2 := by
  ring

theorem complex_gram_identity (a b c d : ℝ) :
    (a^2+b^2)*(c^2+d^2) - (a*c+b*d)^2 = (a*d-b*c)^2 := by
  ring

theorem closure_witness (r k : ℝ) (hr : 0 < r) (hk : k ≠ 0) :
    2*r*k^2 ≠ 0 := by
  exact ne_of_gt (mul_pos (mul_pos (by norm_num) hr) (sq_pos_of_ne_zero hk))

/-- Componentwise covariance, for arbitrary contractions of two covectors. -/
theorem weighted_cross_covariance {ι : Type*} (s : Finset ι)
    (q x y : ι → ℝ) (a b : ℝ)
    (hx : (s.sum fun i => q i*x i) = (s.sum q)*a)
    (hy : (s.sum fun i => q i*y i) = (s.sum q)*b) :
    (s.sum fun i => q i*x i*y i) =
      (s.sum fun i => q i*((x i-a)*(y i-b))) + (s.sum q)*a*b := by
  have he : (s.sum fun i => q i*((x i-a)*(y i-b))) =
      (s.sum fun i => q i*x i*y i) - (s.sum q)*a*b := by
    calc
      (s.sum fun i => q i*((x i-a)*(y i-b))) =
          (s.sum fun i => ((q i*x i*y i - (q i*x i)*b) - a*(q i*y i)) + q i*(a*b)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, hx, hy]
        ring
  rw [he]
  ring

/-- Nonnegative coarse-minus-fine residual for arbitrary finite nested blocks. -/
theorem nested_monotonicity {ι κ : Type*} (s : Finset ι) (blocks : ι → Finset κ)
    (q x : ι → κ → ℝ) (a : ι → ℝ) (b : ℝ)
    (h : ∀ j ∈ s, (blocks j).sum (fun i => q j i * (x j i - a j)) = 0)
    (hq : ∀ j ∈ s, ∀ i ∈ blocks j, 0 ≤ q j i) :
    (s.sum fun j => (blocks j).sum fun i => q j i * (x j i - a j)^2) ≤
      (s.sum fun j => (blocks j).sum fun i => q j i * (x j i - b)^2) := by
  rw [nested_shift s blocks q x a b h]
  have hn : 0 ≤ (s.sum fun j => ((blocks j).sum (q j)) * (a j - b)^2) := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (Finset.sum_nonneg (hq j hj)) (sq_nonneg _)
  linarith

/-- The nonnegative energy and causal norm inequality for a single real covector. -/
theorem energy_flux_causal (t x y z : ℝ) :
    0 ≤ t^2 + x^2 + y^2 + z^2 ∧
    (2*t*x)^2 + (2*t*y)^2 + (2*t*z)^2 ≤ (t^2 + x^2 + y^2 + z^2)^2 := by
  constructor
  · positivity
  · apply sub_nonneg.mp
    rw [energy_flux_gap]
    exact sq_nonneg _

/-- No function of identical resolved inputs can return two distinct stress components. -/
theorem no_mean_only_closure {α : Type*} (f : α → ℝ) (u : α)
    (r k : ℝ) (hr : 0 < r) (hk : k ≠ 0) :
    ¬ (f u = 2*r*k^2 ∧ f u = 0) := by
  intro h
  exact closure_witness r k hr hk (h.1.symm.trans h.2)

end MicroMacro

#print axioms MicroMacro.centered_shift
#print axioms MicroMacro.residual_nonnegative
#print axioms MicroMacro.weighted_covariance
#print axioms MicroMacro.two_block_variance
#print axioms MicroMacro.two_block_hierarchy
#print axioms MicroMacro.two_block_increment_nonnegative
#print axioms MicroMacro.nested_shift
#print axioms MicroMacro.energy_flux_gap
#print axioms MicroMacro.complex_gram_identity
#print axioms MicroMacro.closure_witness
#print axioms MicroMacro.weighted_cross_covariance
#print axioms MicroMacro.nested_monotonicity
#print axioms MicroMacro.energy_flux_causal
#print axioms MicroMacro.no_mean_only_closure
