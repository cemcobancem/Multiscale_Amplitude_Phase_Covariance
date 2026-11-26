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


/-- Finite amplitude/phase kinetic tensor, evaluated on two covectors. -/
theorem amplitude_phase_tensor {ι : Type*} (s : Finset ι)
    (q ax ay bx byy : ι → ℝ) (A₁ A₂ B₁ B₂ : ℝ)
    (ha₁ : (s.sum fun i => q i*ax i) = (s.sum q)*A₁)
    (ha₂ : (s.sum fun i => q i*ay i) = (s.sum q)*A₂)
    (hb₁ : (s.sum fun i => q i*bx i) = (s.sum q)*B₁)
    (hb₂ : (s.sum fun i => q i*byy i) = (s.sum q)*B₂) :
    (s.sum fun i => q i*(ax i*ay i + bx i*byy i)) =
      (s.sum q)*(A₁*A₂+B₁*B₂) +
      (s.sum fun i => q i*((ax i-A₁)*(ay i-A₂)+(bx i-B₁)*(byy i-B₂))) := by
  have h₁ := weighted_cross_covariance s q ax ay A₁ A₂ ha₁ ha₂
  have h₂ := weighted_cross_covariance s q bx byy B₁ B₂ hb₁ hb₂
  simp only [mul_add, Finset.sum_add_distrib]
  have h₃ : (s.sum fun i => q i * (ax i * ay i)) =
      (s.sum fun i => q i * ax i * ay i) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have h₄ : (s.sum fun i => q i * (bx i * byy i)) =
      (s.sum fun i => q i * bx i * byy i) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [h₃, h₄, h₁, h₂]
  ring

/-- The residual is PSD after contraction with any direction. -/
theorem amplitude_phase_residual_psd {ι : Type*} (s : Finset ι)
    (q a b : ι → ℝ) (A B : ℝ) (hq : ∀ i ∈ s, 0 ≤ q i) :
    0 ≤ (s.sum fun i => q i*((a i-A)^2+(b i-B)^2)) := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hq i hi) (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Linear trace reversal preserves the exact split, for an arbitrary
finite inverse-metric array. This is the pointwise tensor algebra,
not an assertion about the Einstein tensor or derivatives. -/
theorem stress_reconstruction {d : Type*} (s : Finset d)
    (g gi K M C : d → d → ℝ) (massDensity : ℝ)
    (h : ∀ i j, K i j = M i j + C i j) (μ ν : d) :
    2*K μ ν - g μ ν*((s.sum fun i => s.sum fun j => gi i j*K i j)+massDensity) =
      (2*M μ ν - g μ ν*((s.sum fun i => s.sum fun j => gi i j*M i j)+massDensity)) +
      (2*C μ ν - g μ ν*(s.sum fun i => s.sum fun j => gi i j*C i j)) := by
  simp only [h, mul_add, Finset.sum_add_distrib]
  ring

/-- Null contraction of residual stress is twice the covariance contraction. -/
theorem residual_null_energy (c g traceC : ℝ) (hc : 0 ≤ c) (hg : g = 0) :
    0 ≤ 2*c - g*traceC := by
  rw [hg]
  linarith

/-- Pointwise complex horizontal derivative Gram identity, including
the normalized amplitude factor. Real variables represent the real
and imaginary components of a derivative after subtracting the mean. -/
theorem projective_horizontal_gram (nr ni ax ay bx byy r : ℝ)
    (hn : nr^2+ni^2 = r) :
    (nr*ax-ni*bx)*(nr*ay-ni*byy) +
      (ni*ax+nr*bx)*(ni*ay+nr*byy) =
      r*(ax*ay+bx*byy) := by
  linear_combination (ax*ay+bx*byy)*hn

/-- Imaginary Gram component of the same horizontal derivatives. -/
theorem projective_horizontal_imaginary (nr ni ax ay bx byy r : ℝ)
    (hn : nr^2+ni^2 = r) :
    (nr*ax-ni*bx)*(ni*ay+nr*byy) -
      (ni*ax+nr*bx)*(nr*ay-ni*byy) =
      r*(ax*byy-bx*ay) := by
  linear_combination (ax*byy-bx*ay)*hn

/-- Summed horizontal Gram real part equals the normalized
amplitude/phase covariance, for a positive-mass block. -/
theorem projective_block_gram {ι : Type*} (s : Finset ι)
    (q nr ni ax ay bx byy : ι → ℝ) (Q : ℝ)
    (hn : ∀ i ∈ s, Q*(nr i^2+ni i^2) = q i) :
    Q*(s.sum fun i => (nr i*ax i-ni i*bx i)*(nr i*ay i-ni i*byy i) +
        (ni i*ax i+nr i*bx i)*(ni i*ay i+nr i*byy i)) =
      (s.sum fun i => q i*(ax i*ay i+bx i*byy i)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  linear_combination (ax i*ay i+bx i*byy i)*hn i hi

/-- Fisher splitting algebra after normalization:
the log-amplitude score is twice the centered amplitude gradient. -/
theorem fisher_quarter_split {ι : Type*} (s : Finset ι)
    (r a b score : ι → ℝ) (A B : ℝ)
    (h : ∀ i ∈ s, score i = 2*(a i-A)) :
    (s.sum fun i => r i*((a i-A)^2+(b i-B)^2)) =
      (s.sum fun i => r i*score i^2)/4 +
      (s.sum fun i => r i*(b i-B)^2) := by
  have he : (s.sum fun i => r i*(a i-A)^2) =
      (s.sum fun i => r i*score i^2)/4 := by
    have hh : (s.sum fun i => r i*score i^2) =
        (s.sum fun i => (r i*(a i-A)^2)*4) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [h i hi]
      ring
    rw [hh, Finset.sum_mul]
    ring
  simp only [mul_add, Finset.sum_add_distrib]
  rw [he]

/-- If the complex Gram determinant is nonnegative, curvature defined
as twice its imaginary component satisfies the paper's weighted bound.
The underlying Cauchy–Schwarz theorem and differential curvature
identification remain separate obligations. -/
theorem curvature_covariance_bound (Q R S X Y F : ℝ)
    (hgram : X^2+Y^2 ≤ R*S) (hF : F = 2*Y) :
    Q^2*F^2/4 ≤ (Q*R)*(Q*S)-(Q*X)^2 := by
  rw [hF]
  have hh : 0 ≤ Q^2*(R*S-(X^2+Y^2)) :=
    mul_nonneg (sq_nonneg Q) (sub_nonneg.mpr hgram)
  nlinarith only [hh]

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
#print axioms MicroMacro.amplitude_phase_tensor
#print axioms MicroMacro.amplitude_phase_residual_psd
#print axioms MicroMacro.stress_reconstruction
#print axioms MicroMacro.residual_null_energy
#print axioms MicroMacro.projective_horizontal_gram
#print axioms MicroMacro.projective_horizontal_imaginary
#print axioms MicroMacro.projective_block_gram
#print axioms MicroMacro.fisher_quarter_split
#print axioms MicroMacro.curvature_covariance_bound
