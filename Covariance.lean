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
    rw [hh, ← Finset.sum_mul]
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


/-- Finite complex Cauchy–Schwarz in real coordinates. No Gram bound
is assumed. The zero-norm case is handled separately. -/
theorem finite_complex_gram_bound {ι : Type*} (s : Finset ι)
    (a b c d : ι → ℝ) :
    (s.sum fun i => a i*c i+b i*d i)^2 +
      (s.sum fun i => a i*d i-b i*c i)^2 ≤
      (s.sum fun i => a i^2+b i^2)*(s.sum fun i => c i^2+d i^2) := by
  let R : ℝ := s.sum fun i => a i^2+b i^2
  let S : ℝ := s.sum fun i => c i^2+d i^2
  let X : ℝ := s.sum fun i => a i*c i+b i*d i
  let Y : ℝ := s.sum fun i => a i*d i-b i*c i
  change X^2+Y^2 ≤ R*S
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  by_cases hzero : R = 0
  · have hz : ∀ i ∈ s, a i = 0 ∧ b i = 0 := by
      intro i hi
      have hle : a i^2+b i^2 ≤ R :=
        Finset.single_le_sum (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) hi
      rw [hzero] at hle
      have ha : a i^2 = 0 := le_antisymm (by linarith [sq_nonneg (b i)]) (sq_nonneg _)
      have hb : b i^2 = 0 := le_antisymm (by linarith [sq_nonneg (a i)]) (sq_nonneg _)
      exact ⟨mul_self_eq_zero.mp (by simpa [pow_two] using ha),
        mul_self_eq_zero.mp (by simpa [pow_two] using hb)⟩
    have hx : X = 0 := by
      dsimp [X]
      calc
        (s.sum fun i => a i*c i+b i*d i) = (s.sum fun _ => (0 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [(hz i hi).1, (hz i hi).2]
        _ = 0 := by simp
    have hy : Y = 0 := by
      dsimp [Y]
      calc
        (s.sum fun i => a i*d i-b i*c i) = (s.sum fun _ => (0 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [(hz i hi).1, (hz i hi).2]
        _ = 0 := by simp
    rw [hx, hy, hzero]
    norm_num
  · have hp : 0 < R := lt_of_le_of_ne hR (Ne.symm hzero)
    have hn : 0 ≤ (s.sum fun i =>
        (R*c i-X*a i+Y*b i)^2+(R*d i-X*b i-Y*a i)^2) :=
      Finset.sum_nonneg (fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    have he : (s.sum fun i =>
        (R*c i-X*a i+Y*b i)^2+(R*d i-X*b i-Y*a i)^2) =
        R*(R*S-(X^2+Y^2)) := by
      calc
        _ = (s.sum fun i => R^2*(c i^2+d i^2) -
          (2*R*X)*(a i*c i+b i*d i) -
          (2*R*Y)*(a i*d i-b i*c i) +
          (X^2+Y^2)*(a i^2+b i^2)) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = R^2*S-(2*R*X)*X-(2*R*Y)*Y+(X^2+Y^2)*R := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
          simp only [R, S, X, Y, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = _ := by ring
    rw [he] at hn
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hn hp)

/-- The curvature bound now follows from explicit finite complex
vectors rather than an assumed Gram inequality. F=2 Im h still
represents the differential curvature identification. -/
theorem finite_curvature_bound {ι : Type*} (s : Finset ι)
    (a b c d : ι → ℝ) (Q F : ℝ)
    (hF : F = 2*(s.sum fun i => a i*d i-b i*c i)) :
    Q^2*F^2/4 ≤
      (Q*(s.sum fun i => a i^2+b i^2))*(Q*(s.sum fun i => c i^2+d i^2)) -
        (Q*(s.sum fun i => a i*c i+b i*d i))^2 := by
  exact curvature_covariance_bound Q _ _ _ _ F (finite_complex_gram_bound s a b c d) hF

/-- Actual one-variable derivative of normalized weight q/Q.
The derivative hypotheses are the definitions of log-amplitude
gradients; Q must be nonzero at the point. -/
theorem normalized_weight_derivative (q Q : ℝ → ℝ) (t a A : ℝ)
    (hq : HasDerivAt q (2*q t*a) t)
    (hQ : HasDerivAt Q (2*Q t*A) t)
    (hne : Q t ≠ 0) :
    HasDerivAt (fun x => q x / Q x) (2*(q t/Q t)*(a-A)) t := by
  have he : (2*q t*a*Q t-q t*(2*Q t*A))/(Q t)^2 =
      2*(q t/Q t)*(a-A) := by
    field_simp
  rw [← he]
  exact hq.div hQ hne

/-- Algebraic divergence identity for a real scalar in flat coordinates
with constant diagonal inverse metric eta. The arrays p and H stand
for first and second derivatives at a point; H is symmetric.
This proves the jet-level identity, not the full manifold theorem. -/
theorem flat_scalar_divergence_jet {d : Type*} (s : Finset d)
    (eta p : d → ℝ) (H : d → d → ℝ) (m2 u : ℝ) (ν : d)
    (hsym : ∀ i j, H i j = H j i) :
    (s.sum fun i => eta i*(2*(H i i*p ν+p i*H i ν)-2*p i*H ν i)) -
        2*m2*u*p ν =
      2*((s.sum fun i => eta i*H i i)-m2*u)*p ν := by
  have he : (s.sum fun i => eta i*(2*(H i i*p ν+p i*H i ν)-2*p i*H ν i)) =
      (s.sum fun i => (2*p ν)*(eta i*H i i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsym i ν]
    ring
  rw [he, ← Finset.mul_sum]
  ring

/-- On-shell specialization of the flat-coordinate scalar divergence. -/
theorem flat_scalar_on_shell_jet {d : Type*} (s : Finset d)
    (eta p : d → ℝ) (H : d → d → ℝ) (m2 u : ℝ) (ν : d)
    (hsym : ∀ i j, H i j = H j i)
    (hkg : (s.sum fun i => eta i*H i i) = m2*u) :
    (s.sum fun i => eta i*(2*(H i i*p ν+p i*H i ν)-2*p i*H ν i)) -
        2*m2*u*p ν = 0 := by
  rw [flat_scalar_divergence_jet s eta p H m2 u ν hsym, hkg]
  ring

/-- Centered cross moment: the shift by a constant disappears. -/
theorem centered_cross_shift {ι : Type*} (s : Finset ι)
    (r x y : ι → ℝ) (B : ℝ)
    (h : (s.sum fun i => r i*x i) = 0) :
    (s.sum fun i => r i*x i*y i) =
      (s.sum fun i => r i*x i*(y i-B)) := by
  have he : (s.sum fun i => r i*x i*(y i-B)) =
      (s.sum fun i => r i*x i*y i - (r i*x i)*B) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he, Finset.sum_sub_distrib, ← Finset.sum_mul, h]
  ring

/-- Phase-curvature identity at the level of first/second derivative
data: x,y are centered amplitude gradients, bx,by phase gradients,
and Hxy,Hyx mixed phase derivatives. The product-rule expansion
is explicit; commuting mixed derivatives and centering are assumed. -/
theorem phase_curvature_jet {ι : Type*} (s : Finset ι)
    (r x y bx byy Hxy Hyx : ι → ℝ) (Bx By : ℝ)
    (hx : (s.sum fun i => r i*x i) = 0)
    (hy : (s.sum fun i => r i*y i) = 0)
    (hmix : ∀ i ∈ s, Hxy i = Hyx i) :
    (s.sum fun i => 2*r i*x i*byy i+r i*Hxy i -
      (2*r i*y i*bx i+r i*Hyx i)) =
      2*(s.sum fun i => r i*(x i*(byy i-By)-y i*(bx i-Bx))) := by
  calc
    _ = (s.sum fun i => 2*(r i*x i*byy i-r i*y i*bx i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hmix i hi]
      ring
    _ = 2*((s.sum fun i => r i*x i*byy i) -
        (s.sum fun i => r i*y i*bx i)) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    _ = 2*((s.sum fun i => r i*x i*(byy i-By)) -
        (s.sum fun i => r i*y i*(bx i-Bx))) := by
      rw [centered_cross_shift s r x byy By hx, centered_cross_shift s r y bx Bx hy]
    _ = _ := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring


/-- Real Cauchy–Schwarz, derived from the finite complex Gram theorem. -/
theorem finite_real_gram_bound {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) :
    (s.sum fun i => a i*b i)^2 ≤
      (s.sum fun i => a i^2)*(s.sum fun i => b i^2) := by
  simpa using finite_complex_gram_bound s a (fun _ => 0) b (fun _ => 0)

/-- The energy and flux of an arbitrary finite collection of covectors
obey the causal inequality in an orthonormal Lorentz frame.
Nonnegative weights can be absorbed by scaling each covector by
the square root of its weight. -/
theorem ensemble_energy_flux_causal {ι : Type*} (s : Finset ι)
    (t x y z : ι → ℝ) :
    0 ≤ (s.sum fun i => t i^2)+(s.sum fun i => x i^2)+
      (s.sum fun i => y i^2)+(s.sum fun i => z i^2) ∧
    4*((s.sum fun i => t i*x i)^2+(s.sum fun i => t i*y i)^2+
      (s.sum fun i => t i*z i)^2) ≤
      ((s.sum fun i => t i^2)+(s.sum fun i => x i^2)+
       (s.sum fun i => y i^2)+(s.sum fun i => z i^2))^2 := by
  have ht : 0 ≤ (s.sum fun i => t i^2) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hx : 0 ≤ (s.sum fun i => x i^2) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hy : 0 ≤ (s.sum fun i => y i^2) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hz : 0 ≤ (s.sum fun i => z i^2) :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  constructor
  · linarith
  · have h1 := finite_real_gram_bound s t x
    have h2 := finite_real_gram_bound s t y
    have h3 := finite_real_gram_bound s t z
    have h4 := sq_nonneg ((s.sum fun i => t i^2) -
      (s.sum fun i => x i^2) - (s.sum fun i => y i^2) -
      (s.sum fun i => z i^2))
    nlinarith only [h1, h2, h3, h4]

/-- Derivative of a normalized weight using a total defined by the
sum of the microscopic weights, not an independently assumed derivative. -/
theorem ensemble_normalized_weight_derivative {ι : Type*} (s : Finset ι)
    (q : ι → ℝ → ℝ) (a : ι → ℝ) (t : ℝ) (i : ι)
    (hi : i ∈ s)
    (hq : ∀ j ∈ s, HasDerivAt (q j) (2*q j t*a j) t)
    (hne : (s.sum fun j => q j t) ≠ 0) :
    HasDerivAt (fun u => q i u / (s.sum fun j => q j u))
      (2*(q i t/(s.sum fun j => q j t))*
        (a i-(s.sum fun j => q j t*a j)/(s.sum fun j => q j t))) t := by
  let Q : ℝ → ℝ := fun u => s.sum fun j => q j u
  let A : ℝ := (s.sum fun j => q j t*a j)/Q t
  change HasDerivAt (fun u => q i u/Q u) (2*(q i t/Q t)*(a i-A)) t
  have hQne : Q t ≠ 0 := hne
  have he : (s.sum fun j => 2*q j t*a j) = 2*Q t*A := by
    calc
      _ = (s.sum fun j => 2*(q j t*a j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 2*(s.sum fun j => q j t*a j) := by rw [Finset.mul_sum]
      _ = _ := by
        dsimp [A]
        field_simp
  have hQ : HasDerivAt Q (2*Q t*A) t := by
    rw [← he]
    exact HasDerivAt.fun_sum hq
  exact normalized_weight_derivative (q i) Q t (a i) A (hq i hi) hQ hQne

/-- An actual directional derivative version of phase_curvature_jet.
The four families are restrictions of weights and phase gradients
to two coordinate lines through the evaluation point. Equality
of their common values and of the mixed phase partials is explicit.
This is not yet a full differential-forms/manifold statement. -/
theorem phase_curvature_line_derivative {ι : Type*} (s : Finset ι)
    (rX rY bY bX : ι → ℝ → ℝ)
    (r x y bx byy Hxy Hyx : ι → ℝ) (Bx By t : ℝ)
    (hrXv : ∀ i ∈ s, rX i t = r i)
    (hrYv : ∀ i ∈ s, rY i t = r i)
    (hbXv : ∀ i ∈ s, bX i t = bx i)
    (hbYv : ∀ i ∈ s, bY i t = byy i)
    (hrX : ∀ i ∈ s, HasDerivAt (rX i) (2*r i*x i) t)
    (hrY : ∀ i ∈ s, HasDerivAt (rY i) (2*r i*y i) t)
    (hbX : ∀ i ∈ s, HasDerivAt (bX i) (Hyx i) t)
    (hbY : ∀ i ∈ s, HasDerivAt (bY i) (Hxy i) t)
    (hx : (s.sum fun i => r i*x i) = 0)
    (hy : (s.sum fun i => r i*y i) = 0)
    (hmix : ∀ i ∈ s, Hxy i = Hyx i) :
    HasDerivAt (fun u => (s.sum fun i => rX i u*bY i u) -
      (s.sum fun i => rY i u*bX i u))
      (2*(s.sum fun i => r i*(x i*(byy i-By)-y i*(bx i-Bx)))) t := by
  have h1 : HasDerivAt (fun u => s.sum fun i => rX i u*bY i u)
      (s.sum fun i => 2*r i*x i*byy i+r i*Hxy i) t := by
    apply HasDerivAt.fun_sum
    intro i hi
    simpa only [hrXv i hi, hbYv i hi] using (hrX i hi).mul (hbY i hi)
  have h2 : HasDerivAt (fun u => s.sum fun i => rY i u*bX i u)
      (s.sum fun i => 2*r i*y i*bx i+r i*Hyx i) t := by
    apply HasDerivAt.fun_sum
    intro i hi
    simpa only [hrYv i hi, hbXv i hi] using (hrY i hi).mul (hbX i hi)
  have he := phase_curvature_jet s r x y bx byy Hxy Hyx Bx By hx hy hmix
  rw [Finset.sum_sub_distrib] at he
  rw [← he]
  exact h1.sub h2


/-- The score of a nonzero normalized weight, using an actual logarithmic derivative. -/
theorem normalized_log_score (q Q : ℝ → ℝ) (t a A : ℝ)
    (hq : HasDerivAt q (2*q t*a) t)
    (hQ : HasDerivAt Q (2*Q t*A) t)
    (hqne : q t ≠ 0) (hQne : Q t ≠ 0) :
    HasDerivAt (fun u => Real.log (q u / Q u)) (2*(a-A)) t := by
  have hr := normalized_weight_derivative q Q t a A hq hQ hQne
  have hn : q t / Q t ≠ 0 := div_ne_zero hqne hQne
  have he : (2*(q t/Q t)*(a-A))/(q t/Q t) = 2*(a-A) := by
    field_simp
  rw [← he]
  exact hr.log hn

/-- Coordinate-level covariant stress divergence. The arrays are a covector
p and its symmetric covariant derivative H. The inverse-metric array gi
is arbitrary, not restricted to diagonal coordinates. The displayed
left side is the metric-compatible product-rule expansion, not a formal
definition of a manifold connection. -/
theorem covariant_scalar_divergence_jet {d : Type*} (s : Finset d)
    (gi : d → d → ℝ) (p : d → ℝ) (H : d → d → ℝ)
    (m2 u : ℝ) (ν : d) (hsym : ∀ i j, H i j = H j i) :
    (s.sum fun i => s.sum fun j => gi i j *
      (2*(H i j*p ν+p j*H i ν)-2*p j*H ν i)) - 2*m2*u*p ν =
      2*((s.sum fun i => s.sum fun j => gi i j*H i j)-m2*u)*p ν := by
  have he : (s.sum fun i => s.sum fun j => gi i j *
      (2*(H i j*p ν+p j*H i ν)-2*p j*H ν i)) =
      (s.sum fun i => s.sum fun j => (2*p ν)*(gi i j*H i j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym i ν]
    ring
  rw [he]
  simp only [← Finset.mul_sum]
  ring

/-- A finite weighted collection of on-shell scalar components has zero
expanded divergence. A complex scalar is represented by two real
components; constant ensemble weights are required for the physical
interpretation. Metric compatibility and symmetric Hessian are encoded
at the coordinate jet level. -/
theorem covariant_ensemble_on_shell_jet {ι d : Type*}
    (s : Finset ι) (D : Finset d)
    (w : ι → ℝ) (gi : d → d → ℝ) (p : ι → d → ℝ)
    (H : ι → d → d → ℝ) (u : ι → ℝ) (m2 : ℝ) (ν : d)
    (hsym : ∀ n ∈ s, ∀ i j, H n i j = H n j i)
    (hkg : ∀ n ∈ s, (D.sum fun i => D.sum fun j => gi i j*H n i j) = m2*u n) :
    (s.sum fun n => w n*((D.sum fun i => D.sum fun j => gi i j *
      (2*(H n i j*p n ν+p n j*H n i ν)-2*p n j*H n ν i)) -
        2*m2*u n*p n ν)) = 0 := by
  calc
    _ = (s.sum fun _ => (0 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [covariant_scalar_divergence_jet D gi (p n) (H n) m2 (u n) ν (hsym n hn),
        hkg n hn]
      ring
    _ = 0 := by simp

/-- Real and imaginary parts of an affine-phase plane wave:
first and second derivatives along a coordinate line. -/
theorem affine_plane_wave_derivatives (k α t : ℝ) :
    HasDerivAt (fun x => Real.cos (k*x+α)) (-Real.sin (k*t+α)*k) t ∧
    HasDerivAt (fun x => Real.sin (k*x+α)) (Real.cos (k*t+α)*k) t ∧
    HasDerivAt (fun x => -Real.sin (k*x+α)*k) (-Real.cos (k*t+α)*k^2) t ∧
    HasDerivAt (fun x => Real.cos (k*x+α)*k) (-Real.sin (k*t+α)*k^2) t := by
  have h : HasDerivAt (fun x : ℝ => k*x+α) k t := by
    simpa using ((hasDerivAt_id t).const_mul k).add_const α
  refine ⟨h.cos, h.sin, ?_, ?_⟩
  · convert (h.sin.neg).mul_const k using 1
    ring
  · convert h.cos.mul_const k using 1
    ring

/-- A plane wave restricted to a time line and a spatial line through the
same phase satisfies the actual second-derivative KG relation for both
real components. This is an explicit flat-spacetime construction in
1+1 dimensions; adding spectator coordinates leaves it unchanged. -/
theorem plane_wave_mass_shell (ω k m2 θ : ℝ)
    (hdisp : ω^2 = k^2+m2) :
    -(deriv (deriv (fun t => Real.cos (-ω*t+θ))) 0) +
      deriv (deriv (fun x => Real.cos (k*x+θ))) 0 - m2*Real.cos θ = 0 ∧
    -(deriv (deriv (fun t => Real.sin (-ω*t+θ))) 0) +
      deriv (deriv (fun x => Real.sin (k*x+θ))) 0 - m2*Real.sin θ = 0 := by
  have hc (a : ℝ) : deriv (fun t => Real.cos (a*t+θ)) =
      fun t => -Real.sin (a*t+θ)*a := by
    funext t
    exact (affine_plane_wave_derivatives a θ t).1.deriv
  have hs (a : ℝ) : deriv (fun t => Real.sin (a*t+θ)) =
      fun t => Real.cos (a*t+θ)*a := by
    funext t
    exact (affine_plane_wave_derivatives a θ t).2.1.deriv
  have hc2 (a : ℝ) :
      deriv (deriv (fun t => Real.cos (a*t+θ))) 0 = -Real.cos θ*a^2 := by
    rw [hc a]
    simpa using (affine_plane_wave_derivatives a θ 0).2.2.1.deriv
  have hs2 (a : ℝ) :
      deriv (deriv (fun t => Real.sin (a*t+θ))) 0 = -Real.sin θ*a^2 := by
    rw [hs a]
    simpa using (affine_plane_wave_derivatives a θ 0).2.2.2.deriv
  constructor
  · rw [hc2 (-ω), hc2 k]
    linear_combination Real.cos θ*hdisp
  · rw [hs2 (-ω), hs2 k]
    linear_combination Real.sin θ*hdisp

/-- The kinetic Gram tensor of the two real components of a plane wave.
Together with affine_plane_wave_derivatives, this computes rather
than assumes the local kinetic tensor of the explicit field. -/
theorem plane_wave_kinetic_component (r k l θ : ℝ) :
    r*((-Real.sin θ*k)*(-Real.sin θ*l) +
       (Real.cos θ*k)*(Real.cos θ*l)) = r*k*l := by
  linear_combination r*k*l*(Real.sin_sq_add_cos_sq θ)

/-- Two equal-weight opposite momenta have zero mean, but their
on-shell spatial stress differs from that of waves along an orthogonal
axis. r is the total positive density. The trace term vanishes by the
mass-shell equation. -/
theorem counterpropagating_stress_witness (r ω k m2 : ℝ)
    (hr : 0 < r) (hk : k ≠ 0) (hdisp : ω^2 = k^2+m2) :
    (r/2*k + r/2*(-k) = 0) ∧
    (2*(r/2*k^2+r/2*(-k)^2) - (-r*ω^2+r*k^2+m2*r) = 2*r*k^2) ∧
    (2*(r/2*(0:ℝ)^2+r/2*0^2) - (-r*ω^2+r*k^2+m2*r) = 0) ∧
    (2*r*k^2 ≠ 0) := by
  refine ⟨by ring, ?_, ?_, closure_witness r k hr hk⟩
  · linear_combination r*hdisp
  · linear_combination r*hdisp

/-- Finite spectral heat-trace identity obtained by integrating the
exponential kernel from each eigenvalue to a finite cutoff. This is a
preliminary analytic step, valid for any finite spectrum, not RH. -/
theorem finite_heat_trace_tail {ι : Type*} (s : Finset ι)
    (eigenvalue : ι → ℝ) (τ B : ℝ) :
    (s.sum fun i => Real.exp (-τ*eigenvalue i)) =
      (s.sum fun i => ∫ x in eigenvalue i..B, τ*Real.exp (-τ*x)) +
        (s.card : ℝ)*Real.exp (-τ*B) := by
  have hd (x : ℝ) : HasDerivAt (fun u => -Real.exp (-τ*u))
      (τ*Real.exp (-τ*x)) x := by
    have h : HasDerivAt (fun u : ℝ => -τ*u) (-τ) x := by
      simpa using (hasDerivAt_id x).const_mul (-τ)
    convert h.exp.neg using 1
    ring
  have hcont : Continuous (fun x => τ*Real.exp (-τ*x)) := by fun_prop
  have hi (i : ι) : (∫ x in eigenvalue i..B, τ*Real.exp (-τ*x)) =
      -Real.exp (-τ*B) - (-Real.exp (-τ*eigenvalue i)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (hcont.intervalIntegrable _ _)
  calc
    _ = (s.sum fun i => (∫ x in eigenvalue i..B, τ*Real.exp (-τ*x)) +
        Real.exp (-τ*B)) := by
      apply Finset.sum_congr rfl
      intro i hmem
      rw [hi i]
      ring
    _ = _ := by simp [Finset.sum_add_distrib, nsmul_eq_mul]

/-- Absolute error bound for a truncated Laplace transform of a
remainder R, dominated pointwise by M. This uses genuine integration,
and is independent of the choice of arithmetic counting function.
The infinite-interval limit and RH prime-counting bound remain open. -/
theorem laplace_remainder_interval (τ a b : ℝ) (R M : ℝ → ℝ)
    (hab : a ≤ b) (hτ : 0 ≤ τ)
    (hbound : ∀ x ∈ Set.Icc a b, |R x| ≤ M x)
    (hint : IntervalIntegrable (fun x => τ*Real.exp (-τ*x)*M x)
      MeasureTheory.volume a b) :
    |∫ x in a..b, τ*Real.exp (-τ*x)*R x| ≤
      ∫ x in a..b, τ*Real.exp (-τ*x)*M x := by
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le hab
  · filter_upwards [] with x hx
    have hn : 0 ≤ τ*Real.exp (-τ*x) := mul_nonneg hτ (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left (hbound x ⟨hx.1.le, hx.2⟩) hn
  · exact hint


/-- Logarithmic majorant used after the Laplace rescaling y = τ x. -/
theorem spectral_log_majorant (τ y : ℝ) (hτ : 0 < τ) (hy : 0 < y) :
    Real.log (y/τ) ≤ -Real.log τ+y := by
  rw [Real.log_div hy.ne' hτ.ne']
  linarith [Real.log_le_self hy.le]

/-- Infinite Laplace remainder estimate at the RH exponent. R is an
extended counting remainder (zero below the counting threshold).
The only analytic input on R is the explicit pointwise bound on its
positive half-line, with log x replaced by max 0 (log x) to allow
zero extension. Gamma integrability is proved, not assumed. -/
theorem infinite_scaled_remainder_bound (R : ℝ → ℝ) (C τ : ℝ)
    (hC : 0 ≤ C) (hτ : 0 < τ) (hsmall : -Real.log τ ≥ 1)
    (hR : ∀ x : ℝ, 0 < x → |R x| ≤
      C*x^(1/2:ℝ)*max 0 (Real.log x)) :
    |∫ y in Set.Ioi (0:ℝ), Real.exp (-y)*R (y/τ)| ≤
      C*τ^(-1/2:ℝ)*(Real.Gamma (3/2)+Real.Gamma (5/2))*(-Real.log τ) := by
  let L := -Real.log τ
  let D := C*τ^(-1/2:ℝ)
  let f : ℝ → ℝ := fun y => Real.exp (-y)*y^(1/2:ℝ)
  let g : ℝ → ℝ := fun y => Real.exp (-y)*y^(3/2:ℝ)
  have hL : 1 ≤ L := hsmall
  have hD : 0 ≤ D := mul_nonneg hC (Real.rpow_nonneg hτ.le _)
  have hf : MeasureTheory.IntegrableOn f (Set.Ioi (0:ℝ)) := by
    simpa [f, show (3/2:ℝ)-1 = 1/2 by norm_num] using
      (Real.GammaIntegral_convergent (s := (3/2:ℝ)) (by norm_num))
  have hg : MeasureTheory.IntegrableOn g (Set.Ioi (0:ℝ)) := by
    simpa [g, show (5/2:ℝ)-1 = 3/2 by norm_num] using
      (Real.GammaIntegral_convergent (s := (5/2:ℝ)) (by norm_num))
  have hfi : (∫ y in Set.Ioi (0:ℝ), f y) = Real.Gamma (3/2) := by
    simpa [f, show (3/2:ℝ)-1 = 1/2 by norm_num] using
      (Real.Gamma_eq_integral (s := (3/2:ℝ)) (by norm_num)).symm
  have hgi : (∫ y in Set.Ioi (0:ℝ), g y) = Real.Gamma (5/2) := by
    simpa [g, show (5/2:ℝ)-1 = 3/2 by norm_num] using
      (Real.Gamma_eq_integral (s := (5/2:ℝ)) (by norm_num)).symm
  have hM : MeasureTheory.IntegrableOn (fun y => (D*L)*f y+D*g y)
      (Set.Ioi (0:ℝ)) := (hf.const_mul _).add (hg.const_mul _)
  have hb : ∀ y ∈ Set.Ioi (0:ℝ),
      ‖Real.exp (-y)*R (y/τ)‖ ≤ (D*L)*f y+D*g y := by
    intro y hy
    have hy' : 0 < y := hy
    have hlog : max 0 (Real.log (y/τ)) ≤ L+y :=
      max_le (by linarith) (spectral_log_majorant τ y hτ hy')
    have hpow : (y/τ)^(1/2:ℝ) = y^(1/2:ℝ)*τ^(-1/2:ℝ) := by
      rw [div_eq_mul_inv, Real.mul_rpow hy'.le (inv_nonneg.mpr hτ.le),
        ← Real.rpow_neg_eq_inv_rpow]
      norm_num
    have hstep : y^(1/2:ℝ)*y = y^(3/2:ℝ) := by
      calc
        _ = y^(1/2:ℝ)*y^(1:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hy']; norm_num
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    calc
      _ ≤ Real.exp (-y)*(C*(y/τ)^(1/2:ℝ)*max 0 (Real.log (y/τ))) :=
        mul_le_mul_of_nonneg_left (hR (y/τ) (div_pos hy' hτ)) (Real.exp_pos _).le
      _ ≤ Real.exp (-y)*(C*(y/τ)^(1/2:ℝ)*(L+y)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog
          (mul_nonneg hC (Real.rpow_nonneg (div_pos hy' hτ).le _))) (Real.exp_pos _).le
      _ = (D*L)*f y+D*g y := by
        rw [hpow]
        dsimp [D, f, g]
        rw [← hstep]
        ring
  have hae : ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
      ‖Real.exp (-y)*R (y/τ)‖ ≤ (D*L)*f y+D*g y :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall hb)
  have hbound := MeasureTheory.norm_integral_le_of_norm_le hM hae
  rw [Real.norm_eq_abs, MeasureTheory.integral_add (hf.const_mul (D*L))
    (hg.const_mul D), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, hfi, hgi] at hbound
  change _ ≤ D*(Real.Gamma (3/2)+Real.Gamma (5/2))*L
  have hG : 0 ≤ Real.Gamma (5/2) := Real.Gamma_nonneg_of_nonneg (by norm_num)
  have hex : 0 ≤ D*Real.Gamma (5/2)*(L-1) :=
    mul_nonneg (mul_nonneg hD hG) (sub_nonneg.mpr hL)
  nlinarith only [hbound, hex]

/-- Exact rescaling of the infinite Laplace integral. No integrability
hypothesis is necessary for this equality of totalized Bochner integrals;
the subsequent application supplies an integrable majorant. -/
theorem infinite_laplace_rescale (R : ℝ → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (∫ x in Set.Ioi (0:ℝ), τ*Real.exp (-τ*x)*R x) =
      ∫ y in Set.Ioi (0:ℝ), Real.exp (-y)*R (y/τ) := by
  let g : ℝ → ℝ := fun y => Real.exp (-y)*R (y/τ)
  have he : (fun x : ℝ => τ*Real.exp (-τ*x)*R x) =
      fun x => τ*g (τ*x) := by
    funext x
    dsimp [g]
    rw [show τ*x/τ = x by field_simp, neg_mul]
    ring
  rw [he, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_comp_mul_left_Ioi g 0 hτ]
  simp [g, smul_eq_mul, hτ.ne']

/-- Explicit infinite-domain RH-rate transfer. Unlike the finite
interval lemma, the error estimate has the target τ^{-1/2} log(1/τ)
rate and a concrete constant. The counting estimate is a hypothesis. -/
theorem infinite_laplace_rh_rate (R : ℝ → ℝ) (C τ : ℝ)
    (hC : 0 ≤ C) (hτ : 0 < τ) (hsmall : -Real.log τ ≥ 1)
    (hR : ∀ x : ℝ, 0 < x → |R x| ≤
      C*x^(1/2:ℝ)*max 0 (Real.log x)) :
    |∫ x in Set.Ioi (0:ℝ), τ*Real.exp (-τ*x)*R x| ≤
      C*τ^(-1/2:ℝ)*(Real.Gamma (3/2)+Real.Gamma (5/2))*(-Real.log τ) := by
  rw [infinite_laplace_rescale R τ hτ]
  exact infinite_scaled_remainder_bound R C τ hC hτ hsmall hR

/-- A single eigenvalue contributes its exponential weight as an
integral over the infinite tail. Both convergence and equality follow
from the improper fundamental theorem of calculus. -/
theorem exponential_tail_integral (a τ : ℝ) (hτ : 0 < τ) :
    MeasureTheory.IntegrableOn (fun x => τ*Real.exp (-τ*x)) (Set.Ioi a) ∧
    (∫ x in Set.Ioi a, τ*Real.exp (-τ*x)) = Real.exp (-τ*a) := by
  have hd (x : ℝ) : HasDerivAt (fun u => -Real.exp (-τ*u))
      (τ*Real.exp (-τ*x)) x := by
    have h : HasDerivAt (fun u : ℝ => -τ*u) (-τ) x := by
      simpa using (hasDerivAt_id x).const_mul (-τ)
    convert h.exp.neg using 1
    ring
  have hl : Filter.Tendsto (fun x : ℝ => -Real.exp (-τ*x)) Filter.atTop (nhds 0) := by
    have hlin : Filter.Tendsto (fun x : ℝ => τ*x) Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_atTop.2
      intro b
      refine ⟨b/τ, ?_⟩
      intro x hx
      simpa [mul_comm] using (div_le_iff₀ hτ).mp hx
    have hex := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin).neg
    simpa [Function.comp_def, neg_mul] using hex
  have hpos : ∀ x ∈ Set.Ioi a, 0 ≤ τ*Real.exp (-τ*x) :=
    fun x _ => mul_nonneg hτ.le (Real.exp_pos (-τ*x)).le
  have hi := MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (fun x _ => hd x) hpos hl
  refine ⟨hi, ?_⟩
  simpa using MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun x _ => hd x) hpos hl

/-- Genuine countable spectral sum, with a counting staircase
represented by its indicator sum. No prime-counting identity is
assumed for this general spectral representation. -/
theorem countable_heat_trace_integral (e : ℕ → ℝ) (τ : ℝ)
    (hτ : 0 < τ) (he : ∀ n : ℕ, (n:ℝ) ≤ e n) :
    (∑' n : ℕ, Real.exp (-τ*e n)) =
      ∫ x : ℝ, (∑' n : ℕ, (Set.Ioi (e n)).indicator
        (fun z => τ*Real.exp (-τ*z)) x) := by
  let F : ℕ → ℝ → ℝ := fun n => (Set.Ioi (e n)).indicator
    (fun x => τ*Real.exp (-τ*x))
  have hF (n : ℕ) : MeasureTheory.Integrable (F n) := by
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).2
      (exponential_tail_integral (e n) τ hτ).1
  have hFi (n : ℕ) : (∫ x, F n x) = Real.exp (-τ*e n) := by
    rw [show F n = (Set.Ioi (e n)).indicator (fun x => τ*Real.exp (-τ*x)) by rfl,
      MeasureTheory.integral_indicator measurableSet_Ioi]
    exact (exponential_tail_integral (e n) τ hτ).2
  have hFn (n : ℕ) : (∫ x, ‖F n x‖) = Real.exp (-τ*e n) := by
    rw [← hFi n]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact Set.indicator_nonneg (fun z _ => mul_nonneg hτ.le (Real.exp_pos _).le) _
  have hs : Summable (fun n => ∫ x, ‖F n x‖) := by
    simp_rw [hFn]
    exact Real.summable_exp_nat_mul_of_ge (neg_neg_of_pos hτ) he
  rw [show (fun n => Real.exp (-τ*e n)) = (fun n => ∫ x, F n x) by
    funext n; exact (hFi n).symm]
  exact MeasureTheory.integral_tsum_of_summable_integral_norm hF hs

/-- Define the prime heat trace using the nth prime enumeration.
The infinite spectral sum is related to an explicit indicator staircase. -/
theorem prime_heat_trace_staircase (τ : ℝ) (hτ : 0 < τ) :
    (∑' n : ℕ, Real.exp (-τ*(Nat.nth Nat.Prime n : ℝ))) =
      ∫ x : ℝ, (∑' n : ℕ, (Set.Ioi (Nat.nth Nat.Prime n : ℝ)).indicator
        (fun z => τ*Real.exp (-τ*z)) x) := by
  apply countable_heat_trace_integral _ τ hτ
  intro n
  exact_mod_cast (show n ≤ Nat.nth Nat.Prime n from
    le_trans (Nat.le_add_right n 2) (Nat.add_two_le_nth_prime n))

/-- Coordinate-free horizontal projection in a complex inner-product
space, with actual Mathlib inner products, not a component array.
Convention: the inner product is linear in its second argument. -/
noncomputable def horizontalProjection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (n v : E) : E :=
  v - inner ℂ n v • n

theorem horizontal_projection_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (n v : E) (hn : inner ℂ n n = 1) :
    inner ℂ n (horizontalProjection n v) = 0 := by
  simp [horizontalProjection, hn]

/-- Horizontal projection removes any change in the vertical (phase)
direction. This is intrinsic Hilbert-space algebra, applicable to
actual tangent derivatives once the derivative map is constructed. -/
theorem horizontal_projection_vertical_invariance {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (n v : E) (c : ℂ) (hn : inner ℂ n n = 1) :
    horizontalProjection n (v+c • n) = horizontalProjection n v := by
  simp only [horizontalProjection, inner_add_right, inner_smul_right, hn, mul_one, add_smul]
  abel

/-- A linear covariant-divergence operator applied to the exact
stress split transfers the on-shell conservation law into an
exchange identity. This theorem does not construct the connection. -/
theorem conservation_exchange_linear {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (D : V →ₗ[ℝ] W) (T M R : V)
    (hT : T = M+R) (hcons : D T = 0) :
    D M = -D R := by
  have he : D M+D R = 0 := by
    simpa [hT] using hcons
  calc
    D M = D M+D R-D R := by abel
    _ = -D R := by rw [he, zero_sub]


/-- Strict real prime-counting staircase (p < x). At integers it differs
from the inclusive staircase by at most one; that distinction is immaterial
to the ordinary Lebesgue integral. -/
noncomputable def strictPrimeCount (x : ℝ) : ℝ :=
  (Nat.primeCounting' (Nat.ceil x) : ℝ)

/-- Logarithmic integral normalized at 2, extended by zero below 2. -/
noncomputable def logCount (x : ℝ) : ℝ :=
  ∫ y in Set.Ioo (2:ℝ) x, (Real.log y)⁻¹

theorem prime_staircase_count (x w : ℝ) :
    (∑' n : ℕ, (Set.Ioi (Nat.nth Nat.Prime n : ℝ)).indicator
      (fun _ => w) x) = w*strictPrimeCount x := by
  classical
  let N := Nat.primeCounting' (Nat.ceil x)
  have hiff (n : ℕ) : (Nat.nth Nat.Prime n : ℝ) < x ↔ n < N := by
    rw [← Nat.lt_ceil]
    exact (Nat.lt_nth_iff_count_lt Nat.infinite_setOf_prime).symm
  have hval (n : ℕ) : (Set.Ioi (Nat.nth Nat.Prime n : ℝ)).indicator
      (fun _ => w) x = if n < N then w else 0 := by
    simp [Set.indicator, hiff n]
  calc
    _ = ∑ n ∈ Finset.range N, (Set.Ioi (Nat.nth Nat.Prime n : ℝ)).indicator
        (fun _ => w) x := by
      apply tsum_eq_sum
      intro n hn
      have hnot : ¬ n < N := fun h => hn (Finset.mem_range.mpr h)
      rw [hval, if_neg hnot]
    _ = ∑ n ∈ Finset.range N, w := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hval, if_pos (Finset.mem_range.mp hn)]
    _ = _ := by simp [strictPrimeCount, N, nsmul_eq_mul, mul_comm]

/-- The prime heat trace equals the Laplace integral of the strict
prime-counting function. The integral is genuinely convergent. -/
theorem prime_heat_trace_counting (τ : ℝ) (hτ : 0 < τ) :
    MeasureTheory.IntegrableOn (fun x => τ*Real.exp (-τ*x)*strictPrimeCount x)
      (Set.Ioi (0:ℝ)) ∧
    (∑' n : ℕ, Real.exp (-τ*(Nat.nth Nat.Prime n : ℝ))) =
      ∫ x in Set.Ioi (0:ℝ), τ*Real.exp (-τ*x)*strictPrimeCount x := by
  let K : ℝ → ℝ := fun x => τ*Real.exp (-τ*x)
  have hcount : (∑' n : ℕ, Real.exp (-τ*(Nat.nth Nat.Prime n : ℝ))) =
      ∫ x : ℝ, K x*strictPrimeCount x := by
    rw [prime_heat_trace_staircase τ hτ]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    exact prime_staircase_count x (K x)
  have hset : (∫ x : ℝ, K x*strictPrimeCount x) =
      ∫ x in Set.Ioi (0:ℝ), K x*strictPrimeCount x := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    by_cases hx : 0 < x
    · simp [Set.indicator, hx]
    · have hzero : strictPrimeCount x = 0 := by
        simp [strictPrimeCount, Nat.ceil_eq_zero.mpr (le_of_not_gt hx), Nat.primeCounting']
      simp [Set.indicator, hx, hzero]
  have heq := hcount.trans hset
  have hs : Summable (fun n : ℕ => Real.exp (-τ*(Nat.nth Nat.Prime n : ℝ))) := by
    apply Real.summable_exp_nat_mul_of_ge (neg_neg_of_pos hτ)
    intro n
    exact_mod_cast (show n ≤ Nat.nth Nat.Prime n from
      le_trans (Nat.le_add_right n 2) (Nat.add_two_le_nth_prime n))
  have hp : 0 < ∑' n : ℕ, Real.exp (-τ*(Nat.nth Nat.Prime n : ℝ)) :=
    hs.tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)
  have hi : MeasureTheory.IntegrableOn (fun x => K x*strictPrimeCount x)
      (Set.Ioi (0:ℝ)) :=
    MeasureTheory.Integrable.of_integral_ne_zero (heq ▸ hp.ne')
  exact ⟨hi, heq⟩

/-- The continuous comparison density 1/log p, p > 2, has the exact
Laplace representation via logCount. Both integrability and the
interchange of integrals are established by Fubini's theorem. -/
theorem smooth_heat_trace_counting (τ : ℝ) (hτ : 0 < τ) :
    MeasureTheory.IntegrableOn (fun x => τ*Real.exp (-τ*x)*logCount x)
      (Set.Ioi (0:ℝ)) ∧
    (∫ p in Set.Ioi (2:ℝ), Real.exp (-τ*p)/Real.log p) =
      ∫ x in Set.Ioi (0:ℝ), τ*Real.exp (-τ*x)*logCount x := by
  let K : ℝ → ℝ := fun x => τ*Real.exp (-τ*x)
  let ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi (2:ℝ))
  let F : ℝ → ℝ → ℝ := fun p x => if p < x then (Real.log p)⁻¹*K x else 0
  have hm : Measurable (Function.uncurry F) := by
    change Measurable (fun z : ℝ × ℝ =>
      if z.1 < z.2 then (Real.log z.1)⁻¹*(τ*Real.exp (-τ*z.2)) else 0)
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      (by fun_prop) measurable_const
  have hform (p : ℝ) : F p = fun x =>
      (Real.log p)⁻¹*(Set.Ioi p).indicator K x := by
    funext x
    by_cases hx : p < x <;> simp [F, Set.indicator, hx]
  have hFi (p : ℝ) : MeasureTheory.Integrable (F p) := by
    rw [hform]
    exact ((MeasureTheory.integrable_indicator_iff measurableSet_Ioi).2
      (exponential_tail_integral p τ hτ).1).const_mul _
  have hFe (p : ℝ) : (∫ x, F p x) = (Real.log p)⁻¹*Real.exp (-τ*p) := by
    rw [hform, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_indicator measurableSet_Ioi]
    rw [show (∫ x in Set.Ioi p, K x) = Real.exp (-τ*p) from
      (exponential_tail_integral p τ hτ).2]
  have hFn (p : ℝ) (hp : p ∈ Set.Ioi (2:ℝ)) :
      (∫ x, ‖F p x‖) = (Real.log p)⁻¹*Real.exp (-τ*p) := by
    rw [← hFe]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    have hp' : 2 < p := hp
    have hl : 0 ≤ (Real.log p)⁻¹ := inv_nonneg.mpr (Real.log_pos (by linarith)).le
    rw [Real.norm_eq_abs, abs_of_nonneg]
    dsimp [F]
    split_ifs
    · exact mul_nonneg hl (mul_nonneg hτ.le (Real.exp_pos _).le)
    · exact le_rfl
  have hM : MeasureTheory.Integrable (fun p => (Real.log (2:ℝ))⁻¹*
      Real.exp (-τ*p)) ν := by
    have he : (fun p : ℝ => (Real.log (2:ℝ))⁻¹*Real.exp (-τ*p)) =
        fun p => ((Real.log (2:ℝ))⁻¹/τ)*(τ*Real.exp (-τ*p)) := by
      funext p
      field_simp
    rw [he]
    exact (exponential_tail_integral 2 τ hτ).1.const_mul _
  have hmainMeas : Measurable (fun p : ℝ => (Real.log p)⁻¹*Real.exp (-τ*p)) := by
    fun_prop
  have hmain : MeasureTheory.Integrable (fun p => (Real.log p)⁻¹*
      Real.exp (-τ*p)) ν := by
    refine hM.mono' hmainMeas.aestronglyMeasurable ?_
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2
    filter_upwards [] with p hp
    have hp' : 2 < p := hp
    have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
    have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    have hinv : (Real.log p)⁻¹ ≤ (Real.log (2:ℝ))⁻¹ :=
      (inv_le_inv₀ hlogp hlog2).2 (Real.log_le_log (by norm_num) hp'.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (inv_nonneg.mpr hlogp.le) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
  have hnorm : MeasureTheory.Integrable (fun p => ∫ x, ‖F p x‖) ν := by
    apply hmain.congr
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2
    exact Filter.Eventually.of_forall (fun p hp => (hFn p hp).symm)
  have hprod : MeasureTheory.Integrable (Function.uncurry F)
      (ν.prod MeasureTheory.volume) :=
    (MeasureTheory.integrable_prod_iff hm.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall hFi, hnorm⟩
  have hright (x : ℝ) : (∫ p, F p x ∂ν) = K x*logCount x := by
    have he : (fun p => F p x) = (Set.Iio x).indicator
        (fun p => (Real.log p)⁻¹*K x) := by
      funext p
      by_cases hx : p < x <;> simp [F, Set.indicator, hx]
    rw [he, MeasureTheory.integral_indicator measurableSet_Iio]
    have hsets : ν.restrict (Set.Iio x) =
        MeasureTheory.volume.restrict (Set.Ioo (2:ℝ) x) := by
      dsimp [ν]
      rw [MeasureTheory.Measure.restrict_restrict measurableSet_Iio]
      congr 1
      ext p
      simp [and_comm]
    rw [show (∫ p in Set.Iio x, (Real.log p)⁻¹*K x ∂ν) =
        ∫ p in Set.Ioo (2:ℝ) x, (Real.log p)⁻¹*K x by
          rw [hsets]]
    rw [MeasureTheory.integral_mul_const]
    simp [logCount, mul_comm]
  have hrightInt : MeasureTheory.Integrable (fun x => ∫ p, F p x ∂ν) :=
    hprod.swap.integral_prod_left
  have hKint : MeasureTheory.Integrable (fun x => K x*logCount x) :=
    hrightInt.congr (Filter.Eventually.of_forall hright)
  refine ⟨hKint.integrableOn, ?_⟩
  calc
    _ = ∫ p, (∫ x, F p x) ∂ν := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with p
      rw [hFe]
      ring
    _ = ∫ x, (∫ p, F p x ∂ν) := MeasureTheory.integral_integral_swap hprod
    _ = ∫ x, K x*logCount x := MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall hright)
    _ = _ := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      by_cases hx : 0 < x
      · simp [Set.indicator, hx, K]
      · have hz : logCount x = 0 := by
          unfold logCount
          have hxe : x ≤ (2:ℝ) := by linarith
          simp [Set.Ioo_eq_empty_of_le hxe]
        simp [Set.indicator, hx, hz, K]

/-- The complete prime heat-trace remainder estimate conditional on
the explicit RH-type pointwise counting bound. RH itself and the
derivation of that classical counting bound from RH are not proved here.
This theorem connects the actual infinite prime sum, actual continuous
logarithmic-density integral, and the explicit rate. -/
theorem prime_heat_trace_conditional_rh (C τ : ℝ)
    (hC : 0 ≤ C) (hτ : 0 < τ) (hsmall : -Real.log τ ≥ 1)
    (hRH : ∀ x : ℝ, 0 < x → |strictPrimeCount x-logCount x| ≤
      C*x^(1/2:ℝ)*max 0 (Real.log x)) :
    |(∑' n : ℕ, Real.exp (-τ*(Nat.nth Nat.Prime n : ℝ))) -
      (∫ p in Set.Ioi (2:ℝ), Real.exp (-τ*p)/Real.log p)| ≤
      C*τ^(-1/2:ℝ)*(Real.Gamma (3/2)+Real.Gamma (5/2))*(-Real.log τ) := by
  have hp := prime_heat_trace_counting τ hτ
  have hs := smooth_heat_trace_counting τ hτ
  rw [hp.2, hs.2, ← MeasureTheory.integral_sub hp.1 hs.1]
  have he : (fun x : ℝ => τ*Real.exp (-τ*x)*strictPrimeCount x -
      τ*Real.exp (-τ*x)*logCount x) =
      fun x => τ*Real.exp (-τ*x)*(strictPrimeCount x-logCount x) := by
    funext x
    ring
  rw [he]
  exact infinite_laplace_rh_rate (fun x => strictPrimeCount x-logCount x)
    C τ hC hτ hsmall hRH


/-- Multiplication by a unit complex scalar preserves the actual
inner product, independent of coordinates. -/
theorem unit_phase_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (c : ℂ) (u v : E)
    (hc : star c*c = 1) :
    inner ℂ (c • u) (c • v) = inner ℂ u v := by
  rw [inner_smul_left, inner_smul_right]
  change star c*(c*inner ℂ u v) = inner ℂ u v
  rw [← mul_assoc, hc, one_mul]

/-- Horizontal derivatives transform equivariantly under a unit phase
and an arbitrary vertical term, as produced by a varying phase. -/
theorem horizontal_projection_phase {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (n v : E) (c d : ℂ)
    (hn : inner ℂ n n = 1) (hc : star c*c = 1) :
    horizontalProjection (c • n) (c • v+d • n) =
      c • horizontalProjection n v := by
  have hn' : inner ℂ (c • n) (c • n) = 1 := by
    rw [unit_phase_inner c n n hc, hn]
  have hne : c ≠ 0 := by
    intro h
    simp [h] at hc
  have hd : d • n = (d/c) • (c • n) := by
    rw [smul_smul, div_mul_cancel₀ _ hne]
  rw [hd, horizontal_projection_vertical_invariance _ _ _ hn']
  unfold horizontalProjection
  rw [unit_phase_inner c n v hc, smul_sub, smul_smul, smul_smul, mul_comm c]

/-- Intrinsic pullback of the Hermitian projective tensor by a real
linear tangent derivative. The actual derivative is supplied by the
smooth state map in the next theorem. -/
noncomputable def projectivePullback {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (n : E) (D : V →L[ℝ] E) (u v : V) : ℂ :=
  inner ℂ (horizontalProjection n (D u)) (horizontalProjection n (D v))

theorem projective_pullback_gauge {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (n : E) (D D' : V →L[ℝ] E) (c : ℂ) (d : V → ℂ)
    (u v : V) (hn : inner ℂ n n = 1) (hc : star c*c = 1)
    (hD : ∀ w, D' w = c • D w+d w • n) :
    projectivePullback (c • n) D' u v = projectivePullback n D u v := by
  unfold projectivePullback
  rw [hD u, hD v, horizontal_projection_phase n (D u) c (d u) hn hc,
    horizontal_projection_phase n (D v) c (d v) hn hc]
  exact unit_phase_inner c _ _ hc

/-- Normalization differentiates to the tangent condition for a genuine
differentiable state curve in a complex Hilbert space. -/
theorem normalized_curve_tangent {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (n : ℝ → E) (v : E) (t : ℝ)
    (h : HasDerivAt n v t) (hn : ∀ x, inner ℂ (n x) (n x) = 1) :
    inner ℂ (n t) v+inner ℂ v (n t) = 0 := by
  have hd := h.inner ℂ h
  have he : (fun x => inner ℂ (n x) (n x)) = fun _ : ℝ => (1:ℂ) := by
    funext x
    exact hn x
  rw [he] at hd
  exact hd.deriv.symm.trans (hasDerivAt_const t (1:ℂ)).deriv

/-- The real-parameter chain/product rule for a varying complex gauge,
followed by the intrinsic projection identity. -/
theorem projective_curve_gauge {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E]
    (n : ℝ → E) (c : ℝ → ℂ) (v : E) (d : ℂ) (t : ℝ)
    (hn : HasDerivAt n v t) (hd : HasDerivAt c d t)
    (hunit : inner ℂ (n t) (n t) = 1) (hc : star (c t)*c t = 1) :
    horizontalProjection (c t • n t)
      (deriv (fun x => c x • n x) t) =
      c t • horizontalProjection (n t) v := by
  rw [(hd.fun_smul hn).deriv]
  exact horizontal_projection_phase _ _ _ _ hunit hc

/-- In a chart, a connection acting on a covector. Γ i l is Γ^l_{ki}
for the fixed differentiation direction k. -/
noncomputable def covectorConnection {d : Type*} (s : Finset d)
    (Γ : d → d → ℝ) (p dp : d → ℝ) (i : d) : ℝ :=
  dp i-s.sum (fun l => Γ i l*p l)

/-- Connection acting on a covariant rank-two tensor in one chart direction. -/
noncomputable def tensorConnection {d : Type*} (s : Finset d)
    (Γ T dT : d → d → ℝ) (i j : d) : ℝ :=
  dT i j-s.sum (fun l => Γ i l*T l j)-s.sum (fun l => Γ j l*T i l)

/-- The connection product rule follows from the explicit connection
formulas and is not an assumed property. -/
theorem covector_outer_connection_rule {d : Type*} (s : Finset d)
    (Γ : d → d → ℝ) (p q dp dq : d → ℝ) (i j : d) :
    tensorConnection s Γ (fun a b => p a*q b)
      (fun a b => dp a*q b+p a*dq b) i j =
    covectorConnection s Γ p dp i*q j+p i*covectorConnection s Γ q dq j := by
  have h1 : (s.sum fun l => Γ i l*(p l*q j)) =
      (s.sum fun l => Γ i l*p l)*q j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have h2 : (s.sum fun l => Γ j l*(p i*q l)) =
      p i*(s.sum fun l => Γ j l*q l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  simp only [tensorConnection, covectorConnection, h1, h2]
  ring

/-- Actual chart-line derivative of a covector outer product, followed
by the connection correction. -/
theorem covector_outer_actual_derivative {d : Type*} (s : Finset d)
    (Γ : d → d → ℝ) (p q : d → ℝ → ℝ) (dp dq : d → ℝ)
    (t : ℝ) (i j : d)
    (hp : ∀ a, HasDerivAt (p a) (dp a) t)
    (hq : ∀ a, HasDerivAt (q a) (dq a) t) :
    tensorConnection s Γ (fun a b => p a t*q b t)
      (fun a b => deriv (fun x => p a x*q b x) t) i j =
    covectorConnection s Γ (fun a => p a t) dp i*q j t+
      p i t*covectorConnection s Γ (fun a => q a t) dq j := by
  have he : (fun a b => deriv (fun x => p a x*q b x) t) =
      fun a b => dp a*q b t+p a t*dq b := by
    funext a b
    exact ((hp a).mul (hq b)).deriv
  rw [he]
  exact covector_outer_connection_rule s Γ _ _ dp dq i j

/-- A metric-compatible connection obeys ∇(g S)=g dS for an actual
differentiable scalar S. Metric compatibility is explicitly required. -/
theorem metric_scalar_connection_rule {d : Type*} (s : Finset d)
    (Γ g dg : d → d → ℝ) (S dS : ℝ) (i j : d)
    (hmetric : tensorConnection s Γ g dg i j = 0) :
    tensorConnection s Γ (fun a b => g a b*S)
      (fun a b => dg a b*S+g a b*dS) i j = g i j*dS := by
  have h1 : (s.sum fun l => Γ i l*(g l j*S)) =
      (s.sum fun l => Γ i l*g l j)*S := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have h2 : (s.sum fun l => Γ j l*(g i l*S)) =
      (s.sum fun l => Γ j l*g i l)*S := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  unfold tensorConnection at hmetric ⊢
  rw [h1, h2]
  linear_combination S*hmetric

/-- The connection is linear on covariant rank-two tensors. -/
theorem tensor_connection_linear_combination {d : Type*} (s : Finset d)
    (Γ U V dU dV : d → d → ℝ) (a b : ℝ) (i j : d) :
    tensorConnection s Γ (fun k l => a*U k l+b*V k l)
      (fun k l => a*dU k l+b*dV k l) i j =
    a*tensorConnection s Γ U dU i j+b*tensorConnection s Γ V dV i j := by
  have h1 (k l : d) :
      (s.sum fun z => Γ k z*(a*U z l+b*V z l)) =
      a*(s.sum fun z => Γ k z*U z l)+b*(s.sum fun z => Γ k z*V z l) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  have h2 (k l : d) :
      (s.sum fun z => Γ l z*(a*U k z+b*V k z)) =
      a*(s.sum fun z => Γ l z*U k z)+b*(s.sum fun z => Γ l z*V k z) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  simp only [tensorConnection, h1, h2]
  ring

/-- Local stress derivative from actual chart-line derivatives and
metric compatibility. S is the scalar kinetic-plus-mass trace; its
derivative is supplied by the field/metric contraction rule.
No global manifold or Levi-Civita existence theorem is claimed. -/
theorem stress_actual_connection_derivative {d : Type*} (s : Finset d)
    (Γ : d → d → ℝ) (p : d → ℝ → ℝ) (g : d → d → ℝ → ℝ)
    (S : ℝ → ℝ) (dp : d → ℝ) (dg : d → d → ℝ)
    (dS t : ℝ) (i j : d)
    (hp : ∀ a, HasDerivAt (p a) (dp a) t)
    (hg : ∀ a b, HasDerivAt (g a b) (dg a b) t)
    (hS : HasDerivAt S dS t)
    (hmetric : tensorConnection s Γ (fun a b => g a b t) dg i j = 0) :
    tensorConnection s Γ
      (fun a b => 2*(p a t*p b t)-g a b t*S t)
      (fun a b => deriv (fun x => 2*(p a x*p b x)-g a b x*S x) t) i j =
      2*(covectorConnection s Γ (fun a => p a t) dp i*p j t+
        p i t*covectorConnection s Γ (fun a => p a t) dp j)-g i j t*dS := by
  have he : (fun a b => deriv (fun x => 2*(p a x*p b x)-g a b x*S x) t) =
      fun a b => 2*(dp a*p b t+p a t*dp b)-(dg a b*S t+g a b t*dS) := by
    funext a b
    exact ((((hp a).mul (hp b)).const_mul 2).sub ((hg a b).mul hS)).deriv
  rw [he]
  have hval : (fun a b => 2*(p a t*p b t)-g a b t*S t) =
      fun a b => 2*(p a t*p b t)+(-1)*(g a b t*S t) := by
    funext a b
    ring
  have hder : (fun a b => 2*(dp a*p b t+p a t*dp b)-(dg a b*S t+g a b t*dS)) =
      fun a b => 2*(dp a*p b t+p a t*dp b)+(-1)*(dg a b*S t+g a b t*dS) := by
    funext a b
    ring
  rw [hval, hder, tensor_connection_linear_combination,
    covector_outer_connection_rule,
    metric_scalar_connection_rule s Γ _ dg (S t) dS i j hmetric]
  ring

/-- Strict prime counting and the normalized logarithmic count both
vanish up to and including 2. -/
theorem counting_zero_below_two (x : ℝ) (hx : x ≤ 2) :
    strictPrimeCount x = 0 ∧ logCount x = 0 := by
  constructor
  · have hc : Nat.ceil x ≤ 2 := Nat.ceil_le.mpr (by exact_mod_cast hx)
    have hz : Nat.primeCounting' 2 = 0 := by decide
    have hh := Nat.monotone_primeCounting' hc
    rw [hz] at hh
    simp [strictPrimeCount, Nat.eq_zero_of_le_zero hh]
  · simp [logCount, Set.Ioo_eq_empty_of_le hx]

/-- The normalized logarithmic count is nonnegative at every real x. -/
theorem log_count_nonnegative (x : ℝ) : 0 ≤ logCount x := by
  unfold logCount
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioo
  intro y hy
  exact inv_nonneg.mpr (Real.log_pos (by linarith [hy.1])).le

/-- The smooth counting function is bounded on every finite positive
interval, using actual integrability of 1/log on [2,B]. -/
theorem log_count_monotone (x B : ℝ) (hx : x ≤ B) :
    logCount x ≤ logCount B := by
  unfold logCount
  have hc : ContinuousOn (fun y : ℝ => (Real.log y)⁻¹) (Set.Icc 2 B) := by
    apply ContinuousOn.inv₀
    · exact Real.continuousOn_log.mono (fun y hy => by
        have h : 0 < y := by linarith [hy.1]
        simpa using h.ne')
    · intro y hy
      exact (Real.log_pos (by linarith [hy.1])).ne'
  have hi : MeasureTheory.IntegrableOn (fun y : ℝ => (Real.log y)⁻¹)
      (Set.Ioo 2 B) := hc.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  apply MeasureTheory.setIntegral_mono_set hi
  · apply (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
    filter_upwards [] with y hy
    exact inv_nonneg.mpr (Real.log_pos (by linarith [hy.1])).le
  · exact Filter.Eventually.of_forall (fun y hy => ⟨hy.1, hy.2.trans_le hx⟩)

/-- An eventual RH-type estimate implies the global zero-extended
estimate used by the verified heat-trace theorem. The finite interval
is handled explicitly, rather than assuming the stronger hypothesis. -/
theorem eventual_prime_bound_global (C B : ℝ) (hC : 0 ≤ C) (_hB : 2 ≤ B)
    (h : ∀ x : ℝ, B ≤ x → |strictPrimeCount x-logCount x| ≤
      C*x^(1/2:ℝ)*Real.log x) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 0 < x →
      |strictPrimeCount x-logCount x| ≤ D*x^(1/2:ℝ)*max 0 (Real.log x) := by
  let M := strictPrimeCount B+logCount B
  let L := Real.log (2:ℝ)
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hM : 0 ≤ M := add_nonneg (by unfold strictPrimeCount; positivity) (log_count_nonnegative B)
  let D := max C (M/L)
  have hD : 0 ≤ D := hC.trans (le_max_left _ _)
  refine ⟨D, hD, ?_⟩
  intro x hx
  by_cases hlow : x ≤ 2
  · obtain ⟨hp, hl⟩ := counting_zero_below_two x hlow
    rw [hp, hl, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg hD (Real.rpow_nonneg hx.le _)) (le_max_left _ _)
  have hx2 : 2 < x := lt_of_not_ge hlow
  have hlog : L ≤ Real.log x := Real.log_le_log (by norm_num) hx2.le
  have hlog0 : 0 ≤ Real.log x := hL.le.trans hlog
  rw [max_eq_right hlog0]
  by_cases hlarge : B ≤ x
  · exact (h x hlarge).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C (M/L)) (Real.rpow_nonneg hx.le _)) hlog0)
  have hxb : x ≤ B := le_of_not_ge hlarge
  have hp0 : 0 ≤ strictPrimeCount x := by unfold strictPrimeCount; positivity
  have hpb : strictPrimeCount x ≤ strictPrimeCount B := by
    unfold strictPrimeCount
    exact_mod_cast Nat.monotone_primeCounting' (Nat.ceil_le_ceil hxb)
  have hl0 := log_count_nonnegative x
  have hlb := log_count_monotone x B hxb
  have hlocal : |strictPrimeCount x-logCount x| ≤ M := by
    rw [abs_le]
    constructor <;> dsimp [M] <;> linarith
  have hD' : M ≤ D*L := (div_le_iff₀ hL).mp (le_max_right C (M/L))
  have hsqrt : 1 ≤ x^(1/2:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hDL : D*L ≤ D*Real.log x := mul_le_mul_of_nonneg_left hlog hD
  have hDL' : D*Real.log x ≤ (D*x^(1/2:ℝ))*Real.log x := by
    apply mul_le_mul_of_nonneg_right _ hlog0
    simpa using mul_le_mul_of_nonneg_left hsqrt hD
  exact hlocal.trans (hD'.trans (hDL.trans hDL'))

/-- End-to-end spectral estimate from an eventual prime-counting
bound with one constant uniform in τ. This is the usual von Koch
form of the input, still not a proof of RH -> von Koch. -/
theorem prime_heat_trace_eventual_rh (C B : ℝ) (hC : 0 ≤ C) (hB : 2 ≤ B)
    (h : ∀ x : ℝ, B ≤ x → |strictPrimeCount x-logCount x| ≤
      C*x^(1/2:ℝ)*Real.log x) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ τ : ℝ, 0 < τ → -Real.log τ ≥ 1 →
      |(∑' n : ℕ, Real.exp (-τ*(Nat.nth Nat.Prime n : ℝ))) -
        (∫ p in Set.Ioi (2:ℝ), Real.exp (-τ*p)/Real.log p)| ≤
        D*τ^(-1/2:ℝ)*(Real.Gamma (3/2)+Real.Gamma (5/2))*(-Real.log τ) := by
  obtain ⟨D, hD, hglobal⟩ := eventual_prime_bound_global C B hC hB h
  exact ⟨D, hD, fun τ hτ hsmall =>
    prime_heat_trace_conditional_rh D τ hD hτ hsmall hglobal⟩


/-- Cancellation identity for the first index of a contracted inverse
metric derivative. This is a finite reindexing identity. -/
theorem connection_contract_first {d : Type*} (s : Finset d)
    (Γ A : d → d → ℝ) (p q : d → ℝ) :
    (s.sum fun i => s.sum fun j =>
      (s.sum fun l => Γ l i*A l j)*p i*q j) =
    (s.sum fun i => s.sum fun j =>
      A i j*(s.sum fun l => Γ i l*p l)*q j) := by
  calc
    _ = (s.sum fun i => s.sum fun j => s.sum fun l =>
        Γ l i*A l j*p i*q j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = (s.sum fun i => s.sum fun l => s.sum fun j =>
        Γ l i*A l j*p i*q j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = (s.sum fun l => s.sum fun i => s.sum fun j =>
        Γ l i*A l j*p i*q j) := Finset.sum_comm
    _ = (s.sum fun i => s.sum fun j => s.sum fun l =>
        Γ i l*A i j*p l*q j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l hl
      ring

/-- Cancellation identity for the second index. -/
theorem connection_contract_second {d : Type*} (s : Finset d)
    (Γ A : d → d → ℝ) (p q : d → ℝ) :
    (s.sum fun i => s.sum fun j =>
      (s.sum fun l => Γ l j*A i l)*p i*q j) =
    (s.sum fun i => s.sum fun j =>
      A i j*p i*(s.sum fun l => Γ j l*q l)) := by
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = (s.sum fun j => s.sum fun l => Γ l j*A i l*p i*q j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = (s.sum fun l => s.sum fun j => Γ l j*A i l*p i*q j) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring

/-- Derive the kinetic-trace differentiation formula from explicit
inverse-metric compatibility. A is the inverse metric at the point;
dA is its ordinary derivative in a fixed chart direction. -/
theorem covariant_kinetic_trace_jet {d : Type*} (s : Finset d)
    (Γ A dA : d → d → ℝ) (p dp : d → ℝ)
    (hA : ∀ i j, dA i j = -(s.sum fun l => Γ l i*A l j)-
      (s.sum fun l => Γ l j*A i l)) :
    (s.sum fun i => s.sum fun j =>
      dA i j*p i*p j+A i j*(dp i*p j+p i*dp j)) =
    (s.sum fun i => s.sum fun j => A i j*
      (covectorConnection s Γ p dp i*p j+
        p i*covectorConnection s Γ p dp j)) := by
  have hl : (s.sum fun i => s.sum fun j =>
      dA i j*p i*p j+A i j*(dp i*p j+p i*dp j)) =
      (s.sum fun i => s.sum fun j =>
        A i j*(dp i*p j+p i*dp j)-
          (s.sum fun l => Γ l i*A l j)*p i*p j-
          (s.sum fun l => Γ l j*A i l)*p i*p j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hA]
    ring
  have hr : (s.sum fun i => s.sum fun j => A i j*
      (covectorConnection s Γ p dp i*p j+
        p i*covectorConnection s Γ p dp j)) =
      (s.sum fun i => s.sum fun j =>
        A i j*(dp i*p j+p i*dp j)-
          A i j*(s.sum fun l => Γ i l*p l)*p j-
          A i j*p i*(s.sum fun l => Γ j l*p l)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    unfold covectorConnection
    ring
  rw [hl, hr]
  simp only [Finset.sum_sub_distrib]
  rw [connection_contract_first s Γ A p p,
    connection_contract_second s Γ A p p]

/-- Actual derivative of the contracted kinetic-plus-mass scalar
along a chart line. The connection terms cancel by the preceding
theorem; the derivative of the scalar trace is not assumed. -/
theorem covariant_trace_actual_derivative {d : Type*} (s : Finset d)
    (Γ : d → d → ℝ) (A : d → d → ℝ → ℝ)
    (p : d → ℝ → ℝ) (u : ℝ → ℝ)
    (dA : d → d → ℝ) (dp : d → ℝ) (du m2 t : ℝ)
    (ha : ∀ i j, HasDerivAt (A i j) (dA i j) t)
    (hp : ∀ i, HasDerivAt (p i) (dp i) t)
    (hu : HasDerivAt u du t)
    (hcompat : ∀ i j, dA i j = -(s.sum fun l => Γ l i*A l j t)-
      (s.sum fun l => Γ l j*A i l t)) :
    HasDerivAt (fun x => (s.sum fun i => s.sum fun j =>
        A i j x*(p i x*p j x))+m2*(u x*u x))
      ((s.sum fun i => s.sum fun j => A i j t*
        (covectorConnection s Γ (fun k => p k t) dp i*p j t+
          p i t*covectorConnection s Γ (fun k => p k t) dp j))+
        2*m2*u t*du) t := by
  have hsum : HasDerivAt (fun x => s.sum fun i => s.sum fun j =>
        A i j x*(p i x*p j x))
      (s.sum fun i => s.sum fun j =>
        dA i j*p i t*p j t+A i j t*(dp i*p j t+p i t*dp j)) t := by
    apply HasDerivAt.fun_sum
    intro i hi
    apply HasDerivAt.fun_sum
    intro j hj
    have hd := (ha i j).mul ((hp i).mul (hp j))
    simp only [Pi.mul_apply] at hd
    convert hd using 1
    ring
  have hmass : HasDerivAt (fun x => m2*(u x*u x)) (2*m2*u t*du) t := by
    convert (hu.mul hu).const_mul m2 using 1 <;> ring
  have h := hsum.add hmass
  rw [covariant_kinetic_trace_jet s Γ (fun i j => A i j t) dA
    (fun i => p i t) dp hcompat] at h
  exact h

/-- Symmetry of the inverse metric combines the two derivative terms. -/
theorem symmetric_kinetic_trace {d : Type*} (s : Finset d)
    (A : d → d → ℝ) (p H : d → ℝ)
    (hsym : ∀ i j, A i j = A j i) :
    (s.sum fun i => s.sum fun j => A i j*(H i*p j+p i*H j)) =
    (s.sum fun i => s.sum fun j => A i j*(2*p j*H i)) := by
  have hswap : (s.sum fun i => s.sum fun j => A i j*(p i*H j)) =
      (s.sum fun i => s.sum fun j => A i j*(H i*p j)) := by
    calc
      _ = (s.sum fun j => s.sum fun i => A i j*(p i*H j)) :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hsym j i]
        ring
  have hleft : (s.sum fun i => s.sum fun j => A i j*(H i*p j+p i*H j)) =
      (s.sum fun i => s.sum fun j => A i j*(H i*p j))+
      (s.sum fun i => s.sum fun j => A i j*(p i*H j)) := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [hleft, hswap, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Actual inverse metric contraction, not an assumed trace equality. -/
theorem inverse_metric_contraction {d : Type*} [DecidableEq d]
    (s : Finset d) (A g : d → d → ℝ) (z : d → ℝ)
    (ν : d) (hν : ν ∈ s)
    (hinv : ∀ i, (s.sum fun j => A i j*g j ν) =
      if i = ν then 1 else 0) :
    (s.sum fun i => s.sum fun j => A i j*(g j ν*z i)) = z ν := by
  calc
    _ = (s.sum fun i => (s.sum fun j => A i j*g j ν)*z i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (s.sum fun i => (if i = ν then 1 else 0)*z i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hinv]
    _ = _ := by simp [ite_mul, hν]

/-- Local contracted stress identity with inverse metric and symmetric
Hessian. The trace derivative is explicitly the expression obtained
by covariant_trace_actual_derivative. -/
theorem local_metric_stress_divergence {d : Type*} [DecidableEq d]
    (s : Finset d) (A g : d → d → ℝ) (p : d → ℝ)
    (H : d → d → ℝ) (m2 u : ℝ) (ν : d) (hν : ν ∈ s)
    (hA : ∀ i j, A i j = A j i)
    (hH : ∀ i j, H i j = H j i)
    (hinv : ∀ i, (s.sum fun j => A i j*g j ν) =
      if i = ν then 1 else 0) :
    (s.sum fun i => s.sum fun j => A i j*
      (2*(H i j*p ν+p j*H i ν)-g j ν*
        ((s.sum fun a => s.sum fun b => A a b*(H i a*p b+p a*H i b))+
          2*m2*u*p i))) =
      2*((s.sum fun i => s.sum fun j => A i j*H i j)-m2*u)*p ν := by
  let z : d → ℝ := fun i =>
    (s.sum fun a => s.sum fun b => A a b*(H i a*p b+p a*H i b))+2*m2*u*p i
  change (s.sum fun i => s.sum fun j => A i j*
    (2*(H i j*p ν+p j*H i ν)-g j ν*z i)) = _
  have hz : z ν = (s.sum fun i => s.sum fun j =>
      A i j*(2*p j*H ν i))+2*m2*u*p ν := by
    dsimp [z]
    rw [symmetric_kinetic_trace s A p (H ν) hA]
  calc
    _ = (s.sum fun i => s.sum fun j => A i j*(2*(H i j*p ν+p j*H i ν)))-
        (s.sum fun i => s.sum fun j => A i j*(g j ν*z i)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ = (s.sum fun i => s.sum fun j => A i j*(2*(H i j*p ν+p j*H i ν)))-z ν := by
      rw [inverse_metric_contraction s A g z ν hν hinv]
    _ = (s.sum fun i => s.sum fun j => A i j*
        (2*(H i j*p ν+p j*H i ν)-2*p j*H ν i))-2*m2*u*p ν := by
      rw [hz]
      simp only [mul_sub, Finset.sum_sub_distrib]
      abel
    _ = _ := covariant_scalar_divergence_jet s A p H m2 u ν hH

/-- On-shell local conservation for a general inverse metric. This is
a contraction-level theorem with explicit compatibility assumptions,
not a global manifold construction. -/
theorem local_metric_stress_on_shell {d : Type*} [DecidableEq d]
    (s : Finset d) (A g : d → d → ℝ) (p : d → ℝ)
    (H : d → d → ℝ) (m2 u : ℝ) (ν : d) (hν : ν ∈ s)
    (hA : ∀ i j, A i j = A j i)
    (hH : ∀ i j, H i j = H j i)
    (hinv : ∀ i, (s.sum fun j => A i j*g j ν) =
      if i = ν then 1 else 0)
    (hkg : (s.sum fun i => s.sum fun j => A i j*H i j) = m2*u) :
    (s.sum fun i => s.sum fun j => A i j*
      (2*(H i j*p ν+p j*H i ν)-g j ν*
        ((s.sum fun a => s.sum fun b => A a b*(H i a*p b+p a*H i b))+
          2*m2*u*p i))) = 0 := by
  rw [local_metric_stress_divergence s A g p H m2 u ν hν hA hH hinv, hkg]
  ring


/-- Projective quantum geometric tensor of an actual differentiable
local lift. The tangent map is the real Frechet derivative. -/
noncomputable def projectiveTensor {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (n : V → E) (x u v : V) : ℂ :=
  projectivePullback (n x) (fderiv ℝ n x) u v

theorem projective_tensor_gauge_fderiv {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E]
    (n : V → E) (c : V → ℂ) (x u v : V)
    (hn : DifferentiableAt ℝ n x) (hc : DifferentiableAt ℝ c x)
    (hunit : inner ℂ (n x) (n x) = 1) (hphase : star (c x)*c x = 1) :
    projectiveTensor (fun y => c y • n y) x u v =
      projectiveTensor n x u v := by
  unfold projectiveTensor
  rw [(hc.hasFDerivAt.fun_smul hn.hasFDerivAt).fderiv]
  apply projective_pullback_gauge _ _ _ _ (fderiv ℝ c x) _ _ hunit hphase
  intro w
  rfl

/-- Pullback under an actual differentiable change of parameters. -/
theorem projective_tensor_reparam {U V E : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (n : V → E) (g : U → V) (x u v : U)
    (hn : DifferentiableAt ℝ n (g x)) (hg : DifferentiableAt ℝ g x) :
    projectiveTensor (n ∘ g) x u v =
      projectiveTensor n (g x) (fderiv ℝ g x u) (fderiv ℝ g x v) := by
  unfold projectiveTensor
  rw [fderiv_comp x hn hg]
  rfl

theorem projective_tensor_hermitian {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (n : V → E) (x u v : V) :
    star (projectiveTensor n x v u) = projectiveTensor n x u v := by
  unfold projectiveTensor projectivePullback
  exact inner_conj_symm _ _

theorem projective_tensor_nonnegative {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (n : V → E) (x u : V) :
    0 ≤ (projectiveTensor n x u u).re := by
  unfold projectiveTensor projectivePullback
  rw [show (inner ℂ (horizontalProjection (n x) (fderiv ℝ n x u))
      (horizontalProjection (n x) (fderiv ℝ n x u))).re =
      ‖horizontalProjection (n x) (fderiv ℝ n x u)‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ) _]
  exact sq_nonneg _

/-- Differentiating the normalization constraint with a full tangent
derivative gives a purely imaginary vertical coefficient. -/
theorem normalized_fderiv_vertical_real_zero {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (n : V → E) (x u : V) (hn : DifferentiableAt ℝ n x)
    (hunit : ∀ y, inner ℂ (n y) (n y) = 1) :
    (inner ℂ (n x) (fderiv ℝ n x u)).re = 0 := by
  have he : (fun y => inner ℂ (n y) (n y)) = fun _ : V => (1:ℂ) := by
    funext y
    exact hunit y
  have h := fderiv_inner_apply ℂ hn hn u
  rw [he] at h
  have hz : fderiv ℝ (fun _ : V => (1:ℂ)) x = 0 := (hasFDerivAt_const (1:ℂ) x).fderiv
  rw [hz] at h
  have hr := congrArg Complex.re h
  simp only [ContinuousLinearMap.zero_apply, Complex.zero_re, Complex.add_re] at hr
  have hs : (inner ℂ (fderiv ℝ n x u) (n x)).re =
      (inner ℂ (n x) (fderiv ℝ n x u)).re := inner_re_symm (𝕜 := ℂ) _ _
  linarith

/-- Intrinsic Gram identity, with no coordinate choices. -/
theorem horizontal_gram_subtract {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n u v : E) (hn : inner ℂ n n = 1) :
    inner ℂ (horizontalProjection n u) (horizontalProjection n v) =
      inner ℂ u v - star (inner ℂ n u)*inner ℂ n v := by
  unfold horizontalProjection
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    inner_smul_right, inner_smul_left, inner_smul_left,
    inner_smul_right, hn]
  rw [show inner ℂ u n = star (inner ℂ n u) from (inner_conj_symm _ _).symm]
  ring

/-- Real part of a normalized vertical inner product is zero, so the
vertical subtraction has no imaginary contribution. -/
theorem horizontal_gram_imaginary {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n u v : E) (hn : inner ℂ n n = 1)
    (hu : (inner ℂ n u).re = 0) (hv : (inner ℂ n v).re = 0) :
    (inner ℂ (horizontalProjection n u) (horizontalProjection n v)).im =
      (inner ℂ u v).im := by
  rw [horizontal_gram_subtract n u v hn]
  have hure : (inner ℂ u n).re = 0 := (inner_re_symm (𝕜 := ℂ) u n).trans hu
  simp [Complex.sub_im, Complex.mul_im, hure, hv]

/-- Actual antisymmetric derivative of the Berry connection. The
symmetric second derivative cancels, rather than being discarded. -/
theorem berry_curvature_fderiv {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (n : V → E) (x u v : V)
    (hn : DifferentiableAt ℝ n x)
    (hd : DifferentiableAt ℝ (fderiv ℝ n) x)
    (hs : IsSymmSndFDerivAt ℝ n x)
    (hunit : ∀ y, inner ℂ (n y) (n y) = 1) :
    (fderiv ℝ (fun y => inner ℂ (n y) (fderiv ℝ n y v)) x u).im -
      (fderiv ℝ (fun y => inner ℂ (n y) (fderiv ℝ n y u)) x v).im =
      2*(projectiveTensor n x u v).im := by
  let D := fderiv ℝ n
  have hEval (w : V) : HasFDerivAt (fun y => D y w)
      ((ContinuousLinearMap.apply ℝ E w).comp (fderiv ℝ D x)) x :=
    (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp x hd.hasFDerivAt
  have he (w z : V) : fderiv ℝ (fun y => D y w) x z =
      fderiv ℝ D x z w := by
    rw [(hEval w).fderiv]
    rfl
  change (fderiv ℝ (fun y => inner ℂ (n y) (D y v)) x u).im -
    (fderiv ℝ (fun y => inner ℂ (n y) (D y u)) x v).im = _
  rw [fderiv_inner_apply ℂ hn (hEval v).differentiableAt,
    fderiv_inner_apply ℂ hn (hEval u).differentiableAt, he v u, he u v]
  change (inner ℂ (n x) (fderiv ℝ D x u v) + inner ℂ (D x u) (D x v)).im -
    (inner ℂ (n x) (fderiv ℝ D x v u) + inner ℂ (D x v) (D x u)).im = _
  have hsym : fderiv ℝ D x u v = fderiv ℝ D x v u := hs u v
  rw [hsym]
  unfold projectiveTensor projectivePullback
  rw [horizontal_gram_imaginary _ _ _ (hunit x)
    (normalized_fderiv_vertical_real_zero n x u hn hunit)
    (normalized_fderiv_vertical_real_zero n x v hn hunit)]
  have him : (inner ℂ (D x v) (D x u)).im =
      -(inner ℂ (D x u) (D x v)).im := inner_im_symm (𝕜 := ℂ) _ _
  simp only [Complex.add_im]
  linarith

/-- Actual C² local lifts automatically have the derivative regularity
and Hessian symmetry needed above. -/
theorem berry_curvature_C2 {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (n : V → E) (x u v : V) (hn : ContDiffAt ℝ 2 n x)
    (hunit : ∀ y, inner ℂ (n y) (n y) = 1) :
    (fderiv ℝ (fun y => inner ℂ (n y) (fderiv ℝ n y v)) x u).im -
      (fderiv ℝ (fun y => inner ℂ (n y) (fderiv ℝ n y u)) x v).im =
      2*(projectiveTensor n x u v).im := by
  apply berry_curvature_fderiv n x u v
  · exact hn.differentiableAt (by norm_num)
  · exact (hn.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  · exact hn.isSymmSndFDerivAt (by simp)
  · exact hunit

/-- Actual complex finite multiplet inner product. -/
theorem finite_inner_re_im {ι : Type*} [Fintype ι]
    (u v : EuclideanSpace ℂ ι) :
    (inner ℂ u v).re = ∑ i, ((u i).re*(v i).re+(u i).im*(v i).im) ∧
    (inner ℂ u v).im = ∑ i, ((u i).re*(v i).im-(u i).im*(v i).re) := by
  rw [PiLp.inner_apply]
  constructor
  · rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [RCLike.inner_apply, Complex.mul_re]
    ring
  · rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [RCLike.inner_apply, Complex.mul_im]
    ring

/-- Finite weighted real and imaginary Gram components computed
from actual complex vectors. The log-amplitude and phase slopes
are encoded as componentwise complex logarithmic derivative data. -/
theorem finite_horizontal_covariance {ι : Type*} [Fintype ι]
    (n U V : EuclideanSpace ℂ ι) (q a b c d : ι → ℝ) (Q : ℝ)
    (hu : ∀ i, U i = n i * ⟨a i,b i⟩)
    (hv : ∀ i, V i = n i * ⟨c i,d i⟩)
    (hq : ∀ i, Q*((n i).re^2+(n i).im^2) = q i) :
    Q*(inner ℂ U V).re = ∑ i, q i*(a i*c i+b i*d i) ∧
    Q*(inner ℂ U V).im = ∑ i, q i*(a i*d i-b i*c i) := by
  obtain ⟨hre,him⟩ := finite_inner_re_im U V
  constructor
  · rw [hre, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hu i,hv i]
    simp only [Complex.mul_re, Complex.mul_im]
    linear_combination (a i*c i+b i*d i)*hq i
  · rw [him, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hu i,hv i]
    simp only [Complex.mul_re, Complex.mul_im]
    linear_combination (a i*d i-b i*c i)*hq i

/-- Componentwise horizontal projection subtracts the actual Berry
coefficient. This derives centered slopes rather than assuming
the horizontal vectors themselves. -/
theorem finite_projected_component {ι : Type*} [Fintype ι]
    (n U : EuclideanSpace ℂ ι) (a b : ι → ℝ) (B : ℝ)
    (hU : ∀ i, U i = n i*⟨a i,b i⟩)
    (hB : inner ℂ n U = ⟨0,B⟩) (i : ι) :
    horizontalProjection n U i = n i*⟨a i,b i-B⟩ := by
  unfold horizontalProjection
  rw [PiLp.sub_apply, PiLp.smul_apply, hB, hU i]
  change n i*⟨a i,b i⟩- (⟨0,B⟩:ℂ)*n i = _
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im] <;> ring

/-- The actual differential projective tensor equals the weighted
centered amplitude-phase covariance, including its imaginary part.
The normalized-state component slope identities and Berry means
are explicit hypotheses, not hidden axioms. -/
theorem projective_tensor_finite_covariance {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : V → EuclideanSpace ℂ ι) (x u v : V)
    (q a b c d : ι → ℝ) (Q B D : ℝ)
    (hu : ∀ i, fderiv ℝ n x u i = n x i*⟨a i,b i⟩)
    (hv : ∀ i, fderiv ℝ n x v i = n x i*⟨c i,d i⟩)
    (hB : inner ℂ (n x) (fderiv ℝ n x u) = ⟨0,B⟩)
    (hD : inner ℂ (n x) (fderiv ℝ n x v) = ⟨0,D⟩)
    (hq : ∀ i, Q*((n x i).re^2+(n x i).im^2) = q i) :
    Q*(projectiveTensor n x u v).re =
      ∑ i, q i*(a i*c i+(b i-B)*(d i-D)) ∧
    Q*(projectiveTensor n x u v).im =
      ∑ i, q i*(a i*(d i-D)-(b i-B)*c i) := by
  unfold projectiveTensor projectivePullback
  exact finite_horizontal_covariance (n x)
    (horizontalProjection (n x) (fderiv ℝ n x u))
    (horizontalProjection (n x) (fderiv ℝ n x v))
    q a (fun i => b i-B) c (fun i => d i-D) Q
    (fun i => finite_projected_component _ _ a b B hu hB i)
    (fun i => finite_projected_component _ _ c d D hv hD i) hq

/-- Berry mean derived from the actual complex finite inner product,
rather than supplied independently. -/
theorem finite_berry_mean {ι : Type*} [Fintype ι]
    (n U : EuclideanSpace ℂ ι) (a b : ι → ℝ)
    (hU : ∀ i, U i = n i*⟨a i,b i⟩)
    (ha : (∑ i, ((n i).re^2+(n i).im^2)*a i) = 0) :
    inner ℂ n U = ⟨0,∑ i, ((n i).re^2+(n i).im^2)*b i⟩ := by
  obtain ⟨hr,hi⟩ := finite_inner_re_im n U
  apply Complex.ext
  · change (inner ℂ n U).re = 0
    rw [hr, ← ha]
    apply Finset.sum_congr rfl
    intro i hi'
    rw [hU i]
    simp only [Complex.mul_re, Complex.mul_im]
    ring
  · change (inner ℂ n U).im = _
    rw [hi]
    apply Finset.sum_congr rfl
    intro i hi'
    rw [hU i]
    simp only [Complex.mul_re, Complex.mul_im]
    ring

/-- Normalization and the actual derivative imply that the real
log-amplitude slopes are centered. The phase mean is therefore
computed solely from the component slope data. -/
theorem finite_normalized_berry_mean {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : V → EuclideanSpace ℂ ι) (x u : V) (a b : ι → ℝ)
    (hn : DifferentiableAt ℝ n x) (hunit : ∀ y, inner ℂ (n y) (n y) = 1)
    (hu : ∀ i, fderiv ℝ n x u i = n x i*⟨a i,b i⟩) :
    inner ℂ (n x) (fderiv ℝ n x u) =
      ⟨0,∑ i, ((n x i).re^2+(n x i).im^2)*b i⟩ := by
  apply finite_berry_mean _ _ a b hu
  have hzero := normalized_fderiv_vertical_real_zero n x u hn hunit
  rw [(finite_inner_re_im (n x) (fderiv ℝ n x u)).1] at hzero
  rw [← hzero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hu i]
  simp only [Complex.mul_re, Complex.mul_im]
  ring

/-- Full local-lift covariance identity, deriving the Berry means
from differentiability and normalization. a,c are the centered
log-amplitude slopes of the normalized multiplet. -/
theorem projective_tensor_normalized_covariance {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : V → EuclideanSpace ℂ ι) (x u v : V)
    (q a b c d : ι → ℝ) (Q : ℝ)
    (hn : DifferentiableAt ℝ n x) (hunit : ∀ y, inner ℂ (n y) (n y) = 1)
    (hu : ∀ i, fderiv ℝ n x u i = n x i*⟨a i,b i⟩)
    (hv : ∀ i, fderiv ℝ n x v i = n x i*⟨c i,d i⟩)
    (hq : ∀ i, Q*((n x i).re^2+(n x i).im^2) = q i) :
    let B := ∑ i, ((n x i).re^2+(n x i).im^2)*b i
    let D := ∑ i, ((n x i).re^2+(n x i).im^2)*d i
    Q*(projectiveTensor n x u v).re =
      ∑ i, q i*(a i*c i+(b i-B)*(d i-D)) ∧
    Q*(projectiveTensor n x u v).im =
      ∑ i, q i*(a i*(d i-D)-(b i-B)*c i) := by
  dsimp
  exact projective_tensor_finite_covariance n x u v q a b c d Q _ _
    hu hv (finite_normalized_berry_mean n x u a b hn hunit hu)
    (finite_normalized_berry_mean n x v c d hn hunit hv) hq

/-- Gauge equivalence of normalized first jets: same phase and arbitrary
vertical derivative. The quotient is of first jets, not a claimed
smooth atlas on complex projective space. -/
def ProjectiveJet {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E] :=
  { p : E × (V →L[ℝ] E) // inner ℂ p.1 p.1 = 1 }

def projectiveJetRel {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (j k : ProjectiveJet (V := V) (E := E)) : Prop :=
  ∃ (c : ℂ) (d : V → ℂ), star c*c = 1 ∧ k.val.1 = c • j.val.1 ∧
    ∀ w, k.val.2 w = c • j.val.2 w+d w • j.val.1

/-- The pullback tensor descends to the quotient generated by the
phase/vertical gauge relation on normalized first jets. -/
noncomputable def quotientJetTensor {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (j : Quot (projectiveJetRel (V := V) (E := E))) (u v : V) : ℂ :=
  Quot.lift (fun k => projectivePullback k.val.1 k.val.2 u v)
    (by
      intro j k h
      obtain ⟨c,d,hc,hn,hD⟩ := h
      change projectivePullback j.val.1 j.val.2 u v = projectivePullback k.val.1 k.val.2 u v
      rw [hn]
      exact (projective_pullback_gauge j.val.1 j.val.2 k.val.2 c d u v
        j.property hc hD).symm) j

theorem quotient_jet_tensor_rep {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (j : ProjectiveJet (V := V) (E := E)) (u v : V) :
    quotientJetTensor (Quot.mk _ j) u v =
      projectivePullback j.val.1 j.val.2 u v := rfl


/-- A linear-functional affine representative of a projective ray.
On the nonvanishing chart it lies in the affine hyperplane ℓ(v)=1. -/
noncomputable def affineRayRep {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (ell : E →L[ℂ] ℂ) (v : E) : E :=
  (ell v)⁻¹ • v

theorem affine_ray_rep_scale {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (ell : E →L[ℂ] ℂ) (v : E) (c : ℂ)
    (hc : c ≠ 0) :
    affineRayRep ell (c • v) = affineRayRep ell v := by
  unfold affineRayRep
  rw [map_smul, smul_smul]
  change ((c*ell v)⁻¹*c) • v = (ell v)⁻¹ • v
  have he : (c*ell v)⁻¹*c = (ell v)⁻¹ := by
    by_cases hz : ell v = 0
    · simp [hz]
    · field_simp
  rw [he]

/-- Affine representatives descend to Mathlib's actual projective
space, the quotient of nonzero vectors by nonzero complex scalars. -/
noncomputable def projectiveAffineRep {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (ell : E →L[ℂ] ℂ) (p : Projectivization ℂ E) : E :=
  Projectivization.lift (fun v => affineRayRep ell v.val) (by
    intro a b c h
    change a.val = c • b.val at h
    have hc : c ≠ 0 := by
      intro hz
      apply a.property
      simpa [hz] using h
    change affineRayRep ell a.val = affineRayRep ell b.val
    rw [h]
    exact affine_ray_rep_scale ell b.val c hc) p

theorem projective_affine_rep_mk {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (ell : E →L[ℂ] ℂ) (v : E) (hv : v ≠ 0) :
    projectiveAffineRep ell (Projectivization.mk ℂ v hv) = affineRayRep ell v := rfl

theorem affine_rep_hyperplane {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (ell : E →L[ℂ] ℂ) (v : E) (hv : ell v ≠ 0) :
    ell (affineRayRep ell v) = 1 := by
  simp [affineRayRep, map_smul, smul_eq_mul, hv]

theorem affine_rep_nonzero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (ell : E →L[ℂ] ℂ) (v : E) (hv : ell v ≠ 0) :
    affineRayRep ell v ≠ 0 := by
  intro h
  have he := affine_rep_hyperplane ell v hv
  simp [h] at he

theorem affine_rep_same_projective_point {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (ell : E →L[ℂ] ℂ) (v : E)
    (hv : v ≠ 0) (h : ell v ≠ 0) :
    Projectivization.mk ℂ (affineRayRep ell v) (affine_rep_nonzero ell v h) =
      Projectivization.mk ℂ v hv := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  exact ⟨(ell v)⁻¹,rfl⟩

theorem affine_rep_fixed_on_hyperplane {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (ell : E →L[ℂ] ℂ) (v : E) (hv : ell v = 1) :
    affineRayRep ell v = v := by simp [affineRayRep,hv]

/-- Algebraic chart equivalence for a nonvanishing linear-functional
chart on the actual projectivization. The source condition is
representative-independent by the quotient construction. -/
noncomputable def projectiveAffineEquiv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (ell : E →L[ℂ] ℂ) :
    {p : Projectivization ℂ E // ell p.rep ≠ 0} ≃ {v : E // ell v = 1} where
  toFun p := ⟨projectiveAffineRep ell p.val, by
    rw [← p.val.mk_rep, projective_affine_rep_mk]
    exact affine_rep_hyperplane ell p.val.rep p.property⟩
  invFun v := by
    have hv : v.val ≠ 0 := by
      intro h
      have he := v.property
      simp [h] at he
    let p := Projectivization.mk ℂ v.val hv
    refine ⟨p, ?_⟩
    intro h
    obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v.val hv
    have he : ell p.rep = (c:ℂ)*ell v.val := by
      have hc' : (c:ℂ) • v.val = p.rep := hc
      calc
        ell p.rep = ell ((c:ℂ) • v.val) := congrArg ell hc'.symm
        _ = (c:ℂ)*ell v.val := by simp [map_smul, smul_eq_mul]
    rw [h,v.property,mul_one] at he
    exact Units.ne_zero c he.symm
  left_inv p := by
    apply Subtype.ext
    change Projectivization.mk ℂ (projectiveAffineRep ell p.val) _ = p.val
    have he : projectiveAffineRep ell p.val = affineRayRep ell p.val.rep := by
      rw [← p.val.mk_rep, projective_affine_rep_mk]
    calc
      _ = Projectivization.mk ℂ (affineRayRep ell p.val.rep)
          (affine_rep_nonzero ell p.val.rep p.property) := by
        apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
        exact ⟨1, by rw [one_smul]; exact he⟩
      _ = Projectivization.mk ℂ p.val.rep p.val.rep_nonzero :=
        affine_rep_same_projective_point ell p.val.rep p.val.rep_nonzero p.property
      _ = p.val := p.val.mk_rep
  right_inv v := by
    apply Subtype.ext
    change projectiveAffineRep ell (Projectivization.mk ℂ v.val _) = v.val
    rw [projective_affine_rep_mk]
    exact affine_rep_fixed_on_hyperplane ell v.val v.property

theorem projective_affine_transition_smooth {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (ell : E →L[ℂ] ℂ) :
    ContDiffOn ℂ (⊤ : WithTop ℕ∞) (affineRayRep ell)
      {v : E | ell v ≠ 0} := by
  unfold affineRayRep
  exact (ell.contDiff.contDiffOn.inv (fun _ hx => hx)).smul contDiff_id.contDiffOn

/-- The transition maps compose on their common domain; this supplies
the cocycle law in affine representatives. -/
theorem projective_affine_transition_cocycle {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ell ell' : E →L[ℂ] ℂ) (v : E) (hv : ell v ≠ 0) :
    affineRayRep ell' (affineRayRep ell v) = affineRayRep ell' v := by
  exact affine_ray_rep_scale ell' v (ell v)⁻¹ (inv_ne_zero hv)

/-- Two normalized representatives of the same actual projective
point differ by a unit complex scalar; the scalar is their inner
product. -/
theorem normalized_same_projective_ray {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n m : E) (hn : inner ℂ n n = 1) (hm : inner ℂ m m = 1)
    (hnz : n ≠ 0) (hmz : m ≠ 0)
    (h : Projectivization.mk ℂ m hmz = Projectivization.mk ℂ n hnz) :
    m = inner ℂ n m • n ∧ star (inner ℂ n m)*inner ℂ n m = 1 := by
  obtain ⟨c,hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ m n hmz hnz).1 h
  have hinner : inner ℂ n m = c := by
    rw [← hc, inner_smul_right, hn, mul_one]
  rw [hinner]
  refine ⟨hc.symm, ?_⟩
  have hval : inner ℂ (c • n) (c • n) = star c*c := by
    rw [inner_smul_left, inner_smul_right, hn, mul_one]
    rfl
  rw [hc,hm] at hval
  exact hval.symm

/-- The tensor of two actual normalized differentiable lifts of the
same projective map is identical. No gauge differentiability is
assumed: the gauge is constructed from the inner product. -/
theorem projective_tensor_same_ray_lifts {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E]
    (n m : V → E) (x u v : V)
    (hn : DifferentiableAt ℝ n x) (hm : DifferentiableAt ℝ m x)
    (hunitn : ∀ y, inner ℂ (n y) (n y) = 1)
    (hunitm : ∀ y, inner ℂ (m y) (m y) = 1)
    (hnz : ∀ y, n y ≠ 0) (hmz : ∀ y, m y ≠ 0)
    (h : ∀ y, Projectivization.mk ℂ (m y) (hmz y) =
      Projectivization.mk ℂ (n y) (hnz y)) :
    projectiveTensor m x u v = projectiveTensor n x u v := by
  let c : V → ℂ := fun y => inner ℂ (n y) (m y)
  have he : m = fun y => c y • n y := by
    funext y
    exact (normalized_same_projective_ray (n y) (m y) (hunitn y)
      (hunitm y) (hnz y) (hmz y) (h y)).1
  have hc : DifferentiableAt ℝ c x := hn.inner ℂ hm
  have hphase : star (c x)*c x = 1 :=
    (normalized_same_projective_ray (n x) (m x) (hunitn x)
      (hunitm x) (hnz x) (hmz x) (h x)).2
  rw [he]
  exact projective_tensor_gauge_fderiv n c x u v hn hc (hunitn x) hphase


/-- The actual quotient topology on complex rays, not a discrete
topology or a topology assumed in a theorem hypothesis. -/
def projectiveRayTopology {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] : TopologicalSpace (Projectivization ℂ E) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℂ E)))

attribute [local instance] projectiveRayTopology

theorem projective_ray_quotient_map {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] :
    Topology.IsQuotientMap
      (Projectivization.mk' ℂ : {v : E // v ≠ 0} → Projectivization ℂ E) :=
  isQuotientMap_quotient_mk'

theorem projective_chart_nonvanishing_mk {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (ell : E →L[ℂ] ℂ) (v : E) (hv : v ≠ 0) :
    ell (Projectivization.mk ℂ v hv).rep ≠ 0 ↔ ell v ≠ 0 := by
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  have he : (c:ℂ) • v = (Projectivization.mk ℂ v hv).rep := hc
  rw [← he, map_smul]
  change (c:ℂ)*ell v ≠ 0 ↔ ell v ≠ 0
  simp [mul_ne_zero_iff, Units.ne_zero c]

/-- The affine chart domains are open in the quotient topology. -/
theorem projective_chart_domain_open {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (ell : E →L[ℂ] ℂ) :
    IsOpen {p : Projectivization ℂ E | ell p.rep ≠ 0} := by
  apply (projective_ray_quotient_map (E := E)).isOpen_preimage.mp
  have he : (Projectivization.mk' ℂ : {v : E // v ≠ 0} → Projectivization ℂ E) ⁻¹'
      {p : Projectivization ℂ E | ell p.rep ≠ 0} =
      {v : {v : E // v ≠ 0} | ell v.val ≠ 0} := by
    ext v
    exact projective_chart_nonvanishing_mk ell v.val v.property
  rw [he]
  exact isOpen_ne_fun (ell.continuous.comp continuous_subtype_val) continuous_const

/-- The linear-functional chart family covers the entire projective
space of a complex inner product space. -/
theorem projective_chart_cover {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (p : Projectivization ℂ E) :
    ∃ ell : E →L[ℂ] ℂ, ell p.rep ≠ 0 := by
  refine ⟨innerSL ℂ p.rep, ?_⟩
  rw [innerSL_apply]
  exact (inner_self_ne_zero (𝕜 := ℂ)).2 p.rep_nonzero

/-- Chart continuity follows by descent from the actual quotient
map and continuity on the nonvanishing domain. -/
theorem projective_affine_rep_continuousOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (ell : E →L[ℂ] ℂ) :
    ContinuousOn (projectiveAffineRep ell)
      {p : Projectivization ℂ E | ell p.rep ≠ 0} := by
  apply (continuousOn_open_iff (projective_chart_domain_open ell)).2
  intro t ht
  apply (projective_ray_quotient_map (E := E)).isOpen_preimage.mp
  let S : Set {v : E // v ≠ 0} := {v | ell v.val ≠ 0}
  have he : (Projectivization.mk' ℂ : {v : E // v ≠ 0} → Projectivization ℂ E) ⁻¹'
      ({p : Projectivization ℂ E | ell p.rep ≠ 0} ∩
        (projectiveAffineRep ell) ⁻¹' t) =
      S ∩ (fun v : {v : E // v ≠ 0} => affineRayRep ell v.val) ⁻¹' t := by
    ext v
    change (ell (Projectivization.mk ℂ v.val v.property).rep ≠ 0 ∧
      projectiveAffineRep ell (Projectivization.mk ℂ v.val v.property) ∈ t) ↔
      (ell v.val ≠ 0 ∧ affineRayRep ell v.val ∈ t)
    rw [projective_chart_nonvanishing_mk, projective_affine_rep_mk]
  rw [he]
  have hs : IsOpen S :=
    isOpen_ne_fun (ell.continuous.comp continuous_subtype_val) continuous_const
  have hc : ContinuousOn (fun v : {v : E // v ≠ 0} => affineRayRep ell v.val) S :=
    (projective_affine_transition_smooth ell).continuousOn.comp
      continuous_subtype_val.continuousOn (fun _ hv => hv)
  exact hc.isOpen_inter_preimage hs ht

/-- Genuine homeomorphism between each open chart domain and its
affine hyperplane. This equips the algebraic chart with topology.
It is not yet a bundled ChartedSpace on a fixed model vector space. -/
noncomputable def projectiveAffineHomeomorph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (ell : E →L[ℂ] ℂ) :
    {p : Projectivization ℂ E // ell p.rep ≠ 0} ≃ₜ {v : E // ell v = 1} where
  toEquiv := projectiveAffineEquiv ell
  continuous_toFun := by
    have h := continuousOn_iff_continuous_restrict.mp
      (projective_affine_rep_continuousOn ell)
    exact h.subtype_mk _
  continuous_invFun := by
    let f : {v : E // ell v = 1} → {v : E // v ≠ 0} := fun v => ⟨v.val, by
      intro hz
      have he := v.property
      simp [hz] at he⟩
    have hf : Continuous f := continuous_subtype_val.subtype_mk _
    have h := (projective_ray_quotient_map (E := E)).continuous.comp hf
    exact h.subtype_mk _

/-- Normalize a nonzero multiplet without selecting any individual
component or taking its logarithm. -/
noncomputable def rayNormalize {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (z : E) : E := ‖z‖⁻¹ • z

theorem ray_normalize_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (z : E) (hz : z ≠ 0) :
    ‖rayNormalize z‖ = 1 := by
  unfold rayNormalize
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

theorem ray_normalize_unit {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (z : E) (hz : z ≠ 0) :
    inner ℂ (rayNormalize z) (rayNormalize z) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, ray_normalize_norm z hz]
  norm_num

/-- Normalization is smooth wherever the total multiplet is nonzero.
Individual zero components are explicitly allowed. -/
theorem ray_normalize_smooth {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (z : V → E) (x : V) (k : WithTop ℕ∞)
    (hz : ContDiffAt ℝ k z x) (h0 : z x ≠ 0) :
    ContDiffAt ℝ k (fun y => rayNormalize (z y)) x := by
  unfold rayNormalize
  exact ((hz.norm ℂ h0).inv (norm_ne_zero_iff.mpr h0)).smul hz

/-- Actual ray normalization produces a representative of the same
projective point without division by any component. -/
theorem ray_normalize_same_ray {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (z : E) (hz : z ≠ 0) (hn : rayNormalize z ≠ 0) :
    Projectivization.mk ℂ (rayNormalize z) hn = Projectivization.mk ℂ z hz := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨((‖z‖⁻¹ : ℝ):ℂ), ?_⟩
  change rayNormalize z = ((‖z‖⁻¹ : ℝ):ℂ) • z
  rw [← Complex.coe_smul]
  rfl

/-- C² multiplets induce a continuous projective tensor at every
point with nonzero total norm, even at component zeros. -/
theorem zero_safe_projective_tensor_continuous {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E]
    (z : V → E) (x u v : V)
    (hz : ContDiffAt ℝ 2 z x) (h0 : z x ≠ 0) :
    ContinuousAt (fun y => projectiveTensor (fun t => rayNormalize (z t)) y u v) x := by
  let n : V → E := fun y => rayNormalize (z y)
  have hn : ContDiffAt ℝ 2 n x := ray_normalize_smooth z x 2 hz h0
  have hn0 : ContinuousAt n x := hn.continuousAt
  have hd : ContDiffAt ℝ 1 (fderiv ℝ n) x := hn.fderiv_right (by norm_num)
  have hu : ContinuousAt (fun y => fderiv ℝ n y u) x :=
    (hd.clm_apply contDiffAt_const).continuousAt
  have hv : ContinuousAt (fun y => fderiv ℝ n y v) x :=
    (hd.clm_apply contDiffAt_const).continuousAt
  change ContinuousAt (fun y => projectiveTensor n y u v) x
  unfold projectiveTensor projectivePullback horizontalProjection
  fun_prop

/-- Polar derivative from actual smooth positive probability and
phase functions, not an assumed complex slope. A normalized
component is exp(½ log r + i θ) wherever r > 0. -/
theorem polar_component_fderiv {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r theta : V → ℝ) (dr dt : V →L[ℝ] ℝ) (x u : V)
    (hr : HasFDerivAt r dr x) (ht : HasFDerivAt theta dt x)
    (hpos : 0 < r x) :
    fderiv ℝ (fun y => Complex.exp
      (((1/2:ℝ)*Real.log (r y):ℝ) + Complex.I*(theta y:ℂ))) x u =
      Complex.exp (((1/2:ℝ)*Real.log (r x):ℝ) + Complex.I*(theta x:ℂ)) *
        ((((1/2:ℝ)*((r x)⁻¹*dr u):ℝ):ℂ)+Complex.I*(dt u:ℂ)) := by
  have ha := (hr.log hpos.ne').const_mul (1/2:ℝ)
  have ha' := Complex.ofRealCLM.hasFDerivAt.comp x ha
  have ht' := Complex.ofRealCLM.hasFDerivAt.comp x ht
  have hd := (ha'.add (ht'.const_mul Complex.I)).cexp
  have he : HasFDerivAt
      (fun y => Complex.exp (((1/2:ℝ)*Real.log (r y):ℝ) + Complex.I*(theta y:ℂ)))
      _ x := hd
  rw [he.fderiv]
  rfl

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
#print axioms MicroMacro.finite_complex_gram_bound
#print axioms MicroMacro.finite_curvature_bound
#print axioms MicroMacro.normalized_weight_derivative
#print axioms MicroMacro.flat_scalar_divergence_jet
#print axioms MicroMacro.flat_scalar_on_shell_jet
#print axioms MicroMacro.centered_cross_shift
#print axioms MicroMacro.phase_curvature_jet
#print axioms MicroMacro.finite_real_gram_bound
#print axioms MicroMacro.ensemble_energy_flux_causal
#print axioms MicroMacro.ensemble_normalized_weight_derivative
#print axioms MicroMacro.phase_curvature_line_derivative
#print axioms MicroMacro.normalized_log_score
#print axioms MicroMacro.covariant_scalar_divergence_jet
#print axioms MicroMacro.covariant_ensemble_on_shell_jet
#print axioms MicroMacro.affine_plane_wave_derivatives
#print axioms MicroMacro.plane_wave_mass_shell
#print axioms MicroMacro.plane_wave_kinetic_component
#print axioms MicroMacro.counterpropagating_stress_witness
#print axioms MicroMacro.finite_heat_trace_tail
#print axioms MicroMacro.laplace_remainder_interval
#print axioms MicroMacro.spectral_log_majorant
#print axioms MicroMacro.infinite_scaled_remainder_bound
#print axioms MicroMacro.infinite_laplace_rescale
#print axioms MicroMacro.infinite_laplace_rh_rate
#print axioms MicroMacro.exponential_tail_integral
#print axioms MicroMacro.countable_heat_trace_integral
#print axioms MicroMacro.prime_heat_trace_staircase
#print axioms MicroMacro.horizontal_projection_orthogonal
#print axioms MicroMacro.horizontal_projection_vertical_invariance
#print axioms MicroMacro.conservation_exchange_linear
#print axioms MicroMacro.prime_staircase_count
#print axioms MicroMacro.prime_heat_trace_counting
#print axioms MicroMacro.smooth_heat_trace_counting
#print axioms MicroMacro.prime_heat_trace_conditional_rh
#print axioms MicroMacro.unit_phase_inner
#print axioms MicroMacro.horizontal_projection_phase
#print axioms MicroMacro.projective_pullback_gauge
#print axioms MicroMacro.normalized_curve_tangent
#print axioms MicroMacro.projective_curve_gauge
#print axioms MicroMacro.covector_outer_connection_rule
#print axioms MicroMacro.covector_outer_actual_derivative
#print axioms MicroMacro.metric_scalar_connection_rule
#print axioms MicroMacro.tensor_connection_linear_combination
#print axioms MicroMacro.stress_actual_connection_derivative
#print axioms MicroMacro.counting_zero_below_two
#print axioms MicroMacro.log_count_nonnegative
#print axioms MicroMacro.log_count_monotone
#print axioms MicroMacro.eventual_prime_bound_global
#print axioms MicroMacro.prime_heat_trace_eventual_rh
#print axioms MicroMacro.connection_contract_first
#print axioms MicroMacro.connection_contract_second
#print axioms MicroMacro.covariant_kinetic_trace_jet
#print axioms MicroMacro.covariant_trace_actual_derivative
#print axioms MicroMacro.symmetric_kinetic_trace
#print axioms MicroMacro.inverse_metric_contraction
#print axioms MicroMacro.local_metric_stress_divergence
#print axioms MicroMacro.local_metric_stress_on_shell
#print axioms MicroMacro.projective_tensor_gauge_fderiv
#print axioms MicroMacro.projective_tensor_reparam
#print axioms MicroMacro.projective_tensor_hermitian
#print axioms MicroMacro.projective_tensor_nonnegative
#print axioms MicroMacro.normalized_fderiv_vertical_real_zero
#print axioms MicroMacro.horizontal_gram_subtract
#print axioms MicroMacro.horizontal_gram_imaginary
#print axioms MicroMacro.berry_curvature_fderiv
#print axioms MicroMacro.berry_curvature_C2
#print axioms MicroMacro.finite_inner_re_im
#print axioms MicroMacro.finite_horizontal_covariance
#print axioms MicroMacro.finite_projected_component
#print axioms MicroMacro.projective_tensor_finite_covariance
#print axioms MicroMacro.finite_berry_mean
#print axioms MicroMacro.finite_normalized_berry_mean
#print axioms MicroMacro.projective_tensor_normalized_covariance
#print axioms MicroMacro.quotient_jet_tensor_rep
#print axioms MicroMacro.affine_ray_rep_scale
#print axioms MicroMacro.projective_affine_rep_mk
#print axioms MicroMacro.affine_rep_hyperplane
#print axioms MicroMacro.affine_rep_nonzero
#print axioms MicroMacro.affine_rep_same_projective_point
#print axioms MicroMacro.affine_rep_fixed_on_hyperplane
#print axioms MicroMacro.projective_affine_transition_smooth
#print axioms MicroMacro.projective_affine_transition_cocycle
#print axioms MicroMacro.normalized_same_projective_ray
#print axioms MicroMacro.projective_tensor_same_ray_lifts
#print axioms MicroMacro.horizontalProjection
#print axioms MicroMacro.strictPrimeCount
#print axioms MicroMacro.logCount
#print axioms MicroMacro.projectivePullback
#print axioms MicroMacro.covectorConnection
#print axioms MicroMacro.tensorConnection
#print axioms MicroMacro.projectiveTensor
#print axioms MicroMacro.ProjectiveJet
#print axioms MicroMacro.projectiveJetRel
#print axioms MicroMacro.quotientJetTensor
#print axioms MicroMacro.affineRayRep
#print axioms MicroMacro.projectiveAffineRep
#print axioms MicroMacro.projectiveAffineEquiv
#print axioms MicroMacro.projective_ray_quotient_map
#print axioms MicroMacro.projective_chart_nonvanishing_mk
#print axioms MicroMacro.projective_chart_domain_open
#print axioms MicroMacro.projective_chart_cover
#print axioms MicroMacro.projective_affine_rep_continuousOn
#print axioms MicroMacro.ray_normalize_norm
#print axioms MicroMacro.ray_normalize_unit
#print axioms MicroMacro.ray_normalize_smooth
#print axioms MicroMacro.ray_normalize_same_ray
#print axioms MicroMacro.zero_safe_projective_tensor_continuous
#print axioms MicroMacro.polar_component_fderiv
#print axioms MicroMacro.projectiveRayTopology
#print axioms MicroMacro.projectiveAffineHomeomorph
#print axioms MicroMacro.rayNormalize
