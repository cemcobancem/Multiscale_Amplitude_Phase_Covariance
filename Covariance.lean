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
    convert h.exp.neg using 1 <;> ring
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
