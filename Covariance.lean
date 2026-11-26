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
          rfl
        _ = _ := by ring
    rw [he] at hn
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hn hp)

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
    field_simp <;> ring
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
