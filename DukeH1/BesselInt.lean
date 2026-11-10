/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.Lipschitz
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The Bessel-type integral

For real `k > 1`, `A ≥ 0`, `n > 0`, `y > 0`:
`∫_ℝ (x + iy)^{−k} e^{−2πinx} e^{−2πiA/(x+iy)} dx
   = (−2πi)^k n^{k−1} e^{−2πny} ∑_j (−4π²An)^j / (j! Γ(k + j))`
(`bessel_integral`), by expanding the second exponential and applying the Lipschitz formula.
-/

@[expose] public section

namespace ThreeSquares.Lip

open Complex MeasureTheory Set Filter Topology

open scoped Real Nat

/-- The Bessel-type series `∑_j (−X)^j / (j! Γ(k + j))`. -/
noncomputable def besS (k : ℝ) (X : ℂ) : ℂ := ∑' j : ℕ, (-X) ^ j / ((j ! : ℂ) * Gamma (k + j))

theorem norm_cpow_neg_real {z : ℂ} (hz : z ≠ 0) (k : ℝ) : ‖z ^ (-(k : ℂ))‖ = ‖z‖ ^ (-k) := by
  rw [norm_cpow_of_ne_zero hz]; simp

theorem norm_z_ge {x y : ℝ} (hy : 0 < y) : y ≤ ‖(x : ℂ) + y * I‖ := by
  have := Complex.abs_im_le_norm ((x : ℂ) + y * I)
  simpa [abs_of_pos hy] using this

theorem z_ne_zero {x y : ℝ} (hy : 0 < y) : (x : ℂ) + y * I ≠ 0 := fun h => by
  have := congrArg Complex.im h; simp at this; linarith

/-- `∫ |x + iy|^{−k} dx < ∞` for `k > 1`. -/
theorem integrable_norm_rpow {k y : ℝ} (hk : 1 < k) (hy : 0 < y) :
    Integrable fun x : ℝ => ‖(x : ℂ) + y * I‖ ^ (-k) := by
  set m : ℝ := min 1 (y ^ 2)
  have hm : 0 < m := lt_min one_pos (by positivity)
  have hint := (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := k)
    (by simp; linarith)).const_mul (m ^ (-(k / 2)))
  refine hint.mono' ((by fun_prop : Measurable fun x : ℝ => ‖(x : ℂ) + y * I‖).pow_const _).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hn2 : ‖(x : ℂ) + y * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have hz : 0 < ‖(x : ℂ) + y * I‖ := norm_pos_iff.mpr (z_ne_zero hy)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have e : ‖(x : ℂ) + y * I‖ ^ (-k) = (‖(x : ℂ) + y * I‖ ^ 2) ^ (-(k / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]; congr 1; push_cast; ring
  rw [e, hn2, neg_div, ← Real.mul_rpow hm.le (by positivity)]
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  rw [Real.norm_eq_abs, sq_abs]
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmy : m ≤ y ^ 2 := min_le_right _ _
  nlinarith [sq_nonneg x]

theorem bessel_integral {k : ℝ} (hk : 1 < k) {A : ℝ} (hA : 0 ≤ A) {n : ℝ} (hn : 0 < n) {y : ℝ}
    (hy : 0 < y) :
    ∫ x : ℝ, ((x : ℂ) + y * I) ^ (-(k : ℂ)) * cexp (-(2 * π * I * n * x)) *
        cexp (-(2 * π * I * A / ((x : ℂ) + y * I))) =
      (-(2 * π * I)) ^ (k : ℂ) * (n : ℂ) ^ ((k : ℂ) - 1) * Real.exp (-(2 * π * n * y)) *
        besS k (4 * π ^ 2 * A * n) := by
  set z : ℝ → ℂ := fun x => (x : ℂ) + y * I
  have hz0 : ∀ x, z x ≠ 0 := fun x => z_ne_zero hy
  set f : ℕ → ℝ → ℂ := fun j x => z x ^ (-(k : ℂ)) * cexp (-(2 * π * I * n * x)) *
    ((-(2 * π * I * A)) ^ j / (j ! : ℂ) * (z x ^ j)⁻¹)
  -- pointwise expansion
  have hpt : ∀ x, z x ^ (-(k : ℂ)) * cexp (-(2 * π * I * n * x)) *
      cexp (-(2 * π * I * A / z x)) = ∑' j, f j x := by
    intro x
    have hs := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (-(2 * π * I * A / z x))
    rw [← Complex.exp_eq_exp_ℂ] at hs
    rw [← hs.tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [f]
    rw [← neg_div, div_pow]
    ring
  -- each term
  have hterm : ∀ j : ℕ, ∫ x, f j x = (-(2 * π * I * A)) ^ j / (j ! : ℂ) *
      ((-(2 * π * I)) ^ ((k : ℂ) + j) * (n : ℂ) ^ ((k : ℂ) + j - 1) * Real.exp (-(2 * π * n * y)) /
        Gamma ((k : ℂ) + j)) := by
    intro j
    have hs : 1 < ((k : ℂ) + j).re := by simp; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
    rw [← lipschitz hs hy hn, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [f]
    rw [neg_add, cpow_add _ _ (hz0 x), cpow_neg _ (j : ℂ), cpow_natCast]
    ring
  -- summability of the integrals of norms
  have hbound : ∀ j x, ‖f j x‖ ≤ (2 * π * A / y) ^ j / (j ! : ℝ) * ‖z x‖ ^ (-k) := by
    intro j x
    have hzx : y ≤ ‖z x‖ := norm_z_ge hy
    have hzp : 0 < ‖z x‖ := lt_of_lt_of_le hy hzx
    simp only [f]
    rw [norm_mul, norm_mul, norm_mul, norm_div, norm_inv, norm_pow, norm_pow, norm_cpow_neg_real
      (hz0 x), Complex.norm_exp, norm_neg, Complex.norm_natCast]
    have e1 : (-(2 * π * I * n * x)).re = 0 := by simp
    have e2 : ‖2 * π * I * (A : ℂ)‖ = 2 * π * A := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I, Complex.norm_two,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        abs_of_nonneg hA]; ring
    rw [e1, Real.exp_zero, mul_one, e2]
    have hj : (‖z x‖ ^ j)⁻¹ ≤ (y ^ j)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ hy.le hzx j)
    calc ‖z x‖ ^ (-k) * ((2 * π * A) ^ j / (j ! : ℝ) * (‖z x‖ ^ j)⁻¹)
        ≤ ‖z x‖ ^ (-k) * ((2 * π * A) ^ j / (j ! : ℝ) * (y ^ j)⁻¹) := by gcongr
      _ = (2 * π * A / y) ^ j / (j ! : ℝ) * ‖z x‖ ^ (-k) := by rw [div_pow]; field_simp
  have hint := integrable_norm_rpow hk hy
  have hmeas : ∀ j, AEStronglyMeasurable (f j) volume := fun j => by
    refine Continuous.aestronglyMeasurable ?_
    simp only [f, z]
    refine Continuous.mul (Continuous.mul ?_ (by fun_prop)) (continuous_const.mul ?_)
    · exact Continuous.cpow (by fun_prop) continuous_const fun x => by
        rw [Complex.mem_slitPlane_iff]; right; simp; exact hy.ne'
    · exact ((by fun_prop : Continuous fun x : ℝ => ((x : ℂ) + y * I) ^ j)).inv₀
        fun x => pow_ne_zero _ (z_ne_zero hy)
  have hsum : ∑' j, ∫⁻ x, ‖f j x‖ₑ ≠ ⊤ := by
    have hle : ∀ j, ∫⁻ x, ‖f j x‖ₑ ≤ ENNReal.ofReal ((2 * π * A / y) ^ j / (j ! : ℝ)) *
        ∫⁻ x, ‖‖z x‖ ^ (-k)‖ₑ := by
      intro j
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun x => ?_
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (by positivity),
        Real.norm_eq_abs (‖z x‖ ^ (-k)), abs_of_nonneg (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hbound j x)
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_mul_right]
    refine ENNReal.mul_ne_top ?_ hint.2.ne
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
      (Real.summable_pow_div_factorial _)]
    exact ENNReal.ofReal_ne_top
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_tsum hmeas hsum]
  simp_rw [hterm]
  unfold besS
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  have hc : (-(2 * π * I)) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hG : Gamma ((k : ℂ) + j) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; positivity)
  rw [cpow_add _ _ hc, cpow_natCast, show (k : ℂ) + j - 1 = ((k : ℂ) - 1) + j by ring,
    cpow_add _ _ hn0, cpow_natCast]
  have hI : (-(2 * π * I)) ^ j * (-(2 * π * I * A)) ^ j * (n : ℂ) ^ j =
      (-(4 * π ^ 2 * A * n)) ^ j := by
    rw [← mul_pow, ← mul_pow]; congr 1; ring_nf; rw [Complex.I_sq]; ring
  rw [← hI]
  field_simp

end ThreeSquares.Lip
