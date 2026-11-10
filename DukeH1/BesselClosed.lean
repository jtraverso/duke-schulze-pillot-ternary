/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.BesselInt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Bessel functions of half-integral order are elementary

`besS k X = ∑_j (−X)^j / (j! Γ(k + j))`. For `k = m + 1/2`:
* `besS_half`: `S_{1/2}(X) = cos(2√X)/√π`; `besS_three_half`: `S_{3/2}(X) = sin(2√X)/(√X √π)`;
* `besS_rec`: `X S_{k+1}(X) = (k − 1) S_k(X) − S_{k−1}(X)`;
* `besS_closed`: `S_{m+1/2}(X) = w^m (e^{2i√X} p_m(w) + e^{−2i√X} q_m(w))`, `w = 1/√X`, for polynomials
  `p_m, q_m`.
-/

@[expose] public section

namespace ThreeSquares.Lip

open Complex Filter Topology Polynomial

open scoped Real Nat

/-! ### Summability and the recurrence -/

theorem Gamma_ne_zero_of_pos {k : ℝ} (hk : 0 < k) (j : ℕ) : Gamma ((k : ℂ) + j) ≠ 0 :=
  Gamma_ne_zero_of_re_pos (by simp; positivity)

theorem summable_besS {k : ℝ} (hk : 0 < k) (X : ℂ) :
    Summable fun j : ℕ => (-X) ^ j / ((j ! : ℂ) * Gamma (k + j)) := by
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  have hev : ∀ᶠ j : ℕ in atTop, 2 * ‖X‖ ≤ (j + 1 : ℝ) * (k + j) := by
    have h := tendsto_natCast_atTop_atTop (R := ℝ)
    filter_upwards [h.eventually_ge_atTop (2 * ‖X‖)] with j hj
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  filter_upwards [hev] with j hj
  have hG := Gamma_ne_zero_of_pos hk j
  have hrec : Gamma ((k : ℂ) + ↑(j + 1)) = ((k : ℂ) + j) * Gamma ((k : ℂ) + j) := by
    rw [show (k : ℂ) + ↑(j + 1) = ((k : ℂ) + j) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ (by intro h; have := congrArg Complex.re h; simp at this; linarith)]
  rw [hrec, Nat.factorial_succ, pow_succ, norm_div, norm_div, norm_mul, norm_mul, norm_mul,
    norm_mul, norm_neg, Nat.cast_mul, norm_mul]
  have hkj : ‖(k : ℂ) + j‖ = k + j := by
    rw [show (k : ℂ) + j = ((k + j : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hj1 : ‖((j + 1 : ℕ) : ℂ)‖ = j + 1 := by rw [Complex.norm_natCast]; push_cast; ring
  rw [hkj, hj1]
  have hpos : 0 < ‖(j ! : ℂ)‖ * ‖Gamma ((k : ℂ) + j)‖ := by
    have : (j ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
    positivity
  have hA : 0 < (j + 1 : ℝ) * (k + j) := by positivity
  have hf0 : 0 < ‖(j ! : ℂ)‖ := by
    have : (j ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
    positivity
  have hG0 : 0 < ‖Gamma ((k : ℂ) + j)‖ := norm_pos_iff.mpr hG
  calc ‖(-X) ^ j‖ * ‖X‖ / ((j + 1 : ℝ) * ‖(j ! : ℂ)‖ * ((k + j) * ‖Gamma ((k : ℂ) + j)‖))
      = (‖(-X) ^ j‖ / (‖(j ! : ℂ)‖ * ‖Gamma ((k : ℂ) + j)‖)) * (‖X‖ / ((j + 1 : ℝ) * (k + j))) := by
        field_simp
    _ ≤ (‖(-X) ^ j‖ / (‖(j ! : ℂ)‖ * ‖Gamma ((k : ℂ) + j)‖)) * (1 / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_iff₀ hA]; linarith
    _ = _ := by ring

/-- **`X S_{k+1}(X) = (k − 1) S_k(X) − S_{k−1}(X)`** for `k > 1`. -/
theorem besS_rec {k : ℝ} (hk : 1 < k) (X : ℂ) :
    X * besS (k + 1) X = (k - 1) * besS k X - besS (k - 1) X := by
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k - 1 := by linarith
  have hs1 := summable_besS (k := k + 1) (by linarith) X
  have hs0 := summable_besS hk0 X
  have hsm := summable_besS hk1 X
  unfold besS
  rw [← tsum_mul_left, ← tsum_mul_left, ← hs0.mul_left _ |>.tsum_sub hsm]
  -- shift the right-hand side by one
  have hR : Summable fun j : ℕ => (k - 1 : ℂ) * ((-X) ^ j / ((j ! : ℂ) * Gamma (k + j))) -
      (-X) ^ j / ((j ! : ℂ) * Gamma ((k - 1 : ℝ) + j)) := (hs0.mul_left _).sub hsm
  rw [hR.tsum_eq_zero_add]
  have h0 : (k - 1 : ℂ) * ((-X) ^ 0 / (((0 : ℕ) ! : ℂ) * Gamma (k + (0 : ℕ)))) -
      (-X) ^ 0 / (((0 : ℕ) ! : ℂ) * Gamma ((k - 1 : ℝ) + (0 : ℕ))) = 0 := by
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, add_zero]
    rw [show (k : ℂ) = ((k - 1 : ℝ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ (by intro h; have := congrArg Complex.re h; simp at this; linarith)]
    have : Gamma ((k - 1 : ℝ) : ℂ) ≠ 0 := by simpa using Gamma_ne_zero_of_pos hk1 0
    have hk1c : ((k - 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk1.ne'
    field_simp
    push_cast
    ring
  rw [h0, zero_add]
  refine tsum_congr fun j => ?_
  have hGk := Gamma_ne_zero_of_pos hk0 j
  have hGk1 := Gamma_ne_zero_of_pos hk1 (j + 1)
  have e1 : Gamma ((k : ℂ) + ↑(j + 1)) = ((k : ℂ) + j) * Gamma ((k : ℂ) + j) := by
    rw [show (k : ℂ) + ↑(j + 1) = ((k : ℂ) + j) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ (by intro h; have := congrArg Complex.re h; simp at this; linarith)]
  have e2 : Gamma (((k + 1 : ℝ) : ℂ) + j) = Gamma ((k : ℂ) + ↑(j + 1)) := by
    congr 1; push_cast; ring
  have e3 : Gamma (((k - 1 : ℝ) : ℂ) + ↑(j + 1)) = Gamma ((k : ℂ) + j) := by
    congr 1; push_cast; ring
  rw [e2, e3, e1, Nat.factorial_succ, pow_succ]
  have hkj : (k : ℂ) + j ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hf : (j ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  push_cast
  field_simp
  ring

/-! ### The base cases -/

theorem fact_mul_Gamma_half (j : ℕ) :
    (j ! : ℂ) * Gamma (((1 / 2 : ℝ) : ℂ) + j) = (2 * j)! * Real.sqrt π / 4 ^ j := by
  rw [show ((1 / 2 : ℝ) : ℂ) + j = ((j + 1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
    Real.Gamma_nat_add_half]
  have h1 : (2 * j)! = (2 * j)‼ * (2 * j - 1)‼ := by
    cases j with
    | zero => simp
    | succ j =>
      rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, Nat.factorial_eq_mul_doubleFactorial]
      simp
  rw [h1, Nat.doubleFactorial_two_mul]
  push_cast
  rw [show (4 : ℂ) ^ j = 2 ^ j * 2 ^ j by rw [← mul_pow]; norm_num]
  field_simp

theorem fact_mul_Gamma_three_half (j : ℕ) :
    (j ! : ℂ) * Gamma (((3 / 2 : ℝ) : ℂ) + j) = (2 * j + 1)! * Real.sqrt π / (2 * 4 ^ j) := by
  rw [show ((3 / 2 : ℝ) : ℂ) + j = ((j + 1 + 1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
    Real.Gamma_nat_add_one_add_half]
  rw [Nat.factorial_eq_mul_doubleFactorial, Nat.doubleFactorial_two_mul]
  push_cast
  rw [show (4 : ℂ) ^ j = 2 ^ j * 2 ^ j by rw [← mul_pow]; norm_num]
  field_simp
  ring

theorem besS_half (X : ℝ) (hX : 0 ≤ X) :
    besS (1 / 2) X = Complex.cos (2 * Real.sqrt X) / Real.sqrt π := by
  have hs := Complex.hasSum_cos (2 * Real.sqrt X)
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [eq_div_iff hπ, ← hs.tsum_eq, besS, ← tsum_mul_right]
  refine tsum_congr fun j => ?_
  have hsq : ((Real.sqrt X : ℂ)) ^ 2 = X := by rw [← Complex.ofReal_pow, Real.sq_sqrt hX]
  rw [fact_mul_Gamma_half, mul_pow, pow_mul, pow_mul, hsq]
  have hf : ((2 * j)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp
  rw [neg_pow]
  norm_num
  ring

theorem besS_three_half (X : ℝ) (hX : 0 < X) :
    besS (3 / 2) X = Complex.sin (2 * Real.sqrt X) / (Real.sqrt X * Real.sqrt π) := by
  have hs := Complex.hasSum_sin (2 * Real.sqrt X)
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hx : (Real.sqrt X : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hX).ne'
  rw [eq_div_iff (mul_ne_zero hx hπ), ← hs.tsum_eq, besS, ← tsum_mul_right]
  refine tsum_congr fun j => ?_
  have hsq : ((Real.sqrt X : ℂ)) ^ 2 = X := by rw [← Complex.ofReal_pow, Real.sq_sqrt hX.le]
  rw [fact_mul_Gamma_three_half, pow_succ, mul_pow, pow_mul, pow_mul, hsq]
  have hf : ((2 * j + 1)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp
  rw [neg_pow]
  norm_num
  ring

/-! ### The closed form -/

/-- `S_{m+1/2}(X) = w^m (e^{2i√X} p(w) + e^{−2i√X} q(w))` with `w = 1/√X`. -/
def BesForm (m : ℕ) (p q : ℂ[X]) : Prop :=
  ∀ X : ℝ, 0 < X → besS (m + 1 / 2) X = ((Real.sqrt X : ℂ)⁻¹) ^ m *
    (cexp (2 * I * Real.sqrt X) * p.eval ((Real.sqrt X : ℂ)⁻¹) +
      cexp (-(2 * I * Real.sqrt X)) * q.eval ((Real.sqrt X : ℂ)⁻¹))

theorem besForm_zero : BesForm 0 (C (1 / (2 * Real.sqrt π))) (C (1 / (2 * Real.sqrt π))) := by
  intro X hX
  have h := besS_half X hX.le
  simp only [Nat.cast_zero, zero_add, pow_zero, one_mul, eval_C] at h ⊢
  rw [h, Complex.cos]
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

theorem besForm_one : BesForm 1 (C (1 / (2 * I * Real.sqrt π))) (C (-(1 / (2 * I * Real.sqrt π)))) := by
  intro X hX
  have h := besS_three_half X hX
  rw [show ((1 : ℕ) : ℝ) + 1 / 2 = 3 / 2 by norm_num, h, Complex.sin]
  simp only [pow_one, eval_C]
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hx : (Real.sqrt X : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hX).ne'
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem besForm_succ {m : ℕ} (hm : 1 ≤ m) {p q p' q' : ℂ[X]} (h : BesForm m p q)
    (h' : BesForm (m - 1) p' q') :
    BesForm (m + 1) (C ((m : ℂ) - 1 / 2) * X * p - p') (C ((m : ℂ) - 1 / 2) * X * q - q') := by
  intro x hx
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hk : 1 < (m : ℝ) + 1 / 2 := by linarith
  have hr := besS_rec hk (x : ℂ)
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hs : (Real.sqrt x : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hx).ne'
  have hsq : (Real.sqrt x : ℂ) ^ 2 = x := by rw [← Complex.ofReal_pow, Real.sq_sqrt hx.le]
  rw [show ((m : ℝ) + 1 / 2 + 1) = ((m + 1 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
    show ((m : ℝ) + 1 / 2 - 1) = ((m - 1 : ℕ) : ℝ) + 1 / 2 by
      rw [Nat.cast_sub hm]; push_cast; ring, h x hx, h' x hx] at hr
  have e : besS (((m + 1 : ℕ) : ℝ) + 1 / 2) x = (x : ℂ)⁻¹ * (((((m : ℝ) + 1 / 2 : ℝ) : ℂ) - 1) *
      (((Real.sqrt x : ℂ)⁻¹) ^ m * (cexp (2 * I * Real.sqrt x) * p.eval ((Real.sqrt x : ℂ)⁻¹) +
        cexp (-(2 * I * Real.sqrt x)) * q.eval ((Real.sqrt x : ℂ)⁻¹))) -
      ((Real.sqrt x : ℂ)⁻¹) ^ (m - 1) * (cexp (2 * I * Real.sqrt x) * p'.eval ((Real.sqrt x : ℂ)⁻¹) +
        cexp (-(2 * I * Real.sqrt x)) * q'.eval ((Real.sqrt x : ℂ)⁻¹))) := by
    rw [← hr]; field_simp
  have hxw : (x : ℂ)⁻¹ = ((Real.sqrt x : ℂ)⁻¹) ^ 2 := by rw [inv_pow, hsq]
  rw [e, hxw]
  simp only [eval_sub, eval_mul, eval_C, eval_X]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [show m' + 1 - 1 = m' by omega]
  push_cast
  ring

/-- **`S_{m+1/2}` is elementary**: polynomials `p_m, q_m` with `BesForm m p_m q_m`. -/
theorem besS_closed (m : ℕ) : ∃ p q : ℂ[X], BesForm m p q := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => exact ⟨_, _, besForm_zero⟩
    | 1, _ => exact ⟨_, _, besForm_one⟩
    | m + 2, ih =>
      obtain ⟨p, q, h⟩ := ih (m + 1) (by omega)
      obtain ⟨p', q', h'⟩ := ih m (by omega)
      exact ⟨_, _, besForm_succ (m := m + 1) (by omega) h (by simpa using h')⟩

end ThreeSquares.Lip
