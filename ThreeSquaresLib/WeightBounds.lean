/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.CfacClosed
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Bounds for the Kloosterman weight

* `polyA`, `norm_eval_le`, `norm_eval_sub_le`: size and Lipschitz constant of a complex polynomial
  on `[0, S]`;
* `norm_e_sub_le`: `|e(x) − e(x')| ≤ 2π |x − x'|`;
* `norm_Kc_le`: `‖Kc‖ ≤ 2 n^{−1/2}`.
-/

@[expose] public section

namespace ThreeSquares.Poin

open Complex Polynomial ThreeSquares.Lip Finset

open scoped Real

/-- The sum of the absolute values of the coefficients. -/
noncomputable def polyA (p : ℂ[X]) : ℝ := ∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖

theorem polyA_nonneg (p : ℂ[X]) : 0 ≤ polyA p := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_eval_le (p : ℂ[X]) {S x : ℝ} (hx0 : 0 ≤ x) (hxS : x ≤ S) :
    ‖p.eval (x : ℂ)‖ ≤ polyA p * (1 + S) ^ p.natDegree := by
  rw [eval_eq_sum_range]
  refine (norm_sum_le _ _).trans ?_
  unfold polyA
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  calc x ^ i ≤ (1 + S) ^ i := pow_le_pow_left₀ hx0 (by linarith) i
    _ ≤ (1 + S) ^ p.natDegree := pow_le_pow_right₀ (by linarith) hi'

theorem norm_eval_sub_le (p : ℂ[X]) {S x x' : ℝ} (hx0 : 0 ≤ x) (hxS : x ≤ S) (hx0' : 0 ≤ x')
    (hxS' : x' ≤ S) :
    ‖p.eval (x' : ℂ) - p.eval (x : ℂ)‖ ≤ polyA p * p.natDegree * (1 + S) ^ p.natDegree * |x' - x| := by
  rw [eval_eq_sum_range, eval_eq_sum_range, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  unfold polyA
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← mul_sub, norm_mul]
  have e : ((x' : ℂ)) ^ i - ((x : ℂ)) ^ i = ((x' ^ i - x ^ i : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  have h1 := abs_pow_sub_pow_le x' x i
  have hmax : max |x'| |x| ≤ 1 + S := by
    rw [abs_of_nonneg hx0', abs_of_nonneg hx0]; exact max_le (by linarith) (by linarith)
  have h2 : max |x'| |x| ^ (i - 1) ≤ (1 + S) ^ p.natDegree := by
    calc max |x'| |x| ^ (i - 1) ≤ (1 + S) ^ (i - 1) := pow_le_pow_left₀ (by positivity) hmax _
      _ ≤ (1 + S) ^ p.natDegree := pow_le_pow_right₀ (by linarith) (by omega)
  have h3 : (i : ℝ) ≤ p.natDegree := by exact_mod_cast hi'
  calc ‖p.coeff i‖ * |x' ^ i - x ^ i| ≤ ‖p.coeff i‖ * (|x' - x| * i * max |x'| |x| ^ (i - 1)) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ ‖p.coeff i‖ * (|x' - x| * p.natDegree * (1 + S) ^ p.natDegree) := by
        gcongr
    _ = _ := by ring

theorem norm_e_sub_le (x x' : ℝ) :
    ‖cexp (2 * π * Complex.I * x') - cexp (2 * π * Complex.I * x)‖ ≤ 2 * π * |x' - x| := by
  have e : cexp (2 * π * Complex.I * x') - cexp (2 * π * Complex.I * x) =
      cexp (2 * π * Complex.I * x) * (cexp (Complex.I * ((2 * π * (x' - x) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; congr 2; push_cast; ring
  rw [e, norm_mul]
  have h1 : ‖cexp (2 * π * Complex.I * x)‖ = 1 := by
    rw [show 2 * (π : ℂ) * Complex.I * x = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [h1, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]

theorem norm_Kc_le (ℓ n : ℕ) (hn : 0 < n) : ‖Kc ℓ n‖ ≤ 2 * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold Kc
  have hz : (-(2 * π * Complex.I)) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hn0 : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnR.ne'
  rw [norm_div, norm_mul, norm_mul, norm_cpow_of_ne_zero hz, norm_cpow_of_ne_zero hn0, norm_pow]
  have h2 : ‖(-(2 * π * Complex.I))‖ = 2 * π := by
    rw [norm_neg, norm_mul, Complex.norm_I, mul_one, norm_mul, Complex.norm_real, Complex.norm_two,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have h3 : ‖(1 + Complex.I)‖ = Real.sqrt 2 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]; simp; norm_num
  rw [h2, h3, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnR, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π * n)]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, Real.exp_zero, div_one, Complex.sub_re,
    Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  -- `(2π)^k n^{k-1} / (√2 (2πn)^{ℓ+1}) = √π n^{-1/2}`
  have hk : kw ℓ = (ℓ + 1 : ℕ) + 1 / 2 := by unfold kw; push_cast; ring
  rw [hk]
  have hπ : (0 : ℝ) < 2 * π := by positivity
  rw [Real.rpow_add hπ, Real.rpow_natCast, show ((ℓ + 1 : ℕ) : ℝ) + 1 / 2 - 1 = (ℓ : ℝ) + 1 / 2 by
    push_cast; ring, Real.rpow_add hnR, Real.rpow_natCast, mul_pow]
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hpi : (2 * π) ^ (1 / 2 : ℝ) ≤ 2 * Real.sqrt 2 := by
    rw [← Real.sqrt_eq_rpow, show (2 : ℝ) * Real.sqrt 2 = Real.sqrt 8 by
      rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_le_four])
  set a := (n : ℝ) ^ (1 / 2 : ℝ) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hnR _
  have haa : a * a = n := by rw [ha, ← Real.rpow_add hnR]; norm_num
  have hneg : (n : ℝ) ^ (-(1 / 2 : ℝ)) = a⁻¹ := Real.rpow_neg hnR.le _
  rw [hneg, pow_succ]
  have hA : (0 : ℝ) < (2 * π) ^ (ℓ + 1) := pow_pos hπ _
  have hN : (0 : ℝ) < (n : ℝ) ^ ℓ := pow_pos hnR _
  calc _ = (2 * π) ^ (1 / 2 : ℝ) / (Real.sqrt 2 * a) := by
        rw [← haa]; field_simp; ring
    _ ≤ 2 * a⁻¹ := by
        rw [div_le_iff₀ (by positivity)]
        calc (2 * π) ^ (1 / 2 : ℝ) ≤ 2 * Real.sqrt 2 := hpi
          _ = 2 * a⁻¹ * (Real.sqrt 2 * a) := by field_simp

end ThreeSquares.Poin
