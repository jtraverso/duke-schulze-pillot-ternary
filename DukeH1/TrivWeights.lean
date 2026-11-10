/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.TrivArith
public import DukeH1.WeightSmooth

/-!
# The weight `cfac` outside the critical range

* `norm_cfac_low`: `c ‖cfac(c)‖ ≤ ‖Kc‖ (A(p) 2^{deg p} + A(q) 2^{deg q})` for `c ≤ 2πn` (closed form);
* `norm_cfac_high`: `‖cfac(c)‖ ≤ cH · c^{−k−1/2}` for `c ≥ n`, `cH = |(−2πi)^k| |n^{k−1}| e^{4π²}` (series).
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares.Poin

open Complex Polynomial ThreeSquares.Lip

open scoped Real

theorem norm_cfac_low (ℓ n : ℕ) (hn : 0 < n) {p q : ℂ[X]} (hpq : BesForm (ℓ + 1) p q) (c : ℕ) (hc : 0 < c)
    (hcn : (c : ℝ) ≤ 2 * π * n) :
    (c : ℝ) * ‖cfac ℓ n c‖ ≤
      ‖Kc ℓ n‖ * (polyA p * (1 + 1) ^ p.natDegree + polyA q * (1 + 1) ^ q.natDegree) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 ≤ (c : ℝ) / (2 * π * n) := by positivity
  have hx1 : (c : ℝ) / (2 * π * n) ≤ 1 := by rw [div_le_one (by positivity)]; exact hcn
  have h := congrArg norm (cfac_closed ℓ n hn hpq c hc)
  rw [norm_mul, Complex.norm_natCast] at h
  rw [h, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have e1 : (2 * π * Complex.I * (2 * n / c) : ℂ) = ((2 * π * (2 * n / c) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have e2 : (-(2 * π * Complex.I * (2 * n / c)) : ℂ) = ((-(2 * π * (2 * n / c)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, e1, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact norm_eval_le p hx0 hx1
  · rw [norm_mul, e2, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact norm_eval_le q hx0 hx1

/-- The constant `|(−2πi)^k| |n^{k−1}| e^{4π²}`. -/
noncomputable def cH (ℓ n : ℕ) : ℝ :=
  ‖(-(2 * π * Complex.I)) ^ (kw ℓ : ℂ)‖ * ‖((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1)‖ * Real.exp (4 * π ^ 2)

theorem cH_nonneg (ℓ n : ℕ) : 0 ≤ cH ℓ n := by unfold cH; positivity

theorem norm_cfac_high (ℓ n : ℕ) (hℓ : 1 ≤ ℓ) {c : ℕ} (hc : 0 < c) (hnc : n ≤ c) :
    ‖cfac ℓ n c‖ ≤ cH ℓ n * (c : ℝ) ^ (-(kw ℓ) - 1 / 2) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hk2 : 2 ≤ kw ℓ := by
    unfold kw; have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hX : (0 : ℝ) ≤ 4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n := by positivity
  have hX' : 4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n ≤ 4 * π ^ 2 := by
    have hnc' : (n : ℝ) ≤ c := by exact_mod_cast hnc
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : (n : ℝ) / (c : ℝ) ^ 2 * n ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]
      nlinarith
    have hpi : 0 ≤ 4 * π ^ 2 := by positivity
    calc 4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n = (4 * π ^ 2) * ((n : ℝ) / (c : ℝ) ^ 2 * n) := by ring
      _ ≤ (4 * π ^ 2) * 1 := mul_le_mul_of_nonneg_left h1 hpi
      _ = 4 * π ^ 2 := by ring
  have hb := besS_norm_le hk2 hX
  have hb' : ‖besS (kw ℓ) ((4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n : ℝ) : ℂ)‖ ≤
      Real.exp (4 * π ^ 2) := hb.trans (Real.exp_le_exp.mpr hX')
  have h1i : (1 : ℝ) ≤ ‖(1 + Complex.I : ℂ)‖ := by
    rw [Complex.norm_def, Complex.normSq_apply]; simp
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.mpr hcR
  unfold cfac cH
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsq, Complex.norm_cpow_eq_rpow_re_of_pos hcR]
  simp only [Complex.neg_re, Complex.ofReal_re]
  have hcs : (c : ℝ) ^ (-(kw ℓ) - 1 / 2) = (c : ℝ) ^ (-(kw ℓ)) / Real.sqrt c := by
    rw [Real.rpow_sub hcR, Real.sqrt_eq_rpow]
  rw [hcs]
  have e : (4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n : ℂ) =
      ((4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  rw [div_le_iff₀ (by positivity)]
  calc ‖(-(2 * π * Complex.I)) ^ (kw ℓ : ℂ)‖ * ‖((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1)‖ *
        (c : ℝ) ^ (-kw ℓ) * ‖besS (kw ℓ) ((4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n : ℝ) : ℂ)‖
      ≤ ‖(-(2 * π * Complex.I)) ^ (kw ℓ : ℂ)‖ * ‖((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1)‖ *
        (c : ℝ) ^ (-kw ℓ) * Real.exp (4 * π ^ 2) := by gcongr
    _ ≤ ‖(-(2 * π * Complex.I)) ^ (kw ℓ : ℂ)‖ * ‖((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1)‖ *
          Real.exp (4 * π ^ 2) * ((c : ℝ) ^ (-kw ℓ) / Real.sqrt c) *
          (‖(1 + Complex.I : ℂ)‖ * Real.sqrt c) := by
        rw [show ‖(-(2 * π * Complex.I)) ^ (kw ℓ : ℂ)‖ * ‖((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1)‖ *
          Real.exp (4 * π ^ 2) * ((c : ℝ) ^ (-kw ℓ) / Real.sqrt c) *
          (‖(1 + Complex.I : ℂ)‖ * Real.sqrt c) = ‖(-(2 * π * Complex.I)) ^ (kw ℓ : ℂ)‖ *
          ‖((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1)‖ * (c : ℝ) ^ (-kw ℓ) * Real.exp (4 * π ^ 2) *
          ‖(1 + Complex.I : ℂ)‖ by field_simp]
        exact le_mul_of_one_le_right (by positivity) h1i

end ThreeSquares.Poin
