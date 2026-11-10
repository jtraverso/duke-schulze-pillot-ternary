/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.ThetaHarm

/-!
# The isotropic theta series at a rational cusp

For `c ≥ 1`, `a ∈ ℤ`, `Im w > 0` and `u` isotropic,
`θ_{u,ℓ}(a/c + w) = (−2iwc²)^{−3/2} ∑_{m ∈ ℤ³} G(a,m₀;c) G(a,m₁;c) G(a,m₂;c) (u·m/(2wc))^ℓ
  e(−|m|²/(4wc²))` (`theta3_rat`). For `ℓ ≥ 1` the term `m = 0` vanishes, which gives the
exponential decay of `θ_{u,ℓ}` at every cusp.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open Complex Finset Real

/-- The dual coefficient `∏ⱼ G(a, mⱼ; c)`. -/
noncomputable def gauss3 (c : ℕ) [NeZero c] (a : ℤ) (m : Fin 3 → ℤ) : ℂ :=
  ∏ j, gaussQ (a : ZMod c) ((m j : ℤ) : ZMod c)

theorem norm_gaussQ_le_card (c : ℕ) [NeZero c] (a n : ZMod c) : ‖gaussQ a n‖ ≤ c := by
  unfold gaussQ
  refine (norm_sum_le _ _).trans ?_
  simp [ZMod.card]

/-- The dual Gaussian factor. -/
noncomputable def dualExp (c : ℕ) (w : ℂ) (m : Fin 3 → ℤ) : ℂ :=
  cexp (-π * I * sq3 m / (2 * w * (c : ℂ) ^ 2))

theorem re_dual_coeff (c : ℕ) [NeZero c] {w : ℂ} (hw : 0 < w.im) :
    (-π * I / (2 * w * (c : ℂ) ^ 2)).re = -π * w.im / (2 * (c : ℝ) ^ 2 * normSq w) := by
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_im] at hw; exact lt_irrefl 0 hw
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hcr : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have e : -π * I / (2 * w * (c : ℂ) ^ 2) = ((-π / (2 * (c : ℝ) ^ 2) : ℝ) : ℂ) * (I / w) := by
    push_cast; field_simp
  rw [e, re_ofReal_mul, div_re]
  simp only [I_re, I_im, zero_mul, zero_div, one_mul, zero_add]
  have := normSq_pos.mpr hw0
  field_simp

theorem expSummable_dual (u : Fin 3 → ℂ) (c : ℕ) [NeZero c] (a : ℤ) {w : ℂ} (hw : 0 < w.im) :
    ExpSummable (fun m : Fin 3 → ℤ => gauss3 c a m * dualExp c w m)
      (fun m => π * I * dot3 u m / (w * c)) := by
  intro R
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_im] at hw; exact lt_irrefl 0 hw
  have hcr : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  set y' := w.im / (4 * (c : ℝ) ^ 2 * normSq w) with hy'
  have hy'0 : 0 < y' := by
    have := normSq_pos.mpr hw0
    positivity
  set K := π / (‖w‖ * c) with hK
  set f : Fin 3 → ℤ → ℂ := fun j n =>
    (((c : ℝ) * Real.exp (-2 * π * y' * (n : ℝ) ^ 2 + (|R| * K * ‖u j‖) * |(n : ℝ)|) : ℝ) : ℂ)
    with hf
  have hfs : ∀ j, Summable fun n => ‖f j n‖ := by
    intro j
    refine ((summable_gauss_abs hy'0 (|R| * K * ‖u j‖)).mul_left (c : ℝ)).congr fun n => ?_
    simp only [hf, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_of_pos (mul_pos (by exact_mod_cast hcr) (Real.exp_pos _))).symm
  have hprod := (tsum_pi_prod f hfs).1
  refine hprod.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
  rw [norm_prod]
  simp only [hf, Complex.norm_real, Real.norm_eq_abs]
  have hpos : ∀ j, 0 < (c : ℝ) * Real.exp (-2 * π * y' * ((m j : ℤ) : ℝ) ^ 2 +
      |R| * K * ‖u j‖ * |((m j : ℤ) : ℝ)|) := fun j => by positivity
  simp only [abs_of_pos (hpos _)]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  -- bound the left side
  have hG : ‖gauss3 c a m‖ ≤ ∏ _j : Fin 3, (c : ℝ) := by
    unfold gauss3
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => norm_gaussQ_le_card c _ _)
  have hE : ‖dualExp c w m‖ = Real.exp (-2 * π * y' * ∑ j, ((m j : ℤ) : ℝ) ^ 2) := by
    unfold dualExp
    rw [Complex.norm_exp]
    congr 1
    have : -π * I * sq3 m / (2 * w * (c : ℂ) ^ 2) = (-π * I / (2 * w * (c : ℂ) ^ 2)) * sq3 m := by
      ring
    rw [this, mul_re, re_dual_coeff c hw]
    have hs : (sq3 m).re = ∑ j, ((m j : ℤ) : ℝ) ^ 2 := by simp [sq3, pow_two]
    have hsi : (sq3 m).im = 0 := by simp [sq3, pow_two]
    rw [hs, hsi, mul_zero, sub_zero, hy']
    field_simp
    ring
  have hlam : ‖π * I * dot3 u m / (w * c)‖ ≤ ∑ j : Fin 3, K * ‖u j‖ * |((m j : ℤ) : ℝ)| := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_mul, Complex.norm_natCast]
    unfold dot3
    have hden : 0 < ‖w‖ * c := by
      have : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      positivity
    rw [div_le_iff₀ hden]
    calc π * ‖∑ j, u j * (m j : ℂ)‖ ≤ π * ∑ j, ‖u j * (m j : ℂ)‖ := by
          gcongr; exact norm_sum_le _ _
      _ = (∑ j : Fin 3, K * ‖u j‖ * |((m j : ℤ) : ℝ)|) * (‖w‖ * c) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, Complex.norm_intCast, hK]
          field_simp
  have hexp : Real.exp (R * ‖π * I * dot3 u m / (w * c)‖) ≤
      Real.exp (|R| * ∑ j : Fin 3, K * ‖u j‖ * |((m j : ℤ) : ℝ)|) :=
    Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right (le_abs_self R) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hlam (abs_nonneg R)))
  have hsplit : Real.exp (-2 * π * y' * ∑ j, ((m j : ℤ) : ℝ) ^ 2) *
      Real.exp (|R| * ∑ j : Fin 3, K * ‖u j‖ * |((m j : ℤ) : ℝ)|) =
      Real.exp (∑ j : Fin 3, (-2 * π * y' * ((m j : ℤ) : ℝ) ^ 2 +
        |R| * K * ‖u j‖ * |((m j : ℤ) : ℝ)|)) := by
    rw [← Real.exp_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [norm_mul, hE, ← hsplit, mul_assoc]
  exact mul_le_mul hG (mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le) (by positivity)
    (by positivity)

theorem summable_norm_cexp_quad (β γ δ : ℂ) (hβ : 0 < β.re) :
    Summable (fun n : ℤ => ‖cexp (-π * β * (n : ℂ) ^ 2 + γ * n + δ)‖) := by
  have hy : 0 < β.re / 2 := by linarith
  refine ((summable_gauss_abs hy |γ.re|).mul_left (Real.exp δ.re)).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ?_)
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : (-π * β * (n : ℂ) ^ 2 + γ * n + δ).re = -π * β.re * (n : ℝ) ^ 2 + γ.re * n + δ.re := by
    simp [mul_re, pow_two]
  rw [hre]
  have : γ.re * (n : ℝ) ≤ |γ.re| * |(n : ℝ)| := by
    rw [← abs_mul]; exact le_abs_self _
  nlinarith [Real.pi_pos]

/-- **The isotropic theta series at a rational point.** -/
theorem theta3_rat (u : Fin 3 → ℂ) (hu : ∑ j, u j ^ 2 = 0) (ℓ : ℕ) (c : ℕ) [NeZero c] (a : ℤ)
    {w : ℂ} (hw : 0 < w.im) :
    theta3 u ℓ ((a : ℂ) / c + w) =
      (1 / (-2 * I * w * (c : ℂ) ^ 2) ^ (1 / 2 : ℂ)) ^ 3 *
        ∑' m : Fin 3 → ℤ, gauss3 c a m * dualExp c w m * (dot3 u m / (2 * w * c)) ^ ℓ := by
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_im] at hw; exact lt_irrefl 0 hw
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  set A := 1 / (-2 * I * w * (c : ℂ) ^ 2) ^ (1 / 2 : ℂ) with hA
  set z := (a : ℂ) / c + w with hz
  have hzim : 0 < z.im := by
    rw [hz]; simp only [add_im, div_natCast_im, intCast_im, zero_div, zero_add]; exact hw
  set Bq := I / (2 * w * (c : ℂ) ^ 2) with hBq
  have hBre : 0 < Bq.re := by
    have hcr : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
    have e : Bq = ((1 / (2 * (c : ℝ) ^ 2) : ℝ) : ℂ) * (I / w) := by
      rw [hBq]; push_cast; field_simp
    rw [e, re_ofReal_mul, div_re]
    simp only [I_re, I_im, zero_mul, zero_div, one_mul, zero_add]
    have := normSq_pos.mpr hw0
    positivity
  -- the generating function, transformed
  have hfun : (fun s => Theta3 u z s) = fun s => A ^ 3 * ∑' m : Fin 3 → ℤ,
      gauss3 c a m * dualExp c w m * cexp (s * (π * I * dot3 u m / (w * c))) := by
    funext s
    rw [Theta3_eq_prod u hzim]
    simp only [hz, thetaJ_rat c a w hw]
    set g : Fin 3 → ℤ → ℂ := fun j n => gaussQ (a : ZMod c) (n : ZMod c) *
      cexp (-π * I * ((n : ℂ) - c * (s * u j)) ^ 2 / (2 * w * (c : ℂ) ^ 2)) with hg
    have hgs : ∀ j, Summable fun n => ‖g j n‖ := by
      intro j
      have hq := summable_norm_cexp_quad Bq (2 * π * Bq * c * (s * u j))
        (-π * Bq * (c * (s * u j)) ^ 2) hBre
      refine (hq.mul_left (c : ℝ)).of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      simp only [hg, norm_mul]
      refine mul_le_mul (norm_gaussQ_le_card c _ _) (le_of_eq ?_) (norm_nonneg _) (Nat.cast_nonneg _)
      congr 2
      rw [hBq]
      field_simp
      ring
    have hp := (tsum_pi_prod g hgs).2
    rw [Fin.prod_univ_three, show A * (∑' n : ℤ, g 0 n) * (A * ∑' n : ℤ, g 1 n) *
      (A * ∑' n : ℤ, g 2 n) = A ^ 3 * ∏ j, ∑' n : ℤ, g j n by
        rw [Fin.prod_univ_three]; ring, ← hp]
    congr 1
    refine tsum_congr fun m => ?_
    simp only [hg, gauss3, dualExp]
    rw [Finset.prod_mul_distrib, ← Complex.exp_sum, mul_assoc (∏ j, _), ← Complex.exp_add]
    congr 2
    simp only [sq3, dot3, Fin.sum_univ_three]
    have hu3 : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 0 := by simpa [Fin.sum_univ_three] using hu
    field_simp
    linear_combination (-(c : ℂ) ^ 2 * s ^ 2) * hu3
  -- compare derivatives
  have hE := expSummable_theta3 u hzim
  have hD := expSummable_dual u c a hw
  have lhs : iteratedDeriv ℓ (fun s => Theta3 u z s) 0 = (2 * π * I) ^ ℓ * theta3 u ℓ z := by
    have : (fun s => Theta3 u z s) = fun s => ∑' x : Fin 3 → ℤ,
        cexp (2 * π * I * sq3 x * z) * cexp (s * (2 * π * I * dot3 u x)) := rfl
    rw [this, iteratedDeriv_tsum_exp hE ℓ, theta3, ← tsum_mul_left]
    refine tsum_congr fun x => ?_
    ring
  have rhs : iteratedDeriv ℓ (fun s => A ^ 3 * ∑' m : Fin 3 → ℤ,
      gauss3 c a m * dualExp c w m * cexp (s * (π * I * dot3 u m / (w * c)))) 0 =
      A ^ 3 * ∑' m : Fin 3 → ℤ, gauss3 c a m * dualExp c w m * (π * I * dot3 u m / (w * c)) ^ ℓ := by
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_tsum_exp hD ℓ]
  have key : iteratedDeriv ℓ (fun s => Theta3 u z s) 0 = iteratedDeriv ℓ (fun s => A ^ 3 *
      ∑' m : Fin 3 → ℤ, gauss3 c a m * dualExp c w m *
        cexp (s * (π * I * dot3 u m / (w * c)))) 0 := by rw [hfun]
  rw [lhs, rhs] at key
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  apply mul_left_cancel₀ (pow_ne_zero ℓ h2pi)
  rw [key, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [show π * I * dot3 u m / (w * c) = (2 * π * I) * (dot3 u m / (2 * w * c)) by
    field_simp, mul_pow]
  ring

end ThreeSquares
