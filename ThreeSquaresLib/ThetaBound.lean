/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.ThetaCoeff
public import Mathlib.NumberTheory.Modular
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The isotropic theta series is bounded like a cusp form

`theta3_bound`: for `u` isotropic and `ℓ ≥ 1` there is `C` with
`(Im z)^{(3/2+ℓ)/2} |θ_{u,ℓ}(z)| ≤ C` on the whole upper half plane.

Every `z` is `(aw+b)/(cw+d)` with `w` in the standard fundamental domain (`Im w ≥ √3/2`). For
`c = 0` this is a translation and the `q`-expansion decays; for `c ≠ 0` the expansion
`theta3_rat` at `a/c` gives a bound in which all powers of `|cw+d|` cancel.
-/

@[expose] public section

namespace ThreeSquares

open Complex Finset Real

/-- A summable majorant: `∑_{m} |u·m|^ℓ e^{−β|m|²}` for `β > 0`. -/
theorem summable_dot_gauss (u : Fin 3 → ℂ) (ℓ : ℕ) {β : ℝ} (hβ : 0 < β) :
    Summable (fun m : Fin 3 → ℤ => ‖dot3 u m‖ ^ ℓ * Real.exp (-β * ((∑ j, m j ^ 2 : ℤ) : ℝ))) := by
  have hz : 0 < ((β / (2 * π) : ℝ) * I).im := by
    rw [mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, zero_mul, add_zero]
    exact div_pos hβ (by positivity)
  have hE := (expSummable_theta3 u hz).summable_pow ℓ 0 le_rfl
  refine (hE.mul_left ((2 * π) ^ ℓ)⁻¹).congr fun m => ?_
  have hn : ‖cexp (2 * π * I * sq3 m * ((β / (2 * π) : ℝ) * I))‖ =
      Real.exp (-β * ((∑ j, m j ^ 2 : ℤ) : ℝ)) := by
    rw [Complex.norm_exp, sq3_natCast]
    congr 1
    have h2π : (2 * π : ℝ) ≠ 0 := by positivity
    have : 2 * π * I * (((∑ j, m j ^ 2 : ℤ)) : ℂ) * (((β / (2 * π) : ℝ)) * I) =
        ((-β * ((∑ j, m j ^ 2 : ℤ) : ℝ) : ℝ) : ℂ) := by
      push_cast; field_simp; ring_nf; rw [I_sq]; ring
    rw [this, ofReal_re]
  rw [hn, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_two, mul_one, zero_mul, Real.exp_zero, mul_one, mul_pow]
  have : (2 * π) ^ ℓ ≠ 0 := pow_ne_zero _ (by positivity)
  rw [mul_pow, mul_pow]
  field_simp

/-- `y^{k/2} e^{−π y N/2} ≤ C_k e^{−π √3 N/8}` for `y ≥ √3/2`, `N ≥ 1`. -/
theorem rpow_mul_exp_le (k : ℝ) (hk : 0 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, Real.sqrt 3 / 2 ≤ y → ∀ N : ℝ, 1 ≤ N →
      y ^ (k / 2) * Real.exp (-π * y * N / 2) ≤ C * Real.exp (-π * Real.sqrt 3 * N / 8) := by
  -- `y^{k/2} e^{−π y/4}` is bounded on `[0, ∞)`
  obtain ⟨C, hC⟩ : ∃ C, ∀ y : ℝ, 0 ≤ y → y ^ (k / 2) * Real.exp (-π * y / 4) ≤ C := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k / 2) (π / 4)
      (by positivity))
    obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp (h.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by
      norm_num)))
    have hcont : ContinuousOn (fun y : ℝ => y ^ (k / 2) * Real.exp (-π * y / 4)) (Set.Icc 0 (max Y 0)) :=
      ((continuousOn_id.rpow_const fun _ _ => Or.inr (by positivity)).mul (by fun_prop))
    obtain ⟨M, hM⟩ := (isCompact_Icc.exists_bound_of_continuousOn hcont)
    refine ⟨max M 1, fun y hy => ?_⟩
    by_cases hyY : y ≤ max Y 0
    · have := hM y ⟨hy, hyY⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    · push Not at hyY
      have := hY y (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hyY))
      have e : -π * y / 4 = -(π / 4) * y := by ring
      rw [e]
      exact this.trans (le_max_right _ _)
  refine ⟨max C 0, le_max_right _ _, fun y hy N hN => ?_⟩
  have hy0 : 0 ≤ y := le_trans (by positivity) hy
  have h1 := hC y hy0
  have hsplit : Real.exp (-π * y * N / 2) =
      Real.exp (-π * y / 4) * Real.exp (-π * y * (2 * N - 1) / 4) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-π * y * (2 * N - 1) / 4) ≤ Real.exp (-π * Real.sqrt 3 * N / 8) := by
    apply Real.exp_le_exp.mpr
    have : Real.sqrt 3 * N / 8 ≤ y * (2 * N - 1) / 4 := by nlinarith
    nlinarith [Real.pi_pos]
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul (h1.trans (le_max_left _ _)) h2 (Real.exp_pos _).le (le_max_right _ _)

theorem theta3_add_int (u : Fin 3 → ℂ) (ℓ : ℕ) (z : ℂ) (n : ℤ) :
    theta3 u ℓ (z + n) = theta3 u ℓ z := by
  unfold theta3
  refine tsum_congr fun x => ?_
  congr 1
  rw [sq3_natCast, mul_add, Complex.exp_add]
  rw [show 2 * π * I * (((∑ j, x j ^ 2 : ℤ)) : ℂ) * (n : ℂ) =
    (((∑ j, x j ^ 2) * n : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem norm_theta3_le (u : Fin 3 → ℂ) (ℓ : ℕ) {z : ℂ} (hz : 0 < z.im) :
    ‖theta3 u ℓ z‖ ≤ ∑' x : Fin 3 → ℤ, ‖dot3 u x‖ ^ ℓ *
      Real.exp (-2 * π * z.im * ((∑ j, x j ^ 2 : ℤ) : ℝ)) := by
  have hs := summable_dot_gauss u ℓ (β := 2 * π * z.im) (by positivity)
  unfold theta3
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun x => ?_))
  · refine hs.congr fun x => ?_
    rw [norm_mul, norm_pow, Complex.norm_exp, sq3_natCast]
    generalize (∑ j, x j ^ 2 : ℤ) = N
    congr 2
    simp [mul_re, mul_im]; ring
  · rw [norm_mul, norm_pow, Complex.norm_exp, sq3_natCast]
    generalize (∑ j, x j ^ 2 : ℤ) = N
    congr 2
    simp [mul_re, mul_im]; ring

theorem norm_cpow_half (X : ℂ) (hX : X ≠ 0) : ‖X ^ (1 / 2 : ℂ)‖ = ‖X‖ ^ ((1 : ℝ) / 2) := by
  rw [Complex.norm_cpow_of_ne_zero hX]
  simp

/-- The case `c > 0`: the bound at `(aw+b)/(cw+d)` in terms of `Im w`. -/
theorem theta3_bound_aux (u : Fin 3 → ℂ) (hu : ∑ j, u j ^ 2 = 0) (ℓ : ℕ) (a b : ℤ) (cn : ℕ)
    [NeZero cn] (d : ℤ) (hdet : a * d - b * cn = 1) (w : ℂ) (hw : 0 < w.im) :
    ((a * w + b) / (cn * w + d)).im ^ (((3 : ℝ) / 2 + ℓ) / 2) *
        ‖theta3 u ℓ ((a * w + b) / (cn * w + d))‖ ≤
      w.im ^ (((3 : ℝ) / 2 + ℓ) / 2) * ∑' m : Fin 3 → ℤ, ‖dot3 u m‖ ^ ℓ *
        Real.exp (-π * w.im * ((∑ j, m j ^ 2 : ℤ) : ℝ) / 2) := by
  set k : ℝ := 3 / 2 + ℓ with hk
  have hcr : (0 : ℝ) < cn := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne cn)
  have hc' : (cn : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne cn
  set ζ := (cn : ℂ) * w + d with hζ
  have hζim : ζ.im = cn * w.im := by rw [hζ]; simp
  have hζ0 : ζ ≠ 0 := fun h => by
    have := hζim; rw [h, zero_im] at this; nlinarith
  set R := ‖ζ‖ with hR
  have hR0 : 0 < R := norm_pos_iff.mpr hζ0
  set w' := -1 / ((cn : ℂ) * ζ) with hw'
  have hzw : (a * w + b) / (cn * w + d) = (a : ℂ) / cn + w' := by
    have := gamma_sub a b cn d (by exact_mod_cast hdet) w (by exact_mod_cast hc')
      (by exact_mod_cast hζ0)
    push_cast at this
    rw [this]
  have hnw' : normSq w' = 1 / ((cn : ℝ) ^ 2 * R ^ 2) := by
    rw [hw', normSq_div, normSq_neg, normSq_one, normSq_mul, normSq_natCast, hR,
      ← Complex.sq_norm]
    ring
  have hw'im : w'.im = w.im / R ^ 2 := by
    rw [hw', div_im]
    simp only [neg_re, one_re, neg_im, one_im, neg_zero, zero_mul, zero_div, zero_sub]
    rw [show ((cn : ℂ) * ζ).im = cn * ζ.im by simp, hζim, normSq_mul, normSq_natCast, hR,
      ← Complex.sq_norm]
    field_simp
  have hw'pos : 0 < w'.im := by rw [hw'im]; positivity
  have hnorm_w' : ‖w'‖ = 1 / ((cn : ℝ) * R) := by
    rw [hw', norm_div, norm_neg, norm_one, norm_mul, Complex.norm_natCast]
  rw [hzw, theta3_rat u hu ℓ cn a hw'pos]
  -- the prefactor
  set X := -2 * I * w' * (cn : ℂ) ^ 2 with hX
  have hX0 : X ≠ 0 := by
    have : w' ≠ 0 := fun h => by rw [h, zero_im] at hw'pos; exact lt_irrefl 0 hw'pos
    rw [hX]; simp [this, hc', I_ne_zero]
  have hnX : ‖X‖ = 2 * cn / R := by
    rw [hX, norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, norm_pow,
      Complex.norm_natCast, hnorm_w', Complex.norm_two]
    field_simp
  have hA : ‖(1 / X ^ (1 / 2 : ℂ)) ^ 3‖ = (R / (2 * cn)) ^ ((3 : ℝ) / 2) := by
    rw [norm_pow, norm_div, norm_one, norm_cpow_half X hX0, hnX]
    rw [← Real.rpow_natCast, one_div, ← Real.inv_rpow (by positivity), ← Real.rpow_mul (by positivity)]
    rw [inv_div]; norm_num
  -- the dual terms
  have hunit : IsUnit (a : ZMod cn) := by
    have : ((a * d - b * cn : ℤ) : ZMod cn) = 1 := by rw [hdet]; simp
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, sub_zero] at this
    exact IsUnit.of_mul_eq_one _ this
  have hG : ∀ m, ‖gauss3 cn a m‖ ≤ (2 * cn) ^ ((3 : ℝ) / 2) := by
    intro m
    unfold gauss3
    rw [norm_prod]
    have h1 : ∀ j, ‖gaussQ (a : ZMod cn) ((m j : ℤ) : ZMod cn)‖ ≤ (2 * cn) ^ ((1 : ℝ) / 2) := by
      intro j
      have := norm_sq_gaussQ_le (a : ZMod cn) ((m j : ℤ) : ZMod cn) hunit
      rw [← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le this
    calc ∏ j, ‖gaussQ (a : ZMod cn) ((m j : ℤ) : ZMod cn)‖ ≤ ∏ _j : Fin 3, (2 * cn : ℝ) ^ ((1 : ℝ) / 2) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => h1 j)
      _ = (2 * cn) ^ ((3 : ℝ) / 2) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
            ← Real.rpow_mul (by positivity)]
          norm_num
  have hD : ∀ m, ‖dualExp cn w' m‖ = Real.exp (-π * w.im * ((∑ j, m j ^ 2 : ℤ) : ℝ) / 2) := by
    intro m
    unfold dualExp
    rw [Complex.norm_exp]
    congr 1
    have : -π * I * sq3 m / (2 * w' * (cn : ℂ) ^ 2) = (-π * I / (2 * w' * (cn : ℂ) ^ 2)) * sq3 m := by
      ring
    rw [this, mul_re, re_dual_coeff cn hw'pos, sq3_natCast, intCast_re, intCast_im, mul_zero,
      sub_zero, hw'im, hnw']
    field_simp
  have hL : ∀ m, ‖dot3 u m / (2 * w' * cn)‖ ^ ℓ = (‖dot3 u m‖ * R / 2) ^ ℓ := by
    intro m
    rw [norm_div, norm_mul, norm_mul, Complex.norm_two, hnorm_w', Complex.norm_natCast]
    congr 1
    field_simp
  -- assemble
  have hsum := summable_dot_gauss u ℓ (β := π * w.im / 2) (by positivity)
  have hterm_le : ∀ m, ‖gauss3 cn a m * dualExp cn w' m * (dot3 u m / (2 * w' * cn)) ^ ℓ‖ ≤
      (2 * cn) ^ ((3 : ℝ) / 2) * (R / 2) ^ ℓ * (‖dot3 u m‖ ^ ℓ *
        Real.exp (-π * w.im * ((∑ j, m j ^ 2 : ℤ) : ℝ) / 2)) := by
    intro m
    rw [norm_mul, norm_mul, norm_pow, hD, hL, div_pow, mul_pow]
    have := hG m
    have h2 : (2 : ℝ) ^ ℓ ≠ 0 := by positivity
    calc ‖gauss3 cn a m‖ * Real.exp (-π * w.im * ((∑ j, m j ^ 2 : ℤ) : ℝ) / 2) *
          (‖dot3 u m‖ ^ ℓ * R ^ ℓ / 2 ^ ℓ)
        ≤ (2 * cn) ^ ((3 : ℝ) / 2) * Real.exp (-π * w.im * ((∑ j, m j ^ 2 : ℤ) : ℝ) / 2) *
          (‖dot3 u m‖ ^ ℓ * R ^ ℓ / 2 ^ ℓ) := by gcongr
      _ = _ := by rw [div_pow]; field_simp
  have hsum2 : Summable fun m : Fin 3 → ℤ => (2 * cn) ^ ((3 : ℝ) / 2) * (R / 2) ^ ℓ *
      (‖dot3 u m‖ ^ ℓ * Real.exp (-π * w.im * ((∑ j, m j ^ 2 : ℤ) : ℝ) / 2)) := by
    refine (hsum.mul_left ((2 * cn : ℝ) ^ ((3 : ℝ) / 2) * (R / 2) ^ ℓ)).congr fun m => ?_
    congr 3; ring
  have hθ : ‖(1 / X ^ (1 / 2 : ℂ)) ^ 3 * ∑' m : Fin 3 → ℤ,
      gauss3 cn a m * dualExp cn w' m * (dot3 u m / (2 * w' * cn)) ^ ℓ‖ ≤
      (R / (2 * cn)) ^ ((3 : ℝ) / 2) * ((2 * cn) ^ ((3 : ℝ) / 2) * (R / 2) ^ ℓ *
        ∑' m : Fin 3 → ℤ, ‖dot3 u m‖ ^ ℓ * Real.exp (-π * w.im * ((∑ j, m j ^ 2 : ℤ) : ℝ) / 2)) := by
    rw [norm_mul, hA]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← tsum_mul_left]
    have hsf := Summable.of_norm_bounded hsum2 hterm_le
    exact (norm_tsum_le_tsum_norm hsf.norm).trans (Summable.tsum_le_tsum hterm_le hsf.norm hsum2)
  -- the powers of `R` cancel
  have hpow1 : (w.im / R ^ 2) ^ (k / 2) = w.im ^ (k / 2) / R ^ k := by
    rw [Real.div_rpow hw.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hR0.le]
    rw [show ((2 : ℕ) : ℝ) * (k / 2) = k by push_cast; ring]
  have hpow2 : (R / (2 * cn)) ^ ((3 : ℝ) / 2) * (2 * cn) ^ ((3 : ℝ) / 2) = R ^ ((3 : ℝ) / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1; field_simp
  have hpow3 : R ^ ((3 : ℝ) / 2) * R ^ ℓ = R ^ k := by
    rw [hk, Real.rpow_add hR0, Real.rpow_natCast]
  have hRk : 0 < R ^ k := Real.rpow_pos_of_pos hR0 _
  set T := ∑' m : Fin 3 → ℤ, ‖dot3 u m‖ ^ ℓ * Real.exp (-π * w.im * ((∑ j, m j ^ 2 : ℤ) : ℝ) / 2)
    with hT
  have hT0 : 0 ≤ T := tsum_nonneg fun _ => by positivity
  calc (((a : ℂ) / cn + w').im) ^ (k / 2) * ‖(1 / X ^ (1 / 2 : ℂ)) ^ 3 * ∑' m : Fin 3 → ℤ,
        gauss3 cn a m * dualExp cn w' m * (dot3 u m / (2 * w' * cn)) ^ ℓ‖
      ≤ (w.im / R ^ 2) ^ (k / 2) * ((R / (2 * cn)) ^ ((3 : ℝ) / 2) *
          ((2 * cn) ^ ((3 : ℝ) / 2) * (R / 2) ^ ℓ * T)) := by
        have him : ((a : ℂ) / cn + w').im = w.im / R ^ 2 := by
          simp only [add_im, div_natCast_im, intCast_im, zero_div, zero_add]; exact hw'im
        rw [him]
        exact mul_le_mul_of_nonneg_left hθ (by positivity)
    _ = w.im ^ (k / 2) * T * (1 / 2) ^ ℓ := by
        rw [hpow1, div_pow]
        have : (R / (2 * cn)) ^ ((3 : ℝ) / 2) * ((2 * cn) ^ ((3 : ℝ) / 2) * (R ^ ℓ / 2 ^ ℓ) * T) =
            (R ^ ((3 : ℝ) / 2) * R ^ ℓ) * T / 2 ^ ℓ := by
          rw [← hpow2]; ring
        rw [this, hpow3]
        field_simp
        rw [one_div_pow, mul_assoc, mul_one_div_cancel (by positivity), mul_one]
    _ ≤ w.im ^ (k / 2) * T := by
        have : (1 / 2 : ℝ) ^ ℓ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have : 0 ≤ w.im ^ (k / 2) * T := by positivity
        nlinarith

/-- **Cusp-form bound for the isotropic theta series.** -/
theorem theta3_bound (u : Fin 3 → ℂ) (hu : ∑ j, u j ^ 2 = 0) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ C : ℝ, ∀ z : ℂ, 0 < z.im →
      z.im ^ (((3 : ℝ) / 2 + ℓ) / 2) * ‖theta3 u ℓ z‖ ≤ C := by
  set k : ℝ := 3 / 2 + ℓ with hk
  obtain ⟨C₀, hC₀, hC⟩ := rpow_mul_exp_le k (by positivity)
  set β := π * Real.sqrt 3 / 8 with hβ
  have hβ0 : 0 < β := by positivity
  have hS := summable_dot_gauss u ℓ hβ0
  set S := ∑' m : Fin 3 → ℤ, ‖dot3 u m‖ ^ ℓ * Real.exp (-β * ((∑ j, m j ^ 2 : ℤ) : ℝ)) with hSdef
  -- the termwise estimate shared by both cases
  have hterm : ∀ (y : ℝ), Real.sqrt 3 / 2 ≤ y → ∀ m : Fin 3 → ℤ,
      y ^ (k / 2) * (‖dot3 u m‖ ^ ℓ * Real.exp (-π * y * ((∑ j, m j ^ 2 : ℤ) : ℝ) / 2)) ≤
        C₀ * (‖dot3 u m‖ ^ ℓ * Real.exp (-β * ((∑ j, m j ^ 2 : ℤ) : ℝ))) := by
    intro y hy m
    by_cases hm : m = 0
    · subst hm
      have : dot3 u 0 = 0 := by simp [dot3]
      rw [this, norm_zero, zero_pow (by omega)]; simp
    · have hN : (1 : ℝ) ≤ ((∑ j, m j ^ 2 : ℤ) : ℝ) := by
        have : (1 : ℤ) ≤ ∑ j, m j ^ 2 := by
          obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
            by_contra h; push Not at h; exact hm (funext h)
          have h1 : 1 ≤ m j ^ 2 := by
            have : 0 < m j ^ 2 := by positivity
            omega
          have := Finset.single_le_sum (f := fun i => m i ^ 2) (fun i _ => sq_nonneg (m i))
            (Finset.mem_univ j)
          linarith
        exact_mod_cast this
      have := hC y hy _ hN
      calc y ^ (k / 2) * (‖dot3 u m‖ ^ ℓ * Real.exp (-π * y * ((∑ j, m j ^ 2 : ℤ) : ℝ) / 2))
          = ‖dot3 u m‖ ^ ℓ * (y ^ (k / 2) *
              Real.exp (-π * y * ((∑ j, m j ^ 2 : ℤ) : ℝ) / 2)) := by ring
        _ ≤ ‖dot3 u m‖ ^ ℓ * (C₀ * Real.exp (-π * Real.sqrt 3 * ((∑ j, m j ^ 2 : ℤ) : ℝ) / 8)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = C₀ * (‖dot3 u m‖ ^ ℓ * Real.exp (-β * ((∑ j, m j ^ 2 : ℤ) : ℝ))) := by
            rw [hβ]; ring_nf
  have hsumbound : ∀ y : ℝ, Real.sqrt 3 / 2 ≤ y →
      y ^ (k / 2) * ∑' m : Fin 3 → ℤ, ‖dot3 u m‖ ^ ℓ *
        Real.exp (-π * y * ((∑ j, m j ^ 2 : ℤ) : ℝ) / 2) ≤ C₀ * S := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
    have hsy := summable_dot_gauss u ℓ (β := π * y / 2) (by positivity)
    rw [← tsum_mul_left, hSdef, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun m => hterm y hy m) ?_ (hS.mul_left _)
    refine (hsy.mul_left (y ^ (k / 2))).congr fun m => ?_
    congr 3; ring
  refine ⟨C₀ * S, fun z hz => ?_⟩
  -- reduce to the fundamental domain
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd (⟨z, hz⟩ : UpperHalfPlane)
  set W := g • (⟨z, hz⟩ : UpperHalfPlane) with hW
  set w : ℂ := (W : ℂ) with hw
  have hwim : Real.sqrt 3 / 2 ≤ w.im := by
    have h1 := hg.1
    have h2 := hg.2
    have hwpos : 0 < w.im := W.im_pos
    rw [show (W : ℂ).normSq = w.re ^ 2 + w.im ^ 2 by rw [normSq_apply]; ring] at h1
    have h3 : w.re ^ 2 ≤ 1 / 4 := by
      have := abs_le.mp h2
      change |w.re| ≤ 1 / 2 at h2
      nlinarith [abs_le.mp h2]
    have h4 : 3 / 4 ≤ w.im ^ 2 := by linarith
    have h5 : Real.sqrt 3 / 2 = Real.sqrt (3 / 4) := by
      rw [Real.sqrt_div' 3 (by norm_num : (0:ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [h5]
    exact Real.sqrt_le_iff.mpr ⟨hwpos.le, by linarith⟩
  have hzW : (⟨z, hz⟩ : UpperHalfPlane) = g⁻¹ • W := by rw [hW, inv_smul_smul]
  set a : ℤ := (g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 0
  set b : ℤ := (g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 0 1
  set c : ℤ := (g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0
  set d : ℤ := (g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 1
  have hdet : a * d - b * c = 1 := by
    have := (g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ).det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  have hzform : z = (a * w + b) / (c * w + d) := by
    have := congrArg (fun p : UpperHalfPlane => (p : ℂ)) hzW
    simp only at this
    rw [UpperHalfPlane.coe_specialLinearGroup_apply] at this
    exact this
  have hw0 : 0 < w.im := lt_of_lt_of_le (by positivity) hwim
  rcases lt_trichotomy c 0 with hneg | hzero | hpos
  · obtain ⟨cn, hcn⟩ : ∃ cn : ℕ, -c = cn := ⟨(-c).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    haveI : NeZero cn := ⟨by omega⟩
    have hz2 : z = (((-a : ℤ) : ℂ) * w + ((-b : ℤ) : ℂ)) / ((cn : ℂ) * w + ((-d : ℤ) : ℂ)) := by
      rw [hzform]
      have hc : (c : ℂ) = -(cn : ℂ) := by
        have : ((-c : ℤ) : ℂ) = ((cn : ℤ) : ℂ) := by rw [hcn]
        push_cast at this; linear_combination -this
      rw [hc]; push_cast
      rw [← neg_div_neg_eq]; congr 1 <;> ring
    have := theta3_bound_aux u hu ℓ (-a) (-b) cn (-d) (by
      have : (cn : ℤ) = -c := hcn.symm
      rw [this]; linarith) w hw0
    rw [hz2]
    exact this.trans (hsumbound _ hwim)
  · have had : a * d = 1 := by rw [hzero] at hdet; linarith
    have hz2 : z = w + ((b * d : ℤ) : ℂ) := by
      rw [hzform, hzero]
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨ha, hd⟩ | ⟨ha, hd⟩
      · rw [ha, hd]; push_cast; ring
      · rw [ha, hd]; push_cast; field_simp; ring
    rw [hz2, theta3_add_int]
    have hz3 : (w + ((b * d : ℤ) : ℂ)).im = w.im := by simp
    rw [hz3]
    have hsy := summable_dot_gauss u ℓ (β := 2 * π * w.im) (by positivity)
    have hsy2 := summable_dot_gauss u ℓ (β := π * w.im / 2) (by positivity)
    calc w.im ^ (k / 2) * ‖theta3 u ℓ w‖
        ≤ w.im ^ (k / 2) * ∑' m : Fin 3 → ℤ, ‖dot3 u m‖ ^ ℓ *
            Real.exp (-2 * π * w.im * ((∑ j, m j ^ 2 : ℤ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (norm_theta3_le u ℓ hw0) (by positivity)
      _ ≤ w.im ^ (k / 2) * ∑' m : Fin 3 → ℤ, ‖dot3 u m‖ ^ ℓ *
            Real.exp (-π * w.im * ((∑ j, m j ^ 2 : ℤ) : ℝ) / 2) := by
          refine mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun m => ?_) ?_ ?_) (by positivity)
          · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
            have : (0 : ℝ) ≤ ((∑ j, m j ^ 2 : ℤ) : ℝ) := by
              exact_mod_cast Finset.sum_nonneg fun j _ => sq_nonneg (m j)
            nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hw0.le) this]
          · exact hsy.congr fun m => by ring_nf
          · exact hsy2.congr fun m => by ring_nf
      _ ≤ C₀ * S := hsumbound _ hwim
  · obtain ⟨cn, hcn⟩ : ∃ cn : ℕ, c = cn := ⟨c.toNat, (Int.toNat_of_nonneg hpos.le).symm⟩
    haveI : NeZero cn := ⟨by omega⟩
    have hz2 : z = ((a : ℂ) * w + b) / ((cn : ℂ) * w + d) := by
      rw [hzform, hcn]; push_cast; rfl
    have := theta3_bound_aux u hu ℓ a b cn d (by rw [← hcn]; exact hdet) w hw0
    rw [hz2]
    exact this.trans (hsumbound _ hwim)

end ThreeSquares
