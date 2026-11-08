/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.ThetaCusp
public import ThreeSquaresLib.Weyl

/-!
# Fourier coefficients of the isotropic theta series

`theta3_coeff`: for `y > 0` and `n ∈ ℕ`,
`∫₀¹ θ_{u,ℓ}(x + iy) e(−n(x + iy)) dx = W_u(n) = ∑_{|x|² = n} (u·x)^ℓ`.
-/

@[expose] public section

namespace ThreeSquares

open Complex Finset Real MeasureTheory intervalIntegral

/-- The Weyl sum `W_u(n) = ∑_{|x|² = n} (u·x)^ℓ`. -/
noncomputable def weylU (u : Fin 3 → ℂ) (ℓ n : ℕ) : ℂ := ∑ x ∈ Duke.reps3 n, dot3 u x ^ ℓ

theorem integral_exp_int (k : ℤ) :
    ∫ s in (0 : ℝ)..1, cexp (2 * π * I * k * s) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · simp [hk]
  · have hc : (2 * π * I * k : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, I_ne_zero, hk]
    have := integral_exp_mul_complex (a := 0) (b := 1) hc
    simp only [ofReal_one, mul_one, ofReal_zero, mul_zero, Complex.exp_zero] at this
    rw [show (fun s : ℝ => cexp (2 * π * I * k * s)) = fun s : ℝ => cexp (2 * π * I * k * (s : ℂ))
      from rfl, this, show 2 * π * I * (k : ℂ) = (k : ℂ) * (2 * π * I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, sub_self, zero_div]

theorem sq3_natCast (x : Fin 3 → ℤ) : sq3 x = ((∑ j, x j ^ 2 : ℤ) : ℂ) := by
  simp [sq3]

theorem theta3_coeff (u : Fin 3 → ℂ) (ℓ n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ s in (0 : ℝ)..1, theta3 u ℓ (s + y * I) * cexp (-(2 * π * I * n * (s + y * I))) =
      weylU u ℓ n := by
  -- termwise
  set g : (Fin 3 → ℤ) → ℝ → ℂ := fun x s =>
    dot3 u x ^ ℓ * cexp (2 * π * I * sq3 x * (s + y * I)) * cexp (-(2 * π * I * n * (s + y * I)))
    with hg
  have hterm : ∀ x, ∫ s in (0 : ℝ)..1, g x s =
      if (∑ j, x j ^ 2 : ℤ) = n then dot3 u x ^ ℓ else 0 := by
    intro x
    have e : ∀ s : ℝ, g x s = (dot3 u x ^ ℓ * cexp (-2 * π * ((∑ j, x j ^ 2 : ℤ) - n) * y)) *
        cexp (2 * π * I * (((∑ j, x j ^ 2 : ℤ) - n : ℤ) : ℂ) * s) := by
      intro s
      simp only [hg, sq3_natCast, mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring_nf
      rw [I_sq]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_exp_int]
    split_ifs with h1 h2 h2
    · rw [h2]; simp
    · exfalso; apply h2; linarith
    · exfalso; apply h1; rw [h2]; ring
    · simp
  -- the bound for interchanging
  have hE := expSummable_theta3 u (z := y * I) (by simpa using hy)
  have hsum : Summable (fun x : Fin 3 → ℤ => ‖dot3 u x‖ ^ ℓ *
      Real.exp (-2 * π * y * ((∑ j, x j ^ 2 : ℤ) : ℝ)) * Real.exp (2 * π * y * n)) := by
    have := (hE.summable_pow ℓ 0 le_rfl).mul_right (Real.exp (2 * π * y * n) / (2 * π) ^ ℓ)
    refine this.congr fun x => ?_
    have hn : ‖cexp (2 * π * I * sq3 x * (y * I))‖ = Real.exp (-2 * π * y * ((∑ j, x j ^ 2 : ℤ) : ℝ)) := by
      rw [Complex.norm_exp, sq3_natCast]
      congr 1
      have : 2 * π * I * (((∑ j, x j ^ 2 : ℤ)) : ℂ) * (y * I) =
          ((-2 * π * y * ((∑ j, x j ^ 2 : ℤ) : ℝ) : ℝ) : ℂ) := by
        push_cast; ring_nf; rw [I_sq]; ring
      rw [this, ofReal_re]
    rw [hn, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_two, zero_mul, Real.exp_zero, mul_one, mul_pow]
    have : (2 * π) ^ ℓ ≠ 0 := pow_ne_zero _ (by positivity)
    field_simp
  have hbound : ∀ x, ∀ s : ℝ, ‖g x s‖ = ‖dot3 u x‖ ^ ℓ *
      Real.exp (-2 * π * y * ((∑ j, x j ^ 2 : ℤ) : ℝ)) * Real.exp (2 * π * y * n) := by
    intro x s
    have hN := sq3_natCast x
    simp only [hg, norm_mul, norm_pow, Complex.norm_exp]
    rw [hN]
    generalize (∑ j, x j ^ 2 : ℤ) = N
    congr 2
    · congr 1
      simp [mul_re, mul_im]; ring
    · simp [mul_re, mul_im]; ring
  -- interchange
  have hθ : ∀ s : ℝ, theta3 u ℓ (s + y * I) * cexp (-(2 * π * I * n * (s + y * I))) =
      ∑' x, g x s := by
    intro s
    rw [theta3, ← tsum_mul_right]
  simp_rw [hθ]
  let F : (Fin 3 → ℤ) → C(ℝ, ℂ) := fun x => ⟨g x, by simp only [hg]; fun_prop⟩
  have hF : Summable fun x =>
      ‖(F x).restrict (⟨Set.uIcc 0 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
    refine hsum.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_)
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun s => ?_
    simp only [ContinuousMap.restrict_apply]
    exact (hbound x s).le
  have hswap := tsum_intervalIntegral_eq_of_summable_norm hF
  change ∫ s in (0 : ℝ)..1, ∑' x, F x s = _
  rw [← hswap]
  change ∑' x, ∫ s in (0 : ℝ)..1, g x s = _
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Duke.reps3 n)]
  · unfold weylU
    refine sum_congr rfl fun x hx => ?_
    rw [Duke.mem_reps3] at hx
    rw [if_pos (by exact_mod_cast hx)]
  · intro x hx
    rw [Duke.mem_reps3] at hx
    rw [if_neg (fun h => hx (by exact_mod_cast h))]

end ThreeSquares
