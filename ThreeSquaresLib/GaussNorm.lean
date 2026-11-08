/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.ThetaMult

/-!
# The theta multiplier has modulus one

`norm_sq_gaussQ_zero`: for `4 ∣ q` and `a` a unit, `|G(a, 0; q)|² = 2q`; hence
`norm_kappa`: `|G(a, 0; q) / ((1 + i)√q)| = 1`.
-/

@[expose] public section

namespace ThreeSquares

open Complex Finset ZMod

theorem two_mul_eq_zero_iff (m : ℕ) (hm : 0 < m) (h : ZMod (4 * m)) :
    2 * h = 0 ↔ h = 0 ∨ h = ((2 * m : ℕ) : ZMod (4 * m)) := by
  haveI : NeZero (4 * m) := ⟨by omega⟩
  constructor
  · intro h2
    have hv := congrArg ZMod.val h2
    rw [ZMod.val_zero, ZMod.val_mul, ZMod.val_two_eq_two_mod] at hv
    have hlt := ZMod.val_lt h
    have h2' : (2 % (4 * m)) = 2 := Nat.mod_eq_of_lt (by omega)
    rw [h2'] at hv
    have : 2 * h.val = 0 ∨ 2 * h.val = 4 * m := by
      have := Nat.dvd_of_mod_eq_zero hv
      obtain ⟨k, hk⟩ := this
      have : k < 2 := by nlinarith
      interval_cases k <;> omega
    rcases this with e | e
    · left
      apply ZMod.val_injective
      rw [ZMod.val_zero]; omega
    · right
      apply ZMod.val_injective
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]; omega
  · rintro (rfl | rfl)
    · simp
    · rw [show (2 : ZMod (4 * m)) * ((2 * m : ℕ) : ZMod (4 * m)) = ((4 * m : ℕ) : ZMod (4 * m)) by
        push_cast; ring, ZMod.natCast_self]

theorem norm_sq_gaussQ_zero (m : ℕ) (hm : 0 < m) (a : ZMod (4 * m)) (ha : IsUnit a) :
    haveI : NeZero (4 * m) := ⟨by omega⟩
    ‖gaussQ a 0‖ ^ 2 = 2 * (4 * m : ℕ) := by
  haveI : NeZero (4 * m) := ⟨by omega⟩
  have hmc := gaussQ_mul_conj a (0 : ZMod (4 * m))
  have hiff : ∀ h : ZMod (4 * m), 2 * a * h = 0 ↔ h = 0 ∨ h = ((2 * m : ℕ) : ZMod (4 * m)) := by
    intro h
    rw [← two_mul_eq_zero_iff m hm h]
    constructor
    · intro e
      have := congrArg (fun x => ha.unit⁻¹.val * x) e
      simp only [mul_zero] at this
      rw [show (ha.unit⁻¹ : (ZMod (4 * m))ˣ).val * (2 * a * h) = 2 * h * (ha.unit⁻¹.val * a) by ring,
        IsUnit.val_inv_mul, mul_one] at this
      exact this
    · intro e; rw [show 2 * a * h = a * (2 * h) by ring, e, mul_zero]
  have hne : (0 : ZMod (4 * m)) ≠ ((2 * m : ℕ) : ZMod (4 * m)) := by
    intro h
    have := congrArg ZMod.val h
    rw [ZMod.val_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at this
    omega
  have hsum : (∑ h : ZMod (4 * m), if 2 * a * h = 0 then
      (ZMod.stdAddChar (a * h ^ 2 + 0 * h) : ℂ) else 0) = 2 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hfilter : (univ.filter fun h : ZMod (4 * m) => 2 * a * h = 0) =
        {0, ((2 * m : ℕ) : ZMod (4 * m))} := by
      ext h; simp [hiff]
    rw [hfilter, Finset.sum_pair hne]
    have hsq : (((2 * m : ℕ) : ZMod (4 * m))) ^ 2 = 0 := by
      rw [← Nat.cast_pow, show (2 * m) ^ 2 = (4 * m) * m by ring, Nat.cast_mul, ZMod.natCast_self,
        zero_mul]
    rw [show a * ((2 * m : ℕ) : ZMod (4 * m)) ^ 2 + 0 * ((2 * m : ℕ) : ZMod (4 * m)) = 0 by
        rw [hsq]; ring,
      show a * (0 : ZMod (4 * m)) ^ 2 + 0 * 0 = 0 by ring, AddChar.map_zero_eq_one]
    norm_num
  rw [hsum, Complex.mul_conj'] at hmc
  have : ((‖gaussQ a 0‖ ^ 2 : ℝ) : ℂ) = ((2 * (4 * m : ℕ) : ℝ) : ℂ) := by
    push_cast; rw [hmc]; push_cast; ring
  exact_mod_cast this

theorem norm_kappa (m : ℕ) (hm : 0 < m) (a : ZMod (4 * m)) (ha : IsUnit a) :
    haveI : NeZero (4 * m) := ⟨by omega⟩
    ‖gaussQ a 0 / ((1 + I) * (Real.sqrt (4 * m : ℕ) : ℂ))‖ = 1 := by
  haveI : NeZero (4 * m) := ⟨by omega⟩
  have h := norm_sq_gaussQ_zero m hm a ha
  have hq : (0 : ℝ) < (4 * m : ℕ) := by exact_mod_cast (by omega : 0 < 4 * m)
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hq)]
  have h1i : ‖(1 + I : ℂ)‖ = Real.sqrt 2 := by
    rw [Complex.norm_def, Complex.normSq_apply]; simp; norm_num
  rw [h1i, ← Real.sqrt_mul (by norm_num), div_eq_one_iff_eq (by positivity)]
  rw [← Real.sqrt_sq (norm_nonneg _), h]

end ThreeSquares
