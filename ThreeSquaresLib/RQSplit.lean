/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.CoprimeT
public import ThreeSquaresLib.RootsUnitary

/-!
# Splitting `T_c` along `c = r a b`

* `Rq_udiv`: `R_q(U, N) = ∑_{a ∥ q} e_q(2 N U z_a)`, `z_a ≡ 1 (a)`, `≡ −1 (q/a)`;
* `phase_core`: for pairwise coprime `r, a, b`, `q = ab`, `rU ≡ 1 (q)`:
  `e_q(2nU z) = e(2n/(rq)) · e_b(−4n \overline{ra}) · e_r(−2n \overline{ab})`.
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset

theorem isUnit_of_isCoprime {q : ℕ} {N : ℤ} (h : IsCoprime N q) : IsUnit (N : ZMod q) := by
  obtain ⟨u, v, huv⟩ := h
  refine IsUnit.of_mul_eq_one (u : ZMod q) ?_
  have := congrArg (fun t : ℤ => (t : ZMod q)) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero, add_zero,
    Int.cast_one] at this
  rw [mul_comm]; exact this

theorem isUnit_two_of_odd {q : ℕ} (hq : Odd q) : IsUnit (2 : ZMod q) := by
  obtain ⟨k, hk⟩ := hq
  have : IsCoprime (2 : ℤ) q := ⟨-k, 1, by rw [hk]; push_cast; ring⟩
  have := isUnit_of_isCoprime this
  simpa using this

/-- **The root sum via unitary divisors.** -/
theorem Rq_udiv {q : ℕ} [NeZero q] (hodd : Odd q) (U N : ℤ) (hN : IsCoprime N q) :
    Rq q U N = ∑ a ∈ udiv q, stdAddChar ((U : ZMod q) * (2 * (N : ZMod q)) * zf q a) := by
  classical
  have hu : IsUnit ((2 : ZMod q) * (N : ZMod q)) :=
    (isUnit_two_of_odd hodd).mul (isUnit_of_isCoprime hN)
  unfold Rq
  rw [← sum_sq_eq_one hodd (fun z => (stdAddChar ((U : ZMod q) * (2 * (N : ZMod q)) * z) : ℂ))]
  symm
  refine Fintype.sum_bijective (fun z => (2 * (N : ZMod q)) * z)
    ⟨fun x y h => hu.mul_left_cancel h, fun y => ⟨hu.unit⁻¹ * y, by
      show (2 * (N : ZMod q)) * (↑hu.unit⁻¹ * y) = y
      rw [← mul_assoc, hu.mul_val_inv, one_mul]⟩⟩ _ _ fun z => ?_
  have hiff : (2 * (N : ZMod q) * z) ^ 2 = 4 * (N : ZMod q) ^ 2 ↔ z ^ 2 = 1 := by
    constructor
    · intro h
      have h' : ((2 * (N : ZMod q)) ^ 2) * z ^ 2 = ((2 * (N : ZMod q)) ^ 2) * 1 := by
        rw [mul_one, ← mul_pow, h]; ring
      exact (hu.pow 2).mul_left_cancel h'
    · intro h; rw [mul_pow, h]; ring
  by_cases hz : z ^ 2 = 1
  · rw [if_pos (hiff.mpr hz), if_pos hz]; congr 1; ring
  · rw [if_neg (fun h => hz (hiff.mp h)), if_neg hz]


theorem intCast_val (m : ℕ) [NeZero m] (x : ZMod m) : (((x.val : ℤ)) : ZMod m) = x := by simp

theorem zmod_int_eq_zero {m : ℕ} {t : ℤ} (h : (t : ZMod m) = 0) : (m : ℤ) ∣ t :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd t m).mp h

/-- **The phase identity.** -/
theorem phase_core (r a b q : ℕ) [NeZero r] [NeZero a] [NeZero b] [NeZero q] (hq : q = a * b)
    (hra : r.Coprime a) (hrb : r.Coprime b) (hab : a.Coprime b) (n : ℤ) (U : ZMod q)
    (hU : (r : ZMod q) * U = 1) (z : ℤ) (hz1 : (z : ZMod a) = 1) (hz2 : (z : ZMod b) = -1) :
    (stdAddChar (U * (2 * (n : ZMod q)) * (z : ZMod q)) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * (2 * n / (r * q))) *
        stdAddChar ((-4 * n : ZMod b) * (((r * a : ℕ) : ZMod b))⁻¹) *
        stdAddChar ((-2 * n : ZMod r) * (((a * b : ℕ) : ZMod r))⁻¹) := by
  set u : ℤ := (U.val : ℤ)
  set α : ℤ := ((((((r * a : ℕ) : ZMod b))⁻¹).val : ℕ) : ℤ)
  set β : ℤ := ((((((a * b : ℕ) : ZMod r))⁻¹).val : ℕ) : ℤ)
  have hU' : U = (u : ZMod q) := (intCast_val q U).symm
  have hα' : (((r * a : ℕ) : ZMod b))⁻¹ = (α : ZMod b) := (intCast_val b _).symm
  have hβ' : (((a * b : ℕ) : ZMod r))⁻¹ = (β : ZMod r) := (intCast_val r _).symm
  have hra_b : IsUnit (((r * a : ℕ) : ZMod b)) := by
    rw [ZMod.isUnit_iff_coprime]; exact Nat.Coprime.mul_left hrb hab
  have hab_r : IsUnit (((a * b : ℕ) : ZMod r)) := by
    rw [ZMod.isUnit_iff_coprime]; exact Nat.Coprime.mul_left hra.symm hrb.symm
  have hαm : ((r * a : ℕ) : ZMod b) * (α : ZMod b) = 1 := by
    rw [← hα']; exact ZMod.mul_inv_of_unit _ hra_b
  have hβm : ((a * b : ℕ) : ZMod r) * (β : ZMod r) = 1 := by
    rw [← hβ']; exact ZMod.mul_inv_of_unit _ hab_r
  -- `r u ≡ 1` mod `a` and mod `b`
  have hda : a ∣ q := ⟨b, hq⟩
  have hdb : b ∣ q := ⟨a, by rw [hq, mul_comm]⟩
  have hUa : (r : ZMod a) * (u : ZMod a) = 1 := by
    have := congrArg (ZMod.castHom hda (ZMod a)) hU
    rw [map_mul, map_natCast, hU', map_intCast, map_one] at this; exact this
  have hUb : (r : ZMod b) * (u : ZMod b) = 1 := by
    have := congrArg (ZMod.castHom hdb (ZMod b)) hU
    rw [map_mul, map_natCast, hU', map_intCast, map_one] at this; exact this
  set D : ℤ := u * z * r - 1 + 2 * α * (r * a) + β * (a * b)
  have hDa : (a : ℤ) ∣ D := by
    apply zmod_int_eq_zero
    simp only [D]; push_cast
    rw [ZMod.natCast_self, hz1]
    linear_combination hUa
  have hDb : (b : ℤ) ∣ D := by
    apply zmod_int_eq_zero
    simp only [D]; push_cast
    rw [ZMod.natCast_self, hz2]
    push_cast at hαm
    linear_combination -hUb + 2 * hαm
  have hDr : (r : ℤ) ∣ D := by
    apply zmod_int_eq_zero
    simp only [D]; push_cast
    rw [ZMod.natCast_self]
    push_cast at hβm
    linear_combination hβm
  have hcop1 : IsCoprime (r : ℤ) (a : ℤ) := Nat.isCoprime_iff_coprime.mpr hra
  have hcop2 : IsCoprime (r : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hrb
  have hcop3 : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
  have hD : ((r * q : ℕ) : ℤ) ∣ D := by
    rw [hq]; push_cast
    rw [← mul_assoc]
    exact IsCoprime.mul_dvd (IsCoprime.mul_left hcop2 hcop3) (IsCoprime.mul_dvd hcop1 hDr hDa) hDb
  obtain ⟨k, hk⟩ := hD
  -- rewrite everything as exponentials
  rw [hU', hα', hβ',
    show (u : ZMod q) * (2 * (n : ZMod q)) * (z : ZMod q) = ((u * (2 * n) * z : ℤ) : ZMod q) by push_cast; ring,
    show (-4 * n : ZMod b) * (α : ZMod b) = ((-4 * n * α : ℤ) : ZMod b) by push_cast; ring,
    show (-2 * n : ZMod r) * (β : ZMod r) = ((-2 * n * β : ℤ) : ZMod r) by push_cast; ring,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add,
    ← Complex.exp_add]
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne r
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne a
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne b
  have hqC : (q : ℂ) = a * b := by rw [hq]; push_cast; ring
  have hkC : (D : ℂ) = (r : ℂ) * q * k := by
    have := congrArg (fun t : ℤ => (t : ℂ)) hk; push_cast at this; exact this
  have hDC : (D : ℂ) = u * z * r - 1 + 2 * α * (r * a) + β * (a * b) := by simp only [D]; push_cast; ring
  have key : 2 * ↑Real.pi * Complex.I * ((u * (2 * n) * z : ℤ) : ℂ) / q =
      2 * Real.pi * Complex.I * (2 * n / (r * q)) + 2 * Real.pi * Complex.I * ((-4 * n * α : ℤ) : ℂ) / b +
        2 * Real.pi * Complex.I * ((-2 * n * β : ℤ) : ℂ) / r + ((2 * n * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have hq0C : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
    have e : ((2 * n * k : ℤ) : ℂ) = 2 * n * D / (r * q) := by
      rw [hkC]; push_cast; field_simp
    rw [e, hDC, hqC]
    push_cast
    field_simp
    ring
  rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end ThreeSquares
