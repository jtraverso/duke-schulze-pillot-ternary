/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.GaussSum
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Quadratic Gauss sums modulo prime powers

* `sum_zmod_eq_range`, `sum_range_mul`: splitting sums over `ℤ/(mk)`;
* `sum_stdAddChar_mul_range`: `∑_{b < k} e(bC/k) = k [k ∣ C]`;
* `gaussQ_pow_add_two`: `G(A, 0; p^{α+2}) = p · G(A, 0; p^α)` for `p ∤ 2A`.
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset

theorem sum_zmod_eq_range (n : ℕ) [NeZero n] (F : ZMod n → ℂ) :
    ∑ x : ZMod n, F x = ∑ i ∈ range n, F (i : ZMod n) := by
  refine Finset.sum_nbij' (fun x => x.val) (fun i => (i : ZMod n)) (fun x _ => ?_)
    (fun i _ => Finset.mem_univ _) (fun x _ => ?_) (fun i hi => ?_) (fun x _ => ?_)
  · exact Finset.mem_range.mpr (ZMod.val_lt x)
  · exact ZMod.natCast_zmod_val x
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hi)
  · rw [ZMod.natCast_zmod_val]

theorem sum_range_mul (G : ℕ → ℂ) (m : ℕ) : ∀ k : ℕ,
    ∑ i ∈ range (m * k), G i = ∑ b ∈ range k, ∑ a ∈ range m, G (m * b + a)
  | 0 => by simp
  | k + 1 => by
    rw [show m * (k + 1) = m * k + m by ring, Finset.sum_range_add, sum_range_mul G m k,
      Finset.sum_range_succ]

/-- `e(j/n)` for integers `j`. -/
theorem stdAddChar_int (n : ℕ) [NeZero n] (j : ℤ) :
    (stdAddChar (j : ZMod n) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * j / n) :=
  ZMod.stdAddChar_coe j

/-- **`∑_{b < k} e(bC/k) = k [k ∣ C]`.** -/
theorem sum_exp_range (k : ℕ) [NeZero k] (C : ℤ) :
    ∑ b ∈ range k, Complex.exp (2 * Real.pi * Complex.I * (b * C) / k) =
      if (k : ℤ) ∣ C then (k : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (C : ZMod k) (ZMod.isPrimitive_stdAddChar k)
  rw [sum_zmod_eq_range] at h
  have e : ∀ b : ℕ, (stdAddChar (((b : ℕ) : ZMod k) * (C : ZMod k)) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * (b * C) / k) := by
    intro b
    rw [show ((b : ℕ) : ZMod k) * (C : ZMod k) = (((b : ℤ) * C : ℤ) : ZMod k) by push_cast; ring,
      stdAddChar_int]
    push_cast; ring_nf
  simp_rw [e] at h
  rw [h]
  by_cases hc : (k : ℤ) ∣ C
  · rw [if_pos ((ZMod.intCast_zmod_eq_zero_iff_dvd C k).mpr hc), if_pos hc, ZMod.card]
  · rw [if_neg (mt (ZMod.intCast_zmod_eq_zero_iff_dvd C k).mp hc), if_neg hc]; simp

theorem gaussQ_eq_range (n : ℕ) [NeZero n] (A : ℤ) :
    gaussQ ((A : ℤ) : ZMod n) 0 = ∑ i ∈ range n, Complex.exp (2 * Real.pi * Complex.I * (A * i ^ 2) / n) := by
  unfold gaussQ
  rw [sum_zmod_eq_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show ((A : ℤ) : ZMod n) * ((i : ℕ) : ZMod n) ^ 2 + 0 * ((i : ℕ) : ZMod n) =
    ((A * (i : ℤ) ^ 2 : ℤ) : ZMod n) by push_cast; ring, stdAddChar_int]
  push_cast; ring_nf

/-- **`G(A; p^{α+2}) = p · G(A; p^α)`** for an odd prime `p ∤ A`. -/
theorem gaussQ_pow_add_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (A : ℤ) (hA : ¬ (p : ℤ) ∣ A)
    (α : ℕ) :
    haveI : NeZero (p ^ (α + 2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    haveI : NeZero (p ^ α) := ⟨pow_ne_zero _ hp.ne_zero⟩
    gaussQ ((A : ℤ) : ZMod (p ^ (α + 2))) 0 = p * gaussQ ((A : ℤ) : ZMod (p ^ α)) 0 := by
  haveI : NeZero (p ^ (α + 2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ α) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [gaussQ_eq_range, gaussQ_eq_range]
  set m := p ^ (α + 1)
  have hq : p ^ (α + 2) = m * p := by simp only [m]; ring
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hm0 : (m : ℂ) ≠ 0 := by simp only [m]; push_cast; exact pow_ne_zero _ hp0
  rw [hq, sum_range_mul _ m p]
  -- the inner structure: `e(A(a + m b)²/(mp)) = e(A a²/(mp)) e(2Aab/p)`
  have hmC : (m : ℂ) = (p : ℂ) ^ (α + 1) := by simp [m]
  have hsplit : ∀ a b : ℕ, Complex.exp (2 * Real.pi * Complex.I * (A * ((m * b + a : ℕ) : ℂ) ^ 2) /
      ((m * p : ℕ) : ℂ)) = Complex.exp (2 * Real.pi * Complex.I * (A * (a : ℂ) ^ 2) / ((m * p : ℕ) : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (b * ((2 * A * a : ℤ) : ℂ)) / p) := by
    intro a b
    rw [← Complex.exp_add]
    have key : 2 * Real.pi * Complex.I * (A * ((m * b + a : ℕ) : ℂ) ^ 2) / ((m * p : ℕ) : ℂ) =
        2 * Real.pi * Complex.I * (A * (a : ℂ) ^ 2) / ((m * p : ℕ) : ℂ) +
          2 * Real.pi * Complex.I * (b * ((2 * A * a : ℤ) : ℂ)) / p +
          ((A * b ^ 2 * p ^ α : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      rw [hmC]
      field_simp
      ring
    rw [key, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => hsplit a b]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm]
  simp_rw [sum_exp_range p]
  -- only `p ∣ a` survives
  have hdiv : ∀ a : ℕ, ((p : ℤ) ∣ 2 * A * a) ↔ ((p : ℤ) ∣ a) := by
    intro a
    have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    constructor
    · intro h
      rcases hp'.dvd_or_dvd h with h' | h'
      · rcases hp'.dvd_or_dvd h' with h'' | h''
        · exfalso
          have : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h''
          have := hp.two_le
          omega
        · exact absurd h'' hA
      · exact h'
    · intro h; exact dvd_mul_of_dvd_right h _
  simp_rw [hdiv, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  -- reindex `a = p w`, `w < p^α`
  have hfilt : (range m).filter (fun a : ℕ => (p : ℤ) ∣ a) = (range (p ^ α)).image (fun w => p * w) := by
    ext a
    simp only [mem_filter, mem_range, mem_image, m]
    constructor
    · rintro ⟨ha, hpa⟩
      obtain ⟨w, hw⟩ := Int.natCast_dvd_natCast.mp hpa
      refine ⟨w, ?_, hw.symm⟩
      rw [hw, pow_succ, mul_comm] at ha
      exact Nat.lt_of_mul_lt_mul_right ha
    · rintro ⟨w, hw, rfl⟩
      refine ⟨by rw [pow_succ, mul_comm]; exact Nat.mul_lt_mul_of_pos_right hw hp.pos, ?_⟩
      exact_mod_cast dvd_mul_right p w
  rw [hfilt, Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp.pos h), Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_comm]
  congr 2
  push_cast
  rw [hmC]
  field_simp
  ring

end ThreeSquares
