/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Arith

/-!
# The three squares theorem

**Gauss–Legendre.** A natural number is a sum of three squares if and only if it is not of the form
`4^a (8 b + 7)` (`sum_three_sq_iff`). Necessity: squares are `0, 1, 4 (mod 8)`, and a sum of three
squares divisible by `4` has all three terms even. Sufficiency: remove factors `4`, then use the
unimodular form of `ThreeSquaresLib.Construct` with the parameters of `ThreeSquaresLib.Arith`.
-/

@[expose] public section

namespace ThreeSquares

theorem sum_three_sq_emod_eight_ne_seven (x y z : ℤ) : (x ^ 2 + y ^ 2 + z ^ 2) % 8 ≠ 7 := by
  have key : ∀ a b c : ZMod 8, a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by decide
  intro h
  apply key x y z
  have h' : ((x ^ 2 + y ^ 2 + z ^ 2 : ℤ) : ZMod 8) = ((7 : ℤ) : ZMod 8) := by
    rw [ZMod.intCast_eq_intCast_iff']
    simpa using h
  push_cast at h'
  exact h'

theorem even_of_sum_three_sq_four_dvd {x y z : ℤ} (h : 4 ∣ x ^ 2 + y ^ 2 + z ^ 2) :
    2 ∣ x ∧ 2 ∣ y ∧ 2 ∣ z := by
  have key : ∀ a b c : ZMod 4, a ^ 2 + b ^ 2 + c ^ 2 = 0 →
      (a = 0 ∨ a = 2) ∧ (b = 0 ∨ b = 2) ∧ (c = 0 ∨ c = 2) := by decide
  have h0 : ((x ^ 2 + y ^ 2 + z ^ 2 : ℤ) : ZMod 4) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr (by exact_mod_cast h)
  push_cast at h0
  have even_of : ∀ w : ℤ, ((w : ZMod 4) = 0 ∨ (w : ZMod 4) = 2) → 2 ∣ w := by
    intro w hw
    rcases hw with hw | hw
    · have : (4 : ℤ) ∣ w := (ZMod.intCast_zmod_eq_zero_iff_dvd w 4).mp hw
      exact dvd_trans (by norm_num) this
    · have hw' : ((w - 2 : ℤ) : ZMod 4) = 0 := by push_cast; rw [hw]; ring
      have : (4 : ℤ) ∣ w - 2 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hw'
      have : (2 : ℤ) ∣ w - 2 := dvd_trans (by norm_num) this
      have := dvd_add this (dvd_refl (2 : ℤ))
      simpa using this
  obtain ⟨hx, hy, hz⟩ := key _ _ _ h0
  exact ⟨even_of x hx, even_of y hy, even_of z hz⟩

/-- **Necessity.** No number of the form `4^a (8 b + 7)` is a sum of three squares. -/
theorem not_sum_three_sq (a b : ℕ) :
    ∀ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 ≠ 4 ^ a * (8 * b + 7) := by
  induction a with
  | zero =>
    intro x y z h
    apply sum_three_sq_emod_eight_ne_seven x y z
    rw [h]
    omega
  | succ a ih =>
    intro x y z h
    have h4 : (4 : ℤ) ∣ x ^ 2 + y ^ 2 + z ^ 2 := by
      rw [h]; exact ⟨4 ^ a * (8 * b + 7), by ring⟩
    obtain ⟨⟨x', rfl⟩, ⟨y', rfl⟩, ⟨z', rfl⟩⟩ := even_of_sum_three_sq_four_dvd h4
    apply ih x' y' z'
    have : 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) = 4 * (4 ^ a * (8 * b + 7)) := by
      rw [← mul_assoc, ← pow_succ']
      linarith [h]
    linarith

/-- **Sufficiency.** A natural number not of the form `4^a (8 b + 7)` is a sum of three squares. -/
theorem sum_three_sq_of_not (n : ℕ) (h : ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, 0, 0, by norm_num⟩
    by_cases h4 : n % 4 = 0
    · obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m := ⟨n / 4, by omega⟩
      have hm : ¬ ∃ a b : ℕ, m = 4 ^ a * (8 * b + 7) := by
        rintro ⟨a, b, rfl⟩
        exact h ⟨a + 1, b, by ring⟩
      obtain ⟨x, y, z, hxyz⟩ := ih m (by omega) hm
      exact ⟨2 * x, 2 * y, 2 * z, by push_cast; rw [← hxyz]; ring⟩
    · have h8 : n % 8 ≠ 7 := by
        intro h8
        exact h ⟨0, n / 8, by omega⟩
      obtain ⟨a, b, ha, hd, hdvd⟩ := exists_param h4 h8
      exact sum_three_sq_of_dvd n ha hd hdvd

/-- **The three squares theorem (Gauss–Legendre).** -/
theorem sum_three_sq_iff (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) ↔ ¬ ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7) := by
  constructor
  · rintro ⟨x, y, z, hxyz⟩ ⟨a, b, rfl⟩
    exact not_sum_three_sq a b x y z (by exact_mod_cast hxyz)
  · intro h
    obtain ⟨x, y, z, hxyz⟩ := sum_three_sq_of_not n h
    refine ⟨x.natAbs, y.natAbs, z.natAbs, ?_⟩
    have : ((x.natAbs ^ 2 + y.natAbs ^ 2 + z.natAbs ^ 2 : ℕ) : ℤ) = n := by
      push_cast
      rw [sq_abs, sq_abs, sq_abs]
      exact hxyz
    exact_mod_cast this

/-- Every `n ≡ 3 (mod 8)` is a sum of three integer squares. -/
theorem exists_sum_sq_of_mod_eight_eq_three (n : ℕ) (hn : n % 8 = 3) :
    ∃ x : Fin 3 → ℤ, ∑ i, x i ^ 2 = n := by
  obtain ⟨x, y, z, hxyz⟩ := sum_three_sq_of_not n (by
    rintro ⟨a, b, rfl⟩
    rcases a with _ | a
    · simp at hn
    · have h4 : 4 ∣ 4 ^ (a + 1) * (8 * b + 7) := ⟨4 ^ a * (8 * b + 7), by ring⟩
      omega)
  exact ⟨![x, y, z], by simp [Fin.sum_univ_three, hxyz]⟩

end ThreeSquares
