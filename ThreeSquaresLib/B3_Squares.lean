/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.B3_Asymp
public import Mathlib.Data.Nat.Squarefree

/-!
# Square roots modulo a squarefree `n`, and the good classes

* `card_sq_eq_one_le`: `#{u ∈ ℤ/n : u² = 1} ≤ d(n)` for squarefree `n` (`u ↦ gcd(u − 1, n)` is
  injective: `u ≡ 1 (mod d)`, `u ≡ −1 (mod n/d)`).
* `card_half_sq_le`: `#{z unit : −z²/2 = w} ≤ d(n)`.
* `good_of_class`: if `m ≡ −z²/2 (mod n)` for a unit `z`, then `m` is coprime to `n` and
  `n ∣ 2t²m + 1` for some `t`.
-/

@[expose] public section

namespace ThreeSquares.B3

open Finset

theorem card_sq_eq_one_le {n : ℕ} [NeZero n] (hsq : Squarefree n) :
    (univ.filter (fun u : ZMod n => u ^ 2 = 1)).card ≤ n.divisors.card := by
  have hn0 : n ≠ 0 := NeZero.ne n
  refine card_le_card_of_injOn (fun u : ZMod n => Int.gcd ((u.val : ℤ) - 1) n) ?_ ?_
  · intro u _
    rw [mem_coe, Nat.mem_divisors]
    refine ⟨?_, hn0⟩
    have := Int.gcd_dvd_right ((u.val : ℤ) - 1) n
    exact_mod_cast this
  · -- the key facts for one `u`
    have key : ∀ u : ZMod n, u ^ 2 = 1 →
        let d := Int.gcd ((u.val : ℤ) - 1) n
        (d : ℤ) ∣ (u.val : ℤ) - 1 ∧ ((n / d : ℕ) : ℤ) ∣ (u.val : ℤ) + 1 ∧ d * (n / d) = n := by
      intro u hu d
      have hdn : d ∣ n := by
        have := Int.gcd_dvd_right ((u.val : ℤ) - 1) n
        exact_mod_cast this
      have hde : d * (n / d) = n := Nat.mul_div_cancel' hdn
      have hcop : d.Coprime (n / d) := Nat.coprime_of_squarefree_mul (by rw [hde]; exact hsq)
      refine ⟨Int.gcd_dvd_left _ _, ?_, hde⟩
      have hsq1 : (n : ℤ) ∣ ((u.val : ℤ) - 1) * ((u.val : ℤ) + 1) := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp
        push_cast
        rw [ZMod.natCast_val, ZMod.cast_id', id]
        linear_combination hu
      have he : ((n / d : ℕ) : ℤ) ∣ ((u.val : ℤ) - 1) * ((u.val : ℤ) + 1) :=
        dvd_trans (by exact_mod_cast Nat.div_dvd_of_dvd hdn) hsq1
      have hc : IsCoprime ((n / d : ℕ) : ℤ) ((u.val : ℤ) - 1) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        set g := Int.gcd ((n / d : ℕ) : ℤ) ((u.val : ℤ) - 1)
        have g1 : g ∣ n / d := by
          have := Int.gcd_dvd_left ((n / d : ℕ) : ℤ) ((u.val : ℤ) - 1)
          exact_mod_cast this
        have g2 : (g : ℤ) ∣ (u.val : ℤ) - 1 := Int.gcd_dvd_right _ _
        have g1' : (g : ℤ) ∣ ((n / d : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr g1
        have hnd : ((n / d : ℕ) : ℤ) ∣ (n : ℤ) :=
          Int.natCast_dvd_natCast.mpr (Nat.div_dvd_of_dvd hdn)
        have g3 : g ∣ d := Int.dvd_gcd g2 (dvd_trans g1' hnd)
        exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left g3 hcop) g1
      exact hc.dvd_of_dvd_mul_left he
    intro u hu u' hu' h
    rw [mem_coe, mem_filter] at hu hu'
    obtain ⟨h1, h2, h3⟩ := key u hu.2
    obtain ⟨h1', h2', -⟩ := key u' hu'.2
    simp only at h h1' h2'
    rw [← h] at h1' h2'
    set d := Int.gcd ((u.val : ℤ) - 1) n
    have hcop : d.Coprime (n / d) := Nat.coprime_of_squarefree_mul (by rw [h3]; exact hsq)
    have hA : (d : ℤ) ∣ (u.val : ℤ) - u'.val := by
      have := dvd_sub h1 h1'
      convert this using 1; ring
    have hB : ((n / d : ℕ) : ℤ) ∣ (u.val : ℤ) - u'.val := by
      have := dvd_sub h2 h2'
      convert this using 1; ring
    have hN : (n : ℤ) ∣ (u.val : ℤ) - u'.val := by
      have := (Nat.isCoprime_iff_coprime.mpr hcop).mul_dvd hA hB
      rwa [← Nat.cast_mul, h3] at this
    have h5 : ((u.val : ℤ) : ZMod n) = ((u'.val : ℤ) : ZMod n) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).mpr (by rw [← neg_sub]; exact dvd_neg.mpr hN)
    rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h5
    exact h5

theorem card_half_sq_le {n : ℕ} [NeZero n] (hsq : Squarefree n) (hodd : Odd n) (w : ZMod n) :
    (univ.filter (fun z : ZMod n => IsUnit z ∧ -z ^ 2 * 2⁻¹ = w)).card ≤ n.divisors.card := by
  by_cases hne : (univ.filter (fun z : ZMod n => IsUnit z ∧ -z ^ 2 * 2⁻¹ = w)).Nonempty
  · obtain ⟨z₀, hz₀⟩ := hne
    rw [mem_filter] at hz₀
    obtain ⟨-, hu₀, hw₀⟩ := hz₀
    have h2 := isUnit_two hodd
    refine le_trans (card_le_card_of_injOn (fun z => z * z₀⁻¹) ?_ ?_) (card_sq_eq_one_le hsq)
    · intro z hz
      rw [mem_coe, mem_filter] at hz ⊢
      refine ⟨mem_univ _, ?_⟩
      obtain ⟨-, -, hw⟩ := hz
      have hzz : z ^ 2 = z₀ ^ 2 := by
        have : -z ^ 2 * 2⁻¹ * 2 = -z₀ ^ 2 * 2⁻¹ * 2 := by rw [hw, hw₀]
        rwa [mul_assoc, mul_assoc, ZMod.inv_mul_of_unit _ h2, mul_one, mul_one, neg_inj] at this
      rw [mul_pow, hzz, ← mul_pow, ZMod.mul_inv_of_unit _ hu₀, one_pow]
    · intro z _ z' _ h
      have := congrArg (· * z₀) h
      simp only [mul_assoc, ZMod.inv_mul_of_unit _ hu₀, mul_one] at this
      exact this
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty]
    exact Nat.zero_le _

theorem good_of_class {n : ℕ} [NeZero n] (hodd : Odd n) {m : ℕ} {z : ZMod n} (hz : IsUnit z)
    (hm : (m : ZMod n) = -z ^ 2 * 2⁻¹) :
    m.Coprime n ∧ ∃ t : ℤ, (n : ℤ) ∣ 2 * t ^ 2 * m + 1 := by
  have h2 := isUnit_two hodd
  constructor
  · rw [← ZMod.isUnit_iff_coprime, hm]
    exact ((hz.pow 2).neg).mul ⟨⟨2⁻¹, 2, ZMod.inv_mul_of_unit _ h2, ZMod.mul_inv_of_unit _ h2⟩, rfl⟩
  · refine ⟨((z⁻¹ : ZMod n).val : ℤ), ?_⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id', id, hm]
    have e1 : (2 : ZMod n) * 2⁻¹ = 1 := ZMod.mul_inv_of_unit _ h2
    have e2 : z * z⁻¹ = 1 := ZMod.mul_inv_of_unit _ hz
    linear_combination (-(z * z⁻¹) ^ 2) * e1 - (z * z⁻¹ + 1) * e2

end ThreeSquares.B3
