/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Construct
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The parameters of the unimodular form

`exists_param`: for `n ≢ 0 (mod 4)` and `n ≢ 7 (mod 8)` there are `a ≥ 1` and `b` with
`a n − 1 > 0` and `a n − 1 ∣ 1 + n b²`. Take a prime `p` in a suitable residue class modulo `4n`
(Dirichlet's theorem, `Nat.forall_exists_prime_gt_and_zmodEq`) so that `n ∣ p + 1` (respectively
`n ∣ 2p + 1`) and `−n` is a square modulo `p` (quadratic reciprocity for the Jacobi symbol); then
`a n − 1 = p` (respectively `2p`).
-/

@[expose] public section

namespace ThreeSquares

/-- `n` is a unit modulo a prime `p` when `n ∣ s p + 1`. -/
theorem natCast_ne_zero_of_dvd {n p : ℕ} (hp : p.Prime) {s : ℤ} (hs : (n : ℤ) ∣ s * p + 1) :
    (n : ZMod p) ≠ 0 := by
  intro h
  have h1 : (p : ℤ) ∣ n := (ZMod.intCast_zmod_eq_zero_iff_dvd (n : ℤ) p).mp (by exact_mod_cast h)
  have h2 : (p : ℤ) ∣ 1 := by
    have := dvd_trans h1 hs
    have h3 : (p : ℤ) ∣ s * p + 1 - s * p := dvd_sub this (dvd_mul_left _ _)
    simpa using h3
  have := Int.eq_one_of_dvd_one (by positivity) h2
  exact hp.one_lt.ne' (by exact_mod_cast this)

/-- A square root of `−n⁻¹` modulo a prime `p` with `p ∤ n` and `J(−n | p) = 1`. -/
theorem exists_b_of_prime {n p : ℕ} (hp : p.Prime) (hn0 : (n : ZMod p) ≠ 0)
    (hJ : jacobiSym (-(n : ℤ)) p = 1) : ∃ b : ℤ, (p : ℤ) ∣ 1 + n * b ^ 2 := by
  have := Fact.mk hp
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJ
  have hr' : r * r = -(n : ZMod p) := by rw [← hr]; push_cast; ring
  set t : ZMod p := r * (n : ZMod p)⁻¹
  have ht : 1 + (n : ZMod p) * t ^ 2 = 0 := by
    calc 1 + (n : ZMod p) * t ^ 2 = 1 + (r * r) * ((n : ZMod p) * (n : ZMod p)⁻¹) *
          (n : ZMod p)⁻¹ := by simp only [t]; ring
      _ = 0 := by rw [hr', mul_inv_cancel₀ hn0, mul_one, neg_mul, mul_inv_cancel₀ hn0]; ring
  refine ⟨(t.val : ℤ), ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  push_cast
  rw [ZMod.natCast_val, ZMod.cast_id', id]
  exact ht

/-- The parameters from a prime `p` with `n ∣ p + 1` and `J(−n | p) = 1`. -/
theorem param_of_prime {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hnp : (n : ℤ) ∣ p + 1)
    (hJ : jacobiSym (-(n : ℤ)) p = 1) :
    ∃ a b : ℤ, 0 < a ∧ 0 < a * n - 1 ∧ a * n - 1 ∣ 1 + n * b ^ 2 := by
  obtain ⟨a, ha⟩ := hnp
  obtain ⟨b, hb⟩ := exists_b_of_prime hp
    (natCast_ne_zero_of_dvd hp (s := 1) ⟨a, by rw [one_mul]; exact ha⟩) hJ
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hn0 : (0 : ℤ) < n := by exact_mod_cast hn
  have hapos : 0 < a := by
    by_contra h
    push Not at h
    have : (n : ℤ) * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hn0.le h
    linarith
  have hd : a * n - 1 = p := by linarith
  exact ⟨a, b, hapos, by rw [hd]; exact hp0, by rw [hd]; exact hb⟩

theorem prime_odd_of_mod_four {p : ℕ} (hp4 : p % 4 = 1) : Odd p :=
  Nat.odd_iff.mpr (by omega)

/-- **Case `n ≡ 1 (mod 4)`.** -/
theorem param_one_mod_four {n : ℕ} (hn : n % 4 = 1) :
    ∃ a b : ℤ, 0 < a ∧ 0 < a * n - 1 ∧ a * n - 1 ∣ 1 + n * b ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 1 := ⟨n / 4, by omega⟩
  have hcop : IsCoprime (2 * ((4 * k + 1 : ℕ) : ℤ) - 1) ((4 * (4 * k + 1) : ℕ) : ℤ) :=
    ⟨2 * ((4 * k + 1 : ℕ) : ℤ) - 1, -(4 * (k : ℤ)), by push_cast; ring⟩
  obtain ⟨p, -, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq 0 (by omega) hcop
  have hdvd : ((4 * (4 * k + 1) : ℕ) : ℤ) ∣ p - (2 * ((4 * k + 1 : ℕ) : ℤ) - 1) :=
    (Int.ModEq.dvd hpmod.symm)
  push_cast at hdvd
  have hnp : ((4 * k + 1 : ℕ) : ℤ) ∣ p + 1 := by
    obtain ⟨m, hm⟩ := hdvd
    exact ⟨4 * m + 2, by push_cast; linarith⟩
  have hp4 : p % 4 = 1 := by
    obtain ⟨m, hm⟩ := hdvd
    have h' : (p : ℤ) = 8 * k + 1 + 4 * ((4 * k + 1) * m) := by linarith
    have : (p : ℤ) % 4 = 1 := by omega
    omega
  refine param_of_prime (by omega) hp hnp ?_
  rw [show -(((4 * k + 1 : ℕ) : ℤ)) = -1 * ((4 * k + 1 : ℕ) : ℤ) by ring, jacobiSym.mul_left,
    jacobiSym.at_neg_one (prime_odd_of_mod_four hp4), ZMod.χ₄_nat_one_mod_four hp4, one_mul,
    ← jacobiSym.quadratic_reciprocity_one_mod_four hp4 (Nat.odd_iff.mpr (by omega))]
  have hmod : (p : ℤ) % ((4 * k + 1 : ℕ) : ℤ) = (-1) % ((4 * k + 1 : ℕ) : ℤ) := by
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    simpa using hnp
  rw [jacobiSym.mod_left' hmod, jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)),
    ZMod.χ₄_nat_one_mod_four (by omega)]

/-- **Case `n ≡ 2 (mod 4)`.** -/
theorem param_two_mod_four {n : ℕ} (hn : n % 4 = 2) :
    ∃ a b : ℤ, 0 < a ∧ 0 < a * n - 1 ∧ a * n - 1 ∣ 1 + n * b ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 2 := ⟨n / 4, by omega⟩
  have hcop : IsCoprime (((4 * k + 2 : ℕ) : ℤ) - 1) ((4 * (4 * k + 2) : ℕ) : ℤ) :=
    ⟨((4 * k + 2 : ℕ) : ℤ) - 1, -(k : ℤ), by push_cast; ring⟩
  obtain ⟨p, -, hp, hpmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq 0 (by omega) hcop
  have hdvd : ((4 * (4 * k + 2) : ℕ) : ℤ) ∣ p - (((4 * k + 2 : ℕ) : ℤ) - 1) :=
    (Int.ModEq.dvd hpmod.symm)
  push_cast at hdvd
  obtain ⟨m, hm⟩ := hdvd
  have hnp : ((4 * k + 2 : ℕ) : ℤ) ∣ p + 1 := ⟨4 * m + 1, by push_cast; linarith⟩
  have hp8 : (p : ℤ) % 8 = (4 * k + 1) % 8 := by
    have h' : (p : ℤ) = 4 * k + 1 + 8 * ((2 * k + 1) * m) := by linarith
    omega
  have hp4 : p % 4 = 1 := by omega
  -- `n = 2 (2k + 1)`
  have hm' : ((2 * k + 1 : ℕ) : ℤ) ∣ p + 1 := by
    obtain ⟨t, ht⟩ := hnp
    exact ⟨2 * t, by push_cast at ht ⊢; linarith⟩
  refine param_of_prime (by omega) hp hnp ?_
  rw [show -(((4 * k + 2 : ℕ) : ℤ)) = -1 * (2 * ((2 * k + 1 : ℕ) : ℤ)) by push_cast; ring,
    jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.at_neg_one (prime_odd_of_mod_four hp4),
    ZMod.χ₄_nat_one_mod_four hp4, one_mul, jacobiSym.at_two (prime_odd_of_mod_four hp4),
    ← jacobiSym.quadratic_reciprocity_one_mod_four hp4 (Nat.odd_iff.mpr (by omega))]
  have hmod : (p : ℤ) % ((2 * k + 1 : ℕ) : ℤ) = (-1) % ((2 * k + 1 : ℕ) : ℤ) := by
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
    apply Int.emod_eq_zero_of_dvd
    simpa using hm'
  rw [jacobiSym.mod_left' hmod, jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)),
    ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₄_nat_eq_if_mod_four]
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have h1 : p % 8 = 1 := by omega
    simp [h1, show p % 2 = 1 by omega, show (2 * (j + j) + 1) % 4 = 1 by omega]
  · have h5 : p % 8 = 5 := by omega
    simp [h5, show p % 2 = 1 by omega, show (2 * (2 * j + 1) + 1) % 4 = 3 by omega]

/-- **Case `n ≡ 3 (mod 8)`.** -/
theorem param_three_mod_eight {n : ℕ} (hn : n % 8 = 3) :
    ∃ a b : ℤ, 0 < a ∧ 0 < a * n - 1 ∧ a * n - 1 ∣ 1 + n * b ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 8 * k + 3 := ⟨n / 8, by omega⟩
  have hcop : IsCoprime ((4 * k + 1 : ℕ) : ℤ) ((4 * (8 * k + 3) : ℕ) : ℤ) :=
    ⟨8 * (k : ℤ) + 1, -(k : ℤ), by push_cast; ring⟩
  obtain ⟨q, hq2, hq, hqmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq 2 (by omega) hcop
  have hdvd : ((4 * (8 * k + 3) : ℕ) : ℤ) ∣ q - ((4 * k + 1 : ℕ) : ℤ) :=
    (Int.ModEq.dvd hqmod.symm)
  push_cast at hdvd
  obtain ⟨m, hm⟩ := hdvd
  have hq4 : q % 4 = 1 := by
    have h' : (q : ℤ) = 4 * k + 1 + 4 * ((8 * k + 3) * m) := by linarith
    have : (q : ℤ) % 4 = 1 := by omega
    omega
  have hnq : ((8 * k + 3 : ℕ) : ℤ) ∣ 2 * q + 1 := ⟨8 * m + 1, by push_cast; linarith⟩
  -- `J(−n | q) = 1`
  have hJ : jacobiSym (-(((8 * k + 3 : ℕ) : ℤ))) q = 1 := by
    have hn_odd : Odd (8 * k + 3) := Nat.odd_iff.mpr (by omega)
    rw [show -(((8 * k + 3 : ℕ) : ℤ)) = -1 * ((8 * k + 3 : ℕ) : ℤ) by ring, jacobiSym.mul_left,
      jacobiSym.at_neg_one (prime_odd_of_mod_four hq4), ZMod.χ₄_nat_one_mod_four hq4, one_mul,
      ← jacobiSym.quadratic_reciprocity_one_mod_four hq4 hn_odd]
    have hmod : (q : ℤ) % ((8 * k + 3 : ℕ) : ℤ) =
        ((4 * k + 1 : ℕ) : ℤ) % ((8 * k + 3 : ℕ) : ℤ) := by
      apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
      apply Int.emod_eq_zero_of_dvd
      exact ⟨4 * m, by push_cast; linarith⟩
    rw [jacobiSym.mod_left' hmod]
    -- `J(2 | n) J((n − 1)/2 | n) = J(−1 | n)`
    have h2 : jacobiSym 2 (8 * k + 3) = -1 := by
      rw [jacobiSym.at_two hn_odd, ZMod.χ₈_nat_eq_if_mod_eight]
      simp [show (8 * k + 3) % 2 = 1 by omega, show (8 * k + 3) % 8 = 3 by omega]
    have hm1 : jacobiSym (-1) (8 * k + 3) = -1 := by
      rw [jacobiSym.at_neg_one hn_odd, ZMod.χ₄_nat_three_mod_four (by omega)]
    have hprod : jacobiSym 2 (8 * k + 3) * jacobiSym ((4 * k + 1 : ℕ) : ℤ) (8 * k + 3) =
        jacobiSym (-1) (8 * k + 3) := by
      rw [← jacobiSym.mul_left]
      apply jacobiSym.mod_left'
      apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
      apply Int.emod_eq_zero_of_dvd
      exact ⟨1, by push_cast; ring⟩
    rw [h2, hm1] at hprod
    linarith
  -- a root modulo `q`, made odd
  obtain ⟨b₀, hb₀⟩ := exists_b_of_prime hq
    (natCast_ne_zero_of_dvd hq (s := 2) (by simpa [mul_comm] using hnq)) hJ
  have hq_odd : Odd (q : ℤ) := by
    have : Odd q := prime_odd_of_mod_four hq4
    exact_mod_cast this
  obtain ⟨b, hb_odd, hqb⟩ : ∃ b : ℤ, Odd b ∧ (q : ℤ) ∣ 1 + ((8 * k + 3 : ℕ) : ℤ) * b ^ 2 := by
    rcases Int.even_or_odd b₀ with hb | hb
    · refine ⟨b₀ + q, hb.add_odd hq_odd, ?_⟩
      have : 1 + ((8 * k + 3 : ℕ) : ℤ) * (b₀ + q) ^ 2 =
          (1 + ((8 * k + 3 : ℕ) : ℤ) * b₀ ^ 2) + q * (((8 * k + 3 : ℕ) : ℤ) * (2 * b₀ + q)) := by
        ring
      rw [this]
      exact dvd_add hb₀ (dvd_mul_right _ _)
    · exact ⟨b₀, hb, hb₀⟩
  have hn_odd : Odd (((8 * k + 3 : ℕ) : ℤ)) := ⟨4 * k + 1, by push_cast; ring⟩
  have h2b : (2 : ℤ) ∣ 1 + ((8 * k + 3 : ℕ) : ℤ) * b ^ 2 :=
    even_iff_two_dvd.mp (odd_one.add_odd (hn_odd.mul (hb_odd.pow)))
  have hcop2 : IsCoprime (2 : ℤ) q := by
    obtain ⟨j, hj⟩ := hq_odd
    exact ⟨-j, 1, by rw [hj]; ring⟩
  have h2q : (2 * q : ℤ) ∣ 1 + ((8 * k + 3 : ℕ) : ℤ) * b ^ 2 := IsCoprime.mul_dvd hcop2 h2b hqb
  obtain ⟨a, ha⟩ := hnq
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hn0 : (0 : ℤ) < ((8 * k + 3 : ℕ) : ℤ) := by positivity
  have hapos : 0 < a := by
    by_contra h
    push Not at h
    have : ((8 * k + 3 : ℕ) : ℤ) * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hn0.le h
    linarith
  have hd : a * ((8 * k + 3 : ℕ) : ℤ) - 1 = 2 * q := by linarith
  exact ⟨a, b, hapos, by rw [hd]; positivity, by rw [hd]; exact h2q⟩

/-- **The parameters.** For `n ≢ 0 (mod 4)` and `n ≢ 7 (mod 8)`. -/
theorem exists_param {n : ℕ} (hn4 : n % 4 ≠ 0) (hn8 : n % 8 ≠ 7) :
    ∃ a b : ℤ, 0 < a ∧ 0 < a * n - 1 ∧ a * n - 1 ∣ 1 + n * b ^ 2 := by
  rcases (by omega : n % 4 = 1 ∨ n % 4 = 2 ∨ n % 8 = 3) with h | h | h
  · exact param_one_mod_four h
  · exact param_two_mod_four h
  · exact param_three_mod_eight h

end ThreeSquares
