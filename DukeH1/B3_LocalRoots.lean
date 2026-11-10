/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.B3_RepCount
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Data.ZMod.QuotientRing

/-!
# Square roots of `−n` modulo `k`

* `sig n k = #{x ∈ ℤ/k : x² + n = 0}`; `sig_one`, `sig_mul` (multiplicative, CRT).
* `hensel_root`: for an odd prime `p ∤ n` and a root of `b² + n` modulo `p`, a root modulo
  every `p^k`.
* `two_le_sig`: `2 ≤ sig n (p^k)` (`k ≥ 1`) when `J(−n | p) = 1`.
* `sig_le_rootCount`: for odd `k` and `n ≡ 3 (mod 8)`, `sig n k ≤ rootCount n k`
  (`x ↦ B ∈ [0, 2k)` odd with `B ≡ x (mod k)`; then `4k ∣ B² + n`).
-/

@[expose] public section

namespace ThreeSquares.B3

open Finset

/-- `#{x ∈ ℤ/k : x² + n = 0}`. -/
noncomputable def sig (n k : ℕ) : ℕ := Nat.card {x : ZMod k // x ^ 2 + n = 0}

theorem sig_one (n : ℕ) : sig n 1 = 1 := by
  unfold sig
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨0, Subsingleton.elim _ _⟩⟩⟩

theorem sig_mul (n : ℕ) {a b : ℕ} (h : a.Coprime b) : sig n (a * b) = sig n a * sig n b := by
  unfold sig
  rw [← Nat.card_prod]
  apply Nat.card_congr
  refine ((ZMod.chineseRemainder h).toEquiv.subtypeEquiv
    (q := fun y : ZMod a × ZMod b => y.1 ^ 2 + n = 0 ∧ y.2 ^ 2 + n = 0) ?_).trans
    (Equiv.subtypeProdEquivProd (p := fun x : ZMod a => x ^ 2 + n = 0)
      (q := fun x : ZMod b => x ^ 2 + n = 0))
  intro x
  have e : ZMod.chineseRemainder h (x ^ 2 + n) =
      ((ZMod.chineseRemainder h x).1 ^ 2 + n, (ZMod.chineseRemainder h x).2 ^ 2 + n) := by
    rw [map_add, map_pow, map_natCast]
    rfl
  constructor
  · intro hx
    have := congrArg (ZMod.chineseRemainder h) hx
    rw [e, map_zero] at this
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · rintro ⟨h1, h2⟩
    apply (ZMod.chineseRemainder h).injective
    rw [e, map_zero]
    exact Prod.ext h1 h2

theorem not_dvd_of_root {n p : ℕ} (hpn : ¬ p ∣ n) {b : ℤ} (hb : (p : ℤ) ∣ b ^ 2 + n) :
    ¬ (p : ℤ) ∣ b := by
  intro h
  apply hpn
  have : (p : ℤ) ∣ b ^ 2 := dvd_pow h two_ne_zero
  have : (p : ℤ) ∣ (n : ℤ) := by
    have := dvd_sub hb this
    simpa using this
  exact_mod_cast this

theorem isCoprime_two_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) :
    IsCoprime (2 * c) (p : ℤ) := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have h2 : ¬ (p : ℤ) ∣ 2 * c := by
    intro h
    rcases hpi.dvd_or_dvd h with h | h
    · have : p ∣ 2 := by exact_mod_cast h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
      exact hp2 this
    · exact hc h
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
  have : Nat.Coprime p (2 * c).natAbs := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    exact h2 (Int.natCast_dvd.mpr h)
  simpa [Int.gcd] using this

/-- **Hensel.** -/
theorem hensel_root {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) {b : ℤ}
    (hb : (p : ℤ) ∣ b ^ 2 + n) :
    ∀ j : ℕ, ∃ c : ℤ, (p : ℤ) ^ (j + 1) ∣ c ^ 2 + n ∧ (p : ℤ) ∣ c - b := by
  intro j
  induction j with
  | zero => exact ⟨b, by simpa using hb, by simp⟩
  | succ j ih =>
    obtain ⟨c, ⟨u, hu⟩, hcb⟩ := ih
    have hc : ¬ (p : ℤ) ∣ c := by
      intro h
      apply not_dvd_of_root hpn hb
      have := dvd_sub h hcb
      simpa using this
    obtain ⟨α, β, hαβ⟩ := isCoprime_two_mul hp hp2 hc
    refine ⟨c + (-u * α) * (p : ℤ) ^ (j + 1), ⟨u * β + (u * α) ^ 2 * (p : ℤ) ^ j, ?_⟩, ?_⟩
    · linear_combination hu - (p : ℤ) ^ (j + 1) * u * hαβ
    · have : (p : ℤ) ∣ (-u * α) * (p : ℤ) ^ (j + 1) :=
        Dvd.dvd.mul_left (dvd_pow_self _ (Nat.succ_ne_zero j)) _
      have := dvd_add hcb this
      convert this using 1
      ring

theorem two_le_sig {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n)
    (hJ : jacobiSym (-(n : ℤ)) p = 1) (j : ℕ) : 2 ≤ sig n (p ^ (j + 1)) := by
  have := Fact.mk hp
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJ
  have hb : (p : ℤ) ∣ (r.val : ℤ) ^ 2 + n := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id', id, sq, ← hr]
    push_cast
    ring
  obtain ⟨c, hc, hcb⟩ := hensel_root hp hp2 hpn hb j
  have hcp : ¬ (p : ℤ) ∣ c := by
    intro h
    apply not_dvd_of_root hpn hb
    have := dvd_sub h hcb
    simpa using this
  set q := p ^ (j + 1)
  have hq0 : q ≠ 0 := pow_ne_zero _ hp.ne_zero
  haveI : NeZero q := ⟨hq0⟩
  have hroot : ∀ d : ℤ, (q : ℤ) ∣ d ^ 2 + n → ((d : ZMod q)) ^ 2 + n = 0 := by
    intro d hd
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (d ^ 2 + n) q).mpr hd
    push_cast at this
    exact this
  have hq : (q : ℤ) = (p : ℤ) ^ (j + 1) := by simp [q]
  have h1 := hroot c (by rw [hq]; exact hc)
  have h2 := hroot (-c) (by rw [hq]; simpa using hc)
  have hne : ((c : ZMod q)) ≠ ((-c : ℤ) : ZMod q) := by
    intro h
    have : ((2 * c : ℤ) : ZMod q) = 0 := by
      push_cast at h ⊢
      linear_combination h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hq] at this
    have : (p : ℤ) ∣ 2 * c := dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero j)) this
    have hu := (isCoprime_two_mul hp hp2 hcp).isUnit_of_dvd' this (dvd_refl _)
    have h1 := hp.one_lt
    rcases Int.isUnit_iff.mp hu with h | h <;> omega
  unfold sig
  have : Nontrivial {x : ZMod q // x ^ 2 + n = 0} := ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, fun h => hne (congrArg
    Subtype.val h)⟩⟩
  exact Finite.one_lt_card_iff_nontrivial.mpr this

theorem four_dvd_of_odd {n : ℕ} (hn : n % 8 = 3) {B : ℤ} (hB : Odd B) : (4 : ℤ) ∣ B ^ 2 + n := by
  obtain ⟨j, rfl⟩ := hB
  have e : (2 * j + 1) ^ 2 + (n : ℤ) = 4 * (j ^ 2 + j) + (1 + n) := by ring
  rw [e]
  refine dvd_add (dvd_mul_right _ _) ?_
  omega

theorem sig_le_rootCount {n k : ℕ} (hn : n % 8 = 3) (hk : Odd k) : sig n k ≤ rootCount n k := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  haveI : NeZero k := ⟨hk0⟩
  let S := (Ico (0 : ℤ) (2 * k)).filter (fun b => (4 * k : ℤ) ∣ b ^ 2 + n)
  let B : ZMod k → ℤ := fun x => if Odd (x.val : ℤ) then (x.val : ℤ) else (x.val : ℤ) + k
  have hBcast : ∀ x : ZMod k, ((B x : ℤ) : ZMod k) = x := by
    intro x
    simp only [B]
    split_ifs <;> simp
  have hBodd : ∀ x : ZMod k, Odd (B x) := by
    intro x
    simp only [B]
    split_ifs with h
    · exact h
    · have hk' : Odd (k : ℤ) := by exact_mod_cast hk
      rw [Int.not_odd_iff_even] at h
      exact h.add_odd hk'
  have hBrange : ∀ x : ZMod k, 0 ≤ B x ∧ B x < 2 * k := by
    intro x
    have := ZMod.val_lt x
    simp only [B]
    split_ifs <;> constructor <;> omega
  have hcop : IsCoprime (4 : ℤ) k := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime 4 k := by
      have : Nat.Coprime 2 k := (Nat.coprime_two_left).mpr hk
      exact Nat.Coprime.pow_left 2 this
    simpa [Int.gcd] using this
  let φ : {x : ZMod k // x ^ 2 + n = 0} → S := fun x => ⟨B x.1, by
    rw [mem_filter, mem_Ico]
    refine ⟨hBrange x.1, ?_⟩
    have hk' : (k : ℤ) ∣ B x.1 ^ 2 + n := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).mp
      push_cast
      rw [hBcast]
      exact x.2
    exact hcop.mul_dvd (four_dvd_of_odd hn (hBodd x.1)) hk'⟩
  have hφ : Function.Injective φ := by
    intro x y h
    have : B x.1 = B y.1 := congrArg Subtype.val h
    apply Subtype.ext
    rw [← hBcast x.1, ← hBcast y.1, this]
  unfold sig rootCount
  have := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_eq_finsetCard] at this

end ThreeSquares.B3
