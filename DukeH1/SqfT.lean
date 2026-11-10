/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.TSum
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Data.Nat.Factorization.Induction

/-!
# `T_q` for squarefree `q`

For odd squarefree `q` coprime to `N` and `U` coprime to `q`:
`T_q(U, N) = J(−N | q) · q · ∑_{y² ≡ 4N² (mod q)} e_q(U y)` (`Tq_squarefree`).
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open ZMod Finset

/-- The root sum `∑_{y² = 4N²} e_q(U y)`. -/
noncomputable def Rq (q : ℕ) [NeZero q] (U N : ℤ) : ℂ :=
  ∑ y : ZMod q, if y ^ 2 = 4 * (N : ZMod q) ^ 2 then (stdAddChar ((U : ZMod q) * y) : ℂ) else 0

/-- The CRT splitting of `e_{rs}`. -/
theorem stdAddChar_crt {r s : ℕ} [NeZero r] [NeZero s] (h : r.Coprime s) (r' s' : ℤ)
    (hb : s' * s + r' * r = 1) (y : ZMod (r * s)) :
    (stdAddChar y : ℂ) = stdAddChar ((s' : ZMod r) * ((ZMod.chineseRemainder h) y).1) *
      stdAddChar ((r' : ZMod s) * ((ZMod.chineseRemainder h) y).2) := by
  set e := ZMod.chineseRemainder h
  have h1 : (e y).1 = ((y.val : ℕ) : ZMod r) := by
    have : (e y).1 = ((RingHom.fst _ _).comp e.toRingHom) y := rfl
    rw [this]; conv_lhs => rw [← ZMod.natCast_zmod_val y]
    rw [map_natCast]
  have h2 : (e y).2 = ((y.val : ℕ) : ZMod s) := by
    have : (e y).2 = ((RingHom.snd _ _).comp e.toRingHom) y := rfl
    rw [this]; conv_lhs => rw [← ZMod.natCast_zmod_val y]
    rw [map_natCast]
  have hy : y = ((y.val : ℤ) : ZMod (r * s)) := by simp
  rw [h1, h2]
  conv_lhs => rw [hy]
  rw [stdAddChar_mul_split r' s' hb]
  push_cast
  ring_nf

theorem Rq_mul {r s : ℕ} [NeZero r] [NeZero s] (h : r.Coprime s) (r' s' : ℤ)
    (hb : s' * s + r' * r = 1) (U N : ℤ) :
    Rq (r * s) U N = Rq r (s' * U) N * Rq s (r' * U) N := by
  classical
  set e := ZMod.chineseRemainder h
  unfold Rq
  rw [sum_mul_sum, ← Fintype.sum_prod_type', ← (e.toEquiv).sum_comp]
  refine Fintype.sum_congr _ _ fun y => ?_
  simp only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv]
  let φ₁ : ZMod (r * s) →+* ZMod r := (RingHom.fst _ _).comp e.toRingHom
  let φ₂ : ZMod (r * s) →+* ZMod s := (RingHom.snd _ _).comp e.toRingHom
  have hcond : y ^ 2 = 4 * (N : ZMod (r * s)) ^ 2 ↔
      (e y).1 ^ 2 = 4 * (N : ZMod r) ^ 2 ∧ (e y).2 ^ 2 = 4 * (N : ZMod s) ^ 2 := by
    have h1 : ∀ z, (e z).1 = φ₁ z := fun z => rfl
    have h2 : ∀ z, (e z).2 = φ₂ z := fun z => rfl
    rw [h1, h2]
    constructor
    · intro hy
      refine ⟨?_, ?_⟩
      · have := congrArg φ₁ hy; simpa [map_ofNat φ₁ 4] using this
      · have := congrArg φ₂ hy; simpa [map_ofNat φ₂ 4] using this
    · rintro ⟨hy1, hy2⟩
      apply e.injective
      ext
      · rw [h1, h1]; simpa [map_ofNat φ₁ 4] using hy1
      · rw [h2, h2]; simpa [map_ofNat φ₂ 4] using hy2
  by_cases hc : y ^ 2 = 4 * (N : ZMod (r * s)) ^ 2
  · obtain ⟨h1, h2⟩ := hcond.mp hc
    rw [if_pos hc, if_pos h1, if_pos h2, stdAddChar_crt h r' s' hb]
    have he : e ((U : ZMod (r * s)) * y) = ((U : ZMod r) * (e y).1, (U : ZMod s) * (e y).2) := by
      rw [map_mul, map_intCast]; rfl
    rw [he]
    push_cast
    ring_nf
  · rw [if_neg hc]
    by_cases h1 : (e y).1 ^ 2 = 4 * (N : ZMod r) ^ 2
    · rw [if_pos h1, if_neg (fun h2 => hc (hcond.mpr ⟨h1, h2⟩)), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem chi_eq_jacobi {p : ℕ} [Fact p.Prime] (N : ℤ) :
    PT.chi p ((N : ZMod p)) = (jacobiSym N p : ℂ) := by
  rw [PT.chi_apply, ← jacobiSym.legendreSym.to_jacobiSym]
  rfl

theorem Rq_prime {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (U N : ℤ) (hN : (N : ZMod p) ≠ 0) :
    Rq p U N = stdAddChar (2 * ((U : ZMod p) * (N : ZMod p))) +
      stdAddChar (-2 * ((U : ZMod p) * (N : ZMod p))) := by
  classical
  have h2 := PT.two_ne_zero' hp2
  have hne : (2 * (N : ZMod p)) ≠ -2 * (N : ZMod p) := by
    intro h; have : 4 * (N : ZMod p) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h4 | h4
    · exact h2 (by have : (2 : ZMod p) * 2 = 0 := by linear_combination h4
                   exact mul_self_eq_zero.mp this)
    · exact hN h4
  unfold Rq
  rw [← Finset.sum_filter, show univ.filter (fun y : ZMod p => y ^ 2 = 4 * (N : ZMod p) ^ 2) =
    {2 * (N : ZMod p), -2 * (N : ZMod p)} by
      ext y; simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · intro hy
        have : (y - 2 * N) * (y + 2 * N) = 0 := by linear_combination hy
        rcases mul_eq_zero.mp this with h | h
        · left; linear_combination h
        · right; linear_combination h
      · rintro (rfl | rfl) <;> ring,
    sum_pair hne]
  congr 1 <;> congr 1 <;> ring

theorem Tq_one (U N : ℤ) : Tq 1 (U : ZMod 1) (N : ZMod 1) = 1 := by
  have hz : ∀ z : ZMod 1, z = 0 := fun z => Subsingleton.elim _ _
  unfold Tq
  simp only [hz, Finset.sum_const, Finset.card_univ, ZMod.card, AddChar.map_zero_eq_one, one_smul,
    nsmul_eq_mul, mul_one]
  rw [ZMod.card_units_eq_totient]; simp

theorem Rq_one (U N : ℤ) : Rq 1 U N = 1 := by
  have hz : ∀ z : ZMod 1, z = 0 := fun z => Subsingleton.elim _ _
  unfold Rq
  simp [hz]

theorem ne_zero_of_coprime {p : ℕ} (hp : p.Prime) {M : ℤ} (hM : IsCoprime M p) :
    (M : ZMod p) ≠ 0 := by
  intro h0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  have h1 := Int.isCoprime_iff_gcd_eq_one.mp hM
  have hd : (p : ℤ) ∣ (Int.gcd M p : ℤ) := Int.dvd_coe_gcd h0 dvd_rfl
  rw [h1] at hd; norm_cast at hd
  exact hp.one_lt.ne' (Nat.dvd_one.mp hd)

theorem Tq_sqf_prime {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (N U : ℤ) (hN : IsCoprime N p)
    (hU : IsCoprime U p) :
    Tq p (U : ZMod p) (N : ZMod p) = (jacobiSym (-N) p : ℂ) * p * Rq p U N := by
  have hNp := ne_zero_of_coprime hp.out hN
  have hUp := ne_zero_of_coprime hp.out hU
  rw [Tq_prime hp2 hUp hNp, Rq_prime hp2 U N hNp,
    show -(N : ZMod p) = ((-N : ℤ) : ZMod p) by push_cast; ring, chi_eq_jacobi]

/-- **`T_q` for squarefree odd `q` coprime to `N`.** -/
theorem Tq_squarefree_aux (N : ℤ) (q : ℕ) (hsq : Squarefree q) (hodd : Odd q)
    (hN : IsCoprime N q) (U : ℤ) (hU : IsCoprime U q) :
    haveI : NeZero q := ⟨hsq.ne_zero⟩
    Tq q (U : ZMod q) (N : ZMod q) = (jacobiSym (-N) q : ℂ) * q * Rq q U N := by
  induction q using Nat.strong_induction_on generalizing U with
  | _ q ih =>
  haveI : NeZero q := ⟨hsq.ne_zero⟩
  rcases eq_or_ne q 1 with rfl | hq1
  · rw [Tq_one, Rq_one]; simp
  · set p := q.minFac
    have hp : p.Prime := Nat.minFac_prime hq1
    obtain ⟨m, hm⟩ : p ∣ q := Nat.minFac_dvd q
    clear_value p
    have hpm : p.Coprime m := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      rintro ⟨t, rfl⟩
      have : p * p ∣ q := ⟨t, by rw [hm]; ring⟩
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p this))
    have hq0 : q ≠ 0 := NeZero.ne q
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hq0 hm
    haveI : NeZero m := ⟨hm0⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      intro h2; rw [hm, h2] at hodd; exact (Nat.not_even_iff_odd.mpr hodd) (even_two_mul m)
    have hmq : m < q := by
      rw [hm]; have := hp.two_le
      calc m = 1 * m := (one_mul m).symm
        _ < p * m := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hm0)
    obtain ⟨r', s', hb'⟩ := Nat.isCoprime_iff_coprime.mpr hpm
    have hb : s' * m + r' * p = 1 := by linear_combination hb'
    have hq' : (q : ℤ) = p * m := by rw [hm]; push_cast; ring
    rw [hq'] at hN hU
    have hNp : IsCoprime N p := hN.of_mul_right_left
    have hNm : IsCoprime N m := hN.of_mul_right_right
    have hUp : IsCoprime U p := hU.of_mul_right_left
    have hUm : IsCoprime U m := hU.of_mul_right_right
    have hsp : IsCoprime s' p := ⟨m, r', by linear_combination hb⟩
    have hrm : IsCoprime r' m := ⟨p, s', by linear_combination hb⟩
    have hsqm : Squarefree m := by rw [hm] at hsq; exact hsq.of_mul_right
    have hoddm : Odd m := by rw [hm] at hodd; exact Nat.Odd.of_mul_right hodd
    subst hm
    rw [Tq_mul hpm r' s' hb U N, Tq_sqf_prime hp2 N (s' * U) hNp (hsp.mul_left hUp),
      ih m hmq hsqm hoddm hNm (r' * U) (hrm.mul_left hUm), Rq_mul hpm r' s' hb U N,
      jacobiSym.mul_right]
    push_cast
    ring

theorem Tq_squarefree (N : ℤ) (q : ℕ) [NeZero q] (hsq : Squarefree q) (hodd : Odd q)
    (hN : IsCoprime N q) (U : ℤ) (hU : IsCoprime U q) :
    Tq q (U : ZMod q) (N : ZMod q) = (jacobiSym (-N) q : ℂ) * q * Rq q U N :=
  Tq_squarefree_aux N q hsq hodd hN U hU

end ThreeSquares
