/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.PrimePowT

/-!
# `T_q` for odd `q` coprime to `N`

For odd `q` coprime to `N` and `U` coprime to `q`:
`T_q(U, N) = J(−N | q) · q · ∑_{y² ≡ 4N² (mod q)} e_q(U y)` (`Tq_coprime`).
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open ZMod Finset

theorem isUnit_of_cast_ne_zero {p : ℕ} [hp : Fact p.Prime] (α : ℕ) [NeZero (p ^ α)]
    (hpq : p ∣ p ^ α) (x : ZMod (p ^ α)) (hx : ZMod.castHom hpq (ZMod p) x ≠ 0) : IsUnit x := by
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime]
  refine Nat.Coprime.pow_right _ ?_
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro hd
  apply hx
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr hd

theorem Rq_prime_pow {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (U N : ℤ) (hN : (N : ZMod p) ≠ 0)
    (α : ℕ) (hα : 1 ≤ α) :
    haveI : NeZero (p ^ α) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    Rq (p ^ α) U N = stdAddChar ((2 * (U * N) : ℤ) : ZMod (p ^ α)) +
      stdAddChar ((-2 * (U * N) : ℤ) : ZMod (p ^ α)) := by
  classical
  haveI : NeZero (p ^ α) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hpq : p ∣ p ^ α := dvd_pow_self p (by omega)
  set f := ZMod.castHom hpq (ZMod p)
  have h2 := PT.two_ne_zero' hp2
  have h4 : (4 : ZMod p) * (N : ZMod p) ≠ 0 := by
    refine mul_ne_zero ?_ hN
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hfN : f (N : ZMod (p ^ α)) = (N : ZMod p) := map_intCast f N
  have hne : (2 * (N : ZMod (p ^ α))) ≠ -2 * (N : ZMod (p ^ α)) := by
    intro h
    apply h4
    have h' := congrArg f h
    simp only [map_mul, map_neg, map_ofNat, hfN] at h'
    linear_combination h'
  unfold Rq
  rw [← Finset.sum_filter, show univ.filter
      (fun y : ZMod (p ^ α) => y ^ 2 = 4 * (N : ZMod (p ^ α)) ^ 2) =
      {2 * (N : ZMod (p ^ α)), -2 * (N : ZMod (p ^ α))} by
      ext y; simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · intro hy
        have hprod : (y - 2 * N) * (y + 2 * N) = 0 := by linear_combination hy
        have hdiff : f (y + 2 * N) - f (y - 2 * N) = 4 * (N : ZMod p) := by
          simp only [map_add, map_sub, map_mul, map_ofNat, hfN]; ring
        by_cases ha : f (y - 2 * N) = 0
        · have hb : f (y + 2 * N) ≠ 0 := by
            intro hb; rw [ha, hb] at hdiff; exact h4 (by linear_combination -hdiff)
          have hu := isUnit_of_cast_ne_zero α hpq _ hb
          left
          have := (hu.mul_left_eq_zero).mp hprod
          linear_combination this
        · have hu := isUnit_of_cast_ne_zero α hpq _ ha
          right
          have := (hu.mul_right_eq_zero).mp hprod
          linear_combination this
      · rintro (rfl | rfl) <;> ring,
    sum_pair hne]
  congr 1 <;> congr 1 <;> push_cast <;> ring

theorem not_dvd_of_coprime {p : ℕ} (hp : p.Prime) {M : ℤ} (hM : IsCoprime M p) :
    ¬ (p : ℤ) ∣ M := by
  intro h
  exact ne_zero_of_coprime hp hM ((ZMod.intCast_zmod_eq_zero_iff_dvd M p).mpr h)

theorem Tq_prime_pow_J {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (N U : ℤ) (hN : IsCoprime N p)
    (hU : IsCoprime U p) (α : ℕ) :
    haveI : NeZero (p ^ α) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    Tq (p ^ α) (U : ZMod (p ^ α)) (N : ZMod (p ^ α)) =
      (jacobiSym (-N) (p ^ α) : ℂ) * (p ^ α : ℕ) * Rq (p ^ α) U N := by
  haveI : NeZero (p ^ α) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rcases Nat.eq_zero_or_pos α with h0 | hα
  · have key : ∀ (q : ℕ) [NeZero q], q = 1 → Tq q (U : ZMod q) (N : ZMod q) =
        (jacobiSym (-N) q : ℂ) * (q : ℕ) * Rq q U N := by
      intro q _ hq; subst hq; rw [Tq_one, Rq_one]; simp
    exact key _ (by rw [h0, pow_zero])
  rw [Tq_prime_pow hp2 N U (not_dvd_of_coprime hp.out hN) (not_dvd_of_coprime hp.out hU) α hα,
    Rq_prime_pow hp2 U N (ne_zero_of_coprime hp.out hN) α hα, jacobiSym.pow_right]
  push_cast
  rw [← chi_eq_jacobi]
  push_cast
  ring

/-- **`T_q` for odd `q` coprime to `N`.** -/
theorem Tq_coprime_aux (N : ℤ) : ∀ q : ℕ, ∀ hq : q ≠ 0, Odd q → IsCoprime N q → ∀ U : ℤ,
    IsCoprime U q →
    haveI : NeZero q := ⟨hq⟩
    Tq q (U : ZMod q) (N : ZMod q) = (jacobiSym (-N) q : ℂ) * q * Rq q U N := by
  intro q
  induction q using Nat.recOnPrimeCoprime with
  | zero => intro h; exact absurd rfl h
  | prime_pow p n hp =>
    intro _ hodd hN U hU
    haveI : Fact p.Prime := ⟨hp⟩
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      have key : ∀ (q : ℕ) [NeZero q], q = 1 → Tq q (U : ZMod q) (N : ZMod q) =
          (jacobiSym (-N) q : ℂ) * (q : ℕ) * Rq q U N := by
        intro q _ hq; subst hq; rw [Tq_one, Rq_one]; simp
      exact key _ (pow_zero p)
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hn.ne').mpr even_two)
    have hpn : ((p ^ n : ℕ) : ℤ) = (p : ℤ) ^ n := by push_cast; ring
    rw [hpn] at hN hU
    have hNp : IsCoprime N p := IsCoprime.of_isCoprime_of_dvd_right hN (dvd_pow_self _ hn.ne')
    have hUp : IsCoprime U p := IsCoprime.of_isCoprime_of_dvd_right hU (dvd_pow_self _ hn.ne')
    exact Tq_prime_pow_J hp2 N U hNp hUp n
  | coprime a b ha hb hab iha ihb =>
    intro hq0 hodd hN U hU
    haveI : NeZero a := ⟨by omega⟩
    haveI : NeZero b := ⟨by omega⟩
    obtain ⟨r', s', hb'⟩ := Nat.isCoprime_iff_coprime.mpr hab
    have hbz : s' * b + r' * a = 1 := by linear_combination hb'
    have hq' : ((a * b : ℕ) : ℤ) = a * b := by push_cast; ring
    rw [hq'] at hN hU
    have hsa : IsCoprime s' a := ⟨b, r', by linear_combination hbz⟩
    have hrb : IsCoprime r' b := ⟨a, s', by linear_combination hbz⟩
    rw [Tq_mul hab r' s' hbz U N,
      iha (by omega) (Nat.Odd.of_mul_left hodd) hN.of_mul_right_left (s' * U)
        (hsa.mul_left hU.of_mul_right_left),
      ihb (by omega) (Nat.Odd.of_mul_right hodd) hN.of_mul_right_right (r' * U)
        (hrb.mul_left hU.of_mul_right_right),
      Rq_mul hab r' s' hbz U N, jacobiSym.mul_right]
    push_cast
    ring

theorem Tq_coprime (N : ℤ) (q : ℕ) [NeZero q] (hodd : Odd q) (hN : IsCoprime N q) (U : ℤ)
    (hU : IsCoprime U q) :
    Tq q (U : ZMod q) (N : ZMod q) = (jacobiSym (-N) q : ℂ) * q * Rq q U N :=
  Tq_coprime_aux N q (NeZero.ne q) hodd hN U hU

end ThreeSquares
