/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Complex.Basic

/-!
# Splitting integers along a set of primes

For a predicate `S` on primes, every `c ≠ 0` is uniquely `c = r q` with all prime factors of `r` in
`S` and none of `q` (`exists_split`, `split_unique`), and sums over `c` can be reindexed over pairs
(`sum_split`).
-/

@[expose] public section

namespace ThreeSquares

open Finset

/-- All prime factors satisfy `S`. -/
def Smooth (S : ℕ → Prop) (r : ℕ) : Prop := ∀ ℓ, ℓ.Prime → ℓ ∣ r → S ℓ

/-- No prime factor satisfies `S`. -/
def Rough (S : ℕ → Prop) (q : ℕ) : Prop := ∀ ℓ, ℓ.Prime → ℓ ∣ q → ¬ S ℓ

theorem exists_split (S : ℕ → Prop) :
    ∀ c, c ≠ 0 → ∃ r q, c = r * q ∧ Smooth S r ∧ Rough S q := by
  intro c
  induction c using Nat.recOnPrimeCoprime with
  | zero => intro h; exact absurd rfl h
  | prime_pow p k hp =>
    intro _
    by_cases hS : S p
    · refine ⟨p ^ k, 1, (mul_one _).symm, fun ℓ hℓ hd => ?_, fun ℓ hℓ hd => absurd (Nat.dvd_one.mp hd) hℓ.one_lt.ne'⟩
      rw [(Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow hd)]; exact hS
    · refine ⟨1, p ^ k, (one_mul _).symm, fun ℓ hℓ hd => absurd (Nat.dvd_one.mp hd) hℓ.one_lt.ne', fun ℓ hℓ hd => ?_⟩
      rw [(Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow hd)]; exact hS
  | coprime a b ha hb _ iha ihb =>
    intro _
    obtain ⟨r₁, q₁, h₁, s₁, t₁⟩ := iha (by omega)
    obtain ⟨r₂, q₂, h₂, s₂, t₂⟩ := ihb (by omega)
    refine ⟨r₁ * r₂, q₁ * q₂, by rw [h₁, h₂]; ring, fun ℓ hℓ hd => ?_, fun ℓ hℓ hd => ?_⟩
    · rcases (Nat.Prime.dvd_mul hℓ).mp hd with h | h
      · exact s₁ ℓ hℓ h
      · exact s₂ ℓ hℓ h
    · rcases (Nat.Prime.dvd_mul hℓ).mp hd with h | h
      · exact t₁ ℓ hℓ h
      · exact t₂ ℓ hℓ h

theorem coprime_of_smooth_rough {S : ℕ → Prop} {r q : ℕ} (hr : Smooth S r) (hq : Rough S q) :
    r.Coprime q := by
  by_contra h
  obtain ⟨ℓ, hℓ, h1, h2⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact hq ℓ hℓ h2 (hr ℓ hℓ h1)

theorem split_unique {S : ℕ → Prop} {r q r' q' : ℕ} (h : r * q = r' * q') (hr : Smooth S r)
    (hq : Rough S q) (hr' : Smooth S r') (hq' : Rough S q') (h0 : r * q ≠ 0) : r = r' ∧ q = q' := by
  have h1 : r ∣ r' := by
    have : r ∣ r' * q' := ⟨q, h.symm⟩
    exact (coprime_of_smooth_rough hr hq').dvd_of_dvd_mul_right this
  have h2 : r' ∣ r := by
    have : r' ∣ r * q := ⟨q', h⟩
    exact (coprime_of_smooth_rough hr' hq).dvd_of_dvd_mul_right this
  have hrr : r = r' := Nat.dvd_antisymm h1 h2
  refine ⟨hrr, ?_⟩
  subst hrr
  have hr0 : r ≠ 0 := by rintro rfl; simp at h0
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr0) h

open Classical in
/-- **Reindexing sums along the split.** -/
theorem sum_split (S : ℕ → Prop) (T : Finset ℕ) (N : ℕ) (hT : ∀ c ∈ T, 0 < c ∧ c ≤ N)
    (F : ℕ → ℂ) :
    ∑ c ∈ T, F c = ∑ r ∈ (range (N + 1)).filter (Smooth S), ∑ q ∈ (range (N + 1)).filter (Rough S),
      if r * q ∈ T then F (r * q) else 0 := by
  classical
  rw [← Finset.sum_product', ← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun x _ => x.1 * x.2) (fun x hx => (Finset.mem_filter.mp hx).2) ?_ ?_ ?_
  · intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_product] at hx hy
    have h0 : x.1 * x.2 ≠ 0 := (hT _ hx.2).1.ne'
    obtain ⟨e1, e2⟩ := split_unique hxy hx.1.1.2 hx.1.2.2 hy.1.1.2 hy.1.2.2 h0
    exact Prod.ext e1 e2
  · intro c hc
    obtain ⟨hc0, hcN⟩ := hT c hc
    obtain ⟨r, q, hrq, hr, hq⟩ := exists_split S c hc0.ne'
    have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; simp at hrq; omega)
    have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hrq; omega)
    have hrc : r ≤ c := by rw [hrq]; exact Nat.le_mul_of_pos_right _ hq0
    have hqc : q ≤ c := by rw [hrq]; exact Nat.le_mul_of_pos_left _ hr0
    refine ⟨(r, q), ?_, hrq.symm⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨⟨by omega, hr⟩, by omega, hq⟩, by rw [← hrq]; exact hc⟩
  · intro x _; rfl

end ThreeSquares
