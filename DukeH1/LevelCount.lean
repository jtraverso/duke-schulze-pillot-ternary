/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.PhatBound
public import Mathlib.NumberTheory.Chebyshev

/-!
# Counting the levels

`levels n P₀` = primes `p ∈ (P₀, 4P₀]` with `p ∤ 2n`. Chebyshev's bounds give
`(#levels + ω(2n)) log(4P₀) ≥ 2 P₀ log 2 − log(4P₀ + 1) − 2 √(4P₀) log(4P₀)` (`card_levels_ge`).
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open Finset Real

/-- The levels: primes in `(P₀, 4P₀]` not dividing `2n`. -/
def levels (n P₀ : ℕ) : Finset ℕ := (Ioc P₀ (4 * P₀)).filter (fun p => p.Prime ∧ ¬ p ∣ 2 * n)

theorem mem_levels {n P₀ p : ℕ} (hp : p ∈ levels n P₀) :
    p.Prime ∧ ¬ p ∣ 2 * n ∧ P₀ ≤ p ∧ p ≤ 4 * P₀ := by
  simp only [levels, mem_filter, mem_Ioc] at hp
  exact ⟨hp.2.1, hp.2.2, hp.1.1.le, hp.1.2⟩

theorem theta_diff_le (n P₀ : ℕ) (hn : 0 < n) (hP₀ : 1 ≤ P₀) :
    Chebyshev.theta ((4 * P₀ : ℕ) : ℝ) - Chebyshev.theta (P₀ : ℝ) ≤
      (((levels n P₀).card : ℝ) + (2 * n).primeFactors.card) * Real.log (4 * P₀) := by
  classical
  have h1 : Chebyshev.theta ((4 * P₀ : ℕ) : ℝ) = Chebyshev.theta (P₀ : ℝ) +
      ∑ p ∈ (Ioc P₀ (4 * P₀)).filter Nat.Prime, Real.log p := by
    simp only [Chebyshev.theta, Nat.floor_natCast]
    rw [sum_filter, sum_filter, sum_filter, sum_Ioc_consecutive _ (Nat.zero_le P₀) (by omega)]
  rw [h1, add_sub_cancel_left]
  have hlog : ∀ p ∈ (Ioc P₀ (4 * P₀)).filter Nat.Prime, Real.log p ≤ Real.log (4 * P₀) := by
    intro p hp
    simp only [mem_filter, mem_Ioc] at hp
    refine Real.log_le_log (by exact_mod_cast hp.2.pos) ?_
    exact_mod_cast hp.1.2
  rw [← sum_filter_add_sum_filter_not _ (fun p => p ∣ 2 * n), filter_filter, filter_filter, add_mul,
    add_comm (((levels n P₀).card : ℝ) * _)]
  refine add_le_add ?_ ?_
  · refine (sum_le_card_nsmul _ _ _ fun p hp => hlog p (by
      simp only [mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩)).trans ?_
    rw [nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg (by
      have : (1 : ℝ) ≤ P₀ := by exact_mod_cast hP₀
      linarith))
    exact_mod_cast card_le_card fun p hp => by
      simp only [mem_filter, mem_Ioc] at hp
      exact Nat.mem_primeFactors.mpr ⟨hp.2.1, hp.2.2, by omega⟩
  · refine (sum_le_card_nsmul _ _ _ fun p hp => hlog p (by
      simp only [mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩)).trans (le_of_eq ?_)
    rw [nsmul_eq_mul]
    rfl

/-- **Chebyshev lower bound for the number of levels.** -/
theorem card_levels_ge (n P₀ : ℕ) (hn : 0 < n) (hP₀ : 1 ≤ P₀) :
    2 * P₀ * Real.log 2 - Real.log (4 * P₀ + 1) - 2 * Real.sqrt (4 * P₀) * Real.log (4 * P₀) ≤
      (((levels n P₀).card : ℝ) + (2 * n).primeFactors.card) * Real.log (4 * P₀) := by
  have hge := Chebyshev.theta_ge (4 * P₀)
  have hle := Chebyshev.theta_le_log4_mul_x (x := (P₀ : ℝ)) (Nat.cast_nonneg _)
  have hd := theta_diff_le n P₀ hn hP₀
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  push_cast at hge hd
  rw [h4] at hle
  linarith

end ThreeSquares
