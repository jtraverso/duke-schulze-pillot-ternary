/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.TrivRange

/-!
# `P̂_{8p}` in terms of the critical sum

`‖P̂_{8p}(n)‖ ≤ 2 + 2 (∑_{c ≤ y, 8p ∣ c} ‖cfac T_c‖ + ‖critSum_p‖ + B)` whenever every partial sum of the tail
`∑_{Y < c ≤ N, 8p ∣ c} ‖cfac T_c‖` is at most `B` (`phat_bound`).
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open Finset

theorem phat_bound (ℓ n p y Y : ℕ) (hℓ : 2 ≤ ℓ) (hyY : y ≤ Y) (B : ℝ)
    (hB : ∀ N, ∑ c ∈ (Ioc Y N).filter (fun c => 8 * p ∣ c), ‖Poin.cfac ℓ n c * Poin.Tc n c‖ ≤ B) :
    ‖Poin.Phat ℓ n (8 * p)‖ ≤ 2 + 2 * (∑ c ∈ (Icc 1 y).filter (fun c => 8 * p ∣ c),
      ‖Poin.cfac ℓ n c * Poin.Tc n c‖ + ‖critSum ℓ n p y Y‖ + B) := by
  classical
  rw [Poin.Phat_eq ℓ n hℓ (dvd_mul_of_dvd_left (by norm_num : 4 ∣ 8) p)]
  set F : ℕ → ℂ := fun c => if 0 < c ∧ 8 * p ∣ c then Poin.cfac ℓ n c * Poin.Tc n c else 0 with hF
  have hFn : ∀ c, Y < c → ‖F c‖ = if 8 * p ∣ c then ‖Poin.cfac ℓ n c * Poin.Tc n c‖ else 0 := by
    intro c hc
    simp only [F]
    by_cases h : 8 * p ∣ c
    · rw [if_pos ⟨by omega, h⟩, if_pos h]
    · rw [if_neg (fun hh => h hh.2), if_neg h, norm_zero]
  set G : ℕ → ℝ := fun i => ‖F (i + (Y + 1))‖
  have hG0 : ∀ i, 0 ≤ G i := fun i => norm_nonneg _
  have hGs : ∀ M, ∑ i ∈ range M, G i ≤ B := by
    intro M
    have e : ∑ i ∈ range M, G i = ∑ c ∈ Ico (Y + 1) (Y + 1 + M), ‖F c‖ := by
      rw [sum_Ico_eq_sum_range, show Y + 1 + M - (Y + 1) = M by omega]
      exact sum_congr rfl fun i _ => by
        show ‖F (i + (Y + 1))‖ = ‖F (Y + 1 + i)‖; rw [add_comm]
    rw [e]
    refine le_trans (le_of_eq ?_) (hB (Y + M))
    rw [sum_filter]
    refine sum_congr (by ext c; simp only [mem_Ico, mem_Ioc]; omega) fun c hc => ?_
    exact hFn c (by simp only [mem_Ioc] at hc; omega)
  have hGsum : Summable G := summable_of_sum_range_le hG0 hGs
  have hGt : ∑' i, G i ≤ B := Real.tsum_le_of_sum_range_le hG0 hGs
  have hFt : Summable (fun i => F (i + (Y + 1))) := hGsum.of_norm
  have hFs : Summable F := (summable_nat_add_iff (Y + 1)).mp hFt
  rw [← hFs.sum_add_tsum_nat_add (Y + 1)]
  have hfin : ∑ c ∈ range (Y + 1), F c =
      ∑ c ∈ (Icc 1 y).filter (fun c => 8 * p ∣ c), Poin.cfac ℓ n c * Poin.Tc n c + critSum ℓ n p y Y := by
    unfold critSum
    rw [show ∑ c ∈ range (Y + 1), F c = ∑ c ∈ (range (Y + 1)).filter (fun c => 0 < c ∧ 8 * p ∣ c),
      Poin.cfac ℓ n c * Poin.Tc n c from (sum_filter _ _).symm]
    rw [← sum_filter_add_sum_filter_not _ (fun c => c ≤ y)]
    congr 1
    · congr 1
      ext c
      simp only [mem_filter, mem_range, mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨⟨by omega, h4⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, by omega, h3⟩, h2⟩
    · congr 1
      ext c
      simp only [mem_filter, mem_range, mem_Ioc]
      constructor
      · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨⟨by omega, by omega⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, by omega, h3⟩, by omega⟩
  rw [hfin]
  have hlow := norm_sum_le ((Icc 1 y).filter (fun c => 8 * p ∣ c)) (fun c => Poin.cfac ℓ n c * Poin.Tc n c)
  have htail : ‖∑' i, F (i + (Y + 1))‖ ≤ B := (norm_tsum_le_tsum_norm hGsum).trans hGt
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  refine norm_add₃_le.trans ?_
  linarith

end ThreeSquares
