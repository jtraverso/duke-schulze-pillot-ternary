/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.NumMethods

/-!
# From class sums to blocks

* `Asum_eq_blocks`: `Asum = ∑_{i, j ≤ L} ABsum(dblock i, dblock j)` when `Y < 2^L`;
* `ABsum_eq_zero_high` / `ABsum_eq_zero_low`: blocks outside the range `(y, Y]` vanish.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open Finset

theorem dblock_le {a i : ℕ} (h : a ∈ dblock i) : a ≤ 2 ^ i := by
  rcases (mem_dblock_iff a i).mp h with ⟨rfl, rfl⟩ | ⟨-, -, h2⟩
  · simp
  · exact h2

theorem dblock_ge {a i : ℕ} (h : a ∈ dblock i) : 2 ^ i ≤ 2 * a := by
  rcases (mem_dblock_iff a i).mp h with ⟨rfl, rfl⟩ | ⟨hi, h1, -⟩
  · simp
  · have : 2 ^ i = 2 * 2 ^ (i - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

theorem ker1_zero_of_le (r y Y : ℕ) (W : ℕ → ℂ) (h : ℤ) (p a b : ℕ) (hc : r * p * a * b ≤ y) :
    ker1 r y Y W h p a b = 0 := by
  unfold ker1; rw [if_neg (fun hh => by omega)]

theorem ker1_zero_of_gt (r y Y : ℕ) (W : ℕ → ℂ) (h : ℤ) (p a b : ℕ) (hc : Y < r * p * a * b) :
    ker1 r y Y W h p a b = 0 := by
  unfold ker1; rw [if_neg (fun hh => by omega)]

/-- **Blocks below the range vanish.** -/
theorem ABsum_eq_zero_low (n p y Y r t₁ t₂ : ℕ) (I J : Finset ℕ) (W : ℕ → ℂ) (h : ℕ → ℤ)
    (Ua Ub : ℕ) (hI : ∀ a ∈ I, a ≤ Ua) (hJ : ∀ b ∈ J, b ≤ Ub) (hlow : r * p * Ua * Ub ≤ y) :
    ABsum n p y Y r t₁ t₂ I J W h = 0 := by
  unfold ABsum
  refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
  rw [ker1_zero_of_le, mul_zero]
  have h1 := hI a (Finset.mem_filter.mp ha).1
  have h2 := hJ b (Finset.mem_filter.mp hb).1
  calc r * p * a * b ≤ r * p * Ua * Ub := by gcongr
    _ ≤ y := hlow

/-- **Blocks above the range vanish.** -/
theorem ABsum_eq_zero_high (n p y Y r t₁ t₂ : ℕ) (I J : Finset ℕ) (W : ℕ → ℂ) (h : ℕ → ℤ)
    (La Lb : ℕ) (hI : ∀ a ∈ I, La ≤ a) (hJ : ∀ b ∈ J, Lb ≤ b) (hhigh : Y < r * p * La * Lb) :
    ABsum n p y Y r t₁ t₂ I J W h = 0 := by
  unfold ABsum
  refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
  rw [ker1_zero_of_gt, mul_zero]
  have h1 := hI a (Finset.mem_filter.mp ha).1
  have h2 := hJ b (Finset.mem_filter.mp hb).1
  calc Y < r * p * La * Lb := hhigh
    _ ≤ r * p * a * b := by gcongr

theorem sum_dblocks_eq_Icc (L : ℕ) (g : ℕ → ℂ) :
    ∑ i ∈ range (L + 1), ∑ a ∈ dblock i, g a = ∑ a ∈ Icc 1 (2 ^ L), g a := by
  classical
  rw [← Finset.sum_biUnion (fun i _ j _ hij => dblock_disjoint hij)]
  congr 1
  ext a
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, ha⟩
    refine ⟨dblock_pos ha, (dblock_le ha).trans (Nat.pow_le_pow_right (by norm_num) (by omega))⟩
  · rintro ⟨ha1, ha2⟩
    obtain ⟨i, hi, hai⟩ := exists_dblock a (L + 1) ha1 (by rw [pow_succ]; omega)
    refine ⟨i, ?_, hai⟩
    rcases (mem_dblock_iff a i).mp hai with ⟨rfl, -⟩ | ⟨hi0, h1, -⟩
    · omega
    · by_contra hc
      have : 2 ^ L ≤ 2 ^ (i - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

theorem sum_range_eq_Icc (Y M : ℕ) (hYM : Y ≤ M) (G : ℕ → ℂ) (h0 : G 0 = 0)
    (hbig : ∀ a, Y < a → G a = 0) : ∑ a ∈ range (Y + 1), G a = ∑ a ∈ Icc 1 M, G a := by
  have e1 : ∑ a ∈ range (Y + 1), G a = ∑ a ∈ Icc 1 Y, G a := by
    refine (Finset.sum_subset (fun a ha => ?_) (fun a ha hna => ?_)).symm
    · simp only [Finset.mem_Icc] at ha; simp only [Finset.mem_range]; omega
    · simp only [Finset.mem_range] at ha; simp only [Finset.mem_Icc, not_and, not_le] at hna
      have : a = 0 := by omega
      rw [this, h0]
  have e2 : ∑ a ∈ Icc 1 M, G a = ∑ a ∈ Icc 1 Y, G a := by
    refine (Finset.sum_subset (fun a ha => ?_) (fun a ha hna => ?_)).symm
    · simp only [Finset.mem_Icc] at ha ⊢; omega
    · simp only [Finset.mem_Icc, not_and, not_le] at ha hna
      exact hbig a (hna ha.1)
  rw [e1, e2]

/-- **Class sums as sums of blocks.** -/
theorem Asum_eq_blocks (n p y Y r t₁ t₂ L : ℕ) (W : ℕ → ℂ) (h : ℕ → ℤ) (hL : Y < 2 ^ L) :
    Asum n p y Y r t₁ t₂ W h =
      ∑ i ∈ range (L + 1), ∑ j ∈ range (L + 1), ABsum n p y Y r t₁ t₂ (dblock i) (dblock j) W h := by
  classical
  unfold Asum ABsum
  set F : ℕ → ℕ → ℂ := fun a b => chiR n a * chiR n b * ker1 r y Y W (h b) p a b
  have hF0 : ∀ a b, (a = 0 ∨ b = 0 ∨ Y < a ∨ Y < b) → F a b = 0 := by
    intro a b hab
    simp only [F]
    by_cases hz : r * p * a * b ≤ y
    · rw [ker1_zero_of_le _ _ _ _ _ _ _ _ hz, mul_zero]
    · rw [ker1_zero_of_gt, mul_zero]
      push_neg at hz
      have hpos : 0 < r * p * a * b := lt_of_le_of_lt (Nat.zero_le _) hz
      have h1 : 1 ≤ r * p := Nat.pos_of_ne_zero (fun h => by rw [h] at hpos; simp at hpos)
      have ha : 1 ≤ a := Nat.pos_of_ne_zero (fun h => by rw [h] at hpos; simp at hpos)
      have hb : 1 ≤ b := Nat.pos_of_ne_zero (fun h => by rw [h] at hpos; simp at hpos)
      rcases hab with h0 | h0 | hY | hY
      · omega
      · omega
      · calc Y < a := hY
          _ = 1 * a * 1 := by ring
          _ ≤ r * p * a * b := by gcongr
      · calc Y < b := hY
          _ = 1 * 1 * b := by ring
          _ ≤ r * p * a * b := by gcongr
  have hYL : Y ≤ 2 ^ L := hL.le
  -- the left side
  have hLHS : ∑ a ∈ (range (Y + 1)).filter (fun a => a % r = t₁), ∑ b ∈ (range (Y + 1)).filter (fun b => b % r = t₂), F a b =
      ∑ a ∈ Icc 1 (2 ^ L), if a % r = t₁ then ∑ b ∈ Icc 1 (2 ^ L), (if b % r = t₂ then F a b else 0) else 0 := by
    rw [Finset.sum_filter]
    refine sum_range_eq_Icc Y (2 ^ L) hYL _ (by split_ifs <;> simp [Finset.sum_filter, hF0]) (fun a ha => ?_) |>.trans ?_
    · split_ifs
      · exact Finset.sum_eq_zero fun b _ => hF0 a b (Or.inr (Or.inr (Or.inl ha)))
      · rfl
    · refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs
      · rw [Finset.sum_filter]
        exact sum_range_eq_Icc Y (2 ^ L) hYL _ (by split_ifs <;> simp [hF0])
          (fun b hb => by split_ifs <;> simp [hF0 a b (Or.inr (Or.inr (Or.inr hb)))])
      · rfl
  rw [hLHS, ← sum_dblocks_eq_Icc L]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [← sum_dblocks_eq_Icc L]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_filter]
  · rfl

end ThreeSquares
