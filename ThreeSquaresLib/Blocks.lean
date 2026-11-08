/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Glue5
public import ThreeSquaresLib.Method2Ref
public import ThreeSquaresLib.PVBlock

/-!
# Dyadic blocks

`dblock 0 = {1}`, `dblock (i+1) = (2^i, 2^{i+1}]`. Every `1 ≤ a ≤ Y` lies in exactly one `dblock i`, `i ≤ L`,
when `Y < 2^L` (`sum_dblocks`).
-/

@[expose] public section

namespace ThreeSquares

open Finset

/-- The dyadic blocks. -/
def dblock : ℕ → Finset ℕ
  | 0 => {1}
  | i + 1 => Ioc (2 ^ i) (2 * 2 ^ i)

theorem mem_dblock_iff (a : ℕ) (i : ℕ) : a ∈ dblock i ↔
    (i = 0 ∧ a = 1) ∨ (0 < i ∧ 2 ^ (i - 1) < a ∧ a ≤ 2 ^ i) := by
  cases i with
  | zero => simp [dblock]
  | succ i => simp [dblock, pow_succ]; omega

theorem dblock_pos {a i : ℕ} (h : a ∈ dblock i) : 0 < a := by
  rcases (mem_dblock_iff a i).mp h with ⟨-, rfl⟩ | ⟨-, h1, -⟩
  · exact one_pos
  · exact lt_of_le_of_lt (Nat.zero_le _) h1

theorem exists_dblock (a L : ℕ) (ha : 0 < a) (hL : a < 2 ^ L) : ∃ i ∈ range (L + 1), a ∈ dblock i := by
  rcases Nat.eq_or_lt_of_le ha with h | h
  · exact ⟨0, by simp, by simp [dblock, ← h]⟩
  · -- `i = log₂ (a - 1) + 1`
    set k := Nat.log 2 (a - 1)
    refine ⟨k + 1, ?_, ?_⟩
    · have h1 : a - 1 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have h2 : 2 ^ k ≤ a - 1 := Nat.pow_log_le_self 2 (by omega)
      have : k < L := by
        by_contra hk; push_neg at hk
        have : 2 ^ L ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        omega
      simp; omega
    · simp only [dblock, Finset.mem_Ioc]
      have h1 : a - 1 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have h2 : 2 ^ k ≤ a - 1 := Nat.pow_log_le_self 2 (by omega)
      rw [pow_succ] at h1
      omega

theorem dblock_disjoint {i j : ℕ} (hij : i ≠ j) : Disjoint (dblock i) (dblock j) := by
  rw [Finset.disjoint_left]
  intro a hi hj
  rw [mem_dblock_iff] at hi hj
  rcases hi with ⟨hi0, ha1⟩ | ⟨hi0, hi1, hi2⟩ <;> rcases hj with ⟨hj0, ha1'⟩ | ⟨hj0, hj1, hj2⟩
  · exact hij (hi0.trans hj0.symm)
  · subst ha1; have : 1 ≤ 2 ^ (j - 1) := Nat.one_le_two_pow; omega
  · subst ha1'; have : 1 ≤ 2 ^ (i - 1) := Nat.one_le_two_pow; omega
  · -- `2^(i-1) < a ≤ 2^i` and `2^(j-1) < a ≤ 2^j` force `i = j`
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · have : 2 ^ i ≤ 2 ^ (j - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have : 2 ^ j ≤ 2 ^ (i - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-- **Splitting a sum over `1 ≤ a ≤ Y` into dyadic blocks.** -/
theorem sum_dblocks (s : Finset ℕ) (L : ℕ) (hs : ∀ a ∈ s, 0 < a ∧ a < 2 ^ L) (f : ℕ → ℂ) :
    ∑ a ∈ s, f a = ∑ i ∈ range (L + 1), ∑ a ∈ s.filter (fun a => a ∈ dblock i), f a := by
  classical
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_subset (fun a ha => ?_) (fun a _ ha => absurd ?_ ha) |>.symm
    · obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
      exact (Finset.mem_filter.mp hai).1
    · obtain ⟨i, hi, hai⟩ := exists_dblock a L (hs a ‹_›).1 (hs a ‹_›).2
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨‹_›, hai⟩⟩
  · intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun a ha hb => ?_
    exact Finset.disjoint_left.mp (dblock_disjoint hij) (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

end ThreeSquares
