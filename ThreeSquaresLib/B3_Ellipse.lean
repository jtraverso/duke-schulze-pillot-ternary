/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.B3_RepCount
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lattice points in the ellipse `f(v) ≤ M`

`ellCount_le`: for `f ∈ Red n` and `M ≥ 1`, `ellCount f M ≤ 8M/√n + 6√a √M + 1`.
From `4a f(x, y) = (2ax + by)² + n y²`: `|y| ≤ Y = √(4aM/n)` and, for each `y`, `x` lies in an
interval of length `S/a`, `S = √(4aM)`; so the count is at most `(2Y + 1)(S/a + 1)` and
`2Y S/a = 8M/√n`. (Any absolute constant in front of `M/√n` suffices for B3.)
-/

@[expose] public section

namespace ThreeSquares.B3

open Finset Real

theorem card_filter_interval_le (s : Finset ℤ) (α ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    ((s.filter (fun x : ℤ => α ≤ x ∧ (x : ℝ) ≤ α + ℓ)).card : ℝ) ≤ ℓ + 1 := by
  have hsub : s.filter (fun x : ℤ => α ≤ x ∧ (x : ℝ) ≤ α + ℓ) ⊆ Icc ⌈α⌉ ⌊α + ℓ⌋ := by
    intro x hx
    rw [mem_filter] at hx
    rw [mem_Icc]
    exact ⟨Int.ceil_le.mpr hx.2.1, Int.le_floor.mpr hx.2.2⟩
  refine le_trans (Nat.cast_le.mpr (card_le_card hsub)) ?_
  rw [Int.card_Icc]
  have h1 := Int.floor_le (α + ℓ)
  have h2 := Int.le_ceil α
  rcases le_or_gt (⌊α + ℓ⌋ + 1 - ⌈α⌉) 0 with h | h
  · rw [Int.toNat_of_nonpos h]
    push_cast
    linarith
  · have : ((⌊α + ℓ⌋ + 1 - ⌈α⌉).toNat : ℝ) = ((⌊α + ℓ⌋ + 1 - ⌈α⌉ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h.le
    rw [this]
    push_cast
    linarith

theorem ellCount_le {n : ℕ} (hn : 0 < n) {f : Form} (hf : f ∈ Red n) {M : ℕ} (hM : 1 ≤ M) :
    (ellCount f M : ℝ) ≤ 8 * M / Real.sqrt n + 6 * Real.sqrt f.a * Real.sqrt M + 1 := by
  obtain ⟨hd, -, ha⟩ := mem_Red.mp hf
  have ha' : (1 : ℝ) ≤ f.a := by exact_mod_cast ha
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  set S := Real.sqrt (4 * f.a * M)
  set Y := Real.sqrt (4 * f.a * M / n)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  -- the two constraints
  have key : ∀ x y : ℤ, f.eval x y ≤ M →
      ((2 * f.a * x + f.b * y : ℤ) : ℝ) ^ 2 ≤ 4 * f.a * M ∧ (n : ℝ) * (y : ℝ) ^ 2 ≤ 4 * f.a * M := by
    intro x y h
    have e := Form.four_a_eval f x y
    rw [hd] at e
    have h' : ((f.eval x y : ℤ) : ℝ) ≤ M := by exact_mod_cast h
    have e' : (4 * f.a * f.eval x y : ℝ) = ((2 * f.a * x + f.b * y : ℤ) : ℝ) ^ 2 + n * (y : ℝ) ^ 2 := by
      exact_mod_cast (by rw [e]; ring : (4 * f.a * f.eval x y : ℤ) = (2 * f.a * x + f.b * y) ^ 2 + n * y ^ 2)
    have h4 : (4 * f.a * f.eval x y : ℝ) ≤ 4 * f.a * M := by
      have : (0 : ℝ) ≤ 4 * f.a := by linarith
      exact_mod_cast mul_le_mul_of_nonneg_left h' this
    constructor <;> nlinarith [sq_nonneg ((2 * f.a * x + f.b * y : ℤ) : ℝ), sq_nonneg (y : ℝ)]
  -- the count, fibre by fibre in `y`
  have hrow : ∀ y : ℤ, ((((Icc (-(2 * M : ℕ) : ℤ) (2 * M : ℕ)).filter
      (fun x => 1 ≤ f.eval x y ∧ f.eval x y ≤ M)).card : ℕ) : ℝ) ≤
      if (n : ℝ) * (y : ℝ) ^ 2 ≤ 4 * f.a * M then S / f.a + 1 else 0 := by
    intro y
    split_ifs with hy
    · set α : ℝ := (-S - f.b * y) / (2 * f.a)
      have hsub : (Icc (-(2 * M : ℕ) : ℤ) (2 * M : ℕ)).filter
          (fun x => 1 ≤ f.eval x y ∧ f.eval x y ≤ M) ⊆
          (Icc (-(2 * M : ℕ) : ℤ) (2 * M : ℕ)).filter
            (fun x : ℤ => α ≤ x ∧ (x : ℝ) ≤ α + S / f.a) := by
        intro x hx
        rw [mem_filter] at hx ⊢
        refine ⟨hx.1, ?_⟩
        have h1 := (key x y hx.2.2).1
        have hab : |((2 * f.a * x + f.b * y : ℤ) : ℝ)| ≤ S := by
          rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h1
        rw [abs_le] at hab
        push_cast at hab
        have h2a : (0 : ℝ) < 2 * f.a := by linarith
        simp only [α]
        constructor
        · rw [div_le_iff₀ h2a]; linarith
        · have : (-S - f.b * y) / (2 * f.a) + S / f.a = (S - f.b * y) / (2 * f.a) := by
            field_simp; ring
          rw [this, le_div_iff₀ h2a]; linarith
      refine le_trans (Nat.cast_le.mpr (card_le_card hsub)) ?_
      exact card_filter_interval_le _ _ _ (div_nonneg hS0 (by linarith))
    · have : (Icc (-(2 * M : ℕ) : ℤ) (2 * M : ℕ)).filter
          (fun x => 1 ≤ f.eval x y ∧ f.eval x y ≤ M) = ∅ := by
        rw [filter_eq_empty_iff]
        intro x _ hx
        exact hy (key x y hx.2).2
      rw [this]; simp
  have hcount : (ellCount f M : ℝ) ≤ (2 * Y + 1) * (S / f.a + 1) := by
    unfold ellCount box
    rw [card_filter, sum_product_right]
    have e1 : ∀ y ∈ Icc (-(2 * M : ℕ) : ℤ) (2 * M : ℕ),
        (∑ x ∈ Icc (-(2 * M : ℕ) : ℤ) (2 * M : ℕ),
          if 1 ≤ f.eval (x, y).1 (x, y).2 ∧ f.eval (x, y).1 (x, y).2 ≤ M then 1 else 0) =
        ((Icc (-(2 * M : ℕ) : ℤ) (2 * M : ℕ)).filter
          (fun x => 1 ≤ f.eval x y ∧ f.eval x y ≤ M)).card := by
      intro y _
      rw [card_filter]
    rw [sum_congr rfl e1]
    push_cast
    refine le_trans (sum_le_sum fun y _ => hrow y) ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have hY : (((Icc (-(2 * M : ℕ) : ℤ) (2 * M : ℕ)).filter
        (fun y : ℤ => (n : ℝ) * (y : ℝ) ^ 2 ≤ 4 * f.a * M)).card : ℝ) ≤ 2 * Y + 1 := by
      have hsub : (Icc (-(2 * M : ℕ) : ℤ) (2 * M : ℕ)).filter
          (fun y : ℤ => (n : ℝ) * (y : ℝ) ^ 2 ≤ 4 * f.a * M) ⊆
          (Icc (-(2 * M : ℕ) : ℤ) (2 * M : ℕ)).filter
            (fun y : ℤ => -Y ≤ y ∧ (y : ℝ) ≤ -Y + 2 * Y) := by
        intro y hy
        rw [mem_filter] at hy ⊢
        refine ⟨hy.1, ?_⟩
        have : (y : ℝ) ^ 2 ≤ 4 * f.a * M / n := by rw [le_div_iff₀ hn']; linarith [hy.2]
        have hab : |(y : ℝ)| ≤ Y := by
          rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt this
        rw [abs_le] at hab
        constructor <;> linarith
      refine le_trans (Nat.cast_le.mpr (card_le_card hsub)) ?_
      have := card_filter_interval_le (Icc (-(2 * M : ℕ) : ℤ) (2 * M : ℕ)) (-Y) (2 * Y) (by linarith)
      linarith
    have : 0 ≤ S / f.a + 1 := by positivity
    push_cast at hY
    nlinarith [mul_le_mul_of_nonneg_right hY this]
  -- arithmetic
  have hYS : Y * S = 4 * f.a * M / Real.sqrt n := by
    simp only [Y, S]
    rw [← Real.sqrt_mul (by positivity), show 4 * (f.a : ℝ) * M / n * (4 * f.a * M) =
      (4 * f.a * M) ^ 2 / n by ring, Real.sqrt_div' _ hn'.le, Real.sqrt_sq (by positivity)]
  have hS : S = 2 * Real.sqrt f.a * Real.sqrt M := by
    simp only [S]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hY : Y ≤ S := by
    simp only [Y, S]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hn']
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : 0 ≤ 4 * (f.a : ℝ) * M := by positivity
    nlinarith
  have hSa : S / f.a ≤ S := div_le_self hS0 ha'
  have hsa : 0 < Real.sqrt (f.a : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn'
  have e2 : 2 * Y * (S / f.a) = 8 * M / Real.sqrt n := by
    rw [mul_div_assoc', mul_assoc, hYS]
    field_simp
    ring
  calc (ellCount f M : ℝ) ≤ (2 * Y + 1) * (S / f.a + 1) := hcount
    _ = 2 * Y * (S / f.a) + 2 * Y + S / f.a + 1 := by ring
    _ ≤ 8 * M / Real.sqrt n + 2 * S + S + 1 := by rw [e2]; linarith
    _ = 8 * M / Real.sqrt n + 6 * Real.sqrt f.a * Real.sqrt M + 1 := by rw [hS]; ring

end ThreeSquares.B3
