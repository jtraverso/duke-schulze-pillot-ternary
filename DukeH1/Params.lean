/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.PowCalc

/-!
# The parameters as powers of `n`

`R = ⌊n^{1/250}⌋`, `P₀ = ⌊n^{11/40}⌋`, `B₀ = ⌊n^{2/25}⌋`, `K = ⌊n^{9/250}⌋`, `y = ⌊n^{1−δ}⌋`, `Y = ⌊n^{1+δ}⌋`
(`0 < δ ≤ 1/8000`), and the eventual inequalities between them needed by `BlockHyp` (`params_eventually`).
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open Real

theorem ev_le (C c a b : ℝ) (hc : 0 < c) (hab : a < b) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → C * (n : ℝ) ^ a ≤ c * (n : ℝ) ^ b := by
  obtain ⟨N₀, h⟩ := ((PowLe.self a).cmul (max C 0 / c) (by positivity)).eventually_le hab
  refine ⟨N₀, fun n hn => ?_⟩
  have h1 := h n hn
  have hpos : 0 ≤ (n : ℝ) ^ a := by positivity
  calc C * (n : ℝ) ^ a ≤ max C 0 * (n : ℝ) ^ a := mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
    _ = c * (max C 0 / c * (n : ℝ) ^ a) := by field_simp
    _ ≤ c * (n : ℝ) ^ b := mul_le_mul_of_nonneg_left h1 hc.le

noncomputable def pR (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 250 : ℝ)⌋₊
noncomputable def pP0 (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (11 / 40 : ℝ)⌋₊
noncomputable def pB0 (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (2 / 25 : ℝ)⌋₊
noncomputable def pK (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (9 / 250 : ℝ)⌋₊
noncomputable def py (δ : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 - δ)⌋₊
noncomputable def pY (δ : ℝ) (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 + δ)⌋₊
noncomputable def pL (δ : ℝ) (n : ℕ) : ℕ := Nat.log 2 (pY δ n) + 1
noncomputable def pUmax (δ : ℝ) (n : ℕ) : ℝ :=
  max (max 1 (2 * (pR n : ℝ))) ((16 * (pK n : ℝ) ^ 2 * (pY δ n : ℝ) / (pP0 n : ℝ)) ^ (1 / 3 : ℝ))
noncomputable def pX (δ : ℝ) (n : ℕ) : ℝ :=
  2 * (pR n : ℝ) * (4 * pP0 n : ℕ) * pUmax δ n * Real.sqrt (pUmax δ n) / (py δ n : ℝ)

theorem pY_lt_two_pow (δ : ℝ) (n : ℕ) : pY δ n < 2 ^ pL δ n := Nat.lt_pow_succ_log_self (by norm_num) _

/-- **The eventual inequalities.** -/
theorem params_eventually (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8000) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
      1 ≤ pR n ∧ pR n < n ∧ 0 < pP0 n ∧ 0 < pK n ∧ 0 < py δ n ∧ 2 * pR n ≤ pB0 n ∧
      pUmax δ n < pP0 n ∧ 2 * pR n ^ 2 * (4 * pP0 n) * pB0 n ^ 2 ≤ py δ n ∧
      py δ n + 1 ≤ pY δ n ∧ n ≤ pY δ n ∧ ((py δ n : ℕ) : ℝ) ≤ 2 * π * n := by
  obtain ⟨N2, h2⟩ := ev_le 2 (1 / 2) (1 / 250) (2 / 25) (by norm_num) (by norm_num)
  obtain ⟨N3, h3⟩ := ev_le 3 (1 / 2) (1 / 250) (11 / 40) (by norm_num) (by norm_num)
  obtain ⟨N4, h4⟩ := ev_le (2 * 32 ^ (1 / 3 : ℝ)) (1 / 2) ((2 * (9 / 250) + 1 + δ - 11 / 40) / 3) (11 / 40)
    (by norm_num) (by linarith)
  obtain ⟨N5, h5⟩ := ev_le 8 (1 / 2) (2 * (1 / 250) + 11 / 40 + 2 * (2 / 25)) (1 - δ) (by norm_num)
    (by linarith)
  obtain ⟨N7, h7⟩ := ev_le 2 (1 / 2) 0 (11 / 40) (by norm_num) (by norm_num)
  refine ⟨max 2 (max N2 (max N3 (max N4 (max N5 N7)))), fun n hn => ?_⟩
  simp only [max_le_iff] at hn
  obtain ⟨hn2, hN2, hN3, hN4, hN5, hN7⟩ := hn
  have hn1 : 1 ≤ n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1R : (1 : ℝ) < n := by linarith
  have e2 := h2 n hN2
  have e3 := h3 n hN3
  have e4 := h4 n hN4
  have e5 := h5 n hN5
  have e7 := h7 n hN7
  rw [Real.rpow_zero, mul_one] at e7
  -- floors
  have fR : (pR n : ℝ) ≤ (n : ℝ) ^ (1 / 250 : ℝ) := Nat.floor_le (by positivity)
  have fK : (pK n : ℝ) ≤ (n : ℝ) ^ (9 / 250 : ℝ) := Nat.floor_le (by positivity)
  have fB : (pB0 n : ℝ) ≤ (n : ℝ) ^ (2 / 25 : ℝ) := Nat.floor_le (by positivity)
  have fP : (pP0 n : ℝ) ≤ (n : ℝ) ^ (11 / 40 : ℝ) := Nat.floor_le (by positivity)
  have fy : (py δ n : ℝ) ≤ (n : ℝ) ^ (1 - δ) := Nat.floor_le (by positivity)
  have fY : (pY δ n : ℝ) ≤ (n : ℝ) ^ (1 + δ) := Nat.floor_le (by positivity)
  have gB : (1 / 2) * (n : ℝ) ^ (2 / 25 : ℝ) ≤ (pB0 n : ℝ) := floor_rpow_ge (2 / 25) (by norm_num) n hn1
  have gP : (1 / 2) * (n : ℝ) ^ (11 / 40 : ℝ) ≤ (pP0 n : ℝ) := floor_rpow_ge (11 / 40) (by norm_num) n hn1
  have gy : (1 / 2) * (n : ℝ) ^ (1 - δ) ≤ (py δ n : ℝ) := floor_rpow_ge (1 - δ) (by linarith) n hn1
  have hP0pos : (0 : ℝ) < pP0 n := lt_of_lt_of_le (by positivity) gP
  have hny : (n : ℝ) ^ (1 - δ) < n := by
    have := Real.rpow_lt_rpow_of_exponent_lt hn1R (show 1 - δ < 1 by linarith)
    rwa [Real.rpow_one] at this
  have hyn : py δ n < n := by
    have : (py δ n : ℝ) < n := lt_of_le_of_lt fy hny
    exact_mod_cast this
  have hnY : n ≤ pY δ n := by
    apply Nat.le_floor
    have := Real.rpow_le_rpow_of_exponent_le hn1R.le (show (1 : ℝ) ≤ 1 + δ by linarith)
    rwa [Real.rpow_one] at this
  refine ⟨floor_rpow_pos _ (by norm_num) n hn1, ?_, floor_rpow_pos _ (by norm_num) n hn1,
    floor_rpow_pos _ (by norm_num) n hn1, floor_rpow_pos _ (by linarith) n hn1, ?_, ?_, ?_, by omega, hnY, ?_⟩
  · have := Real.rpow_lt_rpow_of_exponent_lt hn1R (show (1 / 250 : ℝ) < 1 by norm_num)
    rw [Real.rpow_one] at this
    exact_mod_cast lt_of_le_of_lt fR this
  · have : (2 * pR n : ℝ) ≤ pB0 n := by linarith
    exact_mod_cast this
  · -- `Umax < P₀`
    unfold pUmax
    have hc1 : (1 : ℝ) < pP0 n := by linarith
    have hc2 : 2 * (pR n : ℝ) < pP0 n := by
      have : 0 < (n : ℝ) ^ (1 / 250 : ℝ) := by positivity
      linarith
    have hx : 16 * (pK n : ℝ) ^ 2 * (pY δ n : ℝ) / (pP0 n : ℝ) ≤
        32 * (n : ℝ) ^ (2 * (9 / 250) + 1 + δ - 11 / 40) := by
      rw [div_le_iff₀ hP0pos]
      have hK2 : (pK n : ℝ) ^ 2 ≤ (n : ℝ) ^ (2 * (9 / 250 : ℝ)) := by
        rw [show (2 * (9 / 250 : ℝ)) = 9 / 250 + 9 / 250 by ring, Real.rpow_add hn0, sq]
        exact mul_le_mul fK fK (Nat.cast_nonneg _) (by positivity)
      have e : (n : ℝ) ^ (2 * (9 / 250) + 1 + δ - 11 / 40) * (n : ℝ) ^ (11 / 40 : ℝ) =
          (n : ℝ) ^ (2 * (9 / 250 : ℝ)) * (n : ℝ) ^ (1 + δ) := by
        rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]; ring_nf
      calc 16 * (pK n : ℝ) ^ 2 * (pY δ n : ℝ) ≤ 16 * (n : ℝ) ^ (2 * (9 / 250 : ℝ)) * (n : ℝ) ^ (1 + δ) := by
            gcongr
        _ = 16 * ((n : ℝ) ^ (2 * (9 / 250) + 1 + δ - 11 / 40) * (n : ℝ) ^ (11 / 40 : ℝ)) := by rw [e]; ring
        _ ≤ 16 * ((n : ℝ) ^ (2 * (9 / 250) + 1 + δ - 11 / 40) * (2 * pP0 n)) := by gcongr; linarith
        _ = 32 * (n : ℝ) ^ (2 * (9 / 250) + 1 + δ - 11 / 40) * (pP0 n) := by ring
    have hx0 : 0 ≤ 16 * (pK n : ℝ) ^ 2 * (pY δ n : ℝ) / (pP0 n : ℝ) := by positivity
    have hc3 : (16 * (pK n : ℝ) ^ 2 * (pY δ n : ℝ) / (pP0 n : ℝ)) ^ (1 / 3 : ℝ) < pP0 n := by
      calc (16 * (pK n : ℝ) ^ 2 * (pY δ n : ℝ) / (pP0 n : ℝ)) ^ (1 / 3 : ℝ)
          ≤ (32 * (n : ℝ) ^ (2 * (9 / 250) + 1 + δ - 11 / 40)) ^ (1 / 3 : ℝ) :=
            Real.rpow_le_rpow hx0 hx (by norm_num)
        _ = 32 ^ (1 / 3 : ℝ) * (n : ℝ) ^ ((2 * (9 / 250) + 1 + δ - 11 / 40) / 3) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hn0.le]; ring_nf
        _ < 2 * 32 ^ (1 / 3 : ℝ) * (n : ℝ) ^ ((2 * (9 / 250) + 1 + δ - 11 / 40) / 3) := by
            have : 0 < (32 : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ ((2 * (9 / 250) + 1 + δ - 11 / 40) / 3) := by
              positivity
            linarith
        _ ≤ (1 / 2) * (n : ℝ) ^ (11 / 40 : ℝ) := e4
        _ ≤ pP0 n := gP
    exact max_lt (max_lt hc1 hc2) hc3
  · -- `2 R² (4P₀) B₀² ≤ y`
    have hreal : (2 * (pR n : ℝ) ^ 2 * (4 * pP0 n) * (pB0 n : ℝ) ^ 2) ≤ py δ n := by
      have hR2 : (pR n : ℝ) ^ 2 ≤ (n : ℝ) ^ (2 * (1 / 250 : ℝ)) := by
        rw [show (2 * (1 / 250 : ℝ)) = 1 / 250 + 1 / 250 by ring, Real.rpow_add hn0, sq]
        exact mul_le_mul fR fR (Nat.cast_nonneg _) (by positivity)
      have hB2 : (pB0 n : ℝ) ^ 2 ≤ (n : ℝ) ^ (2 * (2 / 25 : ℝ)) := by
        rw [show (2 * (2 / 25 : ℝ)) = 2 / 25 + 2 / 25 by ring, Real.rpow_add hn0, sq]
        exact mul_le_mul fB fB (Nat.cast_nonneg _) (by positivity)
      have e : (n : ℝ) ^ (2 * (1 / 250 : ℝ)) * (n : ℝ) ^ (11 / 40 : ℝ) * (n : ℝ) ^ (2 * (2 / 25 : ℝ)) =
          (n : ℝ) ^ (2 * (1 / 250) + 11 / 40 + 2 * (2 / 25) : ℝ) := by
        rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
      calc 2 * (pR n : ℝ) ^ 2 * (4 * pP0 n) * (pB0 n : ℝ) ^ 2
          ≤ 2 * (n : ℝ) ^ (2 * (1 / 250 : ℝ)) * (4 * (n : ℝ) ^ (11 / 40 : ℝ)) * (n : ℝ) ^ (2 * (2 / 25 : ℝ)) := by
            gcongr
        _ = 8 * (n : ℝ) ^ (2 * (1 / 250) + 11 / 40 + 2 * (2 / 25) : ℝ) := by rw [← e]; ring
        _ ≤ (1 / 2) * (n : ℝ) ^ (1 - δ) := e5
        _ ≤ py δ n := gy
    exact_mod_cast hreal
  · have : (n : ℝ) ≤ 2 * π * n := by nlinarith [Real.pi_gt_three]
    linarith

end ThreeSquares
