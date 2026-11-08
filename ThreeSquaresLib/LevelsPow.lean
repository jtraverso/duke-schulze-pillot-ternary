/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.FinalPow

/-!
# Many levels

`1/#levels(n, P₀(n)) = O(n^{−11/40 + θ})` (`pl_invLevels`), from Chebyshev (`card_levels_ge`).
-/

@[expose] public section

namespace ThreeSquares

open Real

theorem pl_omega (θ : ℝ) (hθ : 0 < θ) : PowLe (fun n => ((2 * n).primeFactors.card : ℝ)) θ := by
  obtain ⟨C, hC, h⟩ := pow_card_primeFactors_le_rpow 2 (by norm_num) θ hθ
  refine ⟨C * 2 ^ θ, 1, fun n hn => ⟨Nat.cast_nonneg _, ?_⟩⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ((2 * n).primeFactors.card : ℝ) ≤ (2 : ℝ) ^ (2 * n).primeFactors.card := by
    exact_mod_cast (Nat.lt_two_pow_self).le
  calc ((2 * n).primeFactors.card : ℝ) ≤ (2 : ℝ) ^ (2 * n).primeFactors.card := h1
    _ ≤ C * ((2 * n : ℕ) : ℝ) ^ θ := h _ (by omega)
    _ = C * 2 ^ θ * (n : ℝ) ^ θ := by push_cast; rw [Real.mul_rpow (by norm_num) hn0.le]; ring

theorem pl_lg (θ : ℝ) (hθ : 0 < θ) : PowLe (fun n => 1 + Real.log (4 * (pP0 n : ℝ) + 1)) θ :=
  ((PowLe.log_add_one θ hθ).cmul 4 (by norm_num)).of_le 3 fun n hn => by
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hP : (pP0 n : ℝ) ≤ n := by
      refine (Nat.floor_le (by positivity)).trans ?_
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ n) (show (11 / 40 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have hP0 : (0 : ℝ) ≤ pP0 n := Nat.cast_nonneg _
    have h9 : (9 : ℝ) ≤ n * n := by nlinarith
    have hx : 4 * (pP0 n : ℝ) + 1 ≤ (n : ℝ) ^ 3 := by
      have : (n : ℝ) ^ 3 = (n * n) * n := by ring
      rw [this]; nlinarith
    have := log_le_mul_log _ 3 n (by omega) (by linarith) hx
    refine ⟨?_, by push_cast at this; linarith⟩
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 * (pP0 n : ℝ) + 1 by linarith)
    linarith

theorem card_levels_lower (θ : ℝ) (hθ : 0 < θ) :
    ∃ c > 0, ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → c * (n : ℝ) ^ (11 / 40 - θ) ≤ ((levels n (pP0 n)).card : ℝ) := by
  -- the error terms
  have hs : PowLe (fun n => Real.sqrt ((4 * pP0 n : ℕ) : ℝ)) (11 / 80) := by
    have := (pl_P (1 / 10000) (by norm_num) (by norm_num)).sqrt
    exact this.mono (by norm_num)
  have hG : PowLe (fun n => ((2 * n).primeFactors.card : ℝ) * (1 + Real.log (4 * (pP0 n : ℝ) + 1)) +
      (1 + Real.log (4 * (pP0 n : ℝ) + 1)) +
      2 * Real.sqrt ((4 * pP0 n : ℕ) : ℝ) * (1 + Real.log (4 * (pP0 n : ℝ) + 1))) (1 / 5) := by
    have a := ((pl_omega (1 / 100) (by norm_num)).mul (pl_lg (1 / 100) (by norm_num))).mono
      (show (1 / 100 + 1 / 100 : ℝ) ≤ 1 / 5 by norm_num)
    have b := (pl_lg (1 / 100) (by norm_num)).mono (show (1 / 100 : ℝ) ≤ 1 / 5 by norm_num)
    have c := ((hs.cmul 2 (by norm_num)).mul (pl_lg (1 / 100) (by norm_num))).mono
      (show (11 / 80 + 1 / 100 : ℝ) ≤ 1 / 5 by norm_num)
    exact (a.add b).add c
  obtain ⟨NG, hNG⟩ := (hG.cmul (2 / Real.log 2) (by positivity)).eventually_le
    (show (1 / 5 : ℝ) < 11 / 40 by norm_num)
  obtain ⟨Cl, Nl, hl⟩ := pl_lg θ hθ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log 2 / (2 * max Cl 1), by positivity, max 3 (max NG Nl), fun n hn => ?_⟩
  simp only [max_le_iff] at hn
  obtain ⟨hn3, hnG, hnl⟩ := hn
  have hn0 : (0 : ℝ) < n := by have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
                               linarith
  have gP : (1 / 2) * (n : ℝ) ^ (11 / 40 : ℝ) ≤ (pP0 n : ℝ) := floor_rpow_ge _ (by norm_num) n (by omega)
  have hP1 : 1 ≤ pP0 n := floor_rpow_pos _ (by norm_num) n (by omega)
  have hP1R : (1 : ℝ) ≤ pP0 n := by exact_mod_cast hP1
  have hcl := card_levels_ge n (pP0 n) (by omega) hP1
  set lg := 1 + Real.log (4 * (pP0 n : ℝ) + 1)
  set ω := ((2 * n).primeFactors.card : ℝ)
  set L := ((levels n (pP0 n)).card : ℝ)
  have hl4 : Real.log (4 * (pP0 n : ℝ)) ≤ lg := by
    have := Real.log_le_log (by positivity) (show 4 * (pP0 n : ℝ) ≤ 4 * (pP0 n : ℝ) + 1 by linarith)
    simp only [lg]; linarith
  have hl40 : 0 < Real.log (4 * (pP0 n : ℝ)) := Real.log_pos (by linarith)
  have hl41 : Real.log (4 * (pP0 n : ℝ) + 1) ≤ lg := by simp only [lg]; linarith
  have hG' := hNG n hnG
  have hω0 : 0 ≤ ω := Nat.cast_nonneg _
  have hs0 : 0 ≤ Real.sqrt (4 * (pP0 n : ℝ)) := Real.sqrt_nonneg _
  have hsq : Real.sqrt ((4 * pP0 n : ℕ) : ℝ) = Real.sqrt (4 * (pP0 n : ℝ)) := by push_cast; rfl
  rw [hsq] at hG'
  -- `L log(4P₀) ≥ P₀ log 2`
  have hG2 : ω * lg + lg + 2 * Real.sqrt (4 * (pP0 n : ℝ)) * lg ≤ (pP0 n : ℝ) * Real.log 2 := by
    have : 2 / Real.log 2 * (ω * lg + lg + 2 * Real.sqrt (4 * (pP0 n : ℝ)) * lg) ≤ 2 * (pP0 n : ℝ) := by
      linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hlog2] at this
    linarith
  have hkey : (pP0 n : ℝ) * Real.log 2 ≤ L * Real.log (4 * (pP0 n : ℝ)) := by
    have h1 : 2 * Real.sqrt (4 * (pP0 n : ℝ)) * Real.log (4 * (pP0 n : ℝ)) ≤
        2 * Real.sqrt (4 * (pP0 n : ℝ)) * lg := mul_le_mul_of_nonneg_left hl4 (by positivity)
    have h2 : ω * Real.log (4 * (pP0 n : ℝ)) ≤ ω * lg := mul_le_mul_of_nonneg_left hl4 hω0
    nlinarith
  -- `log(4P₀) ≤ max Cl 1 · n^θ`
  obtain ⟨-, hlb⟩ := hl n hnl
  have hlb' : Real.log (4 * (pP0 n : ℝ)) ≤ max Cl 1 * (n : ℝ) ^ θ :=
    hl4.trans (hlb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have e : (n : ℝ) ^ (11 / 40 : ℝ) = (n : ℝ) ^ (11 / 40 - θ) * (n : ℝ) ^ θ := by
    rw [← Real.rpow_add hn0]; ring_nf
  have hC : 0 < max Cl 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hnt : 0 < (n : ℝ) ^ θ := by positivity
  -- conclude
  have h3 : (1 / 2) * (n : ℝ) ^ (11 / 40 - θ) * (n : ℝ) ^ θ * Real.log 2 ≤ L * (max Cl 1 * (n : ℝ) ^ θ) := by
    calc (1 / 2) * (n : ℝ) ^ (11 / 40 - θ) * (n : ℝ) ^ θ * Real.log 2
        = (1 / 2) * (n : ℝ) ^ (11 / 40 : ℝ) * Real.log 2 := by rw [e]; ring
      _ ≤ (pP0 n : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right gP hlog2.le
      _ ≤ L * Real.log (4 * (pP0 n : ℝ)) := hkey
      _ ≤ L * (max Cl 1 * (n : ℝ) ^ θ) := mul_le_mul_of_nonneg_left hlb' hL0
  have h4 : Real.log 2 / (2 * max Cl 1) * (n : ℝ) ^ (11 / 40 - θ) * ((n : ℝ) ^ θ * max Cl 1) ≤
      L * ((n : ℝ) ^ θ * max Cl 1) := by
    have : Real.log 2 / (2 * max Cl 1) * (n : ℝ) ^ (11 / 40 - θ) * ((n : ℝ) ^ θ * max Cl 1) =
        (1 / 2) * (n : ℝ) ^ (11 / 40 - θ) * (n : ℝ) ^ θ * Real.log 2 := by field_simp
    rw [this]; linarith
  exact le_of_mul_le_mul_right h4 (by positivity)

theorem pl_invLevels (θ : ℝ) (hθ : 0 < θ) :
    PowLe (fun n => 1 / ((levels n (pP0 n)).card : ℝ)) (-(11 / 40 - θ)) := by
  obtain ⟨c, hc, N₀, h⟩ := card_levels_lower θ hθ
  exact PowLe.inv_of_ge (f := fun n => ((levels n (pP0 n)).card : ℝ)) c _ hc N₀ h

end ThreeSquares
