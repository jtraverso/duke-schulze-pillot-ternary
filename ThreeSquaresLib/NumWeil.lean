/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.BlockBounds

/-!
# Numerics for the Weil sums of the methods

`∑_{b ∈ Bs} (M/b + c₀ + log b) 2^{ω(b)} √b √(sfp b) τ(b) ≤ (M/L + c₀ + log U) C² U^{1/2 + 2ε} · 3U(1 + log U)`
for `Bs ⊆ [L, U]` (`sum_weil_le`).
-/

@[expose] public section

namespace ThreeSquares

open Finset

theorem two_pow_omega_mul_tau_le (b : ℕ) (hb : b ≠ 0) (C ε : ℝ) (hC : 0 < C)
    (hτ : ((b.divisors.card : ℕ) : ℝ) ≤ C * (b : ℝ) ^ ε) :
    (2 : ℝ) ^ b.primeFactors.card * b.divisors.card ≤ C ^ 2 * (b : ℝ) ^ (2 * ε) := by
  have h1 : (2 : ℝ) ^ b.primeFactors.card ≤ b.divisors.card := by
    exact_mod_cast two_pow_card_primeFactors_le b hb
  have h0 : (0 : ℝ) ≤ b.divisors.card := Nat.cast_nonneg _
  have hb' : (0 : ℝ) ≤ (b : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc (2 : ℝ) ^ b.primeFactors.card * b.divisors.card ≤ (b.divisors.card : ℝ) * b.divisors.card :=
        mul_le_mul_of_nonneg_right h1 h0
    _ ≤ (C * (b : ℝ) ^ ε) * (C * (b : ℝ) ^ ε) := mul_le_mul hτ hτ h0 (by positivity)
    _ = C ^ 2 * (b : ℝ) ^ (2 * ε) := by
        have hbpos : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
        rw [show (2 : ℝ) * ε = ε + ε by ring, Real.rpow_add hbpos]
        ring

/-- **The Weil sum of the methods.** -/
theorem sum_weil_le (Bs : Finset ℕ) (U : ℕ) (hBs : ∀ b ∈ Bs, 0 < b ∧ b ≤ U) (G : ℕ → ℝ) (G₀ : ℝ)
    (hG : ∀ b ∈ Bs, 0 ≤ G b ∧ G b ≤ G₀) (hG₀ : 0 ≤ G₀) (C ε : ℝ) (hC : 0 < C) (hε : 0 ≤ ε)
    (hτ : ∀ m : ℕ, m ≠ 0 → ((m.divisors.card : ℕ) : ℝ) ≤ C * (m : ℝ) ^ ε) :
    ∑ b ∈ Bs, G b * (2 ^ b.primeFactors.card * Real.sqrt b * Real.sqrt (sfp b) * b.divisors.card) ≤
      G₀ * (C ^ 2 * (U : ℝ) ^ (2 * ε) * Real.sqrt U) * (3 * U * (1 + Real.log U)) := by
  have hterm : ∀ b ∈ Bs, G b * (2 ^ b.primeFactors.card * Real.sqrt b * Real.sqrt (sfp b) * b.divisors.card) ≤
      G₀ * (C ^ 2 * (U : ℝ) ^ (2 * ε) * Real.sqrt U) * Real.sqrt (sfp b) := by
    intro b hb
    obtain ⟨hb0, hbU⟩ := hBs b hb
    have h1 := two_pow_omega_mul_tau_le b hb0.ne' C ε hC (hτ b hb0.ne')
    have h2 : (b : ℝ) ^ (2 * ε) ≤ (U : ℝ) ^ (2 * ε) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hbU) (by linarith)
    have h3 : Real.sqrt b ≤ Real.sqrt U := Real.sqrt_le_sqrt (by exact_mod_cast hbU)
    have hs := Real.sqrt_nonneg (sfp b : ℝ)
    calc G b * (2 ^ b.primeFactors.card * Real.sqrt b * Real.sqrt (sfp b) * b.divisors.card)
        = G b * ((2 ^ b.primeFactors.card * b.divisors.card) * Real.sqrt b) * Real.sqrt (sfp b) := by ring
      _ ≤ G₀ * ((C ^ 2 * (U : ℝ) ^ (2 * ε)) * Real.sqrt U) * Real.sqrt (sfp b) := by
          have hX : (2 : ℝ) ^ b.primeFactors.card * b.divisors.card ≤ C ^ 2 * (U : ℝ) ^ (2 * ε) :=
            h1.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg C))
          have hXs : (2 : ℝ) ^ b.primeFactors.card * b.divisors.card * Real.sqrt b ≤
              C ^ 2 * (U : ℝ) ^ (2 * ε) * Real.sqrt U :=
            mul_le_mul hX h3 (Real.sqrt_nonneg _) (by positivity)
          have hGX := mul_le_mul (hG b hb).2 hXs (by positivity) hG₀
          exact mul_le_mul_of_nonneg_right hGX hs
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ∑ b ∈ Bs, Real.sqrt (sfp b) ≤ ∑ b ∈ Icc 1 U, Real.sqrt (sfp b) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => Finset.mem_Icc.mpr ⟨(hBs b hb).1, (hBs b hb).2⟩)
          (fun _ _ _ => Real.sqrt_nonneg _)
    _ ≤ 3 * U * (1 + Real.log U) := sum_sqrt_sfp_le U

end ThreeSquares
