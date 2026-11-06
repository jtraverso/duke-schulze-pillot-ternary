/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The divisor bound

`d(n) ≤ C_ε n^ε` for every `ε > 0` (`card_divisors_le_rpow`). The ratio `d(n) / n^ε` is
multiplicative; at a prime power it is `(k + 1) / p^{kε}`, which is at most
`B = 1 + 1/(ε log 2)` for every prime and at most `1` for `p ≥ 2^{1/ε}`.
-/

@[expose] public section

namespace DSP

open ArithmeticFunction

/-- `(k + 1) ≤ B (1 + k ε log 2)` with `B = 1 + 1/(ε log 2)`. -/
theorem succ_le_B_mul {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    (k : ℝ) + 1 ≤ (1 + 1 / (ε * Real.log 2)) * (1 + k * (ε * Real.log 2)) := by
  have hL : 0 < ε * Real.log 2 := mul_pos hε (Real.log_pos (by norm_num))
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : (1 / (ε * Real.log 2)) * (k * (ε * Real.log 2)) = k := by field_simp
  nlinarith [mul_nonneg hk hL.le, one_div_pos.mpr hL]

/-- The bound at a prime power. -/
theorem prime_pow_ratio_le {ε : ℝ} (hε : 0 < ε) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((k : ℝ) + 1) / ((p : ℝ) ^ ε) ^ k ≤ 1 + 1 / (ε * Real.log 2) := by
  have hL : 0 < ε * Real.log 2 := mul_pos hε (Real.log_pos (by norm_num))
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h2 : 1 + ε * Real.log 2 ≤ (p : ℝ) ^ ε := by
    calc 1 + ε * Real.log 2 ≤ Real.exp (ε * Real.log 2) := by
          have := Real.add_one_le_exp (ε * Real.log 2); linarith
      _ = (2 : ℝ) ^ ε := by rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
      _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num) hp2 hε.le
  have h3 : 1 + k * (ε * Real.log 2) ≤ ((p : ℝ) ^ ε) ^ k :=
    (one_add_mul_le_pow (by linarith) k).trans (pow_le_pow_left₀ (by linarith) h2 k)
  have hpos : 0 < ((p : ℝ) ^ ε) ^ k := by
    have : (0 : ℝ) < (p : ℝ) ^ ε := Real.rpow_pos_of_pos (by linarith) ε
    positivity
  rw [div_le_iff₀ hpos]
  calc (k : ℝ) + 1 ≤ (1 + 1 / (ε * Real.log 2)) * (1 + k * (ε * Real.log 2)) :=
        succ_le_B_mul hε k
    _ ≤ (1 + 1 / (ε * Real.log 2)) * ((p : ℝ) ^ ε) ^ k := by
        apply mul_le_mul_of_nonneg_left h3
        have := one_div_pos.mpr hL; linarith

/-- The bound at a large prime. -/
theorem prime_pow_ratio_le_one {ε : ℝ} (hε : 0 < ε) {p : ℕ}
    (hp : (2 : ℝ) ^ (1 / ε) ≤ p) (k : ℕ) : ((k : ℝ) + 1) / ((p : ℝ) ^ ε) ^ k ≤ 1 := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hp
  have h2 : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
      _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hp hε.le
  have h3 : (k : ℝ) + 1 ≤ ((p : ℝ) ^ ε) ^ k := by
    calc (k : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self
      _ ≤ ((p : ℝ) ^ ε) ^ k := pow_le_pow_left₀ (by norm_num) h2 k
  have hpos : 0 < ((p : ℝ) ^ ε) ^ k := by
    have : (0 : ℝ) < (p : ℝ) ^ ε := Real.rpow_pos_of_pos hp0 ε
    positivity
  rw [div_le_iff₀ hpos, one_mul]
  exact h3

/-- The ratio `d(n) / n^ε`. -/
noncomputable def divRatio (ε : ℝ) (n : ℕ) : ℝ := (sigma 0 n : ℝ) / (n : ℝ) ^ ε

theorem divRatio_mul {ε : ℝ} {m n : ℕ} (h : m.Coprime n) :
    divRatio ε (m * n) = divRatio ε m * divRatio ε n := by
  unfold divRatio
  rw [isMultiplicative_sigma.map_mul_of_coprime h, Nat.cast_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), div_mul_div_comm]

theorem divRatio_prime_pow {ε : ℝ} {p : ℕ} (hp : p.Prime) (k : ℕ) :
    divRatio ε (p ^ k) = ((k : ℝ) + 1) / ((p : ℝ) ^ ε) ^ k := by
  unfold divRatio
  rw [sigma_zero_apply_prime_pow hp]
  push_cast
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
    ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]

/-- **The divisor bound**: `d(n) ≤ C_ε n^ε`. -/
theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  set B : ℝ := 1 + 1 / (ε * Real.log 2) with hB
  have hL : 0 < ε * Real.log 2 := mul_pos hε (Real.log_pos (by norm_num))
  have hB1 : 1 ≤ B := by have := one_div_pos.mpr hL; linarith
  set P : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊ with hP
  refine ⟨B ^ P, by positivity, fun n hn => ?_⟩
  have hfac := Nat.multiplicative_factorization (divRatio ε) (fun x y h => divRatio_mul h)
    (by simp [divRatio]) (Nat.pos_iff_ne_zero.mp hn)
  -- each factor is at most `B`, and at most `1` for large primes
  have hbound : divRatio ε n ≤ B ^ P := by
    rw [hfac, Finsupp.prod]
    have hle : ∀ p ∈ n.factorization.support,
        divRatio ε (p ^ n.factorization p) ≤ if p < P then B else 1 := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
      rw [divRatio_prime_pow hpp]
      split_ifs with hlt
      · exact prime_pow_ratio_le hε hpp _
      · apply prime_pow_ratio_le_one hε
        have : (P : ℝ) ≤ p := by exact_mod_cast not_lt.mp hlt
        exact (Nat.le_ceil _).trans this
    have hnn : ∀ p ∈ n.factorization.support, 0 ≤ divRatio ε (p ^ n.factorization p) :=
      fun p _ => div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    calc ∏ p ∈ n.factorization.support, divRatio ε (p ^ n.factorization p)
        ≤ ∏ p ∈ n.factorization.support, (if p < P then B else 1) :=
          Finset.prod_le_prod₀ hnn hle
      _ = ∏ p ∈ n.factorization.support.filter (· < P), B := by
          rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
      _ = B ^ (n.factorization.support.filter (· < P)).card := Finset.prod_const B
      _ ≤ B ^ P := by
          apply pow_le_pow_right₀ hB1
          calc (n.factorization.support.filter (· < P)).card
              ≤ (Finset.range P).card := Finset.card_le_card (fun p hp => by
                simp only [Finset.mem_filter] at hp; exact Finset.mem_range.mpr hp.2)
            _ = P := Finset.card_range P
  have hpos : 0 < (n : ℝ) ^ ε := Real.rpow_pos_of_pos (by exact_mod_cast hn) ε
  unfold divRatio at hbound
  rw [sigma_zero_apply, div_le_iff₀ hpos] at hbound
  exact hbound

end DSP
