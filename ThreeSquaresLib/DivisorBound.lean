/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The divisor bound

* `prod_primeFactors_le`: a product over the prime factorization whose local factors are `≤ 1`
  for large primes and `≤ C` otherwise is `≤ C ^ T`;
* `card_divisors_le_rpow`: `τ(m) ≤ C_ε m^ε`;
* `pow_card_primeFactors_le_rpow`: `K^{ω(m)} ≤ C_{K,ε} m^ε`.
-/

@[expose] public section

namespace ThreeSquares

open Finset

theorem prod_primeFactors_le (m : ℕ) (f : ℕ → ℕ → ℝ) (T : ℕ) (C : ℝ) (hC : 1 ≤ C)
    (h0 : ∀ p e, p.Prime → 1 ≤ e → 0 ≤ f p e)
    (hbig : ∀ p e, p.Prime → 1 ≤ e → T ≤ p → f p e ≤ 1)
    (hsmall : ∀ p e, p.Prime → 1 ≤ e → f p e ≤ C) :
    ∏ p ∈ m.primeFactors, f p (m.factorization p) ≤ C ^ T := by
  have hmem : ∀ p ∈ m.primeFactors, p.Prime ∧ 1 ≤ m.factorization p := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp)
        (Nat.mem_primeFactors.mp hp).2.2 (Nat.dvd_of_mem_primeFactors hp))⟩
  rw [← Finset.prod_filter_mul_prod_filter_not m.primeFactors (fun p => p < T)]
  have h1 : ∏ p ∈ m.primeFactors.filter (fun p => p < T), f p (m.factorization p) ≤
      C ^ (m.primeFactors.filter (fun p => p < T)).card := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)
    · have := hmem p (Finset.mem_filter.mp hp).1; exact h0 p _ this.1 this.2
    · have := hmem p (Finset.mem_filter.mp hp).1; exact hsmall p _ this.1 this.2
  have h2 : ∏ p ∈ m.primeFactors.filter (fun p => ¬ p < T), f p (m.factorization p) ≤ 1 := by
    refine Finset.prod_le_one₀ (fun p hp => ?_) (fun p hp => ?_)
    · have := hmem p (Finset.mem_filter.mp hp).1; exact h0 p _ this.1 this.2
    · have := hmem p (Finset.mem_filter.mp hp).1
      exact hbig p _ this.1 this.2 (not_lt.mp (Finset.mem_filter.mp hp).2)
  have hcard : (m.primeFactors.filter (fun p => p < T)).card ≤ T := by
    calc (m.primeFactors.filter (fun p => p < T)).card ≤ (range T).card := by
          refine Finset.card_le_card fun p hp => ?_
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      _ = T := Finset.card_range T
  have hA0 : 0 ≤ ∏ p ∈ m.primeFactors.filter (fun p => p < T), f p (m.factorization p) :=
    Finset.prod_nonneg fun p hp => by
      have := hmem p (Finset.mem_filter.mp hp).1; exact h0 p _ this.1 this.2
  calc _ ≤ C ^ (m.primeFactors.filter (fun p => p < T)).card * 1 :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun p hp => by
          have := hmem p (Finset.mem_filter.mp hp).1; exact h0 p _ this.1 this.2)
          (pow_nonneg (by linarith) _)
    _ ≤ C ^ T := by rw [mul_one]; exact pow_le_pow_right₀ hC hcard

/-- `m^ε = ∏_{p^e ∥ m} (p^e)^ε`. -/
theorem rpow_eq_prod_primeFactors {m : ℕ} (hm : m ≠ 0) (ε : ℝ) :
    (m : ℝ) ^ ε = ∏ p ∈ m.primeFactors, ((p : ℝ) ^ m.factorization p) ^ ε := by
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hm]
  push_cast
  exact (Real.finsetProd_rpow _ _ (fun p _ => by positivity) ε).symm

theorem add_one_le_two_rpow (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (e : ℕ) :
    (e + 1 : ℝ) ≤ (2 : ℝ) ^ ((e : ℝ) * ε) / (ε * Real.log 2) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl1 : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num); linarith
  have hεl : 0 < ε * Real.log 2 := mul_pos hε hl
  rw [le_div_iff₀ hεl, Real.rpow_def_of_pos (by norm_num)]
  have := Real.add_one_le_exp (Real.log 2 * ((e : ℝ) * ε))
  have hεl1 : ε * Real.log 2 ≤ 1 := by nlinarith
  nlinarith

/-- **Divisor bound.** -/
theorem card_divisors_le_rpow (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≠ 0 → ((m.divisors.card : ℕ) : ℝ) ≤ C * (m : ℝ) ^ ε := by
  set C₁ : ℝ := max 1 (1 / (ε * Real.log 2))
  set T : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊
  refine ⟨C₁ ^ T, pow_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) _, fun m hm => ?_⟩
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set f : ℕ → ℕ → ℝ := fun p e => ((e : ℝ) + 1) / ((p : ℝ) ^ e) ^ ε
  have hpos : ∀ (p e : ℕ), p.Prime → 0 < ((p : ℝ) ^ e) ^ ε := fun p e hp =>
    Real.rpow_pos_of_pos (pow_pos (by exact_mod_cast hp.pos) _) _
  have hprod := prod_primeFactors_le m f T C₁ (le_max_left _ _)
    (fun p e hp _ => div_nonneg (by positivity) (hpos p e hp).le)
    (fun p e hp _ hT => by
      simp only [f]
      rw [div_le_one (hpos p e hp)]
      have hp2 : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
        have h1 : (2 : ℝ) ^ (1 / ε) ≤ p := le_trans (Nat.le_ceil _) (by exact_mod_cast hT)
        calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
              rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one]
          _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) h1 hε.le
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm, Real.rpow_mul
        (by positivity), Real.rpow_natCast]
      calc (e : ℝ) + 1 ≤ 2 ^ e := by
            have := Nat.lt_two_pow_self (n := e); exact_mod_cast this
        _ ≤ ((p : ℝ) ^ ε) ^ e := pow_le_pow_left₀ (by norm_num) hp2 e)
    (fun p e hp _ => by
      simp only [f]
      rw [div_le_iff₀ (hpos p e hp)]
      have hp2 : (2 : ℝ) ^ ((e : ℝ) * ε) ≤ ((p : ℝ) ^ e) ^ ε := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) le_rfl |>.trans
          (Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp.two_le) (by positivity))
      calc (e : ℝ) + 1 ≤ (2 : ℝ) ^ ((e : ℝ) * ε) / (ε * Real.log 2) := add_one_le_two_rpow ε hε hε1 e
        _ = (1 / (ε * Real.log 2)) * (2 : ℝ) ^ ((e : ℝ) * ε) := by ring
        _ ≤ C₁ * ((p : ℝ) ^ e) ^ ε :=
          mul_le_mul (le_max_right _ _) hp2 (by positivity) (le_trans zero_le_one (le_max_left _ _)))
  have hτ : ((m.divisors.card : ℕ) : ℝ) = ∏ p ∈ m.primeFactors, ((m.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hm]; push_cast; rfl
  have hsplit : ∏ p ∈ m.primeFactors, ((m.factorization p : ℝ) + 1) =
      (∏ p ∈ m.primeFactors, f p (m.factorization p)) * (m : ℝ) ^ ε := by
    rw [rpow_eq_prod_primeFactors hm, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    simp only [f]
    rw [div_mul_cancel₀ _ (hpos p _ (Nat.prime_of_mem_primeFactors hp)).ne']
  rw [hτ, hsplit]
  exact mul_le_mul_of_nonneg_right hprod (by positivity)

/-- **`K^{ω(m)} ≤ C m^ε`.** -/
theorem pow_card_primeFactors_le_rpow (K : ℝ) (hK : 1 ≤ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≠ 0 → K ^ m.primeFactors.card ≤ C * (m : ℝ) ^ ε := by
  set T : ℕ := ⌈K ^ (1 / ε)⌉₊
  refine ⟨K ^ T, pow_pos (by linarith) _, fun m hm => ?_⟩
  set f : ℕ → ℕ → ℝ := fun p e => K / ((p : ℝ) ^ e) ^ ε
  have hpos : ∀ (p e : ℕ), p.Prime → 0 < ((p : ℝ) ^ e) ^ ε := fun p e hp =>
    Real.rpow_pos_of_pos (pow_pos (by exact_mod_cast hp.pos) _) _
  have hprod := prod_primeFactors_le m f T K hK
    (fun p e hp _ => div_nonneg (by linarith) (hpos p e hp).le)
    (fun p e hp he hT => by
      simp only [f]
      rw [div_le_one (hpos p e hp)]
      have hpK : K ≤ (p : ℝ) ^ ε := by
        have h1 : K ^ (1 / ε) ≤ p := le_trans (Nat.le_ceil _) (by exact_mod_cast hT)
        calc K = (K ^ (1 / ε)) ^ ε := by
              rw [← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hε.ne', Real.rpow_one]
          _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) h1 hε.le
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm, Real.rpow_mul
        (by positivity), Real.rpow_natCast]
      calc K = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ e := pow_le_pow_right₀ hK he
        _ ≤ ((p : ℝ) ^ ε) ^ e := pow_le_pow_left₀ (by linarith) hpK e)
    (fun p e hp he => by
      simp only [f]
      rw [div_le_iff₀ (hpos p e hp)]
      have : 1 ≤ ((p : ℝ) ^ e) ^ ε :=
        Real.one_le_rpow (one_le_pow₀ (by exact_mod_cast hp.one_lt.le)) hε.le
      nlinarith)
  have hsplit : K ^ m.primeFactors.card =
      (∏ p ∈ m.primeFactors, f p (m.factorization p)) * (m : ℝ) ^ ε := by
    rw [rpow_eq_prod_primeFactors hm, ← Finset.prod_mul_distrib, ← Finset.prod_const]
    refine Finset.prod_congr rfl fun p hp => ?_
    simp only [f]
    rw [div_mul_cancel₀ _ (hpos p _ (Nat.prime_of_mem_primeFactors hp)).ne']
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hprod (by positivity)

end ThreeSquares
