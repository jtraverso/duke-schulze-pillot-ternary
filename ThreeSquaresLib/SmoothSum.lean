/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Split
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sums over smooth numbers

For a finite set of primes `S` and `σ > 0`,
`∑_{r ≤ X, primes of r in S} r^{−σ} ≤ ∏_{ℓ ∈ S} (1 − ℓ^{−σ})^{−1}` (`sum_smooth_le`).
-/

@[expose] public section

namespace ThreeSquares

open Finset

theorem geom_rpow_le (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (σ : ℝ) (hσ : 0 < σ) (E : ℕ) :
    ∑ e ∈ range E, ((ℓ : ℝ) ^ e) ^ (-σ) ≤ (1 - (ℓ : ℝ) ^ (-σ))⁻¹ := by
  have hx0 : 0 ≤ (ℓ : ℝ) ^ (-σ) := by positivity
  have hx1 : (ℓ : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hℓ) (by linarith)
  have e : ∀ e : ℕ, ((ℓ : ℝ) ^ e) ^ (-σ) = ((ℓ : ℝ) ^ (-σ)) ^ e := by
    intro e
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul (by positivity), mul_comm]
  simp_rw [e]
  exact ((summable_geometric_of_lt_one hx0 hx1).sum_le_tsum _ (fun _ _ => by positivity)).trans
    (le_of_eq (tsum_geometric_of_lt_one hx0 hx1))

open Classical in
/-- **Euler-product bound for smooth numbers.** -/
theorem sum_smooth_le (σ : ℝ) (hσ : 0 < σ) :
    ∀ (S : Finset ℕ), (∀ ℓ ∈ S, ℓ.Prime) → ∀ X : ℕ,
      ∑ r ∈ (range X).filter (fun r => 0 < r ∧ ∀ ℓ, ℓ.Prime → ℓ ∣ r → ℓ ∈ S), (r : ℝ) ^ (-σ) ≤
        ∏ ℓ ∈ S, (1 - (ℓ : ℝ) ^ (-σ))⁻¹ := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ X
    simp only [Finset.notMem_empty, imp_false, Finset.prod_empty]
    -- only `r = 1`
    calc ∑ r ∈ (range X).filter (fun r => 0 < r ∧ ∀ ℓ, ℓ.Prime → ¬ ℓ ∣ r), (r : ℝ) ^ (-σ)
        ≤ ∑ r ∈ ({1} : Finset ℕ), (r : ℝ) ^ (-σ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun r hr => ?_) (fun _ _ _ => by positivity)
          simp only [Finset.mem_filter] at hr
          simp only [Finset.mem_singleton]
          by_contra h1
          obtain ⟨ℓ, hℓ, hd⟩ := Nat.exists_prime_and_dvd h1
          exact hr.2.2 ℓ hℓ hd
      _ = 1 := by simp
  | insert ℓ S hℓS ih =>
    intro hS X
    have hℓ : ℓ.Prime := hS ℓ (Finset.mem_insert_self _ _)
    have ih' := ih (fun q hq => hS q (Finset.mem_insert_of_mem hq)) X
    rw [Finset.prod_insert hℓS]
    -- every `r` is `ℓ^e r'` with `r'` `S`-smooth
    set T := (range X).filter (fun r => 0 < r ∧ ∀ q, q.Prime → q ∣ r → q ∈ S)
    set T' := (range X).filter (fun r => 0 < r ∧ ∀ q, q.Prime → q ∣ r → q ∈ insert ℓ S)
    have hcover : ∀ r ∈ T', ∃ e < X, ∃ r' ∈ T, r = ℓ ^ e * r' := by
      intro r hr
      simp only [T', Finset.mem_filter, Finset.mem_range] at hr
      obtain ⟨e, r', hnd, hrr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hr.2.1.ne' ℓ hℓ.one_lt.ne'
      have hr'0 : 0 < r' := Nat.pos_of_ne_zero (by rintro rfl; simp at hrr; omega)
      have hle : r' ≤ r := by rw [hrr]; exact Nat.le_mul_of_pos_left _ (pow_pos hℓ.pos e)
      have hle2 : e < X := by
        have : e < ℓ ^ e := Nat.lt_pow_self hℓ.one_lt
        have : ℓ ^ e ≤ r := by rw [hrr]; exact Nat.le_mul_of_pos_right _ hr'0
        omega
      refine ⟨e, hle2, r', ?_, hrr⟩
      simp only [T, Finset.mem_filter, Finset.mem_range]
      refine ⟨by omega, hr'0, fun q hq hqd => ?_⟩
      have := hr.2.2 q hq (hrr ▸ dvd_mul_of_dvd_right hqd _)
      rcases Finset.mem_insert.mp this with h | h
      · subst h; exact absurd hqd hnd
      · exact h
    have himg : T' ⊆ ((range X) ×ˢ T).image (fun x : ℕ × ℕ => (ℓ ^ x.1 * x.2 : ℕ)) := by
      intro r hr
      obtain ⟨e, he, r', hr', rfl⟩ := hcover r hr
      exact Finset.mem_image.mpr ⟨(e, r'), Finset.mem_product.mpr ⟨Finset.mem_range.mpr he, hr'⟩, rfl⟩
    calc ∑ r ∈ T', (r : ℝ) ^ (-σ)
        ≤ ∑ r ∈ ((range X) ×ˢ T).image (fun x : ℕ × ℕ => (ℓ ^ x.1 * x.2 : ℕ)), (r : ℝ) ^ (-σ) :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
      _ ≤ ∑ x ∈ (range X) ×ˢ T, (((ℓ ^ x.1 * x.2 : ℕ) : ℝ)) ^ (-σ) :=
          Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)
      _ = (∑ e ∈ range X, ((ℓ : ℝ) ^ e) ^ (-σ)) * ∑ r' ∈ T, (r' : ℝ) ^ (-σ) := by
          rw [Finset.sum_product, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun r' _ => ?_
          push_cast
          rw [Real.mul_rpow (by positivity) (by positivity)]
      _ ≤ (1 - (ℓ : ℝ) ^ (-σ))⁻¹ * ∏ q ∈ S, (1 - (q : ℝ) ^ (-σ))⁻¹ := by
          refine mul_le_mul (geom_rpow_le ℓ hℓ.two_le σ hσ X) ih' (Finset.sum_nonneg fun _ _ => by positivity) ?_
          have hx1 : (ℓ : ℝ) ^ (-σ) < 1 :=
            Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hℓ.one_lt) (by linarith)
          have := sub_pos.mpr hx1
          positivity

end ThreeSquares
