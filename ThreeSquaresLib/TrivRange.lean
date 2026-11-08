/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.TrivWeights

/-!
# The trivial ranges `c ≤ y` and `c > Y`

For a level `8p` (`p ∤ 2n` prime), with `Z(s) = ∑ q^{−s}` and `Π(σ) = ∏_{ℓ ∣ 2n} (1 − ℓ^{−σ})^{−1}`:

* `low_range`: `∑_{c ≤ y, 8p ∣ c} ‖cfac(c) T_c‖ ≤ D √2 C y^{ε+s} p^{−s} Z(s) Π(s − 1/2)` for `y ≤ 2πn`;
* `high_range`: `∑_{Y < c ≤ N, 8p ∣ c} ‖cfac(c) T_c‖ ≤ cH √2 C Y^{−α} p^{−s} Z(s) Π(s − 1/2)` for `n ≤ Y`,
  `s + α = k − 1/2 − ε`, `α ≥ 0`.
-/

@[expose] public section

namespace ThreeSquares

open Finset Polynomial

open scoped Real

theorem rankin_low (r q Y s : ℝ) (hr : 0 < r) (hq : 0 < q) (hY : r * q ≤ Y) (hs : 0 ≤ s) :
    Real.sqrt r ≤ Y ^ s * r ^ (-(s - 1 / 2)) * q ^ (-s) := by
  have hrq : 0 < r * q := mul_pos hr hq
  have e : Y ^ s * r ^ (-(s - 1 / 2)) * q ^ (-s) = Real.sqrt r * (Y / (r * q)) ^ s := by
    rw [show -(s - 1 / 2) = (1 : ℝ) / 2 - s by ring, Real.rpow_sub hr, Real.rpow_neg hq.le,
      Real.sqrt_eq_rpow, Real.div_rpow (by linarith) hrq.le, Real.mul_rpow hr.le hq.le]
    field_simp
  rw [e]
  refine le_mul_of_one_le_right (Real.sqrt_nonneg _) (Real.one_le_rpow ?_ hs)
  rw [le_div_iff₀ hrq]; linarith

theorem rankin_high (r q Y s α : ℝ) (hr : 0 < r) (hq : 0 < q) (hY0 : 0 < Y) (hY : Y ≤ r * q)
    (hα : 0 ≤ α) :
    Real.sqrt r * (r * q) ^ (-(s + α)) ≤ Y ^ (-α) * (r ^ (-(s - 1 / 2)) * q ^ (-s)) := by
  have hrq : 0 < r * q := mul_pos hr hq
  have e1 : (r * q) ^ (-(s + α)) = (r * q) ^ (-s) * (r * q) ^ (-α) := by
    rw [← Real.rpow_add hrq]; ring_nf
  have e2 : Real.sqrt r * (r * q) ^ (-s) = r ^ (-(s - 1 / 2)) * q ^ (-s) := by
    rw [Real.mul_rpow hr.le hq.le, Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add hr]
    ring_nf
  have h3 : (r * q) ^ (-α) ≤ Y ^ (-α) := Real.rpow_le_rpow_of_nonpos hY0 hY (by linarith)
  calc Real.sqrt r * (r * q) ^ (-(s + α)) = (Real.sqrt r * (r * q) ^ (-s)) * (r * q) ^ (-α) := by
        rw [e1]; ring
    _ = (r ^ (-(s - 1 / 2)) * q ^ (-s)) * (r * q) ^ (-α) := by rw [e2]
    _ ≤ (r ^ (-(s - 1 / 2)) * q ^ (-s)) * Y ^ (-α) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = Y ^ (-α) * (r ^ (-(s - 1 / 2)) * q ^ (-s)) := by ring

theorem eight_dvd_smooth (n r q : ℕ) (hq : Rough (S2 n) q) (h8 : 8 ∣ r * q) : 8 ∣ r := by
  have h2q : ¬ 2 ∣ q := fun h2 => hq 2 Nat.prime_two h2 (show 2 ∣ 2 * n from dvd_mul_right 2 n)
  have hcop : Nat.Coprime (2 ^ 3) q :=
    Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2q)
  exact hcop.dvd_of_dvd_mul_right h8

open Classical in
/-- **The range `c ≤ y`.** -/
theorem low_range (ℓ n p y : ℕ) (hn : 0 < n) (hp : p.Prime) (hpn : ¬ p ∣ 2 * n) {pp qq : ℂ[X]}
    (hpq : Lip.BesForm (ℓ + 1) pp qq) (hy : (y : ℝ) ≤ 2 * π * n) (C ε s : ℝ) (hC : 0 < C) (hε : 0 ≤ ε)
    (hs : 1 < s) (hτ : ∀ m : ℕ, m ≠ 0 → ((m.divisors.card : ℕ) : ℝ) ≤ C * (m : ℝ) ^ ε) :
    ∑ c ∈ (Icc 1 y).filter (fun c => 8 * p ∣ c), ‖Poin.cfac ℓ n c * Poin.Tc n c‖ ≤
      ‖Poin.Kc ℓ n‖ * (Poin.polyA pp * (1 + 1) ^ pp.natDegree + Poin.polyA qq * (1 + 1) ^ qq.natDegree) *
        Real.sqrt 2 * C * (y : ℝ) ^ (ε + s) *
        ((p : ℝ) ^ (-s) * (∑' q : ℕ, (q : ℝ) ^ (-s)) *
          ∏ ℓ' ∈ (2 * n).primeFactors, (1 - (ℓ' : ℝ) ^ (-(s - 1 / 2)))⁻¹) := by
  set D := ‖Poin.Kc ℓ n‖ * (Poin.polyA pp * (1 + 1) ^ pp.natDegree + Poin.polyA qq * (1 + 1) ^ qq.natDegree)
  have hD : 0 ≤ D := by unfold D; have := Poin.polyA_nonneg pp; have := Poin.polyA_nonneg qq; positivity
  set T := (Icc 1 y).filter (fun c => 8 * p ∣ c)
  have hT : ∀ c ∈ T, 0 < c ∧ c ≤ y := fun c hc => by
    simp only [T, mem_filter, mem_Icc] at hc; exact ⟨hc.1.1, hc.1.2⟩
  set K := D * Real.sqrt 2 * C * (y : ℝ) ^ (ε + s)
  have hK : 0 ≤ K := by positivity
  rw [sum_split_real (S2 n) T y hT]
  have hpt : ∀ r ∈ (range (y + 1)).filter (Smooth (S2 n)), ∀ q ∈ (range (y + 1)).filter (Rough (S2 n)),
      (if r * q ∈ T then ‖Poin.cfac ℓ n (r * q) * Poin.Tc n (r * q)‖ else 0) ≤
        K * (if r * q ∈ T then (r : ℝ) ^ (-(s - 1 / 2)) * (q : ℝ) ^ (-s) else 0) := by
    intro r hr q hq
    have hrs : Smooth (S2 n) r := (mem_filter.mp hr).2
    have hqr : Rough (S2 n) q := (mem_filter.mp hq).2
    by_cases hc : r * q ∈ T
    · rw [if_pos hc, if_pos hc]
      have hc' := hc
      simp only [T, mem_filter, mem_Icc] at hc'
      obtain ⟨⟨hc1, hcy⟩, h8⟩ := hc'
      have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; simp at hc1)
      have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hc1)
      have h8r : 8 ∣ r := eight_dvd_smooth n r q hqr ((dvd_mul_right 8 p).trans h8)
      have h4r : 4 ∣ r := (by norm_num : 4 ∣ 8).trans h8r
      have hTc := norm_Tc_split n r q hrs hqr h4r hr0 hq0
      have hcf := Poin.norm_cfac_low ℓ n hn hpq (r * q) hc1 (le_trans (by exact_mod_cast hcy) hy)
      have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
      have hyR : ((r * q : ℕ) : ℝ) ≤ y := by exact_mod_cast hcy
      have hτq : ((q.divisors.card : ℕ) : ℝ) ≤ C * (y : ℝ) ^ ε := by
        refine (hτ q hq0.ne').trans (mul_le_mul_of_nonneg_left ?_ hC.le)
        refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hε
        refine le_trans ?_ hyR
        exact_mod_cast Nat.le_mul_of_pos_left q hr0
      have hsr := rankin_low r q y s hrR hqR (by push_cast at hyR; exact hyR) (by linarith)
      have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by positivity) hyR
      have hs2 : Real.sqrt (2 * r) = Real.sqrt 2 * Real.sqrt r := Real.sqrt_mul (by norm_num) _
      rw [norm_mul]
      calc ‖Poin.cfac ℓ n (r * q)‖ * ‖Poin.Tc n (r * q)‖
          ≤ ‖Poin.cfac ℓ n (r * q)‖ * (((r * q : ℕ) : ℝ) * Real.sqrt (2 * r) * q.divisors.card) :=
            mul_le_mul_of_nonneg_left hTc (norm_nonneg _)
        _ = (((r * q : ℕ) : ℝ) * ‖Poin.cfac ℓ n (r * q)‖) * (Real.sqrt 2 * Real.sqrt r) *
              q.divisors.card := by rw [hs2]; ring
        _ ≤ D * (Real.sqrt 2 * Real.sqrt r) * (C * (y : ℝ) ^ ε) := by
            gcongr
        _ ≤ D * (Real.sqrt 2 * ((y : ℝ) ^ s * (r : ℝ) ^ (-(s - 1 / 2)) * (q : ℝ) ^ (-s))) *
              (C * (y : ℝ) ^ ε) := by gcongr
        _ = K * ((r : ℝ) ^ (-(s - 1 / 2)) * (q : ℝ) ^ (-s)) := by
            simp only [K]; rw [Real.rpow_add hy0]; ring
    · rw [if_neg hc, if_neg hc, mul_zero]
  calc ∑ r ∈ (range (y + 1)).filter (Smooth (S2 n)), ∑ q ∈ (range (y + 1)).filter (Rough (S2 n)),
        (if r * q ∈ T then ‖Poin.cfac ℓ n (r * q) * Poin.Tc n (r * q)‖ else 0)
      ≤ ∑ r ∈ (range (y + 1)).filter (Smooth (S2 n)), ∑ q ∈ (range (y + 1)).filter (Rough (S2 n)),
          K * (if r * q ∈ T then (r : ℝ) ^ (-(s - 1 / 2)) * (q : ℝ) ^ (-s) else 0) :=
        sum_le_sum fun r hr => sum_le_sum fun q hq => hpt r hr q hq
    _ = K * ∑ r ∈ (range (y + 1)).filter (Smooth (S2 n)), ∑ q ∈ (range (y + 1)).filter (Rough (S2 n)),
          (if r * q ∈ T then (r : ℝ) ^ (-(s - 1 / 2)) * (q : ℝ) ^ (-s) else 0) := by
        rw [mul_sum]; simp_rw [mul_sum]
    _ ≤ K * ((p : ℝ) ^ (-s) * (∑' q : ℕ, (q : ℝ) ^ (-s)) *
          ∏ ℓ' ∈ (2 * n).primeFactors, (1 - (ℓ' : ℝ) ^ (-(s - 1 / 2)))⁻¹) := by
        refine mul_le_mul_of_nonneg_left (sum_pdiv_le n p y hn hp hpn s hs T fun c hc => ?_) hK
        simp only [T, mem_filter, mem_Icc] at hc
        exact ⟨hc.1.1, (dvd_mul_left p 8).trans hc.2⟩

open Classical in
/-- **The range `Y < c ≤ N`.** -/
theorem high_range (ℓ n p Y N : ℕ) (hℓ : 1 ≤ ℓ) (hn : 0 < n) (hp : p.Prime) (hpn : ¬ p ∣ 2 * n)
    (hnY : n ≤ Y) (hY : 0 < Y) (C ε s α : ℝ) (hC : 0 < C) (hε : 0 ≤ ε) (hs : 1 < s) (hα : 0 ≤ α)
    (hsα : s + α = Poin.kw ℓ - 1 / 2 - ε)
    (hτ : ∀ m : ℕ, m ≠ 0 → ((m.divisors.card : ℕ) : ℝ) ≤ C * (m : ℝ) ^ ε) :
    ∑ c ∈ (Ioc Y N).filter (fun c => 8 * p ∣ c), ‖Poin.cfac ℓ n c * Poin.Tc n c‖ ≤
      Poin.cH ℓ n * Real.sqrt 2 * C * (Y : ℝ) ^ (-α) *
        ((p : ℝ) ^ (-s) * (∑' q : ℕ, (q : ℝ) ^ (-s)) *
          ∏ ℓ' ∈ (2 * n).primeFactors, (1 - (ℓ' : ℝ) ^ (-(s - 1 / 2)))⁻¹) := by
  set T := (Ioc Y N).filter (fun c => 8 * p ∣ c)
  have hT : ∀ c ∈ T, 0 < c ∧ c ≤ N := fun c hc => by
    simp only [T, mem_filter, mem_Ioc] at hc; exact ⟨by omega, hc.1.2⟩
  set K := Poin.cH ℓ n * Real.sqrt 2 * C * (Y : ℝ) ^ (-α)
  have hK : 0 ≤ K := by have := Poin.cH_nonneg ℓ n; positivity
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  rw [sum_split_real (S2 n) T N hT]
  have hpt : ∀ r ∈ (range (N + 1)).filter (Smooth (S2 n)), ∀ q ∈ (range (N + 1)).filter (Rough (S2 n)),
      (if r * q ∈ T then ‖Poin.cfac ℓ n (r * q) * Poin.Tc n (r * q)‖ else 0) ≤
        K * (if r * q ∈ T then (r : ℝ) ^ (-(s - 1 / 2)) * (q : ℝ) ^ (-s) else 0) := by
    intro r hr q hq
    have hrs : Smooth (S2 n) r := (mem_filter.mp hr).2
    have hqr : Rough (S2 n) q := (mem_filter.mp hq).2
    by_cases hc : r * q ∈ T
    · rw [if_pos hc, if_pos hc]
      have hc' := hc
      simp only [T, mem_filter, mem_Ioc] at hc'
      obtain ⟨⟨hYc, hcN⟩, h8⟩ := hc'
      have hc1 : 0 < r * q := by omega
      have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; simp at hc1)
      have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hc1)
      have h8r : 8 ∣ r := eight_dvd_smooth n r q hqr ((dvd_mul_right 8 p).trans h8)
      have h4r : 4 ∣ r := (by norm_num : 4 ∣ 8).trans h8r
      have hTc := norm_Tc_split n r q hrs hqr h4r hr0 hq0
      have hcf := Poin.norm_cfac_high ℓ n hℓ hc1 (by omega)
      have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
      have hx : (0 : ℝ) < (r : ℝ) * q := mul_pos hrR hqR
      have hYx : (Y : ℝ) ≤ (r : ℝ) * q := by exact_mod_cast hYc.le
      push_cast at hTc hcf
      have hτq : ((q.divisors.card : ℕ) : ℝ) ≤ C * ((r : ℝ) * q) ^ ε := by
        refine (hτ q hq0.ne').trans (mul_le_mul_of_nonneg_left ?_ hC.le)
        refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ hε
        exact le_mul_of_one_le_left hqR.le (by exact_mod_cast hr0)
      have hs2 : Real.sqrt (2 * r) = Real.sqrt 2 * Real.sqrt r := Real.sqrt_mul (by norm_num) _
      have hexp : ((r : ℝ) * q) ^ (-(Poin.kw ℓ) - 1 / 2) * ((r : ℝ) * q) * ((r : ℝ) * q) ^ ε =
          ((r : ℝ) * q) ^ (-(s + α)) := by
        rw [show -(s + α) = (-(Poin.kw ℓ) - 1 / 2) + 1 + ε by linarith, Real.rpow_add hx,
          Real.rpow_add hx, Real.rpow_one]
      have hcH := Poin.cH_nonneg ℓ n
      rw [norm_mul]
      calc ‖Poin.cfac ℓ n (r * q)‖ * ‖Poin.Tc n (r * q)‖
          ≤ (Poin.cH ℓ n * ((r : ℝ) * q) ^ (-(Poin.kw ℓ) - 1 / 2)) *
              ((r : ℝ) * q * Real.sqrt (2 * r) * q.divisors.card) :=
            mul_le_mul hcf hTc (norm_nonneg _) (by positivity)
        _ ≤ (Poin.cH ℓ n * ((r : ℝ) * q) ^ (-(Poin.kw ℓ) - 1 / 2)) *
              ((r : ℝ) * q * (Real.sqrt 2 * Real.sqrt r) * (C * ((r : ℝ) * q) ^ ε)) := by
            rw [hs2]; gcongr
        _ = Poin.cH ℓ n * Real.sqrt 2 * C * (Real.sqrt r *
              (((r : ℝ) * q) ^ (-(Poin.kw ℓ) - 1 / 2) * ((r : ℝ) * q) * ((r : ℝ) * q) ^ ε)) := by ring
        _ = Poin.cH ℓ n * Real.sqrt 2 * C * (Real.sqrt r * ((r : ℝ) * q) ^ (-(s + α))) := by rw [hexp]
        _ ≤ Poin.cH ℓ n * Real.sqrt 2 * C * ((Y : ℝ) ^ (-α) * ((r : ℝ) ^ (-(s - 1 / 2)) * (q : ℝ) ^ (-s))) :=
            mul_le_mul_of_nonneg_left (rankin_high r q Y s α hrR hqR hYR hYx hα) (by positivity)
        _ = K * ((r : ℝ) ^ (-(s - 1 / 2)) * (q : ℝ) ^ (-s)) := by simp only [K]; ring
    · rw [if_neg hc, if_neg hc, mul_zero]
  calc ∑ r ∈ (range (N + 1)).filter (Smooth (S2 n)), ∑ q ∈ (range (N + 1)).filter (Rough (S2 n)),
        (if r * q ∈ T then ‖Poin.cfac ℓ n (r * q) * Poin.Tc n (r * q)‖ else 0)
      ≤ ∑ r ∈ (range (N + 1)).filter (Smooth (S2 n)), ∑ q ∈ (range (N + 1)).filter (Rough (S2 n)),
          K * (if r * q ∈ T then (r : ℝ) ^ (-(s - 1 / 2)) * (q : ℝ) ^ (-s) else 0) :=
        sum_le_sum fun r hr => sum_le_sum fun q hq => hpt r hr q hq
    _ = K * ∑ r ∈ (range (N + 1)).filter (Smooth (S2 n)), ∑ q ∈ (range (N + 1)).filter (Rough (S2 n)),
          (if r * q ∈ T then (r : ℝ) ^ (-(s - 1 / 2)) * (q : ℝ) ^ (-s) else 0) := by
        rw [mul_sum]; simp_rw [mul_sum]
    _ ≤ K * ((p : ℝ) ^ (-s) * (∑' q : ℕ, (q : ℝ) ^ (-s)) *
          ∏ ℓ' ∈ (2 * n).primeFactors, (1 - (ℓ' : ℝ) ^ (-(s - 1 / 2)))⁻¹) := by
        refine mul_le_mul_of_nonneg_left (sum_pdiv_le n p N hn hp hpn s hs T fun c hc => ?_) hK
        simp only [T, mem_filter, mem_Ioc] at hc
        exact ⟨by omega, (dvd_mul_left p 8).trans hc.2⟩

end ThreeSquares
