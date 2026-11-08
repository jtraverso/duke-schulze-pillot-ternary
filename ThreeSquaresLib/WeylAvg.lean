/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.WeightInst
public import ThreeSquaresLib.PeterssonIneq

/-!
# Averaging the Petersson inequality over the levels

* `ratio_le`: `(8p)²/φ(8p) ≤ 32 p` for odd primes `p`;
* `phat_level_bound`: `‖P̂_{8p}‖ ≤ 2 + 2 (LB P₀^{−s} + ‖critSum_p‖ + HB P₀^{−s})` for `p` a level;
* `weyl_avg`: `‖W‖² |𝒫| ≤ C_w (32 P) n^{k−1} (2|𝒫|(1 + Lo + Hi) + 2 C_T)`.
-/

@[expose] public section

namespace ThreeSquares

open Finset Polynomial

open scoped Real

theorem totient_eight_mul (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) : Nat.totient (8 * p) = 4 * (p - 1) := by
  have hcop : Nat.Coprime (2 ^ 3) p :=
    Nat.Coprime.pow_left 3 ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm h2))
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.totient_mul hcop, Nat.totient_prime hp,
    Nat.totient_prime_pow Nat.prime_two (by norm_num)]
  norm_num

theorem ratio_le (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    ((8 * p : ℕ) : ℝ) ^ 2 / (Nat.totient (8 * p) : ℝ) ≤ 32 * p := by
  rw [totient_eight_mul p hp h2]
  have hp2 : 2 ≤ p := hp.two_le
  have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  push_cast
  rw [hp1, div_le_iff₀ (by linarith)]
  nlinarith

open Classical in
/-- **`P̂_{8p}` for a level `p`.** -/
theorem phat_level_bound (ℓ n p y Y P₀ : ℕ) (hℓ : 2 ≤ ℓ) (hn : 0 < n) (hp : p.Prime) (hpn : ¬ p ∣ 2 * n)
    (hP₀p : P₀ ≤ p) (hP₀ : 0 < P₀) {pp qq : ℂ[X]} (hpq : Lip.BesForm (ℓ + 1) pp qq)
    (hy : (y : ℝ) ≤ 2 * π * n) (hyY : y ≤ Y) (hnY : n ≤ Y) (hY : 0 < Y)
    (C ε s α : ℝ) (hC : 0 < C) (hε : 0 ≤ ε) (hs : 1 < s) (hα : 0 ≤ α)
    (hsα : s + α = Poin.kw ℓ - 1 / 2 - ε)
    (hτ : ∀ m : ℕ, m ≠ 0 → ((m.divisors.card : ℕ) : ℝ) ≤ C * (m : ℝ) ^ ε) :
    ‖Poin.Phat ℓ n (8 * p)‖ ≤ 2 + 2 * (
      (‖Poin.Kc ℓ n‖ * (Poin.polyA pp * (1 + 1) ^ pp.natDegree + Poin.polyA qq * (1 + 1) ^ qq.natDegree) *
        Real.sqrt 2 * C * (y : ℝ) ^ (ε + s) * ((∑' q : ℕ, (q : ℝ) ^ (-s)) *
          ∏ ℓ' ∈ (2 * n).primeFactors, (1 - (ℓ' : ℝ) ^ (-(s - 1 / 2)))⁻¹)) * (P₀ : ℝ) ^ (-s) +
      ‖critSum ℓ n p y Y‖ +
      (Poin.cH ℓ n * Real.sqrt 2 * C * (Y : ℝ) ^ (-α) * ((∑' q : ℕ, (q : ℝ) ^ (-s)) *
          ∏ ℓ' ∈ (2 * n).primeFactors, (1 - (ℓ' : ℝ) ^ (-(s - 1 / 2)))⁻¹)) * (P₀ : ℝ) ^ (-s)) := by
  set Z := ∑' q : ℕ, (q : ℝ) ^ (-s)
  set Pr := ∏ ℓ' ∈ (2 * n).primeFactors, (1 - (ℓ' : ℝ) ^ (-(s - 1 / 2)))⁻¹
  have hZ : 0 ≤ Z := tsum_nonneg fun _ => by positivity
  have hPr : 0 ≤ Pr := by
    refine prod_nonneg fun q hq => inv_nonneg.mpr ?_
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).two_le
    have : (q : ℝ) ^ (-(s - 1 / 2)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    linarith
  have hps : (p : ℝ) ^ (-s) ≤ (P₀ : ℝ) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hP₀) (by exact_mod_cast hP₀p) (by linarith)
  have hlow := low_range ℓ n p y hn hp hpn hpq hy C ε s hC hε hs hτ
  have hhigh := fun N => high_range ℓ n p Y N (by omega) hn hp hpn hnY hY C ε s α hC hε hs hα hsα hτ
  refine (phat_bound ℓ n p y Y hℓ hyY _ hhigh).trans ?_
  have hD : 0 ≤ ‖Poin.Kc ℓ n‖ * (Poin.polyA pp * (1 + 1) ^ pp.natDegree +
      Poin.polyA qq * (1 + 1) ^ qq.natDegree) * Real.sqrt 2 * C * (y : ℝ) ^ (ε + s) := by
    have := Poin.polyA_nonneg pp; have := Poin.polyA_nonneg qq; positivity
  have hH : 0 ≤ Poin.cH ℓ n * Real.sqrt 2 * C * (Y : ℝ) ^ (-α) := by
    have := Poin.cH_nonneg ℓ n; positivity
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  refine add_le_add (add_le_add (hlow.trans ?_) le_rfl) ?_
  · calc _ = (‖Poin.Kc ℓ n‖ * (Poin.polyA pp * (1 + 1) ^ pp.natDegree +
          Poin.polyA qq * (1 + 1) ^ qq.natDegree) * Real.sqrt 2 * C * (y : ℝ) ^ (ε + s) * (Z * Pr)) *
            (p : ℝ) ^ (-s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hps (by positivity)
  · calc _ = (Poin.cH ℓ n * Real.sqrt 2 * C * (Y : ℝ) ^ (-α) * (Z * Pr)) * (p : ℝ) ^ (-s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hps (by positivity)

/-- **Averaging over the levels.** -/
theorem weyl_avg (u : Fin 3 → ℂ) (ℓ n : ℕ) (hn : 0 < n) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hWsq : ∀ (Q : ℕ) [NeZero Q], 4 ∣ Q → ∀ n : ℕ, 0 < n →
      ‖weylU u ℓ n‖ ^ 2 ≤ Cw * ((Q : ℝ) ^ 2 / Nat.totient Q) * (n : ℝ) ^ (Poin.kw ℓ - 1) *
        ‖Poin.Phat ℓ n Q‖)
    (Ps : Finset ℕ) (P : ℕ) (hPs : ∀ p ∈ Ps, p.Prime ∧ p ≠ 2 ∧ p ≤ P) (Lo Hi CT : ℝ) (c : ℕ → ℝ)
    (hph : ∀ p ∈ Ps, ‖Poin.Phat ℓ n (8 * p)‖ ≤ 2 + 2 * (Lo + c p + Hi))
    (hcrit : ∑ p ∈ Ps, c p ≤ CT) :
    ‖weylU u ℓ n‖ ^ 2 * Ps.card ≤
      Cw * (32 * P) * (n : ℝ) ^ (Poin.kw ℓ - 1) * (2 * Ps.card * (1 + Lo + Hi) + 2 * CT) := by
  have hnk : 0 ≤ (n : ℝ) ^ (Poin.kw ℓ - 1) := by positivity
  have hM : 0 ≤ Cw * (32 * P) * (n : ℝ) ^ (Poin.kw ℓ - 1) := by positivity
  have hpt : ∀ p ∈ Ps, ‖weylU u ℓ n‖ ^ 2 ≤
      Cw * (32 * P) * (n : ℝ) ^ (Poin.kw ℓ - 1) * (2 + 2 * (Lo + c p + Hi)) := by
    intro p hp
    obtain ⟨hpr, hp2, hpP⟩ := hPs p hp
    haveI : NeZero (8 * p) := ⟨by have := hpr.pos; omega⟩
    have h := hWsq (8 * p) (dvd_mul_of_dvd_left (by norm_num) p) n hn
    have hr := ratio_le p hpr hp2
    have hpPR : (p : ℝ) ≤ P := by exact_mod_cast hpP
    calc ‖weylU u ℓ n‖ ^ 2 ≤ Cw * (((8 * p : ℕ) : ℝ) ^ 2 / Nat.totient (8 * p)) * (n : ℝ) ^ (Poin.kw ℓ - 1) *
          ‖Poin.Phat ℓ n (8 * p)‖ := h
      _ ≤ Cw * (32 * P) * (n : ℝ) ^ (Poin.kw ℓ - 1) * (2 + 2 * (Lo + c p + Hi)) := by
          have hr' : ((8 * p : ℕ) : ℝ) ^ 2 / Nat.totient (8 * p) ≤ 32 * P := hr.trans (by linarith)
          have h0 : 0 ≤ ((8 * p : ℕ) : ℝ) ^ 2 / Nat.totient (8 * p) := by positivity
          gcongr
          exact hph p hp
  calc ‖weylU u ℓ n‖ ^ 2 * Ps.card = ∑ p ∈ Ps, ‖weylU u ℓ n‖ ^ 2 := by
        rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ p ∈ Ps, Cw * (32 * P) * (n : ℝ) ^ (Poin.kw ℓ - 1) * (2 + 2 * (Lo + c p + Hi)) :=
        sum_le_sum hpt
    _ = Cw * (32 * P) * (n : ℝ) ^ (Poin.kw ℓ - 1) * (2 * Ps.card * (1 + Lo + Hi) + 2 * ∑ p ∈ Ps, c p) := by
        rw [← mul_sum]; congr 1
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum, sum_add_distrib, sum_add_distrib,
          sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hM

end ThreeSquares
