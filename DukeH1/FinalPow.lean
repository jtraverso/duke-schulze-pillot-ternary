/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.SigmaBound

/-!
# Power bounds for the weights and the Euler products

`Λ = O(n^δ)`, `W₀ = O(n^{−1/2 + dδ})` (`d` = max degree), `∏_{ℓ ∣ 2n} (1 − ℓ^{−σ})^{−1} = O(n^θ)`,
`‖Kc‖ = O(n^{−1/2})`, `cH = O(n^{k−1})`.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open Real Polynomial

theorem pl_Kc (ℓ : ℕ) : PowLe (fun n => ‖Poin.Kc ℓ n‖) (-(1 / 2)) :=
  ((PowLe.self (-(1 / 2))).cmul 2 (by norm_num)).of_le 1 fun n hn =>
    ⟨norm_nonneg _, Poin.norm_Kc_le ℓ n hn⟩

theorem pl_cH (ℓ : ℕ) : PowLe (fun n => Poin.cH ℓ n) (Poin.kw ℓ - 1) := by
  refine ((PowLe.self (Poin.kw ℓ - 1)).cmul (‖(-(2 * π * Complex.I)) ^ (Poin.kw ℓ : ℂ)‖ * Real.exp (4 * π ^ 2))
    (by positivity)).of_le 1 fun n hn => ⟨Poin.cH_nonneg ℓ n, le_of_eq ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold Poin.cH
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
  ring

theorem pl_euler (σ θ : ℝ) (hσ : 0 < σ) (hθ : 0 < θ) :
    PowLe (fun n => ∏ ℓ ∈ (2 * n).primeFactors, (1 - (ℓ : ℝ) ^ (-σ))⁻¹) θ := by
  set K := (1 - (2 : ℝ) ^ (-σ))⁻¹
  have h2 : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hK1 : 1 ≤ K := by
    have h0 : 0 < (2 : ℝ) ^ (-σ) := by positivity
    exact one_le_inv₀ (by linarith) |>.mpr (by linarith)
  obtain ⟨C, hC, hCb⟩ := pow_card_primeFactors_le_rpow K hK1 θ hθ
  refine ⟨C * 2 ^ θ, 1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : ∀ ℓ ∈ (2 * n).primeFactors, 0 ≤ (1 - (ℓ : ℝ) ^ (-σ))⁻¹ ∧ (1 - (ℓ : ℝ) ^ (-σ))⁻¹ ≤ K := by
    intro ℓ hℓ
    have hℓ2 : (2 : ℝ) ≤ ℓ := by exact_mod_cast (Nat.prime_of_mem_primeFactors hℓ).two_le
    have hle : (ℓ : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hℓ2 (by linarith)
    have hpos : 0 < 1 - (ℓ : ℝ) ^ (-σ) := by linarith
    exact ⟨inv_nonneg.mpr hpos.le, inv_anti₀ (by linarith) (by linarith)⟩
  refine ⟨Finset.prod_nonneg fun ℓ hℓ => (hfac ℓ hℓ).1, ?_⟩
  calc ∏ ℓ ∈ (2 * n).primeFactors, (1 - (ℓ : ℝ) ^ (-σ))⁻¹
      ≤ ∏ ℓ ∈ (2 * n).primeFactors, K := Finset.prod_le_prod₀ (fun ℓ hℓ => (hfac ℓ hℓ).1) fun ℓ hℓ => (hfac ℓ hℓ).2
    _ = K ^ (2 * n).primeFactors.card := Finset.prod_const _
    _ ≤ C * ((2 * n : ℕ) : ℝ) ^ θ := hCb _ (by omega)
    _ = C * 2 ^ θ * (n : ℝ) ^ θ := by
        push_cast; rw [Real.mul_rpow (by norm_num) hn0.le]; ring

section weights

variable (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8000)
include hδ0 hδ

theorem wS_le (n : ℕ) (hn : 2 ≤ n) : wS n (pY δ n) ≤ (n : ℝ) ^ δ := by
  obtain ⟨-, -, -, -, -, fY, -⟩ := pbounds δ hδ0 hδ n hn
  have hn0 : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                               linarith
  unfold wS
  have e : (n : ℝ) ^ (1 + δ) = n * (n : ℝ) ^ δ := by rw [Real.rpow_add hn0, Real.rpow_one]
  rw [e] at fY
  have hpi : 1 ≤ 2 * π := by nlinarith [Real.pi_gt_three]
  rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
  have h0 : 0 ≤ (n : ℝ) ^ δ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hpi (mul_nonneg hn0.le h0)]

theorem pl_lamW (p q : ℂ[X]) : PowLe (fun n => wLam n (py δ n) (pY δ n) p q) δ := by
  refine ⟨16 * π + max (p.natDegree : ℝ) q.natDegree, 2, fun n hn => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, gy, -⟩ := pbounds δ hδ0 hδ n hn
  have hn0 : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                               linarith
  have hS := wS_le δ hδ0 hδ n hn
  have hS0 := wS_nonneg n (pY δ n)
  have hd : 0 ≤ max (p.natDegree : ℝ) q.natDegree := le_max_of_le_left (Nat.cast_nonneg _)
  have hy1 : (1 / 2) * (n : ℝ) ^ (1 - δ) ≤ ((py δ n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hyp : 0 < (1 / 2) * (n : ℝ) ^ (1 - δ) := by positivity
  have e : (n : ℝ) = (n : ℝ) ^ (1 - δ) * (n : ℝ) ^ δ := by
    rw [← Real.rpow_add hn0, sub_add_cancel, Real.rpow_one]
  have t1 : 2 * π * |4 * (n : ℝ)| / ((py δ n + 1 : ℕ) : ℝ) ≤ 16 * π * (n : ℝ) ^ δ := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (lt_of_lt_of_le hyp hy1)]
    have : 2 * π * (4 * (n : ℝ)) = 16 * π * (n : ℝ) ^ δ * ((1 / 2) * (n : ℝ) ^ (1 - δ)) := by
      conv_lhs => rw [e]
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hy1 (by positivity)
  unfold wLam
  refine ⟨by positivity, ?_⟩
  have t2 := mul_le_mul_of_nonneg_left hS hd
  nlinarith

theorem wA_le (p : ℂ[X]) (d : ℕ) (hd : p.natDegree ≤ d) (n : ℕ) (hn : 2 ≤ n) :
    wA p (wS n (pY δ n)) ≤ Poin.polyA p * 2 ^ d * (n : ℝ) ^ (d * δ) := by
  have hS := wS_le δ hδ0 hδ n hn
  have hS0 := wS_nonneg n (pY δ n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ δ := Real.one_le_rpow hn1 hδ0.le
  have hb : 1 + wS n (pY δ n) ≤ 2 * (n : ℝ) ^ δ := by linarith
  have hb1 : (1 : ℝ) ≤ 2 * (n : ℝ) ^ δ := by linarith
  unfold wA
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Poin.polyA_nonneg p)
  calc (1 + wS n (pY δ n)) ^ p.natDegree ≤ (2 * (n : ℝ) ^ δ) ^ p.natDegree :=
        pow_le_pow_left₀ (by linarith) hb _
    _ ≤ (2 * (n : ℝ) ^ δ) ^ d := pow_le_pow_right₀ hb1 hd
    _ = 2 ^ d * (n : ℝ) ^ (d * δ) := by
        rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ δ), ← Real.rpow_mul (by positivity), mul_comm δ]

theorem pl_W0 (ℓ : ℕ) (p q : ℂ[X]) :
    PowLe (fun n => wW0 ℓ n (pY δ n) p q) (-(1 / 2) + (max p.natDegree q.natDegree : ℕ) * δ) := by
  set d := max p.natDegree q.natDegree
  have hA : PowLe (fun n => wA p (wS n (pY δ n)) + wA q (wS n (pY δ n))) (d * δ) :=
    ((PowLe.self (d * δ)).cmul (Poin.polyA p * 2 ^ d + Poin.polyA q * 2 ^ d)
      (by have := Poin.polyA_nonneg p; have := Poin.polyA_nonneg q; positivity)).of_le 2 fun n hn => by
      have h1 := wA_le δ hδ0 hδ p d (le_max_left _ _) n hn
      have h2 := wA_le δ hδ0 hδ q d (le_max_right _ _) n hn
      have hS0 := wS_nonneg n (pY δ n)
      refine ⟨add_nonneg (wA_nonneg p hS0) (wA_nonneg q hS0), ?_⟩
      linarith
  exact ((pl_Kc ℓ).mul hA).congr 0 fun n _ => rfl

end weights

end ThreeSquares
