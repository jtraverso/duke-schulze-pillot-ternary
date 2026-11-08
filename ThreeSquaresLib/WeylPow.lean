/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.WeylStep

/-!
# The size of `eE`

`eE(n) = O(n^{ℓ + 1 − 3δ/16})` (`pl_eE`) when `(d + 1) δ ≤ 1/4000`, `d` the degree bound of the Bessel form.
-/

@[expose] public section

namespace ThreeSquares

open Real Polynomial

theorem PowLe.rpow_neg_of_ge {f : ℕ → ℝ} (a s : ℝ) (hs : 0 ≤ s) (N₀ : ℕ)
    (h : ∀ n, N₀ ≤ n → (1 / 2) * (n : ℝ) ^ a ≤ f n) : PowLe (fun n => f n ^ (-s)) (-(a * s)) := by
  refine ⟨(1 / 2 : ℝ) ^ (-s), max 1 N₀, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
  have hpos : 0 < (1 / 2) * (n : ℝ) ^ a := by positivity
  have hf := h n (le_of_max_le_right hn)
  refine ⟨Real.rpow_nonneg (hpos.le.trans hf) _, ?_⟩
  calc f n ^ (-s) ≤ ((1 / 2) * (n : ℝ) ^ a) ^ (-s) := Real.rpow_le_rpow_of_nonpos hpos hf (by linarith)
    _ = (1 / 2 : ℝ) ^ (-s) * (n : ℝ) ^ (-(a * s)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by positivity)]; ring_nf

section final

variable (ℓ : ℕ) (hℓ2 : 2 ≤ ℓ) (Cw : ℝ) (hCw : 0 ≤ Cw) (pp qq : ℂ[X]) (δ : ℝ) (hδ0 : 0 < δ)
  (hδ : δ ≤ 1 / 8000) (hd : ((max pp.natDegree qq.natDegree : ℕ) + 1 : ℝ) * δ ≤ 1 / 4000)
  (C : ℝ) (hC : 0 < C)
include hδ0 hδ

theorem pl_L1 (θ : ℝ) (hθ : 0 < θ) : PowLe (fun n => (pL δ n : ℝ) + 1) θ :=
  ((PowLe.log_add_one θ hθ).cmul 3 (by norm_num)).of_le 2 fun n hn => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hY2, hY1⟩ := pbounds δ hδ0 hδ n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hl2 : (2 : ℝ) / 3 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hpow : (2 : ℝ) ^ Nat.log 2 (pY δ n) ≤ pY δ n := by
      exact_mod_cast Nat.pow_log_le_self 2 (by have := floor_rpow_pos (1 + δ) (by linarith) n (by omega)
                                               unfold pY; omega)
    have hlog : (Nat.log 2 (pY δ n) : ℝ) * Real.log 2 ≤ 2 * Real.log n := by
      have h1 := Real.log_le_log (by positivity) hpow
      rw [Real.log_pow] at h1
      have h2 : Real.log (pY δ n) ≤ Real.log ((n : ℝ) ^ 2) := Real.log_le_log (by linarith) hY2
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith
    have hl0 : 0 ≤ Real.log n := Real.log_nonneg hnR
    have hN : (Nat.log 2 (pY δ n) : ℝ) ≤ 3 * Real.log n := by
      have h0 : (0 : ℝ) ≤ Nat.log 2 (pY δ n) := Nat.cast_nonneg _
      nlinarith
    unfold pL
    push_cast
    exact ⟨by positivity, by linarith⟩

theorem pl_logY (θ : ℝ) (hθ : 0 < θ) : PowLe (fun n => 1 + Real.log (pY δ n)) θ :=
  ((PowLe.log_add_one θ hθ).cmul 3 (by norm_num)).of_le 2 fun n hn => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hY2, hY1⟩ := pbounds δ hδ0 hδ n hn
    have := log_le_mul_log (pY δ n : ℝ) 2 n hn hY1 hY2
    refine ⟨?_, by push_cast at this; linarith⟩
    have := Real.log_nonneg hY1; linarith

theorem pl_card : PowLe (fun n => ((levels n (pP0 n)).card : ℝ)) (11 / 40) :=
  ((PowLe.floor_rpow (11 / 40) (by norm_num)).cmul 4 (by norm_num)).of_le 0 fun n _ => by
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have : (levels n (pP0 n)).card ≤ 4 * pP0 n := by
      refine (Finset.card_filter_le _ _).trans ?_
      simp
    have h : ((levels n (pP0 n)).card : ℝ) ≤ 4 * (pP0 n : ℝ) := by exact_mod_cast this
    unfold pP0 at h
    exact h

theorem pl_invP0 : PowLe (fun n => 1 / (pP0 n : ℝ)) (-(11 / 40)) :=
  PowLe.inv_of_ge (f := fun n => (pP0 n : ℝ)) (1 / 2) (11 / 40) (by norm_num) 2 fun n hn => by
    obtain ⟨-, -, -, -, -, -, gP, -⟩ := pbounds δ hδ0 hδ n hn
    exact gP

theorem pl_Yv : PowLe (fun n => (pY δ n : ℝ)) (1 + δ) := PowLe.floor_rpow _ (by linarith)

theorem pl_yv : PowLe (fun n => (py δ n : ℝ)) (1 - δ) := PowLe.floor_rpow _ (by linarith)

include hℓ2 hd hC hCw in
/-- **`eE = O(n^{ℓ+1−3δ/16})`.** -/
theorem pl_eE : PowLe (eE ℓ Cw δ C pp qq) (ℓ + 1 - 3 * δ / 16) := by
  set θ := δ / 16 with hθdef
  have hθ : 0 < θ := by positivity
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ2
  set d : ℕ := max pp.natDegree qq.natDegree
  have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  set Dc := Poin.polyA pp * (1 + 1) ^ pp.natDegree + Poin.polyA qq * (1 + 1) ^ qq.natDegree
  have hDc : 0 ≤ Dc := by have := Poin.polyA_nonneg pp; have := Poin.polyA_nonneg qq; positivity
  set Z := ∑' q : ℕ, (q : ℝ) ^ (-eS δ)
  have hZ : 0 ≤ Z := tsum_nonneg fun _ => by positivity
  have hs1 : 1 < eS δ := by unfold eS; linarith
  have hα : 0 ≤ eA ℓ δ := by unfold eA eS Poin.kw; linarith
  -- common pieces
  have ZP : PowLe (eZP δ) θ :=
    (((PowLe.const Z hZ).mul (pl_euler (eS δ - 1 / 2) θ (by linarith) hθ)).congr 0 fun n _ => rfl).mono
      (by linarith)
  have P0neg : PowLe (fun n => ((pP0 n : ℕ) : ℝ) ^ (-eS δ)) (-(11 / 40 * eS δ)) :=
    PowLe.rpow_neg_of_ge (f := fun n => ((pP0 n : ℕ) : ℝ)) (11 / 40) (eS δ) (by linarith) 2 fun n hn => by
      obtain ⟨-, -, -, -, -, -, gP, -⟩ := pbounds δ hδ0 hδ n hn; exact gP
  -- the low range
  have Lo : PowLe (eLo ℓ δ C pp qq)
      (-(1 / 2) + 0 + 0 + 0 + (1 - δ) * (δ / 16 + eS δ) + θ + -(11 / 40 * eS δ)) :=
    ((((((pl_Kc ℓ).mul (PowLe.const Dc hDc)).mul (PowLe.const (Real.sqrt 2) (by positivity))).mul
      (PowLe.const C hC.le)).mul ((pl_yv δ hδ0 hδ).rpow' (δ / 16 + eS δ) (by unfold eS; positivity))).mul
      ZP |>.mul P0neg).congr 0 fun n _ => rfl
  -- the high range
  have Yneg : PowLe (fun n => ((pY δ n : ℕ) : ℝ) ^ (-eA ℓ δ)) (-((1 + δ) * eA ℓ δ)) :=
    PowLe.rpow_neg_of_ge (f := fun n => ((pY δ n : ℕ) : ℝ)) (1 + δ) (eA ℓ δ) hα 2 fun n hn => by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, gY, -⟩ := pbounds δ hδ0 hδ n hn; exact gY
  have Hi : PowLe (eHi ℓ δ C) (Poin.kw ℓ - 1 + 0 + 0 + -((1 + δ) * eA ℓ δ) + θ + -(11 / 40 * eS δ)) :=
    (((((pl_cH ℓ).mul (PowLe.const (Real.sqrt 2) (by positivity))).mul (PowLe.const C hC.le)).mul Yneg).mul
      ZP |>.mul P0neg).congr 0 fun n _ => rfl
  -- the critical part
  have hΛ : PowLe (eΛ δ pp qq) δ := (pl_lamW δ hδ0 hδ pp qq).congr 0 fun n _ => rfl
  have σb := powLe_sigma δ hδ0 hδ (δ / 16) θ C (by positivity) hθ (by linarith) (eΛ δ pp qq) hΛ
  have R114 := (pl_R δ hδ0 hδ).rpow' (11 / 4) (by norm_num)
  have Rneg : PowLe (fun n => (pR n : ℝ) ^ (-(1 / 4 : ℝ))) (-(1 / 250 * (1 / 4))) :=
    PowLe.rpow_neg_of_ge (f := fun n => (pR n : ℝ)) (1 / 250) (1 / 4) (by norm_num) 1 fun n hn =>
      floor_rpow_ge _ (by norm_num) n hn
  have L2 : PowLe (fun n => ((pL δ n : ℝ) + 1) ^ 2) (θ + θ) :=
    ((pl_L1 δ hδ0 hδ θ hθ).mul (pl_L1 δ hδ0 hδ θ hθ)).congr 0 fun n _ => sq _
  have YP : PowLe (fun n => 4 * (pY δ n : ℝ) / (pP0 n : ℝ)) (1 + δ + -(11 / 40)) :=
    (((pl_Yv δ hδ0 hδ).cmul 4 (by norm_num)).mul (pl_invP0 δ hδ0 hδ)).congr 0 fun n _ => by ring
  have YP' : PowLe (fun n => (pY δ n : ℝ) / (pP0 n : ℝ)) (1 + δ + -(11 / 40)) :=
    ((pl_Yv δ hδ0 hδ).mul (pl_invP0 δ hδ0 hδ)).congr 0 fun n _ => by ring
  have W0 := pl_W0 δ hδ0 hδ ℓ pp qq
  have A := ((PowLe.const 2 (by norm_num)).mul R114).mul (L2.mul (σb.mul (((pl_P δ hδ0 hδ).mul W0).mul YP)))
  have B := ((PowLe.const 2 (by norm_num)).mul Rneg).mul ((pl_card δ hδ0 hδ).mul
    (W0.mul (YP'.mul (pl_logY δ hδ0 hδ θ hθ))))
  have CTb : PowLe (eCT ℓ δ C pp qq) (0 + (1 / 2 - 5 * δ / 16) + θ) :=
    (((PowLe.const (Real.sqrt 2) (by positivity)).mul ((A.mono (by linarith)).add (B.mono (by linarith)))).mul
      (pl_euler (1 / 4) θ (by norm_num) hθ)).congr 0 fun n _ => rfl
  have e1 : (0 : ℝ) ≤ 9 / 40 - 3 * δ / 16 := by linarith
  have eLo' : -(1 / 2) + 0 + 0 + 0 + (1 - δ) * (δ / 16 + eS δ) + θ + -(11 / 40 * eS δ) ≤ 9 / 40 - 3 * δ / 16 := by
    unfold eS; nlinarith [mul_pos hδ0 hδ0]
  have eHi' : Poin.kw ℓ - 1 + 0 + 0 + -((1 + δ) * eA ℓ δ) + θ + -(11 / 40 * eS δ) ≤ 9 / 40 - 3 * δ / 16 := by
    unfold eA eS Poin.kw; nlinarith [mul_pos hδ0 hδ0, mul_le_mul_of_nonneg_left hℓR hδ0.le]
  have X := ((PowLe.const 2 (by norm_num)).mul ((((PowLe.const 1 (by norm_num)).mono e1).add (Lo.mono eLo')).add
    (Hi.mono eHi'))).add ((((PowLe.const 2 (by norm_num)).mul CTb).mul (pl_invLevels θ hθ)).mono
      (show 0 + (0 + (1 / 2 - 5 * δ / 16) + θ) + -(11 / 40 - θ) ≤ 0 + (9 / 40 - 3 * δ / 16) by linarith))
  have M := ((PowLe.const Cw hCw).mul ((pl_P δ hδ0 hδ).cmul 32 (by norm_num))).mul (PowLe.self (Poin.kw ℓ - 1))
  refine ((M.mul X).congr 0 fun n _ => rfl).mono ?_
  unfold Poin.kw; linarith


end final

end ThreeSquares
