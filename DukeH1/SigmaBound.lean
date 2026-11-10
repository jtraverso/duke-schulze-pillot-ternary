/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.Params

/-!
# Power bounds for the parameters, and the saving `σ`

`pσ = max(√M1, √M2, PV)` (the three quantities of `BlockHyp`), and `PowLe pσ (−7/400)` (`powLe_sigma`)
when `Λ` is `PowLe` with exponent `δ` and `δ + 6ε + 2θ ≤ 1/1000`.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open Real

/-- Floor bounds for `n ≥ 2`. -/
theorem pbounds (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8000) (n : ℕ) (hn : 2 ≤ n) :
    (pR n : ℝ) ≤ (n : ℝ) ^ (1 / 250 : ℝ) ∧ (pP0 n : ℝ) ≤ (n : ℝ) ^ (11 / 40 : ℝ) ∧
    (pB0 n : ℝ) ≤ (n : ℝ) ^ (2 / 25 : ℝ) ∧ (pK n : ℝ) ≤ (n : ℝ) ^ (9 / 250 : ℝ) ∧
    (py δ n : ℝ) ≤ (n : ℝ) ^ (1 - δ) ∧ (pY δ n : ℝ) ≤ (n : ℝ) ^ (1 + δ) ∧
    (1 / 2) * (n : ℝ) ^ (11 / 40 : ℝ) ≤ (pP0 n : ℝ) ∧ (1 / 2) * (n : ℝ) ^ (2 / 25 : ℝ) ≤ (pB0 n : ℝ) ∧
    (1 / 2) * (n : ℝ) ^ (9 / 250 : ℝ) ≤ (pK n : ℝ) ∧ (1 / 2) * (n : ℝ) ^ (1 - δ) ≤ (py δ n : ℝ) ∧
    (1 / 2) * (n : ℝ) ^ (1 + δ) ≤ (pY δ n : ℝ) ∧ (pY δ n : ℝ) ≤ (n : ℝ) ^ 2 ∧ (1 : ℝ) ≤ pY δ n := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have fY : (pY δ n : ℝ) ≤ (n : ℝ) ^ (1 + δ) := Nat.floor_le (by positivity)
  refine ⟨Nat.floor_le (by positivity), Nat.floor_le (by positivity), Nat.floor_le (by positivity),
    Nat.floor_le (by positivity), Nat.floor_le (by positivity), fY,
    floor_rpow_ge _ (by norm_num) n hn1, floor_rpow_ge _ (by norm_num) n hn1,
    floor_rpow_ge _ (by norm_num) n hn1, floor_rpow_ge _ (by linarith) n hn1,
    floor_rpow_ge _ (by linarith) n hn1, ?_, by exact_mod_cast floor_rpow_pos _ (by linarith) n hn1⟩
  refine fY.trans ?_
  have := Real.rpow_le_rpow_of_exponent_le hnR (show 1 + δ ≤ (2 : ℝ) by linarith)
  rwa [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this

theorem log_le_mul_log (x : ℝ) (k : ℕ) (n : ℕ) (hn : 2 ≤ n) (hx : 1 ≤ x) (hxn : x ≤ (n : ℝ) ^ k) :
    1 + Real.log x ≤ (k + 1) * (1 + Real.log n) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have h1 : Real.log x ≤ k * Real.log n := by
    rw [← Real.log_pow]; exact Real.log_le_log (by linarith) hxn
  have h2 : 0 ≤ Real.log n := Real.log_nonneg hnR
  nlinarith

/-- `M1` of `BlockHyp`. -/
noncomputable def pM1 (δ ε C : ℝ) (Λ : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 / ((4 * pP0 n : ℕ) : ℝ) + (3 + 4 * Λ n) * 3 * C ^ 2 * (2 * (pY δ n : ℝ)) ^ (2 * ε) *
    (1 + Real.log (2 * (pY δ n : ℝ))) *
      (6 / Real.sqrt (pB0 n : ℝ) + (1 + Real.log (2 * (pY δ n : ℝ))) / (pK n : ℝ))

/-- `M2` of `BlockHyp`. -/
noncomputable def pM2 (δ ε C : ℝ) (Λ : ℕ → ℝ) (n : ℕ) : ℝ :=
  1 / ((4 * pP0 n : ℕ) : ℝ) + (3 + 4 * Λ n) * 12 * ((4 * pP0 n : ℕ) : ℝ) * C ^ 2 *
    (2 * (pY δ n : ℝ)) ^ (2 * ε) * (1 + Real.log (2 * (pY δ n : ℝ))) *
      (6 / (pP0 n : ℝ) ^ 2 + (1 + Real.log (((4 * pP0 n : ℕ) : ℝ) ^ 2 * (2 * (pY δ n : ℝ)))) * pX δ n)

/-- The Pólya–Vinogradov ratio of `BlockHyp`. -/
noncomputable def pPV (δ : ℝ) (Λ : ℕ → ℝ) (n : ℕ) : ℝ :=
  (pB0 n : ℝ) ^ 2 * ((3 + 2 * Λ n) * (Real.sqrt n * (1 + Real.log n))) / (4 * (pY δ n : ℝ) / (pP0 n : ℝ))

/-- The saving. -/
noncomputable def pσ (δ ε C : ℝ) (Λ : ℕ → ℝ) (n : ℕ) : ℝ :=
  max (max (Real.sqrt (pM1 δ ε C Λ n)) (Real.sqrt (pM2 δ ε C Λ n))) (pPV δ Λ n)

theorem PowLe.div_of_ge {f : ℕ → ℝ} (c a K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (N₀ : ℕ)
    (h : ∀ n, N₀ ≤ n → c * (n : ℝ) ^ a ≤ f n) : PowLe (fun n => K / f n) (-a) := by
  refine ⟨K / c, max 1 N₀, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
  have hpos : 0 < c * (n : ℝ) ^ a := by positivity
  have hf := h n (le_of_max_le_right hn)
  have hf0 : 0 < f n := lt_of_lt_of_le hpos hf
  refine ⟨div_nonneg hK hf0.le, ?_⟩
  calc K / f n ≤ K / (c * (n : ℝ) ^ a) := div_le_div_of_nonneg_left hK hpos hf
    _ = K / c * (n : ℝ) ^ (-a) := by rw [Real.rpow_neg (by positivity)]; field_simp

theorem PowLe.congr {f g : ℕ → ℝ} {a : ℝ} (hf : PowLe f a) (N : ℕ) (h : ∀ n, N ≤ n → g n = f n) :
    PowLe g a := by
  obtain ⟨C, N₀, h₀⟩ := hf
  exact ⟨C, max N₀ N, fun n hn => by
    rw [h n (le_of_max_le_right hn)]; exact h₀ n (le_of_max_le_left hn)⟩

theorem pUmax_ge_one (δ : ℝ) (n : ℕ) : 1 ≤ pUmax δ n :=
  le_max_of_le_left (le_max_left _ _)

section bounds

variable (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8000)
include hδ0 hδ

theorem pl_R : PowLe (fun n => (pR n : ℝ)) (1 / 250) := PowLe.floor_rpow _ (by norm_num)
theorem pl_P : PowLe (fun n => ((4 * pP0 n : ℕ) : ℝ)) (11 / 40) :=
  ((PowLe.floor_rpow (11 / 40) (by norm_num)).cmul 4 (by norm_num)).of_le 0 fun n _ =>
    ⟨by positivity, le_of_eq (by unfold pP0; push_cast; ring)⟩
theorem pl_P0 : PowLe (fun n => (pP0 n : ℝ)) (11 / 40) := PowLe.floor_rpow _ (by norm_num)
theorem pl_B0 : PowLe (fun n => (pB0 n : ℝ)) (2 / 25) := PowLe.floor_rpow _ (by norm_num)

theorem pl_invP : PowLe (fun n => 1 / ((4 * pP0 n : ℕ) : ℝ)) (-(11 / 40)) :=
  PowLe.inv_of_ge (f := fun n => ((4 * pP0 n : ℕ) : ℝ)) 2 (11 / 40) (by norm_num) 2 fun n hn => by
    obtain ⟨-, -, -, -, -, -, gP, -⟩ := pbounds δ hδ0 hδ n hn
    push_cast; linarith

theorem pl_invY4 : PowLe (fun n => 1 / (4 * (pY δ n : ℝ))) (-(1 + δ)) :=
  PowLe.inv_of_ge (f := fun n => 4 * (pY δ n : ℝ)) 2 (1 + δ) (by norm_num) 2 fun n hn => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, gY, -⟩ := pbounds δ hδ0 hδ n hn
    linarith

theorem pl_invy : PowLe (fun n => 1 / (py δ n : ℝ)) (-(1 - δ)) :=
  PowLe.inv_of_ge (f := fun n => (py δ n : ℝ)) (1 / 2) (1 - δ) (by norm_num) 2 fun n hn => by
    obtain ⟨-, -, -, -, -, -, -, -, -, gy, -⟩ := pbounds δ hδ0 hδ n hn
    linarith

theorem pl_invK : PowLe (fun n => 1 / (pK n : ℝ)) (-(9 / 250)) :=
  PowLe.inv_of_ge (f := fun n => (pK n : ℝ)) (1 / 2) (9 / 250) (by norm_num) 2 fun n hn => by
    obtain ⟨-, -, -, -, -, -, -, -, gK, -⟩ := pbounds δ hδ0 hδ n hn
    linarith

theorem pl_log2Y (θ : ℝ) (hθ : 0 < θ) : PowLe (fun n => 1 + Real.log (2 * (pY δ n : ℝ))) θ :=
  ((PowLe.log_add_one θ hθ).cmul 4 (by norm_num)).of_le 2 fun n hn => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hY2, hY1⟩ := pbounds δ hδ0 hδ n hn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : 2 * (pY δ n : ℝ) ≤ (n : ℝ) ^ 3 := by nlinarith
    have := log_le_mul_log (2 * (pY δ n : ℝ)) 3 n hn (by linarith) h3
    refine ⟨?_, by push_cast at this; linarith⟩
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * (pY δ n : ℝ) by linarith)
    linarith

theorem pl_logP2Y (θ : ℝ) (hθ : 0 < θ) :
    PowLe (fun n => 1 + Real.log (((4 * pP0 n : ℕ) : ℝ) ^ 2 * (2 * (pY δ n : ℝ)))) θ :=
  ((PowLe.log_add_one θ hθ).cmul 10 (by norm_num)).of_le 2 fun n hn => by
    obtain ⟨-, fP, -, -, -, -, gP, -, -, -, -, hY2, hY1⟩ := pbounds δ hδ0 hδ n hn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hPn : (pP0 n : ℝ) ≤ n := by
      refine fP.trans ?_
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ n) (show (11 / 40 : ℝ) ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have hP1 : (1 : ℝ) ≤ pP0 n := by
      have : (1 : ℝ) ≤ (n : ℝ) ^ (11 / 40 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      have h0 := floor_rpow_pos (11 / 40) (by norm_num) n (by omega)
      exact_mod_cast h0
    have hx1 : (1 : ℝ) ≤ ((4 * pP0 n : ℕ) : ℝ) ^ 2 * (2 * (pY δ n : ℝ)) := by
      push_cast; nlinarith
    have hx : ((4 * pP0 n : ℕ) : ℝ) ^ 2 * (2 * (pY δ n : ℝ)) ≤ (n : ℝ) ^ 9 := by
      push_cast
      have h1 : (4 * (pP0 n : ℝ)) ^ 2 ≤ 16 * (n : ℝ) ^ 2 := by nlinarith
      have h2 : 32 * (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 9 := by
        have : (32 : ℝ) ≤ (n : ℝ) ^ 5 := by
          calc (32 : ℝ) = 2 ^ 5 := by norm_num
            _ ≤ (n : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hnR 5
        nlinarith [pow_pos (show (0 : ℝ) < n by linarith) 4]
      calc (4 * (pP0 n : ℝ)) ^ 2 * (2 * (pY δ n : ℝ)) ≤ (16 * (n : ℝ) ^ 2) * (2 * (n : ℝ) ^ 2) := by
            gcongr
        _ = 32 * (n : ℝ) ^ 4 := by ring
        _ ≤ (n : ℝ) ^ 9 := h2
    have := log_le_mul_log _ 9 n hn hx1 hx
    refine ⟨?_, by push_cast at this ⊢; linarith⟩
    have := Real.log_nonneg hx1
    linarith

theorem pl_pow2Y (ε : ℝ) (hε : 0 ≤ ε) : PowLe (fun n => (2 * (pY δ n : ℝ)) ^ (2 * ε)) (6 * ε) :=
  (PowLe.self (6 * ε)).of_le 2 fun n hn => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hY2, hY1⟩ := pbounds δ hδ0 hδ n hn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : 2 * (pY δ n : ℝ) ≤ (n : ℝ) ^ 3 := by nlinarith
    refine ⟨by positivity, ?_⟩
    calc (2 * (pY δ n : ℝ)) ^ (2 * ε) ≤ ((n : ℝ) ^ 3) ^ (2 * ε) :=
          Real.rpow_le_rpow (by positivity) h3 (by linarith)
      _ = (n : ℝ) ^ (6 * ε) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; push_cast; ring_nf

theorem pl_isqrtB : PowLe (fun n => 6 / Real.sqrt (pB0 n : ℝ)) (-(1 / 25)) :=
  PowLe.div_of_ge (f := fun n => Real.sqrt (pB0 n : ℝ)) (Real.sqrt (1 / 2)) (1 / 25) 6 (by positivity)
    (by norm_num) 2 fun n hn => by
    obtain ⟨-, -, -, -, -, -, -, gB, -⟩ := pbounds δ hδ0 hδ n hn
    have e : Real.sqrt ((1 / 2) * (n : ℝ) ^ (2 / 25 : ℝ)) = Real.sqrt (1 / 2) * (n : ℝ) ^ (1 / 25 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow ((n : ℝ) ^ (2 / 25 : ℝ)),
        ← Real.rpow_mul (by positivity)]
      norm_num
    rw [← e]
    exact Real.sqrt_le_sqrt gB

/-- The exponent of `Umax`. -/
noncomputable def uE (δ : ℝ) : ℝ := (2 * (9 / 250) + 1 + δ - 11 / 40) / 3

theorem pl_Umax : PowLe (fun n => pUmax δ n) (uE δ) := by
  have hu : (1 / 250 : ℝ) ≤ uE δ := by unfold uE; linarith
  have hu0 : (0 : ℝ) ≤ uE δ := by unfold uE; linarith
  have h1 : PowLe (fun _ => (1 : ℝ)) (uE δ) := (PowLe.const 1 (by norm_num)).mono hu0
  have h2 : PowLe (fun n => 2 * (pR n : ℝ)) (uE δ) := ((pl_R δ hδ0 hδ).cmul 2 (by norm_num)).mono hu
  have h3 : PowLe (fun n => (16 * (pK n : ℝ) ^ 2 * (pY δ n : ℝ) / (pP0 n : ℝ)) ^ (1 / 3 : ℝ)) (uE δ) := by
    refine ((PowLe.self (uE δ)).cmul (32 ^ (1 / 3 : ℝ)) (by positivity)).of_le 2 fun n hn => ?_
    obtain ⟨-, -, -, fK, -, fY, gP, -⟩ := pbounds δ hδ0 hδ n hn
    have hn0 : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                                 linarith
    have hP0pos : (0 : ℝ) < pP0 n := lt_of_lt_of_le (by positivity) gP
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
    refine ⟨by positivity, ?_⟩
    calc (16 * (pK n : ℝ) ^ 2 * (pY δ n : ℝ) / (pP0 n : ℝ)) ^ (1 / 3 : ℝ)
        ≤ (32 * (n : ℝ) ^ (2 * (9 / 250) + 1 + δ - 11 / 40)) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow hx0 hx (by norm_num)
      _ = 32 ^ (1 / 3 : ℝ) * (n : ℝ) ^ (uE δ) := by
          unfold uE
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hn0.le]; ring_nf
  exact (h1.max' h2).max' h3

theorem pl_X : PowLe (fun n => pX δ n) (1 / 250 + 11 / 40 + uE δ + uE δ / 2 + -(1 - δ)) := by
  have h := (((((pl_R δ hδ0 hδ).cmul 2 (by norm_num)).mul (pl_P δ hδ0 hδ)).mul (pl_Umax δ hδ0 hδ)).mul
    (pl_Umax δ hδ0 hδ).sqrt).mul (pl_invy δ hδ0 hδ)
  refine h.of_le 2 fun n hn => ⟨?_, le_of_eq ?_⟩
  · unfold pX; have := pUmax_ge_one δ n; positivity
  · unfold pX; ring

end bounds

section sigma

variable (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8000) (ε θ C : ℝ) (hε : 0 ≤ ε) (hθ : 0 < θ)
  (hsm : δ + 6 * ε + 2 * θ ≤ 1 / 1000) (Λ : ℕ → ℝ) (hΛ : PowLe Λ δ)
include hδ0 hδ hε hθ hsm hΛ

theorem pl_lam (k : ℝ) (hk : 0 ≤ k) : PowLe (fun n => 3 + k * Λ n) δ :=
  ((PowLe.const 3 (by norm_num)).mono hδ0.le).add (hΛ.cmul k hk)

theorem pl_M1 : PowLe (pM1 δ ε C Λ) (-(7 / 200)) := by
  have a := pl_invP δ hδ0 hδ
  have t := ((((pl_lam δ hδ0 hδ ε θ hε hθ hsm Λ hΛ 4 (by norm_num)).mul (PowLe.const 3 (by norm_num))).mul
    (PowLe.const (C ^ 2) (by positivity))).mul (pl_pow2Y δ hδ0 hδ ε hε)).mul (pl_log2Y δ hδ0 hδ θ hθ)
  have l2 : PowLe (fun n => (1 + Real.log (2 * (pY δ n : ℝ))) / (pK n : ℝ)) (θ + -(9 / 250)) :=
    ((pl_log2Y δ hδ0 hδ θ hθ).mul (pl_invK δ hδ0 hδ)).congr 0 fun n _ => by ring
  have last := ((pl_isqrtB δ hδ0 hδ).mono (show -(1 / 25 : ℝ) ≤ θ + -(9 / 250) by linarith)).add l2
  have T := t.mul last
  refine ((a.mono (show -(11 / 40 : ℝ) ≤ -(7 / 200) by norm_num)).add (T.mono ?_)).congr 0 fun n _ => rfl
  linarith

theorem pl_M2 : PowLe (pM2 δ ε C Λ) (-(7 / 200)) := by
  have a := pl_invP δ hδ0 hδ
  have t := (((((pl_lam δ hδ0 hδ ε θ hε hθ hsm Λ hΛ 4 (by norm_num)).mul (PowLe.const 12 (by norm_num))).mul
    (pl_P δ hδ0 hδ)).mul (PowLe.const (C ^ 2) (by positivity))).mul (pl_pow2Y δ hδ0 hδ ε hε)).mul
    (pl_log2Y δ hδ0 hδ θ hθ)
  have h6 : PowLe (fun n => 6 / (pP0 n : ℝ) ^ 2) (-(11 / 20)) :=
    PowLe.div_of_ge (f := fun n => (pP0 n : ℝ) ^ 2) (1 / 4) (11 / 20) 6 (by norm_num) (by norm_num) 2
      fun n hn => by
        obtain ⟨-, -, -, -, -, -, gP, -⟩ := pbounds δ hδ0 hδ n hn
        have hn0 : (0 : ℝ) < n := by have : (2 : ℝ) ≤ n := by exact_mod_cast hn
                                     linarith
        have e : (n : ℝ) ^ (11 / 20 : ℝ) = (n : ℝ) ^ (11 / 40 : ℝ) * (n : ℝ) ^ (11 / 40 : ℝ) := by
          rw [← Real.rpow_add hn0]; norm_num
        rw [e, sq]
        have h0 : 0 ≤ (1 / 2) * (n : ℝ) ^ (11 / 40 : ℝ) := by positivity
        nlinarith [mul_le_mul gP gP h0 (h0.trans gP)]
  have hlx := (pl_logP2Y δ hδ0 hδ θ hθ).mul (pl_X δ hδ0 hδ)
  have last := (h6.mono (show -(11 / 20 : ℝ) ≤ -(8 / 25) by norm_num)).add (hlx.mono (by unfold uE; linarith))
  have T := t.mul last
  refine ((a.mono (show -(11 / 40 : ℝ) ≤ -(7 / 200) by norm_num)).add (T.mono ?_)).congr 0 fun n _ => rfl
  linarith

theorem pl_PV : PowLe (pPV δ Λ) (-(7 / 400)) := by
  have hs : PowLe (fun n => Real.sqrt (n : ℝ)) (1 / 2) :=
    (PowLe.self (1 / 2)).congr 0 fun n _ => Real.sqrt_eq_rpow _
  have T := ((((((pl_B0 δ hδ0 hδ).mul (pl_B0 δ hδ0 hδ)).mul
    (pl_lam δ hδ0 hδ ε θ hε hθ hsm Λ hΛ 2 (by norm_num))).mul hs).mul (PowLe.log_add_one θ hθ)).mul
    (pl_P0 δ hδ0 hδ)).mul (pl_invY4 δ hδ0 hδ)
  refine (T.mono ?_).congr 0 fun n _ => ?_
  · linarith
  · unfold pPV; rw [div_div_eq_mul_div]; ring

theorem powLe_sigma : PowLe (pσ δ ε C Λ) (-(7 / 400)) := by
  have h1 := (pl_M1 δ hδ0 hδ ε θ C hε hθ hsm Λ hΛ).sqrt
  have h2 := (pl_M2 δ hδ0 hδ ε θ C hε hθ hsm Λ hΛ).sqrt
  have h3 := pl_PV δ hδ0 hδ ε θ hε hθ hsm Λ hΛ
  exact ((h1.mono (by norm_num)).max' (h2.mono (by norm_num))).max' h3

end sigma

end ThreeSquares
