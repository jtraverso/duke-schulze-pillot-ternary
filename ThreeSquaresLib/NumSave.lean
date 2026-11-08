/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.BlockSum

/-!
# Uniform bounds for the saving factors

`S_M1 ≤ 1/P + (3+4Λ) 3C² Y^{2ε} (1 + log Y) (6/√B₀ + (1 + log Y)/K)` when `B₀ ≤ U ≤ Y`, `K √U ≤ A`;
`S_M2 ≤ 1/P + (3+4Λ) 12 P C² Y^{2ε} (1 + log Y)(6/P₀² + (1 + log(P² Y)) X)` when `1 ≤ U ≤ Y`, `√U/B ≤ X`.
-/

@[expose] public section

namespace ThreeSquares

theorem save_m1 (P A U Y B₀ K C ε Λ : ℝ) (hP : 0 < P) (hA : 0 < A) (hU1 : 1 ≤ U) (hUY : U ≤ Y)
    (hB₀ : 0 < B₀) (hB₀U : B₀ ≤ U) (hK : 0 < K) (hKA : K * Real.sqrt U ≤ A) (hC : 0 < C)
    (hε : 0 ≤ ε) (hΛ : 0 ≤ Λ) :
    1 / P + (3 + 4 * Λ) * P ^ 2 *
        ((6 * A / U + 1 + Real.log U) * (C ^ 2 * U ^ (2 * ε) * Real.sqrt U) * (3 * U * (1 + Real.log U))) /
          (P ^ 2 * A * U) ≤
      1 / P + (3 + 4 * Λ) * 3 * C ^ 2 * Y ^ (2 * ε) * (1 + Real.log Y) *
        (6 / Real.sqrt B₀ + (1 + Real.log Y) / K) := by
  have hU0 : 0 < U := by linarith
  have hsU : 0 < Real.sqrt U := Real.sqrt_pos.mpr hU0
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU1
  have hlogUY : Real.log U ≤ Real.log Y := Real.log_le_log hU0 hUY
  have hUe : U ^ (2 * ε) ≤ Y ^ (2 * ε) := Real.rpow_le_rpow hU0.le hUY (by linarith)
  have hUe0 : 0 ≤ U ^ (2 * ε) := Real.rpow_nonneg hU0.le _
  -- rewrite the second summand
  have e : (3 + 4 * Λ) * P ^ 2 *
        ((6 * A / U + 1 + Real.log U) * (C ^ 2 * U ^ (2 * ε) * Real.sqrt U) * (3 * U * (1 + Real.log U))) /
          (P ^ 2 * A * U) =
      (3 + 4 * Λ) * 3 * C ^ 2 * U ^ (2 * ε) * (1 + Real.log U) *
        (6 / Real.sqrt U + (1 + Real.log U) * Real.sqrt U / A) := by
    have hsq : Real.sqrt U * Real.sqrt U = U := Real.mul_self_sqrt hU0.le
    have k1 : Real.sqrt U / U = 1 / Real.sqrt U := by
      rw [div_eq_div_iff hU0.ne' hsU.ne', one_mul, hsq]
    calc _ = (3 + 4 * Λ) * 3 * C ^ 2 * U ^ (2 * ε) * (1 + Real.log U) *
          (6 * (Real.sqrt U / U) + (1 + Real.log U) * Real.sqrt U / A) := by
          field_simp; ring
      _ = _ := by rw [k1]; ring
  rw [e]
  have h1 : 6 / Real.sqrt U ≤ 6 / Real.sqrt B₀ :=
    div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hB₀) (Real.sqrt_le_sqrt hB₀U)
  have h2 : (1 + Real.log U) * Real.sqrt U / A ≤ (1 + Real.log Y) / K := by
    rw [div_le_div_iff₀ hA hK]
    have : (1 + Real.log U) * (Real.sqrt U * K) ≤ (1 + Real.log Y) * A := by
      calc (1 + Real.log U) * (Real.sqrt U * K) ≤ (1 + Real.log Y) * (Real.sqrt U * K) := by
            gcongr
        _ ≤ (1 + Real.log Y) * A := by
            gcongr
            · linarith
            · linarith [hKA, mul_comm K (Real.sqrt U)]
    linarith [this]
  have hpos : 0 ≤ (3 + 4 * Λ) * 3 * C ^ 2 := by positivity
  have h3 : 0 ≤ 6 / Real.sqrt U + (1 + Real.log U) * Real.sqrt U / A := by positivity
  refine add_le_add le_rfl ?_
  have hY0 : 0 ≤ Y ^ (2 * ε) := Real.rpow_nonneg (by linarith) _
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hUe hpos) (by linarith) (by linarith)
    (mul_nonneg hpos hY0)) (by linarith) h3 (mul_nonneg (mul_nonneg hpos hY0) (by linarith))

theorem save_m2 (P P₀ B U Y X C ε Λ : ℝ) (hP : 1 ≤ P) (hP₀ : 0 < P₀) (hB : 0 < B) (hU1 : 1 ≤ U)
    (hUY : U ≤ Y) (hX : Real.sqrt U / B ≤ X) (hC : 0 < C) (hε : 0 ≤ ε) (hΛ : 0 ≤ Λ) :
    1 / P + (3 + 4 * Λ) * (4 * P ^ 3) *
        ((6 * B / (P₀ ^ 2 * U) + 1 + Real.log (P ^ 2 * U)) * (C ^ 2 * U ^ (2 * ε) * Real.sqrt U) *
          (3 * U * (1 + Real.log U))) / (P ^ 2 * B * U) ≤
      1 / P + (3 + 4 * Λ) * 12 * P * C ^ 2 * Y ^ (2 * ε) * (1 + Real.log Y) *
        (6 / P₀ ^ 2 + (1 + Real.log (P ^ 2 * Y)) * X) := by
  have hP0 : 0 < P := by linarith
  have hU0 : 0 < U := by linarith
  have hsU : 0 < Real.sqrt U := Real.sqrt_pos.mpr hU0
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU1
  have hlogUY : Real.log U ≤ Real.log Y := Real.log_le_log hU0 hUY
  have hUe : U ^ (2 * ε) ≤ Y ^ (2 * ε) := Real.rpow_le_rpow hU0.le hUY (by linarith)
  have hUe0 : 0 ≤ U ^ (2 * ε) := Real.rpow_nonneg hU0.le _
  have hlogPU : 0 ≤ Real.log (P ^ 2 * U) := Real.log_nonneg (by nlinarith)
  have hlogPUY : Real.log (P ^ 2 * U) ≤ Real.log (P ^ 2 * Y) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have e : (3 + 4 * Λ) * (4 * P ^ 3) *
        ((6 * B / (P₀ ^ 2 * U) + 1 + Real.log (P ^ 2 * U)) * (C ^ 2 * U ^ (2 * ε) * Real.sqrt U) *
          (3 * U * (1 + Real.log U))) / (P ^ 2 * B * U) =
      (3 + 4 * Λ) * 12 * P * C ^ 2 * U ^ (2 * ε) * (1 + Real.log U) *
        (6 / (P₀ ^ 2 * Real.sqrt U) + (1 + Real.log (P ^ 2 * U)) * (Real.sqrt U / B)) := by
    have hsq : Real.sqrt U * Real.sqrt U = U := Real.mul_self_sqrt hU0.le
    have k1 : Real.sqrt U / U = 1 / Real.sqrt U := by
      rw [div_eq_div_iff hU0.ne' hsU.ne', one_mul, hsq]
    calc _ = (3 + 4 * Λ) * 12 * P * C ^ 2 * U ^ (2 * ε) * (1 + Real.log U) *
          (6 / P₀ ^ 2 * (Real.sqrt U / U) + (1 + Real.log (P ^ 2 * U)) * (Real.sqrt U / B)) := by
          field_simp; ring
      _ = _ := by rw [k1]; field_simp
  rw [e]
  have h1 : 6 / (P₀ ^ 2 * Real.sqrt U) ≤ 6 / P₀ ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have : 1 ≤ Real.sqrt U := by rw [Real.one_le_sqrt]; exact hU1
    nlinarith [pow_pos hP₀ 2]
  have h2 : (1 + Real.log (P ^ 2 * U)) * (Real.sqrt U / B) ≤ (1 + Real.log (P ^ 2 * Y)) * X := by
    have : 0 ≤ Real.sqrt U / B := by positivity
    calc (1 + Real.log (P ^ 2 * U)) * (Real.sqrt U / B) ≤ (1 + Real.log (P ^ 2 * Y)) * (Real.sqrt U / B) := by
          gcongr
      _ ≤ (1 + Real.log (P ^ 2 * Y)) * X := by gcongr; linarith
  have hpos : 0 ≤ (3 + 4 * Λ) * 12 * P * C ^ 2 := by positivity
  have h3 : 0 ≤ 6 / (P₀ ^ 2 * Real.sqrt U) + (1 + Real.log (P ^ 2 * U)) * (Real.sqrt U / B) := by positivity
  refine add_le_add le_rfl ?_
  have hY0 : 0 ≤ Y ^ (2 * ε) := Real.rpow_nonneg (by linarith) _
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hUe hpos) (by linarith) (by linarith)
    (mul_nonneg hpos hY0)) (by linarith) h3 (mul_nonneg (mul_nonneg hpos hY0) (by linarith))

end ThreeSquares
