/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot, Juan Pablo Traverso Gianini
The partial-summation argument is adapted from Mathlib's
NumberTheory/LSeries/SumCoeff.lean (Apache-2.0).
-/
module

public import Mathlib.NumberTheory.LSeries.SumCoeff
public import SiegelThmSolution

/-! # Conditional convergence of character sums at s = 1

This uses bounded partial sums and partial summation, rather than absolute
convergence of the Dirichlet series at its boundary.
-/

@[expose] public section
namespace ThreeSquares.B3
open Finset Filter Asymptotics MeasureTheory Complex Topology

/-- Partial summation still gives a limit without absolute convergence. -/
theorem partial_sum_cpow_tendsto {f : ℕ → ℂ} (hf : f 0 = 0) {r : ℝ} (hr : 0 ≤ r) {s : ℂ}
    (hs : r < s.re)
    (hO : (fun n ↦ ∑ k ∈ Icc 1 n, f k) =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    Tendsto (fun n : ℕ => ∑ k ∈ Icc 0 n,f k*(k:ℂ)^(-s)) atTop
      (𝓝 (s*∫ t in Set.Ioi (1:ℝ),(∑ k ∈ Icc 1 ⌊t⌋₊,f k)*(t:ℂ)^(-(s+1)))) := by
  have h₁ : (-s - 1).re + r < -1 := by
    rwa [sub_re, one_re, neg_re, neg_sub_left, neg_add_lt_iff_lt_add, add_neg_cancel_comm]
  have h₂ : s ≠ 0 := ne_zero_of_re_pos (hr.trans_lt hs)
  have h₃ (t : ℝ) (ht : t ∈ Set.Ici 1) : DifferentiableAt ℝ (fun x : ℝ ↦ (x : ℂ) ^ (-s)) t :=
    differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht).ne' (neg_ne_zero.mpr h₂)
  have h₄ : ∀ n, ∑ k ∈ Icc 0 n, f k = ∑ k ∈ Icc 1 n, f k := fun n ↦ by
    rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert (by aesop), hf, zero_add, zero_add]
  simp_rw [← h₄] at hO
  rw [← integral_const_mul]
  simp_rw [mul_comm (f _)]
  convert!
    tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (f := fun x ↦ (x : ℂ) ^ (-s)) (l := 0) ?_ hf h₃ ?_
      ?_ ?_ (integrableAtFilter_rpow_atTop_iff.mpr h₁)
  · rw [zero_sub, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne', h₄]
    · ring_nf
    · exact neg_ne_zero.mpr <| ne_zero_of_re_pos (hr.trans_lt hs)
  · refine (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi <|
      integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one
        (by simpa using! hr.trans_lt hs)).locallyIntegrableOn
  · have hlim : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-(s.re - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by rwa [sub_pos])).comp tendsto_natCast_atTop_atTop
    refine (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-s.re) _ _ ?_ hO ?_).trans_tendsto hlim
    · exact isBigO_norm_left.mp (norm_ofReal_cpow_eventually_eq_atTop _).isBigO.natCast_atTop
    · linarith
  · refine .mul_atTop_rpow_of_isBigO_rpow (-(s + 1).re) r _ ?_ ?_ (by rw [← neg_re, neg_add'])
    · simpa [-neg_add_rev, neg_add'] using! isBigO_deriv_ofReal_cpow_const_atTop _
    · exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans <|
        isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0)


/-- The actual analytically continued L-value is the limit used in B3. -/
theorem character_sum_at_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ≠1) :
    Tendsto (fun M : ℕ => ∑ k ∈ Icc 0 M,χ k/(k:ℂ)) atTop
      (𝓝 (DirichletCharacter.LFunction χ 1)) := by
  let f : ℕ → ℂ := fun k => if k=0 then 0 else χ k
  have hf : f 0=0 := by simp [f]
  have hsum (M : ℕ) : ∑ k ∈ Icc 1 M,f k = ∑ k ∈ Icc 1 M,χ k := by
    apply sum_congr rfl
    intro k hk
    simp [f,ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (mem_Icc.mp hk).1)]
  have hO : (fun M ↦ ∑ k ∈ Icc 1 M,f k) =O[atTop] fun M ↦ (M:ℝ)^(0:ℝ) := by
    apply IsBigO.of_bound N
    apply Filter.Eventually.of_forall
    intro M
    simp only [Real.rpow_zero,norm_one,mul_one,hsum]
    exact SiegelThm.norm_sum_Icc_le hχ M
  have h := partial_sum_cpow_tendsto hf (r:=0) le_rfl (s:=1) (by norm_num) hO
  rw [SiegelThm.LFunction_eq_integral _ χ hχ 1 (by norm_num : 0<(1:ℂ).re)]
  convert h using 1
  · funext M
    apply sum_congr rfl
    intro k _
    by_cases hk : k=0
    · simp [hk,f]
    · simp [f,hk,div_eq_mul_inv,Complex.cpow_neg_one]
  · congr 2
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [hsum]

end ThreeSquares.B3
