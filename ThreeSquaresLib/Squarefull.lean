/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.GeneralKl
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Squarefull parts on average

* `sfp_eq_sq_mul_cube`: `sfp b = u² v³`;
* `sum_sqrt_sfp_le`: `∑_{b ≤ X} √(sfp b) ≤ 3 X (1 + log X)`.
-/

@[expose] public section

namespace ThreeSquares

open Finset

theorem sfp_one : sfp 1 = 1 := by simp [sfp]

theorem sfp_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    sfp (p ^ k) = if k ≤ 1 then 1 else p ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [sfp_one]
  · unfold sfp
    rw [Nat.primeFactors_prime_pow (by omega) hp, Finset.prod_singleton,
      Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
    by_cases h1 : k = 1
    · subst h1; simp
    · rw [if_neg h1, if_neg (by omega)]

theorem sfp_eq_sq_mul_cube : ∀ b : ℕ, b ≠ 0 → ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ sfp b = u ^ 2 * v ^ 3 := by
  intro b
  induction b using Nat.recOnPrimeCoprime with
  | zero => intro h; exact absurd rfl h
  | prime_pow p k hp =>
    intro _
    rw [sfp_prime_pow hp]
    split_ifs with hk
    · exact ⟨1, 1, one_pos, one_pos, by ring⟩
    · obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
      · exact ⟨p ^ j, 1, pow_pos hp.pos _, one_pos, by rw [hj]; ring⟩
      · refine ⟨p ^ (j - 1), p, pow_pos hp.pos _, hp.pos, ?_⟩
        rw [hj, ← pow_mul, ← pow_add]; congr 1; omega
  | coprime a b ha hb hab iha ihb =>
    intro _
    obtain ⟨u₁, v₁, hu₁, hv₁, h₁⟩ := iha (by omega)
    obtain ⟨u₂, v₂, hu₂, hv₂, h₂⟩ := ihb (by omega)
    refine ⟨u₁ * u₂, v₁ * v₂, Nat.mul_pos hu₁ hu₂, Nat.mul_pos hv₁ hv₂, ?_⟩
    rw [sfp_mul (by omega) (by omega) hab, h₁, h₂]; ring

theorem sfp_dvd : ∀ b : ℕ, b ≠ 0 → sfp b ∣ b := by
  intro b
  induction b using Nat.recOnPrimeCoprime with
  | zero => intro h; exact absurd rfl h
  | prime_pow p k hp =>
    intro _
    rw [sfp_prime_pow hp]
    split_ifs
    · exact one_dvd _
    · exact dvd_rfl
  | coprime a b ha hb hab iha ihb =>
    intro _
    rw [sfp_mul (by omega) (by omega) hab]
    exact Nat.mul_dvd_mul (iha (by omega)) (ihb (by omega))

theorem inv_cube_half_le (v : ℕ) :
    1 / (((v + 1 : ℕ) : ℝ) * Real.sqrt ((v + 1 : ℕ) : ℝ)) ≤
      2 * (1 / Real.sqrt (v : ℝ) - 1 / Real.sqrt ((v + 1 : ℕ) : ℝ)) ∨ v = 0 := by
  rcases Nat.eq_zero_or_pos v with h | hv
  · right; exact h
  · left
    set a := Real.sqrt (v : ℝ)
    set b := Real.sqrt ((v + 1 : ℕ) : ℝ)
    have ha : 0 < a := Real.sqrt_pos.mpr (by exact_mod_cast hv)
    have hb : 0 < b := Real.sqrt_pos.mpr (by positivity)
    have ha2 : a ^ 2 = v := Real.sq_sqrt (by positivity)
    have hb2 : b ^ 2 = ((v + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
    have hab : a ≤ b := Real.sqrt_le_sqrt (by push_cast; linarith)
    have hb2' : b ^ 2 = a ^ 2 + 1 := by rw [hb2, ha2]; push_cast; ring
    rw [← hb2]
    rw [div_le_iff₀ (by positivity)]
    have e : 2 * (1 / a - 1 / b) * (b ^ 2 * b) = 2 * b ^ 2 * (b - a) / a := by
      field_simp
    rw [e, le_div_iff₀ ha]
    -- `a ≤ 2 b² (b − a)` since `(b − a)(b + a) = 1`
    have h1 : (b - a) * (b + a) = 1 := by nlinarith
    nlinarith [mul_pos ha hb]

theorem sum_inv_cube_half_le (V : ℕ) :
    ∑ v ∈ range V, 1 / (((v + 1 : ℕ) : ℝ) * Real.sqrt ((v + 1 : ℕ) : ℝ)) ≤ 3 := by
  -- telescoping from `v = 1`
  have key : ∀ V : ℕ, ∑ v ∈ range V, 1 / (((v + 1 : ℕ) : ℝ) * Real.sqrt ((v + 1 : ℕ) : ℝ)) ≤
      3 - 2 / Real.sqrt ((V : ℕ) : ℝ) ∨ V = 0 := by
    intro V
    induction V with
    | zero => right; rfl
    | succ k ih =>
      left
      rw [Finset.sum_range_succ]
      rcases ih with ih | rfl
      · rcases inv_cube_half_le k with h | rfl
        · have : 2 / Real.sqrt ((k + 1 : ℕ) : ℝ) = 2 * (1 / Real.sqrt ((k + 1 : ℕ) : ℝ)) := by ring
          have : 2 / Real.sqrt (k : ℝ) = 2 * (1 / Real.sqrt (k : ℝ)) := by ring
          push_cast at *
          linarith
        · norm_num
      · norm_num
  rcases key V with h | rfl
  · have : 0 ≤ 2 / Real.sqrt ((V : ℕ) : ℝ) := by positivity
    linarith
  · simp

theorem card_multiples_le (s X : ℕ) (hs : 0 < s) :
    ((Icc 1 X).filter (fun b => s ∣ b)).card ≤ X / s := by
  calc ((Icc 1 X).filter (fun b => s ∣ b)).card ≤ (Icc 1 (X / s)).card := by
        refine Finset.card_le_card_of_injOn (fun b => b / s) (fun b hb => ?_) (fun b hb c hc h => ?_)
        · simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hb
          obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hb
          simp only [Finset.coe_Icc, Set.mem_Icc]
          rw [Nat.mul_div_cancel_left _ hs]
          refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at h1), ?_⟩
          rw [Nat.le_div_iff_mul_le hs, mul_comm]; exact h2
        · simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at hb hc
          obtain ⟨-, k, rfl⟩ := hb
          obtain ⟨-, l, rfl⟩ := hc
          simp only [Nat.mul_div_cancel_left _ hs] at h
          rw [h]
    _ = X / s := by simp

/-- **`∑_{b ≤ X} √(sfp b) ≤ 3 X (1 + log X)`.** -/
theorem sum_sqrt_sfp_le (X : ℕ) :
    ∑ b ∈ Icc 1 X, Real.sqrt (sfp b) ≤ 3 * X * (1 + Real.log X) := by
  classical
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp
  set f : ℕ → ℝ := fun s => Real.sqrt s
  rw [show (∑ b ∈ Icc 1 X, Real.sqrt (sfp b)) = ∑ b ∈ Icc 1 X, f (sfp b) from rfl, Finset.sum_comp]
  set T := (Icc 1 X).image sfp
  -- each fiber has at most `X / s` elements
  have h1 : ∑ s ∈ T, ((Icc 1 X).filter (fun b => sfp b = s)).card • f s ≤
      ∑ s ∈ T, (X : ℝ) * (1 / Real.sqrt s) := by
    refine Finset.sum_le_sum fun s hs => ?_
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hs
    have hb₀0 : b₀ ≠ 0 := by simp at hb₀; omega
    have hs0 : 0 < sfp b₀ := sfp_pos b₀
    have hcard : ((Icc 1 X).filter (fun b => sfp b = sfp b₀)).card ≤ X / sfp b₀ := by
      refine le_trans (Finset.card_le_card fun b hb => ?_) (card_multiples_le _ X hs0)
      simp only [Finset.mem_filter, Finset.mem_Icc] at hb ⊢
      refine ⟨hb.1, ?_⟩
      rw [← hb.2]; exact sfp_dvd b (by omega)
    rw [nsmul_eq_mul]
    have hsq : f (sfp b₀) = Real.sqrt (sfp b₀) := rfl
    have hpos : (0 : ℝ) < Real.sqrt (sfp b₀) := Real.sqrt_pos.mpr (by exact_mod_cast hs0)
    calc (((Icc 1 X).filter (fun b => sfp b = sfp b₀)).card : ℝ) * f (sfp b₀)
        ≤ ((X / sfp b₀ : ℕ) : ℝ) * Real.sqrt (sfp b₀) := by
          rw [hsq]; gcongr
      _ ≤ ((X : ℝ) / sfp b₀) * Real.sqrt (sfp b₀) := by
          gcongr; exact Nat.cast_div_le
      _ = (X : ℝ) * (1 / Real.sqrt (sfp b₀)) := by
          have hss : (sfp b₀ : ℝ) = Real.sqrt (sfp b₀) * Real.sqrt (sfp b₀) :=
            (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
          rw [mul_one_div, div_mul_eq_mul_div, div_eq_div_iff (by positivity) hpos.ne', mul_assoc,
            Real.mul_self_sqrt (Nat.cast_nonneg _)]
  -- `T` is covered by `u² v³` with `u, v ≤ X`
  set box := Icc 1 X ×ˢ Icc 1 X
  have hT : T ⊆ box.image (fun uv : ℕ × ℕ => uv.1 ^ 2 * uv.2 ^ 3) := by
    intro s hs
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hs
    have hb0 : b ≠ 0 := by simp at hb; omega
    obtain ⟨u, v, hu, hv, he⟩ := sfp_eq_sq_mul_cube b hb0
    have hle : sfp b ≤ X := (Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) (sfp_dvd b hb0)).trans
      (Finset.mem_Icc.mp hb).2
    refine Finset.mem_image.mpr ⟨(u, v), ?_, he.symm⟩
    simp only [box, Finset.mem_product, Finset.mem_Icc]
    have hu' : u ≤ u ^ 2 * v ^ 3 := by
      calc u ≤ u ^ 2 := by nlinarith
        _ ≤ u ^ 2 * v ^ 3 := Nat.le_mul_of_pos_right _ (pow_pos hv 3)
    have hv' : v ≤ u ^ 2 * v ^ 3 := by
      calc v ≤ v ^ 3 := by nlinarith [pow_pos hv 2]
        _ ≤ u ^ 2 * v ^ 3 := Nat.le_mul_of_pos_left _ (pow_pos hu 2)
    omega
  have h2 : ∑ s ∈ T, (X : ℝ) * (1 / Real.sqrt s) ≤
      ∑ uv ∈ box, (X : ℝ) * (1 / Real.sqrt ((uv.1 ^ 2 * uv.2 ^ 3 : ℕ) : ℝ)) := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hT fun _ _ _ => by positivity).trans ?_
    exact Finset.sum_image_le_of_nonneg fun _ _ => by positivity
  have h3 : ∀ uv : ℕ × ℕ, uv ∈ box → 1 / Real.sqrt ((uv.1 ^ 2 * uv.2 ^ 3 : ℕ) : ℝ) =
      (1 / (uv.1 : ℝ)) * (1 / ((uv.2 : ℝ) * Real.sqrt uv.2)) := by
    intro uv _
    push_cast
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
      show ((uv.2 : ℝ)) ^ 3 = (uv.2 : ℝ) ^ 2 * uv.2 by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
    field_simp
  have h4 : ∑ uv ∈ box, (X : ℝ) * (1 / Real.sqrt ((uv.1 ^ 2 * uv.2 ^ 3 : ℕ) : ℝ)) =
      (X : ℝ) * ((∑ u ∈ Icc 1 X, 1 / (u : ℝ)) * ∑ v ∈ Icc 1 X, 1 / ((v : ℝ) * Real.sqrt v)) := by
    rw [← Finset.mul_sum, Finset.sum_congr rfl h3, Finset.sum_product, Finset.sum_mul_sum]
  have hH : ∑ u ∈ Icc 1 X, 1 / (u : ℝ) ≤ 1 + Real.log X := by
    have := harmonic_le_one_add_log X
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    simpa [one_div] using this
  have hV : ∑ v ∈ Icc 1 X, 1 / ((v : ℝ) * Real.sqrt v) ≤ 3 := by
    have := sum_inv_cube_half_le X
    rw [show Icc 1 X = Ico 1 (X + 1) from by ext; simp, Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel]
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun v _ => ?_
    push_cast; ring_nf
  have hl : 0 ≤ 1 + Real.log X := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ X by exact_mod_cast hX); linarith
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := h4
    _ ≤ (X : ℝ) * ((1 + Real.log X) * 3) := by
        gcongr
    _ = 3 * X * (1 + Real.log X) := by ring

end ThreeSquares
