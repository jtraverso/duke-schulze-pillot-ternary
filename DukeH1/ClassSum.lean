/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.BlockBound
public import FourSquaresCaps.ArithSums

/-!
# Class sums

* `BlockHyp`: the numerical hypotheses of the block bounds, bundled;
* `class_bound_A` / `class_bound_B`: `∑_p ‖Asum_p‖ ≤ (L+1)² σ P W₀ 4Y/P₀` for `r ≤ R`;
* `asum_trivial`: `∑_{t₁, t₂ < r} ‖Asum_p‖ ≤ W₀ (Y/(r p)) (1 + log Y)` (for the tail `r > R`).
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open Finset

/-- The numerical hypotheses of `block_bound_A` / `block_bound_B`. -/
structure BlockHyp (Ps : Finset ℕ) (P₀ P ℓ n y Y B₀ K R : ℕ) (Wk1 Wk2 : ℕ → ℂ)
    (W₀ W₁ C ε Λ Umax X σ : ℝ) : Prop where
  hW1 : SmoothW Wk1 W₀ W₁
  hW2 : SmoothW Wk2 W₀ W₁
  hA1 : ∀ c, y < c → c ≤ Y → W1 ℓ n c = Wk1 c
  hA2 : ∀ c, y < c → c ≤ Y → W2 ℓ n c = Wk2 c
  hn : Squarefree n
  hn4 : n % 4 = 3
  hPs : ∀ p ∈ Ps, p.Prime ∧ ¬ p ∣ 2 * n ∧ P₀ ≤ p ∧ p ≤ P
  hP₀ : 0 < P₀
  hP₀P : P₀ ≤ P
  hC : 0 < C
  hε : 0 ≤ ε
  hτ : ∀ m : ℕ, m ≠ 0 → ((m.divisors.card : ℕ) : ℝ) ≤ C * (m : ℝ) ^ ε
  hΛ0 : 0 ≤ Λ
  hΛ : W₁ ≤ Λ * W₀
  hK : 0 < K
  hB₀R : 2 * R ≤ B₀
  hσ : 0 ≤ σ
  hU1 : 2 * (R : ℝ) ≤ Umax
  hU2 : 16 * (K : ℝ) ^ 2 * Y ≤ Umax ^ 3 * P₀
  hU3 : Umax < P₀
  hU4 : 1 ≤ Umax
  hy : 0 < y
  hX : 2 * (R : ℝ) * P * Umax * Real.sqrt Umax ≤ X * y
  hPV1 : 2 * R ^ 2 * P * B₀ ^ 2 ≤ y
  hPV2 : (B₀ : ℝ) ^ 2 * ((3 + 2 * Λ) * (Real.sqrt n * (1 + Real.log n))) ≤ σ * (4 * Y / P₀)
  hM1 : 1 / (P : ℝ) + (3 + 4 * Λ) * 3 * C ^ 2 * (2 * (Y : ℝ)) ^ (2 * ε) * (1 + Real.log (2 * (Y : ℝ))) *
      (6 / Real.sqrt B₀ + (1 + Real.log (2 * (Y : ℝ))) / K) ≤ σ ^ 2
  hM2 : 1 / (P : ℝ) + (3 + 4 * Λ) * 12 * P * C ^ 2 * (2 * (Y : ℝ)) ^ (2 * ε) * (1 + Real.log (2 * (Y : ℝ))) *
      (6 / (P₀ : ℝ) ^ 2 + (1 + Real.log ((P : ℝ) ^ 2 * (2 * Y))) * X) ≤ σ ^ 2

theorem BlockHyp.rhs_nonneg {Ps : Finset ℕ} {P₀ P ℓ n y Y B₀ K R : ℕ} {Wk1 Wk2 : ℕ → ℂ}
    {W₀ W₁ C ε Λ Umax X σ : ℝ} (H : BlockHyp Ps P₀ P ℓ n y Y B₀ K R Wk1 Wk2 W₀ W₁ C ε Λ Umax X σ) :
    0 ≤ σ * ((P : ℝ) * W₀ * (4 * Y / P₀)) := by
  have := H.hW1.W₀_nonneg
  have := H.hσ
  positivity

/-- Summing the uniform block bound over the `(L+1)²` blocks. -/
theorem sum_blocks_le (Ps : Finset ℕ) (L : ℕ) (G : ℕ → ℕ → ℕ → ℂ) (B : ℝ)
    (hG : ∀ i j, ∑ p ∈ Ps, ‖G p i j‖ ≤ B) :
    ∑ p ∈ Ps, ‖∑ i ∈ range (L + 1), ∑ j ∈ range (L + 1), G p i j‖ ≤ ((L : ℝ) + 1) ^ 2 * B := by
  calc ∑ p ∈ Ps, ‖∑ i ∈ range (L + 1), ∑ j ∈ range (L + 1), G p i j‖
      ≤ ∑ p ∈ Ps, ∑ i ∈ range (L + 1), ∑ j ∈ range (L + 1), ‖G p i j‖ := by
        refine sum_le_sum fun p _ => ?_
        exact (norm_sum_le _ _).trans (sum_le_sum fun i _ => norm_sum_le _ _)
    _ = ∑ i ∈ range (L + 1), ∑ j ∈ range (L + 1), ∑ p ∈ Ps, ‖G p i j‖ := by
        rw [sum_comm]; exact sum_congr rfl fun i _ => sum_comm
    _ ≤ ∑ i ∈ range (L + 1), ∑ j ∈ range (L + 1), B :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => hG i j
    _ = ((L : ℝ) + 1) ^ 2 * B := by simp only [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

theorem class_bound_A {Ps : Finset ℕ} {P₀ P ℓ n y Y B₀ K R : ℕ} {Wk1 Wk2 : ℕ → ℂ}
    {W₀ W₁ C ε Λ Umax X σ : ℝ} (H : BlockHyp Ps P₀ P ℓ n y Y B₀ K R Wk1 Wk2 W₀ W₁ C ε Λ Umax X σ)
    (r t₁ t₂ L : ℕ) (h8 : 8 ∣ r) (hr0 : 0 < r) (hrs : Smooth (S2 n) r) (ht₁ : t₁ < r) (ht₂ : t₂ < r)
    (hn₀ : 1 < n / Nat.gcd n r) (hrR : r ≤ R) (hL : Y < 2 ^ L) :
    ∑ p ∈ Ps, ‖Asum n p y Y r t₁ t₂ (W1 ℓ n) (hInv (-4 * n) r)‖ ≤
      ((L : ℝ) + 1) ^ 2 * (σ * ((P : ℝ) * W₀ * (4 * Y / P₀))) := by
  by_cases hu : IsUnit ((t₁ : ZMod r))
  · simp_rw [Asum_eq_blocks n _ y Y r t₁ t₂ L _ _ hL]
    exact sum_blocks_le Ps L _ _ fun i j => block_bound_A Ps P₀ P ℓ n r y Y t₁ t₂ i j B₀ K R Wk1 Wk2
      H.hW1 H.hW2 H.hA1 H.hA2 H.hn H.hn4 h8 hr0 hrs ht₁ ht₂ hu hn₀ H.hPs H.hP₀ H.hP₀P C ε H.hC H.hε H.hτ
      Λ H.hΛ0 H.hΛ hrR H.hK H.hB₀R Umax X σ H.hσ H.hU1 H.hU2 H.hU3 H.hU4 H.hy H.hX H.hPV1 H.hPV2
      H.hM1 H.hM2
  · rw [sum_eq_zero fun p _ => by rw [Asum_eq_zero_of_not_unit _ _ _ _ _ _ _ _ _ hrs (Or.inl hu), norm_zero]]
    exact mul_nonneg (by positivity) H.rhs_nonneg

theorem class_bound_B {Ps : Finset ℕ} {P₀ P ℓ n y Y B₀ K R : ℕ} {Wk1 Wk2 : ℕ → ℂ}
    {W₀ W₁ C ε Λ Umax X σ : ℝ} (H : BlockHyp Ps P₀ P ℓ n y Y B₀ K R Wk1 Wk2 W₀ W₁ C ε Λ Umax X σ)
    (r t₁ t₂ L : ℕ) (h8 : 8 ∣ r) (hr0 : 0 < r) (hrs : Smooth (S2 n) r) (ht₁ : t₁ < r) (ht₂ : t₂ < r)
    (hn₀ : 1 < n / Nat.gcd n r) (hrR : r ≤ R) (hL : Y < 2 ^ L) :
    ∑ p ∈ Ps, ‖Asum n p y Y r t₁ t₂ (W2 ℓ n) (hInv (4 * n) r)‖ ≤
      ((L : ℝ) + 1) ^ 2 * (σ * ((P : ℝ) * W₀ * (4 * Y / P₀))) := by
  by_cases hu : IsUnit ((t₁ : ZMod r))
  · simp_rw [Asum_eq_blocks n _ y Y r t₁ t₂ L _ _ hL]
    exact sum_blocks_le Ps L _ _ fun i j => block_bound_B Ps P₀ P ℓ n r y Y t₁ t₂ i j B₀ K R Wk1 Wk2
      H.hW1 H.hW2 H.hA1 H.hA2 H.hn H.hn4 h8 hr0 hrs ht₁ ht₂ hu hn₀ H.hPs H.hP₀ H.hP₀P C ε H.hC H.hε H.hτ
      Λ H.hΛ0 H.hΛ hrR H.hK H.hB₀R Umax X σ H.hσ H.hU1 H.hU2 H.hU3 H.hU4 H.hy H.hX H.hPV1 H.hPV2
      H.hM1 H.hM2
  · rw [sum_eq_zero fun p _ => by rw [Asum_eq_zero_of_not_unit _ _ _ _ _ _ _ _ _ hrs (Or.inl hu), norm_zero]]
    exact mul_nonneg (by positivity) H.rhs_nonneg

/-- `#{(a, b) : y < D a b ≤ Y} ≤ (Y/D)(1 + log Y)`. -/
theorem pair_count (D y Y : ℕ) (hD : 0 < D) :
    ∑ a ∈ range (Y + 1), ∑ b ∈ range (Y + 1), (if y < D * a * b ∧ D * a * b ≤ Y then (1 : ℝ) else 0) ≤
      (Y : ℝ) / D * (1 + Real.log Y) := by
  have hrow : ∀ a ∈ range (Y + 1), ∑ b ∈ range (Y + 1),
      (if y < D * a * b ∧ D * a * b ≤ Y then (1 : ℝ) else 0) ≤
        if a = 0 then 0 else (Y : ℝ) / D * (a : ℝ)⁻¹ := by
    intro a _
    split_ifs with ha
    · subst ha; simp
    · rw [sum_boole]
      have hDa : 0 < D * a := Nat.mul_pos hD (Nat.pos_of_ne_zero ha)
      have hsub : (range (Y + 1)).filter (fun b => y < D * a * b ∧ D * a * b ≤ Y) ⊆
          Icc 1 (Y / (D * a)) := by
        intro b hb
        simp only [mem_filter] at hb
        simp only [mem_Icc]
        refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hb), ?_⟩
        rw [Nat.le_div_iff_mul_le hDa, mul_comm]; exact hb.2.2
      calc (((range (Y + 1)).filter (fun b => y < D * a * b ∧ D * a * b ≤ Y)).card : ℝ)
          ≤ ((Icc 1 (Y / (D * a))).card : ℝ) := by exact_mod_cast card_le_card hsub
        _ = ((Y / (D * a) : ℕ) : ℝ) := by simp
        _ ≤ (Y : ℝ) / ((D * a : ℕ) : ℝ) := Nat.cast_div_le
        _ = (Y : ℝ) / D * (a : ℝ)⁻¹ := by push_cast; field_simp
  refine (sum_le_sum hrow).trans ?_
  have e : ∑ a ∈ range (Y + 1), (if a = 0 then (0 : ℝ) else (Y : ℝ) / D * (a : ℝ)⁻¹) =
      ∑ a ∈ Icc 1 Y, (Y : ℝ) / D * (a : ℝ)⁻¹ := by
    rw [← sum_subset (s₁ := Icc 1 Y) (s₂ := range (Y + 1)) (fun a ha => by
      simp only [mem_Icc] at ha; simp only [mem_range]; omega) (fun a ha hna => by
      simp only [mem_range] at ha; simp only [mem_Icc, not_and, not_le] at hna
      have : a = 0 := by omega
      simp [this])]
    exact sum_congr rfl fun a ha => by
      simp only [mem_Icc] at ha; rw [if_neg (by omega)]
  rw [e, ← mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_harmonic_le Y) (by positivity)

/-- **Trivial bound for the class sums** (summed over all classes). -/
theorem asum_trivial (n p y Y r : ℕ) (hr : 0 < r) (hp : 0 < p) (W : ℕ → ℂ) (h : ℕ → ℤ) (W₀ : ℝ)
    (hW0 : 0 ≤ W₀) (hW : ∀ c, y < c → c ≤ Y → ‖W c‖ ≤ W₀) :
    ∑ t₁ ∈ range r, ∑ t₂ ∈ range r, ‖Asum n p y Y r t₁ t₂ W h‖ ≤
      W₀ * ((Y : ℝ) / (r * p) * (1 + Real.log Y)) := by
  set F : ℕ → ℕ → ℂ := fun a b => chiR n a * chiR n b * ker1 r y Y W (h b) p a b
  have hF : ∀ a b, ‖F a b‖ ≤ W₀ * (if y < r * p * a * b ∧ r * p * a * b ≤ Y then 1 else 0) := by
    intro a b
    simp only [F, ker1]
    split_ifs with hc
    · rw [norm_mul, norm_mul, norm_mul, mul_one]
      have h1 := norm_chiR_le n a
      have h2 := norm_chiR_le n b
      have h3 := norm_rph_le b (h b) ((p * a : ℕ) : ℤ)
      have h4 := hW _ hc.1 hc.2
      calc ‖chiR n a‖ * ‖chiR n b‖ * (‖W (r * p * a * b)‖ * ‖rph b (h b) ((p * a : ℕ) : ℤ)‖)
          ≤ 1 * 1 * (W₀ * 1) := by gcongr
        _ = W₀ := by ring
    · simp
  have hmaps : ∀ a ∈ range (Y + 1), a % r ∈ range r := fun a _ => mem_range.mpr (Nat.mod_lt _ hr)
  calc ∑ t₁ ∈ range r, ∑ t₂ ∈ range r, ‖Asum n p y Y r t₁ t₂ W h‖
      ≤ ∑ t₁ ∈ range r, ∑ t₂ ∈ range r, ∑ a ∈ (range (Y + 1)).filter (fun a => a % r = t₁),
          ∑ b ∈ (range (Y + 1)).filter (fun b => b % r = t₂), ‖F a b‖ := by
        refine sum_le_sum fun t₁ _ => sum_le_sum fun t₂ _ => ?_
        exact (norm_sum_le _ _).trans (sum_le_sum fun a _ => norm_sum_le _ _)
    _ = ∑ a ∈ range (Y + 1), ∑ b ∈ range (Y + 1), ‖F a b‖ := by
        have e1 : ∀ t₁ ∈ range r, ∑ t₂ ∈ range r, ∑ a ∈ (range (Y + 1)).filter (fun a => a % r = t₁),
            ∑ b ∈ (range (Y + 1)).filter (fun b => b % r = t₂), ‖F a b‖ =
            ∑ a ∈ (range (Y + 1)).filter (fun a => a % r = t₁), ∑ b ∈ range (Y + 1), ‖F a b‖ := by
          intro t₁ _
          rw [sum_comm]
          exact sum_congr rfl fun a _ => sum_fiberwise_of_maps_to hmaps _
        rw [sum_congr rfl e1]
        exact sum_fiberwise_of_maps_to hmaps _
    _ ≤ ∑ a ∈ range (Y + 1), ∑ b ∈ range (Y + 1),
          W₀ * (if y < r * p * a * b ∧ r * p * a * b ≤ Y then (1 : ℝ) else 0) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => hF a b
    _ = W₀ * ∑ a ∈ range (Y + 1), ∑ b ∈ range (Y + 1),
          (if y < r * p * a * b ∧ r * p * a * b ≤ Y then (1 : ℝ) else 0) := by
        rw [mul_sum]; simp_rw [mul_sum]
    _ ≤ W₀ * ((Y : ℝ) / (r * p) * (1 + Real.log Y)) := by
        refine mul_le_mul_of_nonneg_left ?_ hW0
        have := pair_count (r * p) y Y (Nat.mul_pos hr hp)
        push_cast at this
        exact this

end ThreeSquares
