/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.NumSave

/-!
# The uniform bound for one block

Under explicit numerical hypotheses on the parameters, every dyadic block satisfies
`∑_p ‖ABsum_p‖ ≤ σ · P · W₀ · 4Y/P₀` (`block_bound_A`, `block_bound_B`).
-/

@[expose] public section

namespace ThreeSquares

open Finset

theorem le_of_sq_le_sq_mul (Z T T' S σ : ℝ) (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hσ : 0 ≤ σ) (h : Z ^ 2 ≤ T ^ 2 * S)
    (hS : S ≤ σ ^ 2) (hTT : T ≤ T') : Z ≤ σ * T' := by
  have h1 : Z ^ 2 ≤ (T * σ) ^ 2 := by
    calc Z ^ 2 ≤ T ^ 2 * S := h
      _ ≤ T ^ 2 * σ ^ 2 := by gcongr
      _ = (T * σ) ^ 2 := by ring
  have h2 : Z ≤ T * σ := (pow_le_pow_iff_left₀ hZ (mul_nonneg hT hσ) (by norm_num)).mp h1
  nlinarith [mul_le_mul_of_nonneg_right hTT hσ]

theorem dblock_succ (i : ℕ) : dblock (i + 1) = Ioc (2 ^ i) (2 * 2 ^ i) := rfl

theorem dblock_props (i : ℕ) : ∀ a ∈ dblock i, 0 < a ∧ a ≤ 2 ^ i ∧ 2 ^ i ≤ 2 * a :=
  fun a ha => ⟨dblock_pos ha, dblock_le ha, dblock_ge ha⟩

open Classical in
/-- **The uniform block bound** (case `p ∣ a`). -/
theorem block_bound_A (Ps : Finset ℕ) (P₀ P ℓ n r y Y t₁ t₂ i j B₀ K R : ℕ) (Wk1 Wk2 : ℕ → ℂ)
    {W₀ W₁ : ℝ} (hW1 : SmoothW Wk1 W₀ W₁) (hW2 : SmoothW Wk2 W₀ W₁)
    (hA1 : ∀ c, y < c → c ≤ Y → W1 ℓ n c = Wk1 c) (hA2 : ∀ c, y < c → c ≤ Y → W2 ℓ n c = Wk2 c)
    (hn : Squarefree n) (hn4 : n % 4 = 3) (h8 : 8 ∣ r) (hr0 : 0 < r) (hrs : Smooth (S2 n) r)
    (ht₁ : t₁ < r) (ht₂ : t₂ < r) (hu₁ : IsUnit ((t₁ : ZMod r))) (hn₀ : 1 < n / Nat.gcd n r)
    (hPs : ∀ p ∈ Ps, p.Prime ∧ ¬ p ∣ 2 * n ∧ P₀ ≤ p ∧ p ≤ P) (hP₀ : 0 < P₀) (hP₀P : P₀ ≤ P)
    (C ε : ℝ) (hC : 0 < C) (hε : 0 ≤ ε)
    (hτ : ∀ m : ℕ, m ≠ 0 → ((m.divisors.card : ℕ) : ℝ) ≤ C * (m : ℝ) ^ ε)
    (Λ : ℝ) (hΛ0 : 0 ≤ Λ) (hΛ : W₁ ≤ Λ * W₀) (hrR : r ≤ R) (hK : 0 < K) (hB₀R : 2 * R ≤ B₀)
    (Umax X σ : ℝ) (hσ : 0 ≤ σ) (hU1 : 2 * (R : ℝ) ≤ Umax) (hU2 : 16 * (K : ℝ) ^ 2 * Y ≤ Umax ^ 3 * P₀)
    (hU3 : Umax < P₀) (hU4 : 1 ≤ Umax) (hy : 0 < y)
    (hX : 2 * (R : ℝ) * P * Umax * Real.sqrt Umax ≤ X * y)
    (hPV1 : 2 * R ^ 2 * P * B₀ ^ 2 ≤ y)
    (hPV2 : (B₀ : ℝ) ^ 2 * ((3 + 2 * Λ) * (Real.sqrt n * (1 + Real.log n))) ≤ σ * (4 * Y / P₀))
    (hM1 : 1 / (P : ℝ) + (3 + 4 * Λ) * 3 * C ^ 2 * (2 * (Y : ℝ)) ^ (2 * ε) * (1 + Real.log (2 * (Y : ℝ))) *
      (6 / Real.sqrt B₀ + (1 + Real.log (2 * (Y : ℝ))) / K) ≤ σ ^ 2)
    (hM2 : 1 / (P : ℝ) + (3 + 4 * Λ) * 12 * P * C ^ 2 * (2 * (Y : ℝ)) ^ (2 * ε) * (1 + Real.log (2 * (Y : ℝ))) *
      (6 / (P₀ : ℝ) ^ 2 + (1 + Real.log ((P : ℝ) ^ 2 * (2 * Y))) * X) ≤ σ ^ 2) :
    ∑ p ∈ Ps, ‖ABsum n p y Y r t₁ t₂ (dblock i) (dblock j) (W1 ℓ n) (hInv (-4 * n) r)‖ ≤
      σ * ((P : ℝ) * W₀ * (4 * Y / P₀)) := by
  have hW0 := hW1.W₀_nonneg
  have hP : 0 < P := lt_of_lt_of_le hP₀ hP₀P
  have hRpos : 0 < R := lt_of_lt_of_le hr0 hrR
  have hB₀pos : 0 < B₀ := by omega
  have hRHS : 0 ≤ σ * ((P : ℝ) * W₀ * (4 * Y / P₀)) := by positivity
  obtain ⟨Ua, hUa⟩ : ∃ U, U = 2 ^ i := ⟨_, rfl⟩
  obtain ⟨Ub, hUb⟩ : ∃ U, U = 2 ^ j := ⟨_, rfl⟩
  have hdA : ∀ a ∈ dblock i, 0 < a ∧ a ≤ Ua ∧ Ua ≤ 2 * a := by rw [hUa]; exact dblock_props i
  have hdB : ∀ b ∈ dblock j, 0 < b ∧ b ≤ Ub ∧ Ub ≤ 2 * b := by rw [hUb]; exact dblock_props j
  -- empty below the range
  by_cases hlow : r * P * Ua * Ub ≤ y
  · refine le_trans (le_of_eq ?_) hRHS
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [ABsum_eq_zero_low n p y Y r t₁ t₂ _ _ _ _ Ua Ub (fun a ha => (hdA a ha).2.1)
      (fun b hb => (hdB b hb).2.1) (le_trans (by gcongr; exact (hPs p hp).2.2.2) hlow), norm_zero]
  push_neg at hlow
  -- empty above the range
  set La := max 1 (Ua / 2)
  set Lb := max 1 (Ub / 2)
  have hLa : ∀ a ∈ dblock i, La ≤ a := fun a ha => max_le (hdA a ha).1 (by have := (hdA a ha).2.2; omega)
  have hLb : ∀ b ∈ dblock j, Lb ≤ b := fun b hb => max_le (hdB b hb).1 (by have := (hdB b hb).2.2; omega)
  by_cases hhigh : Y < r * P₀ * La * Lb
  · refine le_trans (le_of_eq ?_) hRHS
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [ABsum_eq_zero_high n p y Y r t₁ t₂ _ _ _ _ La Lb hLa hLb
      (lt_of_lt_of_le hhigh (by gcongr; exact (hPs p hp).2.2.1)), norm_zero]
  push_neg at hhigh
  have hUaLa : Ua ≤ 2 * La := by
    have : Ua ≤ 2 * (Ua / 2) + 1 := by omega
    rcases Nat.lt_or_ge Ua 2 with h | h
    · have : Ua = 1 := by have := Nat.one_le_two_pow (n := i); omega
      omega
    · have : Ua % 2 = 0 := by
        have hi : i ≠ 0 := by rintro rfl; simp [hUa] at h
        rw [hUa]; obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi; simp [pow_succ]
      omega
  have hUbLb : Ub ≤ 2 * Lb := by
    rcases Nat.lt_or_ge Ub 2 with h | h
    · have : Ub = 1 := by have := Nat.one_le_two_pow (n := j); omega
      omega
    · have : Ub % 2 = 0 := by
        have hj : j ≠ 0 := by rintro rfl; simp [hUb] at h
        rw [hUb]; obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj; simp [pow_succ]
      omega
  have hUU : (Ua : ℝ) * Ub ≤ 4 * Y / P₀ := by
    have h1 : Ua * Ub ≤ 4 * (La * Lb) := by
      calc Ua * Ub ≤ (2 * La) * (2 * Lb) := Nat.mul_le_mul hUaLa hUbLb
        _ = 4 * (La * Lb) := by ring
    have h2 : P₀ * (La * Lb) ≤ Y := by
      calc P₀ * (La * Lb) = 1 * P₀ * La * Lb := by ring
        _ ≤ r * P₀ * La * Lb := by gcongr; omega
        _ ≤ Y := hhigh
    rw [le_div_iff₀ (by exact_mod_cast hP₀)]
    have : Ua * Ub * P₀ ≤ 4 * Y := by
      calc Ua * Ub * P₀ ≤ 4 * (La * Lb) * P₀ := Nat.mul_le_mul_right _ h1
        _ = 4 * (P₀ * (La * Lb)) := by ring
        _ ≤ 4 * Y := Nat.mul_le_mul_left _ h2
    exact_mod_cast this
  have hY0 : (0 : ℝ) ≤ Y := Nat.cast_nonneg _
  have hRr : (r : ℝ) ≤ R := by exact_mod_cast hrR
  by_cases hPVc : Ub ≤ B₀
  · ------------------------------------------------------------------ Pólya–Vinogradov
    have hUa_big : 2 * R * B₀ < Ua := by
      by_contra hc
      push_neg at hc
      have : r * P * Ua * Ub ≤ y := by
        calc r * P * Ua * Ub ≤ R * P * (2 * R * B₀) * B₀ := by gcongr
          _ = 2 * R ^ 2 * P * B₀ ^ 2 := by ring
          _ ≤ y := hPV1
      exact absurd this (not_le.mpr hlow)
    cases i with
    | zero => exfalso; simp at hUa; subst hUa; nlinarith
    | succ i' =>
      have hUa2 : Ua = 2 * 2 ^ i' := by rw [hUa, pow_succ]; ring
      have hrUA : r * Ub ≤ 2 ^ i' := by
        have : r * Ub ≤ R * B₀ := Nat.mul_le_mul hrR hPVc
        have h1 : 2 * (R * B₀) < 2 * 2 ^ i' := by rw [← hUa2, ← mul_assoc]; exact hUa_big
        omega
      have hpv := pv_num Ps P n r y Y t₁ t₂ (2 ^ i') Ub (dblock j) (W1 ℓ n) Wk1 hW1 hA1 (hInv (-4 * n) r) hn
        hn4 h8 hr0 hrs ht₁ hu₁ hn₀ (fun b hb => ⟨(hdB b hb).1, (hdB b hb).2.1⟩) hrUA
        (fun p hp => ⟨(hPs p hp).1.one_lt.le, (hPs p hp).2.2.2⟩) Λ hΛ
      rw [dblock_succ]
      refine hpv.trans ?_
      have hK0 : 0 ≤ (3 + 2 * Λ) * (Real.sqrt n * (1 + Real.log n)) := by
        have : 0 ≤ Real.log n := Real.log_nonneg (by
          have : 1 ≤ n := by omega
          exact_mod_cast this)
        positivity
      have hUbB : (Ub : ℝ) ^ 2 ≤ (B₀ : ℝ) ^ 2 := by
        have : (Ub : ℝ) ≤ B₀ := by exact_mod_cast hPVc
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
      calc (P : ℝ) * Ub ^ 2 * ((3 + 2 * Λ) * W₀ * (Real.sqrt n * (1 + Real.log n)))
          = (P * W₀) * (Ub ^ 2 * ((3 + 2 * Λ) * (Real.sqrt n * (1 + Real.log n)))) := by ring
        _ ≤ (P * W₀) * ((B₀ : ℝ) ^ 2 * ((3 + 2 * Λ) * (Real.sqrt n * (1 + Real.log n)))) := by
            gcongr
        _ ≤ (P * W₀) * (σ * (4 * Y / P₀)) := by gcongr
        _ = σ * ((P : ℝ) * W₀ * (4 * Y / P₀)) := by ring
  push_neg at hPVc
  have hUb_pos : 0 < Ub := by omega
  have hUa1 : 1 ≤ Ua := by rw [hUa]; exact Nat.one_le_two_pow
  have hLa1 : 1 ≤ La := le_max_left _ _
  have hLb1 : 1 ≤ Lb := le_max_left _ _
  have hLaY : La ≤ Y := by
    calc La = 1 * 1 * La * 1 := by ring
      _ ≤ r * P₀ * La * Lb := by gcongr <;> omega
      _ ≤ Y := hhigh
  have hLbY : Lb ≤ Y := by
    calc Lb = 1 * 1 * 1 * Lb := by ring
      _ ≤ r * P₀ * La * Lb := by gcongr <;> omega
      _ ≤ Y := hhigh
  have hUaY : Ua ≤ 2 * Y := by omega
  have hUbY : Ub ≤ 2 * Y := by omega
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hW0' : (0 : ℝ) ≤ P * W₀ := mul_nonneg (Nat.cast_nonneg _) hW0
  have hZ : 0 ≤ ∑ p ∈ Ps, ‖ABsum n p y Y r t₁ t₂ (dblock i) (dblock j) (W1 ℓ n) (hInv (-4 * n) r)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  by_cases hM1c : ∃ i', i = i' + 1 ∧ r ≤ 2 ^ i' ∧ (K : ℝ) * Real.sqrt Ub ≤ ((2 ^ i' : ℕ) : ℝ)
  · ------------------------------------------------------------------ Method 1
    obtain ⟨i', rfl, hrA, hKA⟩ := hM1c
    obtain ⟨A, hA⟩ : ∃ A, A = 2 ^ i' := ⟨_, rfl⟩
    rw [← hA] at hrA hKA
    have hUaA : Ua = 2 * A := by rw [hUa, hA, pow_succ]; ring
    have hm1 := m1_num Ps P n r y Y t₁ t₂ A Ub (dblock j) (W1 ℓ n) Wk1 hW1 hA1 (-4 * n) (Or.inr rfl)
      hr0 hrA ht₁ hrs hdB (fun p hp => ⟨(hPs p hp).1.one_lt.le, (hPs p hp).2.2.2⟩) hP C ε hC hε hτ Λ hΛ
      hUb_pos
    have hs := save_m1 (P : ℝ) (A : ℝ) (Ub : ℝ) (2 * (Y : ℝ)) (B₀ : ℝ) (K : ℝ) C ε Λ
      (by exact_mod_cast hP) (by exact_mod_cast (show 0 < A by omega)) (by exact_mod_cast hUb_pos)
      (by exact_mod_cast hUbY) (by exact_mod_cast hB₀pos) (by exact_mod_cast hPVc.le)
      (by exact_mod_cast hK) hKA hC hε hΛ0
    rw [dblock_succ i', ← hA] at hZ ⊢
    refine le_of_sq_le_sq_mul _ _ _ _ σ hZ (by positivity) hσ hm1 (hs.trans hM1) ?_
    have hAU : (A : ℝ) * Ub ≤ 4 * Y / P₀ := by
      refine le_trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)) hUU
      exact_mod_cast (show A ≤ Ua by omega)
    calc (P : ℝ) * A * Ub * W₀ = (P * W₀) * (A * Ub) := by ring
      _ ≤ (P * W₀) * (4 * Y / P₀) := mul_le_mul_of_nonneg_left hAU hW0'
      _ = P * W₀ * (4 * Y / P₀) := by ring
  · ------------------------------------------------------------------ Method 2
    push_neg at hM1c
    have hP0Y : 4 * (Y : ℝ) / P₀ ≤ 4 * Y := div_le_self (by positivity) (by exact_mod_cast hP₀)
    have hUaMax : (Ua : ℝ) ≤ Umax := by
      rcases i with _ | i'
      · have : Ua = 1 := by rw [hUa]; rfl
        rw [this]; push_cast; exact hU4
      · have hUa2 : Ua = 2 * 2 ^ i' := by rw [hUa, pow_succ]; ring
        by_cases hrA : r ≤ 2 ^ i'
        · have hlt := hM1c i' rfl hrA
          have hA0 : (0 : ℝ) ≤ ((2 ^ i' : ℕ) : ℝ) := Nat.cast_nonneg _
          have hUaR : (Ua : ℝ) = 2 * ((2 ^ i' : ℕ) : ℝ) := by rw [hUa2]; push_cast; ring
          have hsq : Real.sqrt Ub ^ 2 = Ub := Real.sq_sqrt (Nat.cast_nonneg _)
          have h1 : (Ua : ℝ) ^ 2 ≤ 4 * K ^ 2 * Ub := by
            have hm := mul_self_le_mul_self hA0 hlt.le
            have e : (K : ℝ) * Real.sqrt Ub * (K * Real.sqrt Ub) = K ^ 2 * Ub := by
              rw [show (K : ℝ) * Real.sqrt Ub * (K * Real.sqrt Ub) = K ^ 2 * Real.sqrt Ub ^ 2 by ring, hsq]
            rw [hUaR]
            calc (2 * ((2 ^ i' : ℕ) : ℝ)) ^ 2 = 4 * (((2 ^ i' : ℕ) : ℝ) * ((2 ^ i' : ℕ) : ℝ)) := by ring
              _ ≤ 4 * ((K : ℝ) * Real.sqrt Ub * (K * Real.sqrt Ub)) := by linarith
              _ = 4 * K ^ 2 * Ub := by rw [e]; ring
          have h2 : (Ua : ℝ) ^ 3 ≤ Umax ^ 3 := by
            have hUa0 : (0 : ℝ) ≤ Ua := Nat.cast_nonneg _
            calc (Ua : ℝ) ^ 3 = Ua ^ 2 * Ua := by ring
              _ ≤ (4 * (K : ℝ) ^ 2 * Ub) * Ua := mul_le_mul_of_nonneg_right h1 hUa0
              _ = 4 * (K : ℝ) ^ 2 * ((Ua : ℝ) * Ub) := by ring
              _ ≤ 4 * (K : ℝ) ^ 2 * (4 * (Y : ℝ) / P₀) :=
                  mul_le_mul_of_nonneg_left hUU (by positivity)
              _ = 16 * (K : ℝ) ^ 2 * Y / P₀ := by ring
              _ ≤ Umax ^ 3 := by
                  rw [div_le_iff₀ (by exact_mod_cast hP₀)]; exact hU2
          exact le_of_pow_le_pow_left₀ (by norm_num) (by linarith) h2
        · push_neg at hrA
          have : Ua < 2 * R := by omega
          calc (Ua : ℝ) ≤ 2 * R := by exact_mod_cast this.le
            _ ≤ Umax := hU1
    have hUaP₀ : ∀ a ∈ dblock i, a < P₀ := by
      intro a ha
      have : (a : ℝ) < P₀ := by
        have : (a : ℝ) ≤ Ua := by exact_mod_cast (hdA a ha).2.1
        linarith
      exact_mod_cast this
    rcases j with _ | j'
    · exfalso; have : Ub = 1 := by rw [hUb]; rfl
      omega
    obtain ⟨B, hB⟩ : ∃ B, B = 2 ^ j' := ⟨_, rfl⟩
    have hUbB : Ub = 2 * B := by rw [hUb, hB, pow_succ]; ring
    have hrB : r ≤ B := by omega
    have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hy' : (y : ℝ) < 2 * R * P * Ua * B := by
      have : y < 2 * R * P * Ua * B := by
        calc y < r * P * Ua * Ub := hlow
          _ ≤ R * P * Ua * (2 * B) := by rw [hUbB]; gcongr
          _ = 2 * R * P * Ua * B := by ring
      exact_mod_cast this
    have hk : 2 * (R : ℝ) * P * Ua * Real.sqrt Ua ≤ X * y := le_trans (by gcongr) hX
    have hX' : Real.sqrt Ua / B ≤ X := by
      rw [div_le_iff₀ hBpos]
      have hyp : (0 : ℝ) < y := by exact_mod_cast hy
      have hs0 := Real.sqrt_nonneg (Ua : ℝ)
      have : Real.sqrt Ua * y ≤ X * B * y := by
        calc Real.sqrt Ua * y ≤ Real.sqrt Ua * (2 * R * P * Ua * B) := mul_le_mul_of_nonneg_left hy'.le hs0
          _ = (2 * R * P * Ua * Real.sqrt Ua) * B := by ring
          _ ≤ (X * y) * B := mul_le_mul_of_nonneg_right hk hBpos.le
          _ = X * B * y := by ring
      exact le_of_mul_le_mul_right this hyp
    have hm2 := m2_num Ps P₀ P ℓ n r y Y t₁ t₂ B Ua (dblock i) Wk2 hW2 hA2 hP₀ hr0 hrB ht₂ hrs
      (fun a ha => ⟨(hdA a ha).1, hUaP₀ a ha, (hdA a ha).2.1, (hdA a ha).2.2⟩) hPs hP C ε hC hε hτ Λ hΛ
      (by omega)
    have hs := save_m2 (P : ℝ) (P₀ : ℝ) (B : ℝ) (Ua : ℝ) (2 * (Y : ℝ)) X C ε Λ hP1
      (by exact_mod_cast hP₀) hBpos (by exact_mod_cast hUa1) (by exact_mod_cast hUaY) hX' hC hε hΛ0
    rw [dblock_succ j', ← hB] at hZ ⊢
    refine le_of_sq_le_sq_mul _ _ _ _ σ hZ (by positivity) hσ hm2 (hs.trans hM2) ?_
    have hBU : (B : ℝ) * Ua ≤ 4 * Y / P₀ := by
      refine le_trans ?_ hUU
      rw [mul_comm (B : ℝ)]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show B ≤ Ub by omega)) (Nat.cast_nonneg _)
    calc (P : ℝ) * B * Ua * W₀ = (P * W₀) * (B * Ua) := by ring
      _ ≤ (P * W₀) * (4 * Y / P₀) := mul_le_mul_of_nonneg_left hBU hW0'
      _ = P * W₀ * (4 * Y / P₀) := by ring

open Classical in
/-- **The uniform block bound** (case `p ∣ b`). -/
theorem block_bound_B (Ps : Finset ℕ) (P₀ P ℓ n r y Y t₁ t₂ i j B₀ K R : ℕ) (Wk1 Wk2 : ℕ → ℂ)
    {W₀ W₁ : ℝ} (hW1 : SmoothW Wk1 W₀ W₁) (hW2 : SmoothW Wk2 W₀ W₁)
    (hA1 : ∀ c, y < c → c ≤ Y → W1 ℓ n c = Wk1 c) (hA2 : ∀ c, y < c → c ≤ Y → W2 ℓ n c = Wk2 c)
    (hn : Squarefree n) (hn4 : n % 4 = 3) (h8 : 8 ∣ r) (hr0 : 0 < r) (hrs : Smooth (S2 n) r)
    (ht₁ : t₁ < r) (ht₂ : t₂ < r) (hu₁ : IsUnit ((t₁ : ZMod r))) (hn₀ : 1 < n / Nat.gcd n r)
    (hPs : ∀ p ∈ Ps, p.Prime ∧ ¬ p ∣ 2 * n ∧ P₀ ≤ p ∧ p ≤ P) (hP₀ : 0 < P₀) (hP₀P : P₀ ≤ P)
    (C ε : ℝ) (hC : 0 < C) (hε : 0 ≤ ε)
    (hτ : ∀ m : ℕ, m ≠ 0 → ((m.divisors.card : ℕ) : ℝ) ≤ C * (m : ℝ) ^ ε)
    (Λ : ℝ) (hΛ0 : 0 ≤ Λ) (hΛ : W₁ ≤ Λ * W₀) (hrR : r ≤ R) (hK : 0 < K) (hB₀R : 2 * R ≤ B₀)
    (Umax X σ : ℝ) (hσ : 0 ≤ σ) (hU1 : 2 * (R : ℝ) ≤ Umax) (hU2 : 16 * (K : ℝ) ^ 2 * Y ≤ Umax ^ 3 * P₀)
    (hU3 : Umax < P₀) (hU4 : 1 ≤ Umax) (hy : 0 < y)
    (hX : 2 * (R : ℝ) * P * Umax * Real.sqrt Umax ≤ X * y)
    (hPV1 : 2 * R ^ 2 * P * B₀ ^ 2 ≤ y)
    (hPV2 : (B₀ : ℝ) ^ 2 * ((3 + 2 * Λ) * (Real.sqrt n * (1 + Real.log n))) ≤ σ * (4 * Y / P₀))
    (hM1 : 1 / (P : ℝ) + (3 + 4 * Λ) * 3 * C ^ 2 * (2 * (Y : ℝ)) ^ (2 * ε) * (1 + Real.log (2 * (Y : ℝ))) *
      (6 / Real.sqrt B₀ + (1 + Real.log (2 * (Y : ℝ))) / K) ≤ σ ^ 2)
    (hM2 : 1 / (P : ℝ) + (3 + 4 * Λ) * 12 * P * C ^ 2 * (2 * (Y : ℝ)) ^ (2 * ε) * (1 + Real.log (2 * (Y : ℝ))) *
      (6 / (P₀ : ℝ) ^ 2 + (1 + Real.log ((P : ℝ) ^ 2 * (2 * Y))) * X) ≤ σ ^ 2) :
    ∑ p ∈ Ps, ‖ABsum n p y Y r t₁ t₂ (dblock i) (dblock j) (W2 ℓ n) (hInv (4 * n) r)‖ ≤
      σ * ((P : ℝ) * W₀ * (4 * Y / P₀)) := by
  have hW0 := hW1.W₀_nonneg
  have hP : 0 < P := lt_of_lt_of_le hP₀ hP₀P
  have hRpos : 0 < R := lt_of_lt_of_le hr0 hrR
  have hB₀pos : 0 < B₀ := by omega
  have hRHS : 0 ≤ σ * ((P : ℝ) * W₀ * (4 * Y / P₀)) := by positivity
  obtain ⟨Ua, hUa⟩ : ∃ U, U = 2 ^ i := ⟨_, rfl⟩
  obtain ⟨Ub, hUb⟩ : ∃ U, U = 2 ^ j := ⟨_, rfl⟩
  have hdA : ∀ a ∈ dblock i, 0 < a ∧ a ≤ Ua ∧ Ua ≤ 2 * a := by rw [hUa]; exact dblock_props i
  have hdB : ∀ b ∈ dblock j, 0 < b ∧ b ≤ Ub ∧ Ub ≤ 2 * b := by rw [hUb]; exact dblock_props j
  -- empty below the range
  by_cases hlow : r * P * Ua * Ub ≤ y
  · refine le_trans (le_of_eq ?_) hRHS
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [ABsum_eq_zero_low n p y Y r t₁ t₂ _ _ _ _ Ua Ub (fun a ha => (hdA a ha).2.1)
      (fun b hb => (hdB b hb).2.1) (le_trans (by gcongr; exact (hPs p hp).2.2.2) hlow), norm_zero]
  push_neg at hlow
  -- empty above the range
  set La := max 1 (Ua / 2)
  set Lb := max 1 (Ub / 2)
  have hLa : ∀ a ∈ dblock i, La ≤ a := fun a ha => max_le (hdA a ha).1 (by have := (hdA a ha).2.2; omega)
  have hLb : ∀ b ∈ dblock j, Lb ≤ b := fun b hb => max_le (hdB b hb).1 (by have := (hdB b hb).2.2; omega)
  by_cases hhigh : Y < r * P₀ * La * Lb
  · refine le_trans (le_of_eq ?_) hRHS
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [ABsum_eq_zero_high n p y Y r t₁ t₂ _ _ _ _ La Lb hLa hLb
      (lt_of_lt_of_le hhigh (by gcongr; exact (hPs p hp).2.2.1)), norm_zero]
  push_neg at hhigh
  have hUaLa : Ua ≤ 2 * La := by
    have : Ua ≤ 2 * (Ua / 2) + 1 := by omega
    rcases Nat.lt_or_ge Ua 2 with h | h
    · have : Ua = 1 := by have := Nat.one_le_two_pow (n := i); omega
      omega
    · have : Ua % 2 = 0 := by
        have hi : i ≠ 0 := by rintro rfl; simp [hUa] at h
        rw [hUa]; obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi; simp [pow_succ]
      omega
  have hUbLb : Ub ≤ 2 * Lb := by
    rcases Nat.lt_or_ge Ub 2 with h | h
    · have : Ub = 1 := by have := Nat.one_le_two_pow (n := j); omega
      omega
    · have : Ub % 2 = 0 := by
        have hj : j ≠ 0 := by rintro rfl; simp [hUb] at h
        rw [hUb]; obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj; simp [pow_succ]
      omega
  have hUU : (Ua : ℝ) * Ub ≤ 4 * Y / P₀ := by
    have h1 : Ua * Ub ≤ 4 * (La * Lb) := by
      calc Ua * Ub ≤ (2 * La) * (2 * Lb) := Nat.mul_le_mul hUaLa hUbLb
        _ = 4 * (La * Lb) := by ring
    have h2 : P₀ * (La * Lb) ≤ Y := by
      calc P₀ * (La * Lb) = 1 * P₀ * La * Lb := by ring
        _ ≤ r * P₀ * La * Lb := by gcongr; omega
        _ ≤ Y := hhigh
    rw [le_div_iff₀ (by exact_mod_cast hP₀)]
    have : Ua * Ub * P₀ ≤ 4 * Y := by
      calc Ua * Ub * P₀ ≤ 4 * (La * Lb) * P₀ := Nat.mul_le_mul_right _ h1
        _ = 4 * (P₀ * (La * Lb)) := by ring
        _ ≤ 4 * Y := Nat.mul_le_mul_left _ h2
    exact_mod_cast this
  have hY0 : (0 : ℝ) ≤ Y := Nat.cast_nonneg _
  have hRr : (r : ℝ) ≤ R := by exact_mod_cast hrR
  by_cases hPVc : Ub ≤ B₀
  · ------------------------------------------------------------------ Pólya–Vinogradov
    have hUa_big : 2 * R * B₀ < Ua := by
      by_contra hc
      push_neg at hc
      have : r * P * Ua * Ub ≤ y := by
        calc r * P * Ua * Ub ≤ R * P * (2 * R * B₀) * B₀ := by gcongr
          _ = 2 * R ^ 2 * P * B₀ ^ 2 := by ring
          _ ≤ y := hPV1
      exact absurd this (not_le.mpr hlow)
    cases i with
    | zero => exfalso; simp at hUa; subst hUa; nlinarith
    | succ i' =>
      have hUa2 : Ua = 2 * 2 ^ i' := by rw [hUa, pow_succ]; ring
      have hrUA : r * Ub ≤ 2 ^ i' := by
        have : r * Ub ≤ R * B₀ := Nat.mul_le_mul hrR hPVc
        have h1 : 2 * (R * B₀) < 2 * 2 ^ i' := by rw [← hUa2, ← mul_assoc]; exact hUa_big
        omega
      have hpv := pv_num Ps P n r y Y t₁ t₂ (2 ^ i') Ub (dblock j) (W2 ℓ n) Wk2 hW2 hA2 (hInv (4 * n) r) hn
        hn4 h8 hr0 hrs ht₁ hu₁ hn₀ (fun b hb => ⟨(hdB b hb).1, (hdB b hb).2.1⟩) hrUA
        (fun p hp => ⟨(hPs p hp).1.one_lt.le, (hPs p hp).2.2.2⟩) Λ hΛ
      rw [dblock_succ]
      refine hpv.trans ?_
      have hK0 : 0 ≤ (3 + 2 * Λ) * (Real.sqrt n * (1 + Real.log n)) := by
        have : 0 ≤ Real.log n := Real.log_nonneg (by
          have : 1 ≤ n := by omega
          exact_mod_cast this)
        positivity
      have hUbB : (Ub : ℝ) ^ 2 ≤ (B₀ : ℝ) ^ 2 := by
        have : (Ub : ℝ) ≤ B₀ := by exact_mod_cast hPVc
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
      calc (P : ℝ) * Ub ^ 2 * ((3 + 2 * Λ) * W₀ * (Real.sqrt n * (1 + Real.log n)))
          = (P * W₀) * (Ub ^ 2 * ((3 + 2 * Λ) * (Real.sqrt n * (1 + Real.log n)))) := by ring
        _ ≤ (P * W₀) * ((B₀ : ℝ) ^ 2 * ((3 + 2 * Λ) * (Real.sqrt n * (1 + Real.log n)))) := by
            gcongr
        _ ≤ (P * W₀) * (σ * (4 * Y / P₀)) := by gcongr
        _ = σ * ((P : ℝ) * W₀ * (4 * Y / P₀)) := by ring
  push_neg at hPVc
  have hUb_pos : 0 < Ub := by omega
  have hUa1 : 1 ≤ Ua := by rw [hUa]; exact Nat.one_le_two_pow
  have hLa1 : 1 ≤ La := le_max_left _ _
  have hLb1 : 1 ≤ Lb := le_max_left _ _
  have hLaY : La ≤ Y := by
    calc La = 1 * 1 * La * 1 := by ring
      _ ≤ r * P₀ * La * Lb := by gcongr <;> omega
      _ ≤ Y := hhigh
  have hLbY : Lb ≤ Y := by
    calc Lb = 1 * 1 * 1 * Lb := by ring
      _ ≤ r * P₀ * La * Lb := by gcongr <;> omega
      _ ≤ Y := hhigh
  have hUaY : Ua ≤ 2 * Y := by omega
  have hUbY : Ub ≤ 2 * Y := by omega
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hW0' : (0 : ℝ) ≤ P * W₀ := mul_nonneg (Nat.cast_nonneg _) hW0
  have hZ : 0 ≤ ∑ p ∈ Ps, ‖ABsum n p y Y r t₁ t₂ (dblock i) (dblock j) (W2 ℓ n) (hInv (4 * n) r)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  by_cases hM1c : ∃ i', i = i' + 1 ∧ r ≤ 2 ^ i' ∧ (K : ℝ) * Real.sqrt Ub ≤ ((2 ^ i' : ℕ) : ℝ)
  · ------------------------------------------------------------------ Method 1
    obtain ⟨i', rfl, hrA, hKA⟩ := hM1c
    obtain ⟨A, hA⟩ : ∃ A, A = 2 ^ i' := ⟨_, rfl⟩
    rw [← hA] at hrA hKA
    have hUaA : Ua = 2 * A := by rw [hUa, hA, pow_succ]; ring
    have hm1 := m1_num Ps P n r y Y t₁ t₂ A Ub (dblock j) (W2 ℓ n) Wk2 hW2 hA2 (4 * n) (Or.inl rfl)
      hr0 hrA ht₁ hrs hdB (fun p hp => ⟨(hPs p hp).1.one_lt.le, (hPs p hp).2.2.2⟩) hP C ε hC hε hτ Λ hΛ
      hUb_pos
    have hs := save_m1 (P : ℝ) (A : ℝ) (Ub : ℝ) (2 * (Y : ℝ)) (B₀ : ℝ) (K : ℝ) C ε Λ
      (by exact_mod_cast hP) (by exact_mod_cast (show 0 < A by omega)) (by exact_mod_cast hUb_pos)
      (by exact_mod_cast hUbY) (by exact_mod_cast hB₀pos) (by exact_mod_cast hPVc.le)
      (by exact_mod_cast hK) hKA hC hε hΛ0
    rw [dblock_succ i', ← hA] at hZ ⊢
    refine le_of_sq_le_sq_mul _ _ _ _ σ hZ (by positivity) hσ hm1 (hs.trans hM1) ?_
    have hAU : (A : ℝ) * Ub ≤ 4 * Y / P₀ := by
      refine le_trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)) hUU
      exact_mod_cast (show A ≤ Ua by omega)
    calc (P : ℝ) * A * Ub * W₀ = (P * W₀) * (A * Ub) := by ring
      _ ≤ (P * W₀) * (4 * Y / P₀) := mul_le_mul_of_nonneg_left hAU hW0'
      _ = P * W₀ * (4 * Y / P₀) := by ring
  · ------------------------------------------------------------------ Method 2
    push_neg at hM1c
    have hP0Y : 4 * (Y : ℝ) / P₀ ≤ 4 * Y := div_le_self (by positivity) (by exact_mod_cast hP₀)
    have hUaMax : (Ua : ℝ) ≤ Umax := by
      rcases i with _ | i'
      · have : Ua = 1 := by rw [hUa]; rfl
        rw [this]; push_cast; exact hU4
      · have hUa2 : Ua = 2 * 2 ^ i' := by rw [hUa, pow_succ]; ring
        by_cases hrA : r ≤ 2 ^ i'
        · have hlt := hM1c i' rfl hrA
          have hA0 : (0 : ℝ) ≤ ((2 ^ i' : ℕ) : ℝ) := Nat.cast_nonneg _
          have hUaR : (Ua : ℝ) = 2 * ((2 ^ i' : ℕ) : ℝ) := by rw [hUa2]; push_cast; ring
          have hsq : Real.sqrt Ub ^ 2 = Ub := Real.sq_sqrt (Nat.cast_nonneg _)
          have h1 : (Ua : ℝ) ^ 2 ≤ 4 * K ^ 2 * Ub := by
            have hm := mul_self_le_mul_self hA0 hlt.le
            have e : (K : ℝ) * Real.sqrt Ub * (K * Real.sqrt Ub) = K ^ 2 * Ub := by
              rw [show (K : ℝ) * Real.sqrt Ub * (K * Real.sqrt Ub) = K ^ 2 * Real.sqrt Ub ^ 2 by ring, hsq]
            rw [hUaR]
            calc (2 * ((2 ^ i' : ℕ) : ℝ)) ^ 2 = 4 * (((2 ^ i' : ℕ) : ℝ) * ((2 ^ i' : ℕ) : ℝ)) := by ring
              _ ≤ 4 * ((K : ℝ) * Real.sqrt Ub * (K * Real.sqrt Ub)) := by linarith
              _ = 4 * K ^ 2 * Ub := by rw [e]; ring
          have h2 : (Ua : ℝ) ^ 3 ≤ Umax ^ 3 := by
            have hUa0 : (0 : ℝ) ≤ Ua := Nat.cast_nonneg _
            calc (Ua : ℝ) ^ 3 = Ua ^ 2 * Ua := by ring
              _ ≤ (4 * (K : ℝ) ^ 2 * Ub) * Ua := mul_le_mul_of_nonneg_right h1 hUa0
              _ = 4 * (K : ℝ) ^ 2 * ((Ua : ℝ) * Ub) := by ring
              _ ≤ 4 * (K : ℝ) ^ 2 * (4 * (Y : ℝ) / P₀) :=
                  mul_le_mul_of_nonneg_left hUU (by positivity)
              _ = 16 * (K : ℝ) ^ 2 * Y / P₀ := by ring
              _ ≤ Umax ^ 3 := by
                  rw [div_le_iff₀ (by exact_mod_cast hP₀)]; exact hU2
          exact le_of_pow_le_pow_left₀ (by norm_num) (by linarith) h2
        · push_neg at hrA
          have : Ua < 2 * R := by omega
          calc (Ua : ℝ) ≤ 2 * R := by exact_mod_cast this.le
            _ ≤ Umax := hU1
    have hUaP₀ : ∀ a ∈ dblock i, a < P₀ := by
      intro a ha
      have : (a : ℝ) < P₀ := by
        have : (a : ℝ) ≤ Ua := by exact_mod_cast (hdA a ha).2.1
        linarith
      exact_mod_cast this
    rcases j with _ | j'
    · exfalso; have : Ub = 1 := by rw [hUb]; rfl
      omega
    obtain ⟨B, hB⟩ : ∃ B, B = 2 ^ j' := ⟨_, rfl⟩
    have hUbB : Ub = 2 * B := by rw [hUb, hB, pow_succ]; ring
    have hrB : r ≤ B := by omega
    have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hy' : (y : ℝ) < 2 * R * P * Ua * B := by
      have : y < 2 * R * P * Ua * B := by
        calc y < r * P * Ua * Ub := hlow
          _ ≤ R * P * Ua * (2 * B) := by rw [hUbB]; gcongr
          _ = 2 * R * P * Ua * B := by ring
      exact_mod_cast this
    have hk : 2 * (R : ℝ) * P * Ua * Real.sqrt Ua ≤ X * y := le_trans (by gcongr) hX
    have hX' : Real.sqrt Ua / B ≤ X := by
      rw [div_le_iff₀ hBpos]
      have hyp : (0 : ℝ) < y := by exact_mod_cast hy
      have hs0 := Real.sqrt_nonneg (Ua : ℝ)
      have : Real.sqrt Ua * y ≤ X * B * y := by
        calc Real.sqrt Ua * y ≤ Real.sqrt Ua * (2 * R * P * Ua * B) := mul_le_mul_of_nonneg_left hy'.le hs0
          _ = (2 * R * P * Ua * Real.sqrt Ua) * B := by ring
          _ ≤ (X * y) * B := mul_le_mul_of_nonneg_right hk hBpos.le
          _ = X * B * y := by ring
      exact le_of_mul_le_mul_right this hyp
    have hm2 := m2_num' Ps P₀ P ℓ n r y Y t₁ t₂ B Ua (dblock i) Wk1 hW1 hA1 hP₀ hr0 hrB ht₂ hrs
      (fun a ha => ⟨(hdA a ha).1, hUaP₀ a ha, (hdA a ha).2.1, (hdA a ha).2.2⟩) hPs hP C ε hC hε hτ Λ hΛ
      (by omega)
    have hs := save_m2 (P : ℝ) (P₀ : ℝ) (B : ℝ) (Ua : ℝ) (2 * (Y : ℝ)) X C ε Λ hP1
      (by exact_mod_cast hP₀) hBpos (by exact_mod_cast hUa1) (by exact_mod_cast hUaY) hX' hC hε hΛ0
    rw [dblock_succ j', ← hB] at hZ ⊢
    refine le_of_sq_le_sq_mul _ _ _ _ σ hZ (by positivity) hσ hm2 (hs.trans hM2) ?_
    have hBU : (B : ℝ) * Ua ≤ 4 * Y / P₀ := by
      refine le_trans ?_ hUU
      rw [mul_comm (B : ℝ)]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show B ≤ Ub by omega)) (Nat.cast_nonneg _)
    calc (P : ℝ) * B * Ua * W₀ = (P * W₀) * (B * Ua) := by ring
      _ ≤ (P * W₀) * (4 * Y / P₀) := mul_le_mul_of_nonneg_left hBU hW0'
      _ = P * W₀ * (4 * Y / P₀) := by ring

end ThreeSquares
