/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.NumWeil

/-!
# Numeric forms of the block bounds

Each method gives `(∑_p ‖ABsum_p‖)² ≤ T² S` with the trivial scale `T = P · |I| · |J| · W₀` and an explicit
saving factor `S` (`m1_num`, `m2_num`, `m2_num'`); Pólya–Vinogradov gives a linear bound (`pv_num`).
-/

@[expose] public section

namespace ThreeSquares

open Finset

/-- The algebraic core of the conversion. -/
theorem num_combine (a b c A U P W₀ W₁ Λ Q S S₀ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (haA : a ≤ A) (hbU : b ≤ U) (hcP : c ≤ P) (hP : 0 < P) (hA : 0 < A) (hU : 0 < U) (hW₀ : 0 ≤ W₀)
    (hW₁ : 0 ≤ W₁) (hΛ : W₁ ≤ Λ * W₀) (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hSS : S ≤ S₀) :
    a * b * (c * b * a * W₀ ^ 2 + (3 * W₀ ^ 2 + 4 * W₀ * W₁) * Q * S) ≤
      (P * A * U * W₀) ^ 2 * (1 / P + (3 + 4 * Λ) * Q * S₀ / (P ^ 2 * A * U)) := by
  have hΛ0 : 0 ≤ (3 + 4 * Λ) * W₀ ^ 2 := by nlinarith [mul_nonneg hW₀ hW₁]
  have h1 : 3 * W₀ ^ 2 + 4 * W₀ * W₁ ≤ (3 + 4 * Λ) * W₀ ^ 2 := by nlinarith
  have h2 : c * b * a * W₀ ^ 2 ≤ P * U * A * W₀ ^ 2 := by
    have := mul_le_mul (mul_le_mul hcP hbU hb (by linarith)) haA ha (by positivity); nlinarith
  have h3 : (3 * W₀ ^ 2 + 4 * W₀ * W₁) * Q * S ≤ (3 + 4 * Λ) * W₀ ^ 2 * Q * S₀ := by
    have : 0 ≤ 3 * W₀ ^ 2 + 4 * W₀ * W₁ := by positivity
    calc (3 * W₀ ^ 2 + 4 * W₀ * W₁) * Q * S ≤ (3 + 4 * Λ) * W₀ ^ 2 * Q * S := by gcongr
      _ ≤ (3 + 4 * Λ) * W₀ ^ 2 * Q * S₀ := by gcongr
  have hin : 0 ≤ c * b * a * W₀ ^ 2 + (3 * W₀ ^ 2 + 4 * W₀ * W₁) * Q * S := by positivity
  calc a * b * (c * b * a * W₀ ^ 2 + (3 * W₀ ^ 2 + 4 * W₀ * W₁) * Q * S)
      ≤ A * U * (P * U * A * W₀ ^ 2 + (3 + 4 * Λ) * W₀ ^ 2 * Q * S₀) := by
        apply mul_le_mul (mul_le_mul haA hbU hb (by linarith)) (add_le_add h2 h3) hin (by positivity)
    _ = (P * A * U * W₀) ^ 2 * (1 / P + (3 + 4 * Λ) * Q * S₀ / (P ^ 2 * A * U)) := by
        field_simp

theorem card_filter_Ioc_le (A r t : ℕ) : (((Ioc A (2 * A)).filter (fun a => a % r = t)).card : ℝ) ≤ A := by
  have : ((Ioc A (2 * A)).filter (fun a => a % r = t)).card ≤ A := by
    calc _ ≤ (Ioc A (2 * A)).card := Finset.card_filter_le _ _
      _ = A := by simp; omega
  exact_mod_cast this

theorem card_le_of_subset_Icc (J : Finset ℕ) (U : ℕ) (hJ : ∀ b ∈ J, 0 < b ∧ b ≤ U) :
    (J.card : ℝ) ≤ U := by
  have : J.card ≤ U := by
    calc J.card ≤ (Icc 1 U).card := Finset.card_le_card fun b hb => Finset.mem_Icc.mpr (hJ b hb)
      _ = U := by simp
  exact_mod_cast this

theorem card_Ps_le (Ps : Finset ℕ) (P : ℕ) (hPs : ∀ p ∈ Ps, 1 ≤ p ∧ p ≤ P) : (Ps.card : ℝ) ≤ P :=
  card_le_of_subset_Icc Ps P fun p hp => ⟨(hPs p hp).1, (hPs p hp).2⟩

open Classical in
/-- **Method 1, numeric.** -/
theorem m1_num (Ps : Finset ℕ) (P n r y Y t₁ t₂ A U : ℕ) (J : Finset ℕ) (W W' : ℕ → ℂ) {W₀ W₁ : ℝ}
    (hW' : SmoothW W' W₀ W₁) (hWW : ∀ c, y < c → c ≤ Y → W c = W' c) (σ : ℤ)
    (hσ : σ = 4 * n ∨ σ = -4 * n) (hr : 0 < r) (hrA : r ≤ A) (ht₁ : t₁ < r) (hrs : Smooth (S2 n) r)
    (hJU : ∀ b ∈ J, 0 < b ∧ b ≤ U ∧ U ≤ 2 * b) (hPs : ∀ p ∈ Ps, 1 ≤ p ∧ p ≤ P) (hP : 0 < P)
    (C ε : ℝ) (hC : 0 < C) (hε : 0 ≤ ε)
    (hτ : ∀ m : ℕ, m ≠ 0 → ((m.divisors.card : ℕ) : ℝ) ≤ C * (m : ℝ) ^ ε)
    (Λ : ℝ) (hΛ : W₁ ≤ Λ * W₀) (hU : 0 < U) :
    (∑ p ∈ Ps, ‖ABsum n p y Y r t₁ t₂ (Ioc A (2 * A)) J W (hInv σ r)‖) ^ 2 ≤
      ((P : ℝ) * A * U * W₀) ^ 2 * (1 / P + (3 + 4 * Λ) * (P : ℝ) ^ 2 *
        ((6 * A / U + 1 + Real.log U) * (C ^ 2 * (U : ℝ) ^ (2 * ε) * Real.sqrt U) * (3 * U * (1 + Real.log U))) /
          ((P : ℝ) ^ 2 * A * U)) := by
  have hA : 1 ≤ A := le_trans hr hrA
  have hW0 := hW'.W₀_nonneg
  have hW1 := hW'.W₁_nonneg
  refine (m1_block Ps P n r y Y t₁ t₂ A J W W' hW' hWW σ hσ hr hrA ht₁ hrs
    (fun b hb => (hJU b hb).1) hPs).trans ?_
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg (by exact_mod_cast hU)
  apply num_combine _ _ _ _ _ _ _ _ _ _ _ _ (by positivity) (by positivity) (by positivity)
    (card_filter_Ioc_le A r _)
    ((card_le_of_subset_Icc _ U fun b hb => ⟨(hJU b (Finset.mem_filter.mp hb).1).1,
      (hJU b (Finset.mem_filter.mp hb).1).2.1⟩)) (card_Ps_le Ps P hPs) (by exact_mod_cast hP) hApos hUpos
    hW0 hW1 hΛ (by positivity)
  · refine Finset.sum_nonneg fun b hb => ?_
    have hb0 := (hJU b (Finset.mem_filter.mp hb).1).1
    have : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast hb0)
    positivity
  · refine sum_weil_le _ U (fun b hb => ⟨(hJU b (Finset.mem_filter.mp hb).1).1,
      (hJU b (Finset.mem_filter.mp hb).1).2.1⟩) _ _ (fun b hb => ?_) (by positivity) C ε hC hε hτ
    obtain ⟨hb0, hbU, hUb⟩ := hJU b (Finset.mem_filter.mp hb).1
    have hbpos : (0 : ℝ) < b := by exact_mod_cast hb0
    have hlogb : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast hb0)
    refine ⟨by positivity, ?_⟩
    have hM : (((2 * A / r + 1 : ℕ) : ℝ)) ≤ 3 * A := by
      have : 2 * A / r + 1 ≤ 3 * A := by
        have := Nat.div_le_self (2 * A) r; omega
      exact_mod_cast this
    have hb2 : (U : ℝ) ≤ 2 * b := by exact_mod_cast hUb
    have h1 : (((2 * A / r + 1 : ℕ) : ℝ)) / b ≤ 6 * A / U := by
      rw [div_le_div_iff₀ hbpos hUpos]; nlinarith
    have h2 : Real.log b ≤ Real.log U := Real.log_le_log hbpos (by exact_mod_cast hbU)
    linarith

open Classical in
/-- **Method 2, numeric** (case `p ∣ a`). -/
theorem m2_num (Ps : Finset ℕ) (P₀ P ℓ n r y Y t₁ t₂ B U : ℕ) (I : Finset ℕ) (W2' : ℕ → ℂ) {W₀ W₁ : ℝ}
    (hW' : SmoothW W2' W₀ W₁) (hWW : ∀ c, y < c → c ≤ Y → W2 ℓ n c = W2' c) (hP₀ : 0 < P₀)
    (hr : 0 < r) (hrB : r ≤ B) (ht₂ : t₂ < r) (hrs : Smooth (S2 n) r)
    (hIU : ∀ a ∈ I, 0 < a ∧ a < P₀ ∧ a ≤ U ∧ U ≤ 2 * a)
    (hPs : ∀ p ∈ Ps, p.Prime ∧ ¬ p ∣ 2 * n ∧ P₀ ≤ p ∧ p ≤ P) (hP : 0 < P)
    (C ε : ℝ) (hC : 0 < C) (hε : 0 ≤ ε)
    (hτ : ∀ m : ℕ, m ≠ 0 → ((m.divisors.card : ℕ) : ℝ) ≤ C * (m : ℝ) ^ ε)
    (Λ : ℝ) (hΛ : W₁ ≤ Λ * W₀) (hU : 0 < U) :
    (∑ p ∈ Ps, ‖ABsum n p y Y r t₁ t₂ I (Ioc B (2 * B)) (W1 ℓ n) (hInv (-4 * n) r)‖) ^ 2 ≤
      ((P : ℝ) * B * U * W₀) ^ 2 * (1 / P + (3 + 4 * Λ) * (4 * (P : ℝ) ^ 3) *
        ((6 * B / ((P₀ : ℝ) ^ 2 * U) + 1 + Real.log ((P : ℝ) ^ 2 * U)) *
          (C ^ 2 * (U : ℝ) ^ (2 * ε) * Real.sqrt U) * (3 * U * (1 + Real.log U))) /
          ((P : ℝ) ^ 2 * B * U)) := by
  have hB : 1 ≤ B := le_trans hr hrB
  have hW0 := hW'.W₀_nonneg
  have hW1 := hW'.W₁_nonneg
  refine (m2_block Ps P₀ P ℓ n r y Y t₁ t₂ B I W2' hW' hWW hP₀ hr hrB ht₂ hrs
    (fun a ha => ⟨(hIU a ha).1, (hIU a ha).2.1⟩) hPs).trans ?_
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
  have hP0pos : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hlogPU : 0 ≤ Real.log ((P : ℝ) ^ 2 * U) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ U := by exact_mod_cast hU
    nlinarith)
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg (by exact_mod_cast hU)
  apply num_combine _ _ _ _ _ _ _ _ _ _ _ _ (by positivity) (by positivity) (by positivity)
    (card_filter_Ioc_le B r _)
    ((card_le_of_subset_Icc _ U fun a ha => ⟨(hIU a (Finset.mem_filter.mp ha).1).1,
      (hIU a (Finset.mem_filter.mp ha).1).2.2.1⟩))
    (card_Ps_le Ps P fun p hp => ⟨(hPs p hp).1.one_lt.le, (hPs p hp).2.2.2⟩) hPpos hBpos hUpos
    hW0 hW1 hΛ (by positivity)
  · refine Finset.sum_nonneg fun a ha => ?_
    have ha0 := (hIU a (Finset.mem_filter.mp ha).1).1
    have : 0 ≤ Real.log ((P : ℝ) ^ 2 * a) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ a := by exact_mod_cast ha0
      nlinarith)
    positivity
  · refine sum_weil_le _ U (fun a ha => ⟨(hIU a (Finset.mem_filter.mp ha).1).1,
      (hIU a (Finset.mem_filter.mp ha).1).2.2.1⟩) _ _ (fun a ha => ?_) (by positivity) C ε hC hε hτ
    obtain ⟨ha0, -, haU, hUa⟩ := hIU a (Finset.mem_filter.mp ha).1
    have hapos : (0 : ℝ) < a := by exact_mod_cast ha0
    have hloga : 0 ≤ Real.log ((P : ℝ) ^ 2 * a) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ a := by exact_mod_cast ha0
      nlinarith)
    refine ⟨by positivity, ?_⟩
    have hM : (((2 * B / r + 1 : ℕ) : ℝ)) ≤ 3 * B := by
      have : 2 * B / r + 1 ≤ 3 * B := by
        have := Nat.div_le_self (2 * B) r; omega
      exact_mod_cast this
    have ha2 : (U : ℝ) ≤ 2 * a := by exact_mod_cast hUa
    have h1 : (((2 * B / r + 1 : ℕ) : ℝ)) / ((P₀ : ℝ) ^ 2 * a) ≤ 6 * B / ((P₀ : ℝ) ^ 2 * U) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hP02 : (0 : ℝ) < (P₀ : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left ha2 hP02.le, mul_le_mul_of_nonneg_left hM (mul_nonneg hP02.le hUpos.le)]
    have h2 : Real.log ((P : ℝ) ^ 2 * a) ≤ Real.log ((P : ℝ) ^ 2 * U) :=
      Real.log_le_log (by positivity) (by
        have : (a : ℝ) ≤ U := by exact_mod_cast haU
        nlinarith)
    linarith

open Classical in
/-- **Method 2, numeric** (mirror). -/
theorem m2_num' (Ps : Finset ℕ) (P₀ P ℓ n r y Y t₁ t₂ B U : ℕ) (I : Finset ℕ) (W2' : ℕ → ℂ) {W₀ W₁ : ℝ}
    (hW' : SmoothW W2' W₀ W₁) (hWW : ∀ c, y < c → c ≤ Y → W1 ℓ n c = W2' c) (hP₀ : 0 < P₀)
    (hr : 0 < r) (hrB : r ≤ B) (ht₂ : t₂ < r) (hrs : Smooth (S2 n) r)
    (hIU : ∀ a ∈ I, 0 < a ∧ a < P₀ ∧ a ≤ U ∧ U ≤ 2 * a)
    (hPs : ∀ p ∈ Ps, p.Prime ∧ ¬ p ∣ 2 * n ∧ P₀ ≤ p ∧ p ≤ P) (hP : 0 < P)
    (C ε : ℝ) (hC : 0 < C) (hε : 0 ≤ ε)
    (hτ : ∀ m : ℕ, m ≠ 0 → ((m.divisors.card : ℕ) : ℝ) ≤ C * (m : ℝ) ^ ε)
    (Λ : ℝ) (hΛ : W₁ ≤ Λ * W₀) (hU : 0 < U) :
    (∑ p ∈ Ps, ‖ABsum n p y Y r t₁ t₂ I (Ioc B (2 * B)) (W2 ℓ n) (hInv (4 * n) r)‖) ^ 2 ≤
      ((P : ℝ) * B * U * W₀) ^ 2 * (1 / P + (3 + 4 * Λ) * (4 * (P : ℝ) ^ 3) *
        ((6 * B / ((P₀ : ℝ) ^ 2 * U) + 1 + Real.log ((P : ℝ) ^ 2 * U)) *
          (C ^ 2 * (U : ℝ) ^ (2 * ε) * Real.sqrt U) * (3 * U * (1 + Real.log U))) /
          ((P : ℝ) ^ 2 * B * U)) := by
  have hB : 1 ≤ B := le_trans hr hrB
  have hW0 := hW'.W₀_nonneg
  have hW1 := hW'.W₁_nonneg
  refine (m2_block' Ps P₀ P ℓ n r y Y t₁ t₂ B I W2' hW' hWW hP₀ hr hrB ht₂ hrs
    (fun a ha => ⟨(hIU a ha).1, (hIU a ha).2.1⟩) hPs).trans ?_
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hPpos : (0 : ℝ) < P := by exact_mod_cast hP
  have hP0pos : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hlogPU : 0 ≤ Real.log ((P : ℝ) ^ 2 * U) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ U := by exact_mod_cast hU
    nlinarith)
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg (by exact_mod_cast hU)
  apply num_combine _ _ _ _ _ _ _ _ _ _ _ _ (by positivity) (by positivity) (by positivity)
    (card_filter_Ioc_le B r _)
    ((card_le_of_subset_Icc _ U fun a ha => ⟨(hIU a (Finset.mem_filter.mp ha).1).1,
      (hIU a (Finset.mem_filter.mp ha).1).2.2.1⟩))
    (card_Ps_le Ps P fun p hp => ⟨(hPs p hp).1.one_lt.le, (hPs p hp).2.2.2⟩) hPpos hBpos hUpos
    hW0 hW1 hΛ (by positivity)
  · refine Finset.sum_nonneg fun a ha => ?_
    have ha0 := (hIU a (Finset.mem_filter.mp ha).1).1
    have : 0 ≤ Real.log ((P : ℝ) ^ 2 * a) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ a := by exact_mod_cast ha0
      nlinarith)
    positivity
  · refine sum_weil_le _ U (fun a ha => ⟨(hIU a (Finset.mem_filter.mp ha).1).1,
      (hIU a (Finset.mem_filter.mp ha).1).2.2.1⟩) _ _ (fun a ha => ?_) (by positivity) C ε hC hε hτ
    obtain ⟨ha0, -, haU, hUa⟩ := hIU a (Finset.mem_filter.mp ha).1
    have hapos : (0 : ℝ) < a := by exact_mod_cast ha0
    have hloga : 0 ≤ Real.log ((P : ℝ) ^ 2 * a) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ a := by exact_mod_cast ha0
      nlinarith)
    refine ⟨by positivity, ?_⟩
    have hM : (((2 * B / r + 1 : ℕ) : ℝ)) ≤ 3 * B := by
      have : 2 * B / r + 1 ≤ 3 * B := by
        have := Nat.div_le_self (2 * B) r; omega
      exact_mod_cast this
    have ha2 : (U : ℝ) ≤ 2 * a := by exact_mod_cast hUa
    have h1 : (((2 * B / r + 1 : ℕ) : ℝ)) / ((P₀ : ℝ) ^ 2 * a) ≤ 6 * B / ((P₀ : ℝ) ^ 2 * U) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hP02 : (0 : ℝ) < (P₀ : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left ha2 hP02.le, mul_le_mul_of_nonneg_left hM (mul_nonneg hP02.le hUpos.le)]
    have h2 : Real.log ((P : ℝ) ^ 2 * a) ≤ Real.log ((P : ℝ) ^ 2 * U) :=
      Real.log_le_log (by positivity) (by
        have : (a : ℝ) ≤ U := by exact_mod_cast haU
        nlinarith)
    linarith

open Classical in
/-- **Pólya–Vinogradov, numeric.** -/
theorem pv_num (Ps : Finset ℕ) (P n r y Y t₁ t₂ A U : ℕ) (J : Finset ℕ) (W W' : ℕ → ℂ) {W₀ W₁ : ℝ}
    (hW' : SmoothW W' W₀ W₁) (hWW : ∀ c, y < c → c ≤ Y → W c = W' c) (h : ℕ → ℤ) (hn : Squarefree n)
    (hn4 : n % 4 = 3) (h8 : 8 ∣ r) (hr0 : 0 < r) (hrs : Smooth (S2 n) r) (ht₁ : t₁ < r)
    (hu₁ : IsUnit ((t₁ : ZMod r))) (hn₀ : 1 < n / Nat.gcd n r) (hJ : ∀ b ∈ J, 0 < b ∧ b ≤ U)
    (hrUA : r * U ≤ A) (hPs : ∀ p ∈ Ps, 1 ≤ p ∧ p ≤ P) (Λ : ℝ) (hΛ : W₁ ≤ Λ * W₀) :
    ∑ p ∈ Ps, ‖ABsum n p y Y r t₁ t₂ (Ioc A (2 * A)) J W h‖ ≤
      (P : ℝ) * U ^ 2 * ((3 + 2 * Λ) * W₀ * (Real.sqrt n * (1 + Real.log n))) := by
  have hW0 := hW'.W₀_nonneg
  have hW1 := hW'.W₁_nonneg
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn4
  refine (pv_block' Ps n r y Y t₁ t₂ A J W W' hW' hWW h hn hn4 h8 hr0 hrs ht₁ hu₁ hn₀
    (fun b hb => ⟨(hJ b hb).1, le_trans (Nat.mul_le_mul_left r (hJ b hb).2) hrUA⟩)
    (fun p hp => (hPs p hp).1)).trans ?_
  set n₀ := n / Nat.gcd n r
  have hn₀n : n₀ ≤ n := Nat.div_le_self _ _
  have hK : (3 * W₀ + 2 * W₁) * (Real.sqrt n₀ * (1 + Real.log n₀)) ≤
      (3 + 2 * Λ) * W₀ * (Real.sqrt n * (1 + Real.log n)) := by
    have h1 : 3 * W₀ + 2 * W₁ ≤ (3 + 2 * Λ) * W₀ := by nlinarith
    have hn₀pos : (0 : ℝ) < n₀ := by exact_mod_cast (by omega : 0 < n₀)
    have h2 : Real.sqrt n₀ ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hn₀n)
    have h3 : Real.log n₀ ≤ Real.log n := Real.log_le_log hn₀pos (by exact_mod_cast hn₀n)
    have h4 : 0 ≤ Real.log n₀ := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n₀))
    have h5 : 0 ≤ (3 + 2 * Λ) * W₀ := by nlinarith
    have h6 : 0 ≤ 3 * W₀ + 2 * W₁ := by positivity
    exact mul_le_mul h1 (mul_le_mul h2 (by linarith) (by positivity) (Real.sqrt_nonneg _)) (by positivity) h5
  calc ∑ p ∈ Ps, ∑ b ∈ J.filter (fun b => b % r = t₂ ∧ Rough (S2 n) b),
        (b : ℝ) * ((3 * W₀ + 2 * W₁) * (Real.sqrt n₀ * (1 + Real.log n₀)))
      ≤ ∑ p ∈ Ps, ∑ b ∈ J.filter (fun b => b % r = t₂ ∧ Rough (S2 n) b),
          (U : ℝ) * ((3 + 2 * Λ) * W₀ * (Real.sqrt n * (1 + Real.log n))) := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun b hb => ?_
        have hbU : (b : ℝ) ≤ U := by exact_mod_cast (hJ b (Finset.mem_filter.mp hb).1).2
        have h4 : 0 ≤ Real.log (n / Nat.gcd n r : ℕ) :=
          Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n / Nat.gcd n r))
        exact mul_le_mul hbU hK (by positivity) (Nat.cast_nonneg _)
    _ ≤ (P : ℝ) * U ^ 2 * ((3 + 2 * Λ) * W₀ * (Real.sqrt n * (1 + Real.log n))) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hc1 := card_Ps_le Ps P hPs
        have hc2 : (((J.filter (fun b => b % r = t₂ ∧ Rough (S2 n) b)).card : ℕ) : ℝ) ≤ U :=
          card_le_of_subset_Icc _ U fun b hb => hJ b (Finset.mem_filter.mp hb).1
        have hX : 0 ≤ (U : ℝ) * ((3 + 2 * Λ) * W₀ * (Real.sqrt n * (1 + Real.log n))) := by
          have : 0 ≤ (3 + 2 * Λ) * W₀ := by nlinarith
          have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0)
          positivity
        calc (Ps.card : ℝ) * (((J.filter _).card : ℝ) * ((U : ℝ) * ((3 + 2 * Λ) * W₀ *
              (Real.sqrt n * (1 + Real.log n)))))
            ≤ (P : ℝ) * ((U : ℝ) * ((U : ℝ) * ((3 + 2 * Λ) * W₀ * (Real.sqrt n * (1 + Real.log n))))) := by
              gcongr
          _ = _ := by ring

end ThreeSquares
