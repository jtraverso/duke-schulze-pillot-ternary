/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.WeylAvg

/-!
# A small calculus of power bounds

`PowLe f a`: eventually `0 ≤ f n ≤ C n^a`. Closed under products, sums, maxima, square roots, real powers,
monotone in the exponent; `1 + log n` is `PowLe` for every positive exponent. `PowLe.eventually_le`:
`PowLe f a`, `a < b` ⇒ eventually `f n ≤ n^b`.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open Real

/-- Eventually `0 ≤ f n ≤ C n^a`. -/
def PowLe (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → 0 ≤ f n ∧ f n ≤ C * (n : ℝ) ^ a

namespace PowLe

theorem of_le {f g : ℕ → ℝ} {a : ℝ} (hg : PowLe g a) (N₁ : ℕ)
    (h : ∀ n, N₁ ≤ n → 0 ≤ f n ∧ f n ≤ g n) : PowLe f a := by
  obtain ⟨C, N₀, hC⟩ := hg
  exact ⟨C, max N₀ N₁, fun n hn => ⟨(h n (le_of_max_le_right hn)).1,
    (h n (le_of_max_le_right hn)).2.trans (hC n (le_of_max_le_left hn)).2⟩⟩

theorem const (c : ℝ) (hc : 0 ≤ c) : PowLe (fun _ => c) 0 :=
  ⟨c, 0, fun n _ => ⟨hc, by simp⟩⟩

theorem self (a : ℝ) : PowLe (fun n => (n : ℝ) ^ a) a :=
  ⟨1, 0, fun n _ => ⟨by positivity, by simp⟩⟩

theorem mul {f g : ℕ → ℝ} {a b : ℝ} (hf : PowLe f a) (hg : PowLe g b) :
    PowLe (fun n => f n * g n) (a + b) := by
  obtain ⟨C₁, N₁, h₁⟩ := hf
  obtain ⟨C₂, N₂, h₂⟩ := hg
  refine ⟨C₁ * C₂, max 1 (max N₁ N₂), fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_left hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨a0, a1⟩ := h₁ n (le_trans (le_max_left _ _) (le_of_max_le_right hn))
  obtain ⟨b0, b1⟩ := h₂ n (le_trans (le_max_right _ _) (le_of_max_le_right hn))
  refine ⟨mul_nonneg a0 b0, ?_⟩
  have hC2 : 0 ≤ C₂ * (n : ℝ) ^ b := b0.trans b1
  calc f n * g n ≤ (C₁ * (n : ℝ) ^ a) * (C₂ * (n : ℝ) ^ b) := mul_le_mul a1 b1 b0 (a0.trans a1)
    _ = C₁ * C₂ * (n : ℝ) ^ (a + b) := by rw [Real.rpow_add hnR]; ring

theorem mono {f : ℕ → ℝ} {a b : ℝ} (hf : PowLe f a) (hab : a ≤ b) : PowLe f b := by
  obtain ⟨C, N₀, h⟩ := hf
  refine ⟨max C 0, max 1 N₀, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
  obtain ⟨h0, h1⟩ := h n (le_of_max_le_right hn)
  refine ⟨h0, h1.trans ?_⟩
  calc C * (n : ℝ) ^ a ≤ max C 0 * (n : ℝ) ^ a := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (n : ℝ) ^ b :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hab) (le_max_right _ _)

theorem add {f g : ℕ → ℝ} {a : ℝ} (hf : PowLe f a) (hg : PowLe g a) :
    PowLe (fun n => f n + g n) a := by
  obtain ⟨C₁, N₁, h₁⟩ := hf
  obtain ⟨C₂, N₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, max N₁ N₂, fun n hn => ?_⟩
  obtain ⟨a0, a1⟩ := h₁ n (le_of_max_le_left hn)
  obtain ⟨b0, b1⟩ := h₂ n (le_of_max_le_right hn)
  exact ⟨add_nonneg a0 b0, by linarith⟩

theorem max' {f g : ℕ → ℝ} {a : ℝ} (hf : PowLe f a) (hg : PowLe g a) :
    PowLe (fun n => max (f n) (g n)) a := by
  obtain ⟨C₁, N₁, h₁⟩ := hf
  obtain ⟨C₂, N₂, h₂⟩ := hg
  refine ⟨C₁ + C₂, max N₁ N₂, fun n hn => ?_⟩
  obtain ⟨a0, a1⟩ := h₁ n (le_of_max_le_left hn)
  obtain ⟨b0, b1⟩ := h₂ n (le_of_max_le_right hn)
  refine ⟨le_max_of_le_left a0, max_le ?_ ?_⟩
  · have : 0 ≤ C₂ * (n : ℝ) ^ a := b0.trans b1
    linarith
  · have : 0 ≤ C₁ * (n : ℝ) ^ a := a0.trans a1
    linarith

theorem cmul {f : ℕ → ℝ} {a : ℝ} (hf : PowLe f a) (c : ℝ) (hc : 0 ≤ c) : PowLe (fun n => c * f n) a := by
  have := (const c hc).mul hf
  simpa using this

theorem sqrt {f : ℕ → ℝ} {a : ℝ} (hf : PowLe f a) : PowLe (fun n => Real.sqrt (f n)) (a / 2) := by
  obtain ⟨C, N₀, h⟩ := hf
  refine ⟨Real.sqrt (max C 0), max 1 N₀, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨h0, h1⟩ := h n (le_of_max_le_right hn)
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  calc Real.sqrt (f n) ≤ Real.sqrt (max C 0 * (n : ℝ) ^ a) :=
        Real.sqrt_le_sqrt (h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
    _ = Real.sqrt (max C 0) * (n : ℝ) ^ (a / 2) := by
        rw [Real.sqrt_mul (le_max_right _ _), Real.sqrt_eq_rpow ((n : ℝ) ^ a), ← Real.rpow_mul hn0]
        ring_nf

theorem log_add_one (θ : ℝ) (hθ : 0 < θ) : PowLe (fun n => 1 + Real.log n) θ := by
  refine ⟨1 + 1 / θ, 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hl := Real.log_le_rpow_div (Nat.cast_nonneg n) hθ
  have hp : 1 ≤ (n : ℝ) ^ θ := Real.one_le_rpow hn1 hθ.le
  refine ⟨by linarith, ?_⟩
  have : Real.log n ≤ 1 / θ * (n : ℝ) ^ θ := by rw [div_eq_mul_inv] at hl; rw [one_div]; linarith
  nlinarith

/-- **Absorbing the constant.** -/
theorem eventually_le {f : ℕ → ℝ} {a b : ℝ} (hf : PowLe f a) (hab : a < b) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → f n ≤ (n : ℝ) ^ b := by
  obtain ⟨C, N₀, h⟩ := hf
  set C' := max C 1
  obtain ⟨M, hM⟩ := exists_nat_ge (C' ^ (1 / (b - a)))
  refine ⟨max 1 (max N₀ M), fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
  have hnR : (0 : ℝ) < n := by linarith
  have hnM : (M : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) (le_of_max_le_right hn)
  obtain ⟨h0, h1⟩ := h n (le_trans (le_max_left _ _) (le_of_max_le_right hn))
  have hC' : 1 ≤ C' := le_max_right _ _
  have hba : 0 < b - a := by linarith
  have key : C' ≤ (n : ℝ) ^ (b - a) := by
    have : C' = (C' ^ (1 / (b - a))) ^ (b - a) := by
      rw [← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hba.ne', Real.rpow_one]
    rw [this]
    exact Real.rpow_le_rpow (by positivity) (hM.trans hnM) hba.le
  calc f n ≤ C * (n : ℝ) ^ a := h1
    _ ≤ C' * (n : ℝ) ^ a := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ (n : ℝ) ^ (b - a) * (n : ℝ) ^ a := mul_le_mul_of_nonneg_right key (by positivity)
    _ = (n : ℝ) ^ b := by rw [← Real.rpow_add hnR]; ring_nf

theorem rpow' {f : ℕ → ℝ} {a : ℝ} (hf : PowLe f a) (c : ℝ) (hc : 0 ≤ c) :
    PowLe (fun n => f n ^ c) (a * c) := by
  obtain ⟨C, N₀, h⟩ := hf
  refine ⟨(max C 0) ^ c, N₀, fun n hn => ?_⟩
  obtain ⟨h0, h1⟩ := h n hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨Real.rpow_nonneg h0 _, ?_⟩
  calc f n ^ c ≤ (max C 0 * (n : ℝ) ^ a) ^ c :=
        Real.rpow_le_rpow h0 (h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))) hc
    _ = (max C 0) ^ c * (n : ℝ) ^ (a * c) := by
        rw [Real.mul_rpow (le_max_right _ _) (by positivity), ← Real.rpow_mul hn0]

theorem inv_of_ge {f : ℕ → ℝ} (c a : ℝ) (hc : 0 < c) (N₀ : ℕ)
    (h : ∀ n, N₀ ≤ n → c * (n : ℝ) ^ a ≤ f n) : PowLe (fun n => 1 / f n) (-a) := by
  refine ⟨1 / c, max 1 N₀, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
  have hnR : (0 : ℝ) < n := by linarith
  have hpos : 0 < c * (n : ℝ) ^ a := by positivity
  have hf := h n (le_of_max_le_right hn)
  have hf0 : 0 < f n := lt_of_lt_of_le hpos hf
  refine ⟨by positivity, ?_⟩
  rw [Real.rpow_neg hnR.le, div_le_iff₀ hf0]
  calc (1 : ℝ) = 1 / c * ((n : ℝ) ^ a)⁻¹ * (c * (n : ℝ) ^ a) := by field_simp
    _ ≤ 1 / c * ((n : ℝ) ^ a)⁻¹ * f n := mul_le_mul_of_nonneg_left hf (by positivity)

end PowLe

theorem floor_ge_half (x : ℝ) (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 := Nat.lt_floor_add_one x
  have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.one_le_floor_iff x |>.mpr hx
  linarith

theorem PowLe.floor_rpow (a : ℝ) (ha : 0 ≤ a) : PowLe (fun n => ((⌊(n : ℝ) ^ a⌋₊ : ℕ) : ℝ)) a :=
  (PowLe.self a).of_le 0 fun n _ => ⟨Nat.cast_nonneg _, Nat.floor_le (by positivity)⟩

theorem floor_rpow_ge (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : 1 ≤ n) :
    (1 / 2) * (n : ℝ) ^ a ≤ ((⌊(n : ℝ) ^ a⌋₊ : ℕ) : ℝ) := by
  have := floor_ge_half ((n : ℝ) ^ a) (Real.one_le_rpow (by exact_mod_cast hn) ha)
  linarith

theorem floor_rpow_pos (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : 1 ≤ n) : 1 ≤ ⌊(n : ℝ) ^ a⌋₊ :=
  Nat.one_le_floor_iff _ |>.mpr (Real.one_le_rpow (by exact_mod_cast hn) ha)

end ThreeSquares
