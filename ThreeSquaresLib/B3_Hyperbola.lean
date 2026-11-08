/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.B3_Char

/-!
# Dirichlet's hyperbola method

`conv a b M = ∑_{m ≤ M} ∑_{e ∣ m} a(e) b(m/e)`.
* `conv_eq`: `conv a b M = ∑_{e ≤ M} a(e) B(M/e)` (`B = psum b`).
* `conv_split`: for `y ≤ M`,
  `conv a b M = ∑_{e ≤ y} a(e) B(M/e) + ∑_{l ≤ M/(y+1)} b(l) (A(M/l) − A(y))`.
* `norm_conv_le`: if `|a|, |b| ≤ 1` and `|A|, |B| ≤ K`, then `‖conv a b M‖ ≤ 3K √M`.
* `norm_conv_sub_le`: if moreover `B(x) = (x/n) P + O(2n)` with `|P| ≤ n`, then
  `conv a b M = (P/n) M ∑_{e ≤ √M} a(e)/e + O((1 + 2n + 2K) √M)`.
-/

@[expose] public section

namespace ThreeSquares.B3

open Finset

/-- `∑_{m ≤ M} (a * b)(m)`. -/
noncomputable def conv (a b : ℕ → ℂ) (M : ℕ) : ℂ :=
  ∑ m ∈ Ioc 0 M, ∑ e ∈ m.divisors, a e * b (m / e)

theorem conv_eq (a b : ℕ → ℂ) (M : ℕ) : conv a b M = ∑ e ∈ Ioc 0 M, a e * psum b (M / e) := by
  unfold conv
  rw [sum_comm' (t' := Ioc 0 M) (s' := fun e => (Ioc 0 M).filter (e ∣ ·))]
  · refine sum_congr rfl fun e he => ?_
    rw [mem_Ioc] at he
    unfold psum
    rw [mul_sum]
    refine sum_nbij' (fun m => m / e) (fun l => e * l) ?_ ?_ ?_ ?_ ?_
    · intro m hm
      simp only [mem_filter, mem_Ioc] at hm
      simp only [mem_Ioc]
      obtain ⟨⟨hm0, hmM⟩, hdvd⟩ := hm
      exact ⟨Nat.div_pos (Nat.le_of_dvd hm0 hdvd) he.1, Nat.div_le_div_right hmM⟩
    · intro l hl
      simp only [mem_Ioc] at hl
      simp only [mem_filter, mem_Ioc]
      refine ⟨⟨Nat.mul_pos he.1 hl.1, ?_⟩, dvd_mul_right _ _⟩
      calc e * l ≤ e * (M / e) := Nat.mul_le_mul_left _ hl.2
        _ ≤ M := Nat.mul_div_le M e
    · intro m hm
      simp only [mem_filter, mem_Ioc] at hm
      exact Nat.mul_div_cancel' hm.2
    · intro l _
      exact Nat.mul_div_cancel_left l he.1
    · intro m _
      rfl
  · intro m e
    simp only [mem_Ioc, Nat.mem_divisors, mem_filter]
    constructor
    · rintro ⟨⟨hm0, hmM⟩, hdvd, -⟩
      exact ⟨⟨⟨hm0, hmM⟩, hdvd⟩, Nat.pos_of_dvd_of_pos hdvd hm0,
        le_trans (Nat.le_of_dvd hm0 hdvd) hmM⟩
    · rintro ⟨⟨⟨hm0, hmM⟩, hdvd⟩, -, -⟩
      exact ⟨⟨hm0, hmM⟩, hdvd, by omega⟩

theorem tail_eq (a b : ℕ → ℂ) {M y : ℕ} (hy : y ≤ M) :
    ∑ e ∈ Ioc y M, a e * psum b (M / e) =
      ∑ l ∈ Ioc 0 (M / (y + 1)), b l * (psum a (M / l) - psum a y) := by
  unfold psum
  simp_rw [mul_sum]
  rw [sum_comm' (t' := Ioc 0 (M / (y + 1))) (s' := fun l => Ioc y (M / l))]
  · refine sum_congr rfl fun l hl => ?_
    rw [mem_Ioc] at hl
    have hyl : y ≤ M / l := by
      have h1 := Nat.mul_le_of_le_div _ _ _ hl.2
      rw [Nat.le_div_iff_mul_le hl.1]
      nlinarith
    rw [← sum_Ioc_consecutive _ (Nat.zero_le y) hyl, add_sub_cancel_left, mul_sum]
    refine sum_congr rfl fun e _ => ?_
    ring
  · intro e l
    simp only [mem_Ioc]
    constructor
    · rintro ⟨⟨hye, heM⟩, hl0, hlM⟩
      have he : 0 < e := by omega
      have h1 : l * e ≤ M := (Nat.le_div_iff_mul_le he).mp hlM
      refine ⟨⟨hye, (Nat.le_div_iff_mul_le hl0).mpr (by linarith)⟩, hl0, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega)]
      nlinarith
    · rintro ⟨⟨hye, heM⟩, hl0, hlM⟩
      have h1 : e * l ≤ M := (Nat.le_div_iff_mul_le hl0).mp heM
      refine ⟨⟨hye, by nlinarith⟩, hl0, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega)]
      linarith

theorem conv_split (a b : ℕ → ℂ) {M y : ℕ} (hy : y ≤ M) :
    conv a b M = ∑ e ∈ Ioc 0 y, a e * psum b (M / e) +
      ∑ l ∈ Ioc 0 (M / (y + 1)), b l * (psum a (M / l) - psum a y) := by
  rw [conv_eq, ← sum_Ioc_consecutive _ (Nat.zero_le y) hy, tail_eq a b hy]

theorem div_sqrt_succ_le (M : ℕ) : M / (Nat.sqrt M + 1) ≤ Nat.sqrt M := by
  have h := Nat.lt_succ_sqrt M
  have : M / (Nat.sqrt M + 1) < Nat.sqrt M + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    simpa [Nat.succ_eq_add_one] using h
  omega

theorem norm_sum_Ioc_le {f : ℕ → ℂ} {K : ℝ} (hf : ∀ k, ‖f k‖ ≤ K) (y : ℕ) :
    ‖∑ k ∈ Ioc 0 y, f k‖ ≤ y * K := by
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (sum_le_sum fun k _ => hf k) ?_
  simp

theorem norm_tail_le {a b : ℕ → ℂ} (hb : ∀ k, ‖b k‖ ≤ 1) {K : ℝ} (hA : ∀ x, ‖psum a x‖ ≤ K)
    (M y : ℕ) :
    ‖∑ l ∈ Ioc 0 (M / (y + 1)), b l * (psum a (M / l) - psum a y)‖ ≤
      (M / (y + 1) : ℕ) * (2 * K) := by
  refine norm_sum_Ioc_le (fun l => ?_) _
  rw [norm_mul]
  have h1 := hb l
  have h2 : ‖psum a (M / l) - psum a y‖ ≤ 2 * K :=
    le_trans (norm_sub_le _ _) (by linarith [hA (M / l), hA y])
  have hK : 0 ≤ K := le_trans (norm_nonneg _) (hA 0)
  calc ‖b l‖ * ‖psum a (M / l) - psum a y‖ ≤ 1 * (2 * K) :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 2 * K := one_mul _

theorem norm_conv_le {a b : ℕ → ℂ} (ha : ∀ k, ‖a k‖ ≤ 1) (hb : ∀ k, ‖b k‖ ≤ 1) {K : ℝ}
    (hA : ∀ x, ‖psum a x‖ ≤ K) (hB : ∀ x, ‖psum b x‖ ≤ K) (M : ℕ) :
    ‖conv a b M‖ ≤ 3 * K * Nat.sqrt M := by
  have hK : 0 ≤ K := le_trans (norm_nonneg _) (hA 0)
  rw [conv_split a b (Nat.sqrt_le_self M)]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖∑ e ∈ Ioc 0 (Nat.sqrt M), a e * psum b (M / e)‖ ≤ Nat.sqrt M * K := by
    refine norm_sum_Ioc_le (fun e => ?_) _
    rw [norm_mul]
    calc ‖a e‖ * ‖psum b (M / e)‖ ≤ 1 * K := mul_le_mul (ha e) (hB _) (norm_nonneg _) zero_le_one
      _ = K := one_mul K
  have h2 := norm_tail_le hb hA M (Nat.sqrt M)
  have h3 : ((M / (Nat.sqrt M + 1) : ℕ) : ℝ) ≤ Nat.sqrt M := by exact_mod_cast div_sqrt_succ_le M
  have h4 : ((M / (Nat.sqrt M + 1) : ℕ) : ℝ) * (2 * K) ≤ Nat.sqrt M * (2 * K) :=
    mul_le_mul_of_nonneg_right h3 (by linarith)
  nlinarith

theorem norm_conv_sub_le {n : ℕ} (hn : 0 < n) {a b : ℕ → ℂ} (ha : ∀ k, ‖a k‖ ≤ 1)
    (hb : ∀ k, ‖b k‖ ≤ 1) {K : ℝ} (hA : ∀ x, ‖psum a x‖ ≤ K) {P : ℂ} (hP : ‖P‖ ≤ n)
    (hB : ∀ x, ‖psum b x - (x / n : ℂ) * P‖ ≤ 2 * n) (M : ℕ) :
    ‖conv a b M - P / n * M * ∑ e ∈ Ioc 0 (Nat.sqrt M), a e / e‖ ≤
      (1 + 2 * n + 2 * K) * Nat.sqrt M := by
  have hK : 0 ≤ K := le_trans (norm_nonneg _) (hA 0)
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [conv_split a b (Nat.sqrt_le_self M)]
  set y := Nat.sqrt M
  have e1 : ∑ e ∈ Ioc 0 y, a e * psum b (M / e) - P / n * M * ∑ e ∈ Ioc 0 y, a e / e =
      ∑ e ∈ Ioc 0 y, (a e * (psum b (M / e) - ((M / e : ℕ) / n : ℂ) * P) +
        a e * (P / n) * (((M / e : ℕ) : ℂ) - (M : ℂ) / e)) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun e he => ?_
    rw [mem_Ioc] at he
    have : (e : ℂ) ≠ 0 := by exact_mod_cast he.1.ne'
    field_simp
    ring
  have h1 : ‖∑ e ∈ Ioc 0 y, (a e * (psum b (M / e) - ((M / e : ℕ) / n : ℂ) * P) +
        a e * (P / n) * (((M / e : ℕ) : ℂ) - (M : ℂ) / e))‖ ≤ y * (2 * n + 1) := by
    refine norm_sum_Ioc_le (fun e => ?_) _
    refine le_trans (norm_add_le _ _) ?_
    have t1 : ‖a e * (psum b (M / e) - ((M / e : ℕ) / n : ℂ) * P)‖ ≤ 2 * n := by
      rw [norm_mul]
      calc ‖a e‖ * ‖psum b (M / e) - ((M / e : ℕ) / n : ℂ) * P‖ ≤ 1 * (2 * n) :=
            mul_le_mul (ha e) (hB _) (norm_nonneg _) zero_le_one
        _ = 2 * n := one_mul _
    have t2 : ‖a e * (P / n) * (((M / e : ℕ) : ℂ) - (M : ℂ) / e)‖ ≤ 1 := by
      rcases Nat.eq_zero_or_pos e with he | he
      · subst he; simp
      have hfl : ‖(((M / e : ℕ) : ℂ) - (M : ℂ) / e)‖ ≤ 1 := by
        have : (((M / e : ℕ) : ℂ) - (M : ℂ) / e) = ((((M / e : ℕ) : ℝ) - (M : ℝ) / e : ℝ) : ℂ) := by
          push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
        have he' : (0 : ℝ) < e := by exact_mod_cast he
        have hle : ((M / e : ℕ) : ℝ) ≤ (M : ℝ) / e := Nat.cast_div_le
        have hgt : (M : ℝ) / e - 1 < ((M / e : ℕ) : ℝ) := by
          rw [div_sub_one he'.ne', div_lt_iff₀ he']
          have := Nat.lt_div_mul_add (a := M) he
          have : (M : ℝ) < ((M / e : ℕ) : ℝ) * e + e := by exact_mod_cast this
          linarith
        constructor <;> linarith
      have hPn : ‖P / n‖ ≤ 1 := by
        rw [norm_div, Complex.norm_natCast, div_le_one (by exact_mod_cast hn)]
        exact hP
      rw [norm_mul, norm_mul]
      calc ‖a e‖ * ‖P / n‖ * ‖(((M / e : ℕ) : ℂ) - (M : ℂ) / e)‖ ≤ 1 * 1 * 1 := by
            gcongr
            · exact ha e
        _ = 1 := by ring
    linarith
  have h2 := norm_tail_le hb hA M y
  have h3 : ((M / (y + 1) : ℕ) : ℝ) ≤ y := by exact_mod_cast div_sqrt_succ_le M
  have h4 : ((M / (y + 1) : ℕ) : ℝ) * (2 * K) ≤ y * (2 * K) :=
    mul_le_mul_of_nonneg_right h3 (by linarith)
  have e2 : ∑ e ∈ Ioc 0 y, a e * psum b (M / e) +
      ∑ l ∈ Ioc 0 (M / (y + 1)), b l * (psum a (M / l) - psum a y) -
        P / n * M * ∑ e ∈ Ioc 0 y, a e / e =
      (∑ e ∈ Ioc 0 y, a e * psum b (M / e) - P / n * M * ∑ e ∈ Ioc 0 y, a e / e) +
        ∑ l ∈ Ioc 0 (M / (y + 1)), b l * (psum a (M / l) - psum a y) := by ring
  rw [e2, e1]
  refine le_trans (norm_add_le _ _) ?_
  nlinarith

end ThreeSquares.B3
