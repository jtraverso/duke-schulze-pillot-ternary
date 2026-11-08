/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.GCD
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Binary quadratic forms and reduction

* `Form`: `a x² + b x y + c y²`; `Form.act f p q r s` is `f ∘ [[p, q], [r, s]]`.
* `Form.exists_reduce`: every positive definite form of discriminant `−n` is properly
  (`ps − qr = 1`) equivalent to a reduced one (`|b| ≤ a ≤ c`). Only existence is proved; reduced
  representatives need not be unique, which the lower bound arguments of B3 never need.
* `Red n`: the finite set of reduced forms of discriminant `−n`, `mem_Red`.
* `Form.min_le_eval`: a reduced form satisfies `a (x² − |xy| + y²) ≤ f(x, y)`.
-/

@[expose] public section

namespace ThreeSquares.B3

/-- The binary quadratic form `a x² + b x y + c y²`. -/
@[ext] structure Form where
  /-- coefficient of `x²` -/
  a : ℤ
  /-- coefficient of `x y` -/
  b : ℤ
  /-- coefficient of `y²` -/
  c : ℤ
deriving DecidableEq

namespace Form

/-- `f(x, y)`. -/
def eval (f : Form) (x y : ℤ) : ℤ := f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2

/-- The discriminant `b² − 4ac`. -/
def disc (f : Form) : ℤ := f.b ^ 2 - 4 * f.a * f.c

/-- `f ∘ γ` for `γ = [[p, q], [r, s]]`. -/
def act (f : Form) (p q r s : ℤ) : Form :=
  ⟨f.eval p r, 2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s, f.eval q s⟩

theorem eval_act (f : Form) (p q r s x y : ℤ) :
    (f.act p q r s).eval x y = f.eval (p * x + q * y) (r * x + s * y) := by
  simp only [eval, act]
  ring

theorem disc_act (f : Form) (p q r s : ℤ) :
    (f.act p q r s).disc = (p * s - q * r) ^ 2 * f.disc := by
  simp only [disc, act, eval]
  ring

theorem act_act (f : Form) (p q r s p' q' r' s' : ℤ) :
    (f.act p q r s).act p' q' r' s' =
      f.act (p * p' + q * r') (p * q' + q * s') (r * p' + s * r') (r * q' + s * s') := by
  ext <;> simp only [act, eval] <;> ring

theorem eval_neg (f : Form) (x y : ℤ) : f.eval (-x) (-y) = f.eval x y := by
  simp only [eval]
  ring

theorem eval_smul (f : Form) (t x y : ℤ) : f.eval (t * x) (t * y) = t ^ 2 * f.eval x y := by
  simp only [eval]
  ring

/-- `4a f(x, y) = (2ax + by)² − disc · y²`. -/
theorem four_a_eval (f : Form) (x y : ℤ) :
    4 * f.a * f.eval x y = (2 * f.a * x + f.b * y) ^ 2 - f.disc * y ^ 2 := by
  simp only [eval, disc]
  ring

/-- Reduced: `|b| ≤ a ≤ c`. -/
def IsReduced (f : Form) : Prop := |f.b| ≤ f.a ∧ f.a ≤ f.c

/-- A positive definite form of discriminant `−n` has `c > 0`. -/
theorem c_pos {f : Form} {n : ℤ} (hn : 0 < n) (ha : 0 < f.a) (hd : f.disc = -n) : 0 < f.c := by
  unfold disc at hd
  by_contra h
  push Not at h
  have : f.a * f.c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le h
  nlinarith [sq_nonneg f.b]

/-- **Reduction** (existence). -/
theorem exists_reduce {n : ℤ} (hn : 0 < n) :
    ∀ (k : ℕ) (f : Form), f.a.toNat ≤ k → 0 < f.a → f.disc = -n →
      ∃ p q r s : ℤ, p * s - q * r = 1 ∧ (f.act p q r s).IsReduced := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro f hk ha hd
  set t : ℤ := (f.a - f.b) / (2 * f.a) with ht
  set g : Form := f.act 1 t 0 1 with hg
  have hga : g.a = f.a := by simp [hg, act, eval]
  have hgb : g.b = f.a - (f.a - f.b) % (2 * f.a) := by
    have := Int.emod_add_mul_ediv (f.a - f.b) (2 * f.a)
    simp only [hg, act, eval]
    rw [← ht] at this
    linarith
  have hgd : g.disc = -n := by rw [hg, disc_act]; simpa using hd
  have h2a : 0 < 2 * f.a := by linarith
  have hm0 := Int.emod_nonneg (f.a - f.b) h2a.ne'
  have hm1 := Int.emod_lt_of_pos (f.a - f.b) h2a
  have hgb' : |g.b| ≤ g.a := by
    rw [abs_le, hga, hgb]
    constructor <;> linarith
  by_cases hac : g.a ≤ g.c
  · exact ⟨1, t, 0, 1, by ring, hgb', hac⟩
  · push Not at hac
    have hgc : 0 < g.c := c_pos hn (by rw [hga]; exact ha) hgd
    set h : Form := g.act 0 (-1) 1 0 with hh
    have hha : h.a = g.c := by simp [hh, act, eval]
    have hhd : h.disc = -n := by rw [hh, disc_act]; simpa using hgd
    have hlt : h.a.toNat < k := by
      have : h.a.toNat < f.a.toNat := by
        rw [hha]
        have := hac
        rw [hga] at this
        omega
      omega
    obtain ⟨p, q, r, s, hdet, hred⟩ :=
      ih h.a.toNat hlt h le_rfl (by rw [hha]; exact hgc) hhd
    rw [hh, hg, act_act, act_act] at hred
    refine ⟨_, _, _, _, ?_, hred⟩
    linear_combination hdet

/-- A reduced positive form satisfies `a (x² − |xy| + y²) ≤ f(x, y)`. -/
theorem min_le_eval {f : Form} (hf : f.IsReduced) (x y : ℤ) :
    f.a * (x ^ 2 - |x * y| + y ^ 2) ≤ f.eval x y := by
  obtain ⟨hb, hac⟩ := hf
  have ha : 0 ≤ f.a := le_trans (abs_nonneg _) hb
  have h1 : -(f.a * |x * y|) ≤ f.b * x * y := by
    have : |f.b * (x * y)| ≤ f.a * |x * y| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    have := neg_abs_le (f.b * (x * y))
    rw [mul_assoc]
    linarith
  have h2 : f.a * y ^ 2 ≤ f.c * y ^ 2 := mul_le_mul_of_nonneg_right hac (sq_nonneg y)
  simp only [eval]
  nlinarith

theorem quad_ge_one {x y : ℤ} (h : x ≠ 0 ∨ y ≠ 0) : 1 ≤ x ^ 2 - |x * y| + y ^ 2 := by
  rw [abs_mul]
  rcases le_total |x| |y| with hxy | hxy
  · have hy : 1 ≤ |y| := by
      rcases h with h | h
      · have := abs_pos.mpr h
        omega
      · exact abs_pos.mpr h
    have e1 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    have e2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
    nlinarith [abs_nonneg x]
  · have hx : 1 ≤ |x| := by
      rcases h with h | h
      · exact abs_pos.mpr h
      · have := abs_pos.mpr h
        omega
    have e1 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    have e2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
    nlinarith [abs_nonneg y]

theorem quad_nonneg (x y : ℤ) : 0 ≤ x ^ 2 - |x * y| + y ^ 2 := by
  by_cases h : x = 0 ∧ y = 0
  · simp [h.1, h.2]
  · have := quad_ge_one (not_and_or.mp h)
    linarith

theorem abs_le_one_of_quad_le_one {x y : ℤ} (h : x ^ 2 - |x * y| + y ^ 2 ≤ 1) :
    |x| ≤ 1 ∧ |y| ≤ 1 := by
  rw [abs_mul] at h
  have e1 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have e2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  have hx0 := abs_nonneg x
  have hy0 := abs_nonneg y
  constructor
  · by_contra hc
    push Not at hc
    nlinarith [sq_nonneg (2 * |y| - |x|)]
  · by_contra hc
    push Not at hc
    nlinarith [sq_nonneg (2 * |x| - |y|)]

/-- A reduced form satisfies `x² + y² ≤ 2 f(x, y)` when `a ≥ 1`. -/
theorem sq_add_sq_le {f : Form} (hf : f.IsReduced) (ha : 1 ≤ f.a) (x y : ℤ) :
    x ^ 2 + y ^ 2 ≤ 2 * f.eval x y := by
  have h := min_le_eval hf x y
  have hq := quad_nonneg x y
  have h2 : 2 * |x * y| ≤ x ^ 2 + y ^ 2 := by
    rw [abs_mul]
    have e1 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    have e2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
    nlinarith [sq_nonneg (|x| - |y|)]
  nlinarith

end Form

open Form

/-- The reduced forms of discriminant `−n`. -/
def Red (n : ℕ) : Finset Form :=
  ((Finset.Icc (1 : ℤ) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (1 : ℤ) n).filter
    (fun u : ℤ × ℤ × ℤ => u.2.1 ^ 2 - 4 * u.1 * u.2.2 = -n ∧ |u.2.1| ≤ u.1 ∧ u.1 ≤ u.2.2)).image
    (fun u : ℤ × ℤ × ℤ => (⟨u.1, u.2.1, u.2.2⟩ : Form))

theorem mem_Red {n : ℕ} {f : Form} :
    f ∈ Red n ↔ f.disc = -n ∧ f.IsReduced ∧ 0 < f.a := by
  constructor
  · intro h
    simp only [Red, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc] at h
    obtain ⟨⟨a, b, c⟩, ⟨⟨⟨ha1, _⟩, _, _⟩, hd, hb, hac⟩, rfl⟩ := h
    exact ⟨hd, ⟨hb, hac⟩, show 0 < a by omega⟩
  · rintro ⟨hd, ⟨hb, hac⟩, ha⟩
    have hd' := hd
    unfold disc at hd'
    have hb2 : f.b ^ 2 ≤ f.a ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have han : f.a ≤ n := by nlinarith
    have hcn : f.c ≤ n := by nlinarith
    rw [abs_le] at hb
    simp only [Red, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨(f.a, f.b, f.c), ⟨⟨?_, ?_, ?_⟩, hd', abs_le.mpr hb, hac⟩, rfl⟩
    · exact ⟨by omega, han⟩
    · exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
    · exact ⟨by linarith, hcn⟩

end ThreeSquares.B3
