/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.B3_Forms
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Roots of `b² ≡ −n (mod 4m)` and representations by reduced forms

For `m ≥ 1` and `4m ∣ b² + n`, the form `gform n m b = (m, b, (b² + n)/4m)` has discriminant `−n`;
reducing it (`Form.exists_reduce`) gives `rootRep n m b = (f, v)` with `f ∈ Red n`, `f(v) = m` and
`v` primitive (`rootRep_mem`, `rootRep_eval`, `rootRep_coprime`).
* `rootRep_inj`: on `0 ≤ b < 2m`, `b ↦ rootRep n m b` is injective (if two reductions give the
  same `(f, v)`, the two forms `(m, b₁, ·)`, `(m, b₂, ·)` differ by `[[1, t], [0, 1]]`, so
  `b₂ = b₁ + 2mt`).
* `smul_coprime_inj`: the content `g` of `g • v` (`v` primitive) is determined.
* `Good n f`: `∃ r s, n ∣ 2 f(r, s) + 1`; `good_of_rep`: a form representing `m` with
  `n ∣ 2t²m + 1` is good.
-/

@[expose] public section

namespace ThreeSquares.B3

open Form

theorem Form.act_one (f : Form) : f.act 1 0 0 1 = f := by
  ext <;> simp [act, eval]

/-- A positive definite form of discriminant `−n` is positive away from `0`. -/
theorem Form.eval_pos {f : Form} {n : ℤ} (hn : 0 < n) (ha : 0 < f.a) (hd : f.disc = -n)
    {x y : ℤ} (hxy : x ≠ 0 ∨ y ≠ 0) : 0 < f.eval x y := by
  have h := four_a_eval f x y
  rw [hd] at h
  have hpos : 0 < (2 * f.a * x + f.b * y) ^ 2 + n * y ^ 2 := by
    by_cases hy : y = 0
    · subst hy
      have hx : x ≠ 0 := by tauto
      have : 0 < (2 * f.a * x) ^ 2 := by positivity
      simpa using this
    · have : 0 < n * y ^ 2 := by positivity
      nlinarith [sq_nonneg (2 * f.a * x + f.b * y)]
  have h4 : 0 < 4 * f.a := by linarith
  by_contra hc
  push Not at hc
  nlinarith

/-- `(m, b, (b² + n)/4m)`. -/
def gform (n m : ℕ) (b : ℤ) : Form := ⟨m, b, (b ^ 2 + n) / (4 * m)⟩

theorem gform_disc {n m : ℕ} {b : ℤ} (hm : 0 < m) (hb : (4 * m : ℤ) ∣ b ^ 2 + n) :
    (gform n m b).disc = -n := by
  obtain ⟨k, hk⟩ := hb
  have : (b ^ 2 + n) / (4 * m) = k := by
    rw [hk]; exact Int.mul_ediv_cancel_left _ (by omega)
  simp only [Form.disc, gform, this]
  linarith

theorem exists_root_red {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {b : ℤ}
    (hb : (4 * m : ℤ) ∣ b ^ 2 + n) :
    ∃ γ : ℤ × ℤ × ℤ × ℤ, γ.1 * γ.2.2.2 - γ.2.1 * γ.2.2.1 = 1 ∧
      (gform n m b).act γ.1 γ.2.1 γ.2.2.1 γ.2.2.2 ∈ Red n := by
  have hd := gform_disc hm hb
  obtain ⟨p, q, r, s, hdet, hred⟩ := Form.exists_reduce (n := (n : ℤ)) (by omega) _
    (gform n m b) le_rfl (by simp [gform]; omega) hd
  refine ⟨(p, q, r, s), hdet, mem_Red.mpr ⟨?_, hred, ?_⟩⟩
  · rw [Form.disc_act, hdet, hd]; ring
  · have hpr : p ≠ 0 ∨ r ≠ 0 := by
      by_contra hc
      push Not at hc
      rw [hc.1, hc.2] at hdet
      simp at hdet
    exact Form.eval_pos (n := n) (by omega) (by simp [gform]; omega) hd hpr

/-- The reducing matrix chosen for the root `b`. -/
noncomputable def rootGamma (n m : ℕ) (b : ℤ) : ℤ × ℤ × ℤ × ℤ :=
  if h : 0 < n ∧ 0 < m ∧ (4 * m : ℤ) ∣ b ^ 2 + n then
    Classical.choose (exists_root_red h.1 h.2.1 h.2.2)
  else (1, 0, 0, 1)

/-- The reduced form and the primitive vector attached to the root `b`. -/
noncomputable def rootRep (n m : ℕ) (b : ℤ) : Form × ℤ × ℤ :=
  ((gform n m b).act (rootGamma n m b).1 (rootGamma n m b).2.1 (rootGamma n m b).2.2.1
    (rootGamma n m b).2.2.2, ((rootGamma n m b).2.2.2, -(rootGamma n m b).2.2.1))

theorem rootGamma_spec {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {b : ℤ}
    (hb : (4 * m : ℤ) ∣ b ^ 2 + n) :
    (rootGamma n m b).1 * (rootGamma n m b).2.2.2 -
        (rootGamma n m b).2.1 * (rootGamma n m b).2.2.1 = 1 ∧
      (rootRep n m b).1 ∈ Red n := by
  have h : 0 < n ∧ 0 < m ∧ (4 * m : ℤ) ∣ b ^ 2 + n := ⟨hn, hm, hb⟩
  have := Classical.choose_spec (exists_root_red h.1 h.2.1 h.2.2)
  simp only [rootRep, rootGamma, dif_pos h]
  exact this

theorem rootRep_mem {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {b : ℤ}
    (hb : (4 * m : ℤ) ∣ b ^ 2 + n) : (rootRep n m b).1 ∈ Red n :=
  (rootGamma_spec hn hm hb).2

theorem rootRep_eval {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {b : ℤ}
    (hb : (4 * m : ℤ) ∣ b ^ 2 + n) :
    (rootRep n m b).1.eval (rootRep n m b).2.1 (rootRep n m b).2.2 = m := by
  have hdet := (rootGamma_spec hn hm hb).1
  simp only [rootRep, Form.eval_act]
  set p := (rootGamma n m b).1
  set q := (rootGamma n m b).2.1
  set r := (rootGamma n m b).2.2.1
  set s := (rootGamma n m b).2.2.2
  have e1 : p * s + q * -r = 1 := by linarith
  have e2 : r * s + s * -r = 0 := by ring
  rw [e1, e2]
  simp [gform, Form.eval]

theorem rootRep_coprime {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {b : ℤ}
    (hb : (4 * m : ℤ) ∣ b ^ 2 + n) : IsCoprime (rootRep n m b).2.1 (rootRep n m b).2.2 := by
  have hdet := (rootGamma_spec hn hm hb).1
  refine ⟨(rootGamma n m b).1, (rootGamma n m b).2.1, ?_⟩
  simp only [rootRep]
  linarith

/-- Two forms properly equivalent by matrices with the same second row differ by a
translation. -/
theorem act_eq_shift (g₁ g₂ : Form) {p₁ q₁ p₂ q₂ r s : ℤ} (d₁ : p₁ * s - q₁ * r = 1)
    (d₂ : p₂ * s - q₂ * r = 1) (h : g₁.act p₁ q₁ r s = g₂.act p₂ q₂ r s) :
    g₂ = g₁.act 1 (p₁ * -q₂ + q₁ * p₂) 0 1 := by
  have h' := congrArg (fun F : Form => F.act s (-q₂) (-r) p₂) h
  simp only [act_act] at h'
  have e1 : p₂ * s + q₂ * -r = 1 := by linarith
  have e2 : p₂ * -q₂ + q₂ * p₂ = 0 := by ring
  have e3 : r * s + s * -r = 0 := by ring
  have e4 : r * -q₂ + s * p₂ = 1 := by linarith
  have e5 : p₁ * s + q₁ * -r = 1 := by linarith
  rw [e1, e2, e3, e4, e5, act_one] at h'
  exact h'.symm

theorem rootRep_inj {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {b₁ b₂ : ℤ}
    (h₁ : (4 * m : ℤ) ∣ b₁ ^ 2 + n) (h₂ : (4 * m : ℤ) ∣ b₂ ^ 2 + n)
    (hb₁ : 0 ≤ b₁ ∧ b₁ < 2 * m) (hb₂ : 0 ≤ b₂ ∧ b₂ < 2 * m)
    (heq : rootRep n m b₁ = rootRep n m b₂) : b₁ = b₂ := by
  have d₁ := (rootGamma_spec hn hm h₁).1
  have d₂ := (rootGamma_spec hn hm h₂).1
  simp only [rootRep, Prod.mk.injEq, neg_inj] at heq
  obtain ⟨hf, hs, hr⟩ := heq
  set γ₁ := rootGamma n m b₁
  set γ₂ := rootGamma n m b₂
  rw [hs, hr] at hf
  rw [hs, hr] at d₁
  have key := act_eq_shift _ _ d₁ d₂ hf
  have hb := congrArg Form.b key
  simp only [gform, act, Form.eval] at hb
  set t := γ₁.1 * -γ₂.2.1 + γ₁.2.1 * γ₂.1
  have hb' : b₂ = b₁ + 2 * m * t := by linarith
  have ht : t = 0 := by
    by_contra hc
    rcases lt_or_gt_of_ne hc with hc | hc
    · have : (m : ℤ) * t ≤ -m := by nlinarith
      linarith
    · have : (m : ℤ) ≤ m * t := by nlinarith
      linarith
  rw [hb', ht]
  ring

/-- The content of `g • v` for primitive `v`. -/
theorem smul_coprime_inj {g g' x y x' y' : ℤ} (hg : 0 < g) (hg' : 0 < g')
    (hc : IsCoprime x y) (hc' : IsCoprime x' y') (h1 : g * x = g' * x') (h2 : g * y = g' * y') :
    g = g' ∧ x = x' ∧ y = y' := by
  have e : Int.gcd (g * x) (g * y) = Int.gcd (g' * x') (g' * y') := by rw [h1, h2]
  rw [Int.gcd_mul_left, Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one.mp hc,
    Int.isCoprime_iff_gcd_eq_one.mp hc'] at e
  have hgg : g = g' := by omega
  subst hgg
  exact ⟨rfl, mul_left_cancel₀ hg.ne' h1, mul_left_cancel₀ hg.ne' h2⟩

/-- `f` is good for `n`: `∃ r s, n ∣ 2 f(r, s) + 1` (the ternary completion exists). -/
def Good (n : ℕ) (f : Form) : Prop := ∃ r s : ℤ, (n : ℤ) ∣ 2 * f.eval r s + 1

theorem good_of_rep {n : ℕ} {f : Form} {x y m t : ℤ} (hm : f.eval x y = m)
    (ht : (n : ℤ) ∣ 2 * t ^ 2 * m + 1) : Good n f :=
  ⟨t * x, t * y, by rw [Form.eval_smul, hm]; convert ht using 1; ring⟩

end ThreeSquares.B3
