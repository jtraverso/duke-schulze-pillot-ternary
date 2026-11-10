/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.LevelCount

/-!
# The smooth weights

On `(y, Y]`, `W1 = formW(Kc, 4n, 1/(2πn), p, q)` and `W2 = formW(Kc, −4n, 1/(2πn), q, p)` (`W1_eq_formW`,
`W2_eq_formW`); the clamped versions are `SmoothW` with common constants `wW0`, `wW1 ≤ wLam · wW0`.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open Finset Polynomial

open scoped Real

theorem SmoothW.mono {W : ℕ → ℂ} {a b a' b' : ℝ} (h : SmoothW W a b) (ha : a ≤ a') (hb : b ≤ b') :
    SmoothW W a' b' := by
  constructor
  · intro c; exact (h.bound c).trans ha
  · intro c c' hc hcc'
    refine (h.lip c c' hc hcc').trans ?_
    have : (0 : ℝ) ≤ ((c' - c : ℕ) : ℝ) / c := by positivity
    calc b * ((c' - c : ℕ) : ℝ) / c = b * (((c' - c : ℕ) : ℝ) / c) := by ring
      _ ≤ b' * (((c' - c : ℕ) : ℝ) / c) := mul_le_mul_of_nonneg_right hb this
      _ = b' * ((c' - c : ℕ) : ℝ) / c := by ring

theorem W1_eq_formW (ℓ n : ℕ) (hn : 0 < n) {p q : ℂ[X]} (hpq : Lip.BesForm (ℓ + 1) p q) (c : ℕ)
    (hc : 0 < c) :
    W1 ℓ n c = Poin.formW (Poin.Kc ℓ n) (4 * n) (1 / (2 * π * n)) p q c := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold W1 Poin.formW
  rw [Poin.cfac_closed ℓ n hn hpq c hc]
  have harg : (((1 / (2 * π * n)) * c : ℝ) : ℂ) = ((c / (2 * π * n) : ℝ) : ℂ) := by
    congr 1; field_simp
  rw [harg]
  set z : ℂ := 2 * π * Complex.I * (2 * n / c)
  have ez : (2 * π * Complex.I * (2 * ((n : ℤ) : ℂ) / c) : ℂ) = z := by simp only [z]; push_cast; ring
  have e4 : Complex.exp (2 * π * Complex.I * (((4 * (n : ℝ) : ℝ) : ℂ) / (c : ℂ))) =
      Complex.exp z * Complex.exp z := by
    rw [← Complex.exp_add]; congr 1; simp only [z]; push_cast; ring
  have hone : Complex.exp (-z) * Complex.exp z = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  clear_value z
  rw [ez, e4]
  linear_combination (Poin.Kc ℓ n * eval (((c : ℝ) / (2 * π * n) : ℝ) : ℂ) q) * hone

theorem W2_eq_formW (ℓ n : ℕ) (hn : 0 < n) {p q : ℂ[X]} (hpq : Lip.BesForm (ℓ + 1) p q) (c : ℕ)
    (hc : 0 < c) :
    W2 ℓ n c = Poin.formW (Poin.Kc ℓ n) (-(4 * n)) (1 / (2 * π * n)) q p c := by
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold W2 Poin.formW
  rw [Poin.cfac_closed ℓ n hn hpq c hc]
  have harg : (((1 / (2 * π * n)) * c : ℝ) : ℂ) = ((c / (2 * π * n) : ℝ) : ℂ) := by
    congr 1; field_simp
  rw [harg]
  set z : ℂ := 2 * π * Complex.I * (2 * n / c)
  have ez : (2 * π * Complex.I * (2 * (-((n : ℤ) : ℂ)) / c) : ℂ) = -z := by simp only [z]; push_cast; ring
  have e4 : Complex.exp (2 * π * Complex.I * (((-(4 * (n : ℝ)) : ℝ) : ℂ) / (c : ℂ))) =
      Complex.exp (-z) * Complex.exp (-z) := by
    rw [← Complex.exp_add]; congr 1; simp only [z]; push_cast; ring
  have hone : Complex.exp z * Complex.exp (-z) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  clear_value z
  rw [ez, e4]
  linear_combination (Poin.Kc ℓ n * eval (((c : ℝ) / (2 * π * n) : ℝ) : ℂ) p) * hone

/-- `polyA p (1 + S)^{deg p}`. -/
noncomputable def wA (p : ℂ[X]) (S : ℝ) : ℝ := Poin.polyA p * (1 + S) ^ p.natDegree

/-- `polyA p · deg p · (1 + S)^{deg p}`. -/
noncomputable def wB (p : ℂ[X]) (S : ℝ) : ℝ := Poin.polyA p * p.natDegree * (1 + S) ^ p.natDegree

theorem wA_nonneg (p : ℂ[X]) {S : ℝ} (hS : 0 ≤ S) : 0 ≤ wA p S := by
  unfold wA; have := Poin.polyA_nonneg p; positivity

theorem wB_le (p : ℂ[X]) {S : ℝ} (hS : 0 ≤ S) (d : ℝ) (hd : (p.natDegree : ℝ) ≤ d) :
    wB p S ≤ d * wA p S := by
  unfold wA wB
  have h := wA_nonneg p hS
  unfold wA at h
  calc Poin.polyA p * p.natDegree * (1 + S) ^ p.natDegree
      = (p.natDegree : ℝ) * (Poin.polyA p * (1 + S) ^ p.natDegree) := by ring
    _ ≤ d * (Poin.polyA p * (1 + S) ^ p.natDegree) := mul_le_mul_of_nonneg_right hd h

/-- The scale `S = Y/(2πn)`. -/
noncomputable def wS (n Y : ℕ) : ℝ := 1 / (2 * π * n) * (Y : ℝ)

/-- The common sup bound. -/
noncomputable def wW0 (ℓ n Y : ℕ) (p q : ℂ[X]) : ℝ := ‖Poin.Kc ℓ n‖ * (wA p (wS n Y) + wA q (wS n Y))

/-- The common log-Lipschitz constant. -/
noncomputable def wW1 (ℓ n y Y : ℕ) (p q : ℂ[X]) : ℝ :=
  ‖Poin.Kc ℓ n‖ * (2 * π * |4 * (n : ℝ)| / ((y + 1 : ℕ) : ℝ) * (wA p (wS n Y) + wA q (wS n Y)) +
    (wB p (wS n Y) + wB q (wS n Y)) * wS n Y)

/-- `Λ = 8πn/(y+1) + max(deg) · S`. -/
noncomputable def wLam (n y Y : ℕ) (p q : ℂ[X]) : ℝ :=
  2 * π * |4 * (n : ℝ)| / ((y + 1 : ℕ) : ℝ) + max (p.natDegree : ℝ) q.natDegree * wS n Y

theorem wS_nonneg (n Y : ℕ) : 0 ≤ wS n Y := by unfold wS; positivity

theorem wW1_le (ℓ n y Y : ℕ) (p q : ℂ[X]) : wW1 ℓ n y Y p q ≤ wLam n y Y p q * wW0 ℓ n Y p q := by
  have hS := wS_nonneg n Y
  have hAp := wA_nonneg p hS
  have hAq := wA_nonneg q hS
  have hBp := wB_le p hS _ (le_max_left (p.natDegree : ℝ) q.natDegree)
  have hBq := wB_le q hS _ (le_max_right (p.natDegree : ℝ) q.natDegree)
  have hK := norm_nonneg (Poin.Kc ℓ n)
  unfold wW1 wLam wW0
  have hc : 0 ≤ 2 * π * |4 * (n : ℝ)| / ((y + 1 : ℕ) : ℝ) := by positivity
  have h2 : (wB p (wS n Y) + wB q (wS n Y)) * wS n Y ≤
      max (p.natDegree : ℝ) q.natDegree * wS n Y * (wA p (wS n Y) + wA q (wS n Y)) := by
    have := mul_le_mul_of_nonneg_right (add_le_add hBp hBq) hS
    linarith
  calc ‖Poin.Kc ℓ n‖ * (2 * π * |4 * (n : ℝ)| / ((y + 1 : ℕ) : ℝ) * (wA p (wS n Y) + wA q (wS n Y)) +
        (wB p (wS n Y) + wB q (wS n Y)) * wS n Y)
      ≤ ‖Poin.Kc ℓ n‖ * (2 * π * |4 * (n : ℝ)| / ((y + 1 : ℕ) : ℝ) * (wA p (wS n Y) + wA q (wS n Y)) +
        max (p.natDegree : ℝ) q.natDegree * wS n Y * (wA p (wS n Y) + wA q (wS n Y))) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl h2) hK
    _ = _ := by ring

/-- The clamped smooth weight for `W1`. -/
noncomputable def Wk1 (ℓ n y Y : ℕ) (p q : ℂ[X]) (c : ℕ) : ℂ :=
  Poin.formW (Poin.Kc ℓ n) (4 * n) (1 / (2 * π * n)) p q (Poin.clampN (y + 1) Y c)

/-- The clamped smooth weight for `W2`. -/
noncomputable def Wk2 (ℓ n y Y : ℕ) (p q : ℂ[X]) (c : ℕ) : ℂ :=
  Poin.formW (Poin.Kc ℓ n) (-(4 * n)) (1 / (2 * π * n)) q p (Poin.clampN (y + 1) Y c)

theorem smoothW_Wk1 (ℓ n y Y : ℕ) (p q : ℂ[X]) (hyY : y + 1 ≤ Y) :
    SmoothW (Wk1 ℓ n y Y p q) (wW0 ℓ n Y p q) (wW1 ℓ n y Y p q) := by
  have hS := wS_nonneg n Y
  refine (Poin.smoothW_form (Poin.Kc ℓ n) (4 * n) (1 / (2 * π * n)) (by positivity) p q (y + 1) Y
    (by omega) hyY).mono (le_of_eq rfl) ?_
  have hAq := wA_nonneg q hS
  have hc : 0 ≤ 2 * π * |4 * (n : ℝ)| / ((y + 1 : ℕ) : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hAq : wA p (wS n Y) ≤ wA p (wS n Y) + wA q (wS n Y)) hc
  unfold wA wB wS at *
  linarith

theorem smoothW_Wk2 (ℓ n y Y : ℕ) (p q : ℂ[X]) (hyY : y + 1 ≤ Y) :
    SmoothW (Wk2 ℓ n y Y p q) (wW0 ℓ n Y p q) (wW1 ℓ n y Y p q) := by
  have hS := wS_nonneg n Y
  refine (Poin.smoothW_form (Poin.Kc ℓ n) (-(4 * n)) (1 / (2 * π * n)) (by positivity) q p (y + 1) Y
    (by omega) hyY).mono (le_of_eq (by unfold wW0 wA wS; ring)) ?_
  have hAp := wA_nonneg p hS
  have hc : 0 ≤ 2 * π * |4 * (n : ℝ)| / ((y + 1 : ℕ) : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hAp : wA q (wS n Y) ≤ wA p (wS n Y) + wA q (wS n Y)) hc
  rw [abs_neg]
  unfold wA wB wS at *
  linarith

theorem Wk1_agree (ℓ n y Y : ℕ) (hn : 0 < n) {p q : ℂ[X]} (hpq : Lip.BesForm (ℓ + 1) p q) :
    ∀ c, y < c → c ≤ Y → W1 ℓ n c = Wk1 ℓ n y Y p q c := by
  intro c h1 h2
  unfold Wk1
  rw [Poin.clampN_eq _ _ _ (by omega) h2, W1_eq_formW ℓ n hn hpq c (by omega)]

theorem Wk2_agree (ℓ n y Y : ℕ) (hn : 0 < n) {p q : ℂ[X]} (hpq : Lip.BesForm (ℓ + 1) p q) :
    ∀ c, y < c → c ≤ Y → W2 ℓ n c = Wk2 ℓ n y Y p q c := by
  intro c h1 h2
  unfold Wk2
  rw [Poin.clampN_eq _ _ _ (by omega) h2, W2_eq_formW ℓ n hn hpq c (by omega)]

end ThreeSquares
