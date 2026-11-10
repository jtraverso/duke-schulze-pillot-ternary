/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.WeightBounds
public import DukeH1.Method1

/-!
# Smoothness of the Kloosterman weight

A weight `F(u) = K (e(θ/u) f(λu) + g(λu))` (polynomials `f, g`), clamped to `[y₀, Y₀]`, is
bounded and `log`-Lipschitz (`smoothW_form`).
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares.Poin

open Complex Polynomial ThreeSquares.Lip Finset

open scoped Real

/-- Clamping to `[y₀, Y₀]`. -/
def clampN (y₀ Y₀ c : ℕ) : ℕ := max y₀ (min c Y₀)

/-- The model weight. -/
noncomputable def formW (K : ℂ) (θ lam : ℝ) (f g : ℂ[X]) (u : ℕ) : ℂ :=
  K * (cexp (2 * π * Complex.I * (θ / u)) * f.eval ((lam * u : ℝ) : ℂ) + g.eval ((lam * u : ℝ) : ℂ))

theorem clampN_ge (y₀ Y₀ c : ℕ) : y₀ ≤ clampN y₀ Y₀ c := le_max_left _ _

theorem clampN_le (y₀ Y₀ c : ℕ) (h : y₀ ≤ Y₀) : clampN y₀ Y₀ c ≤ Y₀ :=
  max_le h (min_le_right _ _)

theorem clampN_eq (y₀ Y₀ c : ℕ) (h1 : y₀ ≤ c) (h2 : c ≤ Y₀) : clampN y₀ Y₀ c = c := by
  unfold clampN; rw [min_eq_left h2, max_eq_right h1]

theorem smoothW_form (K : ℂ) (θ lam : ℝ) (hlam : 0 ≤ lam) (f g : ℂ[X]) (y₀ Y₀ : ℕ) (hy₀ : 1 ≤ y₀)
    (hY : y₀ ≤ Y₀) :
    SmoothW (fun c => formW K θ lam f g (clampN y₀ Y₀ c))
      (‖K‖ * (polyA f * (1 + lam * Y₀) ^ f.natDegree + polyA g * (1 + lam * Y₀) ^ g.natDegree))
      (‖K‖ * (2 * π * |θ| / y₀ * (polyA f * (1 + lam * Y₀) ^ f.natDegree) +
        (polyA f * f.natDegree * (1 + lam * Y₀) ^ f.natDegree +
          polyA g * g.natDegree * (1 + lam * Y₀) ^ g.natDegree) * (lam * Y₀))) := by
  set S := lam * Y₀
  have hS0 : 0 ≤ S := by positivity
  have hrange : ∀ c, 0 ≤ lam * (clampN y₀ Y₀ c : ℝ) ∧ lam * (clampN y₀ Y₀ c : ℝ) ≤ S := by
    intro c
    refine ⟨by positivity, mul_le_mul_of_nonneg_left (by exact_mod_cast clampN_le y₀ Y₀ c hY) hlam⟩
  have hnormE : ∀ x : ℝ, ‖cexp (2 * π * Complex.I * x)‖ = 1 := by
    intro x
    rw [show 2 * (π : ℂ) * Complex.I * x = ((2 * π * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  constructor
  · intro c
    unfold formW
    obtain ⟨h0, h1⟩ := hrange c
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_eval_le g h0 h1))
    rw [norm_mul]
    have := hnormE (θ / (clampN y₀ Y₀ c : ℕ))
    push_cast at this
    rw [this, one_mul]
    exact norm_eval_le f h0 h1
  · intro c c' hc hcc'
    set u := clampN y₀ Y₀ c
    set u' := clampN y₀ Y₀ c'
    have hu : y₀ ≤ u := clampN_ge _ _ _
    have hu' : y₀ ≤ u' := clampN_ge _ _ _
    have huu' : u ≤ u' := by
      simp only [u, u', clampN]; exact max_le_max le_rfl (min_le_min_right _ hcc')
    have hdiff : u' - u ≤ c' - c := by
      simp only [u, u', clampN]
      have := min_le_min_right Y₀ hcc'
      omega
    have hu0 : (0 : ℝ) < u := by exact_mod_cast (lt_of_lt_of_le hy₀ hu)
    have hu0' : (0 : ℝ) < u' := by exact_mod_cast (lt_of_lt_of_le hy₀ hu')
    -- relative step
    have hrel : ((u' - u : ℕ) : ℝ) / u ≤ ((c' - c : ℕ) : ℝ) / c := by
      by_cases hcY : c < Y₀
      · have hcu : c ≤ u := by simp only [u, clampN]; omega
        have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
        calc ((u' - u : ℕ) : ℝ) / u ≤ ((c' - c : ℕ) : ℝ) / u := by
              gcongr
          _ ≤ ((c' - c : ℕ) : ℝ) / c := by
              gcongr
      · push_neg at hcY
        have h1 : u = Y₀ := by simp only [u, clampN]; omega
        have h2 : u' = Y₀ := by simp only [u', clampN]; omega
        rw [h1, h2, Nat.sub_self]; simp; positivity
    have hstep : ‖formW K θ lam f g u' - formW K θ lam f g u‖ ≤
        (‖K‖ * (2 * π * |θ| / y₀ * (polyA f * (1 + S) ^ f.natDegree) +
          (polyA f * f.natDegree * (1 + S) ^ f.natDegree +
            polyA g * g.natDegree * (1 + S) ^ g.natDegree) * S)) * (((u' - u : ℕ) : ℝ) / u) := by
      unfold formW
      rw [← mul_sub, norm_mul, mul_assoc ‖K‖]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      obtain ⟨a0, a1⟩ := hrange c
      obtain ⟨b0, b1⟩ := hrange c'
      set s := lam * (u : ℝ)
      set s' := lam * (u' : ℝ)
      have hss : |s' - s| = S * (((u' - u : ℕ) : ℝ) / u) - lam * (Y₀ - u) * (((u' - u : ℕ) : ℝ) / u) := by
        have : ((u' - u : ℕ) : ℝ) = (u' : ℝ) - u := by push_cast [huu']; ring
        rw [this, abs_of_nonneg (by simp only [s, s']; nlinarith [(by exact_mod_cast huu' : (u : ℝ) ≤ u')])]
        simp only [s, s', S]; field_simp; ring
      have hss' : |s' - s| ≤ S * (((u' - u : ℕ) : ℝ) / u) := by
        rw [hss]
        have : 0 ≤ lam * (Y₀ - u) * (((u' - u : ℕ) : ℝ) / u) := by
          have : (u : ℝ) ≤ Y₀ := by exact_mod_cast clampN_le y₀ Y₀ c hY
          have : 0 ≤ (Y₀ : ℝ) - u := by linarith
          positivity
        linarith
      have he : ‖cexp (2 * π * Complex.I * (θ / u')) - cexp (2 * π * Complex.I * (θ / u))‖ ≤
          2 * π * |θ| / y₀ * (((u' - u : ℕ) : ℝ) / u) := by
        have := norm_e_sub_le (θ / u) (θ / u')
        push_cast at this
        refine this.trans ?_
        have e : θ / (u' : ℝ) - θ / u = -(θ * (((u' : ℝ) - u) / (u * u'))) := by field_simp; ring
        rw [e, abs_neg, abs_mul]
        have hy0 : (0 : ℝ) < y₀ := by exact_mod_cast hy₀
        have hyu' : (y₀ : ℝ) ≤ u' := by exact_mod_cast hu'
        have h1 : |((u' : ℝ) - u) / (u * u')| ≤ (((u' - u : ℕ) : ℝ) / u) / y₀ := by
          have : ((u' - u : ℕ) : ℝ) = (u' : ℝ) - u := by push_cast [huu']; ring
          rw [← this, abs_of_nonneg (by positivity)]
          rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have : 0 ≤ ((u' - u : ℕ) : ℝ) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hyu' (le_of_lt hu0)]
        calc 2 * π * (|θ| * |((u' : ℝ) - u) / (u * u')|) ≤ 2 * π * (|θ| * ((((u' - u : ℕ) : ℝ) / u) / y₀)) := by
              gcongr
          _ = _ := by ring
      have e1 : ‖(cexp (2 * π * Complex.I * (θ / (u' : ℕ))) * f.eval ((lam * (u' : ℕ) : ℝ) : ℂ) +
            g.eval ((lam * (u' : ℕ) : ℝ) : ℂ)) -
          (cexp (2 * π * Complex.I * (θ / (u : ℕ))) * f.eval ((lam * (u : ℕ) : ℝ) : ℂ) +
            g.eval ((lam * (u : ℕ) : ℝ) : ℂ))‖ =
          ‖(cexp (2 * π * Complex.I * (θ / u')) - cexp (2 * π * Complex.I * (θ / u))) * f.eval (s' : ℂ) +
            cexp (2 * π * Complex.I * (θ / u)) * (f.eval (s' : ℂ) - f.eval (s : ℂ)) +
            (g.eval (s' : ℂ) - g.eval (s : ℂ))‖ := by
        congr 1; simp only [s, s']; ring
      refine le_of_eq_of_le e1 ?_
      refine le_trans (norm_add_le _ _) ?_
      refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
      rw [norm_mul, norm_mul]
      have hE := hnormE (θ / u)
      push_cast at hE
      rw [hE, one_mul]
      have hf := norm_eval_le f b0 b1
      have hfl := norm_eval_sub_le f a0 a1 b0 b1
      have hgl := norm_eval_sub_le g a0 a1 b0 b1
      have hpf := polyA_nonneg f
      have hpg := polyA_nonneg g
      have hq : 0 ≤ ((u' - u : ℕ) : ℝ) / u := by positivity
      calc ‖cexp (2 * π * Complex.I * (θ / u')) - cexp (2 * π * Complex.I * (θ / u))‖ * ‖f.eval (s' : ℂ)‖ +
            ‖f.eval (s' : ℂ) - f.eval (s : ℂ)‖ + ‖g.eval (s' : ℂ) - g.eval (s : ℂ)‖
          ≤ (2 * π * |θ| / y₀ * (((u' - u : ℕ) : ℝ) / u)) * (polyA f * (1 + S) ^ f.natDegree) +
            polyA f * f.natDegree * (1 + S) ^ f.natDegree * (S * (((u' - u : ℕ) : ℝ) / u)) +
            polyA g * g.natDegree * (1 + S) ^ g.natDegree * (S * (((u' - u : ℕ) : ℝ) / u)) := by
            gcongr
            · exact hfl.trans (by gcongr)
            · exact hgl.trans (by gcongr)
        _ = _ := by ring
    refine hstep.trans ?_
    have hW1 : 0 ≤ ‖K‖ * (2 * π * |θ| / y₀ * (polyA f * (1 + S) ^ f.natDegree) +
          (polyA f * f.natDegree * (1 + S) ^ f.natDegree +
            polyA g * g.natDegree * (1 + S) ^ g.natDegree) * S) := by
      have := polyA_nonneg f; have := polyA_nonneg g; positivity
    exact (mul_le_mul_of_nonneg_left hrel hW1).trans (le_of_eq (by ring))

end ThreeSquares.Poin
