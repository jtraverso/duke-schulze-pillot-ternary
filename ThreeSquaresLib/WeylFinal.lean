/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.WeylPow

/-!
# Iwaniec's bound for squarefree `n`

For every even `ℓ ≥ 2` there is `η > 0` such that for every isotropic `u`,
`‖W_u(t)‖ ≪_u t^{ℓ/2 + 1/2 − η}` for squarefree `t ≡ 3 (mod 8)` (`weyl_iso_even`).
-/

@[expose] public section

namespace ThreeSquares

open Real Polynomial

/-- **Iwaniec's bound (even degree).** -/
theorem weyl_iso_even (ℓ : ℕ) (hℓ2 : 2 ≤ ℓ) (hℓ : Even ℓ) :
    ∃ η > 0, ∀ u : Fin 3 → ℂ, ∑ j, u j ^ 2 = 0 → ∃ C : ℝ, ∀ t : ℕ, 1 ≤ t → Squarefree t → t % 8 = 3 →
      ‖weylU u ℓ t‖ ≤ C * (t : ℝ) ^ ((ℓ : ℝ) / 2 + 1 / 2 - η) := by
  obtain ⟨pp, qq, hpq⟩ := Lip.besS_closed (ℓ + 1)
  set d : ℕ := max pp.natDegree qq.natDegree
  set δ : ℝ := 1 / (8000 * ((d : ℝ) + 2))
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hδ0 : 0 < δ := by positivity
  have hδ : δ ≤ 1 / 8000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hdδ : ((d : ℝ) + 1) * δ ≤ 1 / 4000 := by
    have : ((d : ℝ) + 1) * δ = ((d : ℝ) + 1) / (8000 * ((d : ℝ) + 2)) := by
      simp only [δ]; field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  refine ⟨δ / 16, by positivity, fun u hu => ?_⟩
  obtain ⟨Cw, hCw, hWsq⟩ := Poin.weyl_sq_le u hu (by omega) hℓ
  obtain ⟨C, hC, hτ⟩ := card_divisors_le_rpow (δ / 16) (by positivity) (by linarith)
  obtain ⟨N₁, hN₁⟩ := params_eventually δ hδ0 hδ
  obtain ⟨c, hc, N₂, hN₂⟩ := card_levels_lower (1 / 100) (by norm_num)
  obtain ⟨N₃, hN₃⟩ := (pl_eE ℓ hℓ2 Cw hCw pp qq δ hδ0 hδ hdδ C hC).eventually_le
    (show (ℓ : ℝ) + 1 - 3 * δ / 16 < ℓ + 1 - 2 * (δ / 16) by linarith)
  set N := max 1 (max N₁ (max N₂ N₃))
  set C₀ := ∑ t ∈ Finset.range N, ‖weylU u ℓ t‖
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨max 1 C₀, fun t ht htsf ht8 => ?_⟩
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ2
  have hexp : 0 ≤ (ℓ : ℝ) / 2 + 1 / 2 - δ / 16 := by linarith
  have hpow1 : 1 ≤ (t : ℝ) ^ ((ℓ : ℝ) / 2 + 1 / 2 - δ / 16) := Real.one_le_rpow htR hexp
  by_cases htN : N ≤ t
  · simp only [N, max_le_iff] at htN
    obtain ⟨-, h1, h2, h3⟩ := htN
    have hcard : 0 < (levels t (pP0 t)).card := by
      have := hN₂ t h2
      have hpos : 0 < c * (t : ℝ) ^ (11 / 40 - 1 / 100 : ℝ) := by positivity
      exact_mod_cast lt_of_lt_of_le hpos this
    have hstep := weyl_step u ℓ hℓ2 Cw hCw hWsq hpq δ hδ0 hδ C hC hτ t htsf (by omega) (hN₁ t h1) hcard
    have hb := hN₃ t h3
    have e : ((t : ℝ) ^ ((ℓ : ℝ) / 2 + 1 / 2 - δ / 16)) ^ 2 = (t : ℝ) ^ ((ℓ : ℝ) + 1 - 2 * (δ / 16)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; push_cast; ring
    have hsq : ‖weylU u ℓ t‖ ^ 2 ≤ ((t : ℝ) ^ ((ℓ : ℝ) / 2 + 1 / 2 - δ / 16)) ^ 2 := by
      rw [e]; exact hstep.trans hb
    have := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
    calc ‖weylU u ℓ t‖ ≤ (t : ℝ) ^ ((ℓ : ℝ) / 2 + 1 / 2 - δ / 16) := this
      _ ≤ max 1 C₀ * (t : ℝ) ^ ((ℓ : ℝ) / 2 + 1 / 2 - δ / 16) :=
          le_mul_of_one_le_left (by positivity) (le_max_left _ _)
  · push_neg at htN
    have h1 : ‖weylU u ℓ t‖ ≤ C₀ :=
      Finset.single_le_sum (f := fun t => ‖weylU u ℓ t‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr htN)
    calc ‖weylU u ℓ t‖ ≤ max 1 C₀ := h1.trans (le_max_right _ _)
      _ ≤ max 1 C₀ * (t : ℝ) ^ ((ℓ : ℝ) / 2 + 1 / 2 - δ / 16) :=
          le_mul_of_one_le_right (by positivity) hpow1

end ThreeSquares
