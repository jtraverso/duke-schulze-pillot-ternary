/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.FourierP

/-!
# The Petersson inequality for the Weyl sums

For `u` isotropic and `ℓ ≥ 2` even there is `C` such that for every level `Q` with `4 ∣ Q` and
every `n ≥ 1`,
`|W_u(n)|² ≤ C · (Q² / φ(Q)) · n^{k−1} · |P̂_Q(n)|`, `k = 3/2 + ℓ` (`weyl_sq_le`),
where `P̂_Q(n) = 2 + 2 ∑_{(c,d₀)} J_k(c, d₀)` is the Kloosterman–Bessel series of `FourierP`.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares.Poin

open Complex UpperHalfPlane ModularGroup MeasureTheory ThreeSquares.FD ThreeSquares.Mult Filter
  Topology Set

open scoped MatrixGroups Real ComplexConjugate

theorem muQ_univ (Q : ℕ) [NeZero Q] :
    (muQ Q Set.univ).toReal = Fintype.card (Keys Q) * (volume fd).toReal := by
  rw [← lintegral_one, lintegral_muQ Q _ measurable_const]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ENNReal.toReal_mul]; simp

theorem muQ_univ_le (Q : ℕ) [NeZero Q] :
    (muQ Q Set.univ).toReal ≤ ((Q : ℝ) ^ 2 / Nat.totient Q) * (volume fd).toReal := by
  rw [muQ_univ]
  gcongr
  have hφ : 0 < Nat.totient Q := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne Q))
  rw [le_div_iff₀ (by exact_mod_cast hφ)]
  exact_mod_cast card_keys_mul_totient Q

/-- **`|W_u(n)|² ≤ C (Q²/φ(Q)) n^{k−1} |P̂_Q(n)|`.** -/
theorem weyl_sq_le (u : Fin 3 → ℂ) (hu : ∑ j, u j ^ 2 = 0) {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓ : Even ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : ℕ) [NeZero Q], 4 ∣ Q → ∀ n : ℕ, 0 < n →
      ‖weylU u ℓ n‖ ^ 2 ≤ C * ((Q : ℝ) ^ 2 / Nat.totient Q) * (n : ℝ) ^ (kw ℓ - 1) *
        ‖Phat ℓ n Q‖ := by
  obtain ⟨M, hM⟩ := theta3_bound u hu ℓ hℓ1
  have hk : 0 < kw ℓ - 1 := by
    unfold kw; have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    linarith
  have hΓ : 0 < Real.Gamma (kw ℓ - 1) := Real.Gamma_pos_of_pos hk
  refine ⟨M ^ 2 * (volume fd).toReal * (4 * π) ^ (kw ℓ - 1) / (2 * Real.Gamma (kw ℓ - 1)),
    by positivity, fun Q _ hQ n hn => ?_⟩
  have hθ := isAut_theta3 u hu hℓ1 hℓ hQ
  have hP := isAut_poin ℓ n hℓ1 hQ hn
  set Γc : ℝ := Real.Gamma (kw ℓ - 1) * (1 / (4 * π * n)) ^ (kw ℓ - 1)
  have hΓc : 0 < Γc := by positivity
  have h1 : pet ℓ Q (theta3 u ℓ) (poin ℓ Q n) = 2 * ((Γc : ℂ) * weylU u ℓ n) := by
    rw [pet_poin ℓ n hℓ1 hn hQ hθ, strip_PhiF_theta3 u hu hℓ1 hℓ hn]
  have h2 : pet ℓ Q (poin ℓ Q n) (poin ℓ Q n) = 2 * ((Γc : ℂ) * Phat ℓ n Q) := by
    rw [pet_poin ℓ n hℓ1 hn hQ hP, strip_PhiF_poin ℓ n hℓ1 hℓ hQ hn]
  have hCS := norm_pet_sq_le ℓ Q hθ hP
  set Aθ := ∫ z, ‖theta3 u ℓ z‖ ^ 2 * z.im ^ kw ℓ ∂muQ Q
  set AP := ∫ z, ‖poin ℓ Q n z‖ ^ 2 * z.im ^ kw ℓ ∂muQ Q
  have hAP : AP = 2 * Γc * ‖Phat ℓ n Q‖ := by
    have := pet_self_eq ℓ Q (poin ℓ Q n)
    rw [h2] at this
    have h0 : 0 ≤ AP := integral_nonneg fun z => by positivity
    have := congrArg norm this
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΓc] at this
    rw [← this]; norm_num; ring
  have hAθ : Aθ ≤ M ^ 2 * (muQ Q Set.univ).toReal :=
    pet_self_le ℓ Q hθ (fun z => hM z z.im_pos)
  rw [h1, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΓc, hAP] at hCS
  have hAθ0 : 0 ≤ Aθ := integral_nonneg fun z => by positivity
  have hmu := muQ_univ_le Q
  have hPn : 0 ≤ ‖Phat ℓ n Q‖ := norm_nonneg _
  -- `4 Γc² |W|² ≤ Aθ · 2 Γc |P̂|`
  have key : ‖weylU u ℓ n‖ ^ 2 ≤ Aθ * ‖Phat ℓ n Q‖ / (2 * Γc) := by
    rw [le_div_iff₀ (by positivity)]
    have : (‖(2 : ℂ)‖ * (Γc * ‖weylU u ℓ n‖)) ^ 2 ≤ Aθ * (2 * Γc * ‖Phat ℓ n Q‖) := hCS
    rw [Complex.norm_two] at this
    nlinarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hΓc' : 1 / (2 * Γc) = (4 * π) ^ (kw ℓ - 1) * (n : ℝ) ^ (kw ℓ - 1) /
      (2 * Real.Gamma (kw ℓ - 1)) := by
    simp only [Γc]
    rw [Real.div_rpow zero_le_one (by positivity), Real.one_rpow,
      Real.mul_rpow (by positivity) hn'.le]
    have h1 : 0 < (4 * π) ^ (kw ℓ - 1) := by positivity
    have h2 : 0 < (n : ℝ) ^ (kw ℓ - 1) := by positivity
    field_simp
  calc ‖weylU u ℓ n‖ ^ 2 ≤ Aθ * ‖Phat ℓ n Q‖ / (2 * Γc) := key
    _ = Aθ * ‖Phat ℓ n Q‖ * (1 / (2 * Γc)) := by ring
    _ ≤ (M ^ 2 * (((Q : ℝ) ^ 2 / Nat.totient Q) * (volume fd).toReal)) * ‖Phat ℓ n Q‖ *
          (1 / (2 * Γc)) := by
        gcongr
        exact hAθ.trans (mul_le_mul_of_nonneg_left hmu (sq_nonneg M))
    _ = _ := by rw [hΓc']; ring

end ThreeSquares.Poin
