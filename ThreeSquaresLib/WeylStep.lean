/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.LevelsPow

/-!
# The Weyl bound for one `n`

For `n` beyond the threshold of `params_eventually`, `‖W_u(n)‖² ≤ eE(n)` with an explicit `eE`
(`weyl_step`), obtained by instantiating `BlockHyp` and combining `crit_total`, `phat_level_bound`
and `weyl_avg`.
-/

@[expose] public section

namespace ThreeSquares

open Real Polynomial

/-- `Λ(n)`. -/
noncomputable def eΛ (δ : ℝ) (pp qq : ℂ[X]) (n : ℕ) : ℝ := wLam n (py δ n) (pY δ n) pp qq

/-- The Rankin exponents `s = 1 + δ/16`, `α = k − 1/2 − δ/16 − s`. -/
noncomputable def eS (δ : ℝ) : ℝ := 1 + δ / 16
noncomputable def eA (ℓ : ℕ) (δ : ℝ) : ℝ := Poin.kw ℓ - 1 / 2 - δ / 16 - eS δ

/-- `ζ(s) ∏_{ℓ ∣ 2n} (1 − ℓ^{1/2 − s})^{−1}`. -/
noncomputable def eZP (δ : ℝ) (n : ℕ) : ℝ :=
  (∑' q : ℕ, (q : ℝ) ^ (-eS δ)) * ∏ ℓ' ∈ (2 * n).primeFactors, (1 - (ℓ' : ℝ) ^ (-(eS δ - 1 / 2)))⁻¹

noncomputable def eLo (ℓ : ℕ) (δ C : ℝ) (pp qq : ℂ[X]) (n : ℕ) : ℝ :=
  (‖Poin.Kc ℓ n‖ * (Poin.polyA pp * (1 + 1) ^ pp.natDegree + Poin.polyA qq * (1 + 1) ^ qq.natDegree) *
    Real.sqrt 2 * C * ((py δ n : ℕ) : ℝ) ^ (δ / 16 + eS δ) * eZP δ n) * ((pP0 n : ℕ) : ℝ) ^ (-eS δ)

noncomputable def eHi (ℓ : ℕ) (δ C : ℝ) (n : ℕ) : ℝ :=
  (Poin.cH ℓ n * Real.sqrt 2 * C * ((pY δ n : ℕ) : ℝ) ^ (-eA ℓ δ) * eZP δ n) * ((pP0 n : ℕ) : ℝ) ^ (-eS δ)

noncomputable def eCT (ℓ : ℕ) (δ C : ℝ) (pp qq : ℂ[X]) (n : ℕ) : ℝ :=
  Real.sqrt 2 * (2 * (pR n : ℝ) ^ (11 / 4 : ℝ) * (((pL δ n : ℝ) + 1) ^ 2 *
      (pσ δ (δ / 16) C (eΛ δ pp qq) n * (((4 * pP0 n : ℕ) : ℝ) * wW0 ℓ n (pY δ n) pp qq *
        (4 * (pY δ n : ℝ) / (pP0 n : ℝ))))) +
    2 * (pR n : ℝ) ^ (-(1 / 4 : ℝ)) * (((levels n (pP0 n)).card : ℝ) * (wW0 ℓ n (pY δ n) pp qq *
      ((pY δ n : ℝ) / (pP0 n : ℝ) * (1 + Real.log (pY δ n)))))) *
    ∏ q ∈ (2 * n).primeFactors, (1 - (q : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹

noncomputable def eE (ℓ : ℕ) (Cw δ C : ℝ) (pp qq : ℂ[X]) (n : ℕ) : ℝ :=
  Cw * (32 * ((4 * pP0 n : ℕ) : ℝ)) * (n : ℝ) ^ (Poin.kw ℓ - 1) *
    (2 * (1 + eLo ℓ δ C pp qq n + eHi ℓ δ C n) + 2 * eCT ℓ δ C pp qq n * (1 / ((levels n (pP0 n)).card : ℝ)))

theorem le_sq_of_sqrt_le (a b : ℝ) (h : Real.sqrt a ≤ b) : a ≤ b ^ 2 := by
  rcases le_or_gt 0 a with ha | ha
  · have := Real.sq_sqrt ha
    nlinarith [Real.sqrt_nonneg a]
  · nlinarith [sq_nonneg b]

/-- **The Weyl bound for one `n`.** -/
theorem weyl_step (u : Fin 3 → ℂ) (ℓ : ℕ) (hℓ2 : 2 ≤ ℓ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hWsq : ∀ (Q : ℕ) [NeZero Q], 4 ∣ Q → ∀ n : ℕ, 0 < n →
      ‖weylU u ℓ n‖ ^ 2 ≤ Cw * ((Q : ℝ) ^ 2 / Nat.totient Q) * (n : ℝ) ^ (Poin.kw ℓ - 1) *
        ‖Poin.Phat ℓ n Q‖)
    {pp qq : ℂ[X]} (hpq : Lip.BesForm (ℓ + 1) pp qq) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8000)
    (C : ℝ) (hC : 0 < C) (hτ : ∀ m : ℕ, m ≠ 0 → ((m.divisors.card : ℕ) : ℝ) ≤ C * (m : ℝ) ^ (δ / 16))
    (n : ℕ) (hn : Squarefree n) (hn4 : n % 4 = 3)
    (hev : 1 ≤ pR n ∧ pR n < n ∧ 0 < pP0 n ∧ 0 < pK n ∧ 0 < py δ n ∧ 2 * pR n ≤ pB0 n ∧
      pUmax δ n < pP0 n ∧ 2 * pR n ^ 2 * (4 * pP0 n) * pB0 n ^ 2 ≤ py δ n ∧
      py δ n + 1 ≤ pY δ n ∧ n ≤ pY δ n ∧ ((py δ n : ℕ) : ℝ) ≤ 2 * π * n)
    (hcard : 0 < (levels n (pP0 n)).card) :
    ‖weylU u ℓ n‖ ^ 2 ≤ eE ℓ Cw δ C pp qq n := by
  obtain ⟨hR1, hRn, hP0, hK, hy, hB0R, hU3, hPV1, hyY1, hnY, hy2pi⟩ := hev
  have hn0 : 0 < n := by omega
  set Ps := levels n (pP0 n)
  have hP0R : (0 : ℝ) < pP0 n := by exact_mod_cast hP0
  have hyR : (0 : ℝ) < py δ n := by exact_mod_cast hy
  have hYR : (0 : ℝ) < pY δ n := by exact_mod_cast (show 0 < pY δ n by omega)
  have hσ0 : 0 ≤ pσ δ (δ / 16) C (eΛ δ pp qq) n :=
    le_max_of_le_left (le_max_of_le_left (Real.sqrt_nonneg _))
  have H : BlockHyp Ps (pP0 n) (4 * pP0 n) ℓ n (py δ n) (pY δ n) (pB0 n) (pK n) (pR n)
      (Wk1 ℓ n (py δ n) (pY δ n) pp qq) (Wk2 ℓ n (py δ n) (pY δ n) pp qq) (wW0 ℓ n (pY δ n) pp qq)
      (wW1 ℓ n (py δ n) (pY δ n) pp qq) C (δ / 16) (eΛ δ pp qq n) (pUmax δ n) (pX δ n)
      (pσ δ (δ / 16) C (eΛ δ pp qq) n) := by
    refine
      { hW1 := smoothW_Wk1 ℓ n _ _ pp qq hyY1
        hW2 := smoothW_Wk2 ℓ n _ _ pp qq hyY1
        hA1 := Wk1_agree ℓ n _ _ hn0 hpq
        hA2 := Wk2_agree ℓ n _ _ hn0 hpq
        hn := hn
        hn4 := hn4
        hPs := fun p hp => mem_levels hp
        hP₀ := hP0
        hP₀P := by omega
        hC := hC
        hε := by positivity
        hτ := hτ
        hΛ0 := ?_
        hΛ := wW1_le ℓ n _ _ pp qq
        hK := hK
        hB₀R := hB0R
        hσ := hσ0
        hU1 := le_max_of_le_left (le_max_right _ _)
        hU2 := ?_
        hU3 := hU3
        hU4 := pUmax_ge_one δ n
        hy := hy
        hX := ?_
        hPV1 := hPV1
        hPV2 := ?_
        hM1 := le_sq_of_sqrt_le _ _ (le_max_of_le_left (le_max_left _ _))
        hM2 := le_sq_of_sqrt_le _ _ (le_max_of_le_left (le_max_right _ _)) }
    · unfold eΛ wLam
      have := wS_nonneg n (pY δ n)
      have : 0 ≤ max (pp.natDegree : ℝ) qq.natDegree := le_max_of_le_left (Nat.cast_nonneg _)
      positivity
    · set x := 16 * (pK n : ℝ) ^ 2 * (pY δ n : ℝ) / (pP0 n : ℝ)
      have hx0 : 0 ≤ x := by positivity
      have hux : x ^ (1 / 3 : ℝ) ≤ pUmax δ n := le_max_right _ _
      have hc : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]; norm_num
      have h3 : x ≤ pUmax δ n ^ 3 := by
        rw [← hc]; exact pow_le_pow_left₀ (by positivity) hux 3
      have : 16 * (pK n : ℝ) ^ 2 * (pY δ n : ℝ) = x * (pP0 n : ℝ) := by
        simp only [x]; field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right h3 hP0R.le
    · unfold pX
      rw [div_mul_cancel₀ _ hyR.ne']
    · have hpos : (0 : ℝ) < 4 * (pY δ n : ℝ) / (pP0 n : ℝ) := by positivity
      have hpv : pPV δ (eΛ δ pp qq) n ≤ pσ δ (δ / 16) C (eΛ δ pp qq) n := le_max_right _ _
      unfold pPV at hpv
      have := mul_le_mul_of_nonneg_right hpv hpos.le
      rw [div_mul_cancel₀ _ hpos.ne'] at this
      exact this
  have hct := crit_total H (pL δ n) (pY_lt_two_pow δ n) (by omega) hRn
  have hs : 1 < eS δ := by unfold eS; linarith
  have hα : 0 ≤ eA ℓ δ := by
    unfold eA eS Poin.kw
    have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ2
    linarith
  have hsα : eS δ + eA ℓ δ = Poin.kw ℓ - 1 / 2 - δ / 16 := by unfold eA; ring
  have hph : ∀ p ∈ Ps, ‖Poin.Phat ℓ n (8 * p)‖ ≤
      2 + 2 * (eLo ℓ δ C pp qq n + ‖critSum ℓ n p (py δ n) (pY δ n)‖ + eHi ℓ δ C n) := by
    intro p hp
    obtain ⟨hpr, hpn, hP0p, -⟩ := mem_levels hp
    have := phat_level_bound ℓ n p (py δ n) (pY δ n) (pP0 n) hℓ2 hn0 hpr hpn hP0p hP0 hpq hy2pi
      (by omega) hnY (by omega) C (δ / 16) (eS δ) (eA ℓ δ) hC (by positivity) hs hα hsα hτ
    unfold eLo eHi eZP
    exact this
  have hPs' : ∀ p ∈ Ps, p.Prime ∧ p ≠ 2 ∧ p ≤ 4 * pP0 n := by
    intro p hp
    obtain ⟨hpr, hpn, -, hp4⟩ := mem_levels hp
    exact ⟨hpr, fun h => hpn (h ▸ dvd_mul_right 2 n), hp4⟩
  have hav := weyl_avg u ℓ n hn0 Cw hCw hWsq Ps (4 * pP0 n) hPs' (eLo ℓ δ C pp qq n) (eHi ℓ δ C n)
    (eCT ℓ δ C pp qq n) (fun p => ‖critSum ℓ n p (py δ n) (pY δ n)‖) hph hct
  have hc : (0 : ℝ) < Ps.card := by exact_mod_cast hcard
  refine le_of_mul_le_mul_right (hav.trans (le_of_eq ?_)) hc
  unfold eE
  rw [show levels n (pP0 n) = Ps from rfl]
  field_simp

end ThreeSquares
