/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.WeylCap

/-! # Finite-degree Weyl bounds suffice for each fixed cap

The cap kernel uses only degrees up to its fixed degree K. A positive saving
may depend on K; no uniform saving over all harmonic degrees is assumed.
-/

@[expose] public section

namespace ThreeSquares.Duke
open MvPolynomial Finset

/-- Harmonic Weyl estimates through a specified finite degree. -/
def WeylBoundThrough (S : Set ℕ) (K : ℕ) (η : ℝ) : Prop :=
  ∀ (d : ℕ) (P : R3), 1 ≤ d → d ≤ K → P.IsHomogeneous d → lap P = 0 →
    ∃ C : ℝ, ∀ t ∈ S, 1 ≤ t → |weylSum P t| ≤ C * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η)

theorem weyl_hom_through {S : Set ℕ} {η : ℝ} {K : ℕ} (hW : WeylBoundThrough S K η) :
    ∀ (d : ℕ) (P : R3), d ≤ K → P.IsHomogeneous d → ∃ C : ℝ, ∀ t ∈ S, 1 ≤ t →
      |weylSum P t - kap d P * (t : ℝ) ^ ((d : ℝ) / 2) * r3 t| ≤
        C * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η)
  | d, P, hdK, hP => by
    by_cases hd2 : d < 2
    · rcases Nat.lt_succ_iff.mp hd2 |>.lt_or_eq with h0 | h1
      · -- `d = 0`: a constant
        have h0 : d = 0 := by omega
        subst h0
        rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hP
        refine ⟨0, fun t _ _ => ?_⟩
        rw [hP, weylSum_C]
        simp [kap]
      · subst h1
        obtain ⟨C, hC⟩ := hW 1 P le_rfl (by omega) hP (lap_eq_zero_of_lt hP (by norm_num))
        refine ⟨C, fun t ht ht1 => ?_⟩
        have : kap 1 P = 0 := by simp [kap]
        rw [this, zero_mul, zero_mul, sub_zero]
        exact hC t ht ht1
    · push Not at hd2
      obtain ⟨H, Q, hH, hHl, hQ, rfl⟩ := fischer hP hd2
      obtain ⟨CH, hCH⟩ := hW d H (by omega) hdK hH hHl
      obtain ⟨CQ, hCQ⟩ := weyl_hom_through hW (d - 2) Q (by omega) hQ
      refine ⟨CH + CQ, fun t ht ht1 => ?_⟩
      have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
      have hkap : kap d (H + nrm * Q) = kap (d - 2) Q := by
        rw [kap_add, kap_harm (by omega) hHl, zero_add]
        have := kap_nrm_mul hQ
        rwa [show d - 2 + 2 = d by omega] at this
      rw [weylSum_add, weylSum_nrm_mul, hkap]
      have hpow : (t : ℝ) ^ ((d : ℝ) / 2) = t * (t : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2) := by
        rw [show (d : ℝ) / 2 = 1 + ((d - 2 : ℕ) : ℝ) / 2 by rw [Nat.cast_sub hd2]; push_cast; ring,
          Real.rpow_add htpos, Real.rpow_one]
      have hpow2 : (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η) =
          t * (t : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2 + 1 / 2 - η) := by
        rw [show (d : ℝ) / 2 + 1 / 2 - η = 1 + (((d - 2 : ℕ) : ℝ) / 2 + 1 / 2 - η) by
          rw [Nat.cast_sub hd2]; push_cast; ring, Real.rpow_add htpos, Real.rpow_one]
      have e : weylSum H t + t * weylSum Q t - kap (d - 2) Q * (t : ℝ) ^ ((d : ℝ) / 2) * r3 t =
          weylSum H t + t * (weylSum Q t - kap (d - 2) Q *
            (t : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2) * r3 t) := by
        rw [hpow]; ring
      rw [e]
      have h1 := hCH t ht ht1
      have h2 := hCQ t ht ht1
      calc |weylSum H t + t * (weylSum Q t - kap (d - 2) Q *
              (t : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2) * r3 t)|
          ≤ |weylSum H t| + t * |weylSum Q t - kap (d - 2) Q *
              (t : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2) * r3 t| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_of_pos htpos]
        _ ≤ CH * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η) +
            t * (CQ * (t : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2 + 1 / 2 - η)) := by
            gcongr
        _ = (CH + CQ) * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η) := by
            rw [hpow2]; ring
  termination_by d => d
  decreasing_by omega


theorem kern_asymp_through {S : Set ℕ} {η : ℝ} {K : ℕ}
    (hW : WeylBoundThrough S K η) (u : Fin 3 → ℝ) (hu : ∑ i, u i ^ 2 = 1) :
    ∃ C : ℝ, ∀ t ∈ S, 1 ≤ t →
      |∑ x ∈ reps3 t, kern u K t x - r3 t / ((K : ℝ) + 1)| ≤ C * (t : ℝ) ^ ((1 : ℝ) / 2 - η) := by
  have hj : ∀ j, ∃ C : ℝ, ∀ t ∈ S, 1 ≤ t → j ≤ K →
      |weylSum (lin u ^ j) t - kap j (lin u ^ j) * (t : ℝ) ^ ((j : ℝ) / 2) * r3 t| ≤
        C * (t : ℝ) ^ ((j : ℝ) / 2 + 1 / 2 - η) :=
    fun j => by
      by_cases hle : j ≤ K
      · obtain ⟨C, hC⟩ := weyl_hom_through hW j _ hle (by simpa using (isHomogeneous_lin u).pow j)
        exact ⟨C, fun t ht ht1 _ => hC t ht ht1⟩
      · exact ⟨0, fun _ _ _ h => False.elim (hle h)⟩
  choose C hC using hj
  refine ⟨∑ j ∈ range (K + 1), ((K.choose j : ℝ) / 2 ^ K) * |C j|, fun t ht ht1 => ?_⟩
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr htpos).ne'
  have hsq : ∀ j : ℕ, (Real.sqrt t)⁻¹ ^ j * (t : ℝ) ^ ((j : ℝ) / 2) = 1 := by
    intro j
    have : (t : ℝ) ^ ((j : ℝ) / 2) = Real.sqrt t ^ j := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul htpos.le]; ring_nf
    rw [this, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hs)]
  have hsq2 : ∀ j : ℕ, (Real.sqrt t)⁻¹ ^ j * (t : ℝ) ^ ((j : ℝ) / 2 + 1 / 2 - η) =
      (t : ℝ) ^ ((1 : ℝ) / 2 - η) := by
    intro j
    rw [show (j : ℝ) / 2 + 1 / 2 - η = (j : ℝ) / 2 + (1 / 2 - η) by ring,
      Real.rpow_add htpos, ← mul_assoc, hsq, one_mul]
  rw [kern_sum u K t ht1, show (r3 t : ℝ) / ((K : ℝ) + 1) = r3 t * (1 / ((K : ℝ) + 1)) by ring,
    ← kern_main u hu K, mul_sum, ← sum_sub_distrib]
  have e : ∀ j ∈ range (K + 1), ((K.choose j : ℝ) / 2 ^ K) *
      ((Real.sqrt t)⁻¹ ^ j * weylSum (lin u ^ j) t) - (r3 t : ℝ) *
      (((K.choose j : ℝ) / 2 ^ K) * kap j (lin u ^ j)) =
      ((K.choose j : ℝ) / 2 ^ K) * ((Real.sqrt t)⁻¹ ^ j *
        (weylSum (lin u ^ j) t - kap j (lin u ^ j) * (t : ℝ) ^ ((j : ℝ) / 2) * r3 t)) := by
    intro j _
    have := hsq j
    linear_combination (((K.choose j : ℝ) / 2 ^ K) * kap j (lin u ^ j) * r3 t) * this
  rw [sum_congr rfl e, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
  have hpos : 0 ≤ (K.choose j : ℝ) / 2 ^ K := by positivity
  have hinv : 0 ≤ (Real.sqrt t)⁻¹ ^ j := by positivity
  rw [abs_mul, abs_of_nonneg hpos, abs_mul, abs_of_nonneg hinv,
    mul_assoc ((K.choose j : ℝ) / 2 ^ K) |C j|]
  refine mul_le_mul_of_nonneg_left ?_ hpos
  calc (Real.sqrt t)⁻¹ ^ j * |weylSum (lin u ^ j) t - kap j (lin u ^ j) *
        (t : ℝ) ^ ((j : ℝ) / 2) * r3 t|
      ≤ (Real.sqrt t)⁻¹ ^ j * (|C j| * (t : ℝ) ^ ((j : ℝ) / 2 + 1 / 2 - η)) := by
        refine mul_le_mul_of_nonneg_left ((hC j t ht ht1 (Nat.le_of_lt_succ (mem_range.mp hj))).trans ?_) hinv
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg htpos.le _)
    _ = |C j| * (t : ℝ) ^ ((1 : ℝ) / 2 - η) := by rw [← hsq2 j]; ring


theorem dukeSquarefree_of_degreewise
    (hW : ∀ K : ℕ, ∃ η > 0, WeylBoundThrough {t | Squarefree t ∧ t % 8 = 3} K η)
    (hL : ∀ η : ℝ, 0 < η → ∃ c > 0, ∃ T : ℕ, ∀ t : ℕ, T ≤ t → Squarefree t → t % 8 = 3 →
      c * (t : ℝ) ^ ((1 : ℝ) / 2 - η) ≤ r3 t) :
    DukeSquarefree := by
  intro u hu ε hε
  set ε₁ := min ε 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  set ρ := 1 - ε₁ ^ 2 / 4 with hρ
  have hρ0 : 0 ≤ ρ := by nlinarith
  have hρ1 : ρ < 1 := by have := pow_pos hε₁0 2; linarith
  obtain ⟨K, hK⟩ := exists_K_small hρ0 hρ1
  obtain ⟨η, hη, hWK⟩ := hW K
  obtain ⟨C, hC⟩ := kern_asymp_through hWK u hu
  obtain ⟨c, hc, T, hT⟩ := hL (η / 2) (by positivity)
  set B := 2 * ((K : ℝ) + 1) * |C| / c with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (B ^ (2 / η))
  refine ⟨max (max T (N + 1)) 1, fun t ht hsq ht8 => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
  have htT : T ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htN : N + 1 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  have hS : t ∈ {t | Squarefree t ∧ t % 8 = 3} := ⟨hsq, ht8⟩
  by_contra hno
  push Not at hno
  -- every point is outside the smaller cap
  have hout : ∀ x ∈ reps3 t, kern u K t x ≤ ρ ^ K := by
    intro x hx
    refine (kern_bounds u hu K t ht1 hx ε₁).2 (fun hnear => ?_) hε₁0.le
    refine hno x ((mem_reps3 t x).mp hx) (fun i => (hnear i).trans ?_)
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
  have hsum_le : ∑ x ∈ reps3 t, kern u K t x ≤ ρ ^ K * r3 t := by
    calc ∑ x ∈ reps3 t, kern u K t x ≤ ∑ _x ∈ reps3 t, ρ ^ K := sum_le_sum hout
      _ = ρ ^ K * r3 t := by rw [sum_const, nsmul_eq_mul, r3, mul_comm]
  have hasym := hC t hS ht1
  have hlow := hT t htT hsq ht8
  have hr3 : 0 ≤ (r3 t : ℝ) := by positivity
  have hM : ρ ^ K < 1 / (2 * ((K : ℝ) + 1)) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  -- `r₃ (1/(K+1) − ρ^K) ≤ |C| t^{1/2 − η}`
  have h1 : (r3 t : ℝ) / ((K : ℝ) + 1) - |C| * (t : ℝ) ^ ((1 : ℝ) / 2 - η) ≤ ρ ^ K * r3 t := by
    have := (abs_le.mp hasym).1
    have hCt : C * (t : ℝ) ^ ((1 : ℝ) / 2 - η) ≤ |C| * (t : ℝ) ^ ((1 : ℝ) / 2 - η) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg htpos.le _)
    linarith
  have h2 : (r3 t : ℝ) / (2 * ((K : ℝ) + 1)) ≤ |C| * (t : ℝ) ^ ((1 : ℝ) / 2 - η) := by
    have : (r3 t : ℝ) / (2 * ((K : ℝ) + 1)) = (r3 t : ℝ) / ((K : ℝ) + 1) -
        (r3 t : ℝ) * (1 / (2 * ((K : ℝ) + 1))) := by field_simp; ring
    rw [this]
    nlinarith
  have hsplit : (t : ℝ) ^ ((1 : ℝ) / 2 - η / 2) =
      (t : ℝ) ^ (η / 2) * (t : ℝ) ^ ((1 : ℝ) / 2 - η) := by
    rw [← Real.rpow_add htpos]; ring_nf
  have hpos2 : 0 < (t : ℝ) ^ ((1 : ℝ) / 2 - η) := Real.rpow_pos_of_pos htpos _
  have h3 : c * (t : ℝ) ^ (η / 2) ≤ 2 * ((K : ℝ) + 1) * |C| := by
    have h4 : c * (t : ℝ) ^ ((1 : ℝ) / 2 - η / 2) ≤
        2 * ((K : ℝ) + 1) * (|C| * (t : ℝ) ^ ((1 : ℝ) / 2 - η)) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((K : ℝ) + 1))).mp h2
      linarith
    rw [hsplit] at h4
    have : (c * (t : ℝ) ^ (η / 2)) * (t : ℝ) ^ ((1 : ℝ) / 2 - η) ≤
        (2 * ((K : ℝ) + 1) * |C|) * (t : ℝ) ^ ((1 : ℝ) / 2 - η) := by linarith
    exact le_of_mul_le_mul_right this hpos2
  have h5 : (t : ℝ) ^ (η / 2) ≤ B := by
    rw [hB, le_div_iff₀ hc]; linarith
  -- but `t > B^{2/η}`
  have h6 : B < (t : ℝ) ^ (η / 2) := by
    have htB : B ^ (2 / η) < t := by
      have : (N : ℝ) + 1 ≤ t := by exact_mod_cast htN
      linarith
    have := Real.rpow_lt_rpow (Real.rpow_nonneg hB0 _) htB (by positivity : 0 < η / 2)
    rwa [← Real.rpow_mul hB0, show 2 / η * (η / 2) = 1 by field_simp, Real.rpow_one] at this
  linarith


end ThreeSquares.Duke
