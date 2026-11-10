/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.ClassSum
public import DukeH1.SmoothSum

/-!
# The critical sums, averaged over the levels

`∑_p ‖critSum_p‖ ≤ √2 (2 R^{11/4} (L+1)² σ P W₀ 4Y/P₀ + 2 R^{−1/4} |𝒫| W₀ (Y/P₀)(1 + log Y)) ·
∏_{ℓ ∣ 2n} (1 − ℓ^{−1/4})^{−1}` (`crit_total`): classes `r ≤ R` by the block bounds, `r > R` trivially.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open Finset

theorem sqrt_mul_sq_le (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    Real.sqrt r * r ^ 2 ≤ R ^ (11 / 4 : ℝ) * r ^ (-(1 / 4 : ℝ)) := by
  have e : Real.sqrt r * r ^ 2 = r ^ (11 / 4 : ℝ) * r ^ (-(1 / 4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast r 2, ← Real.rpow_add hr, ← Real.rpow_add hr]
    norm_num
  rw [e]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hr.le hrR (by norm_num)) (by positivity)

theorem sqrt_div_le (r R : ℝ) (hR : 0 < R) (hRr : R ≤ r) :
    Real.sqrt r / r ≤ R ^ (-(1 / 4 : ℝ)) * r ^ (-(1 / 4 : ℝ)) := by
  have hr : 0 < r := lt_of_lt_of_le hR hRr
  have e : Real.sqrt r / r = r ^ (-(1 / 4 : ℝ)) * r ^ (-(1 / 4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hr, div_eq_iff hr.ne', ← Real.rpow_add_one hr.ne']
    norm_num
  rw [e]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hR hRr (by norm_num)) (by positivity)

theorem one_lt_div_gcd (n r : ℕ) (hr0 : 0 < r) (hrn : r < n) : 1 < n / Nat.gcd n r := by
  have hg : Nat.gcd n r ∣ n := Nat.gcd_dvd_left n r
  have hgr : Nat.gcd n r ≤ r := Nat.le_of_dvd hr0 (Nat.gcd_dvd_right n r)
  have e := Nat.div_mul_cancel hg
  by_contra hc
  push_neg at hc
  have : n ≤ Nat.gcd n r := by
    calc n = n / Nat.gcd n r * Nat.gcd n r := e.symm
      _ ≤ 1 * Nat.gcd n r := Nat.mul_le_mul_right _ hc
      _ = Nat.gcd n r := one_mul _
  omega

/-- **The averaged critical sums.** -/
theorem crit_total {Ps : Finset ℕ} {P₀ P ℓ n y Y B₀ K R : ℕ} {Wk1 Wk2 : ℕ → ℂ}
    {W₀ W₁ C ε Λ Umax X σ : ℝ} (H : BlockHyp Ps P₀ P ℓ n y Y B₀ K R Wk1 Wk2 W₀ W₁ C ε Λ Umax X σ)
    (L : ℕ) (hL : Y < 2 ^ L) (hR : 0 < R) (hRn : R < n) :
    ∑ p ∈ Ps, ‖critSum ℓ n p y Y‖ ≤
      Real.sqrt 2 * (2 * (R : ℝ) ^ (11 / 4 : ℝ) * (((L : ℝ) + 1) ^ 2 * (σ * ((P : ℝ) * W₀ * (4 * Y / P₀)))) +
        2 * (R : ℝ) ^ (-(1 / 4 : ℝ)) * (Ps.card * (W₀ * ((Y : ℝ) / P₀ * (1 + Real.log Y))))) *
      ∏ q ∈ (2 * n).primeFactors, (1 - (q : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := by
  classical
  have hW0 := H.hW1.W₀_nonneg
  have hn0 : n ≠ 0 := by rintro rfl; have := H.hn4; simp at this
  set Q' : ℝ := ((L : ℝ) + 1) ^ 2 * (σ * ((P : ℝ) * W₀ * (4 * Y / P₀))) with hQ'
  set V : ℝ := Ps.card * (W₀ * ((Y : ℝ) / P₀ * (1 + Real.log Y))) with hV
  set M : ℝ := Real.sqrt 2 * (2 * (R : ℝ) ^ (11 / 4 : ℝ) * Q' + 2 * (R : ℝ) ^ (-(1 / 4 : ℝ)) * V) with hM
  have hQ'0 : 0 ≤ Q' := mul_nonneg (by positivity) H.rhs_nonneg
  have hlogY : 0 ≤ Real.log Y := Real.log_natCast_nonneg Y
  have hV0 : 0 ≤ V := by positivity
  set Rset := (range (Y + 1)).filter (fun r => Smooth (S2 n) r ∧ 8 ∣ r)
  set G : ℕ → ℝ := fun r => ∑ t₁ ∈ range r, ∑ t₂ ∈ range r,
    ((∑ p ∈ Ps, ‖Asum n p y Y r t₁ t₂ (W1 ℓ n) (hInv (-4 * n) r)‖) +
      ∑ p ∈ Ps, ‖Asum n p y Y r t₁ t₂ (W2 ℓ n) (hInv (4 * n) r)‖)
  -- step 1: exchange the sums
  have step1 : ∑ p ∈ Ps, ‖critSum ℓ n p y Y‖ ≤ ∑ r ∈ Rset, Real.sqrt (2 * r) * G r := by
    refine (sum_le_sum fun p hp => critSum_le ℓ n p y Y (H.hPs p hp).1 (H.hPs p hp).2.1).trans
      (le_of_eq ?_)
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    simp only [G, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun t₁ _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun t₂ _ => ?_
    rw [← mul_sum, sum_add_distrib]
  -- step 2: the pointwise bound
  have step2 : ∀ r ∈ Rset, Real.sqrt (2 * r) * G r ≤ M * (r : ℝ) ^ (-(1 / 4 : ℝ)) := by
    intro r hr
    simp only [Rset, mem_filter, mem_range] at hr
    obtain ⟨hrY, hrs, h8⟩ := hr
    rcases Nat.eq_zero_or_pos r with h0 | hr0
    · subst h0
      simp [G]
    have hrR0 : (0 : ℝ) < r := by exact_mod_cast hr0
    have hs2 : Real.sqrt (2 * r) = Real.sqrt 2 * Real.sqrt r := Real.sqrt_mul (by norm_num) _
    have hr4 : 0 ≤ (r : ℝ) ^ (-(1 / 4 : ℝ)) := by positivity
    by_cases hrR : r ≤ R
    · have hn₀ := one_lt_div_gcd n r hr0 (lt_of_le_of_lt hrR hRn)
      have hG : G r ≤ r * (r * (Q' + Q')) := by
        calc G r ≤ ∑ t₁ ∈ range r, ∑ t₂ ∈ range r, (Q' + Q') :=
              sum_le_sum fun t₁ ht₁ => sum_le_sum fun t₂ ht₂ => add_le_add
                (class_bound_A H r t₁ t₂ L h8 hr0 hrs (mem_range.mp ht₁) (mem_range.mp ht₂) hn₀ hrR hL)
                (class_bound_B H r t₁ t₂ L h8 hr0 hrs (mem_range.mp ht₁) (mem_range.mp ht₂) hn₀ hrR hL)
          _ = r * (r * (Q' + Q')) := by simp only [sum_const, card_range, nsmul_eq_mul]
      have hsr := sqrt_mul_sq_le r R hrR0 (by exact_mod_cast hrR)
      calc Real.sqrt (2 * r) * G r ≤ Real.sqrt (2 * r) * (r * (r * (Q' + Q'))) :=
            mul_le_mul_of_nonneg_left hG (Real.sqrt_nonneg _)
        _ = Real.sqrt 2 * 2 * Q' * (Real.sqrt r * (r : ℝ) ^ 2) := by rw [hs2]; ring
        _ ≤ Real.sqrt 2 * 2 * Q' * ((R : ℝ) ^ (11 / 4 : ℝ) * (r : ℝ) ^ (-(1 / 4 : ℝ))) :=
            mul_le_mul_of_nonneg_left hsr (by positivity)
        _ = Real.sqrt 2 * (2 * (R : ℝ) ^ (11 / 4 : ℝ) * Q') * (r : ℝ) ^ (-(1 / 4 : ℝ)) := by ring
        _ ≤ M * (r : ℝ) ^ (-(1 / 4 : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ hr4
            refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
            have : 0 ≤ 2 * (R : ℝ) ^ (-(1 / 4 : ℝ)) * V := by positivity
            linarith
    · push_neg at hrR
      have hWb1 : ∀ c, y < c → c ≤ Y → ‖W1 ℓ n c‖ ≤ W₀ := fun c h1 h2 => by
        rw [H.hA1 c h1 h2]; exact H.hW1.bound c
      have hWb2 : ∀ c, y < c → c ≤ Y → ‖W2 ℓ n c‖ ≤ W₀ := fun c h1 h2 => by
        rw [H.hA2 c h1 h2]; exact H.hW2.bound c
      have hP₀R : (0 : ℝ) < P₀ := by exact_mod_cast H.hP₀
      have hpbound : ∀ p ∈ Ps, W₀ * ((Y : ℝ) / (r * p) * (1 + Real.log Y)) ≤
          W₀ * ((Y : ℝ) / (r * P₀) * (1 + Real.log Y)) := by
        intro p hp
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by linarith)) hW0
        refine div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast (H.hPs p hp).2.2.1) hrR0.le
      have hone : ∀ (W : ℕ → ℂ) (h : ℕ → ℤ), (∀ c, y < c → c ≤ Y → ‖W c‖ ≤ W₀) →
          ∑ t₁ ∈ range r, ∑ t₂ ∈ range r, ∑ p ∈ Ps, ‖Asum n p y Y r t₁ t₂ W h‖ ≤
            Ps.card * (W₀ * ((Y : ℝ) / (r * P₀) * (1 + Real.log Y))) := by
        intro W h hW
        rw [(sum_congr rfl fun t₁ _ => sum_comm).trans sum_comm]
        calc ∑ p ∈ Ps, ∑ t₁ ∈ range r, ∑ t₂ ∈ range r, ‖Asum n p y Y r t₁ t₂ W h‖
            ≤ ∑ p ∈ Ps, W₀ * ((Y : ℝ) / (r * P₀) * (1 + Real.log Y)) :=
              sum_le_sum fun p hp => (asum_trivial n p y Y r hr0 (H.hPs p hp).1.pos W h W₀ hW0 hW).trans
                (hpbound p hp)
          _ = Ps.card * (W₀ * ((Y : ℝ) / (r * P₀) * (1 + Real.log Y))) := by
              rw [sum_const, nsmul_eq_mul]
      have hG : G r ≤ 2 * (Ps.card * (W₀ * ((Y : ℝ) / (r * P₀) * (1 + Real.log Y)))) := by
        have e : G r = ∑ t₁ ∈ range r, ∑ t₂ ∈ range r, ∑ p ∈ Ps, ‖Asum n p y Y r t₁ t₂ (W1 ℓ n) (hInv (-4 * n) r)‖ +
            ∑ t₁ ∈ range r, ∑ t₂ ∈ range r, ∑ p ∈ Ps, ‖Asum n p y Y r t₁ t₂ (W2 ℓ n) (hInv (4 * n) r)‖ := by
          simp only [G, ← sum_add_distrib]
        rw [e, two_mul]
        exact add_le_add (hone _ _ hWb1) (hone _ _ hWb2)
      have hsd := sqrt_div_le r R (by exact_mod_cast hR) (by exact_mod_cast hrR.le)
      have e2 : Real.sqrt (2 * r) * (2 * (Ps.card * (W₀ * ((Y : ℝ) / (r * P₀) * (1 + Real.log Y))))) =
          Real.sqrt 2 * 2 * V * (Real.sqrt r / r) := by
        rw [hs2, hV]; field_simp
      calc Real.sqrt (2 * r) * G r
          ≤ Real.sqrt (2 * r) * (2 * (Ps.card * (W₀ * ((Y : ℝ) / (r * P₀) * (1 + Real.log Y))))) :=
            mul_le_mul_of_nonneg_left hG (Real.sqrt_nonneg _)
        _ = Real.sqrt 2 * 2 * V * (Real.sqrt r / r) := e2
        _ ≤ Real.sqrt 2 * 2 * V * ((R : ℝ) ^ (-(1 / 4 : ℝ)) * (r : ℝ) ^ (-(1 / 4 : ℝ))) :=
            mul_le_mul_of_nonneg_left hsd (by positivity)
        _ = Real.sqrt 2 * (2 * (R : ℝ) ^ (-(1 / 4 : ℝ)) * V) * (r : ℝ) ^ (-(1 / 4 : ℝ)) := by ring
        _ ≤ M * (r : ℝ) ^ (-(1 / 4 : ℝ)) := by
            refine mul_le_mul_of_nonneg_right ?_ hr4
            refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
            have : 0 ≤ 2 * (R : ℝ) ^ (11 / 4 : ℝ) * Q' := by positivity
            linarith
  -- step 3: the smooth sum
  have hM0 : 0 ≤ M := by positivity
  have step3 : ∑ r ∈ Rset, M * (r : ℝ) ^ (-(1 / 4 : ℝ)) ≤
      M * ∏ q ∈ (2 * n).primeFactors, (1 - (q : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := by
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hM0
    rw [← sum_filter_of_ne (p := fun r => 0 < r) (fun r _ hne => by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0; simp at hne
      · exact h0)]
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity))
      (sum_smooth_le (1 / 4) (by norm_num) (2 * n).primeFactors (fun q hq => Nat.prime_of_mem_primeFactors hq)
        (Y + 1))
    intro r hr
    simp only [Rset, mem_filter, mem_range] at hr ⊢
    refine ⟨hr.1.1, hr.2, fun q hq hqr => ?_⟩
    exact Nat.mem_primeFactors.mpr ⟨hq, hr.1.2.1 q hq hqr, by omega⟩
  calc ∑ p ∈ Ps, ‖critSum ℓ n p y Y‖ ≤ ∑ r ∈ Rset, Real.sqrt (2 * r) * G r := step1
    _ ≤ ∑ r ∈ Rset, M * (r : ℝ) ^ (-(1 / 4 : ℝ)) := sum_le_sum step2
    _ ≤ M * ∏ q ∈ (2 * n).primeFactors, (1 - (q : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := step3

end ThreeSquares
