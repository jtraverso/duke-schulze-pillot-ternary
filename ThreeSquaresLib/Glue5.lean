/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Glue4

/-!
# The per-level inequality (`critSum_le`)
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset

theorem Asum_eq_zero_of_not_unit (n p y Y r t₁ t₂ : ℕ) (W : ℕ → ℂ) (h : ℕ → ℤ) (hr : Smooth (S2 n) r)
    (ht : ¬ IsUnit ((t₁ : ZMod r)) ∨ ¬ IsUnit ((t₂ : ZMod r))) : Asum n p y Y r t₁ t₂ W h = 0 := by
  unfold Asum
  refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
  simp only [Finset.mem_filter] at ha hb
  rcases ht with ht | ht
  · have : ¬ IsUnit ((a : ZMod r)) := by
      have e : ((a : ZMod r)) = (t₁ : ZMod r) := by rw [← ha.2, ZMod.natCast_mod]
      rw [e]; exact ht
    rw [chiR_eq_zero_of_not_unit n r a hr this]; ring
  · have : ¬ IsUnit ((b : ZMod r)) := by
      have e : ((b : ZMod r)) = (t₂ : ZMod r) := by rw [← hb.2, ZMod.natCast_mod]
      rw [e]; exact ht
    rw [chiR_eq_zero_of_not_unit n r b hr this]; ring

theorem norm_Phi_Asum_le (n p y Y r t₁ t₂ : ℕ) (hr : Smooth (S2 n) r) (h8 : 8 ∣ r) (hp : p.Prime)
    (hpn : ¬ p ∣ 2 * n) (hh : ℤ) (W : ℕ → ℂ) (h : ℕ → ℤ) :
    ‖Phi n r hh (p * t₁ * t₂) * Asum n p y Y r t₁ t₂ W h‖ ≤
      Real.sqrt (2 * r) * ‖Asum n p y Y r t₁ t₂ W h‖ := by
  obtain ⟨m, rfl⟩ : 4 ∣ r := (by norm_num : 4 ∣ 8).trans h8
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; exfalso
      -- `0` is not smooth: a prime not dividing `2n` divides `0`
      obtain ⟨q, hq1, hq⟩ := Nat.exists_infinite_primes (2 * n + 1)
      have := hr q hq (dvd_zero q)
      have hpos : 0 < 2 * n ∨ 2 * n = 0 := by omega
      rcases hpos with hpos | hz
      · exact absurd (Nat.le_of_dvd hpos this) (by omega)
      · -- `n = 0`: then `p ∣ 0 = 2 n`
        exact hpn (by rw [hz]; exact dvd_zero p)
    · exact h0
  by_cases hu : IsUnit (((p * t₁ * t₂ : ℕ) : ZMod (4 * m)))
  · rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    unfold Phi
    rw [norm_mul]
    have h1 := norm_Gam_le n m (p * t₁ * t₂) hm hu
    have h2 := norm_rph_le (4 * m) hh ((p * t₁ * t₂ : ℕ) : ℤ)
    push_cast at h1 ⊢
    calc ‖Gam n (4 * m) (p * t₁ * t₂)‖ * ‖rph (4 * m) hh ((p * t₁ * t₂ : ℕ) : ℤ)‖
        ≤ Real.sqrt (2 * (4 * m)) * 1 := mul_le_mul h1 h2 (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [mul_one]
  · have ht : ¬ IsUnit ((t₁ : ZMod (4 * m))) ∨ ¬ IsUnit ((t₂ : ZMod (4 * m))) := by
      by_contra hc
      push_neg at hc
      apply hu
      have hpu : IsUnit ((p : ZMod (4 * m))) := by
        rw [ZMod.isUnit_iff_coprime]
        exact coprime_of_smooth_rough hr (rough_prime hp hpn) |>.symm
      push_cast
      exact (hpu.mul hc.1).mul hc.2
    rw [Asum_eq_zero_of_not_unit n p y Y (4 * m) t₁ t₂ W h hr ht]
    simp

theorem Phi_mul_mod (n r p : ℕ) (hh : ℤ) (a b : ℕ) :
    Phi n r hh (p * a * b) = Phi n r hh (p * (a % r) * (b % r)) := by
  rw [Phi_mod, Phi_mod n r hh (p * (a % r) * (b % r))]
  congr 1
  exact Nat.ModEq.mul (Nat.ModEq.mul_left p (Nat.mod_modEq a r).symm) (Nat.mod_modEq b r).symm

theorem caseA_bound (ℓ n p y Y r : ℕ) (hp : p.Prime) (hpn : ¬ p ∣ 2 * n) (hrs : Smooth (S2 n) r)
    (h8 : 8 ∣ r) (hr0 : 0 < r) :
    ‖∑ a ∈ range (Y + 1), ∑ b ∈ range (Y + 1),
        (if p ∣ a then (if a.Coprime b ∧ y < r * a * b ∧ r * a * b ≤ Y then TermG ℓ n r a b else 0) else 0)‖ ≤
      ∑ t₁ ∈ range r, ∑ t₂ ∈ range r, Real.sqrt (2 * r) *
        ‖Asum n p y Y r t₁ t₂ (W1 ℓ n) (hInv (-4 * n) r)‖ := by
  classical
  set G : ℕ → ℕ → ℂ := fun a b => if a.Coprime b ∧ y < r * a * b ∧ r * a * b ≤ Y then TermG ℓ n r a b else 0
  have h1 : (∑ a ∈ range (Y + 1), ∑ b ∈ range (Y + 1), (if p ∣ a then G a b else 0)) =
      ∑ a' ∈ range (Y + 1), ∑ b ∈ range (Y + 1), G (p * a') b := by
    have e1 : (∑ a ∈ range (Y + 1), ∑ b ∈ range (Y + 1), (if p ∣ a then G a b else 0)) =
        ∑ a ∈ (range (Y + 1)).filter (fun a => p ∣ a), ∑ b ∈ range (Y + 1), G a b := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
    rw [e1, sum_dvd_mul Y p hp.pos (fun a => ∑ b ∈ range (Y + 1), G a b)]
    refine Finset.sum_subset (fun a' ha' => Finset.mem_range.mpr (by
      have := Finset.mem_range.mp ha'
      have : Y / p ≤ Y := Nat.div_le_self _ _
      omega)) fun a' _ ha' => Finset.sum_eq_zero fun b _ => ?_
    simp only [G]
    rw [if_neg]
    rintro ⟨-, h1, h2⟩
    have hlt : Y / p < a' := by simpa using ha'
    have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
    have : Y < p * a' := by
      have := (Nat.div_lt_iff_lt_mul hp.pos).mp hlt; linarith
    have : p * a' ≤ r * (p * a') * b := by
      calc p * a' ≤ r * (p * a') := Nat.le_mul_of_pos_left _ hr0
        _ ≤ r * (p * a') * b := Nat.le_mul_of_pos_right _ hb
    omega
  rw [h1]
  have h2 : ∀ a' b, G (p * a') b = chiR n p * (Phi n r (-2 * n) (p * a' * b) *
      (chiR n a' * chiR n b * ker1 r y Y (W1 ℓ n) (hInv (-4 * n) r b) p a' b)) := fun a' b =>
    caseA_term ℓ n p y Y r a' b hp hpn hrs hr0
  conv_lhs => rw [Finset.sum_congr rfl (fun a' _ => Finset.sum_congr rfl (fun b _ => h2 a' b))]
  conv_lhs => simp only [← Finset.mul_sum]
  rw [sum_class_split r hr0 _ _ (fun a b => Phi n r (-2 * n) (p * a * b))
    (fun a b => chiR n a * chiR n b * ker1 r y Y (W1 ℓ n) (hInv (-4 * n) r b) p a b)
    (fun a b => Phi_mul_mod n r p _ a b)]
  rw [norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (norm_chiR_le n p)).trans ?_
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t₁ _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t₂ _ => ?_)
  exact norm_Phi_Asum_le n p y Y r t₁ t₂ hrs h8 hp hpn _ _ _

theorem caseB_bound (ℓ n p y Y r : ℕ) (hp : p.Prime) (hpn : ¬ p ∣ 2 * n) (hrs : Smooth (S2 n) r)
    (h8 : 8 ∣ r) (hr0 : 0 < r) :
    ‖∑ a ∈ range (Y + 1), ∑ b ∈ range (Y + 1),
        (if p ∣ b then (if a.Coprime b ∧ y < r * a * b ∧ r * a * b ≤ Y then TermG ℓ n r a b else 0) else 0)‖ ≤
      ∑ t₁ ∈ range r, ∑ t₂ ∈ range r, Real.sqrt (2 * r) *
        ‖Asum n p y Y r t₁ t₂ (W2 ℓ n) (hInv (4 * n) r)‖ := by
  classical
  set G : ℕ → ℕ → ℂ := fun a b => if a.Coprime b ∧ y < r * a * b ∧ r * a * b ≤ Y then TermG ℓ n r a b else 0
  have h1 : (∑ a ∈ range (Y + 1), ∑ b ∈ range (Y + 1), (if p ∣ b then G a b else 0)) =
      ∑ a ∈ range (Y + 1), ∑ b' ∈ range (Y + 1), G a (p * b') := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have e1 : (∑ b ∈ range (Y + 1), (if p ∣ b then G a b else 0)) =
        ∑ b ∈ (range (Y + 1)).filter (fun b => p ∣ b), G a b := by rw [Finset.sum_filter]
    rw [e1, sum_dvd_mul Y p hp.pos (fun b => G a b)]
    refine Finset.sum_subset (fun b' hb' => Finset.mem_range.mpr (by
      have := Finset.mem_range.mp hb'
      have : Y / p ≤ Y := Nat.div_le_self _ _
      omega)) fun b' _ hb' => ?_
    simp only [G]
    rw [if_neg]
    rintro ⟨-, h1, h2⟩
    have hlt : Y / p < b' := by simpa using hb'
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
    have : Y < p * b' := by
      have := (Nat.div_lt_iff_lt_mul hp.pos).mp hlt; linarith
    have : p * b' ≤ r * a * (p * b') := Nat.le_mul_of_pos_left _ (Nat.mul_pos hr0 ha)
    omega
  rw [h1]
  have h2 : ∀ a b', G a (p * b') = chiR n p * (Phi n r (2 * n) (p * b' * a) *
      (chiR n b' * chiR n a * ker1 r y Y (W2 ℓ n) (hInv (4 * n) r a) p b' a)) := fun a b' =>
    caseB_term ℓ n p y Y r a b' hp hpn hrs hr0
  conv_lhs => rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b' _ => h2 a b'))]
  conv_lhs => simp only [← Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  rw [sum_class_split r hr0 _ _ (fun a b => Phi n r (2 * n) (p * a * b))
    (fun a b => chiR n a * chiR n b * ker1 r y Y (W2 ℓ n) (hInv (4 * n) r b) p a b)
    (fun a b => Phi_mul_mod n r p _ a b)]
  rw [norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (norm_chiR_le n p)).trans ?_
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t₁ _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t₂ _ => ?_)
  exact norm_Phi_Asum_le n p y Y r t₁ t₂ hrs h8 hp hpn _ _ _

open Classical in
/-- **The per-level inequality.** -/
theorem critSum_le (ℓ n p y Y : ℕ) (hp : p.Prime) (hpn : ¬ p ∣ 2 * n) :
    ‖critSum ℓ n p y Y‖ ≤
      ∑ r ∈ (range (Y + 1)).filter (fun r => Smooth (S2 n) r ∧ 8 ∣ r),
        ∑ t₁ ∈ range r, ∑ t₂ ∈ range r, Real.sqrt (2 * r) *
          (‖Asum n p y Y r t₁ t₂ (W1 ℓ n) (hInv (-4 * n) r)‖ +
            ‖Asum n p y Y r t₁ t₂ (W2 ℓ n) (hInv (4 * n) r)‖) := by
  rw [critSum_eq ℓ n p y Y hp hpn]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r hr => ?_)
  simp only [Finset.mem_filter] at hr
  obtain ⟨hrY, hrs, h8⟩ := hr
  rcases Nat.eq_zero_or_pos r with h0 | hr0
  · subst h0
    have : (∑ a ∈ range (Y + 1), ∑ b ∈ range (Y + 1), if a.Coprime b ∧ p ∣ a * b ∧ y < 0 * a * b ∧ 0 * a * b ≤ Y
        then W1 ℓ n (0 * a * b) * Gam n 0 (a * b) * (chiR n a * chiR n b) *
          (rph b (-4 * n) ((0 * a : ℕ) : ℤ) * rph 0 (-2 * n) ((a * b : ℕ) : ℤ)) else 0) = 0 := by
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      simp
    rw [this, norm_zero]
    positivity
  -- split into the two cases
  have hsplit : ∀ a b, (if a.Coprime b ∧ p ∣ a * b ∧ y < r * a * b ∧ r * a * b ≤ Y then
      W1 ℓ n (r * a * b) * Gam n r (a * b) * (chiR n a * chiR n b) *
        (rph b (-4 * n) ((r * a : ℕ) : ℤ) * rph r (-2 * n) ((a * b : ℕ) : ℤ)) else 0) =
      (if p ∣ a then (if a.Coprime b ∧ y < r * a * b ∧ r * a * b ≤ Y then TermG ℓ n r a b else 0) else 0) +
      (if p ∣ b then (if a.Coprime b ∧ y < r * a * b ∧ r * a * b ≤ Y then TermG ℓ n r a b else 0) else 0) := by
    intro a b
    unfold TermG
    by_cases ha : p ∣ a <;> by_cases hb : p ∣ b
    · have hnc : ¬ a.Coprime b := Nat.not_coprime_of_dvd_of_dvd hp.one_lt ha hb
      simp [hnc]
    · simp only [ha, hb, if_true, if_false, add_zero]
      by_cases hc : a.Coprime b ∧ y < r * a * b ∧ r * a * b ≤ Y
      · rw [if_pos ⟨hc.1, dvd_mul_of_dvd_left ha b, hc.2⟩, if_pos hc]
      · rw [if_neg (fun h => hc ⟨h.1, h.2.2⟩), if_neg hc]
    · simp only [ha, hb, if_true, if_false, zero_add]
      by_cases hc : a.Coprime b ∧ y < r * a * b ∧ r * a * b ≤ Y
      · rw [if_pos ⟨hc.1, dvd_mul_of_dvd_right hb a, hc.2⟩, if_pos hc]
      · rw [if_neg (fun h => hc ⟨h.1, h.2.2⟩), if_neg hc]
    · simp only [ha, hb, if_false, add_zero]
      rw [if_neg (fun h => (Nat.Prime.dvd_mul hp).mp h.2.1 |>.elim ha hb)]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hsplit a b))]
  simp_rw [Finset.sum_add_distrib]
  refine (norm_add_le _ _).trans ?_
  simp_rw [mul_add, Finset.sum_add_distrib]
  exact add_le_add (caseA_bound ℓ n p y Y r hp hpn hrs h8 hr0) (caseB_bound ℓ n p y Y r hp hpn hrs h8 hr0)

end ThreeSquares
