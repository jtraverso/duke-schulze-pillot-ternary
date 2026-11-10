/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.Method1Sum
public import DukeH1.RQSplit

/-!
# Method 2: the inner sum over `b`

Kernel `K₂(p, a, b) = 1[y < r p a b ≤ Y] W(r p a b) e_{pa}(m \overline{r b})`. For coprime levels
`p₁ ≠ p₂`: `e_{p₁a}(m x̄) · conj e_{p₂a}(m x̄) = e_{p₁p₂a}(m (p₂ − p₁) x̄)` (`rph_mul_conj2`).
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open ZMod Finset RML.ExpSum.Weil

theorem isUnit_of_isUnit_cast_dvd {N M : ℕ} [NeZero N] (hd : M ∣ N) (x : ℤ) (hx : IsUnit (x : ZMod N)) :
    IsUnit (x : ZMod M) := by
  have := hx.map (ZMod.castHom hd (ZMod M))
  rwa [map_intCast] at this

theorem isCoprime_of_isUnit_int {N : ℕ} [NeZero N] {x : ℤ} (hx : IsUnit (x : ZMod N)) : IsCoprime x N := by
  obtain ⟨b, hb⟩ := hx.exists_right_inv
  have h : (((x * (b.val : ℤ) - 1 : ℤ)) : ZMod N) = 0 := by
    push_cast; rw [ZMod.natCast_zmod_val, hb, sub_self]
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp h
  exact ⟨(b.val : ℤ), -k, by linear_combination hk⟩

/-- `e_{p₁a}(m x̄) · conj e_{p₂a}(m x̄) = e_{p₁p₂a}(m (p₂ − p₁) x̄)`. -/
theorem rph_mul_conj2 (p₁ p₂ a : ℕ) (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (ha : 0 < a) (hc : p₁.Coprime p₂)
    (m x : ℤ) :
    rph (p₁ * a) m x * starRingEnd ℂ (rph (p₂ * a) m x) = rph (p₁ * p₂ * a) (m * ((p₂ : ℤ) - p₁)) x := by
  have h1 : p₁ * a ≠ 0 := by positivity
  have h2 : p₂ * a ≠ 0 := by positivity
  have h3 : p₁ * p₂ * a ≠ 0 := by positivity
  unfold rph
  rw [dif_neg h1, dif_neg h2, dif_neg h3]
  haveI : NeZero (p₁ * a) := ⟨h1⟩
  haveI : NeZero (p₂ * a) := ⟨h2⟩
  haveI : NeZero (p₁ * p₂ * a) := ⟨h3⟩
  have hd1 : p₁ * a ∣ p₁ * p₂ * a := ⟨p₂, by ring⟩
  have hd2 : p₂ * a ∣ p₁ * p₂ * a := ⟨p₁, by ring⟩
  unfold reciprocalPhase
  by_cases hx : IsUnit (x : ZMod (p₁ * p₂ * a))
  · have hx1 := isUnit_of_isUnit_cast_dvd hd1 x hx
    have hx2 := isUnit_of_isUnit_cast_dvd hd2 x hx
    rw [if_pos hx1, if_pos hx2, if_pos hx]
    -- an integer inverse
    set u : ℤ := (((x : ZMod (p₁ * p₂ * a))⁻¹).val : ℤ)
    have hu : (x : ZMod (p₁ * p₂ * a)) * (u : ZMod (p₁ * p₂ * a)) = 1 := by
      simp only [u]; rw [Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.mul_inv_of_unit _ hx]
    have hu1 : (x : ZMod (p₁ * a)) * (u : ZMod (p₁ * a)) = 1 := by
      have := congrArg (ZMod.castHom hd1 (ZMod (p₁ * a))) hu
      rwa [map_mul, map_intCast, map_intCast, map_one] at this
    have hu2 : (x : ZMod (p₂ * a)) * (u : ZMod (p₂ * a)) = 1 := by
      have := congrArg (ZMod.castHom hd2 (ZMod (p₂ * a))) hu
      rwa [map_mul, map_intCast, map_intCast, map_one] at this
    rw [ZMod.inv_eq_of_mul_eq_one _ _ _ hu, ZMod.inv_eq_of_mul_eq_one _ _ _ hu1,
      ZMod.inv_eq_of_mul_eq_one _ _ _ hu2,
      show (m : ZMod (p₁ * a)) * (u : ZMod (p₁ * a)) = ((m * u : ℤ) : ZMod (p₁ * a)) by push_cast; ring,
      show (m : ZMod (p₂ * a)) * (u : ZMod (p₂ * a)) = ((m * u : ℤ) : ZMod (p₂ * a)) by push_cast; ring,
      show ((m * ((p₂ : ℤ) - p₁) : ℤ) : ZMod (p₁ * p₂ * a)) * (u : ZMod (p₁ * p₂ * a)) =
        ((m * ((p₂ : ℤ) - p₁) * u : ℤ) : ZMod (p₁ * p₂ * a)) by push_cast; ring,
      ← AddChar.map_neg_eq_conj, ← Int.cast_neg, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe,
      ZMod.stdAddChar_coe, ← Complex.exp_add]
    congr 1
    have h1' : ((p₁ : ℂ)) ≠ 0 := by exact_mod_cast hp₁.ne'
    have h2' : ((p₂ : ℂ)) ≠ 0 := by exact_mod_cast hp₂.ne'
    have ha' : ((a : ℂ)) ≠ 0 := by exact_mod_cast ha.ne'
    push_cast
    field_simp
    ring
  · rw [if_neg hx]
    by_cases hx1 : IsUnit (x : ZMod (p₁ * a))
    · by_cases hx2 : IsUnit (x : ZMod (p₂ * a))
      · exfalso; apply hx
        have c1 := isCoprime_of_isUnit_int hx1
        have c2 := isCoprime_of_isUnit_int hx2
        refine isUnit_of_isCoprime ?_
        have e : ((p₁ * p₂ * a : ℕ) : ℤ) ∣ ((p₁ * a : ℕ) : ℤ) * ((p₂ * a : ℕ) : ℤ) := ⟨a, by push_cast; ring⟩
        exact (c1.mul_right c2).of_isCoprime_of_dvd_right e
      · rw [if_neg hx2]; simp
    · rw [if_neg hx1, zero_mul]

/-- The kernel of Method 2 (summed variable `a`, fixed `b`, modulus `p b`). -/
noncomputable def ker2 (r y Y : ℕ) (W : ℕ → ℂ) (h : ℤ) (p a b : ℕ) : ℂ :=
  if y < r * p * a * b ∧ r * p * a * b ≤ Y then W (r * p * a * b) * rph (p * b) h ((r * a : ℕ) : ℤ) else 0

/-- **The inner sum of Method 2.** -/
theorem inner_bound2 (r y Y : ℕ) (W : ℕ → ℂ) {W₀ W₁ : ℝ} (hW : SmoothW W W₀ W₁) (h : ℤ)
    (A t b p₁ p₂ : ℕ) (hr : 0 < r) (hrA : r ≤ A) (hb0' : 0 < b) (hc : p₁.Coprime p₂)
    (hrb : IsUnit (r : ZMod (p₁ * p₂ * b))) (hp₁0 : 0 < p₁) (hp₂0 : 0 < p₂) :
    ‖∑ a ∈ (Ioc A (2 * A)).filter (fun a => a % r = t % r),
        ker2 r y Y W h p₁ a b * starRingEnd ℂ (ker2 r y Y W h p₂ a b)‖ ≤
      (3 * W₀ ^ 2 + 4 * W₀ * W₁) * ((((2 * A / r + 1 : ℕ) : ℝ) / (p₁ * p₂ * b : ℕ) +
        (1 + Real.log (p₁ * p₂ * b : ℕ))) *
        @klC (p₁ * p₂ * b) (((h * ((p₂ : ℤ) - p₁) : ℤ) : ZMod (p₁ * p₂ * b)) *
          (((r * r : ℕ) : ZMod (p₁ * p₂ * b)))⁻¹)) := by
  classical
  have hb0 : 0 < b := hb0'
  haveI : NeZero (p₁ * p₂ * b) := ⟨by positivity⟩
  have hN0 : 0 < p₁ * p₂ * b := by positivity
  have hrr : IsUnit (((r * r : ℕ) : ZMod (p₁ * p₂ * b))) := by push_cast; exact hrb.mul hrb
  have hW0 := hW.W₀_nonneg
  have hW1 := hW.W₁_nonneg
  set t₀ := t % r
  set h' : ZMod (p₁ * p₂ * b) := ((h * ((p₂ : ℤ) - p₁) : ℤ) : ZMod (p₁ * p₂ * b))
  -- the weight in the variable `j`
  set a_ : ℕ → ℕ := fun j => t₀ + r * j
  set U : ℕ → Prop := fun j => A < a_ j ∧ y < r * p₁ * a_ j * b ∧ y < r * p₂ * a_ j * b
  set D : ℕ → Prop := fun j => a_ j ≤ 2 * A ∧ r * p₁ * a_ j * b ≤ Y ∧ r * p₂ * a_ j * b ≤ Y
  set g : ℕ → ℂ := fun j => W (r * p₁ * a_ j * b) * starRingEnd ℂ (W (r * p₂ * a_ j * b))
  set G : ℕ → ℂ := fun j => if U j ∧ D j then g j else 0
  set M := 2 * A / r + 1
  have hsum : ∑ a ∈ (Ioc A (2 * A)).filter (fun a => a % r = t % r),
      ker2 r y Y W h p₁ a b * starRingEnd ℂ (ker2 r y Y W h p₂ a b) =
      ∑ j ∈ range M, G j * reciprocalPhase (p₁ * p₂ * b) (h' * (((r * r : ℕ) : ZMod (p₁ * p₂ * b)))⁻¹)
        ((t₀ : ZMod (p₁ * p₂ * b)) * ((r : ZMod (p₁ * p₂ * b)))⁻¹ + (j : ZMod (p₁ * p₂ * b))) := by
    rw [sum_ap_interval _ r A (2 * A) t hr]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hrph := rph_mul_conj2 p₁ p₂ b hp₁0 hp₂0 hb0' hc h ((r * a_ j : ℕ) : ℤ)
    have hcast : ((((r * a_ j : ℕ) : ℤ)) : ZMod (p₁ * p₂ * b)) = ((r * r : ℕ) : ZMod (p₁ * p₂ * b)) *
        ((t₀ : ZMod (p₁ * p₂ * b)) * ((r : ZMod (p₁ * p₂ * b)))⁻¹ + (j : ZMod (p₁ * p₂ * b))) := by
      simp only [a_]; push_cast
      have hu := ZMod.mul_inv_of_unit _ hrb
      linear_combination -(r : ZMod (p₁ * p₂ * b)) * (t₀ : ZMod (p₁ * p₂ * b)) * hu
    have hrph' : rph (p₁ * p₂ * b) (h * ((p₂ : ℤ) - p₁)) ((r * a_ j : ℕ) : ℤ) =
        reciprocalPhase (p₁ * p₂ * b) (h' * (((r * r : ℕ) : ZMod (p₁ * p₂ * b)))⁻¹)
          ((t₀ : ZMod (p₁ * p₂ * b)) * ((r : ZMod (p₁ * p₂ * b)))⁻¹ + (j : ZMod (p₁ * p₂ * b))) := by
      unfold rph
      rw [dif_neg hN0.ne', hcast, reciprocalPhase_mul_unit _ _ _ _ hrr]
    rw [hrph'] at hrph
    simp only [G, g, U, D, ker2]
    by_cases hA : A < a_ j ∧ a_ j ≤ 2 * A
    · simp only [a_] at hA
      rw [if_pos hA]
      by_cases h1 : y < r * p₁ * a_ j * b ∧ r * p₁ * a_ j * b ≤ Y
      · by_cases h2 : y < r * p₂ * a_ j * b ∧ r * p₂ * a_ j * b ≤ Y
        · rw [if_pos h1, if_pos h2, if_pos ⟨⟨hA.1, h1.1, h2.1⟩, hA.2, h1.2, h2.2⟩]
          simp only [a_] at hrph h1 h2 ⊢
          rw [map_mul, ← hrph]; ring
        · rw [if_pos h1, if_neg h2, if_neg (show ¬((A < a_ j ∧ y < r * p₁ * a_ j * b ∧ y < r * p₂ * a_ j * b) ∧
              (a_ j ≤ 2 * A ∧ r * p₁ * a_ j * b ≤ Y ∧ r * p₂ * a_ j * b ≤ Y)) from
              fun hh => h2 ⟨hh.1.2.2, hh.2.2.2⟩)]; simp
      · rw [if_neg h1, if_neg (show ¬((A < a_ j ∧ y < r * p₁ * a_ j * b ∧ y < r * p₂ * a_ j * b) ∧
              (a_ j ≤ 2 * A ∧ r * p₁ * a_ j * b ≤ Y ∧ r * p₂ * a_ j * b ≤ Y)) from
              fun hh => h1 ⟨hh.1.2.1, hh.2.2.1⟩)]; simp
    · rw [if_neg hA, if_neg (show ¬((A < a_ j ∧ y < r * p₁ * a_ j * b ∧ y < r * p₂ * a_ j * b) ∧
              (a_ j ≤ 2 * A ∧ r * p₁ * a_ j * b ≤ Y ∧ r * p₂ * a_ j * b ≤ Y)) from
              fun hh => hA ⟨hh.1.1, hh.2.1⟩), zero_mul]
  rw [hsum]
  refine (kl_smooth (p₁ * p₂ * b) _ _ M G).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg ?_ (klC_nonneg _ _))
  rotate_left
  · have := Real.log_nonneg (show (1 : ℝ) ≤ ((p₁ * p₂ * b : ℕ) : ℝ) by exact_mod_cast hN0)
    positivity
  · -- the weight: sup + variation
    have hg : ∀ j, ‖g j‖ ≤ W₀ ^ 2 := by
      intro j; simp only [g]; rw [norm_mul, Complex.norm_conj, sq]
      exact mul_le_mul (hW.bound _) (hW.bound _) (norm_nonneg _) hW0
    have hGM : ‖G (M - 1)‖ ≤ W₀ ^ 2 := by
      simp only [G]; split_ifs
      · exact hg _
      · simp; positivity
    have hU : ∀ j, U j → U (j + 1) := by
      intro j hj; simp only [U, a_] at hj ⊢
      refine ⟨by nlinarith, ?_, ?_⟩
      · calc y < r * p₁ * (t₀ + r * j) * b := hj.2.1
          _ ≤ r * p₁ * (t₀ + r * (j + 1)) * b := by gcongr; omega
      · calc y < r * p₂ * (t₀ + r * j) * b := hj.2.2
          _ ≤ r * p₂ * (t₀ + r * (j + 1)) * b := by gcongr; omega
    have hD : ∀ j, D (j + 1) → D j := by
      intro j hj; simp only [D, a_] at hj ⊢
      refine ⟨by nlinarith, ?_, ?_⟩
      · calc r * p₁ * (t₀ + r * j) * b ≤ r * p₁ * (t₀ + r * (j + 1)) * b := by gcongr; omega
          _ ≤ Y := hj.2.1
      · calc r * p₂ * (t₀ + r * j) * b ≤ r * p₂ * (t₀ + r * (j + 1)) * b := by gcongr; omega
          _ ≤ Y := hj.2.2
    have htv := tvar_cut U D hU hD g (W₀ ^ 2) hg M
    -- each step inside the support
    have hstep : ∀ i, (U i ∧ D i) ∧ (U (i + 1) ∧ D (i + 1)) → ‖g (i + 1) - g i‖ ≤ 2 * W₀ * W₁ * r / A := by
      intro i hi
      have hAi : A < a_ i := hi.1.1.1
      have hlip : ∀ p : ℕ, 0 < p → ‖W (r * p * a_ (i + 1) * b) - W (r * p * a_ i * b)‖ ≤ W₁ * r / A := by
        intro p hp
        have hc0 : 0 < r * p * a_ i * b := by
          have : 0 < a_ i := by omega
          positivity
        have hle : r * p * a_ i * b ≤ r * p * a_ (i + 1) * b := by
          simp only [a_]; gcongr; omega
        refine (hW.lip _ _ hc0 hle).trans ?_
        have hdiff : r * p * a_ (i + 1) * b - r * p * a_ i * b = r * p * b * r := by
          simp only [a_]; apply Nat.sub_eq_of_eq_add; ring
        rw [hdiff]
        have hA0 : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le hr hrA)
        have hai : (A : ℝ) < a_ i := by exact_mod_cast hAi
        rw [div_le_div_iff₀ (by exact_mod_cast hc0) hA0]
        push_cast
        have key : (r : ℝ) * p * b * r * A ≤ (r : ℝ) * p * b * r * (a_ i : ℕ) :=
          mul_le_mul_of_nonneg_left hai.le (by positivity)
        calc W₁ * ((r : ℝ) * p * b * r) * A = W₁ * ((r : ℝ) * p * b * r * A) := by ring
          _ ≤ W₁ * ((r : ℝ) * p * b * r * (a_ i : ℕ)) := mul_le_mul_of_nonneg_left key hW1
          _ = W₁ * r * (r * p * (a_ i : ℕ) * b) := by ring
      simp only [g]
      refine (norm_mul_sub_le _ _ _ _ W₀ (hW.bound _) (by rw [Complex.norm_conj]; exact hW.bound _)).trans ?_
      rw [← map_sub, Complex.norm_conj]
      have hx := hlip p₁ hp₁0; have hy := hlip p₂ hp₂0
      calc W₀ * (‖W (r * p₁ * a_ (i + 1) * b) - W (r * p₁ * a_ i * b)‖ +
            ‖W (r * p₂ * a_ (i + 1) * b) - W (r * p₂ * a_ i * b)‖) ≤ W₀ * (W₁ * r / A + W₁ * r / A) := by
            gcongr
        _ = 2 * W₀ * W₁ * r / A := by ring
    have hnum : ((range (M - 1)).card : ℝ) * (2 * W₀ * W₁ * r / A) ≤ 4 * W₀ * W₁ := by
      rw [Finset.card_range]
      have hA0 : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le hr hrA)
      have hM : ((M - 1 : ℕ) : ℝ) * r ≤ 2 * A := by
        have : (M - 1) * r ≤ 2 * A := by
          simp only [M, Nat.add_sub_cancel]; exact Nat.div_mul_le_self _ _
        exact_mod_cast this
      rw [show ((M - 1 : ℕ) : ℝ) * (2 * W₀ * W₁ * r / A) = (2 * W₀ * W₁) * (((M - 1 : ℕ) : ℝ) * r) / A by ring,
        div_le_iff₀ hA0]
      nlinarith [mul_nonneg hW0 hW1]
    have hsum2 : (∑ i ∈ range (M - 1), if (U i ∧ D i) ∧ (U (i + 1) ∧ D (i + 1)) then ‖g (i + 1) - g i‖ else 0)
        ≤ 4 * W₀ * W₁ := by
      calc (∑ i ∈ range (M - 1), if (U i ∧ D i) ∧ (U (i + 1) ∧ D (i + 1)) then ‖g (i + 1) - g i‖ else 0)
          ≤ ∑ i ∈ range (M - 1), (2 * W₀ * W₁ * r / A) := by
            refine Finset.sum_le_sum fun i _ => ?_
            split_ifs with hi
            · exact hstep i hi
            · positivity
        _ = ((range (M - 1)).card : ℝ) * (2 * W₀ * W₁ * r / A) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 4 * W₀ * W₁ := hnum
    have htv' : tvar G M ≤ (∑ i ∈ range (M - 1), if (U i ∧ D i) ∧ (U (i + 1) ∧ D (i + 1)) then
        ‖g (i + 1) - g i‖ else 0) + 2 * W₀ ^ 2 := htv
    linarith


theorem norm_ker2_le (r y Y : ℕ) (W : ℕ → ℂ) {W₀ W₁ : ℝ} (hW : SmoothW W W₀ W₁) (h : ℤ) (p a b : ℕ) :
    ‖ker2 r y Y W h p a b‖ ≤ W₀ := by
  unfold ker2
  split_ifs
  · rw [norm_mul]
    calc ‖W (r * p * a * b)‖ * ‖rph (p * b) h ((r * a : ℕ) : ℤ)‖ ≤ W₀ * 1 :=
          mul_le_mul (hW.bound _) (norm_rph_le _ _ _) (norm_nonneg _) hW.W₀_nonneg
      _ = W₀ := mul_one _
  · simp; exact hW.W₀_nonneg

/-- **Method 2.** -/
theorem method2 (Ps : Finset ℕ) (r y Y : ℕ) (W : ℕ → ℂ) {W₀ W₁ : ℝ} (hW : SmoothW W W₀ W₁)
    (A t₁ : ℕ) (Bs : Finset ℕ) (hr : 0 < r) (hrA : r ≤ A) (h : ℤ) (α β : ℕ → ℂ)
    (hα : ∀ a, ‖α a‖ ≤ 1) (hβ : ∀ b, ‖β b‖ ≤ 1) (hPs : ∀ p ∈ Ps, 0 < p)
    (hPc : ∀ p₁ ∈ Ps, ∀ p₂ ∈ Ps, p₁ ≠ p₂ → p₁.Coprime p₂) (hrP : ∀ p ∈ Ps, r.Coprime p)
    (hB : ∀ b ∈ Bs, r.Coprime b ∧ 0 < b) :
    (∑ p ∈ Ps, ‖∑ a ∈ (Ioc A (2 * A)).filter (fun a => a % r = t₁ % r),
        ∑ b ∈ Bs, α a * β b * ker2 r y Y W h p a b‖) ^ 2 ≤
      (((Ioc A (2 * A)).filter (fun a => a % r = t₁ % r)).card *
        (Bs).card : ℝ) *
      ((Ps.card * (Bs).card *
          ((Ioc A (2 * A)).filter (fun a => a % r = t₁ % r)).card : ℝ) * W₀ ^ 2 +
        ∑ b ∈ Bs, ∑ p₁ ∈ Ps, ∑ p₂ ∈ Ps.erase p₁,
          (3 * W₀ ^ 2 + 4 * W₀ * W₁) * ((((2 * A / r + 1 : ℕ) : ℝ) / (p₁ * p₂ * b : ℕ) +
            (1 + Real.log (p₁ * p₂ * b : ℕ))) *
            @klC (p₁ * p₂ * b) ((@Int.cast (ZMod (p₁ * p₂ * b)) _ (h * ((p₂ : ℤ) - p₁))) *
              ((@Nat.cast (ZMod (p₁ * p₂ * b)) _ (r * r)))⁻¹))) := by
  classical
  set As := (Ioc A (2 * A)).filter (fun a => a % r = t₁ % r)
  have hW0 := hW.W₀_nonneg
  have hW1 := hW.W₁_nonneg
  have hS : ∀ p, (∑ a ∈ As, ∑ b ∈ Bs, α a * β b * ker2 r y Y W h p a b) =
      ∑ i ∈ As ×ˢ Bs, (α i.1 * β i.2) * ker2 r y Y W h p i.1 i.2 := by
    intro p; rw [Finset.sum_product]
  simp_rw [hS]
  refine (cs_levels Ps (As ×ˢ Bs) (fun i => α i.1 * β i.2) (fun p i => ker2 r y Y W h p i.1 i.2)).trans ?_
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · calc (∑ i ∈ As ×ˢ Bs, ‖α i.1 * β i.2‖ ^ 2) ≤ ∑ i ∈ As ×ˢ Bs, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_mul, mul_pow]
          have := hα i.1; have := hβ i.2
          have h1 : ‖α i.1‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (α i.1)]
          have h2 : ‖β i.2‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (β i.2)]
          nlinarith [sq_nonneg ‖α i.1‖, sq_nonneg ‖β i.2‖]
      _ = (As.card * Bs.card : ℝ) := by rw [Finset.sum_const, Finset.card_product]; push_cast; ring
  · -- the double sum over levels
    have hinner : ∀ p₁ ∈ Ps, ∀ p₂ ∈ Ps, ‖∑ i ∈ As ×ˢ Bs, ker2 r y Y W h p₁ i.1 i.2 *
        starRingEnd ℂ (ker2 r y Y W h p₂ i.1 i.2)‖ ≤
        ∑ b ∈ Bs, ‖∑ a ∈ As, ker2 r y Y W h p₁ a b * starRingEnd ℂ (ker2 r y Y W h p₂ a b)‖ := by
      intro p₁ _ p₂ _
      rw [Finset.sum_product_right]
      exact norm_sum_le _ _
    calc ∑ p₁ ∈ Ps, ∑ p₂ ∈ Ps, ‖∑ i ∈ As ×ˢ Bs, ker2 r y Y W h p₁ i.1 i.2 *
          starRingEnd ℂ (ker2 r y Y W h p₂ i.1 i.2)‖
        ≤ ∑ p₁ ∈ Ps, ∑ p₂ ∈ Ps, ∑ b ∈ Bs, ‖∑ a ∈ As, ker2 r y Y W h p₁ a b *
            starRingEnd ℂ (ker2 r y Y W h p₂ a b)‖ :=
          Finset.sum_le_sum fun p₁ hp₁ => Finset.sum_le_sum fun p₂ hp₂ => hinner p₁ hp₁ p₂ hp₂
      _ = ∑ p₁ ∈ Ps, (∑ b ∈ Bs, ‖∑ a ∈ As, ker2 r y Y W h p₁ a b *
            starRingEnd ℂ (ker2 r y Y W h p₁ a b)‖ +
          ∑ p₂ ∈ Ps.erase p₁, ∑ b ∈ Bs, ‖∑ a ∈ As, ker2 r y Y W h p₁ a b *
            starRingEnd ℂ (ker2 r y Y W h p₂ a b)‖) := by
          refine Finset.sum_congr rfl fun p₁ hp₁ => ?_
          rw [← Finset.add_sum_erase _ _ hp₁]
      _ ≤ ∑ p₁ ∈ Ps, ((Bs.card * As.card : ℝ) * W₀ ^ 2 +
          ∑ b ∈ Bs, ∑ p₂ ∈ Ps.erase p₁,
          (3 * W₀ ^ 2 + 4 * W₀ * W₁) * ((((2 * A / r + 1 : ℕ) : ℝ) / (p₁ * p₂ * b : ℕ) +
            (1 + Real.log (p₁ * p₂ * b : ℕ))) *
            @klC (p₁ * p₂ * b) ((@Int.cast (ZMod (p₁ * p₂ * b)) _ (h * ((p₂ : ℤ) - p₁))) *
              ((@Nat.cast (ZMod (p₁ * p₂ * b)) _ (r * r)))⁻¹))) := by
          refine Finset.sum_le_sum fun p₁ hp₁ => add_le_add ?_ ?_
          · -- diagonal
            calc (∑ b ∈ Bs, ‖∑ a ∈ As, ker2 r y Y W h p₁ a b * starRingEnd ℂ (ker2 r y Y W h p₁ a b)‖)
                ≤ ∑ b ∈ Bs, ∑ a ∈ As, W₀ ^ 2 := by
                  refine Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
                  rw [norm_mul, Complex.norm_conj, sq]
                  exact mul_le_mul (norm_ker2_le r y Y W hW _ _ _ _) (norm_ker2_le r y Y W hW _ _ _ _)
                    (norm_nonneg _) hW0
              _ = (Bs.card * As.card : ℝ) * W₀ ^ 2 := by
                  simp only [Finset.sum_const, nsmul_eq_mul]; ring
          · rw [Finset.sum_comm]
            refine Finset.sum_le_sum fun b hb => Finset.sum_le_sum fun p₂ hp₂ => ?_
            have hbB := hB b hb
            have hp₁0 : 0 < p₁ := hPs p₁ hp₁
            have hp₂0 : 0 < p₂ := hPs p₂ (Finset.mem_of_mem_erase hp₂)
            have hne : p₂ ≠ p₁ := Finset.ne_of_mem_erase hp₂
            have hc : p₁.Coprime p₂ := hPc p₁ hp₁ p₂ (Finset.mem_of_mem_erase hp₂) (Ne.symm hne)
            haveI : NeZero (p₁ * p₂ * b) := ⟨by have := hbB.2; positivity⟩
            have hru : IsUnit (r : ZMod (p₁ * p₂ * b)) := by
              rw [ZMod.isUnit_iff_coprime]
              exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (hrP p₁ hp₁)
                (hrP p₂ (Finset.mem_of_mem_erase hp₂))) hbB.1
            exact inner_bound2 r y Y W hW h A t₁ b p₁ p₂ hr hrA hbB.2 hc hru hp₁0 hp₂0
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_comm]
          ring

end ThreeSquares
