/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.BilinTools

/-!
# Method 1: the inner sum over `a`

For fixed `b` and levels `p₁ ≠ p₂` the product of the kernels
`K(p, a, b) = 1[y < r p a b ≤ Y] W(r p a b) e_b(h \overline{p a})` summed over `a ≡ α₀ (mod r)`,
`A < a ≤ 2A`, is an incomplete Kloosterman sum with a smooth weight (`inner_bound`).
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset RML.ExpSum.Weil

/-- `e_b(h \overline{x})` on integers (zero if `b = 0` or `x` is not a unit mod `b`). -/
noncomputable def rph (b : ℕ) (h x : ℤ) : ℂ :=
  if hb : b = 0 then 0 else @reciprocalPhase b ⟨hb⟩ (h : ZMod b) (x : ZMod b)

theorem norm_rph_le (b : ℕ) (h x : ℤ) : ‖rph b h x‖ ≤ 1 := by
  unfold rph
  split_ifs with hb
  · simp
  · haveI : NeZero b := ⟨hb⟩
    unfold reciprocalPhase
    split_ifs
    · exact (norm_stdAddChar_eq_one _ _).le
    · simp

/-- A smooth weight: bounded and `log`-Lipschitz. -/
structure SmoothW (W : ℕ → ℂ) (W₀ W₁ : ℝ) : Prop where
  bound : ∀ c, ‖W c‖ ≤ W₀
  lip : ∀ c c' : ℕ, 0 < c → c ≤ c' → ‖W c' - W c‖ ≤ W₁ * ((c' - c : ℕ) : ℝ) / c

theorem SmoothW.W₀_nonneg {W : ℕ → ℂ} {W₀ W₁ : ℝ} (h : SmoothW W W₀ W₁) : 0 ≤ W₀ :=
  (norm_nonneg _).trans (h.bound 0)

theorem SmoothW.W₁_nonneg {W : ℕ → ℂ} {W₀ W₁ : ℝ} (h : SmoothW W W₀ W₁) : 0 ≤ W₁ := by
  have := h.lip 1 2 one_pos (by norm_num)
  have h0 := norm_nonneg (W 2 - W 1)
  norm_num at this
  linarith

/-- The kernel. -/
noncomputable def ker1 (r y Y : ℕ) (W : ℕ → ℂ) (h : ℤ) (p a b : ℕ) : ℂ :=
  if y < r * p * a * b ∧ r * p * a * b ≤ Y then W (r * p * a * b) * rph b h ((p * a : ℕ) : ℤ) else 0

/-- `e_b(h \overline{p₁ a}) · conj e_b(h \overline{p₂ a}) = e_b(h (p̄₁ − p̄₂) ā)`. -/
theorem rph_mul_conj {b : ℕ} [NeZero b] (h : ℤ) (p₁ p₂ a : ℕ) (hp₁ : IsUnit (p₁ : ZMod b))
    (hp₂ : IsUnit (p₂ : ZMod b)) :
    rph b h ((p₁ * a : ℕ) : ℤ) * starRingEnd ℂ (rph b h ((p₂ * a : ℕ) : ℤ)) =
      @reciprocalPhase b _ ((h : ZMod b) * (((p₁ : ZMod b))⁻¹ - ((p₂ : ZMod b))⁻¹)) (a : ZMod b) := by
  unfold rph
  rw [dif_neg (NeZero.ne b), dif_neg (NeZero.ne b)]
  push_cast
  rw [reciprocalPhase_mul_unit _ _ _ _ hp₁, reciprocalPhase_mul_unit _ _ _ _ hp₂]
  unfold reciprocalPhase
  by_cases ha : IsUnit (a : ZMod b)
  · rw [if_pos ha, if_pos ha, if_pos ha, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1; ring
  · simp only [ha, if_false, zero_mul]

/-- Reindexing an arithmetic progression inside an interval. -/
theorem sum_ap_interval (F : ℕ → ℂ) (r A B t : ℕ) (hr : 0 < r) :
    ∑ a ∈ (Ioc A B).filter (fun a => a % r = t % r), F a =
      ∑ j ∈ range (B / r + 1), if A < t % r + r * j ∧ t % r + r * j ≤ B then F (t % r + r * j) else 0 := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun a => a / r) (fun j => t % r + r * j) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Ioc] at ha
    simp only [Finset.mem_filter, Finset.mem_range]
    have e : t % r + r * (a / r) = a := by rw [← ha.2]; exact Nat.mod_add_div a r
    refine ⟨Nat.lt_succ_of_le (Nat.div_le_div_right ha.1.2), ?_⟩
    rw [e]; exact ha.1
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨hj.2, ?_⟩
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Ioc] at ha
    rw [← ha.2]; exact Nat.mod_add_div a r
  · intro j _
    rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt (Nat.mod_lt _ hr), zero_add]
  · intro a ha
    simp only [Finset.mem_filter] at ha
    rw [← ha.2, Nat.mod_add_div]

/-- Total variation of a weight cut off by `u ∧ d` with `u` increasing and `d` decreasing. -/
theorem tvar_cut (u d : ℕ → Prop) [DecidablePred u] [DecidablePred d]
    (hu : ∀ j, u j → u (j + 1)) (hd : ∀ j, d (j + 1) → d j) (g : ℕ → ℂ) (G₀ : ℝ)
    (hg : ∀ j, ‖g j‖ ≤ G₀) (L : ℕ) :
    tvar (fun j => if u j ∧ d j then g j else 0) L ≤
      (∑ i ∈ range (L - 1), if (u i ∧ d i) ∧ (u (i + 1) ∧ d (i + 1)) then ‖g (i + 1) - g i‖ else 0) +
        2 * G₀ := by
  unfold tvar
  have hG0 : 0 ≤ G₀ := (norm_nonneg _).trans (hg 0)
  -- the jump indicators
  set χ : ℕ → ℝ := fun j => if u j ∧ d j then 1 else 0
  set υ : ℕ → ℝ := fun j => if u j then 1 else 0
  set δ : ℕ → ℝ := fun j => if d j then 1 else 0
  have hυ : ∀ j, υ j ≤ υ (j + 1) := by
    intro j; simp only [υ]
    by_cases h1 : u j
    · rw [if_pos h1, if_pos (hu j h1)]
    · rw [if_neg h1]; split_ifs <;> norm_num
  have hδ : ∀ j, δ (j + 1) ≤ δ j := by
    intro j; simp only [δ]
    by_cases h1 : d (j + 1)
    · rw [if_pos h1, if_pos (hd j h1)]
    · rw [if_neg h1]; split_ifs <;> norm_num
  have hυ01 : ∀ j, 0 ≤ υ j ∧ υ j ≤ 1 := by intro j; simp only [υ]; split_ifs <;> norm_num
  have hδ01 : ∀ j, 0 ≤ δ j ∧ δ j ≤ 1 := by intro j; simp only [δ]; split_ifs <;> norm_num
  have hjump : ∀ i, ‖(if u (i + 1) ∧ d (i + 1) then g (i + 1) else 0) - (if u i ∧ d i then g i else 0)‖ ≤
      (if (u i ∧ d i) ∧ (u (i + 1) ∧ d (i + 1)) then ‖g (i + 1) - g i‖ else 0) +
        G₀ * ((υ (i + 1) - υ i) + (δ i - δ (i + 1))) := by
    intro i
    have h1 := hυ i; have h2 := hδ i
    by_cases a1 : u i <;> by_cases a2 : d i <;> by_cases a3 : u (i + 1) <;> by_cases a4 : d (i + 1) <;>
      simp only [υ, δ, a1, a2, a3, a4, and_true, and_false, true_and, false_and, if_true, if_false,
        sub_zero, zero_sub, norm_neg, sub_self, norm_zero] at h1 h2 ⊢ <;>
      first
        | (have := hg i; have := hg (i + 1); nlinarith [norm_nonneg (g (i + 1) - g i)])
        | nlinarith [hg i, hg (i + 1), norm_nonneg (g (i + 1) - g i)]
        | linarith
  calc ∑ i ∈ range (L - 1), ‖(if u (i + 1) ∧ d (i + 1) then g (i + 1) else 0) - (if u i ∧ d i then g i else 0)‖
      ≤ ∑ i ∈ range (L - 1), ((if (u i ∧ d i) ∧ (u (i + 1) ∧ d (i + 1)) then ‖g (i + 1) - g i‖ else 0) +
          G₀ * ((υ (i + 1) - υ i) + (δ i - δ (i + 1)))) := Finset.sum_le_sum fun i _ => hjump i
    _ = (∑ i ∈ range (L - 1), if (u i ∧ d i) ∧ (u (i + 1) ∧ d (i + 1)) then ‖g (i + 1) - g i‖ else 0) +
          G₀ * ((υ (L - 1) - υ 0) + (δ 0 - δ (L - 1))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
          Finset.sum_range_sub (fun i => υ i), Finset.sum_range_sub' (fun i => δ i)]
    _ ≤ _ := by
        have := hυ01 (L - 1); have := hυ01 0; have := hδ01 (L - 1); have := hδ01 0
        nlinarith

theorem norm_mul_sub_le (x x' y y' : ℂ) (M : ℝ) (hx' : ‖x'‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ‖x' * y' - x * y‖ ≤ M * (‖x' - x‖ + ‖y' - y‖) := by
  have : x' * y' - x * y = x' * (y' - y) + (x' - x) * y := by ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h1 := norm_nonneg (y' - y); have h2 := norm_nonneg (x' - x)
  nlinarith [norm_nonneg x', norm_nonneg y]

/-- **The inner sum of Method 1.** -/
theorem inner_bound (r y Y : ℕ) (W : ℕ → ℂ) {W₀ W₁ : ℝ} (hW : SmoothW W W₀ W₁) (h : ℤ)
    (A t b p₁ p₂ : ℕ) (hr : 0 < r) (hrA : r ≤ A) [NeZero b] (hrb : IsUnit (r : ZMod b))
    (hp₁ : IsUnit (p₁ : ZMod b)) (hp₂ : IsUnit (p₂ : ZMod b)) (hp₁0 : 0 < p₁) (hp₂0 : 0 < p₂) :
    ‖∑ a ∈ (Ioc A (2 * A)).filter (fun a => a % r = t % r),
        ker1 r y Y W h p₁ a b * starRingEnd ℂ (ker1 r y Y W h p₂ a b)‖ ≤
      (3 * W₀ ^ 2 + 4 * W₀ * W₁) * ((((2 * A / r + 1 : ℕ) : ℝ) / b + (1 + Real.log b)) *
        klC b ((h : ZMod b) * (((p₁ : ZMod b))⁻¹ - ((p₂ : ZMod b))⁻¹) * ((r : ZMod b))⁻¹)) := by
  classical
  have hb0 : 0 < b := NeZero.pos b
  have hW0 := hW.W₀_nonneg
  have hW1 := hW.W₁_nonneg
  set t₀ := t % r
  set h' : ZMod b := (h : ZMod b) * (((p₁ : ZMod b))⁻¹ - ((p₂ : ZMod b))⁻¹)
  -- the weight in the variable `j`
  set a_ : ℕ → ℕ := fun j => t₀ + r * j
  set U : ℕ → Prop := fun j => A < a_ j ∧ y < r * p₁ * a_ j * b ∧ y < r * p₂ * a_ j * b
  set D : ℕ → Prop := fun j => a_ j ≤ 2 * A ∧ r * p₁ * a_ j * b ≤ Y ∧ r * p₂ * a_ j * b ≤ Y
  set g : ℕ → ℂ := fun j => W (r * p₁ * a_ j * b) * starRingEnd ℂ (W (r * p₂ * a_ j * b))
  set G : ℕ → ℂ := fun j => if U j ∧ D j then g j else 0
  set M := 2 * A / r + 1
  have hsum : ∑ a ∈ (Ioc A (2 * A)).filter (fun a => a % r = t % r),
      ker1 r y Y W h p₁ a b * starRingEnd ℂ (ker1 r y Y W h p₂ a b) =
      ∑ j ∈ range M, G j * reciprocalPhase b (h' * ((r : ZMod b))⁻¹)
        ((t₀ : ZMod b) * ((r : ZMod b))⁻¹ + (j : ZMod b)) := by
    rw [sum_ap_interval _ r A (2 * A) t hr]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hrph := rph_mul_conj h p₁ p₂ (a_ j) hp₁ hp₂
    have hcast : ((a_ j : ℕ) : ZMod b) = (r : ZMod b) * ((t₀ : ZMod b) * ((r : ZMod b))⁻¹ + (j : ZMod b)) := by
      simp only [a_]; push_cast
      rw [mul_add, ← mul_assoc, mul_comm (r : ZMod b) (t₀ : ZMod b), mul_assoc,
        ZMod.mul_inv_of_unit _ hrb, mul_one]
    rw [hcast, reciprocalPhase_mul_unit _ _ _ _ hrb] at hrph
    simp only [G, g, U, D, ker1]
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
  refine (kl_smooth b _ _ M G).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg ?_ (klC_nonneg _ _))
  rotate_left
  · have := Real.log_nonneg (show (1 : ℝ) ≤ b by exact_mod_cast hb0)
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

theorem norm_ker1_le (r y Y : ℕ) (W : ℕ → ℂ) {W₀ W₁ : ℝ} (hW : SmoothW W W₀ W₁) (h : ℤ) (p a b : ℕ) :
    ‖ker1 r y Y W h p a b‖ ≤ W₀ := by
  unfold ker1
  split_ifs
  · rw [norm_mul]
    calc ‖W (r * p * a * b)‖ * ‖rph b h ((p * a : ℕ) : ℤ)‖ ≤ W₀ * 1 :=
          mul_le_mul (hW.bound _) (norm_rph_le _ _ _) (norm_nonneg _) hW.W₀_nonneg
      _ = W₀ := mul_one _
  · simp; exact hW.W₀_nonneg

theorem ker1_eq_zero_of_not_unit (r y Y : ℕ) (W : ℕ → ℂ) (h : ℤ) (p a b : ℕ) [NeZero b]
    (hp : ¬ IsUnit (p : ZMod b)) : ker1 r y Y W h p a b = 0 := by
  unfold ker1 rph
  rw [dif_neg (NeZero.ne b)]
  split_ifs with h1
  · unfold reciprocalPhase
    rw [if_neg (fun hu => hp (isUnit_of_mul_isUnit_left (by push_cast at hu; exact hu))), mul_zero]
  · rfl

open Classical in
/-- **Method 1.** -/
theorem method1 (Ps : Finset ℕ) (r y Y : ℕ) (W : ℕ → ℂ) {W₀ W₁ : ℝ} (hW : SmoothW W W₀ W₁)
    (A t₁ : ℕ) (Bs : Finset ℕ) (hBs : ∀ b ∈ Bs, 0 < b) (hr : 0 < r) (hrA : r ≤ A) (h : ℕ → ℤ) (α β : ℕ → ℂ)
    (hα : ∀ a, ‖α a‖ ≤ 1) (hβ : ∀ b, ‖β b‖ ≤ 1) (hPs : ∀ p ∈ Ps, 0 < p)
    (hB : ∀ b ∈ Bs, IsUnit (r : ZMod b)) :
    (∑ p ∈ Ps, ‖∑ a ∈ (Ioc A (2 * A)).filter (fun a => a % r = t₁ % r),
        ∑ b ∈ Bs, α a * β b * ker1 r y Y W (h b) p a b‖) ^ 2 ≤
      (((Ioc A (2 * A)).filter (fun a => a % r = t₁ % r)).card *
        (Bs).card : ℝ) *
      ((Ps.card * (Bs).card *
          ((Ioc A (2 * A)).filter (fun a => a % r = t₁ % r)).card : ℝ) * W₀ ^ 2 +
        ∑ b ∈ Bs, ∑ p₁ ∈ Ps, ∑ p₂ ∈ Ps.erase p₁,
          (3 * W₀ ^ 2 + 4 * W₀ * W₁) * ((((2 * A / r + 1 : ℕ) : ℝ) / b + (1 + Real.log b)) *
            (if hb : b = 0 then 0 else
              if IsUnit (@Nat.cast (ZMod b) _ p₁) ∧ IsUnit (@Nat.cast (ZMod b) _ p₂) then
              @klC b ((@Int.cast (ZMod b) _ (h b)) * ((@Nat.cast (ZMod b) _ p₁)⁻¹ - (@Nat.cast (ZMod b) _ p₂)⁻¹) *
                ((@Nat.cast (ZMod b) _ r))⁻¹) else 0))) := by
  classical
  set As := (Ioc A (2 * A)).filter (fun a => a % r = t₁ % r)
  have hW0 := hW.W₀_nonneg
  have hW1 := hW.W₁_nonneg
  have hS : ∀ p, (∑ a ∈ As, ∑ b ∈ Bs, α a * β b * ker1 r y Y W (h b) p a b) =
      ∑ i ∈ As ×ˢ Bs, (α i.1 * β i.2) * ker1 r y Y W (h i.2) p i.1 i.2 := by
    intro p; rw [Finset.sum_product]
  simp_rw [hS]
  refine (cs_levels Ps (As ×ˢ Bs) (fun i => α i.1 * β i.2) (fun p i => ker1 r y Y W (h i.2) p i.1 i.2)).trans ?_
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
    have hinner : ∀ p₁ ∈ Ps, ∀ p₂ ∈ Ps, ‖∑ i ∈ As ×ˢ Bs, ker1 r y Y W (h i.2) p₁ i.1 i.2 *
        starRingEnd ℂ (ker1 r y Y W (h i.2) p₂ i.1 i.2)‖ ≤
        ∑ b ∈ Bs, ‖∑ a ∈ As, ker1 r y Y W (h b) p₁ a b * starRingEnd ℂ (ker1 r y Y W (h b) p₂ a b)‖ := by
      intro p₁ _ p₂ _
      rw [Finset.sum_product_right]
      exact norm_sum_le _ _
    calc ∑ p₁ ∈ Ps, ∑ p₂ ∈ Ps, ‖∑ i ∈ As ×ˢ Bs, ker1 r y Y W (h i.2) p₁ i.1 i.2 *
          starRingEnd ℂ (ker1 r y Y W (h i.2) p₂ i.1 i.2)‖
        ≤ ∑ p₁ ∈ Ps, ∑ p₂ ∈ Ps, ∑ b ∈ Bs, ‖∑ a ∈ As, ker1 r y Y W (h b) p₁ a b *
            starRingEnd ℂ (ker1 r y Y W (h b) p₂ a b)‖ :=
          Finset.sum_le_sum fun p₁ hp₁ => Finset.sum_le_sum fun p₂ hp₂ => hinner p₁ hp₁ p₂ hp₂
      _ = ∑ p₁ ∈ Ps, (∑ b ∈ Bs, ‖∑ a ∈ As, ker1 r y Y W (h b) p₁ a b *
            starRingEnd ℂ (ker1 r y Y W (h b) p₁ a b)‖ +
          ∑ p₂ ∈ Ps.erase p₁, ∑ b ∈ Bs, ‖∑ a ∈ As, ker1 r y Y W (h b) p₁ a b *
            starRingEnd ℂ (ker1 r y Y W (h b) p₂ a b)‖) := by
          refine Finset.sum_congr rfl fun p₁ hp₁ => ?_
          rw [← Finset.add_sum_erase _ _ hp₁]
      _ ≤ ∑ p₁ ∈ Ps, ((Bs.card * As.card : ℝ) * W₀ ^ 2 +
          ∑ b ∈ Bs, ∑ p₂ ∈ Ps.erase p₁,
          (3 * W₀ ^ 2 + 4 * W₀ * W₁) * ((((2 * A / r + 1 : ℕ) : ℝ) / b + (1 + Real.log b)) *
            (if hb : b = 0 then 0 else
              if IsUnit (@Nat.cast (ZMod b) _ p₁) ∧ IsUnit (@Nat.cast (ZMod b) _ p₂) then
              @klC b ((@Int.cast (ZMod b) _ (h b)) * ((@Nat.cast (ZMod b) _ p₁)⁻¹ - (@Nat.cast (ZMod b) _ p₂)⁻¹) *
                ((@Nat.cast (ZMod b) _ r))⁻¹) else 0))) := by
          refine Finset.sum_le_sum fun p₁ hp₁ => add_le_add ?_ ?_
          · -- diagonal
            calc (∑ b ∈ Bs, ‖∑ a ∈ As, ker1 r y Y W (h b) p₁ a b * starRingEnd ℂ (ker1 r y Y W (h b) p₁ a b)‖)
                ≤ ∑ b ∈ Bs, ∑ a ∈ As, W₀ ^ 2 := by
                  refine Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
                  rw [norm_mul, Complex.norm_conj, sq]
                  exact mul_le_mul (norm_ker1_le r y Y W hW _ _ _ _) (norm_ker1_le r y Y W hW _ _ _ _)
                    (norm_nonneg _) hW0
              _ = (Bs.card * As.card : ℝ) * W₀ ^ 2 := by
                  simp only [Finset.sum_const, nsmul_eq_mul]; ring
          · rw [Finset.sum_comm]
            refine Finset.sum_le_sum fun b hb => Finset.sum_le_sum fun p₂ hp₂ => ?_
            have hb0 : b ≠ 0 := by
              exact (hBs b hb).ne'
            rw [dif_neg hb0]
            haveI : NeZero b := ⟨hb0⟩
            by_cases hu : IsUnit (p₁ : ZMod b) ∧ IsUnit (p₂ : ZMod b)
            · rw [if_pos hu]
              exact inner_bound r y Y W hW (h b) A t₁ b p₁ p₂ hr hrA (hB b hb) hu.1 hu.2
                (hPs p₁ hp₁) (hPs p₂ (Finset.mem_of_mem_erase hp₂))
            · have hz : ∀ a, ker1 r y Y W (h b) p₁ a b * starRingEnd ℂ (ker1 r y Y W (h b) p₂ a b) = 0 := by
                intro a
                rcases not_and_or.mp hu with h1 | h1
                · rw [ker1_eq_zero_of_not_unit _ _ _ _ _ _ _ _ h1, zero_mul]
                · rw [ker1_eq_zero_of_not_unit _ _ _ _ _ _ _ _ h1, map_zero, mul_zero]
              simp only [hz, Finset.sum_const_zero, norm_zero]
              rw [if_neg hu]; simp
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_comm]
          ring

end ThreeSquares
