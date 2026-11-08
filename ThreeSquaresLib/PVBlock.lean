/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Method1
public import ThreeSquaresLib.JacobiGauss

/-!
# The Pólya–Vinogradov block

For fixed `p` and small `b`, the sum over `a ≡ t (mod r)` of `J(a | n₀) K₁(p, a, b)` is split into
classes mod `b`; each class is a progression mod `rb` on which Pólya–Vinogradov applies.
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset RML.ExpSum.Weil

/-- Prefix sums of a Jacobi symbol along a progression are bounded (Pólya–Vinogradov). -/
theorem pv_prefix {n₀ : ℕ} [NeZero n₀] (hsq : Squarefree n₀) (hodd : Odd n₀) (hn1 : 1 < n₀)
    (m s : ℕ) (hm : IsUnit (m : ZMod n₀)) (k : ℕ) :
    ‖∑ j ∈ range k, (jacobiSym ((s + m * j : ℕ) : ℤ) n₀ : ℂ)‖ ≤ Real.sqrt n₀ * (1 + Real.log n₀) := by
  have := polya_vinogradov hsq hodd hn1 (m : ℤ) (s : ℤ) (by exact_mod_cast hm) k
  convert this using 4 with j
  push_cast; ring

/-- **The Pólya–Vinogradov block.** -/
theorem pv_block {n₀ : ℕ} [NeZero n₀] (hsq : Squarefree n₀) (hodd : Odd n₀) (hn1 : 1 < n₀)
    (r y Y : ℕ) (W : ℕ → ℂ) {W₀ W₁ : ℝ} (hW : SmoothW W W₀ W₁) (h : ℤ) (A t b p : ℕ)
    (hr : 0 < r) (hb : 0 < b) (hrb : r.Coprime b) (hrbA : r * b ≤ A) (hp : 0 < p)
    (hu : IsUnit ((r * b : ℕ) : ZMod n₀)) :
    ‖∑ a ∈ (Ioc A (2 * A)).filter (fun a => a % r = t % r),
        (jacobiSym (a : ℤ) n₀ : ℂ) * ker1 r y Y W h p a b‖ ≤
      b * ((3 * W₀ + 2 * W₁) * (Real.sqrt n₀ * (1 + Real.log n₀))) := by
  classical
  have hW0 := hW.W₀_nonneg
  have hW1 := hW.W₁_nonneg
  set As := (Ioc A (2 * A)).filter (fun a => a % r = t % r)
  -- split by the class of `a` mod `b`
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun a => a % b) (t := range b)
    (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hb))]
  refine (norm_sum_le _ _).trans ?_
  rw [show (b : ℝ) * ((3 * W₀ + 2 * W₁) * (Real.sqrt n₀ * (1 + Real.log n₀))) =
    ∑ u ∈ range b, ((3 * W₀ + 2 * W₁) * (Real.sqrt n₀ * (1 + Real.log n₀))) by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]]
  refine Finset.sum_le_sum fun u hu' => ?_
  -- the CRT class `s` mod `r b`
  obtain ⟨s, hs1, hs2⟩ := Nat.chineseRemainder hrb t u
  have hclass : As.filter (fun a => a % b = u) =
      (Ioc A (2 * A)).filter (fun a => a % (r * b) = s % (r * b)) := by
    ext a
    simp only [As, Finset.mem_filter]
    constructor
    · rintro ⟨⟨ha, h1⟩, h2⟩
      refine ⟨ha, ?_⟩
      have e1 : a ≡ s [MOD r] := h1.trans hs1.symm
      have e2 : a ≡ s [MOD b] := by
        have : a % b = u % b := by rw [h2, Nat.mod_eq_of_lt (Finset.mem_range.mp hu')]
        exact this.trans hs2.symm
      exact (Nat.modEq_and_modEq_iff_modEq_mul hrb).mp ⟨e1, e2⟩
    · rintro ⟨ha, h3⟩
      have e := (Nat.modEq_and_modEq_iff_modEq_mul hrb).mpr h3
      refine ⟨⟨ha, e.1.trans hs1⟩, ?_⟩
      have := e.2.trans hs2
      rw [Nat.ModEq, Nat.mod_eq_of_lt (Finset.mem_range.mp hu')] at this
      exact this
  rw [hclass]
  -- on this class, `e_b(h \overline{p a})` is constant
  have hconst : ∀ a ∈ (Ioc A (2 * A)).filter (fun a => a % (r * b) = s % (r * b)),
      (jacobiSym (a : ℤ) n₀ : ℂ) * ker1 r y Y W h p a b =
        rph b h ((p * (s % (r * b)) : ℕ) : ℤ) *
          ((jacobiSym (a : ℤ) n₀ : ℂ) * (if y < r * p * a * b ∧ r * p * a * b ≤ Y then W (r * p * a * b) else 0)) := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    have hab : ((p * a : ℕ) : ℤ) % b = ((p * (s % (r * b)) : ℕ) : ℤ) % b := by
      have : a % b = s % (r * b) % b := by
        have h1 : a % (r * b) % b = a % b := Nat.mod_mod_of_dvd a (dvd_mul_left b r)
        rw [← h1, ha.2]
      push_cast
      rw [Int.mul_emod, Int.mul_emod (p : ℤ)]
      congr 2
      exact_mod_cast this
    have hrph : rph b h ((p * a : ℕ) : ℤ) = rph b h ((p * (s % (r * b)) : ℕ) : ℤ) := by
      unfold rph
      rw [dif_neg hb.ne', dif_neg hb.ne']
      haveI : NeZero b := ⟨hb.ne'⟩
      congr 1
      rw [← ZMod.intCast_mod (((p * a : ℕ) : ℤ)) b, hab, ZMod.intCast_mod]
    unfold ker1
    split_ifs
    · rw [hrph]; ring
    · simp
  rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum, norm_mul]
  refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (norm_rph_le _ _ _)) ?_
  -- reindex the progression and apply Abel + Pólya–Vinogradov
  have hrb0 : 0 < r * b := Nat.mul_pos hr hb
  rw [sum_ap_interval _ (r * b) A (2 * A) s hrb0]
  set s₀ := s % (r * b)
  set U : ℕ → Prop := fun j => A < s₀ + r * b * j ∧ y < r * p * (s₀ + r * b * j) * b
  set D : ℕ → Prop := fun j => s₀ + r * b * j ≤ 2 * A ∧ r * p * (s₀ + r * b * j) * b ≤ Y
  set g : ℕ → ℂ := fun j => W (r * p * (s₀ + r * b * j) * b)
  set M := 2 * A / (r * b) + 1
  have hre : ∀ j ∈ range M, (if A < s₀ + r * b * j ∧ s₀ + r * b * j ≤ 2 * A then
      (jacobiSym ((s₀ + r * b * j : ℕ) : ℤ) n₀ : ℂ) *
        (if y < r * p * (s₀ + r * b * j) * b ∧ r * p * (s₀ + r * b * j) * b ≤ Y then
          W (r * p * (s₀ + r * b * j) * b) else 0) else 0) =
      (if U j ∧ D j then g j else 0) * (jacobiSym ((s₀ + r * b * j : ℕ) : ℤ) n₀ : ℂ) := by
    intro j _
    simp only [U, D, g]
    by_cases h1 : A < s₀ + r * b * j ∧ s₀ + r * b * j ≤ 2 * A
    · rw [if_pos h1]
      by_cases h2 : y < r * p * (s₀ + r * b * j) * b ∧ r * p * (s₀ + r * b * j) * b ≤ Y
      · rw [if_pos h2, if_pos ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩]; ring
      · rw [if_neg h2, if_neg (fun hh => h2 ⟨hh.1.2, hh.2.2⟩)]; simp
    · rw [if_neg h1, if_neg (fun hh => h1 ⟨hh.1.1, hh.2.1⟩), zero_mul]
  rw [Finset.sum_congr rfl hre]
  refine (abel_bound _ _ M _ fun k _ => pv_prefix hsq hodd hn1 (r * b) s₀ hu k).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hg : ∀ j, ‖g j‖ ≤ W₀ := fun j => hW.bound _
  have hU : ∀ j, U j → U (j + 1) := by
    intro j hj; simp only [U] at hj ⊢
    refine ⟨by nlinarith, ?_⟩
    calc y < r * p * (s₀ + r * b * j) * b := hj.2
      _ ≤ r * p * (s₀ + r * b * (j + 1)) * b := by gcongr; omega
  have hD : ∀ j, D (j + 1) → D j := by
    intro j hj; simp only [D] at hj ⊢
    refine ⟨by nlinarith, ?_⟩
    calc r * p * (s₀ + r * b * j) * b ≤ r * p * (s₀ + r * b * (j + 1)) * b := by gcongr; omega
      _ ≤ Y := hj.2
  have htv := tvar_cut U D hU hD g W₀ hg M
  have hstep : ∀ i, (U i ∧ D i) ∧ (U (i + 1) ∧ D (i + 1)) → ‖g (i + 1) - g i‖ ≤ W₁ * (r * b) / A := by
    intro i hi
    have hAi : A < s₀ + r * b * i := hi.1.1.1
    have hc0 : 0 < r * p * (s₀ + r * b * i) * b := by
      have : 0 < s₀ + r * b * i := by omega
      positivity
    have hle : r * p * (s₀ + r * b * i) * b ≤ r * p * (s₀ + r * b * (i + 1)) * b := by gcongr; omega
    refine (hW.lip _ _ hc0 hle).trans ?_
    have hdiff : r * p * (s₀ + r * b * (i + 1)) * b - r * p * (s₀ + r * b * i) * b = r * p * b * (r * b) := by
      apply Nat.sub_eq_of_eq_add; ring
    rw [hdiff]
    have hA0 : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le hrb0 hrbA)
    have hai : (A : ℝ) < ((s₀ + r * b * i : ℕ) : ℝ) := by exact_mod_cast hAi
    rw [div_le_div_iff₀ (by exact_mod_cast hc0) hA0]
    push_cast
    have key : (r : ℝ) * p * b * (r * b) * A ≤ (r : ℝ) * p * b * (r * b) * ((s₀ + r * b * i : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hai.le (by positivity)
    push_cast at key
    calc W₁ * ((r : ℝ) * p * b * (r * b)) * A = W₁ * ((r : ℝ) * p * b * (r * b) * A) := by ring
      _ ≤ W₁ * ((r : ℝ) * p * b * (r * b) * (s₀ + r * b * i)) := mul_le_mul_of_nonneg_left key hW1
      _ = W₁ * (r * b) * (r * p * (s₀ + r * b * i) * b) := by ring
  have hnum : ((range (M - 1)).card : ℝ) * (W₁ * (r * b) / A) ≤ 2 * W₁ := by
    rw [Finset.card_range]
    have hA0 : (0 : ℝ) < A := by exact_mod_cast (lt_of_lt_of_le hrb0 hrbA)
    have hM : ((M - 1 : ℕ) : ℝ) * ((r * b : ℕ) : ℝ) ≤ 2 * A := by
      have : (M - 1) * (r * b) ≤ 2 * A := by
        simp only [M, Nat.add_sub_cancel]; exact Nat.div_mul_le_self _ _
      exact_mod_cast this
    push_cast at hM
    rw [show ((M - 1 : ℕ) : ℝ) * (W₁ * (r * b) / A) = W₁ * (((M - 1 : ℕ) : ℝ) * (r * b)) / A by ring,
      div_le_iff₀ hA0]
    nlinarith
  have hsum2 : (∑ i ∈ range (M - 1), if (U i ∧ D i) ∧ (U (i + 1) ∧ D (i + 1)) then ‖g (i + 1) - g i‖ else 0)
      ≤ 2 * W₁ := by
    calc (∑ i ∈ range (M - 1), if (U i ∧ D i) ∧ (U (i + 1) ∧ D (i + 1)) then ‖g (i + 1) - g i‖ else 0)
        ≤ ∑ i ∈ range (M - 1), (W₁ * (r * b) / A) := by
          refine Finset.sum_le_sum fun i _ => ?_
          split_ifs with hi
          · exact hstep i hi
          · positivity
      _ = ((range (M - 1)).card : ℝ) * (W₁ * (r * b) / A) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * W₁ := hnum
  have hGM : ‖(if U (M - 1) ∧ D (M - 1) then g (M - 1) else 0)‖ ≤ W₀ := by
    split_ifs
    · exact hg _
    · simp; exact hW0
  have htv' : tvar (fun j => if U j ∧ D j then g j else 0) M ≤
      (∑ i ∈ range (M - 1), if (U i ∧ D i) ∧ (U (i + 1) ∧ D (i + 1)) then ‖g (i + 1) - g i‖ else 0) +
        2 * W₀ := htv
  linarith

end ThreeSquares
