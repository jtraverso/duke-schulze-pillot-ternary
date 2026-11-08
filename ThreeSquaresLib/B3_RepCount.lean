/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.B3_Fiber

/-!
# Counting representations by good reduced forms

* `rootCount n k = #{0 ≤ b < 2k : 4k ∣ b² + n}`, `Rcount n m = ∑_{g² ∣ m} rootCount n (m/g²)`.
* `Rcount_le_repSet`: if `n ∣ 2t²m + 1` for some `t`, then
  `Rcount n m ≤ #{(f, v) : f ∈ GoodSet n, |v| ≤ B, f(v) = m}` (`B ≥ 2m`); the injection is
  `(g, b) ↦ (f_b, g • v_b)` (`rootRep`, `smul_coprime_inj`, `rootRep_inj`).
* `sum_Rcount_le`: `∑_{m ≤ M, m good} Rcount n m ≤ ∑_{f ∈ GoodSet n} #{v ∈ [−2M, 2M]² :
  1 ≤ f(v) ≤ M}`.
-/

@[expose] public section

namespace ThreeSquares.B3

open Finset

/-- `#{0 ≤ b < 2k : 4k ∣ b² + n}`. -/
def rootCount (n k : ℕ) : ℕ :=
  ((Ico (0 : ℤ) (2 * k)).filter (fun b => (4 * k : ℤ) ∣ b ^ 2 + n)).card

/-- The divisors `g ≥ 1` with `g² ∣ m`. -/
def sqDiv (m : ℕ) : Finset ℕ := (Icc 1 m).filter (fun g => g ^ 2 ∣ m)

/-- `∑_{g² ∣ m} rootCount n (m / g²)`. -/
def Rcount (n m : ℕ) : ℕ := ∑ g ∈ sqDiv m, rootCount n (m / g ^ 2)

/-- The box `[−B, B]²`. -/
def box (B : ℕ) : Finset (ℤ × ℤ) := Icc (-(B : ℤ)) B ×ˢ Icc (-(B : ℤ)) B

/-- Representations of `m` by good reduced forms, in the box. -/
noncomputable def repSet (n m B : ℕ) : Finset (Form × ℤ × ℤ) :=
  (GoodSet n ×ˢ box B).filter (fun p => p.1.eval p.2.1 p.2.2 = m)

theorem mem_box_of_eval {n : ℕ} {f : Form} (hf : f ∈ Red n) {x y : ℤ} {m B : ℕ}
    (he : f.eval x y = m) (hB : 2 * m ≤ B) : (x, y) ∈ box B := by
  obtain ⟨-, hred, ha⟩ := mem_Red.mp hf
  have h := Form.sq_add_sq_le hred ha x y
  rw [he] at h
  have hx : |x| ≤ x ^ 2 := by
    rcases eq_or_ne x 0 with h0 | h0
    · simp [h0]
    · rw [← sq_abs]; nlinarith [abs_pos.mpr h0]
  have hy : |y| ≤ y ^ 2 := by
    rcases eq_or_ne y 0 with h0 | h0
    · simp [h0]
    · rw [← sq_abs]; nlinarith [abs_pos.mpr h0]
  have hB' : (2 * m : ℤ) ≤ B := by exact_mod_cast hB
  simp only [box, mem_product, mem_Icc]
  rw [abs_le] at hx hy
  constructor <;> constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

theorem Rcount_le_repSet {n m B : ℕ} (hn : 0 < n) (hm : 0 < m) (hB : 2 * m ≤ B)
    {t : ℤ} (ht : (n : ℤ) ∣ 2 * t ^ 2 * m + 1) : Rcount n m ≤ (repSet n m B).card := by
  classical
  unfold Rcount
  simp only [rootCount]
  rw [← card_sigma]
  refine card_le_card_of_injOn
    (fun p => ((rootRep n (m / p.1 ^ 2) p.2).1, (p.1 : ℤ) * (rootRep n (m / p.1 ^ 2) p.2).2.1,
      (p.1 : ℤ) * (rootRep n (m / p.1 ^ 2) p.2).2.2)) ?_ ?_
  · rintro ⟨g, b⟩ hp
    rw [coe_sigma, Set.mem_sigma_iff] at hp
    obtain ⟨hg, hb⟩ := hp
    simp only [sqDiv, coe_filter, mem_Icc, Set.mem_setOf_eq] at hg
    simp only [coe_filter, mem_Ico, Set.mem_setOf_eq] at hb
    obtain ⟨⟨hg1, -⟩, hgm⟩ := hg
    obtain ⟨-, hdvd⟩ := hb
    have hm' : 0 < m / g ^ 2 := Nat.div_pos (Nat.le_of_dvd hm hgm) (by positivity)
    have hfm := rootRep_mem hn hm' hdvd
    have hev := rootRep_eval hn hm' hdvd
    have hev' : (rootRep n (m / g ^ 2) b).1.eval ((g : ℤ) * (rootRep n (m / g ^ 2) b).2.1)
        ((g : ℤ) * (rootRep n (m / g ^ 2) b).2.2) = m := by
      rw [Form.eval_smul, hev]
      have : (g ^ 2 * (m / g ^ 2) : ℕ) = m := Nat.mul_div_cancel' hgm
      exact_mod_cast this
    simp only [repSet, coe_filter, mem_product, Set.mem_setOf_eq]
    refine ⟨⟨mem_GoodSet.mpr ⟨hfm, good_of_rep hev' ht⟩, mem_box_of_eval hfm hev' hB⟩, hev'⟩
  · rintro ⟨g₁, b₁⟩ hp₁ ⟨g₂, b₂⟩ hp₂ heq
    rw [coe_sigma, Set.mem_sigma_iff] at hp₁ hp₂
    obtain ⟨hg₁, hb₁⟩ := hp₁
    obtain ⟨hg₂, hb₂⟩ := hp₂
    simp only [sqDiv, coe_filter, mem_Icc, Set.mem_setOf_eq] at hg₁ hg₂
    simp only [coe_filter, mem_Ico, Set.mem_setOf_eq] at hb₁ hb₂
    simp only [Prod.mk.injEq] at heq
    obtain ⟨hf, h1, h2⟩ := heq
    have hm₁ : 0 < m / g₁ ^ 2 := Nat.div_pos (Nat.le_of_dvd hm hg₁.2) (pow_pos hg₁.1.1 2)
    have hm₂ : 0 < m / g₂ ^ 2 := Nat.div_pos (Nat.le_of_dvd hm hg₂.2) (pow_pos hg₂.1.1 2)
    obtain ⟨hgg, hv1, hv2⟩ := smul_coprime_inj (by exact_mod_cast hg₁.1.1)
      (by exact_mod_cast hg₂.1.1) (rootRep_coprime hn hm₁ hb₁.2)
      (rootRep_coprime hn hm₂ hb₂.2) h1 h2
    have hgg' : g₁ = g₂ := by exact_mod_cast hgg
    subst hgg'
    have hrr : rootRep n (m / g₁ ^ 2) b₁ = rootRep n (m / g₁ ^ 2) b₂ := by
      rw [Prod.ext_iff, Prod.ext_iff]
      exact ⟨hf, hv1, hv2⟩
    have hbb := rootRep_inj hn hm₁ hb₁.2 hb₂.2 (by exact_mod_cast hb₁.1)
      (by exact_mod_cast hb₂.1) hrr
    subst hbb
    rfl

/-- The number of `v ∈ [−2M, 2M]²` with `1 ≤ f(v) ≤ M`. -/
def ellCount (f : Form) (M : ℕ) : ℕ :=
  ((box (2 * M)).filter (fun v => 1 ≤ f.eval v.1 v.2 ∧ f.eval v.1 v.2 ≤ M)).card

theorem sum_Rcount_le {n : ℕ} (hn : 0 < n) (M : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ m, P m → ∃ t : ℤ, (n : ℤ) ∣ 2 * t ^ 2 * m + 1) :
    ∑ m ∈ (Icc 1 M).filter P, Rcount n m ≤ ∑ f ∈ GoodSet n, ellCount f M := by
  classical
  calc ∑ m ∈ (Icc 1 M).filter P, Rcount n m
      ≤ ∑ m ∈ (Icc 1 M).filter P, (repSet n m (2 * M)).card := by
        refine sum_le_sum fun m hm => ?_
        rw [mem_filter, mem_Icc] at hm
        obtain ⟨t, ht⟩ := hP m hm.2
        exact Rcount_le_repSet hn (by omega) (by omega) ht
    _ = ∑ m ∈ (Icc 1 M).filter P, ∑ p ∈ GoodSet n ×ˢ box (2 * M),
          if p.1.eval p.2.1 p.2.2 = m then 1 else 0 := by
        refine sum_congr rfl fun m _ => ?_
        rw [repSet, card_filter]
    _ = ∑ p ∈ GoodSet n ×ˢ box (2 * M), ∑ m ∈ (Icc 1 M).filter P,
          if p.1.eval p.2.1 p.2.2 = m then 1 else 0 := sum_comm
    _ ≤ ∑ p ∈ GoodSet n ×ˢ box (2 * M),
          if 1 ≤ p.1.eval p.2.1 p.2.2 ∧ p.1.eval p.2.1 p.2.2 ≤ M then 1 else 0 := by
        refine sum_le_sum fun p _ => ?_
        set e := p.1.eval p.2.1 p.2.2
        by_cases he : 1 ≤ e ∧ e ≤ M
        · rw [if_pos he]
          have hsub : ((Icc 1 M).filter P).filter (fun m : ℕ => e = (m : ℤ)) ⊆
              ({e.toNat} : Finset ℕ) := by
            intro m hm
            rw [mem_filter] at hm
            rw [mem_singleton]
            omega
          rw [← card_filter]
          exact le_trans (card_le_card hsub) (card_singleton _).le
        · rw [if_neg he]
          apply le_of_eq
          refine sum_eq_zero fun m hm => ?_
          rw [mem_filter, mem_Icc] at hm
          rw [if_neg]
          intro h
          apply he
          rw [h]
          exact ⟨by exact_mod_cast hm.1.1, by exact_mod_cast hm.1.2⟩
    _ = ∑ f ∈ GoodSet n, ellCount f M := by
        rw [sum_product]
        refine sum_congr rfl fun f _ => ?_
        rw [ellCount, card_filter]

end ThreeSquares.B3
