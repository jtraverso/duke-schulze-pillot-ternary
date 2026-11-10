/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.GeneralKl

/-!
# Tools for bilinear sums

* `abel_bound`: summation by parts against a weight of bounded variation;
* `cs_levels`: `(∑_p |∑_i c_i X(p,i)|)² ≤ (∑_i |c_i|²) ∑_{p₁,p₂} |∑_i X(p₁,i) conj X(p₂,i)|`;
* `kl_smooth`: incomplete Kloosterman sums with a smooth weight.
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset RML.ExpSum.Weil

/-- Total variation of a weight on `[0, L)`. -/
noncomputable def tvar (g : ℕ → ℂ) (L : ℕ) : ℝ := ∑ i ∈ range (L - 1), ‖g (i + 1) - g i‖

theorem tvar_nonneg (g : ℕ → ℂ) (L : ℕ) : 0 ≤ tvar g L :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- **Summation by parts.** If all initial sums of `f` are bounded by `M`, then
`|∑_{i<L} g i f i| ≤ (|g (L-1)| + tvar g L) M`. -/
theorem abel_bound (f g : ℕ → ℂ) (L : ℕ) (M : ℝ)
    (hM : ∀ k ≤ L, ‖∑ i ∈ range k, f i‖ ≤ M) :
    ‖∑ i ∈ range L, g i * f i‖ ≤ (‖g (L - 1)‖ + tvar g L) * M := by
  have h := Finset.sum_range_by_parts (n := L) g f
  simp only [smul_eq_mul] at h
  rw [h]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _))
  refine (norm_sub_le _ _).trans ?_
  rw [add_mul]
  gcongr
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM L le_rfl) (norm_nonneg _)
  · unfold tvar
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left (hM _ ?_) (norm_nonneg _)
    have := Finset.mem_range.mp hi; omega

/-- **Cauchy–Schwarz over the levels.** -/
theorem cs_levels {ι κ : Type*} (P : Finset κ) (I : Finset ι) (c : ι → ℂ) (X : κ → ι → ℂ) :
    (∑ p ∈ P, ‖∑ i ∈ I, c i * X p i‖) ^ 2 ≤
      (∑ i ∈ I, ‖c i‖ ^ 2) * ∑ p₁ ∈ P, ∑ p₂ ∈ P, ‖∑ i ∈ I, X p₁ i * starRingEnd ℂ (X p₂ i)‖ := by
  classical
  -- unimodular `ζ_p` with `ζ_p S_p = |S_p|`
  set S : κ → ℂ := fun p => ∑ i ∈ I, c i * X p i
  set ζ : κ → ℂ := fun p => if S p = 0 then 1 else starRingEnd ℂ (S p) / ‖S p‖
  have hζ : ∀ p, ζ p * S p = ‖S p‖ := by
    intro p
    simp only [ζ]
    split_ifs with h
    · rw [h]; simp
    · have hn : (‖S p‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
      field_simp
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hζn : ∀ p, ‖ζ p‖ ≤ 1 := by
    intro p; simp only [ζ]; split_ifs with h
    · simp
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr h)]
  have hsum : ((∑ p ∈ P, ‖S p‖ : ℝ) : ℂ) = ∑ i ∈ I, c i * ∑ p ∈ P, ζ p * X p i := by
    push_cast
    simp_rw [← hζ]
    simp only [S, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => by ring
  have h1 : (∑ p ∈ P, ‖S p‖) ^ 2 ≤ (∑ i ∈ I, ‖c i‖ ^ 2) * ∑ i ∈ I, ‖∑ p ∈ P, ζ p * X p i‖ ^ 2 := by
    have hn : (∑ p ∈ P, ‖S p‖) = ‖∑ i ∈ I, c i * ∑ p ∈ P, ζ p * X p i‖ := by
      rw [← hsum, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
    rw [hn]
    calc ‖∑ i ∈ I, c i * ∑ p ∈ P, ζ p * X p i‖ ^ 2
        ≤ (∑ i ∈ I, ‖c i‖ * ‖∑ p ∈ P, ζ p * X p i‖) ^ 2 := by
          gcongr
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp [norm_mul]
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun _ _ => by positivity))
  -- open the square
  have h2 : ∀ i, (‖∑ p ∈ P, ζ p * X p i‖ ^ 2 : ℝ) =
      (∑ p₁ ∈ P, ∑ p₂ ∈ P, ζ p₁ * starRingEnd ℂ (ζ p₂) * (X p₁ i * starRingEnd ℂ (X p₂ i))).re := by
    intro i
    rw [← Complex.normSq_eq_norm_sq]
    have e : (Complex.normSq (∑ p ∈ P, ζ p * X p i) : ℝ) =
        ((∑ p ∈ P, ζ p * X p i) * starRingEnd ℂ (∑ p ∈ P, ζ p * X p i)).re := by
      rw [Complex.mul_conj]; simp
    rw [e, map_sum, Finset.sum_mul_sum]
    simp only [map_mul]
    congr 1
    refine Finset.sum_congr rfl fun p₁ _ => Finset.sum_congr rfl fun p₂ _ => by ring
  calc ∑ i ∈ I, ‖∑ p ∈ P, ζ p * X p i‖ ^ 2
      = (∑ p₁ ∈ P, ∑ p₂ ∈ P, ζ p₁ * starRingEnd ℂ (ζ p₂) *
          ∑ i ∈ I, X p₁ i * starRingEnd ℂ (X p₂ i)).re := by
        simp_rw [h2]
        rw [← Complex.re_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p₁ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p₂ _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ‖∑ p₁ ∈ P, ∑ p₂ ∈ P, ζ p₁ * starRingEnd ℂ (ζ p₂) *
          ∑ i ∈ I, X p₁ i * starRingEnd ℂ (X p₂ i)‖ := Complex.re_le_norm _
    _ ≤ ∑ p₁ ∈ P, ∑ p₂ ∈ P, ‖∑ i ∈ I, X p₁ i * starRingEnd ℂ (X p₂ i)‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p₁ _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p₂ _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj]
        have := hζn p₁; have := hζn p₂
        calc ‖ζ p₁‖ * ‖ζ p₂‖ * _ ≤ 1 * 1 * ‖∑ i ∈ I, X p₁ i * starRingEnd ℂ (X p₂ i)‖ := by
              gcongr
          _ = _ := by ring

theorem reciprocalPhase_mul_unit (N : ℕ) [NeZero N] (h u x : ZMod N) (hu : IsUnit u) :
    reciprocalPhase N h (u * x) = reciprocalPhase N (h * u⁻¹) x := by
  unfold reciprocalPhase
  by_cases hx : IsUnit x
  · rw [if_pos (hu.mul hx), if_pos hx]
    congr 1
    rw [← hu.unit_spec, ← hx.unit_spec, ← Units.val_mul, ZMod.inv_coe_unit, ZMod.inv_coe_unit,
      ZMod.inv_coe_unit, mul_inv, Units.val_mul]
    ring
  · rw [if_neg (fun h' => hx (isUnit_of_mul_isUnit_right h')), if_neg hx]

/-- **Incomplete Kloosterman sum with a smooth weight**, along the progression `x + j`. -/
theorem kl_smooth (N : ℕ) [NeZero N] (h x : ZMod N) (L : ℕ) (g : ℕ → ℂ) :
    ‖∑ j ∈ range L, g j * reciprocalPhase N h (x + (j : ZMod N))‖ ≤
      (‖g (L - 1)‖ + tvar g L) * (((L : ℝ) / N + (1 + Real.log N)) * klC N h) := by
  refine abel_bound _ g L _ fun k hk => ?_
  refine (norm_interval_reciprocal_le N h x k).trans ?_
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  gcongr
  all_goals first | exact klC_nonneg N h | exact_mod_cast hk

end ThreeSquares
