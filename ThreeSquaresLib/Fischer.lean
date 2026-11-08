/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic

/-!
# The Fischer decomposition in three variables

For real polynomials in three variables, with `Δ = ∑ ∂ᵢ²` and `N = x₀² + x₁² + x₂²`:

* `lap_nrm_mul`: `Δ(N Q) = (4m + 6) Q + N ΔQ` for `Q` homogeneous of degree `m`.
* `fischer`: every homogeneous `P` of degree `d ≥ 2` is `H + N Q` with `H` harmonic homogeneous of
  degree `d` and `Q` homogeneous of degree `d − 2`.
* `lap_iter_nrm_mul`: `Δ^{n}(N Q) = N Δ^n Q + n(4m − 4n + 10) Δ^{n−1} Q`.
-/

@[expose] public section

namespace ThreeSquares.Duke

open MvPolynomial Finset

/-- Real polynomials in three variables. -/
abbrev R3 := MvPolynomial (Fin 3) ℝ

/-- The Laplacian `∑ ∂ᵢ²`. -/
noncomputable def lap : R3 →ₗ[ℝ] R3 :=
  ∑ i : Fin 3, (pderiv i).toLinearMap ∘ₗ (pderiv i).toLinearMap

theorem lap_apply (P : R3) : lap P = ∑ i : Fin 3, pderiv i (pderiv i P) := by
  simp [lap]

/-- `N = x₀² + x₁² + x₂²`. -/
noncomputable def nrm : R3 := ∑ i : Fin 3, X i ^ 2

theorem pderiv_nrm (i : Fin 3) : pderiv i nrm = 2 * X i := by
  simp only [nrm, map_sum, pderiv_pow, pderiv_X]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem isHomogeneous_nrm : nrm.IsHomogeneous 2 := by
  unfold nrm
  exact IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i 2

theorem nrm_ne_zero : nrm ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (fun _ : Fin 3 => (1 : ℝ))) h
  simp [nrm, Fin.sum_univ_three] at this
  norm_num at this

theorem isHomogeneous_pderiv_zero {Q : R3} (hQ : Q.IsHomogeneous 0) (i : Fin 3) :
    pderiv i Q = 0 := by
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hQ
  rw [hQ, pderiv_C]

theorem lap_isHomogeneous {Q : R3} {m : ℕ} (hQ : Q.IsHomogeneous m) :
    (lap Q).IsHomogeneous (m - 2) := by
  rw [lap_apply]
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  have := (hQ.pderiv (i := i)).pderiv (i := i)
  rwa [show m - 1 - 1 = m - 2 by omega] at this

theorem lap_eq_zero_of_lt {Q : R3} {m : ℕ} (hQ : Q.IsHomogeneous m) (hm : m < 2) : lap Q = 0 := by
  rw [lap_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 := hQ.pderiv (i := i)
  rw [show m - 1 = 0 by omega] at h1
  exact isHomogeneous_pderiv_zero h1 i

/-- `Δ(N Q) = (4m + 6) Q + N ΔQ`. -/
theorem lap_nrm_mul {Q : R3} {m : ℕ} (hQ : Q.IsHomogeneous m) :
    lap (nrm * Q) = ((4 * m + 6 : ℕ) : ℝ) • Q + nrm * lap Q := by
  have euler := hQ.sum_X_mul_pderiv
  have h : ∀ i : Fin 3, pderiv i (pderiv i (nrm * Q)) =
      2 * Q + 4 * (X i * pderiv i Q) + nrm * pderiv i (pderiv i Q) := by
    intro i
    have e1 : pderiv i (nrm * Q) = X i * Q + X i * Q + nrm * pderiv i Q := by
      rw [pderiv_mul, pderiv_nrm]; ring
    rw [e1, map_add, map_add, pderiv_mul, pderiv_mul, pderiv_X_self, pderiv_nrm]
    ring
  rw [lap_apply, lap_apply, Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, euler, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Algebra.smul_def, ← C_eq_algebraMap (R := ℝ)]
  simp only [map_natCast]
  push_cast
  ring

theorem mem_hom_smul {Q : R3} {m : ℕ} (hQ : Q.IsHomogeneous m) (c : ℝ) :
    (c • Q).IsHomogeneous m :=
  (mem_homogeneousSubmodule _ _).mp (Submodule.smul_mem _ c ((mem_homogeneousSubmodule _ _).mpr hQ))

/-- The operator `Q ↦ c Q + N ΔQ` is injective on homogeneous polynomials of degree `m` when
`c ≥ 4m + 6`. -/
theorem inj_aux : ∀ (m : ℕ) (c0 : ℝ), 0 ≤ c0 → ∀ Q : R3, Q.IsHomogeneous m →
    (c0 + (4 * m + 6 : ℕ)) • Q + nrm * lap Q = 0 → Q = 0
  | m, c0, hc0, Q, hQ, h => by
    have hc : 0 < c0 + ((4 * m + 6 : ℕ) : ℝ) := by positivity
    by_cases hm : m < 2
    · rw [lap_eq_zero_of_lt hQ hm, mul_zero, add_zero] at h
      exact (smul_eq_zero.mp h).resolve_left hc.ne'
    · push Not at hm
      have hc' : 0 < c0 + ((4 * m + 6 : ℕ) : ℝ) := hc
      obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = c0 + ((4 * m + 6 : ℕ) : ℝ) := ⟨_, rfl⟩
      rw [← hcdef] at h hc'
      obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : R3, Q₁ = (-c⁻¹) • lap Q := ⟨_, rfl⟩
      have hQ₁h : Q₁.IsHomogeneous (m - 2) := hQ₁ ▸ mem_hom_smul (lap_isHomogeneous hQ) _
      have this : c • Q = -(nrm * lap Q) := eq_neg_of_add_eq_zero_left h
      have hQeq : Q = nrm * Q₁ := by
        rw [hQ₁, mul_smul_comm, neg_smul, ← smul_neg, ← this, smul_smul,
          inv_mul_cancel₀ hc'.ne', one_smul]
      have hlap : lap Q = ((4 * (m - 2) + 6 : ℕ) : ℝ) • Q₁ + nrm * lap Q₁ := by
        rw [hQeq]; exact lap_nrm_mul hQ₁h
      have h' := h
      rw [hlap] at h'
      rw [hQeq] at h'
      have key : nrm * ((c + ((4 * (m - 2) + 6 : ℕ) : ℝ)) • Q₁ + nrm * lap Q₁) = 0 := by
        rw [← h']; simp only [smul_eq_C_mul, map_add]; ring
      have key2 := (mul_eq_zero.mp key).resolve_left nrm_ne_zero
      have hQ₁0 : Q₁ = 0 := inj_aux (m - 2) c hc'.le Q₁ hQ₁h key2
      rw [hQeq, hQ₁0, mul_zero]
  termination_by m => m
  decreasing_by omega

/-- The operator `Q ↦ Δ(N Q)` on homogeneous polynomials of degree `m`. -/
noncomputable def opT (m : ℕ) : homogeneousSubmodule (Fin 3) ℝ m →ₗ[ℝ]
    homogeneousSubmodule (Fin 3) ℝ m where
  toFun Q := ⟨lap (nrm * Q.1), by
    have hQ : Q.1.IsHomogeneous m := Q.2
    rw [mem_homogeneousSubmodule, lap_nrm_mul hQ]
    refine (mem_hom_smul hQ _).add ?_
    by_cases hm : m < 2
    · rw [lap_eq_zero_of_lt hQ hm, mul_zero]; exact isHomogeneous_zero _ _ _
    · have := isHomogeneous_nrm.mul (lap_isHomogeneous hQ)
      rwa [show 2 + (m - 2) = m by omega] at this⟩
  map_add' P Q := by ext1; simp [mul_add]
  map_smul' c P := by ext1; simp

theorem opT_injective (m : ℕ) : Function.Injective (opT m) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro Q hQ
  have h : lap (nrm * Q.1) = 0 := congrArg Subtype.val hQ
  have hQh : Q.1.IsHomogeneous m := Q.2
  rw [lap_nrm_mul hQh] at h
  ext1
  exact inj_aux m 0 le_rfl Q.1 hQh (by simpa using h)

theorem opT_surjective (m : ℕ) : Function.Surjective (opT m) := by
  have : Module.Finite ℝ (homogeneousSubmodule (Fin 3) ℝ m) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (σ := Fin 3) (R := ℝ) m)
  exact LinearMap.injective_iff_surjective.mp (opT_injective m)

/-- **Fischer decomposition.** -/
theorem fischer {P : R3} {d : ℕ} (hP : P.IsHomogeneous d) (hd : 2 ≤ d) :
    ∃ H Q : R3, H.IsHomogeneous d ∧ lap H = 0 ∧ Q.IsHomogeneous (d - 2) ∧ P = H + nrm * Q := by
  have hL : lap P ∈ homogeneousSubmodule (Fin 3) ℝ (d - 2) := lap_isHomogeneous hP
  obtain ⟨Q, hQ⟩ := opT_surjective (d - 2) ⟨lap P, hL⟩
  have hQv : lap (nrm * Q.1) = lap P := congrArg Subtype.val hQ
  have hQh : Q.1.IsHomogeneous (d - 2) := Q.2
  have hNQ : (nrm * Q.1).IsHomogeneous d := by
    have := isHomogeneous_nrm.mul hQh
    rwa [show 2 + (d - 2) = d by omega] at this
  refine ⟨P - nrm * Q.1, Q.1, hP.sub hNQ, ?_, hQh, by ring⟩
  rw [map_sub, hQv, sub_self]

/-! ### Iterated Laplacians -/

theorem lap_iter_isHomogeneous {Q : R3} {m : ℕ} (hQ : Q.IsHomogeneous m) :
    ∀ n, (lap^[n] Q).IsHomogeneous (m - 2 * n)
  | 0 => by simpa using hQ
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    have := lap_isHomogeneous (lap_iter_isHomogeneous hQ n)
    rwa [show m - 2 * n - 2 = m - 2 * (n + 1) by omega] at this

/-- `Δ^{n}(N Q) = N Δ^n Q + n(4m − 4n + 10) Δ^{n−1} Q` for `Q` homogeneous of degree `m`,
`1 ≤ n`, `2n ≤ m + 2`. -/
theorem lap_iter_nrm_mul {Q : R3} {m : ℕ} (hQ : Q.IsHomogeneous m) :
    ∀ n, 1 ≤ n → 2 * n ≤ m + 2 →
      lap^[n] (nrm * Q) = nrm * lap^[n] Q +
        ((n : ℝ) * (4 * m - 4 * n + 10)) • lap^[n - 1] Q
  | 0, h, _ => absurd h (by omega)
  | 1, _, _ => by
    simp only [Function.iterate_one, Nat.sub_self, Function.iterate_zero, id]
    rw [lap_nrm_mul hQ]
    push_cast
    module
  | n + 2, _, hn => by
    have ih := lap_iter_nrm_mul hQ (n + 1) (by omega) (by omega)
    have hc := lap_nrm_mul (lap_iter_isHomogeneous hQ (n + 1))
    rw [show n + 1 - 1 = n by omega] at ih
    rw [show n + 2 - 1 = n + 1 by omega]
    have hX : lap (lap^[n] Q) = lap^[n + 1] Q := (Function.iterate_succ_apply' lap n Q).symm
    rw [Function.iterate_succ_apply' lap (n + 1) (nrm * Q), ih, map_add, map_smul, hc, hX,
      Function.iterate_succ_apply' lap (n + 1) Q]
    rw [show ((4 * (m - 2 * (n + 1)) + 6 : ℕ) : ℝ) = 4 * m - 8 * (n + 1) + 6 by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring]
    push_cast
    module

end ThreeSquares.Duke
