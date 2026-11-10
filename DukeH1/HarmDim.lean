/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.Fischer

/-!
# Dimension of harmonic polynomials in three variables

* `finrank_hom`: homogeneous polynomials of degree `m` in three variables form a space of dimension
  `(m+1)(m+2)/2`.
* `finrank_harm`: harmonic homogeneous polynomials of degree `ℓ ≥ 2` form a space of dimension
  `2ℓ+1` (the Laplacian maps `Hom_ℓ` onto `Hom_{ℓ−2}` by the Fischer decomposition).
-/

@[expose] public section

namespace ThreeSquares.Duke

open MvPolynomial Finset

/-- Exponent vectors of total degree `m`. -/
def degSet (m : ℕ) : Set (Fin 3 →₀ ℕ) := {d | Finsupp.weight (1 : Fin 3 → ℕ) d = m}

theorem weight_one_fin3 (d : Fin 3 →₀ ℕ) : Finsupp.weight (1 : Fin 3 → ℕ) d = d 0 + d 1 + d 2 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fin.sum_univ_three]

/-- Pairs `(a, b)` with `a + b ≤ m`. -/
def pairSet (m : ℕ) : Finset (ℕ × ℕ) := ((range (m + 1)) ×ˢ (range (m + 1))).filter fun p => p.1 + p.2 ≤ m

theorem card_pairSet : ∀ m, (pairSet m).card = (m + 1) * (m + 2) / 2
  | 0 => by decide
  | m + 1 => by
    have h : pairSet (m + 1) = pairSet m ∪ ((range (m + 2)).image fun a => (a, m + 1 - a)) := by
      ext ⟨a, b⟩
      simp only [pairSet, mem_union, mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq]
      constructor
      · intro ⟨⟨ha, hb⟩, hab⟩
        by_cases h : a + b ≤ m
        · left; exact ⟨⟨by omega, by omega⟩, h⟩
        · right; exact ⟨a, by omega, rfl, by omega⟩
      · rintro (⟨⟨ha, hb⟩, hab⟩ | ⟨c, hc, rfl, rfl⟩)
        · exact ⟨⟨by omega, by omega⟩, by omega⟩
        · exact ⟨⟨by omega, by omega⟩, by omega⟩
    have hdisj : Disjoint (pairSet m) ((range (m + 2)).image fun a => (a, m + 1 - a)) := by
      rw [Finset.disjoint_left]
      rintro ⟨a, b⟩ h1 h2
      simp only [pairSet, mem_filter, mem_product, mem_range, mem_image, Prod.mk.injEq] at h1 h2
      obtain ⟨c, hc, rfl, rfl⟩ := h2
      omega
    rw [h, card_union_of_disjoint hdisj, card_pairSet m, card_image_of_injective _ (fun x y h => by
      simp only [Prod.mk.injEq] at h; exact h.1), card_range]
    have : (m + 1) * (m + 2) % 2 = 0 := Nat.even_iff.mp (Nat.even_mul_succ_self (m + 1))
    have h2 : (m + 1 + 1) * (m + 1 + 2) = (m + 1) * (m + 2) + 2 * (m + 2) := by ring
    rw [h2]
    omega

/-- `degSet m ≃ pairSet m` via `d ↦ (d 0, d 1)`. -/
noncomputable def degEquiv (m : ℕ) : degSet m ≃ (pairSet m : Set (ℕ × ℕ)) where
  toFun d := ⟨(d.1 0, d.1 1), by
    have := d.2; simp only [degSet, Set.mem_setOf_eq, weight_one_fin3] at this
    simp only [pairSet, coe_filter, mem_product, mem_range, Set.mem_setOf_eq]; omega⟩
  invFun p := ⟨Finsupp.equivFunOnFinite.symm ![p.1.1, p.1.2, m - p.1.1 - p.1.2], by
    have := p.2; simp only [pairSet, coe_filter, mem_product, mem_range, Set.mem_setOf_eq] at this
    simp only [degSet, Set.mem_setOf_eq, weight_one_fin3]
    simp; omega⟩
  left_inv d := by
    have := d.2; simp only [degSet, Set.mem_setOf_eq, weight_one_fin3] at this
    apply Subtype.ext
    ext i
    fin_cases i <;> simp <;> omega
  right_inv p := by simp

theorem finrank_hom (m : ℕ) :
    Module.finrank ℝ (homogeneousSubmodule (Fin 3) ℝ m) = (m + 1) * (m + 2) / 2 := by
  have hs : homogeneousSubmodule (Fin 3) ℝ m = restrictSupport ℝ (degSet m) := by
    ext p
    rw [mem_homogeneousSubmodule, mem_restrictSupport_iff]
    constructor
    · intro h d hd
      exact h (mem_support_iff.mp hd)
    · intro h d hd
      exact h (mem_support_iff.mpr hd)
  rw [hs, Module.finrank_eq_nat_card_basis (basisRestrictSupport ℝ (degSet m)),
    Nat.card_congr (degEquiv m)]
  exact (Nat.card_eq_finsetCard (pairSet m)).trans (card_pairSet m)

instance finiteDimensional_hom (m : ℕ) : FiniteDimensional ℝ (homogeneousSubmodule (Fin 3) ℝ m) :=
  Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg (σ := Fin 3) (R := ℝ) m)

/-- The Laplacian `Hom_ℓ → Hom_{ℓ−2}`. -/
noncomputable def lapHom (ℓ : ℕ) : homogeneousSubmodule (Fin 3) ℝ ℓ →ₗ[ℝ]
    homogeneousSubmodule (Fin 3) ℝ (ℓ - 2) where
  toFun P := ⟨lap P.1, lap_isHomogeneous P.2⟩
  map_add' P Q := by ext1; simp
  map_smul' c P := by ext1; simp

theorem lapHom_surjective (ℓ : ℕ) (hℓ : 2 ≤ ℓ) : Function.Surjective (lapHom ℓ) := by
  intro R
  obtain ⟨Q, hQ⟩ := opT_surjective (ℓ - 2) R
  have hQh : Q.1.IsHomogeneous (ℓ - 2) := Q.2
  have hNQ : (nrm * Q.1).IsHomogeneous ℓ := by
    have := isHomogeneous_nrm.mul hQh
    rwa [show 2 + (ℓ - 2) = ℓ by omega] at this
  refine ⟨⟨nrm * Q.1, hNQ⟩, ?_⟩
  ext1
  exact congrArg Subtype.val hQ

/-- **Harmonic polynomials of degree `ℓ ≥ 2` form a space of dimension `2ℓ+1`.** -/
theorem finrank_harm (ℓ : ℕ) (hℓ : 2 ≤ ℓ) : Module.finrank ℝ (LinearMap.ker (lapHom ℓ)) = 2 * ℓ + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 2 := ⟨ℓ - 2, by omega⟩
  have h := LinearMap.finrank_range_add_finrank_ker (lapHom (n + 2))
  rw [LinearMap.range_eq_top.mpr (lapHom_surjective (n + 2) hℓ), finrank_top, finrank_hom,
    finrank_hom] at h
  have e : (n + 2 - 2 + 1) * (n + 2 - 2 + 2) / 2 = (n + 1) * (n + 2) / 2 := by
    rw [show n + 2 - 2 = n by omega]
  rw [e] at h
  have e1 : (n + 2 + 1) * (n + 2 + 2) = (n + 1) * (n + 2) + 2 * (2 * (n + 2) + 1) := by ring
  rw [e1] at h
  have : (n + 1) * (n + 2) % 2 = 0 := Nat.even_iff.mp (Nat.even_mul_succ_self (n + 1))
  omega

end ThreeSquares.Duke
