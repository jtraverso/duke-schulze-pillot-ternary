/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.KlTerm

/-!
# Auxiliary facts for the Fourier coefficient of the Poincaré series

* `integral_eq_tsum_Ico`: `∫_ℝ g = ∑_m ∫_{[0,1)} g(x + m)` for integrable `g`;
* `phi_eq_of_row`: `φ_γ` only depends on the bottom row of `γ`;
* `phi_mul_T`: `φ_{δ T^m}(z) = φ_δ(z + m)`;
* `phi_neg`: `φ_{−γ} = φ_γ` for even `ℓ`.
-/

@[expose] public section

namespace ThreeSquares.Poin

open Complex UpperHalfPlane ModularGroup MeasureTheory ThreeSquares.FD ThreeSquares.Mult
  ThreeSquares.Lip Filter Topology Set

open scoped MatrixGroups Real ComplexConjugate

/-! ### Tiling the line by unit intervals -/

theorem iUnion_Ico_int : (⋃ m : ℤ, Ico (m : ℝ) (m + 1)) = univ := by
  ext x
  simp only [mem_iUnion, mem_Ico, mem_univ, iff_true]
  exact ⟨⌊x⌋, Int.floor_le x, Int.lt_floor_add_one x⟩

theorem pairwise_disjoint_Ico_int : Pairwise (Function.onFun Disjoint fun m : ℤ => Ico (m : ℝ) (m + 1)) := by
  intro m m' hne
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  simp only [mem_Ico] at hx hx'
  apply hne
  have h1 : (m : ℝ) < m' + 1 := lt_of_le_of_lt hx.1 hx'.2
  have h2 : (m' : ℝ) < m + 1 := lt_of_le_of_lt hx'.1 hx.2
  have h1' : m < m' + 1 := by exact_mod_cast h1
  have h2' : m' < m + 1 := by exact_mod_cast h2
  omega

theorem setIntegral_Ico_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E)
    (m : ℤ) : ∫ x in Ico (m : ℝ) (m + 1), g x = ∫ x in Ico (0 : ℝ) 1, g (x + m) := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) (m : ℝ)).setIntegral_preimage_emb
    (measurableEmbedding_addRight (m : ℝ)) g (Ico (m : ℝ) (m + 1))
  have hpre : (fun x : ℝ => x + m) ⁻¹' Ico (m : ℝ) (m + 1) = Ico 0 1 := by
    ext x; simp only [mem_preimage, mem_Ico]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hpre] at h
  exact h.symm

theorem integral_eq_tsum_Ico {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} (hg : Integrable g) :
    ∫ x, g x = ∑' m : ℤ, ∫ x in Ico (0 : ℝ) 1, g (x + m) := by
  have := integral_iUnion (μ := volume) (f := g) (fun m : ℤ => measurableSet_Ico)
    pairwise_disjoint_Ico_int (by rw [iUnion_Ico_int]; exact hg.integrableOn)
  rw [iUnion_Ico_int, Measure.restrict_univ] at this
  rw [this]
  exact tsum_congr fun m => setIntegral_Ico_shift g m

/-! ### Relations between the `φ_γ` -/

variable (ℓ : ℕ) (n : ℕ)

theorem phi_eq_of_row {γ γ' : SL(2, ℤ)} (h4 : (4 : ℤ) ∣ γ 1 0) (e : rowOf γ = rowOf γ') {z : ℂ}
    (hz : 0 < z.im) : phi ℓ n γ' z = phi ℓ n γ z := by
  obtain ⟨m, hm⟩ := eq_T_mul_of_rowOf_eq e
  rw [hm, phi_T_mul ℓ n m γ h4 hz]

theorem phi_mul_T (δ : SL(2, ℤ)) (h4 : (4 : ℤ) ∣ δ 1 0) (m : ℤ) {z : ℂ} (hz : 0 < z.im) :
    phi ℓ n (δ * T ^ m) z = phi ℓ n δ (z + m) := by
  have h := phi_mul ℓ n δ (T ^ m) h4 (dvd4_T_zpow m) hz
  rw [jk_T_zpow, one_mul, mob_T_zpow] at h
  exact h.symm

theorem neg_10 (γ : SL(2, ℤ)) : (-γ) 1 0 = -γ 1 0 := by simp [Matrix.SpecialLinearGroup.coe_neg]
theorem neg_11 (γ : SL(2, ℤ)) : (-γ) 1 1 = -γ 1 1 := by simp [Matrix.SpecialLinearGroup.coe_neg]
theorem neg_00 (γ : SL(2, ℤ)) : (-γ) 0 0 = -γ 0 0 := by simp [Matrix.SpecialLinearGroup.coe_neg]
theorem neg_01 (γ : SL(2, ℤ)) : (-γ) 0 1 = -γ 0 1 := by simp [Matrix.SpecialLinearGroup.coe_neg]

theorem jm_neg (γ : SL(2, ℤ)) (z : ℂ) : jm (-γ) z = jm γ z := by
  unfold jm
  rw [neg_10, neg_11, neg_00]
  by_cases h1 : 0 < γ 1 0
  · have h2 : ¬ (0 < -γ 1 0) := by omega
    have h3 : -γ 1 0 < 0 := by omega
    simp only [h1, h2, h3, if_true, if_false, neg_neg]
  · by_cases h3 : γ 1 0 < 0
    · have h2 : 0 < -γ 1 0 := by omega
      simp only [h1, h2, h3, if_true, if_false]
    · have h0 : γ 1 0 = 0 := by omega
      simp [h0]

theorem mob_neg (γ : SL(2, ℤ)) (z : ℂ) : mob (-γ) z = mob γ z := by
  unfold mob; rw [neg_10, neg_11, neg_00, neg_01]; push_cast; rw [← neg_div_neg_eq]; congr 1 <;> ring

theorem phi_neg {ℓ : ℕ} (hℓ : Even ℓ) (γ : SL(2, ℤ)) (z : ℂ) : phi ℓ n (-γ) z = phi ℓ n γ z := by
  unfold phi jk
  rw [jm_neg, mob_neg, show den (-γ) z = -den γ z by unfold den; rw [neg_10, neg_11]; push_cast; ring,
    hℓ.neg_pow]

end ThreeSquares.Poin
