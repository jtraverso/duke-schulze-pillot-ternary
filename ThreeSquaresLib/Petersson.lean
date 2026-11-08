/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Poincare
public import ThreeSquaresLib.Unfold

/-!
# The Poincaré series: automorphy, periodicity, measurability

* `poin_mob`: `P(γz) = j_k(γ, z) P(z)` for `γ ∈ Γ₀(Q)` (`4 ∣ Q`);
* `poin_add_one`: `P(z + 1) = P(z)`;
* `measurable_poinH`: `z ↦ P(z)` is measurable on `ℍ`.
-/

@[expose] public section

namespace ThreeSquares.Poin

open Complex UpperHalfPlane ModularGroup MeasureTheory ThreeSquares.FD ThreeSquares.Mult Filter
  Topology

open scoped MatrixGroups Real

variable (ℓ : ℕ) (Q n : ℕ)

theorem jk_T_zpow (m : ℤ) (w : ℂ) : jk ℓ (T ^ m) w = 1 := by
  simp [jk, jm, den, coe_T_zpow]

theorem mob_T_zpow (m : ℤ) (w : ℂ) : mob (T ^ m) w = w + m := by
  simp [mob, coe_T_zpow]

theorem dvd4_T_zpow (m : ℤ) : (4 : ℤ) ∣ (T ^ m) 1 0 := by simp [coe_T_zpow]

theorem jk_ne_zero (γ : SL(2, ℤ)) (h4 : (4 : ℤ) ∣ γ 1 0) {z : ℂ} (hz : 0 < z.im) :
    jk ℓ γ z ≠ 0 := by
  have h := norm_jk ℓ γ h4 hz
  have hd : 0 < ‖den γ z‖ := norm_pos_iff.mpr (den_ne_zero γ hz)
  intro h0
  rw [h0, norm_zero] at h
  exact (Real.rpow_pos_of_pos hd _).ne' h.symm

theorem phi_T_mul (m : ℤ) (δ : SL(2, ℤ)) (h4 : (4 : ℤ) ∣ δ 1 0) {z : ℂ} (hz : 0 < z.im) :
    phi ℓ n (T ^ m * δ) z = phi ℓ n δ z := by
  unfold phi
  rw [jk_mul ℓ (T ^ m) δ (dvd4_T_zpow m) h4 hz, jk_T_zpow, one_mul, mob_mul _ _ hz, mob_T_zpow]
  congr 1
  rw [mul_add, Complex.exp_add, show 2 * π * Complex.I * n * (m : ℂ) = ((n * m : ℤ) : ℂ) *
    (2 * π * Complex.I) by push_cast; ring, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem phi_mul (δ γ : SL(2, ℤ)) (hδ : (4 : ℤ) ∣ δ 1 0) (hγ : (4 : ℤ) ∣ γ 1 0) {z : ℂ}
    (hz : 0 < z.im) : phi ℓ n δ (mob γ z) = jk ℓ γ z * phi ℓ n (δ * γ) z := by
  have hne := jk_ne_zero ℓ γ hγ hz
  unfold phi
  rw [jk_mul ℓ δ γ hδ hγ hz, mob_mul δ γ hz, mul_inv]
  set E := cexp (2 * π * Complex.I * n * mob δ (mob γ z))
  rw [show jk ℓ γ z * ((jk ℓ δ (mob γ z))⁻¹ * (jk ℓ γ z)⁻¹ * E) =
    (jk ℓ δ (mob γ z))⁻¹ * E * (jk ℓ γ z * (jk ℓ γ z)⁻¹) by ring, mul_inv_cancel₀ hne, mul_one]

/-- Right multiplication by `γ ∈ Γ₀(Q)` permutes the rows with `Q ∣ r₀`. -/
noncomputable def rowMapQ (γ : SL(2, ℤ)) (hγ : InG0 Q γ) : RowsQ Q ≃ RowsQ Q where
  toFun r := ⟨rowOf (gam r.1 * γ), inG0_mul (inG0_gam r.2) hγ⟩
  invFun r := ⟨rowOf (gam r.1 * γ⁻¹), inG0_mul (inG0_gam r.2) (inG0_inv hγ)⟩
  left_inv r := Subtype.ext ((rowMap γ).left_inv r.1)
  right_inv r := Subtype.ext ((rowMap γ).right_inv r.1)

theorem rowMapQ_apply (γ : SL(2, ℤ)) (hγ : InG0 Q γ) (r : RowsQ Q) :
    ((rowMapQ Q γ hγ) r).1 = rowOf (gam r.1 * γ) := rfl

/-- **Automorphy of the Poincaré series.** -/
theorem poin_mob {Q : ℕ} (hQ : 4 ∣ Q) (γ : SL(2, ℤ)) (hγ : InG0 Q γ) {z : ℂ} (hz : 0 < z.im) :
    poin ℓ Q n (mob γ z) = jk ℓ γ z * poin ℓ Q n z := by
  have h4γ : (4 : ℤ) ∣ γ 1 0 := dvd_trans (show (4 : ℤ) ∣ (Q : ℤ) by exact_mod_cast hQ) hγ
  unfold poin
  have e1 : ∀ r : RowsQ Q, phi ℓ n (gam r.1) (mob γ z) = jk ℓ γ z * phi ℓ n (gam r.1 * γ) z :=
    fun r => phi_mul ℓ n (gam r.1) γ (dvd4_gam hQ r) h4γ hz
  rw [tsum_congr e1, tsum_mul_left]
  refine congrArg (jk ℓ γ z * ·) ?_
  rw [← (rowMapQ Q γ hγ).tsum_eq (fun r : RowsQ Q => phi ℓ n (gam r.1) z)]
  refine tsum_congr fun r => ?_
  obtain ⟨m, hm⟩ := eq_T_mul_gam (gam r.1 * γ)
  have h4 : (4 : ℤ) ∣ (gam (rowOf (gam r.1 * γ))) 1 0 := by
    have h0 : (gam (rowOf (gam r.1 * γ))) 1 0 = (gam r.1 * γ) 1 0 :=
      congrFun (gam_row (rowOf (gam r.1 * γ))) 0
    rw [h0]
    exact dvd_trans (show (4 : ℤ) ∣ (Q : ℤ) by exact_mod_cast hQ) (inG0_mul (inG0_gam r.2) hγ)
  have e2 : phi ℓ n (gam r.1 * γ) z = phi ℓ n (gam (rowOf (gam r.1 * γ))) z := by
    rw [← phi_T_mul ℓ n m _ h4 hz, ← hm]
  rw [e2, rowMapQ_apply]

theorem inG0_T (Q : ℕ) : InG0 Q T := by unfold InG0; simp [T]

theorem poin_add_one {Q : ℕ} (hQ : 4 ∣ Q) {z : ℂ} (hz : 0 < z.im) :
    poin ℓ Q n (z + 1) = poin ℓ Q n z := by
  have h := poin_mob ℓ n hQ T (inG0_T Q) hz
  have hT : T = T ^ (1 : ℤ) := by simp
  rw [hT, jk_T_zpow, one_mul, mob_T_zpow] at h
  simpa using h

/-! ### Measurability -/

theorem measurable_jm (γ : SL(2, ℤ)) : Measurable (jm γ) := by
  unfold jm
  split_ifs
  · exact measurable_const.mul ((by fun_prop : Measurable fun z : ℂ => (γ 1 0 : ℂ) * z + γ 1 1).pow_const _)
  · exact measurable_const.mul ((by fun_prop : Measurable fun z : ℂ =>
      ((-γ 1 0 : ℤ) : ℂ) * z + ((-γ 1 1 : ℤ) : ℂ)).pow_const _)
  · exact measurable_const

theorem measurable_phi (γ : SL(2, ℤ)) : Measurable (phi ℓ n γ) := by
  unfold phi jk mob den
  have := measurable_jm γ
  fun_prop

theorem summable_phi {Q : ℕ} (hℓ : 1 ≤ ℓ) (hQ : 4 ∣ Q) (hn : 0 < n) (z : ℍ) :
    Summable (fun r : RowsQ Q => phi ℓ n (gam r.1) z) := by
  obtain ⟨M, -, hM⟩ := poin_bound ℓ n hℓ hQ hn
  exact (hM z).1.of_norm

theorem measurable_poinH {Q : ℕ} (hℓ : 1 ≤ ℓ) (hQ : 4 ∣ Q) (hn : 0 < n) :
    Measurable fun z : ℍ => poin ℓ Q n z := by
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset (RowsQ Q)))
    (f := fun s (z : ℍ) => ∑ r ∈ s, phi ℓ n (gam r.1) z) (fun s => ?_) ?_
  · exact Finset.measurable_sum _ fun r _ => (measurable_phi ℓ n _).comp measurable_coe
  · refine tendsto_pi_nhds.mpr fun z => ?_
    exact (summable_phi ℓ n hℓ hQ hn z).hasSum

end ThreeSquares.Poin
