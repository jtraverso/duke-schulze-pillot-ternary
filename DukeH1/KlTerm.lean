/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.PetUnfold
public import DukeH1.BesselInt

/-!
# The contribution of one double coset to the Fourier coefficient of `P`

For `γ = (a b; c d)` with `c > 0`:
* `phi_shift`: `φ_γ(w − d/c) = κ(a,c)^{−3} c^{−k} w^{−k} e(na/c) e(−(n/c²)/w)`;
* `integral_phi_pos`: `∫_ℝ φ_γ(x + iy) e^{−2πinx} dx
     = κ(a,c)^{−3} c^{−k} e(n(a+d)/c) (−2πi)^k n^{k−1} e^{−2πny} S_k(4π²n²/c²)`;
* `integrable_phi_pos`: `x ↦ φ_γ(x + iy)` is integrable on `ℝ` (for `4 ∣ c`).
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares.Poin

open Complex UpperHalfPlane ModularGroup MeasureTheory ThreeSquares.FD ThreeSquares.Mult
  ThreeSquares.Lip Filter Topology

open scoped MatrixGroups Real ComplexConjugate

variable (ℓ : ℕ) (n : ℕ)

theorem ofReal_mul_cpow {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : w ≠ 0) (s : ℂ) :
    ((c : ℂ) * w) ^ s = (c : ℂ) ^ s * w ^ s := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  apply cpow_mul_of_log hc0 hw
  apply Complex.log_mul hc0 hw
  rw [Complex.arg_ofReal_of_nonneg hc.le, zero_add]
  exact ⟨Complex.neg_pi_lt_arg w, Complex.arg_le_pi w⟩

theorem jk_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) {z : ℂ} (hz : 0 < z.im) :
    jk ℓ γ z = kap (γ 0 0) (γ 1 0) ^ 3 * den γ z ^ (kw ℓ : ℂ) := by
  have hd := den_ne_zero γ hz
  unfold jk
  rw [show jm γ z = kap (γ 0 0) (γ 1 0) * den γ z ^ (1 / 2 : ℂ) by simp [jm, hc, den]]
  rw [mul_pow, ← cpow_nat_mul, mul_assoc, ← cpow_natCast (den γ z) ℓ, ← cpow_add _ _ hd]
  congr 2
  unfold kw; push_cast; ring

theorem phi_shift (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) {w : ℂ} (hw : 0 < w.im) :
    phi ℓ n γ (w - (γ 1 1 : ℂ) / (γ 1 0)) =
      (kap (γ 0 0) (γ 1 0) ^ 3)⁻¹ * ((γ 1 0 : ℝ) : ℂ) ^ (-(kw ℓ : ℂ)) * w ^ (-(kw ℓ : ℂ)) *
        cexp (2 * π * Complex.I * n * ((γ 0 0 : ℂ) / (γ 1 0))) *
          cexp (-(2 * π * Complex.I * (((n : ℝ) / (γ 1 0 : ℝ) ^ 2 : ℝ) : ℂ) / w)) := by
  have hc0 : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hcR : (0 : ℝ) < (γ 1 0 : ℝ) := by exact_mod_cast hc
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  set z := w - (γ 1 1 : ℂ) / (γ 1 0)
  have hz : 0 < z.im := by simp [z, hw]
  have hden : den γ z = ((γ 1 0 : ℝ) : ℂ) * w := by
    simp only [den, z]; push_cast; field_simp; ring
  have hcz : (γ 1 0 : ℂ) * z + γ 1 1 = (γ 1 0 : ℂ) * w := by
    simp only [z]; field_simp; ring
  have hmob : mob γ z = (γ 0 0 : ℂ) / (γ 1 0) + (-1 / ((γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * w))) := by
    unfold mob
    rw [gamma_sub _ _ _ _ (det_eq γ) z hc0 (by rw [hcz]; exact mul_ne_zero hc0 hw0), hcz]
  unfold phi
  rw [jk_pos ℓ γ hc hz, hden, ofReal_mul_cpow hcR hw0, hmob, mul_add, Complex.exp_add]
  rw [mul_inv, mul_inv, ← cpow_neg, ← cpow_neg]
  have e : 2 * π * Complex.I * n * (-1 / ((γ 1 0 : ℂ) * ((γ 1 0 : ℂ) * w))) =
      -(2 * π * Complex.I * (((n : ℝ) / (γ 1 0 : ℝ) ^ 2 : ℝ) : ℂ) / w) := by
    push_cast; field_simp
  rw [e]
  ring

theorem integral_phi_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) {y : ℝ} (hy : 0 < y) (hn : 0 < n) :
    ∫ x : ℝ, phi ℓ n γ ((x : ℂ) + y * Complex.I) * cexp (-(2 * π * Complex.I * n * x)) =
      (kap (γ 0 0) (γ 1 0) ^ 3)⁻¹ * ((γ 1 0 : ℝ) : ℂ) ^ (-(kw ℓ : ℂ)) *
        cexp (2 * π * Complex.I * n * (((γ 0 0 : ℂ) + γ 1 1) / (γ 1 0))) *
        ((-(2 * π * Complex.I)) ^ (kw ℓ : ℂ) * ((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1) *
          Real.exp (-(2 * π * n * y)) *
          besS (kw ℓ) (4 * π ^ 2 * ((n : ℝ) / (γ 1 0 : ℝ) ^ 2) * n)) := by
  have hk : 1 < kw ℓ := by unfold kw; have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ; linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : (0 : ℝ) ≤ (n : ℝ) / (γ 1 0 : ℝ) ^ 2 := by positivity
  have hc0 : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set t : ℝ := (γ 1 1 : ℝ) / (γ 1 0 : ℝ)
  rw [← integral_sub_right_eq_self _ t]
  have hpt : ∀ x : ℝ, phi ℓ n γ (((x - t : ℝ) : ℂ) + y * Complex.I) * cexp (-(2 * π * Complex.I * n * ((x - t : ℝ) : ℂ))) =
      (kap (γ 0 0) (γ 1 0) ^ 3)⁻¹ * ((γ 1 0 : ℝ) : ℂ) ^ (-(kw ℓ : ℂ)) *
        cexp (2 * π * Complex.I * n * (((γ 0 0 : ℂ) + γ 1 1) / (γ 1 0))) *
        (((x : ℂ) + y * Complex.I) ^ (-((kw ℓ : ℝ) : ℂ)) * cexp (-(2 * π * Complex.I * ((n : ℝ) : ℂ) * x)) *
          cexp (-(2 * π * Complex.I * (((n : ℝ) / (γ 1 0 : ℝ) ^ 2 : ℝ) : ℂ) / ((x : ℂ) + y * Complex.I)))) := by
    intro x
    have hw : 0 < ((x : ℂ) + y * Complex.I).im := by simp [hy]
    have e1 : ((x - t : ℝ) : ℂ) + y * Complex.I = ((x : ℂ) + y * Complex.I) - (γ 1 1 : ℂ) / (γ 1 0) := by
      simp only [t]; push_cast; ring
    rw [e1, phi_shift ℓ n γ hc hw]
    have e2 : cexp (2 * π * Complex.I * n * ((γ 0 0 : ℂ) / (γ 1 0))) * cexp (-(2 * π * Complex.I * n * ((x - t : ℝ) : ℂ))) =
        cexp (2 * π * Complex.I * n * (((γ 0 0 : ℂ) + γ 1 1) / (γ 1 0))) * cexp (-(2 * π * Complex.I * ((n : ℝ) : ℂ) * x)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [t]; push_cast; field_simp; ring
    linear_combination ((kap (γ 0 0) (γ 1 0) ^ 3)⁻¹ * ((γ 1 0 : ℝ) : ℂ) ^ (-(kw ℓ : ℂ)) *
      ((x : ℂ) + y * Complex.I) ^ (-(kw ℓ : ℂ)) *
      cexp (-(2 * π * Complex.I * (((n : ℝ) / (γ 1 0 : ℝ) ^ 2 : ℝ) : ℂ) / ((x : ℂ) + y * Complex.I)))) * e2
  simp_rw [hpt]
  rw [integral_const_mul, bessel_integral hk hA hnR hy]
  push_cast
  ring

theorem integrable_phi_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) (h4 : (4 : ℤ) ∣ γ 1 0) {y : ℝ}
    (hy : 0 < y) : Integrable fun x : ℝ => phi ℓ n γ ((x : ℂ) + y * Complex.I) := by
  have hk : 1 < kw ℓ := by unfold kw; have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ; linarith
  have hcR : (0 : ℝ) < (γ 1 0 : ℝ) := by exact_mod_cast hc
  set t : ℝ := (γ 1 1 : ℝ) / (γ 1 0 : ℝ)
  have hint := ((integrable_norm_rpow hk hy).comp_add_right t).const_mul ((γ 1 0 : ℝ) ^ (-kw ℓ))
  refine hint.mono' ((measurable_phi ℓ n γ).comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hz : 0 < ((x : ℂ) + y * Complex.I).im := by simp [hy]
  have hd := den_ne_zero γ hz
  have hc0 : (γ 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hden : den γ ((x : ℂ) + y * Complex.I) = ((γ 1 0 : ℝ) : ℂ) * (((x + t : ℝ) : ℂ) + y * Complex.I) := by
    simp only [den, t]; push_cast; field_simp; ring
  have hD : ‖den γ ((x : ℂ) + y * Complex.I)‖ = (γ 1 0 : ℝ) * ‖((x + t : ℝ) : ℂ) + y * Complex.I‖ := by
    rw [hden, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcR]
  unfold phi
  rw [norm_mul, norm_inv, norm_jk ℓ γ h4 hz, norm_cexp_n, hD]
  have hm : 0 < (mob γ ((x : ℂ) + y * Complex.I)).im := im_mob_pos γ hz
  have hexp : Real.exp (-(2 * π * n * (mob γ ((x : ℂ) + y * Complex.I)).im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have : 0 ≤ 2 * π * n * (mob γ ((x : ℂ) + y * Complex.I)).im :=
        mul_nonneg (by positivity) hm.le
      linarith)
  have hnz : 0 < ‖((x + t : ℝ) : ℂ) + y * Complex.I‖ := norm_pos_iff.mpr (z_ne_zero hy)
  rw [Real.mul_rpow hcR.le hnz.le, show kw ℓ = 3 / 2 + ℓ from rfl, Real.rpow_neg hcR.le,
    Real.rpow_neg hnz.le, mul_inv]
  calc (((γ 1 0 : ℝ) ^ ((3 : ℝ) / 2 + ℓ))⁻¹ * (‖((x + t : ℝ) : ℂ) + y * Complex.I‖ ^ ((3 : ℝ) / 2 + ℓ))⁻¹) *
        Real.exp (-(2 * π * n * (mob γ ((x : ℂ) + y * Complex.I)).im))
      ≤ ((γ 1 0 : ℝ) ^ ((3 : ℝ) / 2 + ℓ))⁻¹ * (‖((x + t : ℝ) : ℂ) + y * Complex.I‖ ^ ((3 : ℝ) / 2 + ℓ))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by simp

end ThreeSquares.Poin
