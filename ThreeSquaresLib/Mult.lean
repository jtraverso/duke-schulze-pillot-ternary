/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.GaussNorm
public import ThreeSquaresLib.ThetaBound
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# The theta multiplier on `Γ₀(4)`

For `γ = (a b; c d) ∈ SL(2, ℤ)` with `4 ∣ c` we define the weight-`1/2` multiplier `jm γ z`
(normalized so that `jm (-γ) = jm γ`), and prove

* `thetaFn_mob`: `θ(γz) = jm γ z · θ(z)`;
* `jm_mul`: the cocycle relation `jm (γ₁γ₂) z = jm γ₁ (γ₂z) · jm γ₂ z` on `ℍ` (from the
  automorphy of `θ` near `i∞`, where `θ ≠ 0`, and the identity theorem);
* `norm_jm`: `|jm γ z| = |cz + d|^{1/2}`;
* `theta3_mob`: `θ_{u,ℓ}(γz) = jm γ z ^ 3 (cz + d)^ℓ θ_{u,ℓ}(z)` for even `ℓ`.
-/

@[expose] public section

namespace ThreeSquares.Mult

open Complex

open scoped MatrixGroups Real

/-- Möbius action of `SL(2, ℤ)` on `ℂ`. -/
noncomputable def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)

/-- The automorphy denominator `cz + d`. -/
noncomputable def den (γ : SL(2, ℤ)) (z : ℂ) : ℂ := (γ 1 0 : ℂ) * z + γ 1 1

/-- `κ(a, c) = G(a, 0; c) / ((1 + i)√c)` for `c > 0` (and `1` otherwise). -/
noncomputable def kap (a c : ℤ) : ℂ :=
  if h : 0 < c then
    haveI : NeZero c.toNat := ⟨by omega⟩
    gaussQ ((a : ZMod c.toNat)) 0 / ((1 + I) * (Real.sqrt (c.toNat : ℕ) : ℂ))
  else 1

/-- The weight-`1/2` theta multiplier, normalized by the sign of `c`. -/
noncomputable def jm (γ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  if 0 < γ 1 0 then kap (γ 0 0) (γ 1 0) * ((γ 1 0 : ℂ) * z + γ 1 1) ^ (1 / 2 : ℂ)
  else if γ 1 0 < 0 then kap (-γ 0 0) (-γ 1 0) * ((-γ 1 0 : ℤ) * z + (-γ 1 1 : ℤ)) ^ (1 / 2 : ℂ)
  else 1

theorem det_eq (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have := γ.det_coe
  rwa [Matrix.det_fin_two] at this

theorem thetaFn_add_int (z : ℂ) (m : ℤ) : thetaFn (z + m) = thetaFn z := by
  unfold thetaFn
  refine tsum_congr fun n => ?_
  rw [mul_add, Complex.exp_add]
  rw [show 2 * π * I * (n : ℂ) ^ 2 * (m : ℂ) = ((n ^ 2 * m : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem den_ne_zero (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : den γ z ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [den] at him hre
  rcases him with h0 | h0
  · rw [h0] at hre
    simp at hre
    have := det_eq γ
    rw [h0, hre] at this
    simp at this
  · linarith

theorem im_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    (mob γ z).im = z.im / Complex.normSq (den γ z) := by
  have h : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
    exact_mod_cast det_eq γ
  unfold mob den
  rw [Complex.div_im, ← sub_div]
  congr 1
  simp
  linear_combination z.im * h

theorem im_mob_pos (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : 0 < (mob γ z).im := by
  rw [im_mob γ hz]
  exact div_pos hz (Complex.normSq_pos.mpr (den_ne_zero γ hz))

theorem mul_00 (γ₁ γ₂ : SL(2, ℤ)) : (γ₁ * γ₂) 0 0 = γ₁ 0 0 * γ₂ 0 0 + γ₁ 0 1 * γ₂ 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
theorem mul_01 (γ₁ γ₂ : SL(2, ℤ)) : (γ₁ * γ₂) 0 1 = γ₁ 0 0 * γ₂ 0 1 + γ₁ 0 1 * γ₂ 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
theorem mul_10 (γ₁ γ₂ : SL(2, ℤ)) : (γ₁ * γ₂) 1 0 = γ₁ 1 0 * γ₂ 0 0 + γ₁ 1 1 * γ₂ 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
theorem mul_11 (γ₁ γ₂ : SL(2, ℤ)) : (γ₁ * γ₂) 1 1 = γ₁ 1 0 * γ₂ 0 1 + γ₁ 1 1 * γ₂ 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem mob_mul (γ₁ γ₂ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    mob (γ₁ * γ₂) z = mob γ₁ (mob γ₂ z) := by
  have h2 := den_ne_zero γ₂ hz
  have h1 := den_ne_zero γ₁ (im_mob_pos γ₂ hz)
  unfold den mob at *
  set D := (γ₂ 1 0 : ℂ) * z + γ₂ 1 1
  set N := (γ₂ 0 0 : ℂ) * z + γ₂ 0 1
  have h1' : (γ₁ 1 0 : ℂ) * N + γ₁ 1 1 * D ≠ 0 := by
    intro h; apply h1
    rw [show (γ₁ 1 0 : ℂ) * (N / D) + γ₁ 1 1 = ((γ₁ 1 0 : ℂ) * N + γ₁ 1 1 * D) / D by
      field_simp, h, zero_div]
  rw [mul_00, mul_01, mul_10, mul_11]
  push_cast
  rw [div_eq_div_iff (by intro h; apply h1'; rw [← h]; ring) (by
    intro h; apply h1; rw [← h])]
  field_simp
  ring

theorem den_mul (γ₁ γ₂ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    den (γ₁ * γ₂) z = den γ₁ (mob γ₂ z) * den γ₂ z := by
  have h2 := den_ne_zero γ₂ hz
  unfold den mob
  unfold den at h2
  rw [mul_10, mul_11]
  push_cast
  field_simp
  ring

/-! ### Automorphy of `θ` -/

theorem cast_toNat {c : ℤ} (hc : 0 < c) : ((c.toNat : ℕ) : ℂ) = (c : ℂ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hc.le]

theorem thetaFn_mob (γ : SL(2, ℤ)) (h4 : (4 : ℤ) ∣ γ 1 0) {z : ℂ} (hz : 0 < z.im) :
    thetaFn (mob γ z) = jm γ z * thetaFn z := by
  have hdet := det_eq γ
  by_cases hpos : 0 < γ 1 0
  · haveI : NeZero (γ 1 0).toNat := ⟨by omega⟩
    have h := thetaFn_gamma (γ 1 0).toNat (by omega) (γ 0 0) (γ 0 1) (γ 1 1)
      (by rw [Int.toNat_of_nonneg hpos.le]; linarith) z hz
    rw [cast_toNat hpos] at h
    simp only [jm, hpos, if_true, kap, ↓reduceDIte, ↓reduceIte]
    rw [show mob γ z = ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) from rfl, h]
  by_cases hneg : γ 1 0 < 0
  · have hpos' : 0 < -γ 1 0 := by omega
    haveI : NeZero (-γ 1 0).toNat := ⟨by omega⟩
    have h := thetaFn_gamma (-γ 1 0).toNat (by omega) (-γ 0 0) (-γ 0 1) (-γ 1 1)
      (by rw [Int.toNat_of_nonneg hpos'.le]; linarith) z hz
    rw [cast_toNat hpos'] at h
    simp only [jm, hpos, if_false, hneg, if_true, kap, hpos', ↓reduceDIte, ↓reduceIte]
    have hm : mob γ z = (((-γ 0 0 : ℤ) : ℂ) * z + ((-γ 0 1 : ℤ) : ℂ)) /
        (((-γ 1 0 : ℤ) : ℂ) * z + ((-γ 1 1 : ℤ) : ℂ)) := by
      unfold mob; push_cast; rw [← neg_div_neg_eq]; congr 1 <;> ring
    rw [hm, h]
  · have h0 : γ 1 0 = 0 := by omega
    rw [h0, mul_zero, sub_zero] at hdet
    simp only [jm, hpos, hneg, if_false, one_mul]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
    · have : mob γ z = z + ((γ 0 1 : ℤ) : ℂ) := by
        unfold mob; rw [ha, hd, h0]; simp
      rw [this, thetaFn_add_int]
    · have : mob γ z = z + ((-γ 0 1 : ℤ) : ℂ) := by
        unfold mob; rw [ha, hd, h0]; push_cast; field_simp; ring
      rw [this, thetaFn_add_int]

/-! ### Nonvanishing of `θ` high in the half-plane -/

theorem thetaFn_eq_jacobiTheta (z : ℂ) : thetaFn z = jacobiTheta (2 * z) := by
  unfold thetaFn jacobiTheta
  exact tsum_congr fun n => by ring_nf

theorem thetaFn_ne_zero {z : ℂ} (hz : 1 < z.im) : thetaFn z ≠ 0 := by
  rw [thetaFn_eq_jacobiTheta]
  have him : (2 * z).im = 2 * z.im := by simp
  have hpos : 0 < (2 * z).im := by rw [him]; linarith
  have hb := norm_jacobiTheta_sub_one_le hpos
  set e := Real.exp (-π * (2 * z).im) with he
  have he0 : 0 < e := Real.exp_pos _
  have he3 : e < 1 / 3 := by
    have h1 : Real.exp (2 * π) > 3 := by
      have := Real.add_one_le_exp (2 * π)
      linarith [Real.two_le_pi]
    have h2 : e ≤ Real.exp (-(2 * π)) := by
      rw [he]; apply Real.exp_le_exp.mpr; rw [him]; nlinarith [Real.pi_pos]
    rw [Real.exp_neg] at h2
    calc e ≤ (Real.exp (2 * π))⁻¹ := h2
      _ < 1 / 3 := by rw [one_div]; exact inv_strictAnti₀ (by norm_num) h1
  have hlt : 2 / (1 - e) * e < 1 := by
    rw [div_mul_eq_mul_div, div_lt_one (by linarith)]; linarith
  intro h0
  rw [h0, zero_sub, norm_neg, norm_one] at hb
  linarith

/-! ### Holomorphy of the multiplier -/

theorem differentiableAt_jm (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (jm γ) z := by
  unfold jm
  split_ifs with h1 h2
  · refine (DifferentiableAt.const_mul ?_ _)
    refine DifferentiableAt.cpow_const (by fun_prop) ?_
    rw [Complex.mem_slitPlane_iff]; right
    simp; exact ⟨by exact_mod_cast h1.ne', hz.ne'⟩
  · refine (DifferentiableAt.const_mul ?_ _)
    refine DifferentiableAt.cpow_const (by fun_prop) ?_
    rw [Complex.mem_slitPlane_iff]; right
    simp; exact ⟨by exact_mod_cast h2.ne, hz.ne'⟩
  · exact differentiableAt_const _

theorem differentiableAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (mob γ) z := by
  unfold mob
  exact DifferentiableAt.div (by fun_prop) (by fun_prop) (den_ne_zero γ hz)

/-! ### The cocycle relation -/

theorem dvd_mul_10 (γ₁ γ₂ : SL(2, ℤ)) (h1 : (4 : ℤ) ∣ γ₁ 1 0) (h2 : (4 : ℤ) ∣ γ₂ 1 0) :
    (4 : ℤ) ∣ (γ₁ * γ₂) 1 0 := by
  rw [mul_10]
  exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)

theorem jm_mul (γ₁ γ₂ : SL(2, ℤ)) (h1 : (4 : ℤ) ∣ γ₁ 1 0) (h2 : (4 : ℤ) ∣ γ₂ 1 0) {z : ℂ}
    (hz : 0 < z.im) : jm (γ₁ * γ₂) z = jm γ₁ (mob γ₂ z) * jm γ₂ z := by
  let U : Set ℂ := {w | 0 < w.im}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hF : AnalyticOnNhd ℂ (jm (γ₁ * γ₂)) U :=
    DifferentiableOn.analyticOnNhd (fun w hw => (differentiableAt_jm _ hw).differentiableWithinAt) hU
  have hG : AnalyticOnNhd ℂ (fun w => jm γ₁ (mob γ₂ w) * jm γ₂ w) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hU
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.mul ?_ (differentiableAt_jm _ hw))
    exact (differentiableAt_jm γ₁ (im_mob_pos γ₂ hw)).comp w (differentiableAt_mob γ₂ hw)
  have hconv : Convex ℝ U := convex_halfSpace_im_gt 0
  have heq : ∀ w : ℂ, 1 < w.im → jm (γ₁ * γ₂) w = jm γ₁ (mob γ₂ w) * jm γ₂ w := by
    intro w hw
    have hw0 : 0 < w.im := by linarith
    have hθ := thetaFn_ne_zero hw
    have e1 := thetaFn_mob (γ₁ * γ₂) (dvd_mul_10 γ₁ γ₂ h1 h2) hw0
    rw [mob_mul γ₁ γ₂ hw0, thetaFn_mob γ₁ h1 (im_mob_pos γ₂ hw0), thetaFn_mob γ₂ h2 hw0] at e1
    exact (mul_right_cancel₀ hθ (by rw [← e1]; ring)).symm
  have hev : jm (γ₁ * γ₂) =ᶠ[nhds (2 * I)] fun w => jm γ₁ (mob γ₂ w) * jm γ₂ w := by
    have : {w : ℂ | 1 < w.im} ∈ nhds (2 * I) :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by simp)
    filter_upwards [this] with w hw using heq w hw
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG hconv.isPreconnected (by simp [U]) hev hz

/-! ### Norm of the multiplier -/

theorem norm_kap {a c : ℤ} (hc : 0 < c) (h4 : (4 : ℤ) ∣ c) (hu : ∃ d : ℤ, a * d ≡ 1 [ZMOD c]) :
    ‖kap a c‖ = 1 := by
  simp only [kap, dif_pos hc]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, c.toNat = 4 * m := ⟨c.toNat / 4, by omega⟩
  have hm0 : 0 < m := by omega
  obtain ⟨d, hd⟩ := hu
  have key : ∀ (q : ℕ) (hq : q = c.toNat) [NeZero q],
      ‖gaussQ ((a : ZMod q)) 0 / ((1 + I) * (Real.sqrt (q : ℕ) : ℂ))‖ = 1 := by
    intro q hq _
    rw [hm] at hq
    subst hq
    refine norm_kappa m hm0 _ ?_
    refine IsUnit.of_mul_eq_one (d : ZMod (4 * m)) ?_
    have : ((a * d : ℤ) : ZMod (4 * m)) = ((1 : ℤ) : ZMod (4 * m)) := by
      rw [ZMod.intCast_eq_intCast_iff]
      have hc' : ((4 * m : ℕ) : ℤ) = c := by rw [← hm, Int.toNat_of_nonneg hc.le]
      rw [hc']; exact hd
    push_cast at this; exact this
  haveI : NeZero c.toNat := ⟨by omega⟩
  exact key c.toNat rfl

theorem unit_of_det (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 ≡ 1 [ZMOD γ 1 0] :=
  Int.modEq_iff_dvd.mpr ⟨-(γ 0 1), by linear_combination (-1 : ℤ) * det_eq γ⟩

theorem norm_jm (γ : SL(2, ℤ)) (h4 : (4 : ℤ) ∣ γ 1 0) {z : ℂ} (hz : 0 < z.im) :
    ‖jm γ z‖ = ‖den γ z‖ ^ ((1 : ℝ) / 2) := by
  have hden := den_ne_zero γ hz
  unfold jm
  split_ifs with h1 h2
  · rw [norm_mul, norm_kap h1 h4 ⟨γ 1 1, unit_of_det γ⟩, one_mul]
    exact norm_cpow_half (den γ z) hden
  · have hn : ((-γ 1 0 : ℤ) : ℂ) * z + ((-γ 1 1 : ℤ) : ℂ) = -den γ z := by
      unfold den; push_cast; ring
    rw [norm_mul, norm_kap (by omega) (by simpa using h4) ⟨-γ 1 1,
      Int.modEq_iff_dvd.mpr ⟨γ 0 1, by linear_combination (-1 : ℤ) * det_eq γ⟩⟩, one_mul,
      hn, norm_cpow_half _ (neg_ne_zero.mpr hden), norm_neg]
  · have h0 : γ 1 0 = 0 := by omega
    have hdet := det_eq γ
    rw [h0, mul_zero, sub_zero] at hdet
    have hd : (γ 1 1).natAbs = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨_, hd⟩ | ⟨_, hd⟩ <;> simp [hd]
    have : ‖den γ z‖ = 1 := by
      unfold den; rw [h0]; simp
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨_, hd⟩ | ⟨_, hd⟩ <;> simp [hd]
    rw [this, Real.one_rpow, norm_one]

/-! ### The weight `3/2 + ℓ` multiplier and the automorphy of `θ_{u,ℓ}` -/

/-- The weight-`3/2 + ℓ` multiplier. -/
noncomputable def jk (ℓ : ℕ) (γ : SL(2, ℤ)) (z : ℂ) : ℂ := jm γ z ^ 3 * den γ z ^ ℓ

theorem jk_mul (ℓ : ℕ) (γ₁ γ₂ : SL(2, ℤ)) (h1 : (4 : ℤ) ∣ γ₁ 1 0) (h2 : (4 : ℤ) ∣ γ₂ 1 0) {z : ℂ}
    (hz : 0 < z.im) : jk ℓ (γ₁ * γ₂) z = jk ℓ γ₁ (mob γ₂ z) * jk ℓ γ₂ z := by
  unfold jk
  rw [jm_mul γ₁ γ₂ h1 h2 hz, den_mul γ₁ γ₂ hz]
  ring

theorem norm_jk (ℓ : ℕ) (γ : SL(2, ℤ)) (h4 : (4 : ℤ) ∣ γ 1 0) {z : ℂ} (hz : 0 < z.im) :
    ‖jk ℓ γ z‖ = ‖den γ z‖ ^ ((3 : ℝ) / 2 + ℓ) := by
  have hd : 0 < ‖den γ z‖ := norm_pos_iff.mpr (den_ne_zero γ hz)
  unfold jk
  rw [norm_mul, norm_pow, norm_pow, norm_jm γ h4 hz, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul hd.le, ← Real.rpow_add hd]
  norm_num

theorem theta3_mob (u : Fin 3 → ℂ) (hu : ∑ j, u j ^ 2 = 0) (ℓ : ℕ) (hℓ : Even ℓ) (γ : SL(2, ℤ))
    (h4 : (4 : ℤ) ∣ γ 1 0) {z : ℂ} (hz : 0 < z.im) :
    theta3 u ℓ (mob γ z) = jk ℓ γ z * theta3 u ℓ z := by
  have hdet := det_eq γ
  unfold jk den
  by_cases hpos : 0 < γ 1 0
  · haveI : NeZero (γ 1 0).toNat := ⟨by omega⟩
    have h := theta3_gamma u hu ℓ (γ 1 0).toNat (by omega) (γ 0 0) (γ 0 1) (γ 1 1)
      (by rw [Int.toNat_of_nonneg hpos.le]; linarith) z hz
    rw [cast_toNat hpos] at h
    simp only [jm, hpos, if_true, kap, ↓reduceDIte, ↓reduceIte]
    rw [show mob γ z = ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) from rfl, h]
    ring
  by_cases hneg : γ 1 0 < 0
  · have hpos' : 0 < -γ 1 0 := by omega
    haveI : NeZero (-γ 1 0).toNat := ⟨by omega⟩
    have h := theta3_gamma u hu ℓ (-γ 1 0).toNat (by omega) (-γ 0 0) (-γ 0 1) (-γ 1 1)
      (by rw [Int.toNat_of_nonneg hpos'.le]; linarith) z hz
    rw [cast_toNat hpos'] at h
    simp only [jm, hpos, if_false, hneg, if_true, kap, hpos', ↓reduceDIte, ↓reduceIte]
    have hm : mob γ z = (((-γ 0 0 : ℤ) : ℂ) * z + ((-γ 0 1 : ℤ) : ℂ)) /
        (((-γ 1 0 : ℤ) : ℂ) * z + ((-γ 1 1 : ℤ) : ℂ)) := by
      unfold mob; push_cast; rw [← neg_div_neg_eq]; congr 1 <;> ring
    have hn : (((-γ 1 0 : ℤ) : ℂ) * z + ((-γ 1 1 : ℤ) : ℂ)) ^ ℓ = ((γ 1 0 : ℂ) * z + γ 1 1) ^ ℓ := by
      rw [show ((-γ 1 0 : ℤ) : ℂ) * z + ((-γ 1 1 : ℤ) : ℂ) = -((γ 1 0 : ℂ) * z + γ 1 1) by
        push_cast; ring, hℓ.neg_pow]
    rw [hm, h, hn]
    push_cast
    ring
  · have h0 : γ 1 0 = 0 := by omega
    rw [h0, mul_zero, sub_zero] at hdet
    simp only [jm, hpos, hneg, if_false, one_pow, one_mul, h0, Int.cast_zero, zero_mul, zero_add]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
    · have : mob γ z = z + ((γ 0 1 : ℤ) : ℂ) := by
        unfold mob; rw [ha, hd, h0]; simp
      rw [this, theta3_add_int, hd]; simp
    · have : mob γ z = z + ((-γ 0 1 : ℤ) : ℂ) := by
        unfold mob; rw [ha, hd, h0]; push_cast; field_simp; ring
      rw [this, theta3_add_int, hd]; push_cast; rw [hℓ.neg_pow]; simp

end ThreeSquares.Mult
