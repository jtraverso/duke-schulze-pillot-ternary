/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.PetUnfold
public import DukeH1.ThetaCoeff

/-!
# `θ_{u,ℓ}` as an automorphic form of level `Q`, and its unfolded integral

For `u` isotropic, `ℓ ≥ 2` even, `4 ∣ Q`:
* `isAut_theta3`: `θ_{u,ℓ}` is automorphic of weight `3/2 + ℓ` on `Γ₀(Q)` with `y^{k/2}|θ|` bounded;
* `strip_PhiF_theta3`: `∫_{strip} θ(z) conj(e(nz)) y^k = Γ(k − 1) (4πn)^{1−k} W_u(n)`.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares.Poin

open Complex UpperHalfPlane ModularGroup MeasureTheory ThreeSquares.FD ThreeSquares.Mult Filter
  Topology

open scoped MatrixGroups Real ComplexConjugate

theorem summable_theta3_term (u : Fin 3 → ℂ) (ℓ : ℕ) {z : ℂ} (hz : 0 < z.im) :
    Summable (fun x : Fin 3 → ℤ => dot3 u x ^ ℓ * cexp (2 * π * Complex.I * sq3 x * z)) := by
  have h := (expSummable_theta3 u hz).summable_pow ℓ 0 le_rfl
  refine Summable.of_norm_bounded (h.mul_left (((2 * π) ^ ℓ)⁻¹)) fun x => le_of_eq ?_
  rw [norm_mul, norm_pow, zero_mul, Real.exp_zero, mul_one, norm_mul, norm_mul, norm_mul,
    Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, Complex.norm_two, abs_of_pos Real.pi_pos]
  rw [mul_one, mul_pow (2 * π) ‖dot3 u x‖ ℓ]
  have : (0 : ℝ) < (2 * π) ^ ℓ := by positivity
  field_simp

theorem measurable_theta3H (u : Fin 3 → ℂ) (ℓ : ℕ) : Measurable fun z : ℍ => theta3 u ℓ z := by
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset (Fin 3 → ℤ)))
    (f := fun s (z : ℍ) => ∑ x ∈ s, dot3 u x ^ ℓ * cexp (2 * π * Complex.I * sq3 x * z))
    (fun s => ?_) ?_
  · exact Finset.measurable_sum _ fun x _ => by fun_prop
  · exact tendsto_pi_nhds.mpr fun z => (summable_theta3_term u ℓ z.im_pos).hasSum

theorem isAut_theta3 (u : Fin 3 → ℂ) (hu : ∑ j, u j ^ 2 = 0) {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓ : Even ℓ)
    {Q : ℕ} (hQ : 4 ∣ Q) : IsAut ℓ Q (theta3 u ℓ) where
  aut γ hγ z hz := theta3_mob u hu ℓ hℓ γ (dvd_trans (show (4 : ℤ) ∣ (Q : ℤ) by exact_mod_cast hQ) hγ) hz
  meas := measurable_theta3H u ℓ
  bdd := by
    obtain ⟨C, hC⟩ := theta3_bound u hu ℓ hℓ1
    exact ⟨C, fun z => hC z z.im_pos⟩

theorem conj_en (n : ℕ) (x y : ℝ) :
    conj (en n ((x : ℂ) + (y : ℂ) * Complex.I)) =
      cexp (-(2 * π * Complex.I * n * ((x : ℂ) + (y : ℂ) * Complex.I))) *
        ((Real.exp (-(4 * π * n * y)) : ℝ) : ℂ) := by
  unfold en
  rw [← Complex.exp_conj, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The unfolded integral of `θ_{u,ℓ}`.** -/
theorem strip_PhiF_theta3 (u : Fin 3 → ℂ) (hu : ∑ j, u j ^ 2 = 0) {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ)
    (hℓ : Even ℓ) {n : ℕ} (hn : 0 < n) :
    ∫ z in strip, PhiF ℓ n (theta3 u ℓ) z =
      ((Real.Gamma (kw ℓ - 1) * (1 / (4 * π * n)) ^ (kw ℓ - 1) : ℝ) : ℂ) * weylU u ℓ n := by
  have hF := isAut_theta3 u hu hℓ1 hℓ (Q := 4) dvd_rfl
  set G : ℂ → ℂ := fun w => theta3 u ℓ w * conj (en n w) * ((w.im ^ kw ℓ : ℝ) : ℂ)
  have hint : IntegrableOn (fun z : ℍ => G z) strip :=
    ⟨(measurable_PhiF ℓ n hF).aestronglyMeasurable, lintegral_PhiF_lt_top ℓ n hℓ1 hn hF⟩
  show ∫ z in strip, G z = _
  rw [integral_strip G hint]
  have hk : 0 < kw ℓ - 1 := by
    unfold kw; have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    linarith
  have inner : ∀ y : ℝ, 0 < y → ∫ x : ℝ in Set.Ico 0 1, G ((x : ℂ) + (y : ℂ) * Complex.I) =
      ((y ^ kw ℓ * Real.exp (-(4 * π * n * y)) : ℝ) : ℂ) * weylU u ℓ n := by
    intro y hy
    have hc := theta3_coeff u ℓ n hy
    rw [intervalIntegral.integral_of_le zero_le_one] at hc
    rw [integral_Ioc_eq_integral_Ioo, ← integral_Ico_eq_integral_Ioo] at hc
    rw [← hc, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
    simp only [G]
    rw [conj_en]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, Complex.I_re, mul_zero, Complex.I_im, mul_one,
      zero_add]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => by rw [inner y hy]]
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi hk (by positivity : (0 : ℝ) < 4 * π * n)
  have e : ∀ y ∈ Set.Ioi (0 : ℝ), (1 / y ^ 2 : ℝ) • (((y ^ kw ℓ * Real.exp (-(4 * π * n * y)) : ℝ)
      : ℂ) * weylU u ℓ n) = ((y ^ (kw ℓ - 1 - 1) * Real.exp (-(4 * π * n * y)) : ℝ) : ℂ) *
        weylU u ℓ n := by
    intro y (hy : 0 < y)
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    rw [show kw ℓ - 1 - 1 = kw ℓ - 2 by ring, Real.rpow_sub hy, Real.rpow_two]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_mul_const, integral_complex_ofReal, hg]
  push_cast
  ring

end ThreeSquares.Poin
