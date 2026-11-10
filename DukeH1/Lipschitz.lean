/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# The Lipschitz formula

* `integral_cpow_mul_exp_neg_mul_Ioi_cplx`: `∫₀^∞ t^{s−1} e^{−rt} dt = (1/r)^s Γ(s)` for `Re s > 0`,
  `Re r > 0` (from the real case by the identity theorem in `r`);
* `lipschitz`: `∫_ℝ (x + iy)^{−s} e^{−2πinx} dx = (−2πi)^s n^{s−1} e^{−2πny} / Γ(s)` for `Re s > 1`,
  `y > 0`, `n > 0` (Fourier inversion).
-/

@[expose] public section

namespace ThreeSquares.Lip

open Complex MeasureTheory Set Filter Topology

open scoped Real FourierTransform

/-! ### The complex Gamma integral -/

theorem norm_cpow_exp_le {s r : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) * cexp (-(r * t))‖ = t ^ (s.re - 1) * Real.exp (-(r.re * t)) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  simp

theorem integrableOn_cpow_exp {s r : ℂ} (hs : 0 < s.re) (hr : 0 < r.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * cexp (-(r * t))) (Ioi 0) := by
  have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s.re - 1) (p := 1) (b := r.re)
    (by linarith) one_pos hr
  refine Integrable.mono' hb ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    exact ((continuousAt_ofReal_cpow_const t _ (Or.inr (ne_of_gt ht))).mul
      (by fun_prop)).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_cpow_exp_le ht, Real.rpow_one, neg_mul]

theorem integral_cpow_mul_exp_neg_mul_Ioi_cplx {s r : ℂ} (hs : 0 < s.re) (hr : 0 < r.re) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * cexp (-(r * t)) = (1 / r) ^ s * Gamma s := by
  set U : Set ℂ := {w | 0 < w.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set f : ℂ → ℂ := fun w => ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * cexp (-(w * t))
  set g : ℂ → ℂ := fun w => (1 / w) ^ s * Gamma s
  -- `f` is holomorphic on `U`
  have hf : AnalyticOnNhd ℂ f U := by
    refine DifferentiableOn.analyticOnNhd (fun w₀ hw₀ => ?_) hUo
    have hw₀' : 0 < w₀.re := hw₀
    set δ := w₀.re / 2
    have hδ : 0 < δ := by positivity
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
      (μ := volume.restrict (Ioi 0)) (x₀ := w₀) (s := Metric.ball w₀ δ)
      (F := fun w (t : ℝ) => (t : ℂ) ^ (s - 1) * cexp (-(w * t)))
      (F' := fun w (t : ℝ) => (t : ℂ) ^ (s - 1) * (cexp (-(w * t)) * (-(t : ℂ))))
      (bound := fun t : ℝ => t ^ s.re * Real.exp (-δ * t ^ (1 : ℝ)))
      (Metric.ball_mem_nhds w₀ hδ)
      (Eventually.of_forall fun w => ContinuousOn.aestronglyMeasurable (fun t ht =>
        ((continuousAt_ofReal_cpow_const t _ (Or.inr (ne_of_gt ht))).mul
          (by fun_prop)).continuousWithinAt) measurableSet_Ioi)
      (integrableOn_cpow_exp hs hw₀')
      (ContinuousOn.aestronglyMeasurable (fun t ht =>
        ((continuousAt_ofReal_cpow_const t _ (Or.inr (ne_of_gt ht))).mul
          (by fun_prop)).continuousWithinAt) measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t (ht : 0 < t) w hw => by
        have hwr : δ < w.re := by
          have := Metric.mem_ball.mp hw
          have h2 : |w.re - w₀.re| ≤ ‖w - w₀‖ := by
            rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
          simp only [δ] at *
          rw [dist_eq_norm] at this
          linarith [abs_le.mp h2]
        rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp, norm_neg,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, Real.rpow_one]
        have e1 : t ^ (s - 1).re * t = t ^ s.re := by
          rw [Complex.sub_re, Complex.one_re, Real.rpow_sub ht, Real.rpow_one]; field_simp
        calc t ^ (s - 1).re * (Real.exp (-(w * t)).re * t)
            = t ^ s.re * Real.exp (-(w.re * t)) := by
              rw [← e1]; simp; ring
          _ ≤ t ^ s.re * Real.exp (-δ * t) := by
              gcongr; nlinarith))
      (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hδ)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ w _ => by
        have := ((hasDerivAt_id w).mul_const (t : ℂ)).neg.cexp
        simpa using this.const_mul ((t : ℂ) ^ (s - 1))))
    exact key.2.differentiableAt.differentiableWithinAt
  have hg : AnalyticOnNhd ℂ g U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    have hw' : 0 < w.re := hw
    have hw0 : w ≠ 0 := fun h => by rw [h] at hw'; simp at hw'
    refine (DifferentiableAt.mul_const ?_ _).differentiableWithinAt
    refine DifferentiableAt.cpow_const ((differentiableAt_const _).div differentiableAt_id hw0) ?_
    rw [Complex.mem_slitPlane_iff]; left
    rw [one_div, Complex.inv_re]
    exact div_pos hw' (Complex.normSq_pos.mpr hw0)
  -- they agree on positive reals
  have hreal : ∀ x : ℝ, 0 < x → f x = g x := fun x hx => integral_cpow_mul_exp_neg_mul_Ioi hs hx
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), f w = g w := by
    have ht : Tendsto (fun m : ℕ => ((1 + 1 / ((m : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun m => ?_⟩
      · have : Tendsto (fun m : ℕ => (1 + 1 / ((m : ℝ) + 1) : ℝ)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        rw [add_zero] at this
        exact (Complex.continuous_ofReal.tendsto 1).comp this |>.trans (by simp)
      · simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        have h1 := congrArg Complex.re h
        simp only [Complex.ofReal_re, Complex.one_re] at h1
        have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
        linarith
    exact ht.frequently (Frequently.of_forall fun m => hreal _ (by positivity))
  have heq := hf.eqOn_of_preconnected_of_frequently_eq hg
    (convex_halfSpace_re_gt 0).isPreconnected (by simp [U]) hfreq
  exact heq hr

/-! ### The Lipschitz formula -/

theorem log_neg_two_pi_I_mul {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-(2 * π * I) * z) = Complex.log (-(2 * π * I)) + Complex.log z := by
  have h1 : -(2 * π * I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  apply Complex.log_mul h1 h2
  have ha : Complex.arg (-(2 * π * I)) = -(π / 2) := by
    rw [show -(2 * π * I) = ((2 * π : ℝ) : ℂ) * (-I) by push_cast; ring,
      Complex.arg_real_mul _ (by positivity), Complex.arg_neg_I]
  have hb1 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr hz.le
  have hb2 : Complex.arg z ≤ π := Complex.arg_le_pi z
  rw [ha]
  constructor <;> linarith [Real.pi_pos]

theorem cpow_mul_of_log {a b s : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hl : Complex.log (a * b) = Complex.log a + Complex.log b) : (a * b) ^ s = a ^ s * b ^ s := by
  rw [cpow_def_of_ne_zero (mul_ne_zero ha hb), cpow_def_of_ne_zero ha, cpow_def_of_ne_zero hb, hl,
    ← Complex.exp_add]
  ring_nf

/-- `(1 / (2π(y − ix)))^s = (−2πi)^{−s} (x + iy)^{−s}`. -/
theorem inv_R_cpow (s : ℂ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    (1 / ((2 * π : ℂ) * (y + (-x : ℝ) * I))) ^ s =
      ((-(2 * π * I)) ^ s)⁻¹ * ((x : ℂ) + y * I) ^ (-s) := by
  set z : ℂ := (x : ℂ) + y * I
  have hz : 0 < z.im := by simp [z, hy]
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have ha : -(2 * π * I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have e : (2 * π : ℂ) * (y + (-x : ℝ) * I) = -(2 * π * I) * z := by
    simp only [z]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hre : 0 < (-(2 * π * I) * z).re := by
    rw [← e]; simp; positivity
  have harg : Complex.arg (-(2 * π * I) * z) ≠ π := by
    intro h
    have := Complex.arg_eq_pi_iff.mp h
    linarith [this.1]
  rw [e, one_div, inv_cpow _ _ harg, cpow_mul_of_log ha hz0 (log_neg_two_pi_I_mul hz), mul_inv,
    cpow_neg]

theorem cpow_neg_two_pi_I_ne_zero (s : ℂ) : (-(2 * π * I)) ^ s ≠ 0 := by
  rw [Ne, Complex.cpow_eq_zero_iff]; push_neg
  intro h0; simp [Real.pi_ne_zero, Complex.I_ne_zero] at h0

theorem lipschitz {s : ℂ} (hs : 1 < s.re) {y : ℝ} (hy : 0 < y) {n : ℝ} (hn : 0 < n) :
    ∫ x : ℝ, ((x : ℂ) + y * I) ^ (-s) * cexp (-(2 * π * I * n * x)) =
      (-(2 * π * I)) ^ s * (n : ℂ) ^ (s - 1) * Real.exp (-(2 * π * n * y)) / Gamma s := by
  have hs0 : 0 < s.re := by linarith
  have hΓ : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs0
  set r0 : ℂ := ((2 * π * y : ℝ) : ℂ)
  have hr0 : 0 < r0.re := by simp only [r0, Complex.ofReal_re]; positivity
  set h : ℝ → ℂ := (Ioi 0).indicator fun t : ℝ => (t : ℂ) ^ (s - 1) * cexp (-(r0 * t))
  have hhi : Integrable h :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (integrableOn_cpow_exp hs0 hr0)
  set R : ℝ → ℂ := fun w => (2 * π : ℂ) * (y + w * I)
  have hR : ∀ w : ℝ, 0 < (R w).re := fun w => by simp only [R]; simp; positivity
  have hF : ∀ w : ℝ, 𝓕 h w = (1 / R w) ^ s * Gamma s := by
    intro w
    rw [Real.fourier_real_eq_integral_exp_smul]
    have e : (fun v : ℝ => cexp (↑(-2 * π * v * w) * I) • h v) =
        (Ioi 0).indicator (fun v : ℝ => (v : ℂ) ^ (s - 1) * cexp (-(R w * v))) := by
      ext v
      by_cases hv : v ∈ Ioi 0
      · rw [indicator_of_mem hv]
        simp only [h, indicator_of_mem hv, smul_eq_mul]
        rw [show cexp (↑(-2 * π * v * w) * I) * ((v : ℂ) ^ (s - 1) * cexp (-(r0 * v))) =
          (v : ℂ) ^ (s - 1) * (cexp (↑(-2 * π * v * w) * I) * cexp (-(r0 * v))) by ring,
          ← Complex.exp_add]
        congr 2
        simp only [R, r0]; push_cast; ring
      · rw [indicator_of_notMem hv]
        simp only [h, indicator_of_notMem hv, smul_zero]
    rw [e, integral_indicator measurableSet_Ioi, integral_cpow_mul_exp_neg_mul_Ioi_cplx hs0 (hR w)]
  -- the Fourier transform is integrable
  have hFi : Integrable (𝓕 h) := by
    set m : ℝ := min 1 (y ^ 2)
    have hm : 0 < m := lt_min one_pos (by positivity)
    set C : ℝ := ‖Gamma s‖ * Real.exp (π * |s.im|) * ((2 * π) ^ 2 * m) ^ (-(s.re / 2))
    have hb : ∀ w : ℝ, ‖𝓕 h w‖ ≤ C * ((1 : ℝ) + ‖w‖ ^ 2) ^ (-s.re / 2) := by
      intro w
      rw [hF w]
      have hR0 : R w ≠ 0 := fun h0 => by have := hR w; rw [h0] at this; simp at this
      have hz0 : 1 / R w ≠ 0 := one_div_ne_zero hR0
      have h1 : 1 / Real.exp (Complex.arg (1 / R w) * s.im) ≤ Real.exp (π * |s.im|) := by
        rw [one_div, ← Real.exp_neg]
        apply Real.exp_le_exp.mpr
        have := abs_arg_le_pi (1 / R w)
        have h2 : |Complex.arg (1 / R w) * s.im| ≤ π * |s.im| := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
        linarith [neg_abs_le (Complex.arg (1 / R w) * s.im)]
      have hRn : ‖R w‖ ^ 2 = (2 * π) ^ 2 * (y ^ 2 + w ^ 2) := by
        simp only [R]
        rw [norm_mul, mul_pow, ← Complex.normSq_eq_norm_sq (y + w * I), Complex.normSq_apply]
        simp [Complex.norm_two, abs_of_pos Real.pi_pos]
        ring
      have hlow : (2 * π) ^ 2 * m * (1 + ‖w‖ ^ 2) ≤ ‖R w‖ ^ 2 := by
        rw [hRn, Real.norm_eq_abs, sq_abs]
        have h3 : m * (1 + w ^ 2) ≤ y ^ 2 + w ^ 2 := by
          have hm1 : m ≤ 1 := min_le_left _ _
          have hmy : m ≤ y ^ 2 := min_le_right _ _
          nlinarith [sq_nonneg w]
        have hpi : 0 < (2 * π) ^ 2 := by positivity
        nlinarith
      have hzn : ‖1 / R w‖ ^ s.re = (‖R w‖ ^ 2) ^ (-(s.re / 2)) := by
        rw [norm_div, norm_one, Real.div_rpow zero_le_one (norm_nonneg _), Real.one_rpow,
          ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
          show ((2 : ℕ) : ℝ) * -(s.re / 2) = -s.re by push_cast; ring,
          Real.rpow_neg (norm_nonneg _), one_div]
      have hpos : 0 < (2 * π) ^ 2 * m * (1 + ‖w‖ ^ 2) := by positivity
      have h4 : (‖R w‖ ^ 2) ^ (-(s.re / 2)) ≤ ((2 * π) ^ 2 * m) ^ (-(s.re / 2)) *
          (1 + ‖w‖ ^ 2) ^ (-s.re / 2) := by
        rw [neg_div, ← Real.mul_rpow (by positivity) (by positivity)]
        exact Real.rpow_le_rpow_of_nonpos hpos hlow (by linarith)
      rw [norm_mul, norm_cpow_of_ne_zero hz0, hzn, div_eq_mul_one_div]
      calc (‖R w‖ ^ 2) ^ (-(s.re / 2)) * (1 / Real.exp (Complex.arg (1 / R w) * s.im)) *
            ‖Gamma s‖
          ≤ (((2 * π) ^ 2 * m) ^ (-(s.re / 2)) * (1 + ‖w‖ ^ 2) ^ (-s.re / 2)) *
              Real.exp (π * |s.im|) * ‖Gamma s‖ := by gcongr
        _ = C * ((1 : ℝ) + ‖w‖ ^ 2) ^ (-s.re / 2) := by simp only [C]; ring
    have hint := (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := s.re)
      (by simp; linarith)).const_mul C
    refine hint.mono' ?_ (Eventually.of_forall hb)
    have : 𝓕 h = fun w => (1 / R w) ^ s * Gamma s := funext hF
    rw [this]
    refine Measurable.aestronglyMeasurable ?_
    simp only [R]
    fun_prop
  -- continuity of `h` at `n`
  have hc : ContinuousAt h n := by
    have hg : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (s - 1) * cexp (-(r0 * t))) n :=
      (continuousAt_ofReal_cpow_const n _ (Or.inr hn.ne')).mul (by fun_prop)
    refine hg.congr ?_
    filter_upwards [Ioi_mem_nhds hn] with t ht
    simp only [h, indicator_of_mem ht]
  have hinv := hhi.fourierInv_fourier_eq hFi hc
  have hhn : h n = (n : ℂ) ^ (s - 1) * Real.exp (-(2 * π * n * y)) := by
    simp only [h, indicator_of_mem (show n ∈ Ioi (0 : ℝ) from hn), r0]
    congr 1
    push_cast; ring_nf
  have key : ∫ x : ℝ, ((x : ℂ) + y * I) ^ (-s) * cexp (-(2 * π * I * n * x)) *
      (((-(2 * π * I)) ^ s)⁻¹ * Gamma s) = h n := by
    rw [← hinv, Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
    conv_rhs => rw [← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul]
    rw [hF, show R (-x) = (2 * π : ℂ) * (y + (-x : ℝ) * I) from rfl, inv_R_cpow s hy x]
    rw [show cexp (↑(-2 * π * -x * -n) * I) = cexp (-(2 * π * I * n * x)) by
      congr 1; push_cast; ring]
    ring
  rw [integral_mul_const, hhn] at key
  have h2 := cpow_neg_two_pi_I_ne_zero s
  set I0 := ∫ x : ℝ, ((x : ℂ) + y * I) ^ (-s) * cexp (-(2 * π * I * n * x))
  rw [eq_div_iff hΓ]
  have e : I0 * Gamma s = (-(2 * π * I)) ^ s * (I0 * (((-(2 * π * I)) ^ s)⁻¹ * Gamma s)) := by
    field_simp
  rw [e, key]
  ring

end ThreeSquares.Lip
