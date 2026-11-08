/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.ThetaJac
public import ThreeSquaresLib.Lattice
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Theta series with an isotropic power on `Γ₀(4)`

For `u ∈ ℂ³` with `u₀² + u₁² + u₂² = 0` and `ℓ ∈ ℕ`,
`θ_{u,ℓ}(z) = ∑_{x ∈ ℤ³} (u·x)^ℓ e(|x|² z)`.

* `iteratedDeriv_tsum_exp`: for an absolutely summable exponential family,
  `∂_s^ℓ ∑ a_x e^{s λ_x} |_{s=0} = ∑ a_x λ_x^ℓ`.
* `theta3_gamma`: for `γ = (a b; c d) ∈ Γ₀(4)` with `c > 0`,
  `θ_{u,ℓ}(γz) = κ³ ((cz+d)^{1/2})³ (cz+d)^ℓ θ_{u,ℓ}(z)` with `κ = G(a,0;c)/((1+i)√c)`
  (from the two-variable theta transformation in each coordinate; the factor `e(cζ²/4(cz+d))`
  cancels because `u` is isotropic).
-/

@[expose] public section

namespace ThreeSquares

open Complex Finset Real

/-! ### Derivatives of exponential series -/

/-- `‖λ‖^m ≤ m! e^{‖λ‖}`. -/
theorem norm_pow_le_factorial_mul_exp (lam : ℂ) (m : ℕ) :
    ‖lam‖ ^ m ≤ m.factorial * Real.exp ‖lam‖ := by
  have := Real.pow_div_factorial_le_exp ‖lam‖ (norm_nonneg lam) m
  have hf : (0 : ℝ) < m.factorial := by positivity
  rw [div_le_iff₀ hf] at this
  linarith

/-- The exponential-series condition: `∑ ‖a_x‖ e^{R ‖λ_x‖} < ∞` for every `R`. -/
def ExpSummable {ι : Type*} (a lam : ι → ℂ) : Prop :=
  ∀ R : ℝ, Summable (fun x => ‖a x‖ * Real.exp (R * ‖lam x‖))

theorem ExpSummable.summable_pow {ι : Type*} {a lam : ι → ℂ} (h : ExpSummable a lam) (m : ℕ)
    (R : ℝ) (_hR : 0 ≤ R) :
    Summable (fun x => ‖a x‖ * ‖lam x‖ ^ m * Real.exp (R * ‖lam x‖)) := by
  refine ((h (R + 1)).mul_left (m.factorial : ℝ)).of_nonneg_of_le
    (fun x => by positivity) (fun x => ?_)
  have h1 := norm_pow_le_factorial_mul_exp (lam x) m
  have h2 : Real.exp ‖lam x‖ * Real.exp (R * ‖lam x‖) = Real.exp ((R + 1) * ‖lam x‖) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖a x‖ * ‖lam x‖ ^ m * Real.exp (R * ‖lam x‖)
      ≤ ‖a x‖ * (m.factorial * Real.exp ‖lam x‖) * Real.exp (R * ‖lam x‖) := by gcongr
    _ = m.factorial * (‖a x‖ * Real.exp ((R + 1) * ‖lam x‖)) := by rw [← h2]; ring

/-- The `j`-th formal derivative `∑ a_x λ_x^j e^{s λ_x}`. -/
noncomputable def expSeries {ι : Type*} (a lam : ι → ℂ) (j : ℕ) (s : ℂ) : ℂ :=
  ∑' x, a x * lam x ^ j * cexp (s * lam x)

theorem hasDerivAt_expSeries {ι : Type*} {a lam : ι → ℂ} (h : ExpSummable a lam) (j : ℕ)
    (s₀ : ℂ) : HasDerivAt (expSeries a lam j) (expSeries a lam (j + 1) s₀) s₀ := by
  set R := ‖s₀‖ + 1 with _hR
  have hR0 : 0 ≤ R := by positivity
  have hu := h.summable_pow (j + 1) R hR0
  have hderiv : ∀ x, ∀ y ∈ Metric.ball s₀ 1, HasDerivAt (fun s => a x * lam x ^ j * cexp (s * lam x))
      (a x * lam x ^ (j + 1) * cexp (y * lam x)) y := by
    intro x y _
    have := ((hasDerivAt_id y).mul_const (lam x)).cexp.const_mul (a x * lam x ^ j)
    convert this using 1
    · funext s; simp only [id]
    · simp only [id]; ring
  have hbound : ∀ x, ∀ y ∈ Metric.ball s₀ 1,
      ‖a x * lam x ^ (j + 1) * cexp (y * lam x)‖ ≤
        ‖a x‖ * ‖lam x‖ ^ (j + 1) * Real.exp (R * ‖lam x‖) := by
    intro x y hy
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp]
    gcongr
    have hy' : ‖y‖ ≤ R := by
      have := norm_le_norm_add_norm_sub' y s₀
      rw [Metric.mem_ball, dist_eq_norm] at hy
      linarith
    calc (y * lam x).re ≤ ‖y * lam x‖ := re_le_norm _
      _ = ‖y‖ * ‖lam x‖ := norm_mul _ _
      _ ≤ R * ‖lam x‖ := by gcongr
  have hsum0 : Summable (fun x => a x * lam x ^ j * cexp (s₀ * lam x)) := by
    refine Summable.of_norm ((h.summable_pow j R hR0).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun x => ?_))
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp]
    gcongr
    calc (s₀ * lam x).re ≤ ‖s₀ * lam x‖ := re_le_norm _
      _ = ‖s₀‖ * ‖lam x‖ := norm_mul _ _
      _ ≤ R * ‖lam x‖ := by gcongr; linarith
  exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball s₀ 1).isPreconnected
    hderiv hbound (Metric.mem_ball_self one_pos) hsum0 (Metric.mem_ball_self one_pos)

theorem iteratedDeriv_expSeries {ι : Type*} {a lam : ι → ℂ} (h : ExpSummable a lam) :
    ∀ m j, iteratedDeriv m (expSeries a lam j) = expSeries a lam (j + m)
  | 0, j => by simp
  | m + 1, j => by
    rw [iteratedDeriv_succ', show j + (m + 1) = (j + 1) + m by ring]
    have : deriv (expSeries a lam j) = expSeries a lam (j + 1) :=
      funext fun s => (hasDerivAt_expSeries h j s).deriv
    rw [this, iteratedDeriv_expSeries h m (j + 1)]

/-- `∂_s^ℓ ∑ a_x e^{s λ_x} |_{s=0} = ∑ a_x λ_x^ℓ`. -/
theorem iteratedDeriv_tsum_exp {ι : Type*} {a lam : ι → ℂ} (h : ExpSummable a lam) (ℓ : ℕ) :
    iteratedDeriv ℓ (fun s => ∑' x, a x * cexp (s * lam x)) 0 = ∑' x, a x * lam x ^ ℓ := by
  have e : (fun s => ∑' x, a x * cexp (s * lam x)) = expSeries a lam 0 := by
    funext s; simp [expSeries]
  rw [e, iteratedDeriv_expSeries h ℓ 0, zero_add]
  simp [expSeries]

theorem ExpSummable.smul {ι : Type*} {a lam : ι → ℂ} (h : ExpSummable a lam) (c : ℂ) :
    ExpSummable a (fun x => c * lam x) := by
  intro R
  refine (h (|R| * ‖c‖)).of_nonneg_of_le (fun x => by positivity) (fun x => ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  rw [norm_mul]
  calc R * (‖c‖ * ‖lam x‖) ≤ |R| * (‖c‖ * ‖lam x‖) :=
        mul_le_mul_of_nonneg_right (le_abs_self R) (by positivity)
    _ = |R| * ‖c‖ * ‖lam x‖ := by ring

/-! ### One-dimensional Gaussian bounds -/

theorem summable_gauss_abs {y : ℝ} (hy : 0 < y) (B : ℝ) :
    Summable (fun n : ℤ => Real.exp (-2 * π * y * (n : ℝ) ^ 2 + B * |(n : ℝ)|)) := by
  have hreal : ∀ B' : ℝ, Summable (fun n : ℤ => Real.exp (-2 * π * y * (n : ℝ) ^ 2 + B' * n)) := by
    intro B'
    have h := summable_cexp_quad ((2 * y : ℝ) : ℂ) (B' : ℂ) 0 (by simp; linarith)
    have e : (fun n : ℤ => cexp (-π * ((2 * y : ℝ) : ℂ) * (n : ℂ) ^ 2 + (B' : ℂ) * n + 0)) =
        fun n : ℤ => ((Real.exp (-2 * π * y * (n : ℝ) ^ 2 + B' * n) : ℝ) : ℂ) := by
      funext n; rw [Complex.ofReal_exp]; push_cast; ring_nf
    rw [e] at h
    exact Complex.summable_ofReal.mp h
  refine ((hreal B).add (hreal (-B))).of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun n => ?_)
  rcases le_total 0 (n : ℝ) with h | h
  · rw [abs_of_nonneg h]
    have := (Real.exp_pos (-2 * π * y * (n : ℝ) ^ 2 + -B * n)).le
    linarith
  · rw [abs_of_nonpos h]
    have := (Real.exp_pos (-2 * π * y * (n : ℝ) ^ 2 + B * n)).le
    have e : B * -(n : ℝ) = -B * n := by ring
    rw [e]; linarith

/-! ### The three-dimensional theta series -/

/-- `|x|²` as a complex number. -/
noncomputable def sq3 (x : Fin 3 → ℤ) : ℂ := ∑ j, ((x j : ℤ) : ℂ) ^ 2

/-- `u · x`. -/
noncomputable def dot3 (u : Fin 3 → ℂ) (x : Fin 3 → ℤ) : ℂ := ∑ j, u j * x j

/-- `θ_{u,ℓ}(z) = ∑_{x ∈ ℤ³} (u·x)^ℓ e(|x|² z)`. -/
noncomputable def theta3 (u : Fin 3 → ℂ) (ℓ : ℕ) (z : ℂ) : ℂ :=
  ∑' x : Fin 3 → ℤ, dot3 u x ^ ℓ * cexp (2 * π * I * sq3 x * z)

theorem expSummable_theta3 (u : Fin 3 → ℂ) {z : ℂ} (hz : 0 < z.im) :
    ExpSummable (fun x : Fin 3 → ℤ => cexp (2 * π * I * sq3 x * z))
      (fun x => 2 * π * I * dot3 u x) := by
  intro R
  set R' := |R| with hR'
  set f : Fin 3 → ℤ → ℂ := fun j n =>
    ((Real.exp (-2 * π * z.im * (n : ℝ) ^ 2 + (R' * 2 * π * ‖u j‖) * |(n : ℝ)|) : ℝ) : ℂ) with hf
  have hfs : ∀ j, Summable fun n => ‖f j n‖ := by
    intro j
    refine (summable_gauss_abs hz (R' * 2 * π * ‖u j‖)).congr fun n => ?_
    simp only [hf, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hprod := (tsum_pi_prod f hfs).1
  refine hprod.of_nonneg_of_le (fun x => by positivity) (fun x => ?_)
  rw [norm_prod]
  simp only [hf, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_sum, Complex.norm_exp]
  have hre : (2 * π * I * sq3 x * z).re = ∑ j : Fin 3, -2 * π * z.im * ((x j : ℤ) : ℝ) ^ 2 := by
    simp only [sq3, Finset.mul_sum, Finset.sum_mul, re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_re, mul_im, pow_two]; ring
  have hlam : ‖2 * π * I * dot3 u x‖ ≤ ∑ j : Fin 3, 2 * π * ‖u j‖ * |((x j : ℤ) : ℝ)| := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_two]
    unfold dot3
    calc 2 * π * ‖∑ j, u j * (x j : ℂ)‖ ≤ 2 * π * ∑ j, ‖u j * (x j : ℂ)‖ := by
          gcongr; exact norm_sum_le _ _
      _ = ∑ j : Fin 3, 2 * π * ‖u j‖ * |((x j : ℤ) : ℝ)| := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, Complex.norm_intCast]; ring
  rw [← Real.exp_add, hre]
  apply Real.exp_le_exp.mpr
  have : R * ‖2 * π * I * dot3 u x‖ ≤ R' * ∑ j : Fin 3, 2 * π * ‖u j‖ * |((x j : ℤ) : ℝ)| :=
    (mul_le_mul_of_nonneg_right (le_abs_self R) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hlam (abs_nonneg R))
  calc ∑ j : Fin 3, -2 * π * z.im * ((x j : ℤ) : ℝ) ^ 2 + R * ‖2 * π * I * dot3 u x‖
      ≤ ∑ j : Fin 3, -2 * π * z.im * ((x j : ℤ) : ℝ) ^ 2 +
          R' * ∑ j : Fin 3, 2 * π * ‖u j‖ * |((x j : ℤ) : ℝ)| := by linarith
    _ = _ := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- The generating function `∑_x e(|x|² z) e^{s 2πi (u·x)}`. -/
noncomputable def Theta3 (u : Fin 3 → ℂ) (z s : ℂ) : ℂ :=
  ∑' x : Fin 3 → ℤ, cexp (2 * π * I * sq3 x * z) * cexp (s * (2 * π * I * dot3 u x))

theorem Theta3_eq_prod (u : Fin 3 → ℂ) {z : ℂ} (hz : 0 < z.im) (s : ℂ) :
    Theta3 u z s = ∏ j, thetaJ z (s * u j) := by
  set f : Fin 3 → ℤ → ℂ := fun j n => cexp (2 * π * I * ((n : ℂ) ^ 2 * z + n * (s * u j))) with hf
  have hfs : ∀ j, Summable fun n => ‖f j n‖ := by
    intro j
    refine (summable_gauss_abs hz (2 * π * |(s * u j).im|)).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun n => ?_)
    simp only [hf, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have : (2 * π * I * ((n : ℂ) ^ 2 * z + n * (s * u j))).re =
        -2 * π * z.im * (n : ℝ) ^ 2 + -2 * π * (n : ℝ) * (s * u j).im := by
      simp [mul_re, mul_im, pow_two]; ring
    rw [this]
    have h1 : -2 * π * (n : ℝ) * (s * u j).im ≤ 2 * π * |(s * u j).im| * |(n : ℝ)| := by
      have := neg_abs_le ((n : ℝ) * (s * u j).im)
      rw [abs_mul] at this
      nlinarith [Real.pi_pos]
    linarith
  have hp := (tsum_pi_prod f hfs).2
  unfold Theta3
  unfold thetaJ
  rw [← hp]
  refine tsum_congr fun x => ?_
  simp only [hf]
  rw [← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  simp only [sq3, dot3, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Isotropic theta series on `Γ₀(4)`.** -/
theorem theta3_gamma (u : Fin 3 → ℂ) (hu : ∑ j, u j ^ 2 = 0) (ℓ : ℕ)
    (c : ℕ) [NeZero c] (hc4 : 4 ∣ c) (a b d : ℤ) (hdet : a * d - b * c = 1)
    (z : ℂ) (hz : 0 < z.im) :
    theta3 u ℓ ((a * z + b) / (c * z + d)) =
      (gaussQ (a : ZMod c) 0 / ((1 + I) * (Real.sqrt c : ℂ))) ^ 3 *
        (((c : ℂ) * z + d) ^ (1 / 2 : ℂ)) ^ 3 * ((c : ℂ) * z + d) ^ ℓ * theta3 u ℓ z := by
  set ζ₀ := (c : ℂ) * z + d with hζ₀
  set κ := gaussQ (a : ZMod c) 0 / ((1 + I) * (Real.sqrt c : ℂ)) with hκ
  set γz := (a * z + b) / (c * z + d) with hγz
  have hcr : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hζim : 0 < ζ₀.im := by
    rw [hζ₀]; simp only [add_im, mul_im, natCast_re, natCast_im, zero_mul, add_zero, intCast_im]
    positivity
  have hζ0 : ζ₀ ≠ 0 := fun h => by rw [h, zero_im] at hζim; exact lt_irrefl 0 hζim
  have hγim : 0 < γz.im := by
    have := gamma_sub a b c d hdet z (by exact_mod_cast NeZero.ne c) (by exact_mod_cast hζ0)
    push_cast at this
    rw [hγz, this]
    simp only [add_im, div_natCast_im, intCast_im, zero_div, zero_add]
    rw [div_im]
    simp only [neg_re, one_re, neg_im, one_im, neg_zero, zero_mul, zero_div, zero_sub]
    have h1 : ((c : ℂ) * (c * z + d)).im = c * ζ₀.im := by rw [← hζ₀]; simp [mul_im]
    rw [h1, neg_mul, neg_div, neg_neg]
    have : 0 < normSq ((c : ℂ) * (c * z + d)) := by
      rw [← hζ₀]; exact normSq_pos.mpr (mul_ne_zero hc' hζ0)
    positivity
  have hfun : (fun s => Theta3 u γz (s / ζ₀)) =
      fun s => κ ^ 3 * (ζ₀ ^ (1 / 2 : ℂ)) ^ 3 * Theta3 u z s := by
    funext s
    rw [Theta3_eq_prod u hγim, Theta3_eq_prod u hz]
    have hj : ∀ j, thetaJ γz (s / ζ₀ * u j) =
        κ * ζ₀ ^ (1 / 2 : ℂ) * cexp (2 * π * I * (c * (s * u j) ^ 2 / (4 * ζ₀))) *
          thetaJ z (s * u j) := by
      intro j
      rw [show s / ζ₀ * u j = (s * u j) / ((c : ℂ) * z + d) by rw [hζ₀]; ring]
      exact thetaJ_gamma c hc4 a b d hdet z hz (s * u j)
    simp only [hj, Fin.prod_univ_three]
    have hexp : cexp (2 * π * I * (c * (s * u 0) ^ 2 / (4 * ζ₀))) *
        cexp (2 * π * I * (c * (s * u 1) ^ 2 / (4 * ζ₀))) *
          cexp (2 * π * I * (c * (s * u 2) ^ 2 / (4 * ζ₀))) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      have : 2 * π * I * (c * (s * u 0) ^ 2 / (4 * ζ₀)) +
          2 * π * I * (c * (s * u 1) ^ 2 / (4 * ζ₀)) +
          2 * π * I * (c * (s * u 2) ^ 2 / (4 * ζ₀)) =
          2 * π * I * c * s ^ 2 / (4 * ζ₀) * (∑ j, u j ^ 2) := by
        simp only [Fin.sum_univ_three]; ring
      rw [this, hu, mul_zero, Complex.exp_zero]
    linear_combination (κ * ζ₀ ^ (1 / 2 : ℂ)) ^ 3 * thetaJ z (s * u 0) * thetaJ z (s * u 1) *
      thetaJ z (s * u 2) * hexp
  have hE := expSummable_theta3 u hγim
  have hE' : ExpSummable (fun x : Fin 3 → ℤ => cexp (2 * π * I * sq3 x * γz))
      (fun x => ζ₀⁻¹ * (2 * π * I * dot3 u x)) := hE.smul ζ₀⁻¹
  have hE0 := expSummable_theta3 u hz
  have lhs : iteratedDeriv ℓ (fun s => Theta3 u γz (s / ζ₀)) 0 =
      (ζ₀⁻¹ * (2 * π * I)) ^ ℓ * theta3 u ℓ γz := by
    have e : (fun s => Theta3 u γz (s / ζ₀)) = fun s => ∑' x : Fin 3 → ℤ,
        cexp (2 * π * I * sq3 x * γz) * cexp (s * (ζ₀⁻¹ * (2 * π * I * dot3 u x))) := by
      funext s; unfold Theta3; refine tsum_congr fun x => ?_; congr 2; field_simp
    rw [e, iteratedDeriv_tsum_exp hE' ℓ, theta3, ← tsum_mul_left]
    refine tsum_congr fun x => ?_
    ring
  have rhs : iteratedDeriv ℓ (fun s => κ ^ 3 * (ζ₀ ^ (1 / 2 : ℂ)) ^ 3 * Theta3 u z s) 0 =
      κ ^ 3 * (ζ₀ ^ (1 / 2 : ℂ)) ^ 3 * ((2 * π * I) ^ ℓ * theta3 u ℓ z) := by
    rw [iteratedDeriv_const_mul_field]
    congr 1
    have : Theta3 u z = fun s => ∑' x : Fin 3 → ℤ,
        cexp (2 * π * I * sq3 x * z) * cexp (s * (2 * π * I * dot3 u x)) := rfl
    rw [this, iteratedDeriv_tsum_exp hE0 ℓ, theta3, ← tsum_mul_left]
    refine tsum_congr fun x => ?_
    ring
  have key : iteratedDeriv ℓ (fun s => Theta3 u γz (s / ζ₀)) 0 =
      iteratedDeriv ℓ (fun s => κ ^ 3 * (ζ₀ ^ (1 / 2 : ℂ)) ^ 3 * Theta3 u z s) 0 := by rw [hfun]
  rw [lhs, rhs] at key
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hpow : (ζ₀⁻¹ * (2 * π * I)) ^ ℓ ≠ 0 := pow_ne_zero _ (mul_ne_zero (inv_ne_zero hζ0) h2pi)
  apply mul_left_cancel₀ hpow
  rw [key]
  have hz2 : (ζ₀⁻¹ * (2 * π * I)) ^ ℓ * ζ₀ ^ ℓ = (2 * π * I) ^ ℓ := by
    rw [← mul_pow]; congr 1; field_simp
  linear_combination (-(κ ^ 3 * (ζ₀ ^ (1 / 2 : ℂ)) ^ 3 * theta3 u ℓ z)) * hz2

end ThreeSquares
