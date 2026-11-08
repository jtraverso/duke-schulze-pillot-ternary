/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Petersson
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The Petersson product and unfolding against Poincaré series

* `pet ℓ Q F G = ∫ F conj(G) y^k dμ_Q`;
* `pet_poin`: for `F` automorphic of weight `k` on `Γ₀(Q)`, measurable and with `y^{k/2}|F|`
  bounded, `⟨F, P_n⟩ = 2 ∫_{strip} F(z) conj(e(nz)) y^k`;
* `norm_pet_sq_le`: Cauchy–Schwarz; `pet_self_le`: `⟨F, F⟩ ≤ M² μ_Q(ℍ)`.
-/

@[expose] public section

namespace ThreeSquares.Poin

open Complex UpperHalfPlane ModularGroup MeasureTheory ThreeSquares.FD ThreeSquares.Mult Filter
  Topology

open scoped MatrixGroups Real ComplexConjugate

variable (ℓ : ℕ) (n : ℕ)

/-- `e(nw)`. -/
noncomputable def en (w : ℂ) : ℂ := cexp (2 * π * Complex.I * n * w)

/-- The Petersson product at level `Q`. -/
noncomputable def pet (Q : ℕ) [NeZero Q] (F G : ℂ → ℂ) : ℂ :=
  ∫ z, F z * conj (G z) * ((z.im ^ kw ℓ : ℝ) : ℂ) ∂muQ Q

/-- Weight-`k` automorphic forms on `Γ₀(Q)` with `y^{k/2}|F|` bounded. -/
structure IsAut (Q : ℕ) (F : ℂ → ℂ) : Prop where
  aut : ∀ γ : SL(2, ℤ), InG0 Q γ → ∀ z : ℂ, 0 < z.im → F (mob γ z) = jk ℓ γ z * F z
  meas : Measurable fun z : ℍ => F z
  bdd : ∃ M : ℝ, ∀ z : ℍ, z.im ^ (kw ℓ / 2) * ‖F z‖ ≤ M

theorem isAut_poin (hℓ : 1 ≤ ℓ) {Q : ℕ} (hQ : 4 ∣ Q) (hn : 0 < n) : IsAut ℓ Q (poin ℓ Q n) where
  aut γ hγ z hz := poin_mob ℓ n hQ γ hγ hz
  meas := measurable_poinH ℓ n hℓ hQ hn
  bdd := by
    obtain ⟨M, -, hM⟩ := poin_bound ℓ n hℓ hQ hn
    refine ⟨M, fun z => le_trans ?_ (hM z).2⟩
    exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hM z).1) (by positivity)

/-- The unfolded integrand `F(w) conj(e(nw)) y^k`. -/
noncomputable def PhiF (F : ℂ → ℂ) (w : ℍ) : ℂ := F w * conj (en n w) * ((w.im ^ kw ℓ : ℝ) : ℂ)

theorem en_add_one (w : ℂ) : en n (w + 1) = en n w := by
  unfold en
  rw [mul_add, Complex.exp_add, show 2 * π * Complex.I * n * (1 : ℂ) = ((n : ℤ) : ℂ) *
    (2 * π * Complex.I) by push_cast; ring, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem T_smul_coe (w : ℍ) : ((T • w : ℍ) : ℂ) = w + 1 := by
  rw [show T • w = ((1 : ℝ) +ᵥ w) by simpa using modular_T_smul w]; simp [add_comm]

theorem PhiF_T {Q : ℕ} {F : ℂ → ℂ} (hF : IsAut ℓ Q F) (w : ℍ) :
    PhiF ℓ n F (T • w) = PhiF ℓ n F w := by
  have hFT : F (w + 1) = F w := by
    have h := hF.aut (T ^ (1 : ℤ)) (by simpa using inG0_T Q) w w.im_pos
    rwa [jk_T_zpow, one_mul, mob_T_zpow, Int.cast_one] at h
  have him : (T • w).im = w.im := by
    rw [show (T • w).im = ((T • w : ℍ) : ℂ).im from rfl, T_smul_coe]; simp
  unfold PhiF
  rw [T_smul_coe, hFT, en_add_one, him]

theorem pt_unfold {Q : ℕ} {F : ℂ → ℂ} (hF : IsAut ℓ Q F) (γ : SL(2, ℤ)) (hγ : InG0 Q γ)
    (h4 : (4 : ℤ) ∣ γ 1 0) (w : ℍ) :
    F w * conj (phi ℓ n γ w) * ((w.im ^ kw ℓ : ℝ) : ℂ) = PhiF ℓ n F (γ • w) := by
  have hw := w.im_pos
  have hj : jk ℓ γ w ≠ 0 := jk_ne_zero ℓ γ h4 hw
  have hnorm : ‖jk ℓ γ w‖ = ‖den γ w‖ ^ kw ℓ := norm_jk ℓ γ h4 hw
  have hD : 0 < ‖den γ w‖ := norm_pos_iff.mpr (den_ne_zero γ hw)
  have hIm : (γ • w).im ^ kw ℓ = w.im ^ kw ℓ / ‖jk ℓ γ w‖ ^ 2 := by
    rw [hnorm, ModularGroup.im_smul_eq_div_normSq, ← den_eq, Complex.normSq_eq_norm_sq,
      Real.div_rpow hw.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hD.le, ← Real.rpow_mul hD.le, mul_comm]
  unfold PhiF phi
  rw [show ((γ • w : ℍ) : ℂ) = mob γ w from (mob_eq γ w).symm, hF.aut γ hγ w hw, hIm]
  have hc : conj (jk ℓ γ w) ≠ 0 := (map_ne_zero _).mpr hj
  rw [map_mul, map_inv₀]
  push_cast
  rw [← Complex.mul_conj']
  unfold en
  field_simp

/-! ### Integrability on the strip -/

theorem lintegral_strip_rpow_exp_lt_top {s b C : ℝ} (hs : -1 < s) (hb : 0 < b) :
    ∫⁻ z in strip, ENNReal.ofReal (C * z.im ^ (s + 2) * Real.exp (-(b * z.im))) < ⊤ := by
  set G : ℂ → ENNReal := fun w => ENNReal.ofReal (C * w.im ^ (s + 2) * Real.exp (-(b * w.im)))
  have hG : Measurable G := by simp only [G]; fun_prop
  show ∫⁻ z in strip, G z < ⊤
  rw [lintegral_strip _ hG]
  have hint : IntegrableOn (fun y : ℝ => y ^ s * Real.exp (-b * y ^ (1 : ℝ))) (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow hs one_pos hb
  calc ∫⁻ y in Set.Ioi 0, ∫⁻ x in Set.Ico (0 : ℝ) 1, ENNReal.ofReal (1 / y ^ 2) *
        ENNReal.ofReal (C * ((x : ℂ) + (y : ℂ) * Complex.I).im ^ (s + 2) *
          Real.exp (-(b * ((x : ℂ) + (y : ℂ) * Complex.I).im)))
      = ∫⁻ y in Set.Ioi 0, ENNReal.ofReal (C * (y ^ s * Real.exp (-b * y ^ (1 : ℝ)))) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
        have hy0 : 0 < y := hy
        simp only [add_im, ofReal_im, mul_im, ofReal_re, Complex.I_re, mul_zero, Complex.I_im, mul_one,
          zero_add, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_Ico, sub_zero, ENNReal.ofReal_one, mul_one, Real.rpow_one]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [add_zero, Real.rpow_add hy0, Real.rpow_two, neg_mul]
        field_simp
    _ ≤ ∫⁻ y in Set.Ioi 0, ‖C * (y ^ s * Real.exp (-b * y ^ (1 : ℝ)))‖ₑ := by
        refine setLIntegral_mono (by fun_prop) fun y _ => ?_
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ < ⊤ := (hint.const_mul C).2

theorem norm_PhiF_le {Q : ℕ} {F : ℂ → ℂ} {M : ℝ} (hM : ∀ z : ℍ, z.im ^ (kw ℓ / 2) * ‖F z‖ ≤ M)
    (w : ℍ) : ‖PhiF ℓ n F w‖ ≤ M * w.im ^ (kw ℓ / 2) * Real.exp (-(2 * π * n * w.im)) := by
  have hw := w.im_pos
  unfold PhiF en
  rw [norm_mul, norm_mul, Complex.norm_conj, norm_cexp_n, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  have hF : ‖F w‖ ≤ M * w.im ^ (-(kw ℓ / 2)) := by
    have := hM w
    rw [Real.rpow_neg hw.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  have e : w.im ^ kw ℓ = w.im ^ (kw ℓ / 2) * w.im ^ (kw ℓ / 2) := by
    rw [← Real.rpow_add hw]; ring_nf
  calc ‖F w‖ * Real.exp (-(2 * π * n * w.im)) * w.im ^ kw ℓ
      ≤ M * w.im ^ (-(kw ℓ / 2)) * Real.exp (-(2 * π * n * w.im)) * w.im ^ kw ℓ := by gcongr
    _ = M * w.im ^ (kw ℓ / 2) * Real.exp (-(2 * π * n * w.im)) := by
        rw [e, Real.rpow_neg hw.le]
        field_simp

theorem lintegral_PhiF_lt_top (hℓ : 1 ≤ ℓ) (hn : 0 < n) {Q : ℕ} {F : ℂ → ℂ} (hF : IsAut ℓ Q F) :
    ∫⁻ z in strip, ‖PhiF ℓ n F z‖ₑ < ⊤ := by
  obtain ⟨M, hM⟩ := hF.bdd
  have hk : -1 < kw ℓ / 2 - 2 := by
    unfold kw; have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  refine lt_of_le_of_lt (setLIntegral_mono (by fun_prop) fun z _ => ?_)
    (lintegral_strip_rpow_exp_lt_top (C := M) hk (by positivity : (0 : ℝ) < 2 * π * n))
  rw [← ofReal_norm_eq_enorm, show kw ℓ / 2 - 2 + 2 = kw ℓ / 2 by ring]
  apply ENNReal.ofReal_le_ofReal
  have := norm_PhiF_le ℓ n (Q := Q) hM z
  rwa [show -(2 * π * n * z.im) = -(2 * π * n * z.im) from rfl] at this

/-! ### Unfolding -/

theorem measurable_PhiF {Q : ℕ} {F : ℂ → ℂ} (hF : IsAut ℓ Q F) : Measurable (PhiF ℓ n F) := by
  unfold PhiF en
  have h1 := hF.meas
  have h2 : Measurable fun w : ℍ => (w : ℂ) := measurable_coe
  have h3 : Measurable fun w : ℍ => w.im := Complex.measurable_im.comp measurable_coe
  exact (h1.mul (Complex.continuous_conj.measurable.comp (by fun_prop))).mul
    (Complex.measurable_ofReal.comp (h3.pow_const _))

/-- **Unfolding: `⟨F, P_n⟩ = 2 ∫_{strip} F(z) conj(e(nz)) y^k`.** -/
theorem pet_poin (hℓ : 1 ≤ ℓ) (hn : 0 < n) {Q : ℕ} [NeZero Q] (hQ : 4 ∣ Q) {F : ℂ → ℂ}
    (hF : IsAut ℓ Q F) :
    pet ℓ Q F (poin ℓ Q n) = 2 * ∫ z in strip, PhiF ℓ n F z := by
  have hpt : ∀ z : ℍ, F z * conj (poin ℓ Q n z) * ((z.im ^ kw ℓ : ℝ) : ℂ) =
      ∑' r : RowsQ Q, PhiF ℓ n F (gam r.1 • z) := by
    intro z
    unfold poin
    rw [conj_tsum, ← tsum_mul_left, ← tsum_mul_right]
    exact tsum_congr fun r => pt_unfold ℓ n hF (gam r.1) (inG0_gam r.2) (dvd4_gam hQ r) z
  have hmeas := measurable_PhiF ℓ n hF
  have hper := PhiF_T ℓ n hF
  have hint := lintegral_PhiF_lt_top ℓ n hℓ hn hF
  unfold pet
  rw [integral_congr_ae (Eventually.of_forall hpt)]
  rw [← integral_of_unfolds (unfoldsStrip_nu' Q) _ hmeas hper hint,
    integral_nu'_eq Q _ (integrable_of_unfolds (unfoldsStrip_nu' Q) _ hmeas hper hint) hmeas]
  refine integral_tsum (μ := muQ Q) (f := fun (r : RowsQ Q) (z : ℍ) => PhiF ℓ n F (gam r.1 • z))
    (fun r => (hmeas.comp (measurable_smul_SL _)).aestronglyMeasurable) ?_
  have := unfoldsStrip_nu' Q (fun z => ‖PhiF ℓ n F z‖ₑ) hmeas.enorm (fun z => by rw [hper])
  rw [nu', lintegral_sum_measure] at this
  simp_rw [lintegral_map hmeas.enorm (measurable_smul_SL _)] at this
  rw [this]
  exact (ENNReal.mul_lt_top ENNReal.ofNat_lt_top hint).ne

/-! ### Cauchy–Schwarz and the trivial bound -/

theorem pet_self_eq (Q : ℕ) [NeZero Q] (F : ℂ → ℂ) :
    pet ℓ Q F F = ((∫ z, ‖F z‖ ^ 2 * z.im ^ kw ℓ ∂muQ Q : ℝ) : ℂ) := by
  unfold pet
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [Complex.mul_conj']
  push_cast; ring

theorem norm_pet_sq_le (Q : ℕ) [NeZero Q] {F G : ℂ → ℂ} (hF : IsAut ℓ Q F) (hG : IsAut ℓ Q G) :
    ‖pet ℓ Q F G‖ ^ 2 ≤ (∫ z, ‖F z‖ ^ 2 * z.im ^ kw ℓ ∂muQ Q) *
      (∫ z, ‖G z‖ ^ 2 * z.im ^ kw ℓ ∂muQ Q) := by
  obtain ⟨MF, hMF⟩ := hF.bdd
  obtain ⟨MG, hMG⟩ := hG.bdd
  set f : ℍ → ℝ := fun z => z.im ^ (kw ℓ / 2) * ‖F z‖
  set g : ℍ → ℝ := fun z => z.im ^ (kw ℓ / 2) * ‖G z‖
  have h3 : Measurable fun w : ℍ => w.im := Complex.measurable_im.comp measurable_coe
  have hfm : Measurable f := (h3.pow_const _).mul hF.meas.norm
  have hgm : Measurable g := (h3.pow_const _).mul hG.meas.norm
  have hf0 : ∀ z, 0 ≤ f z := fun z => by simp only [f]; positivity
  have hg0 : ∀ z, 0 ≤ g z := fun z => by simp only [g]; positivity
  have hfL : MemLp f (ENNReal.ofReal 2) (muQ Q) :=
    MemLp.of_bound hfm.aestronglyMeasurable MF (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]; exact hMF z)
  have hgL : MemLp g (ENNReal.ofReal 2) (muQ Q) :=
    MemLp.of_bound hgm.aestronglyMeasurable MG (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 z)]; exact hMG z)
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := muQ Q) Real.HolderConjugate.two_two
    (Eventually.of_forall hf0) (Eventually.of_forall hg0) hfL hgL
  have hsq : ∀ z : ℍ, z.im ^ kw ℓ = (z.im ^ (kw ℓ / 2)) ^ 2 := fun z => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul z.im_pos.le]; norm_num
  have hff : ∀ z, f z ^ (2 : ℝ) = ‖F z‖ ^ 2 * z.im ^ kw ℓ := fun z => by
    simp only [f]; rw [Real.rpow_two, hsq]; ring
  have hgg : ∀ z, g z ^ (2 : ℝ) = ‖G z‖ ^ 2 * z.im ^ kw ℓ := fun z => by
    simp only [g]; rw [Real.rpow_two, hsq]; ring
  simp_rw [hff, hgg] at hCS
  have hA : 0 ≤ ∫ z, ‖F z‖ ^ 2 * z.im ^ kw ℓ ∂muQ Q :=
    integral_nonneg fun z => by positivity
  have hB : 0 ≤ ∫ z, ‖G z‖ ^ 2 * z.im ^ kw ℓ ∂muQ Q :=
    integral_nonneg fun z => by positivity
  have hnorm : ‖pet ℓ Q F G‖ ≤ ∫ z, f z * g z ∂muQ Q := by
    unfold pet
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq (integral_congr_ae
      (Eventually.of_forall fun z => ?_)))
    simp only [f, g]
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < z.im ^ kw ℓ), hsq]
    ring
  have hpos : 0 ≤ ∫ z, f z * g z ∂muQ Q := integral_nonneg fun z => mul_nonneg (hf0 z) (hg0 z)
  calc ‖pet ℓ Q F G‖ ^ 2 ≤ (∫ z, f z * g z ∂muQ Q) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ ((∫ z, ‖F z‖ ^ 2 * z.im ^ kw ℓ ∂muQ Q) ^ (1 / (2 : ℝ)) *
          (∫ z, ‖G z‖ ^ 2 * z.im ^ kw ℓ ∂muQ Q) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ hpos hCS 2
    _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hA,
          ← Real.rpow_mul hB]
        norm_num

theorem pet_self_le (Q : ℕ) [NeZero Q] {F : ℂ → ℂ} (hF : IsAut ℓ Q F) {M : ℝ}
    (hM : ∀ z : ℍ, z.im ^ (kw ℓ / 2) * ‖F z‖ ≤ M) :
    ∫ z, ‖F z‖ ^ 2 * z.im ^ kw ℓ ∂muQ Q ≤ M ^ 2 * (muQ Q Set.univ).toReal := by
  have hb : ∀ z : ℍ, ‖F z‖ ^ 2 * z.im ^ kw ℓ ≤ M ^ 2 := fun z => by
    have h0 : 0 ≤ z.im ^ (kw ℓ / 2) * ‖F z‖ := by positivity
    have hsq : z.im ^ kw ℓ = (z.im ^ (kw ℓ / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul z.im_pos.le]; norm_num
    rw [hsq, show ‖F z‖ ^ 2 * (z.im ^ (kw ℓ / 2)) ^ 2 = (z.im ^ (kw ℓ / 2) * ‖F z‖) ^ 2 by ring]
    exact pow_le_pow_left₀ h0 (hM z) 2
  calc ∫ z, ‖F z‖ ^ 2 * z.im ^ kw ℓ ∂muQ Q ≤ ∫ _z, M ^ 2 ∂muQ Q :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => by positivity)
          (integrable_const _) (Eventually.of_forall hb)
    _ = M ^ 2 * (muQ Q Set.univ).toReal := by
        rw [integral_const, smul_eq_mul, mul_comm, Measure.real]

end ThreeSquares.Poin
