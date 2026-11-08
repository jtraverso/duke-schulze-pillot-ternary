/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.FundDom
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrals over the upper half-plane as iterated integrals

* `map_coe_volume`: the invariant measure on `ℍ`, pushed to `ℂ`, is `dx dy / y²` on `Im > 0`.
* `lintegral_strip`, `integral_strip`: integrals over the strip `0 ≤ Re z < 1` as iterated
  integrals `∫_{y > 0} y⁻² ∫_{0 ≤ x < 1} … dx dy`.
-/

@[expose] public section

namespace ThreeSquares.FD

open UpperHalfPlane MeasureTheory Set

/-- The density `1 / y²`. -/
noncomputable def dens (w : ℂ) : ENNReal := ENNReal.ofReal (1 / w.im ^ 2)

theorem measurable_dens : Measurable dens := by
  unfold dens; fun_prop

/-- The upper half-plane as a subset of `ℂ`. -/
def Uc : Set ℂ := {w | 0 < w.im}

theorem measurableSet_Uc : MeasurableSet Uc := measurableSet_lt measurable_const Complex.measurable_im

theorem map_coe_volume : Measure.map UpperHalfPlane.coe (volume : Measure ℍ) =
    (volume.restrict Uc).withDensity dens := by
  ext s hs
  rw [Measure.map_apply measurable_coe hs, withDensity_apply _ hs, Measure.restrict_restrict hs,
    volume_eq_lintegral]
  have : UpperHalfPlane.coe '' (UpperHalfPlane.coe ⁻¹' s) = s ∩ Uc := by
    rw [Set.image_preimage_eq_inter_range, range_coe]; rfl
  rw [this]
  refine setLIntegral_congr_fun (hs.inter measurableSet_Uc) fun w hw => ?_
  have hpos : 0 < w.im := hw.2
  rw [dens, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  rw [Real.norm_eq_abs, abs_of_pos hpos, div_pow, one_pow]

theorem lintegral_H (G : ℂ → ENNReal) (hG : Measurable G) :
    ∫⁻ z : ℍ, G z = ∫⁻ w in Uc, dens w * G w := by
  rw [← measurableEmbedding_coe.lintegral_map, map_coe_volume,
    lintegral_withDensity_eq_lintegral_mul _ measurable_dens hG]
  rfl

theorem integral_H (F : ℂ → ℂ) :
    ∫ z : ℍ, F z = ∫ w in Uc, (1 / w.im ^ 2 : ℝ) • F w := by
  rw [← measurableEmbedding_coe.integral_map, map_coe_volume,
    integral_withDensity_eq_integral_toReal_smul measurable_dens
      (Filter.Eventually.of_forall fun w => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Uc fun w _ => ?_
  rw [dens, ENNReal.toReal_ofReal (by positivity)]

/-- The strip in `ℂ`. -/
def Sc : Set ℂ := {w | 0 ≤ w.re ∧ w.re < 1 ∧ 0 < w.im}

theorem measurableSet_Sc : MeasurableSet Sc := by
  unfold Sc
  exact (measurableSet_le measurable_const Complex.measurable_re).inter
    ((measurableSet_lt Complex.measurable_re measurable_const).inter
      (measurableSet_lt measurable_const Complex.measurable_im))

theorem symm_apply (p : ℝ × ℝ) :
    Complex.measurableEquivRealProd.symm p = (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Complex.measurableEquivRealProd]

theorem preimage_Sc : Complex.measurableEquivRealProd.symm ⁻¹' Sc = Ico 0 1 ×ˢ Ioi 0 := by
  ext ⟨x, y⟩
  simp [Sc, Complex.measurableEquivRealProd, Complex.equivRealProd]
  tauto

theorem strip_indicator (G : ℂ → ENNReal) (z : ℍ) :
    strip.indicator (fun z : ℍ => G z) z = ({w : ℂ | 0 ≤ w.re ∧ w.re < 1}.indicator G) z := by
  by_cases h : z ∈ strip
  · rw [indicator_of_mem h, indicator_of_mem (show (z : ℂ) ∈ {w : ℂ | 0 ≤ w.re ∧ w.re < 1} from h)]
  · rw [indicator_of_notMem h, indicator_of_notMem (show (z : ℂ) ∉ {w : ℂ | 0 ≤ w.re ∧ w.re < 1}
      from h)]

theorem measurableSet_stripC : MeasurableSet {w : ℂ | 0 ≤ w.re ∧ w.re < 1} :=
  (measurableSet_le measurable_const Complex.measurable_re).inter
    (measurableSet_lt Complex.measurable_re measurable_const)

/-- `∫⁻_{strip} G = ∫⁻_{y>0} ∫⁻_{0≤x<1} y⁻² G(x + iy)`. -/
theorem lintegral_strip (G : ℂ → ENNReal) (hG : Measurable G) :
    ∫⁻ z in strip, G z = ∫⁻ y : ℝ in Ioi 0, ∫⁻ x : ℝ in Ico 0 1,
      ENNReal.ofReal (1 / y ^ 2) * G ((x : ℂ) + (y : ℂ) * Complex.I) := by
  rw [← lintegral_indicator measurableSet_strip]
  simp_rw [strip_indicator G]
  rw [lintegral_H _ (hG.indicator measurableSet_stripC)]
  rw [← lintegral_indicator measurableSet_Uc]
  have : (Uc.indicator fun w => dens w * {w : ℂ | 0 ≤ w.re ∧ w.re < 1}.indicator G w) =
      Sc.indicator fun w => dens w * G w := by
    ext w
    by_cases h1 : 0 < w.im <;> simp [Uc, Sc, Set.indicator, h1]
  rw [this, lintegral_indicator measurableSet_Sc]
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding, preimage_Sc,
    Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm]
  · refine lintegral_congr fun y => lintegral_congr fun x => ?_
    simp [symm_apply, dens, Complex.mk_eq_add_mul_I]
  · exact ((measurable_dens.mul hG).comp
      Complex.measurableEquivRealProd.symm.measurable).aemeasurable

/-- `∫_{strip} F = ∫_{y>0} y⁻² ∫_{0≤x<1} F(x + iy)`, for `F` integrable on the strip. -/
theorem integral_strip (F : ℂ → ℂ) (hF : IntegrableOn (fun z : ℍ => F z) strip) :
    ∫ z in strip, F z = ∫ y : ℝ in Ioi 0, (1 / y ^ 2 : ℝ) •
      ∫ x : ℝ in Ico 0 1, F ((x : ℂ) + (y : ℂ) * Complex.I) := by
  have hind : ∀ z : ℍ, strip.indicator (fun z : ℍ => F z) z =
      ({w : ℂ | 0 ≤ w.re ∧ w.re < 1}.indicator F) z := by
    intro z
    by_cases h : z ∈ strip
    · rw [indicator_of_mem h, indicator_of_mem (show (z : ℂ) ∈ {w : ℂ | 0 ≤ w.re ∧ w.re < 1} from h)]
    · rw [indicator_of_notMem h, indicator_of_notMem (show (z : ℂ) ∉ {w : ℂ | 0 ≤ w.re ∧ w.re < 1}
        from h)]
  rw [← integral_indicator measurableSet_strip]
  simp_rw [hind]
  rw [integral_H, ← integral_indicator measurableSet_Uc]
  have : (Uc.indicator fun w => (1 / w.im ^ 2 : ℝ) • {w : ℂ | 0 ≤ w.re ∧ w.re < 1}.indicator F w) =
      Sc.indicator fun w => (1 / w.im ^ 2 : ℝ) • F w := by
    ext w
    by_cases h1 : 0 < w.im <;> simp [Uc, Sc, Set.indicator, h1]
  rw [this, integral_indicator measurableSet_Sc]
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).setIntegral_preimage_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding, preimage_Sc,
    Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm]
  · refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    rw [← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
    simp [symm_apply, Complex.mk_eq_add_mul_I]
  · -- integrability on the product, transported from the strip
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← preimage_Sc]
    have h1 : IntegrableOn (fun w : ℂ => (1 / w.im ^ 2 : ℝ) • F w) Sc := by
      have h0 : Integrable (strip.indicator fun z : ℍ => F z) := (integrable_indicator_iff
        measurableSet_strip).mpr hF
      rw [show (strip.indicator fun z : ℍ => F z) = fun z : ℍ =>
        ({w : ℂ | 0 ≤ w.re ∧ w.re < 1}.indicator F) z from funext hind] at h0
      replace h0 := (measurableEmbedding_coe.integrable_map_iff (μ := volume)
        (g := ({w : ℂ | 0 ≤ w.re ∧ w.re < 1}.indicator F))).mpr h0
      rw [map_coe_volume, integrable_withDensity_iff_integrable_smul' measurable_dens
          (Filter.Eventually.of_forall fun w => ENNReal.ofReal_lt_top)] at h0
      rw [← integrable_indicator_iff measurableSet_Sc]
      replace h0 := (integrable_indicator_iff measurableSet_Uc).mpr h0
      have hd : ∀ w, (dens w).toReal = 1 / w.im ^ 2 := fun w => by
        rw [dens, ENNReal.toReal_ofReal (by positivity)]
      simp only [hd] at h0
      refine h0.congr (Filter.Eventually.of_forall fun w => ?_)
      by_cases h1 : 0 < w.im <;> simp [Uc, Sc, Set.indicator, h1]
    exact (Complex.volume_preserving_equiv_real_prod.symm.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr h1

end ThreeSquares.FD
