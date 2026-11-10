/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.Level
public import DukeH1.HInt
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Unfolding for complex integrands

`nu Q = ∑_{(k, r)} (γ_r σ_k)_* (vol|𝒟)`. For `T`-periodic `Φ` integrable on the strip,
`∫ Φ dν = 2 ∫_{strip} Φ` (`integral_nu`). Also `volume 𝒟 < ∞`.
-/

@[expose] public section

namespace ThreeSquares.FD

open UpperHalfPlane ModularGroup MeasureTheory Set

open scoped MatrixGroups

variable (Q : ℕ) [NeZero Q]

/-- `γ_r σ_k`. -/
noncomputable def gk (p : Keys Q × RowsQ Q) : SL(2, ℤ) := gam p.2.1 * pick Q p.1

/-- The unfolding measure. -/
noncomputable def nu : Measure ℍ :=
  Measure.sum fun p : Keys Q × RowsQ Q => (volume.restrict fd).map fun z => gk Q p • z

theorem lintegral_nu (ψ : ℍ → ENNReal) (hψ : Measurable ψ) (hper : ∀ z, ψ (T • z) = ψ z) :
    ∫⁻ z, ψ z ∂nu Q = 2 * ∫⁻ z in strip, ψ z := by
  rw [← unfold_level Q ψ hψ hper, nu, lintegral_sum_measure]
  simp_rw [lintegral_map hψ (measurable_smul_SL _)]
  rw [ENNReal.tsum_prod (f := fun (k : Keys Q) (r : RowsQ Q) => ∫⁻ z in fd, ψ (gk Q (k, r) • z)),
    tsum_fintype (L := SummationFilter.unconditional _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [lintegral_tsum (f := fun (r : RowsQ Q) z => ψ ((gam r.1 * pick Q k) • z))
    fun r => (hψ.comp (measurable_smul_SL _)).aemeasurable]
  rfl

theorem integrable_nu_iff (Φ : ℍ → ℂ) (hΦ : Measurable Φ) (hper : ∀ z, Φ (T • z) = Φ z) :
    Integrable Φ (nu Q) ↔ ∫⁻ z in strip, ‖Φ z‖ₑ < ⊤ := by
  rw [Integrable, and_iff_right hΦ.aestronglyMeasurable, HasFiniteIntegral,
    lintegral_nu Q _ hΦ.enorm (fun z => by rw [hper])]
  constructor
  · intro h
    by_contra h'
    rw [not_lt, top_le_iff] at h'
    rw [h', ENNReal.mul_top two_ne_zero] at h
    exact lt_irrefl _ h
  · intro h; exact ENNReal.mul_lt_top ENNReal.ofNat_lt_top h

/-- The unfolding identity for a measure `μ` on `ℍ`. -/
def UnfoldsStrip (μ : Measure ℍ) : Prop :=
  ∀ ψ : ℍ → ENNReal, Measurable ψ → (∀ z, ψ (T • z) = ψ z) → ∫⁻ z, ψ z ∂μ = 2 * ∫⁻ z in strip, ψ z

theorem unfoldsStrip_nu : UnfoldsStrip (nu Q) := fun ψ hψ hper => lintegral_nu Q ψ hψ hper

theorem integrable_of_unfolds {μ : Measure ℍ} (hμ : UnfoldsStrip μ) (Φ : ℍ → ℂ) (hΦ : Measurable Φ)
    (hper : ∀ z, Φ (T • z) = Φ z) (hint : ∫⁻ z in strip, ‖Φ z‖ₑ < ⊤) : Integrable Φ μ := by
  refine ⟨hΦ.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, hμ _ hΦ.enorm (fun z => by rw [hper])]
  exact ENNReal.mul_lt_top ENNReal.ofNat_lt_top hint

theorem integral_real_of_unfolds {μ : Measure ℍ} (hμ : UnfoldsStrip μ) (g : ℍ → ℝ)
    (hg : Measurable g) (hper : ∀ z, g (T • z) = g z) (hint : ∫⁻ z in strip, ‖g z‖ₑ < ⊤) :
    ∫ z, g z ∂μ = 2 * ∫ z in strip, g z := by
  have hi : Integrable g μ := by
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hμ _ hg.enorm (fun z => by rw [hper])]
    exact ENNReal.mul_lt_top ENNReal.ofNat_lt_top hint
  have hs : IntegrableOn g strip := ⟨hg.aestronglyMeasurable, hint⟩
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hs,
    hμ (fun z => ENNReal.ofReal (g z)) (ENNReal.measurable_ofReal.comp hg)
      (fun z => by rw [hper]),
    hμ (fun z => ENNReal.ofReal (-g z)) (ENNReal.measurable_ofReal.comp hg.neg)
      (fun z => by rw [hper]),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_ofNat]
  ring

/-- **Unfolding for complex `T`-periodic integrands**, for any measure with the unfolding identity. -/
theorem integral_of_unfolds {μ : Measure ℍ} (hμ : UnfoldsStrip μ) (Φ : ℍ → ℂ) (hΦ : Measurable Φ)
    (hper : ∀ z, Φ (T • z) = Φ z) (hint : ∫⁻ z in strip, ‖Φ z‖ₑ < ⊤) :
    ∫ z, Φ z ∂μ = 2 * ∫ z in strip, Φ z := by
  have hi : Integrable Φ μ := integrable_of_unfolds hμ Φ hΦ hper hint
  have hs : IntegrableOn Φ strip := ⟨hΦ.aestronglyMeasurable, hint⟩
  rw [← integral_re_add_im hi, ← integral_re_add_im hs]
  have hre := integral_real_of_unfolds hμ (fun z => RCLike.re (Φ z))
    (RCLike.continuous_re.measurable.comp hΦ)
    (fun z => by show RCLike.re (Φ (T • z)) = RCLike.re (Φ z); rw [hper])
    (lt_of_le_of_lt (setLIntegral_mono hΦ.enorm fun z _ => by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (RCLike.norm_re_le_norm (Φ z))) hint)
  have him := integral_real_of_unfolds hμ (fun z => RCLike.im (Φ z))
    (RCLike.continuous_im.measurable.comp hΦ)
    (fun z => by show RCLike.im (Φ (T • z)) = RCLike.im (Φ z); rw [hper])
    (lt_of_le_of_lt (setLIntegral_mono hΦ.enorm fun z _ => by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (RCLike.norm_im_le_norm (Φ z))) hint)
  rw [hre, him]
  push_cast
  ring

theorem integral_nu (Φ : ℍ → ℂ) (hΦ : Measurable Φ) (hper : ∀ z, Φ (T • z) = Φ z)
    (hint : ∫⁻ z in strip, ‖Φ z‖ₑ < ⊤) :
    ∫ z, Φ z ∂nu Q = 2 * ∫ z in strip, Φ z :=
  integral_of_unfolds (unfoldsStrip_nu Q) Φ hΦ hper hint

/-- Integrals against `ν` as sums over `(k, r)` of integrals over `𝒟`. -/
theorem integral_nu_eq_tsum (Φ : ℍ → ℂ) (hi : Integrable Φ (nu Q)) (hΦ : Measurable Φ) :
    ∫ z, Φ z ∂nu Q = ∑' p : Keys Q × RowsQ Q, ∫ z in fd, Φ (gk Q p • z) := by
  rw [nu, integral_sum_measure hi]
  refine tsum_congr fun p => ?_
  rw [integral_map (measurable_smul_SL _).aemeasurable hΦ.aestronglyMeasurable]

/-! ### `volume 𝒟 < ∞` -/

theorem measurableSet_high : MeasurableSet {z : ℍ | Real.sqrt 3 / 2 ≤ z.im} :=
  measurableSet_le measurable_const (by fun_prop)

theorem volume_strip_high_lt_top :
    volume (strip ∩ {z : ℍ | Real.sqrt 3 / 2 ≤ z.im}) < ⊤ := by
  set H := {z : ℍ | Real.sqrt 3 / 2 ≤ z.im}
  have e1 : volume (strip ∩ H) = ∫⁻ z in strip, H.indicator 1 z := by
    rw [lintegral_indicator_one measurableSet_high, Measure.restrict_apply measurableSet_high,
      inter_comm]
  set G : ℂ → ENNReal := fun w => if Real.sqrt 3 / 2 ≤ w.im then 1 else 0
  have hG : Measurable G := Measurable.ite (measurableSet_le measurable_const
    Complex.measurable_im) measurable_const measurable_const
  have e2 : ∫⁻ z in strip, H.indicator 1 z = ∫⁻ z in strip, G z := by
    refine lintegral_congr fun z => ?_
    by_cases h : Real.sqrt 3 / 2 ≤ z.im
    · simp [H, G, h, indicator]
    · simp [H, G, h, indicator]
  rw [e1, e2, lintegral_strip G hG]
  have hc : (0 : ℝ) < Real.sqrt 3 / 2 := by positivity
  have hint : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi (Real.sqrt 3 / 2)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hc
  calc ∫⁻ y in Ioi 0, ∫⁻ x in Ico (0 : ℝ) 1, ENNReal.ofReal (1 / y ^ 2) *
        G ((x : ℂ) + (y : ℂ) * Complex.I)
      = ∫⁻ y in Ioi 0, (Ici (Real.sqrt 3 / 2)).indicator (fun y => ENNReal.ofReal (1 / y ^ 2)) y := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
        by_cases h : Real.sqrt 3 / 2 ≤ y
        · simp [G, h, indicator]
        · simp [G, h, indicator]
    _ ≤ ∫⁻ y in Ioi (Real.sqrt 3 / 4), ‖y ^ (-2 : ℝ)‖ₑ := by
        rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
        refine lintegral_mono fun y => ?_
        by_cases h : Real.sqrt 3 / 2 ≤ y
        · have hy : 0 < y := lt_of_lt_of_le hc h
          have hy4 : y ∈ Ioi (Real.sqrt 3 / 4) := by
            simp only [mem_Ioi]; linarith
          rw [indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy), indicator_of_mem (show y ∈
            Ici (Real.sqrt 3 / 2) from h), indicator_of_mem hy4, ← ofReal_norm_eq_enorm]
          apply ENNReal.ofReal_le_ofReal
          rw [Real.norm_eq_abs, abs_of_pos (by positivity), Real.rpow_neg hy.le,
            Real.rpow_two, one_div]
        · by_cases h0 : y ∈ Ioi (0 : ℝ)
          · rw [indicator_of_mem h0, indicator_of_notMem (show y ∉ Ici (Real.sqrt 3 / 2) from h)]
            exact bot_le
          · rw [indicator_of_notMem h0]; exact bot_le
    _ < ⊤ := by
        have h2 : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Ioi (Real.sqrt 3 / 4)) :=
          integrableOn_Ioi_rpow_of_lt (by norm_num) (by positivity)
        exact h2.2

theorem im_ge_of_mem_fd {z : ℍ} (hz : z ∈ fd) : Real.sqrt 3 / 2 ≤ z.im := by
  have h3 := three_le_four_mul_im_sq_of_mem_fd hz
  have hy := z.im_pos
  rw [show Real.sqrt 3 / 2 = Real.sqrt (3 / 4) by
    rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
  rw [show z.im = Real.sqrt (z.im ^ 2) from (Real.sqrt_sq hy.le).symm]
  exact Real.sqrt_le_sqrt (by linarith)

theorem volume_fd_lt_top : volume fd < ⊤ := by
  set H := {z : ℍ | Real.sqrt 3 / 2 ≤ z.im}
  have hsub : fd ⊆ (strip ∩ H) ∪ (fun z => T • z) ⁻¹' (strip ∩ H) := by
    intro z hz
    have hre := abs_le.mp hz.2
    have him := im_ge_of_mem_fd hz
    by_cases h : 0 ≤ z.re
    · left; exact ⟨⟨h, by linarith⟩, him⟩
    · right
      have hT : T • z = ((1 : ℝ) +ᵥ z) := by simpa using modular_T_smul z
      simp only [mem_preimage, hT]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simp; linarith
      · simp; linarith
      · show Real.sqrt 3 / 2 ≤ ((1 : ℝ) +ᵥ z).im
        simpa using him
  calc volume fd ≤ volume ((strip ∩ H) ∪ (fun z => T • z) ⁻¹' (strip ∩ H)) := measure_mono hsub
    _ ≤ volume (strip ∩ H) + volume ((fun z => T • z) ⁻¹' (strip ∩ H)) := measure_union_le _ _
    _ = volume (strip ∩ H) + volume (strip ∩ H) := by
        rw [(measurePreserving_SL T).measure_preimage
          (measurableSet_strip.inter measurableSet_high).nullMeasurableSet]
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨volume_strip_high_lt_top, volume_strip_high_lt_top⟩

/-! ### The Petersson measure at level `Q` -/

/-- `μ_Q = ∑_k (σ_k)_* (vol|𝒟)`: integrating a `Γ₀(Q)`-invariant function against `μ_Q` is
integrating over `Γ₀(Q)\ℍ` (twice). -/
noncomputable def muQ : Measure ℍ :=
  Measure.sum fun k : Keys Q => (volume.restrict fd).map fun z => pick Q k • z

theorem lintegral_muQ (ψ : ℍ → ENNReal) (hψ : Measurable ψ) :
    ∫⁻ z, ψ z ∂muQ Q = ∑ k : Keys Q, ∫⁻ z in fd, ψ (pick Q k • z) := by
  rw [muQ, lintegral_sum_measure, tsum_fintype (L := SummationFilter.unconditional _)]
  simp_rw [lintegral_map hψ (measurable_smul_SL _)]

instance : IsFiniteMeasure (muQ Q) := by
  refine ⟨?_⟩
  rw [← lintegral_one, lintegral_muQ Q _ measurable_const]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul]
  exact ENNReal.sum_lt_top.mpr fun k _ => volume_fd_lt_top

/-- `ν' = ∑_r (γ_r)_* μ_Q`. -/
noncomputable def nu' : Measure ℍ :=
  Measure.sum fun r : RowsQ Q => (muQ Q).map fun z => gam r.1 • z

theorem unfoldsStrip_nu' : UnfoldsStrip (nu' Q) := by
  intro ψ hψ hper
  rw [← unfold_level Q ψ hψ hper, nu', lintegral_sum_measure]
  simp_rw [lintegral_map hψ (measurable_smul_SL _)]
  rw [tsum_congr fun r : RowsQ Q => lintegral_muQ Q (fun z => ψ (gam r.1 • z))
    (hψ.comp (measurable_smul_SL _))]
  simp_rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  rw [lintegral_tsum (f := fun (r : RowsQ Q) z => ψ ((gam r.1 * pick Q k) • z))
    fun r => (hψ.comp (measurable_smul_SL _)).aemeasurable]
  simp_rw [mul_smul]

theorem integral_nu'_eq (Φ : ℍ → ℂ) (hi : Integrable Φ (nu' Q)) (hΦ : Measurable Φ) :
    ∫ z, Φ z ∂nu' Q = ∑' r : RowsQ Q, ∫ z, Φ (gam r.1 • z) ∂muQ Q := by
  rw [nu', integral_sum_measure hi]
  refine tsum_congr fun r => ?_
  rw [integral_map (measurable_smul_SL _).aemeasurable hΦ.aestronglyMeasurable]

end ThreeSquares.FD
