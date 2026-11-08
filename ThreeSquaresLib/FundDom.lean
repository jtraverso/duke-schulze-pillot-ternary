/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.NumberTheory.Modular
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The standard fundamental domain, measure-theoretically

* `measurePreserving_SL`: `SL(2, ℤ)` preserves the invariant measure `dx dy / y²` on `ℍ`.
* `volume_fd_diff_fdo`: the boundary `fd \ fdo` is a null set.
* `ae_unique_fd`: for almost every `z ∈ ℍ` there is `g` with `g • z ∈ fdo`, and every `h` with
  `h • z ∈ fd` is `± g`.
-/

@[expose] public section

namespace ThreeSquares.FD

open UpperHalfPlane ModularGroup MeasureTheory Matrix.SpecialLinearGroup

open scoped MatrixGroups

instance : Countable (Matrix (Fin 2) (Fin 2) ℤ) := by unfold Matrix; infer_instance

instance : Countable SL(2, ℤ) := Subtype.countable

theorem smul_eq_GL (g : SL(2, ℤ)) (z : ℍ) : g • z = (mapGL ℝ g) • z :=
  MulAction.compHom_smul_def _ g z

theorem measurePreserving_SL (g : SL(2, ℤ)) :
    MeasurePreserving (fun z : ℍ => g • z) volume volume := by
  have : (fun z : ℍ => g • z) = fun z => (mapGL ℝ g) • z := by
    funext z; exact smul_eq_GL g z
  rw [this]
  exact measurePreserving_smul _ _

/-- A set of `ℂ` that is Lebesgue-null gives a null subset of `ℍ`. -/
theorem volume_eq_zero_of_coe_null {s : Set ℍ} (h : volume (UpperHalfPlane.coe '' s) = 0) :
    volume s = 0 := by
  rw [volume_eq_lintegral]
  exact setLIntegral_measure_zero _ _ h

theorem volume_re_eq (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm).measure_preimage
    (s := {z : ℂ | z.re = c}) (measurableSet_eq_fun Complex.measurable_re measurable_const).nullMeasurableSet
  rw [← h]
  have : Complex.measurableEquivRealProd.symm ⁻¹' {z : ℂ | z.re = c} = {c} ×ˢ Set.univ := by
    ext ⟨x, y⟩; simp [Complex.measurableEquivRealProd]
  rw [this, Measure.volume_eq_prod, Measure.prod_prod]
  simp

theorem volume_fd_diff_fdo : volume (fd \ fdo) = 0 := by
  apply volume_eq_zero_of_coe_null
  have hsub : UpperHalfPlane.coe '' (fd \ fdo) ⊆
      {z : ℂ | z.re = 1 / 2} ∪ {z : ℂ | z.re = -1 / 2} ∪ Metric.sphere 0 1 := by
    rintro _ ⟨z, ⟨hz, hzo⟩, rfl⟩
    simp only [fd, fdo, Set.mem_setOf_eq, not_and_or, not_lt] at hz hzo
    rcases hzo with h | h
    · right
      rw [mem_sphere_zero_iff_norm]
      have h1 := hz.1
      have e : Complex.normSq (z : ℂ) = ‖(z : ℂ)‖ ^ 2 := Complex.normSq_eq_norm_sq _
      have h3 : ‖(z : ℂ)‖ ^ 2 = 1 := by linarith
      have hn := norm_nonneg (z : ℂ)
      nlinarith
    · left
      have h2 : |z.re| = 1 / 2 := le_antisymm hz.2 h
      rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mp h2 with h3 | h3
      · left; simpa using h3
      · right; simp only [Set.mem_setOf_eq]; rw [UpperHalfPlane.coe_re]; linarith
  refine measure_mono_null hsub (measure_union_null (measure_union_null (volume_re_eq _)
    (volume_re_eq _)) ?_)
  exact Measure.addHaar_sphere volume (0 : ℂ) 1

/-- The null set of points whose orbit meets the boundary of `fd`. -/
def badSet : Set ℍ := ⋃ g : SL(2, ℤ), (fun z => g • z) ⁻¹' (fd \ fdo)

theorem volume_badSet : volume badSet = 0 := by
  refine measure_iUnion_null fun g => ?_
  rw [(measurePreserving_SL g).measure_preimage
    ((isClosed_fd.measurableSet.diff isOpen_fdo.measurableSet).nullMeasurableSet)]
  exact volume_fd_diff_fdo

theorem unique_fd {z : ℍ} (hz : z ∉ badSet) :
    ∃ g : SL(2, ℤ), g • z ∈ fdo ∧ ∀ h : SL(2, ℤ), h • z ∈ fd → h = g ∨ h = -g := by
  have hgood : ∀ g : SL(2, ℤ), g • z ∈ fd → g • z ∈ fdo := by
    intro g hg
    by_contra hno
    exact hz (Set.mem_iUnion.mpr ⟨g, hg, hno⟩)
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  refine ⟨g, hgood g hg, fun h hh => ?_⟩
  have h1 := hgood g hg
  have h2 := hgood h hh
  have : (h * g⁻¹) • (g • z) ∈ fdo := by rwa [smul_smul, inv_mul_cancel_right]
  rcases eq_one_or_neg_one_of_mem_fdo_mem_fdo h1 this with e | e
  · left; rw [← mul_inv_eq_one.mp e]
  · right
    have : h = -1 * g := by rw [← e]; group
    rw [this]; simp

/-! ### Unfolding against the strip -/

/-- Coprime bottom rows. -/
abbrev Rows : Type := {r : Fin 2 → ℤ // IsCoprime (r 0) (r 1)}

instance : Countable Rows := Subtype.countable

/-- A matrix with bottom row `r`. -/
noncomputable def gam (r : Rows) : SL(2, ℤ) := (bottom_row_surj (R := ℤ) r.2).choose

theorem gam_row (r : Rows) : (gam r : Matrix (Fin 2) (Fin 2) ℤ) 1 = r.1 :=
  (bottom_row_surj (R := ℤ) r.2).choose_spec.2

theorem row_coprime (h : SL(2, ℤ)) : IsCoprime (h 1 0) (h 1 1) := by
  have hd := h.det_coe
  rw [Matrix.det_fin_two] at hd
  exact ⟨-(h 0 1), h 0 0, by linarith⟩

/-- The row of `h`. -/
def rowOf (h : SL(2, ℤ)) : Rows := ⟨(h : Matrix (Fin 2) (Fin 2) ℤ) 1, row_coprime h⟩

theorem bottom_row_eq_T (g : SL(2, ℤ)) (h0 : g 1 0 = 0) (h1 : g 1 1 = 1) : g = T ^ (g 0 1) := by
  have hd := g.det_coe
  rw [Matrix.det_fin_two, h0, h1] at hd
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_T_zpow, h0, h1] <;> linarith

theorem row_mul_inv (h : SL(2, ℤ)) :
    (h * (gam (rowOf h))⁻¹) 1 0 = 0 ∧ (h * (gam (rowOf h))⁻¹) 1 1 = 1 := by
  have hr := gam_row (rowOf h)
  have hd := (gam (rowOf h)).det_coe
  rw [Matrix.det_fin_two] at hd
  simp only [rowOf] at hr
  have h10 : (gam (rowOf h)) 1 0 = h 1 0 := by rw [← congrFun hr 0]; rfl
  have h11 : (gam (rowOf h)) 1 1 = h 1 1 := by rw [← congrFun hr 1]; rfl
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.head_fin_const]
  rw [← h10, ← h11]
  exact ⟨by ring, by linear_combination hd⟩

theorem row_T_mul (m : ℤ) (r : Rows) : rowOf (T ^ m * gam r) = r := by
  apply Subtype.ext
  ext j
  have := gam_row r
  simp only [rowOf, Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow]
  rw [← this]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `SL(2, ℤ) ≃ Σ (r : coprime rows), ℤ`, `h = T^m γ_r`. -/
noncomputable def slEquiv : SL(2, ℤ) ≃ Σ _r : Rows, ℤ where
  toFun h := ⟨rowOf h, (h * (gam (rowOf h))⁻¹) 0 1⟩
  invFun p := T ^ p.2 * gam p.1
  left_inv h := by
    simp only
    obtain ⟨h0, h1⟩ := row_mul_inv h
    rw [← bottom_row_eq_T _ h0 h1, inv_mul_cancel_right]
  right_inv p := by
    obtain ⟨r, m⟩ := p
    simp only [row_T_mul m r, mul_inv_cancel_right]
    congr
    simp [coe_T_zpow]

/-- The strip `0 ≤ Re z < 1`. -/
def strip : Set ℍ := {z | 0 ≤ z.re ∧ z.re < 1}

theorem measurableSet_strip : MeasurableSet strip := by
  have hre : Measurable fun z : ℍ => z.re :=
    Complex.measurable_re.comp measurable_coe
  exact (measurableSet_le measurable_const hre).inter (measurableSet_lt hre measurable_const)

/-- Exactly one translate `z + m` lies in the strip. -/
theorem tsum_indicator_strip (z : ℍ) (c : ENNReal) :
    ∑' m : ℤ, strip.indicator (fun _ => c) (T ^ m • z) = c := by
  set m₀ := -⌊z.re⌋ with hm₀
  rw [tsum_eq_single m₀]
  · rw [Set.indicator_of_mem]
    simp only [strip, Set.mem_setOf_eq, re_T_zpow_smul, hm₀, Int.cast_neg]
    constructor
    · linarith [Int.floor_le z.re]
    · linarith [Int.lt_floor_add_one z.re]
  · intro m hm
    rw [Set.indicator_of_notMem]
    simp only [strip, Set.mem_setOf_eq, re_T_zpow_smul, not_and_or, not_le, not_lt]
    by_contra hcon
    push Not at hcon
    apply hm
    have h1 := hcon.1; have h2 := hcon.2
    have : ⌊z.re⌋ = -m := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    rw [hm₀, this, neg_neg]

theorem neg_ne_self (g : SL(2, ℤ)) : -g ≠ g := by
  intro h
  have h1 := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ)) h
  have hd := g.det_coe
  rw [Matrix.det_fin_two] at hd
  have e : ∀ i j, -(g i j) = g i j := fun i j => by
    have := congrFun (congrFun h1 i) j
    simpa [Matrix.SpecialLinearGroup.coe_neg] using this
  have := e 0 0; have := e 1 1; have := e 0 1; have := e 1 0
  have h00 : g 0 0 = 0 := by linarith
  have h01 : g 0 1 = 0 := by linarith
  rw [h00, h01] at hd
  simp at hd

theorem tsum_indicator_fd {z : ℍ} (hz : z ∉ badSet) :
    ∑' h : SL(2, ℤ), fd.indicator (fun _ => (1 : ENNReal)) (h • z) = 2 := by
  obtain ⟨g, hg, huniq⟩ := unique_fd hz
  have hgfd : g • z ∈ fd := fdo_subset_fd hg
  have hngfd : (-g) • z ∈ fd := by rwa [SL_neg_smul]
  rw [tsum_eq_sum (s := {g, -g})]
  · rw [Finset.sum_pair (neg_ne_self g).symm, Set.indicator_of_mem hgfd, Set.indicator_of_mem hngfd]
    norm_num
  · intro h hh
    rw [Set.indicator_of_notMem]
    intro hmem
    rcases huniq h hmem with e | e <;> simp [e] at hh

theorem psi_T_zpow {ψ : ℍ → ENNReal} (hper : ∀ z, ψ (T • z) = ψ z) (m : ℤ) (z : ℍ) :
    ψ (T ^ m • z) = ψ z := by
  induction m using Int.induction_on generalizing z with
  | zero => simp
  | succ n ih => rw [zpow_add_one, mul_smul, ih, hper]
  | pred n ih =>
    rw [zpow_sub_one, mul_smul, ih, ← hper (T⁻¹ • z), smul_inv_smul]

theorem measurable_smul_SL (g : SL(2, ℤ)) : Measurable fun z : ℍ => g • z :=
  (measurePreserving_SL g).measurable

/-- **Unfolding for `SL(2, ℤ)`.** For a measurable `T`-periodic `ψ ≥ 0`,
`∫_{strip} ψ = ½ ∑_{coprime rows r} ∫_𝒟 ψ(γ_r z)`. -/
theorem unfold_strip (ψ : ℍ → ENNReal) (hψ : Measurable ψ) (hper : ∀ z, ψ (T • z) = ψ z) :
    ∫⁻ z in strip, ψ z = (1 / 2) * ∑' r : Rows, ∫⁻ z in fd, ψ (gam r • z) := by
  have hfdm : MeasurableSet fd := isClosed_fd.measurableSet
  -- step 1: insert `½ ∑_h 1_𝒟(h z)`
  have hae : (fun z => strip.indicator ψ z) =ᵐ[volume] fun z =>
      (1 / 2) * ∑' h : SL(2, ℤ), fd.indicator (fun _ => (1 : ENNReal)) (h • z) *
        strip.indicator ψ z := by
    have hnull : ∀ᵐ z ∂volume, z ∉ badSet := measure_eq_zero_iff_ae_notMem.mp volume_badSet
    filter_upwards [hnull] with z hz
    rw [ENNReal.tsum_mul_right, tsum_indicator_fd hz, ← mul_assoc, one_div,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
  rw [← lintegral_indicator measurableSet_strip, lintegral_congr_ae hae,
    lintegral_const_mul' _ _ (by norm_num)]
  congr 1
  rw [lintegral_tsum (f := fun (h : SL(2, ℤ)) (z : ℍ) =>
    fd.indicator (fun _ => (1 : ENNReal)) (h • z) * strip.indicator ψ z) fun h =>
      (((measurable_const.indicator hfdm).comp (measurable_smul_SL h)).mul
        (hψ.indicator measurableSet_strip)).aemeasurable]
  -- step 2: change variables `w = h z`
  have hcv : ∀ h : SL(2, ℤ), ∫⁻ z, fd.indicator (fun _ => (1 : ENNReal)) (h • z) *
      strip.indicator ψ z = ∫⁻ w, fd.indicator (fun _ => (1 : ENNReal)) w *
        strip.indicator ψ (h⁻¹ • w) := by
    intro h
    have hmp := measurePreserving_SL h⁻¹
    rw [← hmp.lintegral_comp (f := fun w => fd.indicator (fun _ => (1 : ENNReal)) (h • w) *
      strip.indicator ψ w) (((measurable_const.indicator hfdm).comp (measurable_smul_SL h)).mul
        (hψ.indicator measurableSet_strip))]
    refine lintegral_congr fun z => ?_
    simp only [smul_inv_smul]
  simp_rw [hcv]
  rw [← (Equiv.inv SL(2, ℤ)).tsum_eq]
  simp only [Equiv.inv_apply, inv_inv]
  rw [← lintegral_tsum (f := fun (h : SL(2, ℤ)) (w : ℍ) =>
    fd.indicator (fun _ => (1 : ENNReal)) w * strip.indicator ψ (h • w)) fun h =>
      ((measurable_const.indicator hfdm).mul
        ((hψ.indicator measurableSet_strip).comp (measurable_smul_SL h))).aemeasurable]
  simp_rw [ENNReal.tsum_mul_left]
  -- step 3: the pointwise sum over `h`
  have hpt : ∀ w : ℍ, ∑' h : SL(2, ℤ), strip.indicator ψ (h • w) = ∑' r : Rows, ψ (gam r • w) := by
    intro w
    rw [← slEquiv.symm.tsum_eq, ENNReal.tsum_sigma']
    refine tsum_congr fun r => ?_
    simp only [slEquiv, Equiv.coe_fn_symm_mk, mul_smul]
    have : ∀ m : ℤ, strip.indicator ψ (T ^ m • gam r • w) =
        strip.indicator (fun _ => ψ (gam r • w)) (T ^ m • gam r • w) := by
      intro m
      by_cases hm : T ^ m • gam r • w ∈ strip
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm, psi_T_zpow hper]
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm]
    simp_rw [this]
    exact tsum_indicator_strip _ _
  simp_rw [hpt]
  have hptw : ∀ w, fd.indicator (fun _ => (1 : ENNReal)) w * ∑' r : Rows, ψ (gam r • w) =
      ∑' r : Rows, fd.indicator (fun z => ψ (gam r • z)) w := by
    intro w
    by_cases hw : w ∈ fd
    · simp [hw]
    · simp [hw]
  simp_rw [hptw]
  rw [lintegral_tsum (f := fun (r : Rows) (w : ℍ) => fd.indicator (fun z => ψ (gam r • z)) w)
    fun r => (hψ.comp (measurable_smul_SL (gam r))).aemeasurable.indicator hfdm]
  exact tsum_congr fun r => lintegral_indicator hfdm _

end ThreeSquares.FD
