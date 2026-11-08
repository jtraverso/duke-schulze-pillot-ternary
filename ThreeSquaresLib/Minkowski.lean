/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A small value of a positive definite ternary form

`exists_qf_lt_two`: a positive definite integral ternary quadratic form of determinant at most `2`
takes a value smaller than `2` at a nonzero integer vector. The ellipsoid `{q < 2}` is the preimage
of a Euclidean ball under the linear map of the `LDLᵀ` decomposition of the form, so its volume is
`(4/3) π 2^{3/2} / √det ≥ 8π/3 > 8`, and Minkowski's convex body theorem applies to `ℤ³`.
-/

@[expose] public section

namespace ThreeSquares

open MeasureTheory Matrix Real

/-- The quadratic form `xᵀ A x` of an integer matrix. -/
def qf (A : Matrix (Fin 3) (Fin 3) ℤ) (x : Fin 3 → ℤ) : ℤ := x ⬝ᵥ (A *ᵥ x)

theorem symm_entries {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : Aᵀ = A) :
    A 1 0 = A 0 1 ∧ A 2 0 = A 0 2 ∧ A 2 1 = A 1 2 := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrFun (congrFun hA 0) 1; simpa [transpose_apply] using this
  · have := congrFun (congrFun hA 0) 2; simpa [transpose_apply] using this
  · have := congrFun (congrFun hA 1) 2; simpa [transpose_apply] using this

theorem qf_expand {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : Aᵀ = A) (x : Fin 3 → ℤ) :
    qf A x = A 0 0 * x 0 ^ 2 + A 1 1 * x 1 ^ 2 + A 2 2 * x 2 ^ 2 + 2 * A 0 1 * x 0 * x 1 +
      2 * A 0 2 * x 0 * x 2 + 2 * A 1 2 * x 1 * x 2 := by
  obtain ⟨h10, h20, h21⟩ := symm_entries hA
  simp only [qf, dotProduct, mulVec, Fin.sum_univ_three, h10, h20, h21]
  ring

theorem det_expand {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : Aᵀ = A) :
    A.det = A 0 0 * A 1 1 * A 2 2 + 2 * A 0 1 * A 0 2 * A 1 2 - A 0 0 * A 1 2 ^ 2 -
      A 0 1 ^ 2 * A 2 2 - A 0 2 ^ 2 * A 1 1 := by
  obtain ⟨h10, h20, h21⟩ := symm_entries hA
  rw [det_fin_three, h10, h20, h21]
  ring

/-- The real quadratic form with the coefficients of `A`. -/
def qr (A : Matrix (Fin 3) (Fin 3) ℤ) (y : Fin 3 → ℝ) : ℝ :=
  (A 0 0 : ℝ) * y 0 ^ 2 + (A 1 1 : ℝ) * y 1 ^ 2 + (A 2 2 : ℝ) * y 2 ^ 2 +
    2 * (A 0 1 : ℝ) * y 0 * y 1 + 2 * (A 0 2 : ℝ) * y 0 * y 2 + 2 * (A 1 2 : ℝ) * y 1 * y 2

theorem qr_intCast {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : Aᵀ = A) (x : Fin 3 → ℤ) :
    qr A (fun i => (x i : ℝ)) = (qf A x : ℝ) := by
  rw [qf_expand hA]
  simp only [qr]
  push_cast
  ring

theorem qr_neg (A : Matrix (Fin 3) (Fin 3) ℤ) (y : Fin 3 → ℝ) : qr A (-y) = qr A y := by
  simp only [qr, Pi.neg_apply]
  ring

/-- The leading minors of a positive definite integral form are positive. -/
theorem minors_pos {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : Aᵀ = A)
    (hpos : ∀ x : Fin 3 → ℤ, x ≠ 0 → 0 < qf A x) :
    0 < A 0 0 ∧ 0 < A 0 0 * A 1 1 - A 0 1 ^ 2 := by
  have h1 := hpos ![1, 0, 0] (by intro h; have := congrFun h 0; simp at this)
  rw [qf_expand hA] at h1
  simp at h1
  refine ⟨h1, ?_⟩
  have h2 := hpos ![-A 0 1, A 0 0, 0] (by
    intro h; have := congrFun h 1; simp at this; omega)
  rw [qf_expand hA] at h2
  simp at h2
  have key : 0 < A 0 0 * (A 0 0 * A 1 1 - A 0 1 ^ 2) := by nlinarith
  exact pos_of_mul_pos_right key h1.le

set_option maxHeartbeats 4000000 in
-- the `LDLᵀ` identity and the volume computation exceed the default heartbeat budget
/-- **A small value.** A positive definite integral ternary form of determinant at most `2` takes a
value smaller than `2` at a nonzero integer vector. -/
theorem exists_qf_lt_two {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : Aᵀ = A)
    (hpos : ∀ x : Fin 3 → ℤ, x ≠ 0 → 0 < qf A x) (hdet : 0 < A.det) (hdet2 : A.det ≤ 2) :
    ∃ x : Fin 3 → ℤ, x ≠ 0 ∧ qf A x < 2 := by
  obtain ⟨ha0, hM0⟩ := minors_pos hA hpos
  rw [det_expand hA] at hdet hdet2
  have ha : (0 : ℝ) < (A 0 0 : ℝ) := by exact_mod_cast ha0
  have hM : (0 : ℝ) < (A 0 0 : ℝ) * (A 1 1 : ℝ) - (A 0 1 : ℝ) ^ 2 := by exact_mod_cast hM0
  have hD : (0 : ℝ) < (A 0 0 : ℝ) * (A 1 1 : ℝ) * (A 2 2 : ℝ) +
      2 * (A 0 1 : ℝ) * (A 0 2 : ℝ) * (A 1 2 : ℝ) - (A 0 0 : ℝ) * (A 1 2 : ℝ) ^ 2 -
      (A 0 1 : ℝ) ^ 2 * (A 2 2 : ℝ) - (A 0 2 : ℝ) ^ 2 * (A 1 1 : ℝ) := by exact_mod_cast hdet
  have hD2 : (A 0 0 : ℝ) * (A 1 1 : ℝ) * (A 2 2 : ℝ) +
      2 * (A 0 1 : ℝ) * (A 0 2 : ℝ) * (A 1 2 : ℝ) - (A 0 0 : ℝ) * (A 1 2 : ℝ) ^ 2 -
      (A 0 1 : ℝ) ^ 2 * (A 2 2 : ℝ) - (A 0 2 : ℝ) ^ 2 * (A 1 1 : ℝ) ≤ 2 := by exact_mod_cast hdet2
  set a : ℝ := (A 0 0 : ℝ) with ha_def
  set b : ℝ := (A 0 1 : ℝ) with hb_def
  set c : ℝ := (A 0 2 : ℝ) with hc_def
  set d : ℝ := (A 1 1 : ℝ) with hd_def
  set e : ℝ := (A 1 2 : ℝ) with he_def
  set f : ℝ := (A 2 2 : ℝ) with hf_def
  set M : ℝ := a * d - b ^ 2 with hM_def
  set D : ℝ := a * d * f + 2 * b * c * e - a * e ^ 2 - b ^ 2 * f - c ^ 2 * d with hD_def
  -- the `LDLᵀ` decomposition
  have hldl : ∀ y : Fin 3 → ℝ, qr A y = a * (y 0 + b / a * y 1 + c / a * y 2) ^ 2 +
      M / a * (y 1 + (a * e - b * c) / M * y 2) ^ 2 + D / M * y 2 ^ 2 := by
    intro y
    simp only [qr]
    rw [← ha_def, ← hb_def, ← hc_def, ← hd_def, ← he_def, ← hf_def]
    field_simp
    rw [hM_def, hD_def]
    ring
  have hqr_nonneg : ∀ y, 0 ≤ qr A y := by
    intro y
    rw [hldl]
    have h1 : 0 ≤ M / a := div_nonneg hM.le ha.le
    have h2 : 0 ≤ D / M := div_nonneg hD.le hM.le
    positivity
  -- the linear map
  set s₁ := Real.sqrt a
  set s₂ := Real.sqrt (M / a)
  set s₃ := Real.sqrt (D / M)
  have hs₁ : s₁ ^ 2 = a := Real.sq_sqrt ha.le
  have hs₂ : s₂ ^ 2 = M / a := Real.sq_sqrt (div_nonneg hM.le ha.le)
  have hs₃ : s₃ ^ 2 = D / M := Real.sq_sqrt (div_nonneg hD.le hM.le)
  let T : Matrix (Fin 3) (Fin 3) ℝ :=
    !![s₁, s₁ * (b / a), s₁ * (c / a); 0, s₂, s₂ * ((a * e - b * c) / M); 0, 0, s₃]
  have hT : ∀ y : Fin 3 → ℝ, ∑ i, (T *ᵥ y) i ^ 2 = qr A y := by
    intro y
    rw [hldl]
    have hsum : ∑ i, (T *ᵥ y) i ^ 2 = s₁ ^ 2 * (y 0 + b / a * y 1 + c / a * y 2) ^ 2 +
        s₂ ^ 2 * (y 1 + (a * e - b * c) / M * y 2) ^ 2 + s₃ ^ 2 * y 2 ^ 2 := by
      simp [T, mulVec, dotProduct, Fin.sum_univ_three]
      ring
    rw [hsum, hs₁, hs₂, hs₃]
  have hdetT : T.det = s₁ * s₂ * s₃ := by
    simp [T, det_fin_three]
  have hs_pos : 0 < s₁ * s₂ * s₃ := by
    have := Real.sqrt_pos.mpr ha
    have := Real.sqrt_pos.mpr (div_pos hM ha)
    have := Real.sqrt_pos.mpr (div_pos hD hM)
    positivity
  have hdetT_sq : (s₁ * s₂ * s₃) ^ 2 = D := by
    rw [mul_pow, mul_pow, hs₁, hs₂, hs₃]
    field_simp
  -- the convex body
  set S : Set (Fin 3 → ℝ) := {y | qr A y < 2} with hS
  set B : Set (Fin 3 → ℝ) := {z | (∑ i, |z i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) < Real.sqrt 2} with hB
  have hSB : S = (Matrix.toLin' T) ⁻¹' B := by
    ext y
    simp only [hS, hB, Set.mem_ofPred_eq, Set.mem_preimage, Matrix.toLin'_apply]
    have hsum : ∑ i, |(T *ᵥ y) i| ^ (2 : ℝ) = qr A y := by
      rw [← hT]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.rpow_two, sq_abs]
    rw [hsum, ← Real.sqrt_eq_rpow, Real.sqrt_lt_sqrt_iff (hqr_nonneg y)]
  have hvolB : volume B = ENNReal.ofReal (Real.sqrt 2 ^ 3 * (4 * π / 3)) := by
    rw [hB, MeasureTheory.volume_sum_rpow_lt (Fin 3) (by norm_num : (1 : ℝ) ≤ 2) (Real.sqrt 2)]
    simp only [Fintype.card_fin]
    have g1 : Real.Gamma (1 / 2 + 1) = Real.sqrt π / 2 := by
      rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]; ring
    have g2 : Real.Gamma ((3 : ℕ) / 2 + 1) = 3 * Real.sqrt π / 4 := by
      rw [show ((3 : ℕ) : ℝ) / 2 + 1 = (1 / 2 + 1) + 1 by norm_num,
        Real.Gamma_add_one (by norm_num), g1]
      ring
    rw [g1, g2, ← ENNReal.ofReal_pow (Real.sqrt_nonneg 2), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hpi : Real.sqrt π ^ 2 = π := Real.sq_sqrt Real.pi_pos.le
    have hpi0 : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    field_simp
    exact hpi
  have hdet0 : LinearMap.det (Matrix.toLin' T) ≠ 0 := by
    rw [LinearMap.det_toLin', hdetT]; exact hs_pos.ne'
  have hvolS : volume S = ENNReal.ofReal ((s₁ * s₂ * s₃)⁻¹ * (Real.sqrt 2 ^ 3 * (4 * π / 3))) := by
    rw [hSB, MeasureTheory.Measure.addHaar_preimage_linearMap _ hdet0, hvolB,
      LinearMap.det_toLin', hdetT, abs_of_pos (inv_pos.mpr hs_pos),
      ← ENNReal.ofReal_mul (inv_pos.mpr hs_pos).le]
  -- the volume exceeds `8`
  have hbig : (8 : ℝ) < (s₁ * s₂ * s₃)⁻¹ * (Real.sqrt 2 ^ 3 * (4 * π / 3)) := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsq2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hle : s₁ * s₂ * s₃ ≤ Real.sqrt 2 := by
      rw [← Real.sqrt_sq hs_pos.le, hdetT_sq]
      exact Real.sqrt_le_sqrt hD2
    rw [inv_mul_eq_div, lt_div_iff₀ hs_pos]
    have hpi := Real.pi_gt_three
    calc 8 * (s₁ * s₂ * s₃) ≤ 8 * Real.sqrt 2 := by linarith
      _ < Real.sqrt 2 ^ 3 * (4 * π / 3) := by
        rw [show Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 by ring, h2]
        nlinarith
  -- Minkowski
  have hconv : Convex ℝ S := by
    have hcvx : ConvexOn ℝ Set.univ (qr A) := by
      refine ⟨convex_univ, fun y _ z _ s t hs ht hst => ?_⟩
      have key : s * qr A y + t * qr A z - qr A (s • y + t • z) = s * t * qr A (y - z) := by
        have ht' : t = 1 - s := by linarith
        subst ht'
        simp only [qr, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      have := hqr_nonneg (y - z)
      simp only [smul_eq_mul]
      nlinarith [mul_nonneg (mul_nonneg hs ht) this]
    have := hcvx.convex_lt 2
    simpa [hS] using this
  have hsymm : ∀ y ∈ S, -y ∈ S := by
    intro y hy
    simp only [hS, Set.mem_ofPred_eq] at hy ⊢
    rwa [qr_neg]
  let L := (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 3)))).toAddSubgroup
  have fund := ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin 3)) volume
  have hmemL : ∀ m : Fin 3 → ℤ, (fun i => (m i : ℝ)) ∈ L := fun m =>
    ((Pi.basisFun ℝ (Fin 3)).mem_span_iff_repr_mem ℤ _).mpr (fun i => ⟨m i, by simp⟩)
  have hcoordL : ∀ x : L, ∀ i, ∃ m : ℤ, (m : ℝ) = (x : Fin 3 → ℝ) i := by
    intro x i
    obtain ⟨m, hm⟩ := ((Pi.basisFun ℝ (Fin 3)).mem_span_iff_repr_mem ℤ _).mp x.2 i
    exact ⟨m, by simpa [Pi.basisFun_repr] using hm⟩
  have : Countable L := by
    refine Function.Surjective.countable (f := fun m : Fin 3 → ℤ => (⟨_, hmemL m⟩ : L)) ?_
    intro x
    choose m hm using hcoordL x
    exact ⟨m, Subtype.ext (funext fun i => hm i)⟩
  have hF : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) = 1 := by
    rw [ZSpan.volume_fundamentalDomain]
    have : Matrix.of (Pi.basisFun ℝ (Fin 3)) = 1 := by
      ext i j
      simp [Pi.basisFun_apply, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this, det_one, abs_one, ENNReal.ofReal_one]
  have hvol : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin 3))) *
      2 ^ Module.finrank ℝ (Fin 3 → ℝ) < volume S := by
    rw [hF, Module.finrank_fin_fun, one_mul, hvolS]
    rw [show (2 : ENNReal) ^ 3 = ENNReal.ofReal 8 by norm_num]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hbig
  obtain ⟨x, hx0, hxS⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure fund hsymm hconv hvol
  -- an integer vector
  choose m hm using hcoordL x
  refine ⟨m, ?_, ?_⟩
  · intro h0
    apply hx0
    ext i
    have := hm i
    rw [h0] at this
    simp only [Pi.zero_apply, Int.cast_zero] at this
    rw [← this]
    rfl
  · have hx : (x : Fin 3 → ℝ) = fun i => (m i : ℝ) := funext fun i => (hm i).symm
    have h := hxS
    simp only [hS, Set.mem_ofPred_eq] at h
    rw [hx, qr_intCast hA] at h
    exact_mod_cast h

end ThreeSquares
