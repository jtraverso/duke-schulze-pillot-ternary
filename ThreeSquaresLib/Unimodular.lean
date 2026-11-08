/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Minkowski

/-!
# Positive definite unimodular ternary forms

`exists_eq_transpose_mul`: a positive definite integral ternary quadratic form of determinant `1` is
equivalent to `x² + y² + z²`, i.e. its matrix is `Pᵀ P` for an integer matrix `P`. A vector `v₁`
with `q(v₁) = 1` exists by `exists_qf_lt_two`; applied to the form `q(x) + B(v₁, x)²` (determinant
`2`) it gives `v₂` with `q(v₂) = 1` and `B(v₁, v₂) = 0`; the vector `w = adj(A) (v₁ × v₂)` completes
an orthonormal basis.
-/

@[expose] public section

namespace ThreeSquares

open Matrix

/-- The bilinear form `xᵀ A y`. -/
def bf (A : Matrix (Fin 3) (Fin 3) ℤ) (x y : Fin 3 → ℤ) : ℤ := x ⬝ᵥ (A *ᵥ y)

/-- The cross product. -/
def cr (u v : Fin 3 → ℤ) : Fin 3 → ℤ :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

theorem bf_symm {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : Aᵀ = A) (x y : Fin 3 → ℤ) :
    bf A x y = bf A y x := by
  obtain ⟨h10, h20, h21⟩ := symm_entries hA
  simp only [bf, dotProduct, mulVec, Fin.sum_univ_three, h10, h20, h21]
  ring

theorem bf_self (A : Matrix (Fin 3) (Fin 3) ℤ) (x : Fin 3 → ℤ) : bf A x x = qf A x := rfl

theorem det_add_vecMulVec (A : Matrix (Fin 3) (Fin 3) ℤ) (c : Fin 3 → ℤ) :
    (A + vecMulVec c c).det = A.det + c ⬝ᵥ (adjugate A *ᵥ c) := by
  simp [det_fin_three, adjugate_fin_three, vecMulVec_apply, dotProduct, mulVec,
    Fin.sum_univ_three]
  ring

theorem cr_dot_left (u v : Fin 3 → ℤ) : u ⬝ᵥ cr u v = 0 := by
  simp [cr, dotProduct, Fin.sum_univ_three]
  ring

theorem cr_dot_right (u v : Fin 3 → ℤ) : v ⬝ᵥ cr u v = 0 := by
  simp [cr, dotProduct, Fin.sum_univ_three]
  ring

/-- `(v₁ × v₂)ᵀ adj(A) (v₁ × v₂)` is the Gram determinant of `v₁, v₂`. -/
theorem cr_adj_cr {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : Aᵀ = A) (v₁ v₂ : Fin 3 → ℤ) :
    cr v₁ v₂ ⬝ᵥ (adjugate A *ᵥ cr v₁ v₂) = qf A v₁ * qf A v₂ - bf A v₁ v₂ ^ 2 := by
  obtain ⟨h10, h20, h21⟩ := symm_entries hA
  simp [cr, qf, bf, adjugate_fin_three, dotProduct, mulVec, Fin.sum_univ_three, h10, h20, h21]
  ring

/-- `A (adj(A) u) = u` for `det A = 1`. -/
theorem mulVec_adjugate_mulVec {A : Matrix (Fin 3) (Fin 3) ℤ} (hdet : A.det = 1)
    (u : Fin 3 → ℤ) : A *ᵥ (adjugate A *ᵥ u) = u := by
  rw [mulVec_mulVec, mul_adjugate, hdet, one_smul, one_mulVec]

set_option maxHeartbeats 4000000 in
-- the construction of the orthonormal basis exceeds the default heartbeat budget
/-- **Unimodular ternary forms.** A positive definite integral ternary form of determinant `1` has
matrix `Pᵀ P` for an integer matrix `P`. -/
theorem exists_eq_transpose_mul {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : Aᵀ = A)
    (hpos : ∀ x : Fin 3 → ℤ, x ≠ 0 → 0 < qf A x) (hdet : A.det = 1) :
    ∃ P : Matrix (Fin 3) (Fin 3) ℤ, A = Pᵀ * P := by
  -- a vector of norm one
  obtain ⟨v₁, hv₁0, hv₁⟩ := exists_qf_lt_two hA hpos (by rw [hdet]; norm_num)
    (by rw [hdet]; norm_num)
  have hq₁ : qf A v₁ = 1 := by have := hpos v₁ hv₁0; omega
  -- a second one, orthogonal to the first
  set c := A *ᵥ v₁ with hc
  set A' := A + vecMulVec c c with hA'def
  have hA' : A'ᵀ = A' := by
    rw [hA'def, transpose_add, hA, transpose_vecMulVec]
  have hcx : ∀ x, c ⬝ᵥ x = bf A v₁ x := by
    intro x
    rw [hc, bf_symm hA, bf, dotProduct_comm]
  have hqA' : ∀ x, qf A' x = qf A x + (c ⬝ᵥ x) ^ 2 := by
    intro x
    simp [qf, hA'def, dotProduct, mulVec, vecMulVec_apply,
      Fin.sum_univ_three]
    ring
  have hposA' : ∀ x : Fin 3 → ℤ, x ≠ 0 → 0 < qf A' x := by
    intro x hx
    rw [hqA']
    have := hpos x hx
    positivity
  have hdetA' : A'.det = 2 := by
    rw [hA'def, det_add_vecMulVec, hdet, hc, mulVec_mulVec, adjugate_mul, hdet, one_smul,
      one_mulVec, dotProduct_comm, ← qf, hq₁]
    norm_num
  obtain ⟨v₂, hv₂0, hv₂⟩ := exists_qf_lt_two hA' hposA' (by rw [hdetA']; norm_num)
    (by rw [hdetA'])
  rw [hqA'] at hv₂
  have hq₂pos := hpos v₂ hv₂0
  set t := (c ⬝ᵥ v₂) ^ 2 with ht
  have ht0 : 0 ≤ t := sq_nonneg _
  have hq₂ : qf A v₂ = 1 := by omega
  have hb₁₂ : bf A v₁ v₂ = 0 := by
    have : t = 0 := by omega
    rw [ht] at this
    rw [← hcx]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  -- the third vector
  set u := cr v₁ v₂ with hu
  set w := adjugate A *ᵥ u with hw
  have hAw : A *ᵥ w = u := mulVec_adjugate_mulVec hdet u
  have hbw : ∀ v, bf A v w = v ⬝ᵥ u := by
    intro v; rw [bf, hAw]
  have hw₁ : bf A v₁ w = 0 := by rw [hbw, hu, cr_dot_left]
  have hw₂ : bf A v₂ w = 0 := by rw [hbw, hu, cr_dot_right]
  have hqw : qf A w = 1 := by
    rw [← bf_self, hbw, hw, dotProduct_comm, hu, cr_adj_cr hA, hq₁, hq₂, hb₁₂]
    norm_num
  -- the basis matrix
  let cols : Fin 3 → Fin 3 → ℤ := ![v₁, v₂, w]
  let V : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun i j => cols j i
  have hentry : ∀ j k, (Vᵀ * A * V) j k = bf A (cols j) (cols k) := by
    intro j k
    simp only [V, bf, Matrix.mul_apply, transpose_apply, of_apply, dotProduct, mulVec,
      Fin.sum_univ_three]
    ring
  have hgram : Vᵀ * A * V = 1 := by
    ext j k
    rw [hentry]
    fin_cases j <;> fin_cases k <;>
      simp [cols, bf_self, hq₁, hq₂, hqw, hb₁₂, hw₁, hw₂, bf_symm hA v₂ v₁,
        bf_symm hA w v₁, bf_symm hA w v₂]
  have hdetV : V.det * V.det = 1 := by
    have := congrArg Matrix.det hgram
    rw [det_mul, det_mul, det_transpose, hdet, det_one, mul_one] at this
    exact this
  have hunit : IsUnit V.det := isUnit_iff_exists_inv.mpr ⟨V.det, hdetV⟩
  refine ⟨V⁻¹, ?_⟩
  have hVP : V * V⁻¹ = 1 := mul_nonsing_inv V hunit
  calc A = (V * V⁻¹)ᵀ * A * (V * V⁻¹) := by rw [hVP, transpose_one, Matrix.one_mul, Matrix.mul_one]
    _ = (V⁻¹)ᵀ * (Vᵀ * A * V) * V⁻¹ := by
        rw [transpose_mul]; simp only [Matrix.mul_assoc]
    _ = (V⁻¹)ᵀ * V⁻¹ := by rw [hgram, Matrix.mul_one]

/-- The diagonal entries of a positive definite integral ternary form of determinant `1` are sums
of three squares. -/
theorem sum_three_sq_of_unimodular {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : Aᵀ = A)
    (hpos : ∀ x : Fin 3 → ℤ, x ≠ 0 → 0 < qf A x) (hdet : A.det = 1) (k : Fin 3) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = A k k := by
  obtain ⟨P, hP⟩ := exists_eq_transpose_mul hA hpos hdet
  refine ⟨P 0 k, P 1 k, P 2 k, ?_⟩
  rw [hP, Matrix.mul_apply, Fin.sum_univ_three]
  simp only [transpose_apply]
  ring

end ThreeSquares
