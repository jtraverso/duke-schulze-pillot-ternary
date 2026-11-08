/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.B3_Roots
public import ThreeSquaresLib.Unimodular
public import ThreeSquaresLib.Weyl

/-!
# Good forms give points on the sphere

`exists_basis_of_good`: if `f = (a, b, c) ∈ Red n` is good (`n ∣ 2f(r, s) + 1`), there are
`e₁, e₂, e₃ ∈ ℤ³` with Gram matrix `[[2a, b], [b, 2c]]` for `e₁, e₂` and `det(e₁, e₂, e₃) = 1`.
The matrix `F = [[2a, b, −s], [b, 2c, r], [−s, r, (2f(r,s)+1)/n]]` is positive definite of
determinant `1` (`A D q = D(Ax₀ + Bx₁ + Rx₂)² + (Dx₁ + Ex₂)² + A det F x₂²`), hence `Pᵀ P`
(`exists_eq_transpose_mul`), and `e_i` are the columns of `P`.
`cr_sq_sum` (Lagrange): `|e₁ × e₂|² = |e₁|²|e₂|² − (e₁·e₂)² = 4ac − b² = n`.
-/

@[expose] public section

namespace ThreeSquares.B3

open Matrix ThreeSquares

/-- Lagrange's identity. -/
theorem cr_sq_sum (u v : Fin 3 → ℤ) :
    ∑ i, cr u v i ^ 2 = (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2 := by
  simp [cr, dotProduct, Fin.sum_univ_three]
  ring

/-- `det P = col₂ · (col₀ × col₁)`. -/
theorem det_eq_dot_cr (P : Matrix (Fin 3) (Fin 3) ℤ) :
    P.det = (fun k => P k 2) ⬝ᵥ cr (fun k => P k 0) (fun k => P k 1) := by
  simp [det_fin_three, cr, dotProduct, Fin.sum_univ_three]
  ring

theorem gram_of_eq {F P : Matrix (Fin 3) (Fin 3) ℤ} (h : F = Pᵀ * P) (i j : Fin 3) :
    F i j = (fun k => P k i) ⬝ᵥ (fun k => P k j) := by
  rw [h, mul_apply]
  simp [dotProduct]

set_option maxHeartbeats 1000000 in
-- positivity of the explicit 3 × 3 matrix
theorem exists_basis_of_good {n : ℕ} (hn : 0 < n) {f : Form} (hf : f ∈ Red n)
    (hg : Good n f) :
    ∃ e₁ e₂ e₃ : Fin 3 → ℤ, e₁ ⬝ᵥ e₁ = 2 * f.a ∧ e₁ ⬝ᵥ e₂ = f.b ∧ e₂ ⬝ᵥ e₂ = 2 * f.c ∧
      e₃ ⬝ᵥ cr e₁ e₂ = 1 := by
  obtain ⟨hd, -, ha⟩ := mem_Red.mp hf
  obtain ⟨r, s, u, hu⟩ := hg
  unfold Form.disc at hd
  unfold Form.eval at hu
  let F : Matrix (Fin 3) (Fin 3) ℤ := !![2 * f.a, f.b, -s; f.b, 2 * f.c, r; -s, r, u]
  have hF : Fᵀ = F := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hdet : F.det = 1 := by
    simp [F, det_fin_three]
    linear_combination -hu - u * hd
  have hpos : ∀ x : Fin 3 → ℤ, x ≠ 0 → 0 < qf F x := by
    intro x hx
    have hq : qf F x = 2 * f.a * x 0 ^ 2 + 2 * f.c * x 1 ^ 2 + u * x 2 ^ 2 +
        2 * f.b * x 0 * x 1 + 2 * -s * x 0 * x 2 + 2 * r * x 1 * x 2 := by
      rw [qf_expand hF]
      simp [F, vecHead, vecTail]
    rw [hq]
    set E := 2 * f.a * r - f.b * -s
    have key : 2 * f.a * (n : ℤ) * (2 * f.a * x 0 ^ 2 + 2 * f.c * x 1 ^ 2 + u * x 2 ^ 2 +
        2 * f.b * x 0 * x 1 + 2 * -s * x 0 * x 2 + 2 * r * x 1 * x 2) =
        n * (2 * f.a * x 0 + f.b * x 1 + -s * x 2) ^ 2 + (n * x 1 + E * x 2) ^ 2 +
          2 * f.a * x 2 ^ 2 := by
      have hD : (n : ℤ) = 2 * f.a * (2 * f.c) - f.b ^ 2 := by linarith
      have hdet' : 2 * f.a * (2 * f.c * u - r ^ 2) - f.b * (f.b * u - r * -s) +
          -s * (f.b * r - 2 * f.c * -s) = 1 := by linear_combination -hu - u * hd
      rw [hD]
      linear_combination 2 * f.a * x 2 ^ 2 * hdet'
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have h2a : 0 < 2 * f.a * (n : ℤ) := by positivity
    have hR : 0 < (n : ℤ) * (2 * f.a * x 0 + f.b * x 1 + -s * x 2) ^ 2 +
        (n * x 1 + E * x 2) ^ 2 + 2 * f.a * x 2 ^ 2 := by
      have t1 : 0 ≤ (n : ℤ) * (2 * f.a * x 0 + f.b * x 1 + -s * x 2) ^ 2 := by positivity
      have t2 : 0 ≤ ((n : ℤ) * x 1 + E * x 2) ^ 2 := sq_nonneg _
      by_cases h2 : x 2 = 0
      · by_cases h1 : x 1 = 0
        · have h0 : x 0 ≠ 0 := by
            intro h0
            apply hx
            ext i
            fin_cases i <;> simp [h0, h1, h2]
          rw [h1, h2]
          have : 0 < (2 * f.a * x 0) ^ 2 := by positivity
          nlinarith
        · rw [h2]
          have : 0 < ((n : ℤ) * x 1) ^ 2 := by positivity
          nlinarith
      · have : 0 < 2 * f.a * x 2 ^ 2 := by positivity
        linarith
    by_contra hc
    push Not at hc
    nlinarith [mul_nonpos_of_nonneg_of_nonpos h2a.le hc, key, hR]
  obtain ⟨P, hP⟩ := exists_eq_transpose_mul hF hpos hdet
  have hdetP : P.det * P.det = 1 := by
    have := congrArg Matrix.det hP
    rw [det_mul, det_transpose, hdet] at this
    exact this.symm
  set e₁ : Fin 3 → ℤ := fun k => P k 0
  set e₂ : Fin 3 → ℤ := fun k => P k 1
  set e₃ : Fin 3 → ℤ := fun k => P k 2
  have g11 : e₁ ⬝ᵥ e₁ = 2 * f.a := by rw [← gram_of_eq hP 0 0]; rfl
  have g12 : e₁ ⬝ᵥ e₂ = f.b := by rw [← gram_of_eq hP 0 1]; rfl
  have g22 : e₂ ⬝ᵥ e₂ = 2 * f.c := by rw [← gram_of_eq hP 1 1]; rfl
  have hd3 : e₃ ⬝ᵥ cr e₁ e₂ = P.det := (det_eq_dot_cr P).symm
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hdetP with h | h
  · exact ⟨e₁, e₂, e₃, g11, g12, g22, by rw [hd3, h]⟩
  · exact ⟨e₁, e₂, -e₃, g11, g12, g22, by rw [neg_dotProduct, hd3, h]; rfl⟩

/-- The cross product of such a basis lies on the sphere `|x|² = n`. -/
theorem cr_mem_reps3 {n : ℕ} {f : Form} (hf : f ∈ Red n) {e₁ e₂ : Fin 3 → ℤ}
    (h11 : e₁ ⬝ᵥ e₁ = 2 * f.a) (h12 : e₁ ⬝ᵥ e₂ = f.b) (h22 : e₂ ⬝ᵥ e₂ = 2 * f.c) :
    cr e₁ e₂ ∈ Duke.reps3 n := by
  rw [Duke.mem_reps3, cr_sq_sum, h11, h12, h22]
  have hd := (mem_Red.mp hf).1
  unfold Form.disc at hd
  linarith

end ThreeSquares.B3
