/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Mult

/-!
# `κ⁴ = 1`

For `4 ∣ c`, `c > 0`, and `a` a unit mod `c`: `κ(a, c)⁴ = 1` (`kap_pow_four`), hence
`(κ(a, c)³)⁻¹ = κ(a, c)` (`kap_cube_inv`). The proof avoids the sign of the Gauss sum: squaring the
cocycle relation for `(1 0; c 1)(1 0; c' 1) = (1 0; c+c' 1)` gives `κ(1, c+c')² = κ(1, c)² κ(1, c')²`;
`κ(1, 4) = 1`; and `G(a, 0)⁴ = G(1, 0)⁴`.
-/

@[expose] public section

namespace ThreeSquares.Mult

open Complex

open scoped MatrixGroups Real

/-- The matrix `(1 0; c 1)`. -/
def lowT (c : ℤ) : SL(2, ℤ) := ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

theorem lowT_10 (c : ℤ) : (lowT c) 1 0 = c := rfl
theorem lowT_00 (c : ℤ) : (lowT c) 0 0 = 1 := rfl

theorem lowT_mul (c c' : ℤ) : lowT c * lowT c' = lowT (c + c') := by
  apply Subtype.ext
  show (!![1, 0; c, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; c', 1] = !![1, 0; c + c', 1]
  rw [Matrix.mul_fin_two]
  simp [add_comm]

theorem jm_lowT {c : ℤ} (hc : 0 < c) (z : ℂ) :
    jm (lowT c) z = kap 1 c * den (lowT c) z ^ (1 / 2 : ℂ) := by
  simp [jm, lowT, hc, den]

theorem cpow_half_sq (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  have := cpow_nat_inv_pow w (n := 2) two_ne_zero
  simpa using this

theorem kap1_sq_add {c c' : ℤ} (hc : 0 < c) (hc' : 0 < c') (h4 : (4 : ℤ) ∣ c) (h4' : (4 : ℤ) ∣ c') :
    kap 1 (c + c') ^ 2 = kap 1 c ^ 2 * kap 1 c' ^ 2 := by
  have hz : (0 : ℝ) < (I : ℂ).im := by simp
  have h := jm_mul (lowT c) (lowT c') h4 h4' hz
  rw [lowT_mul, jm_lowT (by omega), jm_lowT hc, jm_lowT hc'] at h
  have h2 := congrArg (· ^ 2) h
  simp only [mul_pow, cpow_half_sq] at h2
  have hd := den_mul (lowT c) (lowT c') hz
  rw [lowT_mul] at hd
  have hne : den (lowT (c + c')) I ≠ 0 := den_ne_zero _ hz
  rw [hd] at h2 hne
  have hne' := hne
  apply mul_right_cancel₀ hne'
  linear_combination h2

theorem kap_one_four : kap 1 4 = 1 := by
  have hG : gaussQ (1 : ZMod 4) 0 = 2 + 2 * I := by
    unfold gaussQ
    have hu : (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by decide
    have h0 : (1 * (0 : ZMod 4) ^ 2 + 0 * 0 : ZMod 4) = 0 := by decide
    have h1 : (1 * (1 : ZMod 4) ^ 2 + 0 * 1 : ZMod 4) = 1 := by decide
    have h2 : (1 * (2 : ZMod 4) ^ 2 + 0 * 2 : ZMod 4) = 0 := by decide
    have h3 : (1 * (3 : ZMod 4) ^ 2 + 0 * 3 : ZMod 4) = 1 := by decide
    have hI : (ZMod.stdAddChar (N := 4) 1 : ℂ) = I := by
      rw [ZMod.stdAddChar_apply, show (1 : ZMod 4) = ((1 : ℕ) : ZMod 4) by simp,
        ZMod.toCircle_natCast]
      rw [show 2 * (π : ℂ) * I * ((1 : ℕ) : ℂ) / ((4 : ℕ) : ℂ) = π / 2 * I by push_cast; ring]
      exact Complex.exp_pi_div_two_mul_I
    rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton, h0, h1, h2, h3,
      AddChar.map_zero_eq_one, hI]
    ring
  have h4 : (0 : ℤ) < 4 := by norm_num
  rw [kap, dif_pos h4]
  show gaussQ ((1 : ℤ) : ZMod 4) 0 / ((1 + I) * (Real.sqrt ((4 : ℕ) : ℝ) : ℂ)) = 1
  rw [Int.cast_one, hG, show Real.sqrt ((4 : ℕ) : ℝ) = 2 by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  have : (1 + I) ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this
  field_simp
  push_cast
  ring

theorem kap1_sq_four_mul : ∀ m : ℕ, 1 ≤ m → kap 1 (4 * m) ^ 2 = 1
  | 0, h => absurd h (by norm_num)
  | 1, _ => by norm_num [kap_one_four]
  | m + 2, _ => by
    have ih := kap1_sq_four_mul (m + 1) (by omega)
    rw [show (4 : ℤ) * ((m + 2 : ℕ) : ℤ) = 4 * ((m + 1 : ℕ) : ℤ) + 4 by push_cast; ring,
      kap1_sq_add (by positivity) (by norm_num) (dvd_mul_right _ _) dvd_rfl, ih, kap_one_four]
    norm_num

theorem kap1_sq {c : ℤ} (hc : 0 < c) (h4 : (4 : ℤ) ∣ c) : kap 1 c ^ 2 = 1 := by
  obtain ⟨m, rfl⟩ := h4
  lift m to ℕ using (by omega)
  have := kap1_sq_four_mul m (by omega)
  simpa using this

/-- **`κ(a, c)⁴ = 1`.** -/
theorem kap_pow_four {a c : ℤ} (hc : 0 < c) (h4 : (4 : ℤ) ∣ c) (hu : ∃ d : ℤ, a * d ≡ 1 [ZMOD c]) :
    kap a c ^ 4 = 1 := by
  have h1 : kap a c ^ 4 = kap 1 c ^ 4 := by
    haveI : NeZero c.toNat := ⟨by omega⟩
    simp only [kap, dif_pos hc]
    rw [div_pow, div_pow, Int.cast_one]
    congr 1
    apply gaussQ_pow_four_eq
    obtain ⟨d, hd⟩ := hu
    refine IsUnit.of_mul_eq_one (d : ZMod c.toNat) ?_
    have hc' : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hc.le
    have : ((a * d : ℤ) : ZMod c.toNat) = ((1 : ℤ) : ZMod c.toNat) := by
      rw [ZMod.intCast_eq_intCast_iff, hc']; exact hd
    push_cast at this; exact this
  rw [h1, show kap 1 c ^ 4 = (kap 1 c ^ 2) ^ 2 by ring, kap1_sq hc h4, one_pow]

theorem kap_cube_inv {a c : ℤ} (hc : 0 < c) (h4 : (4 : ℤ) ∣ c) (hu : ∃ d : ℤ, a * d ≡ 1 [ZMOD c]) :
    (kap a c ^ 3)⁻¹ = kap a c := by
  have h := kap_pow_four hc h4 hu
  have hne : kap a c ^ 3 ≠ 0 := by
    intro h0; rw [show kap a c ^ 4 = kap a c ^ 3 * kap a c by ring, h0, zero_mul] at h
    exact zero_ne_one h
  exact inv_eq_of_mul_eq_one_right (by rw [← h]; ring)

end ThreeSquares.Mult
