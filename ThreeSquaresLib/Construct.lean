/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Unimodular

/-!
# A unimodular form representing `n`

`sum_three_sq_of_dvd`: if `a ≥ 1`, `d = a n − 1 > 0` and `d ∣ 1 + n b²`, then with
`c = (1 + n b²) / d` the matrix `[[a, b, 1], [b, c, 0], [1, 0, n]]` is positive definite of
determinant `1` (`a d q(x, y, z) = d (a x + b y + z)² + a y² + (b y − d z)²`), so its diagonal entry
`n` is a sum of three squares (`sum_three_sq_of_unimodular`).
-/

@[expose] public section

namespace ThreeSquares

open Matrix

set_option maxHeartbeats 4000000 in
-- the positivity argument for the explicit matrix exceeds the default heartbeat budget
theorem sum_three_sq_of_dvd (n : ℕ) {a b : ℤ} (ha : 0 < a) (hd : 0 < a * n - 1)
    (hdvd : a * n - 1 ∣ 1 + n * b ^ 2) : ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  obtain ⟨c, hc⟩ := hdvd
  let A : Matrix (Fin 3) (Fin 3) ℤ := !![a, b, 1; b, c, 0; 1, 0, (n : ℤ)]
  have hA : Aᵀ = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hdet : A.det = 1 := by
    simp [A, det_fin_three]
    linear_combination -hc
  have hpos : ∀ x : Fin 3 → ℤ, x ≠ 0 → 0 < qf A x := by
    intro x hx
    rw [qf_expand hA]
    simp only [A, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
      cons_val_fin_one]
    set d := a * n - 1 with hd_def
    have key : a * d * (a * x 0 ^ 2 + c * x 1 ^ 2 + (n : ℤ) * x 2 ^ 2 + 2 * b * x 0 * x 1 +
        2 * 1 * x 0 * x 2 + 2 * 0 * x 1 * x 2) =
        d * (a * x 0 + b * x 1 + x 2) ^ 2 + a * x 1 ^ 2 + (b * x 1 - d * x 2) ^ 2 := by
      rw [hd_def] at hc ⊢
      linear_combination (-(a * x 1 ^ 2)) * hc
    by_contra hQ
    push Not at hQ
    have had : 0 < a * d := mul_pos ha hd
    have hS : d * (a * x 0 + b * x 1 + x 2) ^ 2 + a * x 1 ^ 2 + (b * x 1 - d * x 2) ^ 2 ≤ 0 := by
      rw [← key]
      exact mul_nonpos_of_nonneg_of_nonpos had.le hQ
    have t1 : 0 ≤ d * (a * x 0 + b * x 1 + x 2) ^ 2 := by positivity
    have t2 : 0 ≤ a * x 1 ^ 2 := by positivity
    have t3 : 0 ≤ (b * x 1 - d * x 2) ^ 2 := by positivity
    have e2 : a * x 1 ^ 2 = 0 := by linarith
    have e3 : (b * x 1 - d * x 2) ^ 2 = 0 := by linarith
    have e1 : d * (a * x 0 + b * x 1 + x 2) ^ 2 = 0 := by linarith
    have hx1 : x 1 = 0 := by
      rcases mul_eq_zero.mp e2 with h | h
      · exact absurd h ha.ne'
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    have hx2 : x 2 = 0 := by
      have h := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e3
      rw [hx1, mul_zero, zero_sub, neg_eq_zero] at h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hd.ne'
      · exact h
    have hx0 : x 0 = 0 := by
      rcases mul_eq_zero.mp e1 with h | h
      · exact absurd h hd.ne'
      · have h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
        rw [hx1, hx2, mul_zero, add_zero, add_zero] at h'
        rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' ha.ne'
        · exact h''
    apply hx
    ext i
    fin_cases i
    · exact hx0
    · exact hx1
    · exact hx2
  obtain ⟨x, y, z, hxyz⟩ := sum_three_sq_of_unimodular hA hpos hdet 2
  exact ⟨x, y, z, by rw [hxyz]; rfl⟩

end ThreeSquares
