/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Divisors
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Squarefree.Basic

/-!
# Duke–Schulze-Pillot (1990): Lemma 5(ii) (upper bound) and Theorem 3(ii)

W. Duke and R. Schulze-Pillot, *Representation of integers by positive ternary quadratic forms
and equidistribution of lattice points on ellipsoids*, Invent. Math. 99 (1990) 49–57.

`q(x) = ½ xᵗ A x` for a symmetric integer `3 × 3` matrix `A` with `q > 0` on `ℚ³ \ {0}`;
`h ∈ ℚ³`; `r(q, h, n) = #{x ∈ h + ℤ³ : q(x) = n}` (`repCount`) and, for `F ⊆ ℝ³`,
`r(q, F, h, n) = #{x ∈ h + ℤ³ : q(x) = n, x / √n ∈ F}` (`repCountF`).

* `card_divisors_le_rpow`: the divisor bound `d(n) ≤ C_ε n^ε`.
* `repCount_le`: `r(q, h, n) ≤ C_ε n^{1/2+ε}` (unconditional).
* `average_le`: the same bound for every weighted average of such counts, in particular for
  `r(spn_N q, h, n)`, the upper bound of Lemma 5(ii).
* `thm3_ii`: Theorem 3(ii), `r(q, F, h, n) = r(spn_N q, h, n) μ(F) + O(n^{1/2 − 1/175 + ε})` on
  the restricted set of `n`, **conditional** on Theorem 1 and Theorem 3(i) of the paper, which
  are hypotheses (`hThm1`, `hThm3i`); `R n` stands for `r(spn_N q, h, n)` and `μF` for `μ(F)`.
* `spn_upper`: under Theorem 3(i), `R n ≤ C_ε n^{1/2+ε}`.

The Mathlib definitions used in these statements are listed in `MATHLIB_DEFINITIONS.md` at the
root of this repository.
-/

@[expose] public section

namespace DukeSchulzePillot

open Matrix

/-- `q(x) = ½ xᵗ A x`. -/
def qform (A : Matrix (Fin 3) (Fin 3) ℤ) (x : Fin 3 → ℚ) : ℚ :=
  (1 / 2 : ℚ) * (x ⬝ᵥ (A.map (Int.cast : ℤ → ℚ)) *ᵥ x)

/-- `r(q, h, n)`: the points of `h + ℤ³` on the ellipsoid `q(x) = n`. -/
noncomputable def repCount (A : Matrix (Fin 3) (Fin 3) ℤ) (h : Fin 3 → ℚ) (n : ℕ) : ℕ :=
  Nat.card {z : Fin 3 → ℤ // qform A (h + fun i => (z i : ℚ)) = n}

/-- `r(q, F, h, n)`: the points of `h + ℤ³` on `q(x) = n` with `x / √n ∈ F`. -/
noncomputable def repCountF (A : Matrix (Fin 3) (Fin 3) ℤ) (h : Fin 3 → ℚ) (F : Set (Fin 3 → ℝ))
    (n : ℕ) : ℕ :=
  Nat.card {z : Fin 3 → ℤ // qform A (h + fun i => (z i : ℚ)) = n ∧
    (fun i => ((h i + z i : ℚ) : ℝ) / Real.sqrt n) ∈ F}

/-- **The divisor bound**: `d(n) ≤ C_ε n^ε`. -/
theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  sorry

/-- **Upper bound of Lemma 5(ii)** for one form: `r(q, h, n) ≤ C_ε n^{1/2+ε}`. -/
theorem repCount_le (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm)
    (hpos : ∀ x : Fin 3 → ℚ, x ≠ 0 → 0 < qform A x) (h : Fin 3 → ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (repCount A h n : ℝ) ≤ C * (n : ℝ) ^ (1 / 2 + ε) := by
  sorry

/-- **Upper bound of Lemma 5(ii)** for weighted averages of representation numbers, such as
`r(spn_N q, h, n)`. -/
theorem average_le {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin 3) (Fin 3) ℤ)
    (hA : ∀ i ∈ s, (A i).IsSymm) (hpos : ∀ i ∈ s, ∀ x : Fin 3 → ℚ, x ≠ 0 → 0 < qform (A i) x)
    (h : ι → Fin 3 → ℚ) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (∑ i ∈ s, w i * repCount (A i) (h i) n) / (∑ i ∈ s, w i) ≤ C * (n : ℝ) ^ (1 / 2 + ε) := by
  sorry

/-- **Theorem 3(ii)**, from Theorem 1 and Theorem 3(i) of the paper (hypotheses `hThm1`,
`hThm3i`): `r(q, F, h, n) = R(n) μ(F) + O(n^{1/2 − 1/175 + ε})` on the restricted set `S`, where
`R(n) = r(spn_N q, h, n)`. -/
theorem thm3_ii (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm)
    (hpos : ∀ x : Fin 3 → ℚ, x ≠ 0 → 0 < qform A x) (h : Fin 3 → ℚ) (F : Set (Fin 3 → ℝ))
    (μF : ℝ) (hμ0 : 0 ≤ μF) (hμ1 : μF ≤ 1) (S : Set ℕ) (R : ℕ → ℝ)
    (hThm1 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n ∈ S, 1 ≤ n →
      |(repCountF A h F n : ℝ) - repCount A h n * μF| ≤
        C * ((n : ℝ) ^ (-(1 / 175 : ℝ)) * repCount A h n + (n : ℝ) ^ (1 / 2 - 1 / 175 + ε)))
    (hThm3i : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n ∈ S, 1 ≤ n →
      |(repCount A h n : ℝ) - R n| ≤ C * (n : ℝ) ^ (1 / 2 - 1 / 28 + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n ∈ S, 1 ≤ n →
      |(repCountF A h F n : ℝ) - R n * μF| ≤ C * (n : ℝ) ^ (1 / 2 - 1 / 175 + ε) := by
  sorry

/-- Under Theorem 3(i), the main term `R(n) = r(spn_N q, h, n)` is at most `C_ε n^{1/2+ε}`. -/
theorem spn_upper (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm)
    (hpos : ∀ x : Fin 3 → ℚ, x ≠ 0 → 0 < qform A x) (h : Fin 3 → ℚ) (S : Set ℕ) (R : ℕ → ℝ)
    (hThm3i : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n ∈ S, 1 ≤ n →
      |(repCount A h n : ℝ) - R n| ≤ C * (n : ℝ) ^ (1 / 2 - 1 / 28 + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n ∈ S, 1 ≤ n → R n ≤ C * (n : ℝ) ^ (1 / 2 + ε) := by
  sorry

/-- **H1 (unconditional).** Every fixed cap contains an integral representation of every
sufficiently large squarefree integer congruent to 3 modulo 8. The cutoff is ineffective. -/
theorem squarefree_three_squares_in_caps (u : Fin 3 → ℝ)
    (hu : ∑ i, u i ^ 2 = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℕ, ∀ t : ℕ, T₀ ≤ t → Squarefree t → t % 8 = 3 →
      ∃ x : Fin 3 → ℤ, ∑ i, x i ^ 2 = (t : ℤ) ∧
        ∀ i, |(x i : ℝ) - Real.sqrt t * u i| ≤ ε * Real.sqrt t := by
  sorry

end DukeSchulzePillot
