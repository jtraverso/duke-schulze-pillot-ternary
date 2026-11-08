/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DSPLib.Main
public import ThreeSquaresLib.DukeSquarefreeProof

/-!
# Proofs of the statements in `DSPChallenge.lean`

The proofs are in `DSPLib/` (namespace `DSP`): `Divisor.lean` (the divisor bound),
`SqrtMod.lean` (square roots modulo `M`: Chinese remainder theorem and a valuation argument at
prime powers), `BinaryCount.lean` (representations by `X² + ΔY²` through square roots of `-Δ`
modulo `M`), `Ternary.lean` (completing the square twice), `Main.lean` (the shifted lattice,
weighted averages, and the deduction of Theorem 3(ii)). The definitions below are the same as
those of `DSPLib.Main`.
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
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε :=
  DSP.card_divisors_le_rpow hε

/-- **Upper bound of Lemma 5(ii)** for one form: `r(q, h, n) ≤ C_ε n^{1/2+ε}`. -/
theorem repCount_le (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm)
    (hpos : ∀ x : Fin 3 → ℚ, x ≠ 0 → 0 < qform A x) (h : Fin 3 → ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (repCount A h n : ℝ) ≤ C * (n : ℝ) ^ (1 / 2 + ε) :=
  DSP.repCount_le A hA hpos h hε

/-- **Upper bound of Lemma 5(ii)** for weighted averages of representation numbers, such as
`r(spn_N q, h, n)`. -/
theorem average_le {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin 3) (Fin 3) ℤ)
    (hA : ∀ i ∈ s, (A i).IsSymm) (hpos : ∀ i ∈ s, ∀ x : Fin 3 → ℚ, x ≠ 0 → 0 < qform (A i) x)
    (h : ι → Fin 3 → ℚ) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (∑ i ∈ s, w i * repCount (A i) (h i) n) / (∑ i ∈ s, w i) ≤ C * (n : ℝ) ^ (1 / 2 + ε) :=
  DSP.average_le s A hA hpos h w hw hε

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
      |(repCountF A h F n : ℝ) - R n * μF| ≤ C * (n : ℝ) ^ (1 / 2 - 1 / 175 + ε) :=
  DSP.thm3_ii A hA hpos h F μF hμ0 hμ1 S R hThm1 hThm3i

/-- Under Theorem 3(i), the main term `R(n) = r(spn_N q, h, n)` is at most `C_ε n^{1/2+ε}`. -/
theorem spn_upper (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm)
    (hpos : ∀ x : Fin 3 → ℚ, x ≠ 0 → 0 < qform A x) (h : Fin 3 → ℚ) (S : Set ℕ) (R : ℕ → ℝ)
    (hThm3i : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n ∈ S, 1 ≤ n →
      |(repCount A h n : ℝ) - R n| ≤ C * (n : ℝ) ^ (1 / 2 - 1 / 28 + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n ∈ S, 1 ≤ n → R n ≤ C * (n : ℝ) ^ (1 / 2 + ε) :=
  DSP.spn_upper A hA hpos h S R hThm3i

/-- **H1 (unconditional).** Every fixed cap contains an integral representation of every
sufficiently large squarefree integer congruent to 3 modulo 8. The cutoff is ineffective. -/
theorem squarefree_three_squares_in_caps (u : Fin 3 → ℝ)
    (hu : ∑ i, u i ^ 2 = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℕ, ∀ t : ℕ, T₀ ≤ t → Squarefree t → t % 8 = 3 →
      ∃ x : Fin 3 → ℤ, ∑ i, x i ^ 2 = (t : ℤ) ∧
        ∀ i, |(x i : ℝ) - Real.sqrt t * u i| ≤ ε * Real.sqrt t :=
  ThreeSquares.dukeSquarefree u hu ε hε

end DukeSchulzePillot
