/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The two analytic inputs of B3, as hypotheses

Both are theorems of the lake dependency `jtraverso/siegel-theorem` @ `dbe9353` (namespace
`SiegelThm`; Siegel's theorem by Goldfeld's argument, Mathlib only). They are stated here as
hypotheses so that B3 can be developed independently of the dependency; `B3_VerifiedInputs.lean`
discharges them: `SiegelHyp` is `SiegelThm.siegel` and `LOneIntegralHyp` is
`SiegelThm.LFunction_eq_integral`.

* `SiegelHyp` (Siegel's theorem): `‖L(1, χ)‖ ≥ c(ε) N^{−ε}` for every real
  non-principal Dirichlet character `χ` mod `N`.
* `LOneIntegralHyp`: `L(s, χ) = s ∫_1^∞ A(t) t^{−s−1} dt` for `Re s > 0`, `χ`
  non-principal, `A(t) = ∑_{1 ≤ k ≤ t} χ(k)`.
-/

@[expose] public section

namespace ThreeSquares.B3

/-- Siegel's theorem (statement of `SiegelThm.siegel`). -/
def SiegelHyp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
      c * (N : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖

/-- The integral representation of `L(s, χ)` on `Re s > 0` (statement of
`SiegelThm.LFunction_eq_integral`). -/
def LOneIntegralHyp : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ s : ℂ, 0 < s.re →
    DirichletCharacter.LFunction χ s =
      s * ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k) * (t : ℂ) ^ (-(s + 1))

end ThreeSquares.B3
