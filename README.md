# Duke–Schulze-Pillot: Lemma 5(ii) (upper bound) and a conditional Theorem 3(ii) in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization around W. Duke and R. Schulze-Pillot, *Representation of
integers by positive ternary quadratic forms and equidistribution of lattice points on
ellipsoids*, Invent. Math. 99 (1990) 49–57
([doi:10.1007/BF01234411](https://doi.org/10.1007/BF01234411)).

## Setting

`q(x) = ½ xᵗ A x` for a symmetric integer `3 × 3` matrix `A` with `q > 0` on `ℚ³ \ {0}`; `h ∈ ℚ³`;
`r(q, h, n) = #{x ∈ h + ℤ³ : q(x) = n}` (`repCount`) and, for `F ⊆ ℝ³`,
`r(q, F, h, n) = #{x ∈ h + ℤ³ : q(x) = n, x / √n ∈ F}` (`repCountF`).

## Statements (`DSPChallenge.lean`, namespace `DukeSchulzePillot`)

| Lean | Statement | Status |
|---|---|---|
| `card_divisors_le_rpow` | `d(n) ≤ C_ε n^ε` | unconditional |
| `repCount_le` | `r(q, h, n) ≤ C_ε n^{1/2+ε}` | unconditional |
| `average_le` | the same bound for every nonnegatively weighted average of representation numbers, in particular `r(spn_N q, h, n)`: the **upper bound of Lemma 5(ii)** | unconditional |
| `thm3_ii` | **Theorem 3(ii)**: `r(q, F, h, n) = R(n) μ(F) + O(n^{1/2 − 1/175 + ε})` on `S` | conditional on `hThm1` (Theorem 1 of the paper) and `hThm3i` (Theorem 3(i)) |
| `spn_upper` | `R(n) ≤ C_ε n^{1/2+ε}` | conditional on `hThm3i` |

In `thm3_ii`, `R` stands for `r(spn_N q, h, n)`, `μF ∈ [0, 1]` for `μ(F)`, and `S` for the
restricted set of `n`; the hypotheses are exactly the estimates of Theorem 1 and Theorem 3(i).

## What is not formalized

Theorem 1 (Iwaniec's bound for Fourier coefficients of half-integral weight cusp forms, the
Shimura correspondence, Deligne's bound, harmonic polynomials of Golubeva–Fomenko), Theorems 2 and
3(i) (Siegel and spinor mass formulas), Lemmas 1–4, the lower bound `n^{1/2−ε} ≪ r(spn_N q, h, n)`
of Lemma 5(ii) (Siegel's ineffective bound for `L(1, χ)`), the Corollary, and spinor genera. None
of these is available in Mathlib.

## Proof of the upper bound (elementary, not the paper's)

1. `Divisor.lean`: `d(n)/n^ε` is multiplicative and bounded at prime powers.
2. `SqrtMod.lean`: the number of square roots of `c ≠ 0` modulo `M` is at most `(2|c|)^{|c|+2} d(M)`
   (Chinese remainder theorem; at most two roots modulo odd prime powers not dividing `c`, at
   most `4|c|` otherwise, by a valuation argument).
3. `BinaryCount.lean`: a primitive solution of `X² + ΔY² = M` gives the root `X Y⁻¹` of `−Δ`
   modulo `M`, with fibres of size at most four (`(X₀² + ΔY₀²)(X² + ΔY²) = (X₀X + ΔY₀Y)² +
   Δ(X₀Y − XY₀)²`); all solutions are primitive solutions scaled by `g` with `g² ∣ M`. Hence
   `#{X² + ΔY² = M} ≪ M^ε`.
4. `Ternary.lean`: completing the square twice,
   `a b₁₁ Q(y) = b₁₁ z² + X² + Δ y₂²`, so the solutions of `Q(y) = N` inject into pairs
   `(z, (X, y₂))` with `|z| ≤ √(aN)` and `X² + Δ y₂² = b₁₁(aN − z²)`: `≪ N^{1/2+ε}`.
5. `Main.lean`: the shift `h + ℤ³` (common denominator), weighted averages, and the deduction of
   Theorem 3(ii) from the two hypotheses, as in the paper.

## Checking

```
lake build DSPChallenge DSPSolution
```

`DSPChallenge.lean` states the results (with `sorry`) using only Mathlib; `DSPSolution.lean`
imports the proofs. `comparator.json` lists the compared theorems and definitions;
`MATHLIB_DEFINITIONS.md` excerpts the Mathlib definitions used in the statements.

## AI disclosure

The Lean development was written by an AI agent (Claude Opus 5.5 in Claude Code) under the
author's direction, and mechanically verified (no `sorry`; axioms `propext`, `Classical.choice`,
`Quot.sound`). The formalization is by a different author than the article; its authors were not
involved.
