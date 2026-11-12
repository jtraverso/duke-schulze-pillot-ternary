# Duke–Schulze-Pillot bounds and squarefree three squares in fixed caps (H1)

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization around W. Duke and R. Schulze-Pillot, *Representation of
integers by positive ternary quadratic forms and equidistribution of lattice points on
ellipsoids*, Invent. Math. 99 (1990) 49–57
([doi:10.1007/BF01234411](https://doi.org/10.1007/BF01234411)).

## H1: the new unconditional cap theorem

For every unit direction `u : Fin 3 → ℝ` and every `ε > 0`, all sufficiently
large **squarefree** `t ≡ 3 (mod 8)` admit `x : Fin 3 → ℤ` with
`∑ i, x i ^ 2 = t` and `|xᵢ − √t uᵢ| ≤ ε √t` for all three coordinates.
The public declaration is `DukeSchulzePillot.squarefree_three_squares_in_caps`.
Its proof is `ThreeSquares.dukeSquarefree`; all analytic inputs are proved.
The threshold is ineffective because the argument uses Siegel's theorem.

The five original declarations below are retained. This does **not** prove the
general Duke–Schulze-Pillot theorem unconditionally, remove the hypotheses from
`thm3_ii`, or assert the sharp `1/175` rate. The H1 proof lives in `DukeH1/`; see
[the submission scope](docs/h1-v2/SCOPE.md).

Registered code is reused only as lake dependencies (nothing is copied):

| Dependency | Palomar entry | Used for |
|---|---|---|
| [jtraverso/siegel-theorem](https://github.com/jtraverso/siegel-theorem) @ dbe9353 | PALOMAR-2026-11-12-000005 | Siegel's theorem, integral representation of `L(s, χ)` |
| [charliedorsey/weil-bounds-toolkit](https://github.com/charliedorsey/weil-bounds-toolkit) @ 0f3e4c3 | PALOMAR-2026-11-03-000018 | Weil bounds for Kloosterman sums |
| [jtraverso/three-squares-gauss-legendre](https://github.com/jtraverso/three-squares-gauss-legendre) @ 783ec66 | PALOMAR-2026-11-07-000011 | Gauss–Legendre, unimodular lattices |
| [jtraverso/four-squares-in-caps](https://github.com/jtraverso/four-squares-in-caps) @ a1fcaaf | PALOMAR-2026-11-08-000002 | Gauss and Kloosterman sums, theta functions |

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
| `squarefree_three_squares_in_caps` | every fixed cap contains representations of all large squarefree `t ≡ 3 (mod 8)` | unconditional; ineffective cutoff |

In `thm3_ii`, `R` stands for `r(spn_N q, h, n)`, `μF ∈ [0, 1]` for `μ(F)`, and `S` for the
restricted set of `n`; the hypotheses are exactly the estimates of Theorem 1 and Theorem 3(i).

## What is not claimed

The general ternary-form Theorems 1, 2 and 3(i), spinor genera, and the lower
bound for arbitrary spinor-genus averages are not proved here. The older general
Theorem 3(ii) remains conditional on `hThm1` and `hThm3i`. H1 supplies a separate,
unconditional fixed-cap result on the three-square sphere, with verified
sphere-specific harmonic estimates and a verified Siegel input. It does not
assert a sharp quantitative rate or an effective numerical cutoff.

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

## H1 assembly and provenance

`DegreewiseWeyl` fixes a cap degree before choosing a finite minimum of positive
Weyl savings. `IsoDegreewiseWeyl` combines the even-degree estimate with exact
antipodal cancellation in odd degrees. `B3_SchiLimit`, `B3_GoodClasses`,
`B3_GoodLimit` and `B3_RepresentationLower` compare character-sum averages with
binary-form counts and derive the lower bound needed by the cap argument.
`B3_VerifiedInputs` supplies the actual Siegel and integral-representation proofs.
`DukeSquarefreeProof` assembles these into H1.

The underlying source audit and assembly were developed with Codex under the
author's direction. Imported source licenses and attributions are preserved.
`UPSTREAM_AXIOMS.log` is historical evidence for the larger upstream assembly;
this submission selects only H1, and its own six declarations are checked
separately. The registered Gauss–Legendre repository is unchanged.
