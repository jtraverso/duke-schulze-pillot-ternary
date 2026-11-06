# Mathlib definitions used in DSPChallenge.lean

Verbatim excerpts of the Mathlib definitions used by the statements in `DSPChallenge.lean`, at the
pinned Mathlib revision `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`, repository
https://github.com/leanprover-community/mathlib4). Mathlib is released under the Apache-2.0
licence. Each excerpt gives the file and line at that revision; the complete source is at
`https://github.com/leanprover-community/mathlib4/blob/c55e6e786f49471c72fbddbec5415808896aec1e/<file>`.

These excerpts are provided so that the meaning of every imported notion used by the
Challenge can be audited without fetching Mathlib. The notation `∑ x ∈ s, f x` is `Finset.sum s f`.

## Matrix

`Mathlib/LinearAlgebra/Matrix/Defs.lean`, line 54:

```lean
/-- `Matrix m n R` is the type of matrices with entries in `R`, whose rows are indexed by `m`
and whose columns are indexed by `n`. -/
@[wikidata Q44337]
def Matrix (m : Type u) (n : Type u') (α : Type v) : Type max u u' v :=
  m → n → α
```

## Matrix.map

`Mathlib/LinearAlgebra/Matrix/Defs.lean`, line 125:

```lean
/-- `M.map f` is the matrix obtained by applying `f` to each entry of the matrix `M`.

This is available in bundled forms as:
* `AddMonoidHom.mapMatrix`
* `LinearMap.mapMatrix`
* `LinearMap.mapMatrixLinear`
* `RingHom.mapMatrix`
* `AlgHom.mapMatrix`
* `Equiv.mapMatrix`
* `AddEquiv.mapMatrix`
* `LinearEquiv.mapMatrix`
* `RingEquiv.mapMatrix`
* `AlgEquiv.mapMatrix`
-/
def map (M : Matrix m n α) (f : α → β) : Matrix m n β :=
  of fun i j => f (M i j)
```

## Matrix.IsSymm

`Mathlib/LinearAlgebra/Matrix/Symmetric.lean`, line 33:

```lean
/-- A matrix `A : Matrix n n α` is "symmetric" if `Aᵀ = A`. -/
@[wikidata Q339011]
def IsSymm (A : Matrix n n α) : Prop :=
  Aᵀ = A
```

## dotProduct (notation `⬝ᵥ`)

`Mathlib/Data/Matrix/Mul.lean`, line 69:

```lean
/-- `dotProduct v w` is the sum of the entrywise products `v i * w i`.

This is available in bundled forms as:
* `dotProductBilin`
* `dotProductEquiv`
-/
def dotProduct [Mul α] [AddCommMonoid α] (v w : m → α) : α :=
  ∑ i, v i * w i
```

## Matrix.mulVec (notation `*ᵥ`)

`Mathlib/Data/Matrix/Mul.lean`, line 701:

```lean
/--
`M *ᵥ v` (notation for `mulVec M v`) is the matrix-vector product of matrix `M` and vector `v`,
where `v` is seen as a column vector.

The notation has precedence 73, which comes immediately before ` ⬝ᵥ ` for `dotProduct`,
so that `A *ᵥ v ⬝ᵥ B *ᵥ w` is parsed as `(A *ᵥ v) ⬝ᵥ (B *ᵥ w)`.

This is available in bundled forms as:
* `Matrix.mulVec.addMonoidHomLeft`
* `Matrix.mulVecLin`
* `Matrix.mulVecBilin`
-/
def mulVec [Fintype n] (M : Matrix m n α) (v : n → α) : m → α
  | i => (fun j => M i j) ⬝ᵥ v
```

## Nat.card

`Mathlib/SetTheory/Cardinal/Finite.lean`, line 39:

```lean
/-- `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`. -/
protected def card (α : Type*) : ℕ :=
  toNat (mk α)
```

## Nat.divisors

`Mathlib/NumberTheory/Divisors.lean`, line 51:

```lean
/-- `divisors n` is the `Finset` of divisors of `n`. By convention, we set `divisors 0 = ∅`. -/
def divisors : Finset ℕ := {d ∈ Ico 1 (n + 1) | d ∣ n}
```

## Real.sqrt

`Mathlib/Analysis/Real/Sqrt.lean`, line 109:

```lean
/-- The square root of a real number. This returns 0 for negative inputs.

This has notation `√x`. Note that `√x⁻¹` is parsed as `√(x⁻¹)`. -/
@[irreducible] noncomputable def sqrt (x : ℝ) : ℝ :=
  NNReal.sqrt (Real.toNNReal x)
```

## Real.rpow (notation `x ^ y` for real `y`)

`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`, line 31:

```lean
/-- The real power function `x ^ y`, defined as the real part of the complex power function.
For `x > 0`, it is equal to `exp (y log x)`. For `x = 0`, one sets `0 ^ 0=1` and `0 ^ y=0` for
`y ≠ 0`. For `x < 0`, the definition is somewhat arbitrary as it depends on the choice of a complex
determination of the logarithm. With our conventions, it is equal to `exp (y log x) cos (π y)`. -/
noncomputable def rpow (x y : ℝ) :=
  ((x : ℂ) ^ (y : ℂ)).re
```
