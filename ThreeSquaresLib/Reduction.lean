/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Main
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Squarefree

/-!
# Reduction of the dense three squares statement

`ThreeSquaresDense`: for every unit vector `u` and `ε > 0`, every large `n ≡ 3 (mod 8)` has a
representation `x` with `|xᵢ − √n uᵢ| ≤ ε √n`. Write `n = t m²` with `t` squarefree; then `m` is odd
and `t ≡ 3 (mod 8)`.

* If `t` is large, a representation of `t` near `u` (`DukeSquarefree`, Duke's theorem for squarefree
  `t`) scaled by `m` works.
* If `t` is bounded, take any representation `x₀` of `t` (Gauss–Legendre) and rotate it by a
  quaternion `β` of norm `m`: `rot β x₀` has norm `t m²`, and its direction is near `u` for some `β`
  when `m` is large (`QuaternionRotationsDense`).

`threeSquaresDense_of`: `DukeSquarefree → QuaternionRotationsDense → ThreeSquaresDense`.
-/

@[expose] public section

namespace ThreeSquares

open Matrix

/-- `x` is within `ε √n` of `√n u` in every coordinate. -/
def Near (u : Fin 3 → ℝ) (ε : ℝ) (n : ℕ) (x : Fin 3 → ℤ) : Prop :=
  ∀ i, |(x i : ℝ) - Real.sqrt n * u i| ≤ ε * Real.sqrt n

/-- Every large `n ≡ 3 (mod 8)` has a representation as a sum of three squares near any
direction (the input needed by CDR Paper III). -/
def ThreeSquaresDense : Prop :=
  ∀ u : Fin 3 → ℝ, ∑ i, u i ^ 2 = 1 → ∀ ε > 0, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → n % 8 = 3 →
    ∃ x : Fin 3 → ℤ, ∑ i, x i ^ 2 = (n : ℤ) ∧ Near u ε n x

/-- **Hypothesis (Duke's theorem for squarefree `t`).** -/
def DukeSquarefree : Prop :=
  ∀ u : Fin 3 → ℝ, ∑ i, u i ^ 2 = 1 → ∀ ε > 0, ∃ T₀ : ℕ, ∀ t : ℕ, T₀ ≤ t → Squarefree t →
    t % 8 = 3 → ∃ x : Fin 3 → ℤ, ∑ i, x i ^ 2 = (t : ℤ) ∧ Near u ε t x

/-- The rotation matrix of the quaternion `a + b i + c j + d k`, multiplied by its norm. -/
def rot (β : Fin 4 → ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![β 0 ^ 2 + β 1 ^ 2 - β 2 ^ 2 - β 3 ^ 2, 2 * (β 1 * β 2 - β 0 * β 3),
      2 * (β 1 * β 3 + β 0 * β 2);
    2 * (β 1 * β 2 + β 0 * β 3), β 0 ^ 2 - β 1 ^ 2 + β 2 ^ 2 - β 3 ^ 2,
      2 * (β 2 * β 3 - β 0 * β 1);
    2 * (β 1 * β 3 - β 0 * β 2), 2 * (β 2 * β 3 + β 0 * β 1),
      β 0 ^ 2 - β 1 ^ 2 - β 2 ^ 2 + β 3 ^ 2]

/-- **Hypothesis (equidistribution of quaternion rotations).** For unit vectors `y, u` and
`ε > 0`, every large odd `m` is the norm of a quaternion `β` whose rotation takes `y` within `ε` of
`u`. -/
def QuaternionRotationsDense : Prop :=
  ∀ y u : Fin 3 → ℝ, ∑ i, y i ^ 2 = 1 → ∑ i, u i ^ 2 = 1 → ∀ ε > 0, ∃ M₀ : ℕ, ∀ m : ℕ,
    M₀ ≤ m → Odd m → ∃ β : Fin 4 → ℤ, ∑ i, β i ^ 2 = (m : ℤ) ∧
      ∀ i, |((rot β).map (Int.cast : ℤ → ℝ) *ᵥ y) i / m - u i| ≤ ε

/-- The rotation multiplies norms by the square of the norm of the quaternion. -/
theorem sum_sq_rot_mulVec (β : Fin 4 → ℤ) (x : Fin 3 → ℤ) :
    ∑ i, (rot β *ᵥ x) i ^ 2 = (∑ i, β i ^ 2) ^ 2 * ∑ i, x i ^ 2 := by
  simp [rot, mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

theorem odd_and_mod_of_sq_mul {n t m : ℕ} (hn : n % 8 = 3) (h : m ^ 2 * t = n) :
    Odd m ∧ t % 8 = 3 := by
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exfalso
    have : n = 4 * (k * k * t) := by rw [← h]; ring
    omega
  · refine ⟨⟨k, rfl⟩, ?_⟩
    obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
    have : n = 8 * (j * t) + t := by
      rw [← h]
      have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
      rw [this, hj]
      ring
    omega

set_option maxHeartbeats 4000000 in
-- the case analysis and the estimates exceed the default heartbeat budget
/-- **The reduction.** -/
theorem threeSquaresDense_of (h1 : DukeSquarefree) (h2 : QuaternionRotationsDense) :
    ThreeSquaresDense := by
  classical
  intro u hu ε hε
  obtain ⟨T₀, hT₀⟩ := h1 u hu ε hε
  -- a representation of every small `t ≡ 3 (mod 8)`
  have hrep : ∀ t : ℕ, ∃ x₀ : Fin 3 → ℤ, t % 8 = 3 → ∑ i, x₀ i ^ 2 = (t : ℤ) := by
    intro t
    by_cases ht : t % 8 = 3
    · obtain ⟨x₀, hx₀⟩ := exists_sum_sq_of_mod_eight_eq_three t ht
      exact ⟨x₀, fun _ => hx₀⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose x₀ hx₀ using hrep
  let y : ℕ → Fin 3 → ℝ := fun t i => (x₀ t i : ℝ) / Real.sqrt t
  have hy : ∀ t, t % 8 = 3 → ∑ i, y t i ^ 2 = 1 := by
    intro t ht
    have htpos : (0 : ℝ) < t := by have : 0 < t := by omega
                                   exact_mod_cast this
    have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt htpos.le
    have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr htpos).ne'
    have hsum : ∑ i, (x₀ t i : ℝ) ^ 2 = t := by exact_mod_cast hx₀ t ht
    simp only [y, div_pow, ← Finset.sum_div, hsum, hs]
    exact div_self htpos.ne'
  have hM : ∀ t, ∃ M : ℕ, t % 8 = 3 → ∀ m : ℕ, M ≤ m → Odd m → ∃ β : Fin 4 → ℤ,
      ∑ i, β i ^ 2 = (m : ℤ) ∧
        ∀ i, |((rot β).map (Int.cast : ℤ → ℝ) *ᵥ y t) i / m - u i| ≤ ε := by
    intro t
    by_cases ht : t % 8 = 3
    · obtain ⟨M, hM⟩ := h2 (y t) u (hy t ht) hu ε hε
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose M hMspec using hM
  set Mmax := (Finset.range T₀).sup M with hMmax
  refine ⟨T₀ * (Mmax + 1) ^ 2 + 1, fun n hn hn8 => ?_⟩
  obtain ⟨m, t, hmt, hsq⟩ := exists_sq_mul_squarefree n
  obtain ⟨hm_odd, ht8⟩ := odd_and_mod_of_sq_mul hn8 hmt
  have hm0 : 0 < m := hm_odd.pos
  have htpos : 0 < t := by omega
  have hsqrt : Real.sqrt n = m * Real.sqrt t := by
    rw [← hmt]
    push_cast
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  by_cases hT : T₀ ≤ t
  · -- large squarefree part: scale a representation of `t`
    obtain ⟨z, hz, hzn⟩ := hT₀ t hT hsq ht8
    refine ⟨fun i => (m : ℤ) * z i, ?_, ?_⟩
    · have : ∑ i, ((m : ℤ) * z i) ^ 2 = (m : ℤ) ^ 2 * ∑ i, z i ^ 2 := by
        simp only [mul_pow, Finset.mul_sum]
      rw [this, hz, ← hmt]
      push_cast
      ring
    · intro i
      have h := hzn i
      have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
      rw [hsqrt]
      push_cast
      have : (m : ℝ) * z i - m * Real.sqrt t * u i = m * (z i - Real.sqrt t * u i) := by ring
      rw [this, abs_mul, abs_of_pos hm0']
      calc (m : ℝ) * |(z i : ℝ) - Real.sqrt t * u i| ≤ m * (ε * Real.sqrt t) :=
            mul_le_mul_of_nonneg_left h hm0'.le
        _ = ε * (m * Real.sqrt t) := by ring
  · -- bounded squarefree part: rotate a representation of `t`
    push Not at hT
    have hMt : M t ≤ Mmax := Finset.le_sup (Finset.mem_range.mpr hT)
    have hmbig : M t ≤ m := by
      by_contra hlt
      push Not at hlt
      have h1 : m ≤ Mmax := by omega
      have h2' : m ^ 2 * t ≤ (Mmax + 1) ^ 2 * T₀ :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) hT.le
      have : n ≤ T₀ * (Mmax + 1) ^ 2 := by rw [← hmt]; linarith
      omega
    obtain ⟨β, hβ, hβu⟩ := hMspec t ht8 m hmbig hm_odd
    refine ⟨rot β *ᵥ x₀ t, ?_, ?_⟩
    · rw [sum_sq_rot_mulVec, hβ, hx₀ t ht8, ← hmt]
      push_cast
      ring
    · intro i
      have h := hβu i
      have hm0' : (0 : ℝ) < m := by exact_mod_cast hm0
      have htpos' : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr (by exact_mod_cast htpos)
      -- `rot β x₀ = √t · rot β y`
      have hrot : ((rot β *ᵥ x₀ t) i : ℝ) =
          Real.sqrt t * ((rot β).map (Int.cast : ℤ → ℝ) *ᵥ y t) i := by
        simp only [mulVec, dotProduct, Fin.sum_univ_three, map_apply, y]
        push_cast
        field_simp
      rw [hrot, hsqrt]
      have : Real.sqrt t * ((rot β).map (Int.cast : ℤ → ℝ) *ᵥ y t) i - m * Real.sqrt t * u i =
          (m * Real.sqrt t) * (((rot β).map (Int.cast : ℤ → ℝ) *ᵥ y t) i / m - u i) := by
        field_simp
      rw [this, abs_mul, abs_of_pos (by positivity)]
      calc (m * Real.sqrt t) * |((rot β).map (Int.cast : ℤ → ℝ) *ᵥ y t) i / m - u i| ≤
          (m * Real.sqrt t) * ε := mul_le_mul_of_nonneg_left h (by positivity)
        _ = ε * (m * Real.sqrt t) := by ring

end ThreeSquares
