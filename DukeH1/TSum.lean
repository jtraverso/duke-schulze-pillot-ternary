/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import FourSquaresCaps.Twisted
public import DukeH1.PrimeT

/-!
# The exponential sum `T_q(u, n)` and its twisted multiplicativity

`T_q(u, n) = ∑_{d ∈ (ℤ/q)ˣ} ∑_{x mod q} e_q(u (d⁻¹(x² + n) + n d))`.
* `Tq_mul`: for coprime `r, s` with `s' s + r' r = 1`, `T_{rs}(U, N) = T_r(s'U, N) · T_s(r'U, N)`;
* `Tq_prime`: `T_p(u, n) = χ(−n) p (e_p(2un) + e_p(−2un))` for odd primes `p ∤ un`.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open ZMod Finset

/-- `T_q(u, n)`. -/
noncomputable def Tq (q : ℕ) [NeZero q] (u n : ZMod q) : ℂ :=
  ∑ d : (ZMod q)ˣ, ∑ x : ZMod q,
    (stdAddChar (u * (((d⁻¹ : (ZMod q)ˣ) : ZMod q) * (x ^ 2 + n) + n * (d : ZMod q))) : ℂ)

/-- **Twisted multiplicativity of `T`.** -/
theorem Tq_mul {r s : ℕ} [NeZero r] [NeZero s] (h : r.Coprime s) (r' s' : ℤ)
    (hb : s' * s + r' * r = 1) (U N : ℤ) :
    Tq (r * s) (U : ZMod (r * s)) (N : ZMod (r * s)) =
      Tq r ((s' * U : ℤ) : ZMod r) (N : ZMod r) * Tq s ((r' * U : ℤ) : ZMod s) (N : ZMod s) := by
  classical
  set e := ZMod.chineseRemainder h
  let φ₁ : ZMod (r * s) →+* ZMod r := (RingHom.fst _ _).comp e.toRingHom
  let φ₂ : ZMod (r * s) →+* ZMod s := (RingHom.snd _ _).comp e.toRingHom
  have hφ₁ : ∀ y : ZMod (r * s), φ₁ y = ((y.val : ℕ) : ZMod r) := by
    intro y
    conv_lhs => rw [← ZMod.natCast_zmod_val y]
    rw [map_natCast]
  have hφ₂ : ∀ y : ZMod (r * s), φ₂ y = ((y.val : ℕ) : ZMod s) := by
    intro y
    conv_lhs => rw [← ZMod.natCast_zmod_val y]
    rw [map_natCast]
  have hsplit : ∀ y : ZMod (r * s), (stdAddChar y : ℂ) =
      stdAddChar ((s' : ZMod r) * φ₁ y) * stdAddChar ((r' : ZMod s) * φ₂ y) := by
    intro y
    have hy : y = ((y.val : ℤ) : ZMod (r * s)) := by simp
    rw [hφ₁, hφ₂]
    conv_lhs => rw [hy]
    rw [stdAddChar_mul_split r' s' hb]
    push_cast
    ring_nf
  let EU : (ZMod (r * s))ˣ ≃* (ZMod r)ˣ × (ZMod s)ˣ :=
    (Units.mapEquiv e.toMulEquiv).trans MulEquiv.prodUnits
  let EX : ZMod (r * s) ≃ ZMod r × ZMod s := e.toEquiv
  let g₁ : (ZMod r)ˣ → ZMod r → ℂ := fun a x =>
    stdAddChar (((s' * U : ℤ) : ZMod r) * (((a⁻¹ : (ZMod r)ˣ) : ZMod r) * (x ^ 2 + (N : ZMod r)) +
      (N : ZMod r) * (a : ZMod r)))
  let g₂ : (ZMod s)ˣ → ZMod s → ℂ := fun a x =>
    stdAddChar (((r' * U : ℤ) : ZMod s) * (((a⁻¹ : (ZMod s)ˣ) : ZMod s) * (x ^ 2 + (N : ZMod s)) +
      (N : ZMod s) * (a : ZMod s)))
  have hterm : ∀ (a : (ZMod (r * s))ˣ) (x : ZMod (r * s)),
      (stdAddChar ((U : ZMod (r * s)) * (((a⁻¹ : (ZMod (r * s))ˣ) : ZMod (r * s)) *
        (x ^ 2 + (N : ZMod (r * s))) + (N : ZMod (r * s)) * (a : ZMod (r * s)))) : ℂ) =
        g₁ (EU a).1 (EX x).1 * g₂ (EU a).2 (EX x).2 := by
    intro a x
    rw [hsplit]
    simp only [g₁, g₂, map_add, map_mul, map_pow, map_intCast]
    push_cast
    simp only [mul_assoc]
    rfl
  unfold Tq
  calc ∑ a : (ZMod (r * s))ˣ, ∑ x : ZMod (r * s),
        (stdAddChar ((U : ZMod (r * s)) * (((a⁻¹ : (ZMod (r * s))ˣ) : ZMod (r * s)) *
          (x ^ 2 + (N : ZMod (r * s))) + (N : ZMod (r * s)) * (a : ZMod (r * s)))) : ℂ)
      = ∑ a : (ZMod (r * s))ˣ, ∑ x : ZMod (r * s), g₁ (EU a).1 (EX x).1 * g₂ (EU a).2 (EX x).2 :=
        Fintype.sum_congr _ _ fun a => Fintype.sum_congr _ _ fun x => hterm a x
    _ = ∑ p : (ZMod r)ˣ × (ZMod s)ˣ, ∑ x : ZMod r × ZMod s, g₁ p.1 x.1 * g₂ p.2 x.2 :=
        Fintype.sum_equiv EU.toEquiv _ _ fun a => Fintype.sum_equiv EX _ _ fun x => rfl
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp_rw [Fintype.sum_prod_type, sum_mul_sum]
        rfl

/-- **`T` at an odd prime.** -/
theorem Tq_prime {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {u n : ZMod p} (hu : u ≠ 0)
    (hn : n ≠ 0) :
    Tq p u n = PT.chi p (-n) * p * (stdAddChar (2 * (u * n)) + stdAddChar (-2 * (u * n))) := by
  rw [← PT.T_prime hp2 hu hn]
  unfold Tq
  refine Fintype.sum_congr _ _ fun d => Fintype.sum_congr _ _ fun x => ?_
  rw [show ((d⁻¹ : (ZMod p)ˣ) : ZMod p) = (d : ZMod p)⁻¹ from (ZMod.inv_coe_unit d).symm]

end ThreeSquares
