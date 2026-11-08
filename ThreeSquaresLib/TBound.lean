/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.TSplit
public import ThreeSquaresLib.GaussNorm
public import ThreeSquaresLib.PrimePowT

/-!
# Pointwise bounds for `T_c`

* `norm_Tq_four_le`: `|T_r(u, N)| ≤ r √(2r)` for `4 ∣ r`, `u` a unit;
* `norm_Tc_le`: `|T_{rq}(1, n)| ≤ r √(2r) · q · τ(q)` for `4 ∣ r`, `q` odd coprime to `r n`.
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset

theorem norm_exp_two_pi_I_real (t : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * t)‖ = 1 := by
  rw [show 2 * (Real.pi : ℂ) * Complex.I * t = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_Tq_four_le (m : ℕ) (hm : 0 < m) (u N : ZMod (4 * m)) (hu : IsUnit u) :
    haveI : NeZero (4 * m) := ⟨by omega⟩
    ‖Tq (4 * m) u N‖ ≤ (4 * m : ℕ) * Real.sqrt (2 * (4 * m : ℕ)) := by
  haveI : NeZero (4 * m) := ⟨by omega⟩
  unfold Tq
  simp_rw [Tq_inner]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ d : (ZMod (4 * m))ˣ, ‖stdAddChar (u * N * ((d : ZMod (4 * m)) +
      ((d⁻¹ : (ZMod (4 * m))ˣ) : ZMod (4 * m)))) * gaussQ (u * ((d⁻¹ : (ZMod (4 * m))ˣ) : ZMod (4 * m))) 0‖ =
      Real.sqrt (2 * (4 * m : ℕ)) := by
    intro d
    rw [norm_mul, RML.ExpSum.Weil.norm_stdAddChar_eq_one, one_mul]
    have h := norm_sq_gaussQ_zero m hm _ (hu.mul (Units.isUnit (d⁻¹)))
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  gcongr
  have : Fintype.card (ZMod (4 * m))ˣ ≤ 4 * m := by
    rw [ZMod.card_units_eq_totient]; exact Nat.totient_le _
  exact_mod_cast this

theorem card_udiv_le (q : ℕ) : (udiv q).card ≤ q.divisors.card :=
  Finset.card_filter_le _ _

/-- **`|T_{rq}| ≤ r √(2r) q τ(q)`.** -/
theorem norm_Tc_le (n m q : ℕ) (hm : 0 < m) (hq : 0 < q) (hrq : (4 * m).Coprime q) (hodd : Odd q)
    (hn : Nat.Coprime n q) :
    ‖Poin.Tc n (4 * m * q)‖ ≤ (4 * m : ℕ) * Real.sqrt (2 * (4 * m : ℕ)) * (q * q.divisors.card) := by
  rw [Tc_expand n (4 * m) q (by omega) hq hrq hodd hn]
  haveI : NeZero (4 * m) := ⟨by omega⟩
  rw [norm_mul]
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
  · refine norm_Tq_four_le m hm _ _ ?_
    have hb := Nat.gcd_eq_gcd_ab q (4 * m)
    rw [Nat.Coprime.gcd_eq_one hrq.symm] at hb
    have h1 : ((Nat.gcdA q (4 * m) : ℤ) : ZMod (4 * m)) * (q : ZMod (4 * m)) = 1 := by
      have := congrArg (fun t : ℤ => (t : ZMod (4 * m))) hb
      push_cast at this
      have h0 : (4 : ZMod (4 * m)) * (m : ZMod (4 * m)) = 0 := by exact_mod_cast ZMod.natCast_self (4 * m)
      rw [h0, zero_mul, add_zero] at this
      exact (mul_comm _ _).trans this.symm
    exact IsUnit.of_mul_eq_one _ h1
  · rw [norm_mul, norm_mul, Complex.norm_natCast]
    have hJ : ‖(jacobiSym (-(n : ℤ)) q : ℂ)‖ ≤ 1 := by
      rcases jacobiSym.trichotomy (-(n : ℤ)) q with h | h | h <;> rw [h] <;> simp
    have hS : ‖∑ a ∈ udiv q, Complex.exp (2 * Real.pi * Complex.I * (2 * (n : ℤ) / ((4 * m : ℕ) * q))) *
        rph (q / a) (-4 * n) (((4 * m) * a : ℕ) : ℤ) * rph (4 * m) (-2 * n) ((a * (q / a) : ℕ) : ℤ)‖ ≤
        q.divisors.card := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ a ∈ udiv q, ‖Complex.exp (2 * Real.pi * Complex.I * (2 * (n : ℤ) / ((4 * m : ℕ) * q))) *
            rph (q / a) (-4 * n) (((4 * m) * a : ℕ) : ℤ) * rph (4 * m) (-2 * n) ((a * (q / a) : ℕ) : ℤ)‖
          ≤ ∑ a ∈ udiv q, (1 : ℝ) := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_mul, norm_mul]
            have e1 : ‖Complex.exp (2 * Real.pi * Complex.I * (2 * (n : ℤ) / ((4 * m : ℕ) * q)))‖ = 1 := by
              have := norm_exp_two_pi_I_real (2 * n / ((4 * m : ℕ) * q))
              push_cast at this ⊢; exact this
            rw [e1, one_mul]
            exact mul_le_one₀ (norm_rph_le _ _ _) (norm_nonneg _) (norm_rph_le _ _ _)
        _ = (udiv q).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ q.divisors.card := by exact_mod_cast card_udiv_le q
    calc ‖(jacobiSym (-(n : ℤ)) q : ℂ)‖ * (q : ℝ) * ‖_‖ ≤ 1 * q * q.divisors.card := by gcongr
      _ = q * q.divisors.card := by ring

end ThreeSquares
