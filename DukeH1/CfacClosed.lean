/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.KlBridge
public import DukeH1.BesselClosed

/-!
# Closed form of the Kloosterman weight

With `k = ℓ + 3/2` and `besS(k, X) = X^{−m/2}(e^{2i√X} p(X^{−1/2}) + e^{−2i√X} q(X^{−1/2}))`, `m = ℓ + 1`:
`c · cfac(c) = K (e(2n/c) p(c/(2πn)) + e(−2n/c) q(c/(2πn)))` with `‖K‖ = √π n^{−1/2}`.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares.Poin

open Complex Polynomial ThreeSquares.Lip

open scoped Real

/-- The constant of the closed form. -/
noncomputable def Kc (ℓ n : ℕ) : ℂ :=
  (-(2 * π * Complex.I)) ^ (kw ℓ : ℂ) * ((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1) /
    ((1 + Complex.I) * ((2 * π * n : ℝ) : ℂ) ^ (ℓ + 1))

theorem cfac_closed (ℓ n : ℕ) (hn : 0 < n) {p q : ℂ[X]} (hpq : BesForm (ℓ + 1) p q) (c : ℕ) (hc : 0 < c) :
    (c : ℂ) * cfac ℓ n c = Kc ℓ n *
      (cexp (2 * π * Complex.I * (2 * n / c)) * p.eval ((c / (2 * π * n) : ℝ) : ℂ) +
        cexp (-(2 * π * Complex.I * (2 * n / c))) * q.eval ((c / (2 * π * n) : ℝ) : ℂ)) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set t : ℝ := 2 * π * n / c with ht
  have ht0 : 0 < t := by positivity
  have hX : 4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n = t ^ 2 := by rw [ht]; field_simp; ring
  have hsq : Real.sqrt (t ^ 2) = t := Real.sqrt_sq ht0.le
  have hB := hpq (t ^ 2) (by positivity)
  rw [hsq] at hB
  have hk : ((ℓ + 1 : ℕ) : ℝ) + 1 / 2 = kw ℓ := by unfold kw; push_cast; ring
  rw [hk] at hB
  unfold cfac
  have hX' : (4 * (π : ℂ) ^ 2 * (((n : ℝ) : ℂ) / ((c : ℝ) : ℂ) ^ 2) * (n : ℂ)) = ((t ^ 2 : ℝ) : ℂ) := by
    rw [← hX]; push_cast; ring
  rw [hX', hB]
  have hinv : ((t : ℂ))⁻¹ = (((c / (2 * π * n)) : ℝ) : ℂ) := by
    rw [ht]; push_cast; field_simp
  rw [hinv]
  have he1 : cexp (2 * Complex.I * (t : ℂ)) = cexp (2 * π * Complex.I * (2 * n / c)) := by
    congr 1; rw [ht]; push_cast; field_simp
  have he2 : cexp (-(2 * Complex.I * (t : ℂ))) = cexp (-(2 * π * Complex.I * (2 * n / c))) := by
    congr 1; rw [ht]; push_cast; field_simp
  rw [he1, he2]
  unfold Kc
  -- the powers of `c` cancel: `c · c^{−k} · c^{−1/2} · c^{m} = 1`
  have hcpow : ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) ^ (-(kw ℓ : ℂ)) / (Real.sqrt c : ℂ) *
      ((((c / (2 * π * n)) : ℝ) : ℂ)) ^ (ℓ + 1) = 1 / ((2 * π * n : ℝ) : ℂ) ^ (ℓ + 1) := by
    have h1 : ((c : ℝ) : ℂ) ^ (-(kw ℓ : ℂ)) = ((c ^ (-(kw ℓ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hcR.le]; push_cast; rfl
    rw [h1]
    have h2 : (c : ℝ) ^ (-(kw ℓ)) = (c : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) * (c : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hcR, ← hk]; ring_nf
    have h3 : Real.sqrt c = (c : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow c
    have h4 : (c : ℝ) ^ (-((ℓ + 1 : ℕ) : ℝ)) = ((c : ℝ) ^ (ℓ + 1))⁻¹ := by
      rw [Real.rpow_neg hcR.le, Real.rpow_natCast]
    have h5 : (c : ℝ) ^ (-(1 / 2 : ℝ)) = ((c : ℝ) ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hcR.le _
    have h6 : (0 : ℝ) < (c : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hcR _
    rw [h2, h4, h5, h3]
    have h7 : (c : ℝ) ^ (1 / 2 : ℝ) * (c : ℝ) ^ (1 / 2 : ℝ) = (c : ℝ) := by
      rw [← Real.rpow_add hcR]; norm_num
    have hs : (((c : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (((c : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) = (c : ℂ) := by
      exact_mod_cast h7
    have hs0 : (((c : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h6.ne'
    have hπn : (0 : ℝ) < 2 * π * n := by positivity
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hπn' : (2 * (π : ℂ) * n) ≠ 0 := by exact_mod_cast hπn.ne'
    push_cast
    rw [div_pow]
    field_simp
    rw [← hs]
    ring
  have hsqrt : ((Real.sqrt (c : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hcR).ne'
  have hπn : ((2 * π * n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0 : ℝ) < 2 * π * n).ne'
  have h1i : (1 + Complex.I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  calc (c : ℂ) * ((-(2 * π * Complex.I)) ^ (kw ℓ : ℂ) * ((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1) *
        ((c : ℝ) : ℂ) ^ (-(kw ℓ : ℂ)) *
        ((((c / (2 * π * n)) : ℝ) : ℂ) ^ (ℓ + 1) *
          (cexp (2 * π * Complex.I * (2 * n / c)) * p.eval ((c / (2 * π * n) : ℝ) : ℂ) +
            cexp (-(2 * π * Complex.I * (2 * n / c))) * q.eval ((c / (2 * π * n) : ℝ) : ℂ))) /
        ((1 + Complex.I) * (Real.sqrt c : ℂ)))
      = (-(2 * π * Complex.I)) ^ (kw ℓ : ℂ) * ((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1) / (1 + Complex.I) *
          (((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) ^ (-(kw ℓ : ℂ)) / (Real.sqrt c : ℂ) *
            ((((c / (2 * π * n)) : ℝ) : ℂ)) ^ (ℓ + 1)) *
          (cexp (2 * π * Complex.I * (2 * n / c)) * p.eval ((c / (2 * π * n) : ℝ) : ℂ) +
            cexp (-(2 * π * Complex.I * (2 * n / c))) * q.eval ((c / (2 * π * n) : ℝ) : ℂ)) := by
        push_cast; field_simp
    _ = _ := by rw [hcpow]; field_simp

end ThreeSquares.Poin
