/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Fischer

/-!
# Weyl sums on the sphere `x₀² + x₁² + x₂² = t`

* `reps3 t`: the integer points on the sphere, `r3 t` their number.
* `weylSum P t = ∑_{|x|² = t} P(x)`.
* `kap d P`: the spherical mean of a homogeneous `P` of degree `d`, `Δ^{d/2} P / (d+1)!` for `d`
  even and `0` for `d` odd.
* `weyl_hom`: if the Weyl sums of harmonic polynomials of degree `d ≥ 1` are
  `O(t^{d/2 + 1/2 − η})` on a set `S` of `t`, then for every homogeneous `P` of degree `d`,
  `weylSum P t = kap d P · t^{d/2} r3 t + O(t^{d/2 + 1/2 − η})` on `S` (Fischer decomposition).
-/

@[expose] public section

namespace ThreeSquares.Duke

open MvPolynomial Finset

/-- The integer points on the sphere `|x|² = t`. -/
noncomputable def reps3 (t : ℕ) : Finset (Fin 3 → ℤ) :=
  (Fintype.piFinset fun _ => Icc (-(t : ℤ)) t).filter (fun x => ∑ i, x i ^ 2 = t)

theorem mem_reps3 (t : ℕ) (x : Fin 3 → ℤ) : x ∈ reps3 t ↔ ∑ i, x i ^ 2 = t := by
  unfold reps3
  rw [mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => ?_, h⟩
    have hle : x i ^ 2 ≤ (t : ℤ) := by
      rw [← h]
      exact single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (mem_univ i)
    rw [mem_Icc]
    constructor <;> nlinarith [sq_nonneg (x i - 1), sq_nonneg (x i + 1)]

/-- `r₃(t)`. -/
noncomputable def r3 (t : ℕ) : ℕ := (reps3 t).card

/-- The real point of `x`. -/
def pt3 (x : Fin 3 → ℤ) : Fin 3 → ℝ := fun i => (x i : ℝ)

/-- `∑_{|x|² = t} P(x)`. -/
noncomputable def weylSum (P : R3) (t : ℕ) : ℝ := ∑ x ∈ reps3 t, eval (pt3 x) P

theorem eval_nrm {t : ℕ} {x : Fin 3 → ℤ} (hx : x ∈ reps3 t) : eval (pt3 x) nrm = t := by
  rw [mem_reps3] at hx
  have : ((∑ i, x i ^ 2 : ℤ) : ℝ) = (t : ℝ) := by rw [hx]; simp
  push_cast at this
  simp [nrm, pt3, this]

theorem weylSum_add (P Q : R3) (t : ℕ) : weylSum (P + Q) t = weylSum P t + weylSum Q t := by
  simp [weylSum, sum_add_distrib]

theorem weylSum_nrm_mul (Q : R3) (t : ℕ) : weylSum (nrm * Q) t = t * weylSum Q t := by
  unfold weylSum
  rw [mul_sum]
  refine sum_congr rfl fun x hx => ?_
  rw [eval_mul, eval_nrm hx]

theorem weylSum_C (a : ℝ) (t : ℕ) : weylSum (C a) t = a * r3 t := by
  simp [weylSum, r3, mul_comm]

/-- The spherical mean of a homogeneous polynomial of degree `d`. -/
noncomputable def kap (d : ℕ) (P : R3) : ℝ :=
  if Even d then constantCoeff ((lap ^ (d / 2)) P) / ((d + 1).factorial : ℝ) else 0

theorem lap_pow_apply (n : ℕ) (P : R3) : (lap ^ n) P = lap^[n] P := by
  rw [Module.End.pow_apply]

theorem kap_add (d : ℕ) (P Q : R3) : kap d (P + Q) = kap d P + kap d Q := by
  unfold kap
  split_ifs
  · rw [map_add, map_add, add_div]
  · simp

theorem kap_harm {H : R3} {d : ℕ} (hd : 1 ≤ d) (hH : lap H = 0) : kap d H = 0 := by
  unfold kap
  split_ifs with he
  · obtain ⟨j, rfl⟩ := he
    have hj : j + j = 2 * j := by ring
    rw [hj, Nat.mul_div_cancel_left j (by norm_num)]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [lap_pow_apply, Function.iterate_succ_apply, hH, Function.iterate_fixed (map_zero lap) i,
      map_zero, zero_div]
  · rfl

theorem kap_nrm_mul {Q : R3} {m : ℕ} (hQ : Q.IsHomogeneous m) : kap (m + 2) (nrm * Q) = kap m Q := by
  unfold kap
  by_cases he : Even m
  · have he2 : Even (m + 2) := he.add even_two
    rw [if_pos he2, if_pos he]
    obtain ⟨j, rfl⟩ := he
    have hj : j + j = 2 * j := by ring
    rw [hj, show (2 * j + 2) / 2 = j + 1 by omega, Nat.mul_div_cancel_left j (by norm_num)]
    rw [lap_pow_apply, lap_pow_apply, lap_iter_nrm_mul (hj ▸ hQ) (j + 1) (by omega) (by omega),
      show j + 1 - 1 = j by omega]
    have hz : lap^[j + 1] Q = 0 := by
      rw [Function.iterate_succ_apply']
      exact lap_eq_zero_of_lt (lap_iter_isHomogeneous (hj ▸ hQ) j) (by omega)
    rw [hz, mul_zero, zero_add, smul_eq_C_mul, map_mul, constantCoeff_C]
    rw [show 2 * j + 2 + 1 = (2 * j + 1) + 2 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    have h1 : ((2 * j + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  · have he2 : ¬ Even (m + 2) := by
      intro h; exact he (by simpa using (Nat.even_add.mp h).mpr even_two)
    rw [if_neg he2, if_neg he]

/-- The hypothesis on Weyl sums of harmonic polynomials. -/
def WeylBound (S : Set ℕ) (η : ℝ) : Prop :=
  ∀ (d : ℕ) (P : R3), 1 ≤ d → P.IsHomogeneous d → lap P = 0 →
    ∃ C : ℝ, ∀ t ∈ S, 1 ≤ t → |weylSum P t| ≤ C * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η)

theorem weyl_hom {S : Set ℕ} {η : ℝ} (hW : WeylBound S η) :
    ∀ (d : ℕ) (P : R3), P.IsHomogeneous d → ∃ C : ℝ, ∀ t ∈ S, 1 ≤ t →
      |weylSum P t - kap d P * (t : ℝ) ^ ((d : ℝ) / 2) * r3 t| ≤
        C * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η)
  | d, P, hP => by
    by_cases hd2 : d < 2
    · rcases Nat.lt_succ_iff.mp hd2 |>.lt_or_eq with h0 | h1
      · -- `d = 0`: a constant
        have h0 : d = 0 := by omega
        subst h0
        rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hP
        refine ⟨0, fun t _ _ => ?_⟩
        rw [hP, weylSum_C]
        simp [kap]
      · subst h1
        obtain ⟨C, hC⟩ := hW 1 P le_rfl hP (lap_eq_zero_of_lt hP (by norm_num))
        refine ⟨C, fun t ht ht1 => ?_⟩
        have : kap 1 P = 0 := by simp [kap]
        rw [this, zero_mul, zero_mul, sub_zero]
        exact hC t ht ht1
    · push Not at hd2
      obtain ⟨H, Q, hH, hHl, hQ, rfl⟩ := fischer hP hd2
      obtain ⟨CH, hCH⟩ := hW d H (by omega) hH hHl
      obtain ⟨CQ, hCQ⟩ := weyl_hom hW (d - 2) Q hQ
      refine ⟨CH + CQ, fun t ht ht1 => ?_⟩
      have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
      have hkap : kap d (H + nrm * Q) = kap (d - 2) Q := by
        rw [kap_add, kap_harm (by omega) hHl, zero_add]
        have := kap_nrm_mul hQ
        rwa [show d - 2 + 2 = d by omega] at this
      rw [weylSum_add, weylSum_nrm_mul, hkap]
      have hpow : (t : ℝ) ^ ((d : ℝ) / 2) = t * (t : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2) := by
        rw [show (d : ℝ) / 2 = 1 + ((d - 2 : ℕ) : ℝ) / 2 by rw [Nat.cast_sub hd2]; push_cast; ring,
          Real.rpow_add htpos, Real.rpow_one]
      have hpow2 : (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η) =
          t * (t : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2 + 1 / 2 - η) := by
        rw [show (d : ℝ) / 2 + 1 / 2 - η = 1 + (((d - 2 : ℕ) : ℝ) / 2 + 1 / 2 - η) by
          rw [Nat.cast_sub hd2]; push_cast; ring, Real.rpow_add htpos, Real.rpow_one]
      have e : weylSum H t + t * weylSum Q t - kap (d - 2) Q * (t : ℝ) ^ ((d : ℝ) / 2) * r3 t =
          weylSum H t + t * (weylSum Q t - kap (d - 2) Q *
            (t : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2) * r3 t) := by
        rw [hpow]; ring
      rw [e]
      have h1 := hCH t ht ht1
      have h2 := hCQ t ht ht1
      calc |weylSum H t + t * (weylSum Q t - kap (d - 2) Q *
              (t : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2) * r3 t)|
          ≤ |weylSum H t| + t * |weylSum Q t - kap (d - 2) Q *
              (t : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2) * r3 t| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_of_pos htpos]
        _ ≤ CH * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η) +
            t * (CQ * (t : ℝ) ^ (((d - 2 : ℕ) : ℝ) / 2 + 1 / 2 - η)) := by
            gcongr
        _ = (CH + CQ) * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η) := by
            rw [hpow2]; ring
  termination_by d => d
  decreasing_by omega

end ThreeSquares.Duke
