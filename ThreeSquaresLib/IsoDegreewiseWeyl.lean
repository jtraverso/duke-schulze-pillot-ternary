/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.IsoWeyl
public import ThreeSquaresLib.WeylFinal
public import ThreeSquaresLib.DegreewiseWeyl

/-! # From even-degree isotropic estimates to finite-degree Weyl estimates -/

@[expose] public section

namespace ThreeSquares
open Finset

/-- Odd-degree isotropic Weyl sums vanish by the antipodal involution. -/
theorem weylU_odd_eq_zero (u : Fin 3 → ℂ) {d : ℕ} (hd : Odd d) (t : ℕ) :
    weylU u d t = 0 := by
  classical
  have hn (x : Fin 3 → ℤ) : dot3 u (-x) = -dot3 u x := by
    simp [dot3, Finset.sum_neg_distrib]
  have hm {x : Fin 3 → ℤ} (hx : x ∈ Duke.reps3 t) : -x ∈ Duke.reps3 t := by
    rw [Duke.mem_reps3] at hx ⊢
    simpa using hx
  have hsum : weylU u d t = -weylU u d t := by
    unfold weylU
    calc (∑ x ∈ Duke.reps3 t, dot3 u x ^ d)
        = ∑ x ∈ Duke.reps3 t, dot3 u (-x) ^ d := by
            apply Finset.sum_bij (fun x _ => -x)
            · intro x hx; exact hm hx
            · intro x _ y _ h; exact neg_injective h
            · intro x hx; exact ⟨-x, hm hx, by simp⟩
            · intro x _; simp
      _ = -(∑ x ∈ Duke.reps3 t, dot3 u x ^ d) := by
            simp_rw [hn, hd.neg_pow]
            rw [Finset.sum_neg_distrib]
  have htwo : (2 : ℂ) * weylU u d t = 0 := by linear_combination hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Each positive degree has a positive saving; odd degrees need no analytic estimate. -/
theorem weyl_iso_degree (d : ℕ) (hd : 1 ≤ d) :
    ∃ η > 0, ∀ u : Fin 3 → ℂ, ∑ j, u j ^ 2 = 0 → ∃ C : ℝ, ∀ t : ℕ,
      1 ≤ t → Squarefree t → t % 8 = 3 →
      ‖weylU u d t‖ ≤ C * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η) := by
  rcases Nat.even_or_odd d with he | ho
  · have hd2 : 2 ≤ d := by obtain ⟨k,hk⟩ := he; omega
    exact weyl_iso_even d hd2 he
  · refine ⟨1, by norm_num, fun u _ => ⟨0, fun t _ _ _ => ?_⟩⟩
    rw [weylU_odd_eq_zero u ho t, norm_zero, zero_mul]

namespace Duke
open MvPolynomial

theorem weyl_bound_at_degree_of_iso {S : Set ℕ} {η : ℝ} (d : ℕ) (hd : 1 ≤ d)
    (hiso : ∀ t₀ : ℂ, ∃ C : ℝ, ∀ t ∈ S, 1 ≤ t →
      ‖weylU (uvec t₀) d t‖ ≤ C * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η))
    (P : R3) (hP : P.IsHomogeneous d) (hl : lap P = 0) :
    ∃ C : ℝ, ∀ t ∈ S, 1 ≤ t →
      |weylSum P t| ≤ C * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (map_mem_span_Qk d hd hP hl)
  obtain ⟨w, hw⟩ := Qk_eq_sum d
  have hC : ∀ i : Fin (2 * d + 1), ∃ C : ℝ, ∀ t ∈ S, 1 ≤ t →
      ‖weylU (uvec ((i : ℕ) : ℂ)) d t‖ ≤ C * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η) :=
    fun i => hiso _
  choose C hCb using hC
  refine ⟨∑ k, ∑ i, ‖c k‖ * ‖w k i‖ * |C i|, fun t ht ht1 => ?_⟩
  -- the Weyl sum of `P` as a complex combination
  have e1 : ∀ x : Fin 3 → ℤ, ((eval (pt3 x) P : ℝ) : ℂ) =
      ∑ k, ∑ i, c k * w k i * dot3 (uvec ((i : ℕ) : ℂ)) x ^ d := by
    intro x
    rw [← eval_map_real, ← hc, map_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [smul_eq_C_mul, map_mul, eval_C, hw k, map_sum, Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_eq_C_mul, map_mul, eval_C, eval_linC_pow]
    ring
  have hsum : ((weylSum P t : ℝ) : ℂ) = ∑ k, ∑ i, c k * w k i * weylU (uvec ((i : ℕ) : ℂ)) d t := by
    unfold weylSum weylU
    push_cast
    simp_rw [e1]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  have hpow : 0 ≤ (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η) := Real.rpow_nonneg htpos.le _
  calc |weylSum P t| = ‖((weylSum P t : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ k, ∑ i, ‖c k * w k i * weylU (uvec ((i : ℕ) : ℂ)) d t‖ := by
        rw [hsum]
        exact (norm_sum_le _ _).trans (sum_le_sum fun k _ => norm_sum_le _ _)
    _ ≤ ∑ k, ∑ i, ‖c k‖ * ‖w k i‖ * |C i| * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η) := by
        refine sum_le_sum fun k _ => sum_le_sum fun i _ => ?_
        rw [norm_mul, norm_mul]
        have := (hCb i t ht ht1).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hpow)
        calc ‖c k‖ * ‖w k i‖ * ‖weylU (uvec ((i : ℕ) : ℂ)) d t‖
            ≤ ‖c k‖ * ‖w k i‖ * (|C i| * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η)) := by gcongr
          _ = _ := by ring
    _ = _ := by rw [Finset.sum_mul]; simp_rw [Finset.sum_mul]


/-- The minimum of finitely many positive degree savings is positive. -/
theorem weyl_bound_through (K : ℕ) :
    ∃ η > 0, WeylBoundThrough {t | Squarefree t ∧ t % 8 = 3} K η := by
  classical
  have hchoose : ∀ d : ℕ, ∃ η > 0, ∀ u : Fin 3 → ℂ, ∑ j, u j ^ 2 = 0 → ∃ C : ℝ,
      ∀ t : ℕ, 1 ≤ t → Squarefree t → t % 8 = 3 → 1 ≤ d →
      ‖weylU u d t‖ ≤ C * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η) := by
    intro d
    by_cases hd : 1 ≤ d
    · obtain ⟨η,hη,h⟩ := weyl_iso_degree d hd
      exact ⟨η,hη,fun u hu => by
        obtain ⟨C,hC⟩ := h u hu
        exact ⟨C,fun t ht hs h8 _ => hC t ht hs h8⟩⟩
    · exact ⟨1,by norm_num,fun _ _ => ⟨0,fun _ _ _ _ h => False.elim (hd h)⟩⟩
  choose e he hbound using hchoose
  let E := (range (K+1)).image e
  have hE : E.Nonempty := ⟨e 0, mem_image.mpr ⟨0, by simp, rfl⟩⟩
  let η := E.min' hE
  have hη : 0 < η := by
    obtain ⟨d,_,hd⟩ := mem_image.mp (E.min'_mem hE)
    change 0 < E.min' hE
    rw [←hd]
    exact he d
  have hle {d : ℕ} (hd : d ≤ K) : η ≤ e d :=
    E.min'_le (e d) (mem_image.mpr ⟨d,mem_range.mpr (by omega),rfl⟩)
  refine ⟨η,hη,fun d P hd hdK hP hl => ?_⟩
  apply weyl_bound_at_degree_of_iso d hd ?_ P hP hl
  intro z
  obtain ⟨C,hC⟩ := hbound d (uvec z) (uvec_isotropic z)
  refine ⟨|C|,fun t ht ht1 => ?_⟩
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  calc ‖weylU (uvec z) d t‖ ≤ C * (t : ℝ)^((d : ℝ)/2+1/2-e d) := hC t ht1 ht.1 ht.2 hd
    _ ≤ |C| * (t : ℝ)^((d : ℝ)/2+1/2-e d) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by positivity) _)
    _ ≤ |C| * (t : ℝ)^((d : ℝ)/2+1/2-η) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
      exact Real.rpow_le_rpow_of_exponent_le htR (by linarith [hle hdK])

end Duke
end ThreeSquares
