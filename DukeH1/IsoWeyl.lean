/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.IsoSpan
public import DukeH1.ThetaCoeff

/-!
# Weyl sums of harmonic polynomials from isotropic powers

* `map_mem_span_Qk`: a real harmonic homogeneous polynomial of degree `ℓ ≥ 1`, viewed over `ℂ`, is a
  linear combination of the `Q_k` (dimension count: both spaces have dimension `2ℓ+1`).
* `Qk_eq_sum`: each `Q_k` is a combination of `(u_{t_i}·x)^ℓ`, `t_i = 0, …, 2ℓ` (Vandermonde).
* `weylBound_of_iso`: bounds for the Weyl sums `∑_{|x|²=t} (u·x)^ℓ` of isotropic powers give
  `WeylBound` (the hypothesis of `dukeSquarefree_of_weyl`).
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares.Duke

open MvPolynomial Finset

theorem finrank_harm' (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    Module.finrank ℝ (LinearMap.ker (lapHom ℓ)) = 2 * ℓ + 1 := by
  rcases Nat.lt_or_ge ℓ 2 with h | h
  · have hℓ1 : ℓ = 1 := by omega
    subst hℓ1
    have htop : LinearMap.ker (lapHom 1) = ⊤ := by
      rw [eq_top_iff]
      intro P _
      rw [LinearMap.mem_ker]
      ext1
      exact lap_eq_zero_of_lt P.2 (by norm_num)
    rw [htop, finrank_top, finrank_hom]
  · exact finrank_harm ℓ h

/-- Complex harmonic homogeneous polynomials of degree `ℓ`. -/
noncomputable def HC (ℓ : ℕ) : Submodule ℂ RC :=
  homogeneousSubmodule (Fin 3) ℂ ℓ ⊓ LinearMap.ker lapC

theorem reP_zero : reP 0 = 0 := by simp [reP]

theorem imP_zero : imP 0 = 0 := by simp [imP]

theorem HC_le_span (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ f : Fin (2 * ℓ + 1) → RC, HC ℓ ≤ Submodule.span ℂ (Set.range f) := by
  set K := LinearMap.ker (lapHom ℓ)
  haveI : Module.Free ℝ K := Module.Free.of_divisionRing ℝ K
  let b := Module.finBasisOfFinrankEq ℝ K (finrank_harm' ℓ hℓ)
  let f : Fin (2 * ℓ + 1) → RC := fun i => map Complex.ofRealHom (((b i : K) : homogeneousSubmodule
    (Fin 3) ℝ ℓ) : R3)
  refine ⟨f, fun P hP => ?_⟩
  obtain ⟨hPh, hPl⟩ := hP
  rw [SetLike.mem_coe, mem_homogeneousSubmodule] at hPh
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hPl
  -- a real harmonic polynomial maps into the span
  have hreal : ∀ Q : R3, Q.IsHomogeneous ℓ → lap Q = 0 →
      map Complex.ofRealHom Q ∈ Submodule.span ℂ (Set.range f) := by
    intro Q hQh hQl
    have hQK : (⟨Q, hQh⟩ : homogeneousSubmodule (Fin 3) ℝ ℓ) ∈ K := by
      rw [LinearMap.mem_ker]; ext1; exact hQl
    have hrepr := b.sum_repr ⟨_, hQK⟩
    have hQ : Q = ∑ i, b.repr ⟨_, hQK⟩ i • (((b i : K) : homogeneousSubmodule (Fin 3) ℝ ℓ) : R3) := by
      have := congrArg (fun v : K => ((v : homogeneousSubmodule (Fin 3) ℝ ℓ) : R3)) hrepr
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    rw [hQ, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_eq_C_mul, map_mul, map_C]
    rw [show C (Complex.ofRealHom (b.repr ⟨_, hQK⟩ i)) *
        map Complex.ofRealHom (((b i : K) : homogeneousSubmodule (Fin 3) ℝ ℓ) : R3) =
        (b.repr ⟨_, hQK⟩ i : ℂ) • f i by rw [smul_eq_C_mul]; rfl]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 := hreal (reP P) (isHomogeneous_reP hPh) (by rw [lap_reP, hPl, reP_zero])
  have h2 := hreal (imP P) (isHomogeneous_imP hPh) (by rw [lap_imP, hPl, imP_zero])
  rw [reP_add_imP P, ← smul_eq_C_mul]
  exact Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2)

theorem Qk_mem_HC (ℓ k : ℕ) : Qk ℓ k ∈ HC ℓ :=
  ⟨isHomogeneous_Qk ℓ k, lapC_Qk ℓ k⟩

/-- **Real harmonic polynomials are combinations of the `Q_k`.** -/
theorem map_mem_span_Qk (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {P : R3} (hP : P.IsHomogeneous ℓ) (hl : lap P = 0) :
    map Complex.ofRealHom P ∈ Submodule.span ℂ (Set.range fun k : Fin (2 * ℓ + 1) => Qk ℓ k) := by
  set V := Submodule.span ℂ (Set.range fun k : Fin (2 * ℓ + 1) => Qk ℓ k)
  obtain ⟨f, hf⟩ := HC_le_span ℓ hℓ
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  have hfin : FiniteDimensional ℂ (HC ℓ) :=
    Submodule.finiteDimensional_of_le hf
  have hVle : V ≤ HC ℓ := Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact Qk_mem_HC ℓ k)
  have hVrank : Module.finrank ℂ V = 2 * ℓ + 1 := by
    rw [finrank_span_eq_card (linearIndependent_Qk ℓ), Fintype.card_fin]
  have hHCrank : Module.finrank ℂ (HC ℓ) ≤ 2 * ℓ + 1 :=
    (Submodule.finrank_mono hf).trans ((finrank_span_le_card _).trans
      (by simpa using Finset.card_image_le (s := Finset.univ) (f := f)))
  have hEq : V = HC ℓ := Submodule.eq_of_le_of_finrank_le hVle (by rw [hVrank]; exact hHCrank)
  rw [hEq]
  refine ⟨?_, ?_⟩
  · exact hP.map _
  · rw [SetLike.mem_coe, LinearMap.mem_ker, lapC_map, hl, map_zero]

/-- **Vandermonde**: `Q_k = ∑_i w_{ki} (u_{t_i} · x)^ℓ` with `t_i = i`. -/
theorem Qk_eq_sum (ℓ : ℕ) : ∃ w : Fin (2 * ℓ + 1) → Fin (2 * ℓ + 1) → ℂ,
    ∀ k : Fin (2 * ℓ + 1), Qk ℓ k = ∑ i, w k i • linC (uvec ((i : ℕ) : ℂ)) ^ ℓ := by
  set M : Matrix (Fin (2 * ℓ + 1)) (Fin (2 * ℓ + 1)) ℂ :=
    Matrix.vandermonde (fun i : Fin (2 * ℓ + 1) => ((i : ℕ) : ℂ)) with hM
  have hdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_vandermonde_ne_zero_iff]
    intro a b h
    simp only at h
    exact Fin.ext (by exact_mod_cast h)
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hdet)
  have hv : ∀ i : Fin (2 * ℓ + 1), linC (uvec ((i : ℕ) : ℂ)) ^ ℓ =
      ∑ j : Fin (2 * ℓ + 1), M i j • Qk ℓ j := by
    intro i
    rw [← eval_Qpoly ℓ, ← Fin.sum_univ_eq_sum_range (fun j => Qk ℓ j * C ((i : ℕ) : ℂ) ^ j)]
    refine sum_congr rfl fun j _ => ?_
    rw [hM, Matrix.vandermonde_apply, smul_eq_C_mul, map_pow, mul_comm]
  refine ⟨fun k i => M⁻¹ k i, fun k => ?_⟩
  calc Qk ℓ k = ∑ j, (M⁻¹ * M) k j • Qk ℓ j := by
        rw [hinv]; simp [Matrix.one_apply]
    _ = ∑ i, M⁻¹ k i • ∑ j, M i j • Qk ℓ j := by
        simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
    _ = ∑ i, M⁻¹ k i • linC (uvec ((i : ℕ) : ℂ)) ^ ℓ := by simp_rw [hv]

theorem eval_linC_pow (u : Fin 3 → ℂ) (ℓ : ℕ) (x : Fin 3 → ℤ) :
    eval (fun j => ((x j : ℤ) : ℂ)) (linC u ^ ℓ) = dot3 u x ^ ℓ := by
  simp [linC, dot3]

theorem eval_map_real (P : R3) (x : Fin 3 → ℤ) :
    eval (fun j => ((x j : ℤ) : ℂ)) (map Complex.ofRealHom P) = ((eval (pt3 x) P : ℝ) : ℂ) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]; push_cast; ring
  | mul_X p i hp => simp only [map_mul, map_X, eval_X, hp, pt3]; push_cast; ring

/-- **Weyl bounds for isotropic powers give `WeylBound`.** -/
theorem weylBound_of_iso {S : Set ℕ} {η : ℝ}
    (hiso : ∀ (ℓ : ℕ), 1 ≤ ℓ → ∀ t₀ : ℂ, ∃ C : ℝ, ∀ t ∈ S, 1 ≤ t →
      ‖weylU (uvec t₀) ℓ t‖ ≤ C * (t : ℝ) ^ ((ℓ : ℝ) / 2 + 1 / 2 - η)) :
    WeylBound S η := by
  intro d P hd hP hl
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (map_mem_span_Qk d hd hP hl)
  obtain ⟨w, hw⟩ := Qk_eq_sum d
  have hC : ∀ i : Fin (2 * d + 1), ∃ C : ℝ, ∀ t ∈ S, 1 ≤ t →
      ‖weylU (uvec ((i : ℕ) : ℂ)) d t‖ ≤ C * (t : ℝ) ^ ((d : ℝ) / 2 + 1 / 2 - η) :=
    fun i => hiso d hd _
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

end ThreeSquares.Duke
