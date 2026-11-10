/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.HarmDim
public import DukeH1.WeylCap

/-!
# Harmonic polynomials are spanned by isotropic powers: the complex family `Q_k`

With `α = x₀ + i x₁`, `β = −x₀ + i x₁`, `γ = x₂`, the isotropic vectors
`u_t = (1 − t², i(1 + t²), 2t)` satisfy `u_t · x = α + 2tγ + t²β`. We write
`(α + 2tγ + t²β)^ℓ = ∑_k t^k Q_k` and show that each `Q_k` is harmonic (`lapC_Q`).
-/

@[expose] public section

namespace ThreeSquares.Duke

open MvPolynomial Finset

/-- Complex polynomials in three variables. -/
abbrev RC := MvPolynomial (Fin 3) ℂ

/-- The complex Laplacian. -/
noncomputable def lapC : RC →ₗ[ℂ] RC :=
  ∑ i : Fin 3, (pderiv i).toLinearMap ∘ₗ (pderiv i).toLinearMap

theorem lapC_apply (P : RC) : lapC P = ∑ i : Fin 3, pderiv i (pderiv i P) := by
  simp [lapC]

/-- The isotropic vector `u_t`. -/
noncomputable def uvec (t : ℂ) : Fin 3 → ℂ := ![1 - t ^ 2, Complex.I * (1 + t ^ 2), 2 * t]

theorem uvec_isotropic (t : ℂ) : ∑ j, uvec t j ^ 2 = 0 := by
  simp only [uvec, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The linear form `u · x` as a complex polynomial. -/
noncomputable def linC (u : Fin 3 → ℂ) : RC := ∑ j, C (u j) * X j

theorem pderiv_linC (u : Fin 3 → ℂ) (i : Fin 3) : pderiv i (linC u) = C (u i) := by
  simp only [linC, map_sum, pderiv_C_mul, pderiv_X]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem pderiv_linC_pow (u : Fin 3 → ℂ) (i : Fin 3) (m : ℕ) :
    pderiv i (linC u ^ m) = C ((m : ℂ) * u i) * linC u ^ (m - 1) := by
  rw [pderiv_pow, pderiv_linC, map_mul, map_natCast]; ring

theorem lapC_linC_pow (u : Fin 3 → ℂ) (hu : ∑ j, u j ^ 2 = 0) (ℓ : ℕ) : lapC (linC u ^ ℓ) = 0 := by
  rw [lapC_apply]
  rcases ℓ with _ | _ | n
  · simp
  · simp [pderiv_linC]
  · have h : ∀ i : Fin 3, pderiv i (pderiv i (linC u ^ (n + 2))) =
        C (((n + 2) * (n + 1) : ℕ) : ℂ) * C (u i ^ 2) * linC u ^ n := by
      intro i
      rw [pderiv_linC_pow, pderiv_C_mul, pderiv_linC_pow, show n + 2 - 1 - 1 = n by omega,
        ← mul_assoc, ← map_mul, ← map_mul]
      congr 2
      push_cast
      ring
    rw [Finset.sum_congr rfl fun i _ => h i, ← Finset.sum_mul, ← Finset.mul_sum, ← map_sum, hu,
      map_zero, mul_zero, zero_mul]

/-! ### The family `Q_k` -/

/-- `α + 2tγ + t²β` as a polynomial in `t` with coefficients in `RC`. -/
noncomputable def basePoly : Polynomial RC :=
  Polynomial.C (X 0 + C Complex.I * X 1) + Polynomial.C (2 * X 2) * Polynomial.X +
    Polynomial.C (-X 0 + C Complex.I * X 1) * Polynomial.X ^ 2

/-- `(α + 2tγ + t²β)^ℓ`. -/
noncomputable def Qpoly (ℓ : ℕ) : Polynomial RC := basePoly ^ ℓ

/-- `Q_k`, the coefficient of `t^k`. -/
noncomputable def Qk (ℓ k : ℕ) : RC := (Qpoly ℓ).coeff k

theorem eval_basePoly (t : ℂ) : basePoly.eval (C t) = linC (uvec t) := by
  simp only [basePoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow, linC, uvec, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  simp only [map_sub, map_one, map_pow, map_mul, map_add, map_ofNat]
  ring

theorem natDegree_Qpoly_le (ℓ : ℕ) : (Qpoly ℓ).natDegree ≤ 2 * ℓ := by
  unfold Qpoly
  refine (Polynomial.natDegree_pow_le).trans ?_
  have : basePoly.natDegree ≤ 2 := by
    unfold basePoly
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact (Polynomial.natDegree_C _).le.trans (by norm_num)
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  nlinarith

theorem eval_Qpoly (ℓ : ℕ) (t : ℂ) :
    ∑ k ∈ range (2 * ℓ + 1), Qk ℓ k * C t ^ k = linC (uvec t) ^ ℓ := by
  have h1 : (Qpoly ℓ).eval (C t) = linC (uvec t) ^ ℓ := by
    rw [Qpoly, Polynomial.eval_pow, eval_basePoly]
  rw [← h1, Polynomial.eval_eq_sum_range' (n := 2 * ℓ + 1)
    (by have := natDegree_Qpoly_le ℓ; omega)]
  rfl

/-- **Each `Q_k` is harmonic.** -/
theorem lapC_Qk (ℓ k : ℕ) : lapC (Qk ℓ k) = 0 := by
  set E : Polynomial RC := ∑ j ∈ range (2 * ℓ + 1), Polynomial.monomial j (lapC (Qk ℓ j)) with hE
  have hroot : ∀ t : ℂ, E.eval (C t) = 0 := by
    intro t
    have h := congrArg lapC (eval_Qpoly ℓ t)
    rw [lapC_linC_pow _ (uvec_isotropic t), map_sum] at h
    rw [hE, Polynomial.eval_finset_sum]
    rw [← h]
    refine sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_monomial, ← map_pow, mul_comm (Qk ℓ j), ← smul_eq_C_mul,
      LinearMap.map_smul, smul_eq_C_mul, mul_comm]
  have hE0 : E = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun t : ℂ => (C t : RC))
      (fun a b h => C_injective _ _ h) (fun t => hroot t)
  by_cases hk : k < 2 * ℓ + 1
  · have := congrArg (fun p => p.coeff k) hE0
    simp only [hE, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero]
      at this
    rw [Finset.sum_eq_single k (fun j _ hj => if_neg hj) (fun h => absurd (mem_range.mpr hk) h),
      if_pos rfl] at this
    exact this
  · have : Qk ℓ k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (natDegree_Qpoly_le ℓ) (by omega))
    rw [this, map_zero]

theorem isHomogeneous_Qk (ℓ k : ℕ) : (Qk ℓ k).IsHomogeneous ℓ := by
  -- every `Q_k` is a coefficient of `basePoly^ℓ`, whose coefficients are homogeneous of degree `ℓ`
  have hb : ∀ j, (basePoly.coeff j).IsHomogeneous 1 := by
    intro j
    simp only [basePoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_X_pow]
    refine IsHomogeneous.add (IsHomogeneous.add ?_ ?_) ?_
    · split_ifs
      · exact (isHomogeneous_X _ _).add ((isHomogeneous_X _ _).C_mul _)
      · exact isHomogeneous_zero _ _ _
    · split_ifs <;> simp only [mul_one, mul_zero]
      · rw [show (2 : RC) * X 2 = C 2 * X 2 by rw [map_ofNat]]
        exact (isHomogeneous_X _ _).C_mul _
      · exact isHomogeneous_zero _ _ _
    · split_ifs <;> simp only [mul_one, mul_zero]
      · exact (isHomogeneous_X ℂ (0 : Fin 3)).neg.add ((isHomogeneous_X _ _).C_mul _)
      · exact isHomogeneous_zero _ _ _
  have key : ∀ n j, ((basePoly ^ n).coeff j).IsHomogeneous n := by
    intro n
    induction n with
    | zero =>
      intro j
      simp only [pow_zero, Polynomial.coeff_one]
      split_ifs
      · exact isHomogeneous_one _ _
      · exact isHomogeneous_zero _ _ _
    | succ n ih =>
      intro j
      rw [pow_succ, Polynomial.coeff_mul]
      refine IsHomogeneous.sum _ _ _ fun p _ => ?_
      exact (ih p.1).mul (hb p.2)
  exact key ℓ k

/-! ### Real and imaginary parts -/

/-- The real part of a complex polynomial (coefficientwise). -/
noncomputable def reP (P : RC) : R3 := ∑ d ∈ P.support, monomial d (P.coeff d).re

/-- The imaginary part of a complex polynomial (coefficientwise). -/
noncomputable def imP (P : RC) : R3 := ∑ d ∈ P.support, monomial d (P.coeff d).im

theorem coeff_reP (P : RC) (m : Fin 3 →₀ ℕ) : (reP P).coeff m = (P.coeff m).re := by
  rw [reP, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single m (fun d _ hd => if_neg hd) (fun hm => by
    rw [mem_support_iff, not_not] at hm; simp [hm]), if_pos rfl]

theorem coeff_imP (P : RC) (m : Fin 3 →₀ ℕ) : (imP P).coeff m = (P.coeff m).im := by
  rw [imP, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single m (fun d _ hd => if_neg hd) (fun hm => by
    rw [mem_support_iff, not_not] at hm; simp [hm]), if_pos rfl]

theorem reP_add_imP (P : RC) :
    P = map Complex.ofRealHom (reP P) + C Complex.I * map Complex.ofRealHom (imP P) := by
  ext m
  rw [MvPolynomial.coeff_add, coeff_C_mul, coeff_map, coeff_map, coeff_reP, coeff_imP]
  simp [Complex.ext_iff]

theorem lap_reP (P : RC) : lap (reP P) = reP (lapC P) := by
  ext m
  rw [lap_apply, lapC_apply, coeff_reP, coeff_sum, coeff_sum, Complex.re_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_reP]
  simp [Complex.mul_re]

theorem lap_imP (P : RC) : lap (imP P) = imP (lapC P) := by
  ext m
  rw [lap_apply, lapC_apply, coeff_imP, coeff_sum, coeff_sum, Complex.im_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_imP]
  simp [Complex.mul_im]

theorem isHomogeneous_reP {P : RC} {n : ℕ} (h : P.IsHomogeneous n) : (reP P).IsHomogeneous n := by
  intro d hd
  apply h
  intro h0; apply hd; rw [coeff_reP, h0, Complex.zero_re]

theorem isHomogeneous_imP {P : RC} {n : ℕ} (h : P.IsHomogeneous n) : (imP P).IsHomogeneous n := by
  intro d hd
  apply h
  intro h0; apply hd; rw [coeff_imP, h0, Complex.zero_im]

theorem lapC_map (P : R3) : lapC (map Complex.ofRealHom P) = map Complex.ofRealHom (lap P) := by
  rw [lapC_apply, lap_apply, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [pderiv_map, pderiv_map]

/-! ### Evaluating `Q_k` at special points -/

theorem eval_Qk (x : Fin 3 → ℂ) (ℓ k : ℕ) : eval x (Qk ℓ k) =
    ((Polynomial.C (x 0 + Complex.I * x 1) + Polynomial.C (2 * x 2) * Polynomial.X +
      Polynomial.C (-x 0 + Complex.I * x 1) * Polynomial.X ^ 2) ^ ℓ).coeff k := by
  rw [Qk, Qpoly, ← Polynomial.coeff_map, Polynomial.map_pow]
  congr 2
  simp [basePoly]

theorem coeff_one_add_pow (a : ℂ) (n k : ℕ) :
    ((1 + Polynomial.C a * Polynomial.X) ^ n).coeff k = n.choose k * a ^ k := by
  rw [add_comm, add_pow, Polynomial.finset_sum_coeff]
  simp only [one_pow, mul_one, mul_pow, ← Polynomial.C_pow]
  simp_rw [mul_comm _ ((n.choose _ : ℕ) : Polynomial ℂ), ← Polynomial.C_eq_natCast, ← mul_assoc,
    ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow]
  by_cases hk : k < n + 1
  · rw [Finset.sum_eq_single k (fun j _ hj => if_neg (Ne.symm hj)) (fun h => absurd (mem_range.mpr hk) h),
      if_pos rfl]
  · rw [Finset.sum_eq_zero (fun j hj => if_neg (by rw [mem_range] at hj; omega)),
      Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- The point `(1/2, −i/2, s)`, where `α = 1`, `β = 0`, `γ = s`. -/
noncomputable def ptA (s : ℂ) : Fin 3 → ℂ := ![1 / 2, -Complex.I / 2, s]

/-- The point `(−1/2, −i/2, s)`, where `α = 0`, `β = 1`, `γ = s`. -/
noncomputable def ptB (s : ℂ) : Fin 3 → ℂ := ![-1 / 2, -Complex.I / 2, s]

theorem eval_Qk_ptA (ℓ k : ℕ) (s : ℂ) : eval (ptA s) (Qk ℓ k) = ℓ.choose k * (2 * s) ^ k := by
  rw [eval_Qk, ← coeff_one_add_pow]
  congr 2
  simp only [ptA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  have h1 : (1 / 2 : ℂ) + Complex.I * (-Complex.I / 2) = 1 := by
    ring_nf; rw [Complex.I_sq]; ring
  have h2 : -(1 / 2 : ℂ) + Complex.I * (-Complex.I / 2) = 0 := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [h1, h2]
  simp

theorem eval_Qk_ptB (ℓ k : ℕ) (s : ℂ) (hk : ℓ ≤ k) :
    eval (ptB s) (Qk ℓ k) = ℓ.choose (k - ℓ) * (2 * s) ^ (2 * ℓ - k) := by
  rw [eval_Qk]
  simp only [ptB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  have h1 : (-1 / 2 : ℂ) + Complex.I * (-Complex.I / 2) = 0 := by
    ring_nf; rw [Complex.I_sq]; ring
  have h2 : -(-1 / 2 : ℂ) + Complex.I * (-Complex.I / 2) = 1 := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [h1, h2, map_zero, map_one, zero_add, one_mul,
    show Polynomial.C (2 * s) * Polynomial.X + Polynomial.X ^ 2 =
      Polynomial.X * (Polynomial.X + Polynomial.C (2 * s)) by ring, mul_pow,
    show k = (k - ℓ) + ℓ by omega, Polynomial.coeff_X_pow_mul', if_pos (by omega),
    show k - ℓ + ℓ - ℓ = k - ℓ by omega, Polynomial.coeff_X_add_C_pow]
  by_cases hkl : k - ℓ ≤ ℓ
  · rw [show ℓ - (k - ℓ) = 2 * ℓ - (k - ℓ + ℓ) by omega]; ring
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

/-- Polynomial identity: if `∑ c_k s^{e_k} = 0` for all `s` with distinct exponents, all `c_k = 0`. -/
theorem coeffs_zero_of_poly {ι : Type*} (S : Finset ι) (c : ι → ℂ) (e : ι → ℕ)
    (he : Set.InjOn e S) (h : ∀ s : ℂ, ∑ k ∈ S, c k * s ^ e k = 0) : ∀ k ∈ S, c k = 0 := by
  set p : Polynomial ℂ := ∑ k ∈ S, Polynomial.C (c k) * Polynomial.X ^ e k with hp
  have hp0 : p = 0 := by
    apply Polynomial.funext
    intro s
    rw [hp, Polynomial.eval_finset_sum, Polynomial.eval_zero]
    simpa using h s
  intro k hk
  have := congrArg (fun q => q.coeff (e k)) hp0
  simp only [hp, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero]
    at this
  rw [Finset.sum_eq_single k (fun j hj hjk => if_neg (fun h => hjk (he hj hk h.symm)))
    (fun h => absurd hk h), if_pos rfl] at this
  exact this

/-- **The `2ℓ+1` polynomials `Q_k` are linearly independent.** -/
theorem linearIndependent_Qk (ℓ : ℕ) :
    LinearIndependent ℂ (fun k : Fin (2 * ℓ + 1) => Qk ℓ k) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hev : ∀ x, ∑ k : Fin (2 * ℓ + 1), g k * eval x (Qk ℓ k) = 0 := by
    intro x
    have := congrArg (eval x) hg
    simpa [map_sum, smul_eq_mul] using this
  -- indices `k ≤ ℓ` from the points `ptA s`
  have hlow : ∀ k : Fin (2 * ℓ + 1), (k : ℕ) ≤ ℓ → g k = 0 := by
    have h := coeffs_zero_of_poly (Finset.univ.filter fun k : Fin (2 * ℓ + 1) => (k : ℕ) ≤ ℓ)
      (fun k => g k * ℓ.choose k * 2 ^ (k : ℕ)) (fun k => k)
      (fun a _ b _ hab => Fin.ext hab) (fun s => by
        have := hev (ptA s)
        simp only [eval_Qk_ptA] at this
        rw [← this, Finset.sum_filter]
        refine sum_congr rfl fun k _ => ?_
        split_ifs with hk
        · ring
        · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp)
    intro k hk
    have := h k (by simp [hk])
    have hc : (ℓ.choose k : ℂ) * 2 ^ (k : ℕ) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast (Nat.choose_pos hk).ne') (pow_ne_zero _ two_ne_zero)
    rw [mul_assoc] at this
    exact (mul_eq_zero.mp this).resolve_right hc
  -- indices `k ≥ ℓ` from the points `ptB s`
  have hhigh : ∀ k : Fin (2 * ℓ + 1), ℓ ≤ (k : ℕ) → g k = 0 := by
    have h := coeffs_zero_of_poly (Finset.univ.filter fun k : Fin (2 * ℓ + 1) => ℓ ≤ (k : ℕ))
      (fun k => g k * ℓ.choose (k - ℓ) * 2 ^ (2 * ℓ - k)) (fun k => 2 * ℓ - k)
      (fun a ha b hb hab => by
        simp only [coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hb
        have := a.2; have := b.2
        exact Fin.ext (by simp only at hab; omega)) (fun s => by
        have := hev (ptB s)
        rw [← this, Finset.sum_filter]
        refine sum_congr rfl fun k _ => ?_
        split_ifs with hk
        · rw [eval_Qk_ptB ℓ k s hk]; ring
        · rw [hlow k (by omega), zero_mul])
    intro k hk
    have := h k (by simp [hk])
    have h1 : (ℓ.choose (k - ℓ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by have := k.2; omega)).ne'
    have h2 : (2 : ℂ) ^ (2 * ℓ - (k : ℕ)) ≠ 0 := pow_ne_zero _ two_ne_zero
    rw [mul_assoc] at this
    exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero h1 h2)
  intro k
  rcases le_total (k : ℕ) ℓ with hk | hk
  · exact hlow k hk
  · exact hhigh k hk

end ThreeSquares.Duke
