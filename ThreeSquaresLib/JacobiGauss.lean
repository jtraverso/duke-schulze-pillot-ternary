/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.PrimeT
public import ThreeSquaresLib.SqfT
public import rml.weil.crt_and_completion

/-!
# Gauss sums of the Jacobi symbol and the Pólya–Vinogradov inequality

For odd squarefree `n`:
* `jg_eq`: `G_n(h) = J(h | n) · G_n(1)` and `normSq_jg_one`: `|G_n(1)|² = n`;
* `polya_vinogradov`: `|∑_{j < L} J(t + m j | n)| ≤ √n (1 + log n)` for `m` coprime to `n`, `n > 1`.
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset

/-- The Jacobi symbol `J(x | n)` on `ℤ/n`. -/
noncomputable def jac (n : ℕ) (x : ZMod n) : ℂ := (jacobiSym (x.val : ℤ) n : ℂ)

theorem jac_intCast (n : ℕ) [NeZero n] (a : ℤ) : jac n (a : ZMod n) = (jacobiSym a n : ℂ) := by
  unfold jac
  rw [ZMod.val_intCast, ← jacobiSym.mod_left]

theorem intCast_val_eq (n : ℕ) [NeZero n] (x : ZMod n) : (((x.val : ℤ)) : ZMod n) = x := by
  simp

theorem jac_mul (n : ℕ) [NeZero n] (x y : ZMod n) : jac n (x * y) = jac n x * jac n y := by
  rw [← intCast_val_eq n x, ← intCast_val_eq n y, ← Int.cast_mul, jac_intCast, jac_intCast,
    jac_intCast, jacobiSym.mul_left]
  push_cast; ring

/-- The Gauss sum `G_n(h) = ∑_x J(x | n) e(hx/n)`. -/
noncomputable def jg (n : ℕ) [NeZero n] (h : ℤ) : ℂ :=
  ∑ x : ZMod n, jac n x * stdAddChar ((h : ZMod n) * x)

theorem jac_prime {p : ℕ} [Fact p.Prime] (x : ZMod p) : jac p x = PT.chi p x := by
  rw [← intCast_val_eq p x, jac_intCast, chi_eq_jacobi]

theorem jg_prime {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (h : ℤ) :
    jg p h = (jacobiSym h p : ℂ) * PT.gs p := by
  rw [← chi_eq_jacobi]
  unfold jg
  simp_rw [jac_prime]
  by_cases h0 : (h : ZMod p) = 0
  · rw [h0]
    simp only [zero_mul, AddChar.map_zero_eq_one, mul_one]
    rw [PT.chi_zero, zero_mul]
    exact MulChar.sum_eq_zero_of_ne_one (PT.chi_ne_one hp2)
  · have hu : IsUnit (h : ZMod p) := Ne.isUnit h0
    have hg := gaussSum_mulShift (PT.chi p) (PT.psi p) hu.unit
    have hsq : PT.chi p (h : ZMod p) * PT.chi p (h : ZMod p) = 1 := by
      rw [← sq]; exact PT.chi_sq h0
    have hG : gaussSum (PT.chi p) ((PT.psi p).mulShift (h : ZMod p)) =
        ∑ x : ZMod p, PT.chi p x * stdAddChar ((h : ZMod p) * x) := by
      unfold gaussSum; rfl
    rw [← hG]
    unfold PT.gs
    rw [← hg]
    simp only [IsUnit.unit_spec]
    linear_combination (-(gaussSum (PT.chi p) ((PT.psi p).mulShift (h : ZMod p)))) * hsq

theorem norm_chi_eq_one {p : ℕ} [hp : Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) : ‖PT.chi p a‖ = 1 := by
  have hsq := PT.chi_sq (p := p) ha
  have : ‖PT.chi p a‖ ^ 2 = 1 := by rw [← norm_pow, hsq, norm_one]
  nlinarith [norm_nonneg (PT.chi p a)]

theorem normSq_gs {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) : Complex.normSq (PT.gs p) = p := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  have h := PT.gs_sq (p := p) hp2
  have hc := norm_chi_eq_one (p := p) (a := -1) (neg_ne_zero.mpr (one_ne_zero (α := ZMod p)))
  have h1 : ‖PT.gs p‖ ^ 2 = p := by
    rw [← norm_pow, h, norm_mul, Complex.norm_natCast]
    rw [norm_chi_eq_one, one_mul]
    exact neg_ne_zero.mpr (one_ne_zero (α := ZMod p))
  rw [Complex.normSq_eq_norm_sq, h1]

/-- **CRT for `G`.** -/
theorem jg_mul {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂] (hc : n₁.Coprime n₂) (h : ℤ) :
    jg (n₁ * n₂) h = (jacobiSym n₂ n₁ : ℂ) * (jacobiSym n₁ n₂ : ℂ) * jg n₁ h * jg n₂ h := by
  classical
  set Φ : ZMod n₁ × ZMod n₂ → ZMod (n₁ * n₂) := fun y =>
    (((n₂ : ℤ) * (y.1.val : ℤ) + (n₁ : ℤ) * (y.2.val : ℤ) : ℤ) : ZMod (n₁ * n₂))
  have hd1 : n₁ ∣ n₁ * n₂ := dvd_mul_right _ _
  have hd2 : n₂ ∣ n₁ * n₂ := dvd_mul_left _ _
  set c1 := ZMod.castHom hd1 (ZMod n₁)
  set c2 := ZMod.castHom hd2 (ZMod n₂)
  have hc1 : ∀ y, c1 (Φ y) = (n₂ : ZMod n₁) * y.1 := by
    intro y; simp only [Φ, map_intCast]; push_cast; simp
  have hc2 : ∀ y, c2 (Φ y) = (n₁ : ZMod n₂) * y.2 := by
    intro y; simp only [Φ, map_intCast]; push_cast; simp
  have hu1 : IsUnit (n₂ : ZMod n₁) := (ZMod.unitOfCoprime n₂ hc.symm).isUnit
  have hu2 : IsUnit (n₁ : ZMod n₂) := (ZMod.unitOfCoprime n₁ hc).isUnit
  have hinj : Function.Injective Φ := by
    intro y z hyz
    have e1 := congrArg c1 hyz
    have e2 := congrArg c2 hyz
    rw [hc1, hc1] at e1; rw [hc2, hc2] at e2
    exact Prod.ext (hu1.mul_left_cancel e1) (hu2.mul_left_cancel e2)
  have hbij : Function.Bijective Φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp [ZMod.card]⟩
  have hjac : ∀ y, jac (n₁ * n₂) (Φ y) =
      (jacobiSym n₂ n₁ : ℂ) * (jacobiSym n₁ n₂ : ℂ) * jac n₁ y.1 * jac n₂ y.2 := by
    intro y
    simp only [Φ]
    rw [jac_intCast, jacobiSym.mul_right]
    have e1 : (jacobiSym ((n₂ : ℤ) * (y.1.val : ℤ) + (n₁ : ℤ) * (y.2.val : ℤ)) n₁ : ℂ) =
        jac n₁ ((n₂ : ZMod n₁) * y.1) := by
      rw [← jac_intCast]; congr 1; push_cast; simp
    have e2 : (jacobiSym ((n₂ : ℤ) * (y.1.val : ℤ) + (n₁ : ℤ) * (y.2.val : ℤ)) n₂ : ℂ) =
        jac n₂ ((n₁ : ZMod n₂) * y.2) := by
      rw [← jac_intCast]; congr 1; push_cast; simp
    push_cast
    rw [e1, e2, jac_mul, jac_mul]
    have f1 : jac n₁ (n₂ : ZMod n₁) = (jacobiSym n₂ n₁ : ℂ) := by
      rw [show ((n₂ : ℕ) : ZMod n₁) = (((n₂ : ℤ)) : ZMod n₁) by push_cast; rfl, jac_intCast]
    have f2 : jac n₂ (n₁ : ZMod n₂) = (jacobiSym n₁ n₂ : ℂ) := by
      rw [show ((n₁ : ℕ) : ZMod n₂) = (((n₁ : ℤ)) : ZMod n₂) by push_cast; rfl, jac_intCast]
    rw [f1, f2]; ring
  have hchar : ∀ y, (stdAddChar ((h : ZMod (n₁ * n₂)) * Φ y) : ℂ) =
      stdAddChar ((h : ZMod n₁) * y.1) * stdAddChar ((h : ZMod n₂) * y.2) := by
    intro y
    simp only [Φ]
    rw [← Int.cast_mul, ZMod.stdAddChar_coe,
      show (h : ZMod n₁) * y.1 = ((h * (y.1.val : ℤ) : ℤ) : ZMod n₁) by push_cast; simp,
      show (h : ZMod n₂) * y.2 = ((h * (y.2.val : ℤ) : ℤ) : ZMod n₂) by push_cast; simp,
      ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
    congr 1
    have h1 : (n₁ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n₁
    have h2 : (n₂ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n₂
    push_cast
    field_simp
  unfold jg
  rw [← hbij.sum_comp, Fintype.sum_prod_type]
  simp_rw [hjac, hchar]
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y1 _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y2 _ => ?_
  ring

theorem jacobiSym_sq_eq_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : (jacobiSym a b : ℂ) ^ 2 = 1 := by
  rcases jacobiSym.eq_one_or_neg_one h with h1 | h1 <;> rw [h1] <;> norm_num

/-- **`G_n(h) = J(h | n) G_n(1)` and `|G_n(1)|² = n`** for odd squarefree `n`. -/
theorem jg_sqf_aux : ∀ n : ℕ, ∀ hn : n ≠ 0, Squarefree n → Odd n →
    (haveI : NeZero n := ⟨hn⟩
     (∀ h : ℤ, jg n h = (jacobiSym h n : ℂ) * jg n 1) ∧ Complex.normSq (jg n 1) = n) := by
  intro n
  induction n using Nat.recOnPrimeCoprime with
  | zero => intro h; exact absurd rfl h
  | prime_pow p k hp =>
    intro hn hsq hodd
    haveI : Fact p.Prime := ⟨hp⟩
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · -- `n = 1`
        have key : ∀ (q : ℕ) [NeZero q], q = 1 → (∀ h : ℤ, jg q h = (jacobiSym h q : ℂ) * jg q 1) ∧
            Complex.normSq (jg q 1) = q := by
          intro q _ hq; subst hq
          have hz : ∀ z : ZMod 1, z = 0 := fun z => Subsingleton.elim _ _
          refine ⟨fun h => ?_, ?_⟩ <;> simp [jg, jac, hz, jacobiSym.one_right]
        exact key _ (pow_zero p)
      · have hp2 : p ≠ 2 := by
          rintro rfl; norm_num at hodd
        have key : ∀ (q : ℕ) [NeZero q], q = p → (∀ h : ℤ, jg q h = (jacobiSym h q : ℂ) * jg q 1) ∧
            Complex.normSq (jg q 1) = q := by
          intro q _ hq; subst hq
          refine ⟨fun h => ?_, ?_⟩
          · rw [jg_prime hp2, jg_prime hp2, jacobiSym.one_left]; push_cast; ring
          · rw [jg_prime hp2, jacobiSym.one_left]; push_cast; rw [one_mul, normSq_gs hp2]
        exact key _ (pow_one p)
    · exfalso
      have : p * p ∣ p ^ k := by
        rw [← sq]; exact pow_dvd_pow p hk
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p this))
  | coprime a b ha hb hab iha ihb =>
    intro hn hsq hodd
    haveI : NeZero a := ⟨by omega⟩
    haveI : NeZero b := ⟨by omega⟩
    obtain ⟨ha1, ha2⟩ := iha (by omega) (hsq.of_mul_left) (Nat.Odd.of_mul_left hodd)
    obtain ⟨hb1, hb2⟩ := ihb (by omega) (hsq.of_mul_right) (Nat.Odd.of_mul_right hodd)
    have hJ : (jacobiSym b a : ℂ) ^ 2 = 1 := jacobiSym_sq_eq_one (by
      rw [Int.gcd_natCast_natCast]; exact hab.symm)
    have hJ' : (jacobiSym a b : ℂ) ^ 2 = 1 := jacobiSym_sq_eq_one (by
      rw [Int.gcd_natCast_natCast]; exact hab)
    refine ⟨fun h => ?_, ?_⟩
    · rw [jg_mul hab, jg_mul hab, ha1, hb1, ha1 1, hb1 1, jacobiSym.mul_right]
      simp only [jacobiSym.one_left]
      push_cast; ring
    · rw [jg_mul hab, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul, ha2, hb2]
      have n1 : Complex.normSq (jacobiSym b a : ℂ) = 1 := by
        rw [Complex.normSq_eq_norm_sq, ← norm_pow, hJ, norm_one]
      have n2 : Complex.normSq (jacobiSym a b : ℂ) = 1 := by
        rw [Complex.normSq_eq_norm_sq, ← norm_pow, hJ', norm_one]
      rw [n1, n2]; push_cast; ring

theorem jg_eq {n : ℕ} [NeZero n] (hsq : Squarefree n) (hodd : Odd n) (h : ℤ) :
    jg n h = (jacobiSym h n : ℂ) * jg n 1 :=
  (jg_sqf_aux n (NeZero.ne n) hsq hodd).1 h

theorem normSq_jg_one {n : ℕ} [NeZero n] (hsq : Squarefree n) (hodd : Odd n) :
    Complex.normSq (jg n 1) = n :=
  (jg_sqf_aux n (NeZero.ne n) hsq hodd).2

theorem norm_jg_one {n : ℕ} [NeZero n] (hsq : Squarefree n) (hodd : Odd n) :
    ‖jg n 1‖ = Real.sqrt n := by
  rw [← normSq_jg_one hsq hodd, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- **Pólya–Vinogradov** in arithmetic progressions. -/
theorem polya_vinogradov {n : ℕ} [NeZero n] (hsq : Squarefree n) (hodd : Odd n) (hn1 : 1 < n)
    (m t : ℤ) (hm : IsUnit (m : ZMod n)) (L : ℕ) :
    ‖∑ j ∈ range L, (jacobiSym (t + m * j) n : ℂ)‖ ≤ Real.sqrt n * (1 + Real.log n) := by
  classical
  set G := jg n 1
  have hG : ‖G‖ = Real.sqrt n := norm_jg_one hsq hodd
  have hGpos : 0 < ‖G‖ := by rw [hG]; exact Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos n)
  have hG0 : G ≠ 0 := norm_pos_iff.mp hGpos
  -- expansion `J(x | n) = G⁻¹ ∑_y J(y | n) e(xy/n)`
  have hexp : ∀ x : ℤ, (jacobiSym x n : ℂ) = G⁻¹ * ∑ y : ZMod n, jac n y * stdAddChar ((x : ZMod n) * y) := by
    intro x
    have h1 := jg_eq hsq hodd x
    show _ = G⁻¹ * jg n x
    rw [h1, mul_comm, mul_assoc, mul_inv_cancel₀ hG0, mul_one]
  simp_rw [hexp]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hterm : ∀ y : ZMod n, ∑ j ∈ range L, jac n y * stdAddChar ((((t + m * j : ℤ)) : ZMod n) * y) =
      jac n y * stdAddChar ((t : ZMod n) * y) * ∑ j ∈ range L, (stdAddChar ((m : ZMod n) * y)) ^ j := by
    intro y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← AddChar.map_nsmul_eq_pow, mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    push_cast; rw [nsmul_eq_mul]; push_cast; ring
  simp_rw [hterm]
  rw [norm_mul, norm_inv, hG]
  have hjac0 : jac n 0 = 0 := by
    unfold jac; rw [ZMod.val_zero]; push_cast; rw [jacobiSym.zero_left hn1]; simp
  have hbound : ‖∑ y : ZMod n, jac n y * stdAddChar ((t : ZMod n) * y) *
      ∑ j ∈ range L, (stdAddChar ((m : ZMod n) * y)) ^ j‖ ≤
      ∑ y : ZMod n, if y = 0 then (0 : ℝ) else
        (n : ℝ) / (2 * RML.ExpSum.Weil.zmodFrequencyDistance ((m : ZMod n) * y)) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    by_cases hy : y = 0
    · rw [if_pos hy, hy, hjac0]; simp
    · rw [if_neg hy, norm_mul, norm_mul]
      have hmy : (m : ZMod n) * y ≠ 0 := by
        intro h0; exact hy ((hm.mul_right_eq_zero).mp h0)
      have hj : ‖jac n y‖ ≤ 1 := by
        unfold jac
        rcases jacobiSym.trichotomy (y.val : ℤ) n with h | h | h <;> rw [h] <;> simp
      have hk := RML.ExpSum.Weil.geometricKernel_norm_le hmy L
      have hc : ‖(stdAddChar ((t : ZMod n) * y) : ℂ)‖ = 1 := RML.ExpSum.Weil.norm_stdAddChar_eq_one _ _
      rw [hc, mul_one]
      calc ‖jac n y‖ * ‖∑ j ∈ range L, (stdAddChar ((m : ZMod n) * y)) ^ j‖
          ≤ 1 * ((n : ℝ) / (2 * RML.ExpSum.Weil.zmodFrequencyDistance ((m : ZMod n) * y))) :=
            mul_le_mul hj hk (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  -- reindex `y ↦ m y`
  have hre : (∑ y : ZMod n, if y = 0 then (0 : ℝ) else
        (n : ℝ) / (2 * RML.ExpSum.Weil.zmodFrequencyDistance ((m : ZMod n) * y))) =
      (n / 2 : ℝ) * ∑ u : ZMod n, if u = 0 then (0 : ℝ) else
        ((RML.ExpSum.Weil.zmodFrequencyDistance u : ℕ) : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    refine Fintype.sum_bijective (fun y => (m : ZMod n) * y) ?_ _ _ fun y => ?_
    · exact ⟨fun a b hab => hm.mul_left_cancel hab, fun u => ⟨hm.unit⁻¹ * u, by
      show (m : ZMod n) * (↑hm.unit⁻¹ * u) = u
      rw [← mul_assoc, hm.mul_val_inv, one_mul]⟩⟩
    · by_cases hy : y = 0
      · simp [hy]
      · have hmy : (m : ZMod n) * y ≠ 0 := by
          intro h0; exact hy ((hm.mul_right_eq_zero).mp h0)
        rw [if_neg hy, if_neg hmy]
        field_simp
  have hmass := RML.ExpSum.Weil.frequencyReciprocalMass_le_log n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  calc (Real.sqrt n)⁻¹ * ‖_‖ ≤ (Real.sqrt n)⁻¹ * ((n / 2 : ℝ) * (2 * (1 + Real.log n))) := by
        refine mul_le_mul_of_nonneg_left (hbound.trans ?_) (by positivity)
        rw [hre]
        exact mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = Real.sqrt n * (1 + Real.log n) := by
        have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
        have hs0 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
        field_simp
        nlinarith [hs]

end ThreeSquares
