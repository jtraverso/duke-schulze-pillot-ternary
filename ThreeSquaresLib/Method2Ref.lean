/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Method2Sum

/-!
# Method 2 when the levels are coprime to the non-summed variable

Then `gcd(m (p₂ − p₁), p₁p₂b) = gcd(p₂ − p₁, b)` and `sfp(p₁p₂b) = sfp(b)`, and the Weil constant of the
modulus `p₁p₂b` loses only `4P` (`klC_N_le'`, `method2_bound'`).
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset

theorem sfp_prime {p : ℕ} (hp : p.Prime) : sfp p = 1 := by
  have := sfp_prime_pow hp 1; simpa using this

theorem gcd_mul_coprime_right (d x b : ℕ) (h : d.Coprime x) : Nat.gcd d (x * b) = Nat.gcd d b :=
  Nat.Coprime.gcd_mul_left_cancel_right b (Nat.Coprime.symm h) |> fun h' => by
    rw [Nat.gcd_comm, Nat.Coprime.gcd_mul_left_cancel b (Nat.Coprime.symm h), Nat.gcd_comm]

/-- **The Weil constant of `p₁ p₂ b`, coprime case.** -/
theorem klC_N_le' (P p₁ p₂ b : ℕ) (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂) (hP₁ : p₁ ≤ P)
    (hP₂ : p₂ ≤ P) (hb : 0 < b) (hc₁ : p₁.Coprime b) (hc₂ : p₂.Coprime b) (m : ℤ)
    (hm : Nat.Coprime m.natAbs (p₁ * p₂ * b)) (u : ZMod (p₁ * p₂ * b)) [NeZero (p₁ * p₂ * b)]
    (hu : IsUnit u) :
    klC (p₁ * p₂ * b) (((m * ((p₂ : ℤ) - p₁) : ℤ) : ZMod (p₁ * p₂ * b)) * u) ≤
      4 * (P : ℝ) * (2 ^ b.primeFactors.card * Real.sqrt b * Real.sqrt (sfp b) *
        Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b)) := by
  unfold klC
  set d : ℤ := (p₂ : ℤ) - p₁
  have hb0 : b ≠ 0 := hb.ne'
  have h12 : p₁.Coprime p₂ := (Nat.coprime_primes hp₁ hp₂).mpr hne
  have hd12 : Nat.Coprime d.natAbs (p₁ * p₂) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp₁]
      intro h
      have h' : (p₁ : ℤ) ∣ d := Int.natCast_dvd.mpr h
      have : (p₁ : ℤ) ∣ (p₂ : ℤ) := by
        have := dvd_add h' (dvd_refl (p₁ : ℤ)); simp only [d, sub_add_cancel] at this; exact this
      exact hne ((Nat.prime_dvd_prime_iff_eq hp₁ hp₂).mp (Int.natCast_dvd_natCast.mp this))
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp₂]
      intro h
      have h' : (p₂ : ℤ) ∣ d := Int.natCast_dvd.mpr h
      have : (p₂ : ℤ) ∣ (p₁ : ℤ) := by
        have := dvd_sub (dvd_refl (p₂ : ℤ)) h'; simp only [d, sub_sub_cancel] at this; exact this
      exact hne ((Nat.prime_dvd_prime_iff_eq hp₂ hp₁).mp (Int.natCast_dvd_natCast.mp this)).symm
  have hg : Nat.gcd ((((m * d : ℤ) : ZMod (p₁ * p₂ * b)) * u).val) (p₁ * p₂ * b) = Int.gcd d b := by
    rw [mul_comm (((m * d : ℤ)) : ZMod (p₁ * p₂ * b)) u, gcd_val_mul_unit _ _ hu, gcd_val_intCast]
    rw [Int.gcd_eq_natAbs, Int.natAbs_mul, Int.natAbs_natCast, Nat.Coprime.gcd_mul_left_cancel _ hm,
      gcd_mul_coprime_right _ _ _ hd12, Int.gcd_eq_natAbs, Int.natAbs_natCast]
  have hs : sfp (p₁ * p₂ * b) = sfp b := by
    rw [sfp_mul (Nat.mul_ne_zero hp₁.ne_zero hp₂.ne_zero) hb0 (Nat.coprime_mul_iff_left.mpr ⟨hc₁, hc₂⟩),
      sfp_mul hp₁.ne_zero hp₂.ne_zero h12, sfp_prime hp₁, sfp_prime hp₂]; ring
  have hω : (p₁ * p₂ * b).primeFactors.card ≤ b.primeFactors.card + 2 := by
    have e1 := card_primeFactors_mul_le (Nat.mul_ne_zero hp₁.ne_zero hp₂.ne_zero) hb0
    have e2 := card_primeFactors_mul_le hp₁.ne_zero hp₂.ne_zero
    simp only [hp₁.primeFactors, hp₂.primeFactors, Finset.card_singleton] at e2
    omega
  have hP : (p₁ * p₂ : ℝ) ≤ (P : ℝ) ^ 2 := by
    have : (p₁ : ℝ) ≤ P := by exact_mod_cast hP₁
    have : (p₂ : ℝ) ≤ P := by exact_mod_cast hP₂
    have := (Nat.cast_nonneg p₁ : (0 : ℝ) ≤ p₁); have := (Nat.cast_nonneg p₂ : (0 : ℝ) ≤ p₂)
    nlinarith
  have a1 : (2 : ℝ) ^ (p₁ * p₂ * b).primeFactors.card ≤ 4 * 2 ^ b.primeFactors.card := by
    calc (2 : ℝ) ^ (p₁ * p₂ * b).primeFactors.card ≤ 2 ^ (b.primeFactors.card + 2) :=
          pow_le_pow_right₀ (by norm_num) hω
      _ = 4 * 2 ^ b.primeFactors.card := by rw [pow_add]; ring
  have a2 : Real.sqrt ((p₁ * p₂ * b : ℕ) : ℝ) ≤ P * Real.sqrt b := by
    rw [show ((p₁ * p₂ * b : ℕ) : ℝ) = (p₁ * p₂ : ℝ) * b by push_cast; ring, Real.sqrt_mul (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    rw [show (P : ℝ) = Real.sqrt ((P : ℝ) ^ 2) by rw [Real.sqrt_sq (Nat.cast_nonneg _)]]
    exact Real.sqrt_le_sqrt hP
  rw [hg, hs]
  calc (2 : ℝ) ^ (p₁ * p₂ * b).primeFactors.card * Real.sqrt ((p₁ * p₂ * b : ℕ) : ℝ) *
        Real.sqrt (Int.gcd d b) * Real.sqrt (sfp b)
      ≤ (4 * 2 ^ b.primeFactors.card) * (P * Real.sqrt b) * Real.sqrt (Int.gcd d b) * Real.sqrt (sfp b) := by
        gcongr
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- **Method 2, explicit form, levels coprime to the non-summed variable.** -/
theorem method2_bound' (Ps : Finset ℕ) (P₀ P : ℕ) (hP₀ : 0 < P₀) (r y Y : ℕ) (W : ℕ → ℂ) {W₀ W₁ : ℝ} (hW : SmoothW W W₀ W₁)
    (A t₁ : ℕ) (Bs : Finset ℕ) (hr : 0 < r) (hrA : r ≤ A) (m : ℤ) (α β : ℕ → ℂ)
    (hα : ∀ a, ‖α a‖ ≤ 1) (hβ : ∀ b, ‖β b‖ ≤ 1) (hPs : ∀ p ∈ Ps, p.Prime ∧ P₀ ≤ p ∧ p ≤ P)
    (hPb : ∀ p ∈ Ps, ∀ b ∈ Bs, p.Coprime b)
    (hrP : ∀ p ∈ Ps, r.Coprime p) (hmP : ∀ p ∈ Ps, Nat.Coprime m.natAbs p)
    (hB : ∀ b ∈ Bs, r.Coprime b ∧ 0 < b ∧
      Nat.Coprime m.natAbs b) :
    (∑ p ∈ Ps, ‖∑ a ∈ (Ioc A (2 * A)).filter (fun a => a % r = t₁ % r),
        ∑ b ∈ Bs, α a * β b * ker2 r y Y W m p a b‖) ^ 2 ≤
      (((Ioc A (2 * A)).filter (fun a => a % r = t₁ % r)).card *
        (Bs).card : ℝ) *
      ((Ps.card * (Bs).card *
          ((Ioc A (2 * A)).filter (fun a => a % r = t₁ % r)).card : ℝ) * W₀ ^ 2 +
        (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (4 * (P : ℝ) ^ 3) *
          ∑ b ∈ Bs,
            ((((2 * A / r + 1 : ℕ) : ℝ) / ((P₀ : ℝ) ^ 2 * b) + (1 + Real.log ((P : ℝ) ^ 2 * b))) *
              (2 ^ b.primeFactors.card * Real.sqrt b * Real.sqrt (sfp b) * b.divisors.card))) := by
  have hPc : ∀ p₁ ∈ Ps, ∀ p₂ ∈ Ps, p₁ ≠ p₂ → p₁.Coprime p₂ := fun p₁ h₁ p₂ h₂ hne =>
    (Nat.coprime_primes (hPs p₁ h₁).1 (hPs p₂ h₂).1).mpr hne
  refine (method2 Ps r y Y W hW A t₁ Bs hr hrA m α β hα hβ (fun p hp => (hPs p hp).1.pos) hPc hrP
    (fun b hb => ⟨(hB b hb).1, (hB b hb).2.1⟩)).trans ?_
  have hW0 := hW.W₀_nonneg
  have hW1 := hW.W₁_nonneg
  refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  obtain ⟨hrb, hb0, hmb⟩ := hB b hb
  set F := (((2 * A / r + 1 : ℕ) : ℝ) / ((P₀ : ℝ) ^ 2 * b) + (1 + Real.log ((P : ℝ) ^ 2 * b))) with hFdef
  set K := (2 : ℝ) ^ b.primeFactors.card * Real.sqrt b * Real.sqrt (sfp b) with hKdef
  have hK : 0 ≤ K := by positivity
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb0
  have hterm : ∀ p₁ ∈ Ps, ∀ p₂ ∈ Ps.erase p₁,
      (3 * W₀ ^ 2 + 4 * W₀ * W₁) * ((((2 * A / r + 1 : ℕ) : ℝ) / (p₁ * p₂ * b : ℕ) +
        (1 + Real.log (p₁ * p₂ * b : ℕ))) *
        @klC (p₁ * p₂ * b) ((@Int.cast (ZMod (p₁ * p₂ * b)) _ (m * ((p₂ : ℤ) - p₁))) *
          ((@Nat.cast (ZMod (p₁ * p₂ * b)) _ (r * r)))⁻¹)) ≤
      (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (F * (4 * (P : ℝ) * (K * Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b)))) := by
    intro p₁ hp₁ p₂ hp₂
    have hp₂' := Finset.mem_of_mem_erase hp₂
    obtain ⟨pr₁, hP₀₁, hP₁⟩ := hPs p₁ hp₁
    obtain ⟨pr₂, hP₀₂, hP₂⟩ := hPs p₂ hp₂'
    haveI : NeZero (p₁ * p₂ * b) := ⟨by have := pr₁.pos; have := pr₂.pos; positivity⟩
    have hN1 : (1 : ℝ) ≤ ((p₁ * p₂ * b : ℕ) : ℝ) := by
      have : 1 ≤ p₁ * p₂ * b := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
      exact_mod_cast this
    have hru : IsUnit (((r * r : ℕ) : ZMod (p₁ * p₂ * b))) := by
      rw [ZMod.isUnit_iff_coprime]
      have h1 := hrP p₁ hp₁; have h2 := hrP p₂ hp₂'
      have h3 : r.Coprime (p₁ * p₂ * b) := Nat.Coprime.mul_right (Nat.Coprime.mul_right h1 h2) hrb
      exact Nat.coprime_mul_iff_left.mpr ⟨h3, h3⟩
    have hmN : Nat.Coprime m.natAbs (p₁ * p₂ * b) :=
      Nat.Coprime.mul_right (Nat.Coprime.mul_right (hmP p₁ hp₁) (hmP p₂ hp₂')) hmb
    have hne : p₁ ≠ p₂ := (Finset.ne_of_mem_erase hp₂).symm
    have hkl := klC_N_le' P p₁ p₂ b pr₁ pr₂ hne hP₁ hP₂ hb0 (hPb p₁ hp₁ b hb) (hPb p₂ hp₂' b hb) m hmN _
      (isUnit_inv_of_isUnit hru)
    have hF : (((2 * A / r + 1 : ℕ) : ℝ) / (p₁ * p₂ * b : ℕ) + (1 + Real.log (p₁ * p₂ * b : ℕ))) ≤ F := by
      simp only [hFdef]
      have hle : ((p₁ * p₂ * b : ℕ) : ℝ) ≤ (P : ℝ) ^ 2 * b := by
        have a : (p₁ : ℝ) ≤ P := by exact_mod_cast hP₁
        have c : (p₂ : ℝ) ≤ P := by exact_mod_cast hP₂
        push_cast
        have := (Nat.cast_nonneg p₁ : (0 : ℝ) ≤ p₁); have := (Nat.cast_nonneg p₂ : (0 : ℝ) ≤ p₂)
        have hb' : (0 : ℝ) ≤ b := by linarith
        have : (p₁ : ℝ) * p₂ ≤ (P : ℝ) ^ 2 := by nlinarith
        nlinarith
      have hge : (P₀ : ℝ) ^ 2 * b ≤ ((p₁ * p₂ * b : ℕ) : ℝ) := by
        have a : (P₀ : ℝ) ≤ p₁ := by exact_mod_cast hP₀₁
        have c : (P₀ : ℝ) ≤ p₂ := by exact_mod_cast hP₀₂
        push_cast
        have : (0 : ℝ) ≤ P₀ := Nat.cast_nonneg _
        have hb' : (0 : ℝ) ≤ b := Nat.cast_nonneg _
        have : (P₀ : ℝ) ^ 2 ≤ p₁ * p₂ := by nlinarith
        nlinarith
      have hP0' : (0 : ℝ) < (P₀ : ℝ) ^ 2 * b := by
        have : (0 : ℝ) < P₀ := by exact_mod_cast hP₀
        have : (0 : ℝ) < b := by exact_mod_cast hb0
        positivity
      gcongr
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc _ ≤ F * @klC (p₁ * p₂ * b) ((@Int.cast (ZMod (p₁ * p₂ * b)) _ (m * ((p₂ : ℤ) - p₁))) *
          ((@Nat.cast (ZMod (p₁ * p₂ * b)) _ (r * r)))⁻¹) :=
          mul_le_mul_of_nonneg_right hF (klC_nonneg _ _)
      _ ≤ F * (4 * (P : ℝ) * (K * Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b))) := by
          refine mul_le_mul_of_nonneg_left (le_trans hkl (le_of_eq ?_)) ?_
          · rw [hKdef]
          · have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast le_trans pr₁.one_lt.le hP₁
            have : 0 ≤ Real.log ((P : ℝ) ^ 2 * b) := Real.log_nonneg (by nlinarith)
            simp only [hFdef]
            positivity
  refine le_trans (Finset.sum_le_sum fun p₁ hp₁ => Finset.sum_le_sum fun p₂ hp₂ => hterm p₁ hp₁ p₂ hp₂) ?_
  have hPs' : ∀ p ∈ Ps, 1 ≤ p ∧ p ≤ P := fun p hp => ⟨(hPs p hp).1.one_lt.le, (hPs p hp).2.2⟩
  have hlogP : 0 ≤ Real.log ((P : ℝ) ^ 2 * b) := by
    rcases Nat.eq_zero_or_pos P with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ P := by exact_mod_cast h
      exact Real.log_nonneg (by nlinarith)
  have hF0 : 0 ≤ F := by simp only [hFdef]; positivity
  calc ∑ p₁ ∈ Ps, ∑ p₂ ∈ Ps.erase p₁,
          (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (F * (4 * (P : ℝ) * (K * Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b))))
        = (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (F * (4 * (P : ℝ) * K)) *
            ∑ p₁ ∈ Ps, ∑ p₂ ∈ Ps.erase p₁, Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p₁ _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p₂ _ => ?_; ring
      _ ≤ (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (F * (4 * (P : ℝ) * K)) * ((P : ℝ) ^ 2 * b.divisors.card) :=
          mul_le_mul_of_nonneg_left (sum_sqrt_gcd_le Ps P b hb0.ne' hPs') (by positivity)
      _ = _ := by rw [hKdef]; ring

end ThreeSquares
