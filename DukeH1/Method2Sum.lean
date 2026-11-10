/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.Method2

/-!
# Summing the Weil bounds of Method 2

The modulus is `p₁ p₂ b`; we bound its Weil constant crudely by that of `b` times `4 P⁴`.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open ZMod Finset

theorem sfp_mul_prime_le {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : a ≠ 0) : sfp (p * a) ≤ p ^ 2 * sfp a := by
  obtain ⟨e, a₀, hnd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd ha p hp.one_lt.ne'
  have ha₀ : a₀ ≠ 0 := by rintro rfl; simp at ha
  have hc : ∀ k, (p ^ k).Coprime a₀ := fun k => Nat.Coprime.pow_left _ ((hp.coprime_iff_not_dvd).mpr hnd)
  rw [← mul_assoc, ← pow_succ', sfp_mul (pow_ne_zero _ hp.ne_zero) ha₀ (hc _),
    sfp_mul (pow_ne_zero _ hp.ne_zero) ha₀ (hc _), sfp_prime_pow hp, sfp_prime_pow hp]
  have hs := sfp_pos a₀
  rcases Nat.lt_or_ge e 2 with he | he
  · interval_cases e
    · simp; exact Nat.le_mul_of_pos_left _ (pow_pos hp.pos 2)
    · simp
  · rw [if_neg (by omega), if_neg (by omega), pow_succ]
    have hp2 : p ≤ p ^ 2 := by nlinarith [hp.two_le]
    calc p ^ e * p * sfp a₀ = (p ^ e * sfp a₀) * p := by ring
      _ ≤ (p ^ e * sfp a₀) * p ^ 2 := Nat.mul_le_mul_left _ hp2
      _ = p ^ 2 * (p ^ e * sfp a₀) := by ring

theorem card_primeFactors_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).primeFactors.card ≤ a.primeFactors.card + b.primeFactors.card := by
  rw [Nat.primeFactors_mul ha hb]; exact Finset.card_union_le _ _

/-- **The Weil constant of `p₁ p₂ b`.** -/
theorem klC_N_le (P p₁ p₂ b : ℕ) (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hP₁ : p₁ ≤ P) (hP₂ : p₂ ≤ P)
    (hb : 0 < b) (m : ℤ) (hm : Nat.Coprime m.natAbs (p₁ * p₂ * b)) (u : ZMod (p₁ * p₂ * b))
    [NeZero (p₁ * p₂ * b)] (hu : IsUnit u) :
    klC (p₁ * p₂ * b) (((m * ((p₂ : ℤ) - p₁) : ℤ) : ZMod (p₁ * p₂ * b)) * u) ≤
      4 * (P : ℝ) ^ 4 * (2 ^ b.primeFactors.card * Real.sqrt b * Real.sqrt (sfp b) *
        Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b)) := by
  unfold klC
  set d : ℤ := (p₂ : ℤ) - p₁
  have hb0 : b ≠ 0 := hb.ne'
  -- the gcd
  have hg : Nat.gcd ((((m * d : ℤ) : ZMod (p₁ * p₂ * b)) * u).val) (p₁ * p₂ * b) ≤ Int.gcd d b * (p₁ * p₂) := by
    rw [mul_comm (((m * d : ℤ)) : ZMod (p₁ * p₂ * b)) u, gcd_val_mul_unit _ _ hu, gcd_val_intCast]
    rw [Int.gcd_eq_natAbs, Int.natAbs_mul, Int.natAbs_natCast]
    rw [Nat.Coprime.gcd_mul_left_cancel _ hm]
    have h1 : Nat.gcd d.natAbs (p₁ * p₂ * b) ∣ Nat.gcd d.natAbs (p₁ * p₂) * Nat.gcd d.natAbs b :=
      gcd_mul_dvd_mul_gcd (α := ℕ) _ _ _
    have h2 : 0 < Nat.gcd d.natAbs (p₁ * p₂) * Nat.gcd d.natAbs b :=
      Nat.mul_pos (Nat.gcd_pos_of_pos_right _ (Nat.mul_pos hp₁.pos hp₂.pos))
        (Nat.gcd_pos_of_pos_right _ hb)
    have h3 := Nat.le_of_dvd h2 h1
    have h4 : Nat.gcd d.natAbs (p₁ * p₂) ≤ p₁ * p₂ :=
      Nat.le_of_dvd (Nat.mul_pos hp₁.pos hp₂.pos) (Nat.gcd_dvd_right _ _)
    have h5 : Int.gcd d b = Nat.gcd d.natAbs b := by rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    rw [h5]
    nlinarith [Nat.zero_le (Nat.gcd d.natAbs b)]
  -- the squarefull part
  have hs : sfp (p₁ * p₂ * b) ≤ p₁ ^ 2 * p₂ ^ 2 * sfp b := by
    have e1 := sfp_mul_prime_le hp₁ (Nat.mul_ne_zero hp₂.ne_zero hb0)
    have e2 := sfp_mul_prime_le hp₂ hb0
    rw [mul_assoc]
    calc sfp (p₁ * (p₂ * b)) ≤ p₁ ^ 2 * sfp (p₂ * b) := e1
      _ ≤ p₁ ^ 2 * (p₂ ^ 2 * sfp b) := Nat.mul_le_mul_left _ e2
      _ = _ := by ring
  -- the number of prime factors
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
  have hsq : ∀ x : ℝ, 0 ≤ x → x ≤ (P : ℝ) ^ 2 → Real.sqrt x ≤ P := by
    intro x hx hxP
    rw [show (P : ℝ) = Real.sqrt ((P : ℝ) ^ 2) by rw [Real.sqrt_sq (Nat.cast_nonneg _)]]
    exact Real.sqrt_le_sqrt hxP
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  -- assemble
  have a1 : (2 : ℝ) ^ (p₁ * p₂ * b).primeFactors.card ≤ 4 * 2 ^ b.primeFactors.card := by
    calc (2 : ℝ) ^ (p₁ * p₂ * b).primeFactors.card ≤ 2 ^ (b.primeFactors.card + 2) :=
          pow_le_pow_right₀ (by norm_num) hω
      _ = 4 * 2 ^ b.primeFactors.card := by rw [pow_add]; ring
  have a2 : Real.sqrt ((p₁ * p₂ * b : ℕ) : ℝ) ≤ P * Real.sqrt b := by
    rw [show ((p₁ * p₂ * b : ℕ) : ℝ) = (p₁ * p₂ : ℝ) * b by push_cast; ring, Real.sqrt_mul (by positivity)]
    exact mul_le_mul_of_nonneg_right (hsq _ (by positivity) hP) (Real.sqrt_nonneg _)
  have a3 : Real.sqrt (Nat.gcd ((((m * d : ℤ) : ZMod (p₁ * p₂ * b)) * u).val) (p₁ * p₂ * b) : ℝ) ≤
      P * Real.sqrt (Int.gcd d b) := by
    have hg' : (Nat.gcd ((((m * d : ℤ) : ZMod (p₁ * p₂ * b)) * u).val) (p₁ * p₂ * b) : ℝ) ≤
        (p₁ * p₂ : ℝ) * Int.gcd d b := by
      calc (Nat.gcd ((((m * d : ℤ) : ZMod (p₁ * p₂ * b)) * u).val) (p₁ * p₂ * b) : ℝ)
          ≤ ((Int.gcd d b * (p₁ * p₂) : ℕ) : ℝ) := by exact_mod_cast hg
        _ = _ := by push_cast; ring
    calc _ ≤ Real.sqrt ((p₁ * p₂ : ℝ) * Int.gcd d b) := Real.sqrt_le_sqrt hg'
      _ = Real.sqrt (p₁ * p₂ : ℝ) * Real.sqrt (Int.gcd d b) := Real.sqrt_mul (by positivity) _
      _ ≤ P * Real.sqrt (Int.gcd d b) :=
          mul_le_mul_of_nonneg_right (hsq _ (by positivity) hP) (Real.sqrt_nonneg _)
  have a4 : Real.sqrt (sfp (p₁ * p₂ * b) : ℝ) ≤ (P : ℝ) ^ 2 * Real.sqrt (sfp b) := by
    have hs' : (sfp (p₁ * p₂ * b) : ℝ) ≤ ((p₁ * p₂ : ℝ)) ^ 2 * sfp b := by
      calc (sfp (p₁ * p₂ * b) : ℝ) ≤ ((p₁ ^ 2 * p₂ ^ 2 * sfp b : ℕ) : ℝ) := by exact_mod_cast hs
        _ = _ := by push_cast; ring
    calc _ ≤ Real.sqrt (((p₁ * p₂ : ℝ)) ^ 2 * sfp b) := Real.sqrt_le_sqrt hs'
      _ = (p₁ * p₂ : ℝ) * Real.sqrt (sfp b) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      _ ≤ (P : ℝ) ^ 2 * Real.sqrt (sfp b) := mul_le_mul_of_nonneg_right hP (Real.sqrt_nonneg _)
  refine le_trans (mul_le_mul (mul_le_mul (mul_le_mul a1 a2 (Real.sqrt_nonneg _) (by positivity)) a3
    (Real.sqrt_nonneg _) (by positivity)) a4 (Real.sqrt_nonneg _) (by positivity)) (le_of_eq ?_)
  ring

set_option maxHeartbeats 1000000 in
/-- **Method 2, explicit form.** -/
theorem method2_bound (Ps : Finset ℕ) (P : ℕ) (r y Y : ℕ) (W : ℕ → ℂ) {W₀ W₁ : ℝ} (hW : SmoothW W W₀ W₁)
    (A t₁ : ℕ) (Bs : Finset ℕ) (hr : 0 < r) (hrA : r ≤ A) (m : ℤ) (α β : ℕ → ℂ)
    (hα : ∀ a, ‖α a‖ ≤ 1) (hβ : ∀ b, ‖β b‖ ≤ 1) (hPs : ∀ p ∈ Ps, p.Prime ∧ p ≤ P)
    (hrP : ∀ p ∈ Ps, r.Coprime p) (hmP : ∀ p ∈ Ps, Nat.Coprime m.natAbs p)
    (hB : ∀ b ∈ Bs, r.Coprime b ∧ 0 < b ∧
      Nat.Coprime m.natAbs b) :
    (∑ p ∈ Ps, ‖∑ a ∈ (Ioc A (2 * A)).filter (fun a => a % r = t₁ % r),
        ∑ b ∈ Bs, α a * β b * ker2 r y Y W m p a b‖) ^ 2 ≤
      (((Ioc A (2 * A)).filter (fun a => a % r = t₁ % r)).card *
        (Bs).card : ℝ) *
      ((Ps.card * (Bs).card *
          ((Ioc A (2 * A)).filter (fun a => a % r = t₁ % r)).card : ℝ) * W₀ ^ 2 +
        (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (4 * (P : ℝ) ^ 6) *
          ∑ b ∈ Bs,
            ((((2 * A / r + 1 : ℕ) : ℝ) / b + (1 + Real.log ((P : ℝ) ^ 2 * b))) *
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
  set F := (((2 * A / r + 1 : ℕ) : ℝ) / b + (1 + Real.log ((P : ℝ) ^ 2 * b))) with hFdef
  set K := (2 : ℝ) ^ b.primeFactors.card * Real.sqrt b * Real.sqrt (sfp b) with hKdef
  have hK : 0 ≤ K := by positivity
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb0
  have hterm : ∀ p₁ ∈ Ps, ∀ p₂ ∈ Ps.erase p₁,
      (3 * W₀ ^ 2 + 4 * W₀ * W₁) * ((((2 * A / r + 1 : ℕ) : ℝ) / (p₁ * p₂ * b : ℕ) +
        (1 + Real.log (p₁ * p₂ * b : ℕ))) *
        @klC (p₁ * p₂ * b) ((@Int.cast (ZMod (p₁ * p₂ * b)) _ (m * ((p₂ : ℤ) - p₁))) *
          ((@Nat.cast (ZMod (p₁ * p₂ * b)) _ (r * r)))⁻¹)) ≤
      (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (F * (4 * (P : ℝ) ^ 4 * (K * Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b)))) := by
    intro p₁ hp₁ p₂ hp₂
    have hp₂' := Finset.mem_of_mem_erase hp₂
    obtain ⟨pr₁, hP₁⟩ := hPs p₁ hp₁
    obtain ⟨pr₂, hP₂⟩ := hPs p₂ hp₂'
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
    have hkl := klC_N_le P p₁ p₂ b pr₁ pr₂ hP₁ hP₂ hb0 m hmN _ (isUnit_inv_of_isUnit hru)
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
      have hge : (b : ℝ) ≤ ((p₁ * p₂ * b : ℕ) : ℝ) := by
        have : b ≤ p₁ * p₂ * b := Nat.le_mul_of_pos_left _ (Nat.mul_pos pr₁.pos pr₂.pos)
        exact_mod_cast this
      gcongr
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc _ ≤ F * @klC (p₁ * p₂ * b) ((@Int.cast (ZMod (p₁ * p₂ * b)) _ (m * ((p₂ : ℤ) - p₁))) *
          ((@Nat.cast (ZMod (p₁ * p₂ * b)) _ (r * r)))⁻¹) :=
          mul_le_mul_of_nonneg_right hF (klC_nonneg _ _)
      _ ≤ F * (4 * (P : ℝ) ^ 4 * (K * Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b))) := by
          refine mul_le_mul_of_nonneg_left (le_trans hkl (le_of_eq ?_)) ?_
          · rw [hKdef]
          · have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast le_trans pr₁.one_lt.le hP₁
            have : 0 ≤ Real.log ((P : ℝ) ^ 2 * b) := Real.log_nonneg (by nlinarith)
            simp only [hFdef]
            positivity
  refine le_trans (Finset.sum_le_sum fun p₁ hp₁ => Finset.sum_le_sum fun p₂ hp₂ => hterm p₁ hp₁ p₂ hp₂) ?_
  have hPs' : ∀ p ∈ Ps, 1 ≤ p ∧ p ≤ P := fun p hp => ⟨(hPs p hp).1.one_lt.le, (hPs p hp).2⟩
  have hlogP : 0 ≤ Real.log ((P : ℝ) ^ 2 * b) := by
    rcases Nat.eq_zero_or_pos P with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ P := by exact_mod_cast h
      exact Real.log_nonneg (by nlinarith)
  have hF0 : 0 ≤ F := by simp only [hFdef]; positivity
  calc ∑ p₁ ∈ Ps, ∑ p₂ ∈ Ps.erase p₁,
          (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (F * (4 * (P : ℝ) ^ 4 * (K * Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b))))
        = (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (F * (4 * (P : ℝ) ^ 4 * K)) *
            ∑ p₁ ∈ Ps, ∑ p₂ ∈ Ps.erase p₁, Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p₁ _ => ?_
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p₂ _ => ?_; ring
      _ ≤ (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (F * (4 * (P : ℝ) ^ 4 * K)) * ((P : ℝ) ^ 2 * b.divisors.card) :=
          mul_le_mul_of_nonneg_left (sum_sqrt_gcd_le Ps P b hb0.ne' hPs') (by positivity)
      _ = _ := by rw [hKdef]; ring

end ThreeSquares
