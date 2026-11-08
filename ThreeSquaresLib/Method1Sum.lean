/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Method1
public import ThreeSquaresLib.Squarefull
public import ThreeSquaresLib.DivisorBound

/-!
# Summing the Weil bounds of Method 1

* `gcd_val_inv_sub`: `gcd(h (p̄₁ − p̄₂) r̄, b) = gcd(p₂ − p₁, b)` for units;
* `sum_sqrt_gcd_le`: `∑_{p₁ ≠ p₂ ≤ P} √gcd(p₂ − p₁, b) ≤ P² τ(b)`;
* `two_pow_card_primeFactors_le`: `2^{ω(b)} ≤ τ(b)`.
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset

theorem isUnit_inv_of_isUnit {b : ℕ} [NeZero b] {x : ZMod b} (hx : IsUnit x) : IsUnit x⁻¹ := by
  rw [← hx.unit_spec, ZMod.inv_coe_unit]; exact Units.isUnit _

theorem gcd_val_intCast (b : ℕ) [NeZero b] (d : ℤ) : Nat.gcd ((d : ZMod b).val) b = Int.gcd d b := by
  have h1 : Nat.gcd ((d : ZMod b).val) b = Int.gcd (((d : ZMod b).val : ℕ) : ℤ) (b : ℤ) := by
    rw [Int.gcd_natCast_natCast]
  rw [h1, ZMod.val_intCast, Int.gcd_emod]

theorem gcd_val_inv_sub {b : ℕ} [NeZero b] (h : ℤ) (r p₁ p₂ : ℕ) (hh : IsUnit (h : ZMod b))
    (hr : IsUnit (r : ZMod b)) (hp₁ : IsUnit (p₁ : ZMod b)) (hp₂ : IsUnit (p₂ : ZMod b)) :
    Nat.gcd (((h : ZMod b) * (((p₁ : ZMod b))⁻¹ - ((p₂ : ZMod b))⁻¹) * ((r : ZMod b))⁻¹).val) b =
      Int.gcd ((p₂ : ℤ) - p₁) b := by
  have e : (h : ZMod b) * (((p₁ : ZMod b))⁻¹ - ((p₂ : ZMod b))⁻¹) * ((r : ZMod b))⁻¹ =
      ((h : ZMod b) * ((r : ZMod b))⁻¹ * ((p₁ : ZMod b))⁻¹ * ((p₂ : ZMod b))⁻¹) *
        ((((p₂ : ℤ) - p₁ : ℤ)) : ZMod b) := by
    have h1 := ZMod.mul_inv_of_unit _ hp₁
    have h2 := ZMod.mul_inv_of_unit _ hp₂
    push_cast
    linear_combination (h : ZMod b) * ((r : ZMod b))⁻¹ * (((p₂ : ZMod b))⁻¹ * h1 - ((p₁ : ZMod b))⁻¹ * h2)
  have hu : IsUnit ((h : ZMod b) * ((r : ZMod b))⁻¹ * ((p₁ : ZMod b))⁻¹ * ((p₂ : ZMod b))⁻¹) :=
    ((hh.mul (isUnit_inv_of_isUnit hr)).mul (isUnit_inv_of_isUnit hp₁)).mul (isUnit_inv_of_isUnit hp₂)
  rw [e, gcd_val_mul_unit _ _ hu, gcd_val_intCast]

theorem two_pow_card_primeFactors_le (b : ℕ) (hb : b ≠ 0) : 2 ^ b.primeFactors.card ≤ b.divisors.card := by
  rw [Nat.card_divisors hb, ← Finset.prod_const]
  refine Finset.prod_le_prod' fun p hp => ?_
  have := (Nat.Prime.factorization_pos_of_dvd (Nat.prime_of_mem_primeFactors hp) hb
    (Nat.dvd_of_mem_primeFactors hp))
  omega

theorem mod_eq_of_int_dvd {e m p : ℕ} (h : (e : ℤ) ∣ (m : ℤ) - p) : m % e = p % e :=
  ((Nat.modEq_iff_dvd).mpr h).symm

/-- Elements `≤ P` in a fixed class mod `e`, other than `p ≤ P`: at most `P / e`. -/
theorem card_cong_le (P p e : ℕ) (he : 0 < e) (hp : p ≤ P) :
    ((Icc 1 P).filter (fun m => m ≠ p ∧ (e : ℤ) ∣ (m : ℤ) - p)).card ≤ P / e := by
  classical
  have hinj : Set.InjOn (fun m => m / e) ((Icc 1 P).filter (fun m => m ≠ p ∧ (e : ℤ) ∣ (m : ℤ) - p) : Set ℕ) := by
    intro m hm m' hm' hmm
    simp only [Finset.coe_filter, Finset.mem_Icc] at hm hm'
    have h1 := mod_eq_of_int_dvd hm.2.2
    have h2 := mod_eq_of_int_dvd hm'.2.2
    simp only at hmm
    rw [← Nat.mod_add_div m e, ← Nat.mod_add_div m' e, h1, h2, hmm]
  have hmaps : ∀ m ∈ (Icc 1 P).filter (fun m => m ≠ p ∧ (e : ℤ) ∣ (m : ℤ) - p),
      m / e ∈ (range (P / e + 1)).erase (p / e) := by
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    simp only [Finset.mem_erase, Finset.mem_range]
    refine ⟨fun hc => hm.2.1 ?_, Nat.lt_succ_of_le (Nat.div_le_div_right hm.1.2)⟩
    have h1 := mod_eq_of_int_dvd hm.2.2
    rw [← Nat.mod_add_div m e, ← Nat.mod_add_div p e, h1, hc]
  have hpe : p / e ∈ range (P / e + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hp))
  calc _ ≤ ((range (P / e + 1)).erase (p / e)).card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ = P / e := by rw [Finset.card_erase_of_mem hpe, Finset.card_range]; rfl

theorem sqrt_gcd_le_sum (d : ℤ) (b : ℕ) (hb : b ≠ 0) :
    Real.sqrt (Int.gcd d b) ≤ ∑ e ∈ b.divisors.filter (fun e : ℕ => (e : ℤ) ∣ d), Real.sqrt e := by
  classical
  have hmem : Int.gcd d b ∈ b.divisors.filter (fun e : ℕ => (e : ℤ) ∣ d) := by
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, hb⟩, Int.gcd_dvd_left d b⟩
    have := Int.gcd_dvd_right d (b : ℤ)
    exact_mod_cast this
  exact Finset.single_le_sum (f := fun e : ℕ => Real.sqrt e) (fun _ _ => Real.sqrt_nonneg _) hmem

/-- **`∑_{p₁ ≠ p₂} √gcd(p₂ − p₁, b) ≤ P² τ(b)`** for levels in `[1, P]`. -/
theorem sum_sqrt_gcd_le (Ps : Finset ℕ) (P b : ℕ) (hb : b ≠ 0) (hPs : ∀ p ∈ Ps, 1 ≤ p ∧ p ≤ P) :
    ∑ p₁ ∈ Ps, ∑ p₂ ∈ Ps.erase p₁, Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b) ≤
      (P : ℝ) ^ 2 * b.divisors.card := by
  classical
  have hone : ∀ p₁ ∈ Ps, ∑ p₂ ∈ Ps.erase p₁, Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b) ≤
      (P : ℝ) * b.divisors.card := by
    intro p₁ hp₁
    calc ∑ p₂ ∈ Ps.erase p₁, Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b)
        ≤ ∑ p₂ ∈ Ps.erase p₁, ∑ e ∈ b.divisors, if (e : ℤ) ∣ (p₂ : ℤ) - p₁ then Real.sqrt e else 0 := by
          refine Finset.sum_le_sum fun p₂ _ => (sqrt_gcd_le_sum _ b hb).trans (le_of_eq ?_)
          rw [Finset.sum_filter]
      _ = ∑ e ∈ b.divisors, Real.sqrt e *
            ((Ps.erase p₁).filter (fun p₂ : ℕ => (e : ℤ) ∣ (p₂ : ℤ) - p₁)).card := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ e ∈ b.divisors, (P : ℝ) := by
          refine Finset.sum_le_sum fun e he => ?_
          have he0 : 0 < e := Nat.pos_of_mem_divisors he
          have hcard : ((Ps.erase p₁).filter (fun p₂ : ℕ => (e : ℤ) ∣ (p₂ : ℤ) - p₁)).card ≤ P / e := by
            refine le_trans (Finset.card_le_card fun m hm => ?_) (card_cong_le P p₁ e he0 (hPs p₁ hp₁).2)
            simp only [Finset.mem_filter, Finset.mem_erase] at hm
            simp only [Finset.mem_filter, Finset.mem_Icc]
            exact ⟨hPs m hm.1.2, hm.1.1, hm.2⟩
          have hc : (((Ps.erase p₁).filter (fun p₂ : ℕ => (e : ℤ) ∣ (p₂ : ℤ) - p₁)).card : ℝ) ≤ (P : ℝ) / e :=
            le_trans (by exact_mod_cast hcard) Nat.cast_div_le
          have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he0
          have hs : Real.sqrt e ≤ e := by
            rw [Real.sqrt_le_left (by positivity)]; nlinarith
          calc Real.sqrt e * _ ≤ Real.sqrt e * ((P : ℝ) / e) :=
                mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)
            _ ≤ (e : ℝ) * ((P : ℝ) / e) := mul_le_mul_of_nonneg_right hs (by positivity)
            _ = P := by field_simp
      _ = (P : ℝ) * b.divisors.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hcardPs : (Ps.card : ℝ) ≤ P := by
    have : Ps ⊆ Icc 1 P := fun p hp => Finset.mem_Icc.mpr (hPs p hp)
    have := Finset.card_le_card this
    rw [Nat.card_Icc] at this
    exact_mod_cast (by omega : Ps.card ≤ P)
  calc _ ≤ ∑ p₁ ∈ Ps, (P : ℝ) * b.divisors.card := Finset.sum_le_sum hone
    _ = Ps.card * ((P : ℝ) * b.divisors.card) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ P * ((P : ℝ) * b.divisors.card) := mul_le_mul_of_nonneg_right hcardPs (by positivity)
    _ = (P : ℝ) ^ 2 * b.divisors.card := by ring

set_option maxHeartbeats 1000000 in
open Classical in
/-- **Method 1, explicit form.** -/
theorem method1_bound (Ps : Finset ℕ) (P : ℕ) (r y Y : ℕ) (W : ℕ → ℂ) {W₀ W₁ : ℝ} (hW : SmoothW W W₀ W₁)
    (A t₁ : ℕ) (Bs : Finset ℕ) (hBs : ∀ b ∈ Bs, 0 < b) (hr : 0 < r) (hrA : r ≤ A) (h : ℕ → ℤ) (α β : ℕ → ℂ)
    (hα : ∀ a, ‖α a‖ ≤ 1) (hβ : ∀ b, ‖β b‖ ≤ 1) (hPs : ∀ p ∈ Ps, 1 ≤ p ∧ p ≤ P)
    (hB : ∀ b ∈ Bs, IsUnit (r : ZMod b))
    (hh : ∀ b ∈ Bs, IsUnit (h b : ZMod b)) :
    (∑ p ∈ Ps, ‖∑ a ∈ (Ioc A (2 * A)).filter (fun a => a % r = t₁ % r),
        ∑ b ∈ Bs, α a * β b * ker1 r y Y W (h b) p a b‖) ^ 2 ≤
      (((Ioc A (2 * A)).filter (fun a => a % r = t₁ % r)).card *
        (Bs).card : ℝ) *
      ((Ps.card * (Bs).card *
          ((Ioc A (2 * A)).filter (fun a => a % r = t₁ % r)).card : ℝ) * W₀ ^ 2 +
        (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (P : ℝ) ^ 2 *
          ∑ b ∈ Bs,
            ((((2 * A / r + 1 : ℕ) : ℝ) / b + (1 + Real.log b)) *
              (2 ^ b.primeFactors.card * Real.sqrt b * Real.sqrt (sfp b) * b.divisors.card))) := by
  refine (method1 Ps r y Y W hW A t₁ Bs hBs hr hrA h α β hα hβ (fun p hp => (hPs p hp).1) hB).trans ?_
  have hW0 := hW.W₀_nonneg
  have hW1 := hW.W₁_nonneg
  refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  have hb0 : b ≠ 0 := (hBs b hb).ne'
  have hlog : 0 ≤ (((2 * A / r + 1 : ℕ) : ℝ) / b + (1 + Real.log b)) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ b by exact_mod_cast Nat.pos_of_ne_zero hb0); positivity
  set F := (((2 * A / r + 1 : ℕ) : ℝ) / b + (1 + Real.log b)) with hFdef
  set K := (2 : ℝ) ^ b.primeFactors.card * Real.sqrt b * Real.sqrt (sfp b) with hKdef
  have hK : 0 ≤ K := by positivity
  have hterm : ∀ p₁ ∈ Ps, ∀ p₂ ∈ Ps.erase p₁,
      (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (F * (if hb : b = 0 then 0 else
        if IsUnit (@Nat.cast (ZMod b) _ p₁) ∧ IsUnit (@Nat.cast (ZMod b) _ p₂) then
        @klC b ((@Int.cast (ZMod b) _ (h b)) * ((@Nat.cast (ZMod b) _ p₁)⁻¹ - (@Nat.cast (ZMod b) _ p₂)⁻¹) *
          ((@Nat.cast (ZMod b) _ r))⁻¹) else 0)) ≤
      (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (F * (K * Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b))) := by
    intro p₁ _ p₂ _
    rw [dif_neg hb0]
    haveI : NeZero b := ⟨hb0⟩
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hlog) (by positivity)
    split_ifs with hu
    · unfold klC
      rw [gcd_val_inv_sub (h b) r p₁ p₂ (hh b hb) (hB b hb) hu.1 hu.2]
      rw [hKdef]; exact le_of_eq (by ring)
    · positivity
  refine le_trans (Finset.sum_le_sum fun p₁ hp₁ => Finset.sum_le_sum fun p₂ hp₂ => hterm p₁ hp₁ p₂ hp₂) ?_
  calc ∑ p₁ ∈ Ps, ∑ p₂ ∈ Ps.erase p₁,
          (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (F * (K * Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b)))
        = (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (F * K) *
          ∑ p₁ ∈ Ps, ∑ p₂ ∈ Ps.erase p₁, Real.sqrt (Int.gcd ((p₂ : ℤ) - p₁) b) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p₁ _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p₂ _ => ?_; ring
    _ ≤ (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (F * K) * ((P : ℝ) ^ 2 * b.divisors.card) :=
        mul_le_mul_of_nonneg_left (sum_sqrt_gcd_le Ps P b hb0 hPs) (by positivity)
    _ = _ := by rw [hKdef]; ring

end ThreeSquares
