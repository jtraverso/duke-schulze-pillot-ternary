/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.PrimePowGauss

/-!
# Kloosterman sums `K(M, M; p^{2β})`

For an odd prime `p ∤ M` and `β ≥ 1`:
`∑_{d ∈ (ℤ/p^{2β})ˣ} e((M (d + d⁻¹))/p^{2β}) = p^β (e(2M/p^{2β}) + e(−2M/p^{2β}))` (`kloosterman_even`).
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset

/-- In `ℤ/q` with `m² = 0`: `(A + m b)⁻¹ = A⁻¹ − A⁻² m b`. -/
theorem inv_add_nilp {q : ℕ} {A m b : ZMod q} (hA : IsUnit A) (hm : m * m = 0) :
    (A + m * b) * (A⁻¹ - A⁻¹ * A⁻¹ * m * b) = 1 := by
  have hA1 : A * A⁻¹ = 1 := ZMod.mul_inv_of_unit A hA
  linear_combination (1 - A⁻¹ * m * b) * hA1 - A⁻¹ * A⁻¹ * b * b * hm

/-- A unit in `ℤ/p^β` squaring to `1` is `±1` (odd `p`). -/
theorem sq_eq_one_pow {p β : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℤ)
    (h : (p : ℤ) ^ β ∣ a ^ 2 - 1) : (p : ℤ) ^ β ∣ a - 1 ∨ (p : ℤ) ^ β ∣ a + 1 := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rw [show a ^ 2 - 1 = (a - 1) * (a + 1) by ring] at h
  by_cases h1 : (p : ℤ) ∣ a - 1
  · left
    have h2 : ¬ (p : ℤ) ∣ a + 1 := by
      intro h2
      have : (p : ℤ) ∣ 2 := by
        have := dvd_sub h2 h1; rwa [show a + 1 - (a - 1) = 2 by ring] at this
      have := Int.le_of_dvd (by norm_num) this
      have := hp.two_le
      omega
    exact (IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hp').mpr h2)).dvd_of_dvd_mul_left (by rw [mul_comm]; exact h)
  · right
    exact (IsCoprime.pow_left ((Prime.coprime_iff_not_dvd hp').mpr h1)).dvd_of_dvd_mul_right (by rw [mul_comm]; exact h)

theorem sum_units_eq_range (q : ℕ) [NeZero q] (F : ZMod q → ℂ) :
    ∑ d : (ZMod q)ˣ, F d = ∑ i ∈ range q, if IsUnit (i : ZMod q) then F i else 0 := by
  classical
  rw [← sum_zmod_eq_range q (fun x => if IsUnit x then F x else 0), Finset.sum_ite,
    Finset.sum_const_zero, add_zero]
  refine Finset.sum_nbij' (fun d => (d : ZMod q)) (fun x => if h : IsUnit x then h.unit else 1)
    (fun d _ => by simp) (fun x _ => Finset.mem_univ _) (fun d _ => by simp) (fun x hx => ?_)
    (fun d _ => rfl)
  have hx' : IsUnit x := (Finset.mem_filter.mp hx).2
  simp [hx']

/-- `∑_{b < m} e_q(m b c) = m [m c = 0]` when `q = m²`. -/
theorem sum_range_mul_char {q m : ℕ} [NeZero q] (hq : q = m * m) (hm0 : 0 < m) (c : ZMod q) :
    ∑ b ∈ range m, (stdAddChar ((m : ZMod q) * (b : ZMod q) * c) : ℂ) =
      if (m : ZMod q) * c = 0 then (m : ℂ) else 0 := by
  subst hq
  have hmm : (m : ZMod (m * m)) * (m : ZMod (m * m)) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_self]
  have hfull := AddChar.sum_mulShift ((m : ZMod (m * m)) * c) (ZMod.isPrimitive_stdAddChar (m * m))
  rw [sum_zmod_eq_range, sum_range_mul _ m m] at hfull
  have hper : ∀ t b : ℕ, (stdAddChar (((m * t + b : ℕ) : ZMod (m * m)) * ((m : ZMod (m * m)) * c)) : ℂ) =
      stdAddChar ((m : ZMod (m * m)) * (b : ZMod (m * m)) * c) := by
    intro t b
    congr 1
    push_cast
    linear_combination (t * c) * hmm
  simp_rw [hper, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ZMod.card] at hfull
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  by_cases h : (m : ZMod (m * m)) * c = 0
  · rw [if_pos h]; rw [if_pos h] at hfull
    push_cast at hfull
    exact mul_left_cancel₀ hm (by rw [hfull])
  · rw [if_neg h]; rw [if_neg h] at hfull
    simp only [Nat.cast_zero] at hfull
    exact (mul_eq_zero.mp hfull).resolve_left hm

/-- **`K(M, M; p^{2β}) = p^β (e(2M/q) + e(−2M/q))`.** -/
theorem kloosterman_even {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (M : ℤ) (hM : ¬ (p : ℤ) ∣ M)
    {β : ℕ} (hβ : 1 ≤ β) :
    haveI : NeZero (p ^ (2 * β)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    ∑ d : (ZMod (p ^ (2 * β)))ˣ,
      (stdAddChar ((M : ZMod (p ^ (2 * β))) * ((d : ZMod (p ^ (2 * β))) +
        ((d⁻¹ : (ZMod (p ^ (2 * β)))ˣ) : ZMod (p ^ (2 * β))))) : ℂ) =
      (p : ℂ) ^ β * (stdAddChar ((2 * M : ℤ) : ZMod (p ^ (2 * β))) +
        stdAddChar ((-2 * M : ℤ) : ZMod (p ^ (2 * β)))) := by
  haveI : NeZero (p ^ (2 * β)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ β) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set q := p ^ (2 * β)
  set m := p ^ β
  have hqm : q = m * m := by simp only [q, m]; ring
  have hmm : (m : ZMod q) * (m : ZMod q) = 0 := by
    rw [← Nat.cast_mul, ← hqm, ZMod.natCast_self]
  -- rewrite `d⁻¹` with the `ZMod` inverse
  have hinv : ∀ d : (ZMod q)ˣ, ((d⁻¹ : (ZMod q)ˣ) : ZMod q) = (d : ZMod q)⁻¹ :=
    fun d => (ZMod.inv_coe_unit d).symm
  simp_rw [hinv]
  rw [sum_units_eq_range q (fun x => stdAddChar ((M : ZMod q) * (x + x⁻¹))),
    show range q = range (m * m) by rw [hqm], sum_range_mul _ m m, Finset.sum_comm]
  have hm0 : 0 < m := pow_pos hp.pos β
  have hpm : (p : ℤ) ∣ (m : ℤ) := by
    simp only [m]; push_cast; exact dvd_pow_self _ (by omega)
  have hM : IsUnit (M : ZMod q) := by
    have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hc : IsCoprime M ((q : ℕ) : ℤ) := by
      simp only [q]; push_cast
      exact IsCoprime.pow_right ((Prime.coprime_iff_not_dvd hp').mpr hM).symm
    obtain ⟨u, v, huv⟩ := hc
    refine IsUnit.of_mul_eq_one (u : ZMod q) ?_
    have := congrArg (Int.cast : ℤ → ZMod q) huv
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, add_zero] at this
    linear_combination this
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hm3 : 3 ≤ m := by
    have := hp.two_le
    have h3 : 3 ≤ p := by omega
    calc 3 ≤ p := h3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ β := Nat.pow_le_pow_right hp.pos hβ
  -- each `a`
  have hterm : ∀ a ∈ range m, (∑ b ∈ range m, if IsUnit ((m * b + a : ℕ) : ZMod q) then
      (stdAddChar ((M : ZMod q) * (((m * b + a : ℕ) : ZMod q) + ((m * b + a : ℕ) : ZMod q)⁻¹)) : ℂ)
      else 0) = if a = 1 ∨ a = m - 1 then (m : ℂ) * stdAddChar ((M : ZMod q) *
        ((a : ZMod q) + (a : ZMod q)⁻¹)) else 0 := by
    intro a ha
    have ham : a < m := Finset.mem_range.mp ha
    by_cases hpa : (p : ℤ) ∣ a
    · -- no units
      have hne : ¬ (a = 1 ∨ a = m - 1) := by
        rintro (rfl | h)
        · have := Int.le_of_dvd one_pos hpa; have := hp.two_le; omega
        · have h1 : (p : ℤ) ∣ (m : ℤ) - a := dvd_sub hpm hpa
          rw [h, show (m : ℤ) - ((m - 1 : ℕ) : ℤ) = 1 by omega] at h1
          have := Int.le_of_dvd one_pos h1; have := hp.two_le; omega
      rw [if_neg hne]
      refine Finset.sum_eq_zero fun b _ => if_neg ?_
      intro hu
      rw [ZMod.isUnit_iff_coprime] at hu
      have h1 : p ∣ m * b + a := by
        have : (p : ℤ) ∣ ((m * b + a : ℕ) : ℤ) := by push_cast; exact dvd_add (dvd_mul_of_dvd_left hpm _) hpa
        exact_mod_cast this
      have h2 : p ∣ q := dvd_pow_self p (by omega)
      have := Nat.Coprime.coprime_dvd_left h1 hu
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this h2)
    · have hA : IsUnit (a : ZMod q) := by
        rw [ZMod.isUnit_iff_coprime]
        have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
        have : IsCoprime (a : ℤ) ((q : ℕ) : ℤ) := by
          simp only [q]; push_cast
          exact IsCoprime.pow_right ((Prime.coprime_iff_not_dvd hp').mpr hpa).symm
        exact Nat.isCoprime_iff_coprime.mp this
      set A : ZMod q := (a : ZMod q)
      set c : ZMod q := (M : ZMod q) * (1 - A⁻¹ * A⁻¹)
      have hb : ∀ b : ℕ, (if IsUnit ((m * b + a : ℕ) : ZMod q) then
          (stdAddChar ((M : ZMod q) * (((m * b + a : ℕ) : ZMod q) + ((m * b + a : ℕ) : ZMod q)⁻¹)) : ℂ)
          else 0) = stdAddChar ((M : ZMod q) * (A + A⁻¹)) *
            stdAddChar ((m : ZMod q) * (b : ZMod q) * c) := by
        intro b
        have hx : ((m * b + a : ℕ) : ZMod q) = A + (m : ZMod q) * (b : ZMod q) := by push_cast; ring
        have hxy := inv_add_nilp (b := (b : ZMod q)) hA hmm
        rw [hx, if_pos (IsUnit.of_mul_eq_one _ hxy), ZMod.inv_eq_of_mul_eq_one _ _ _ hxy,
          ← AddChar.map_add_eq_mul]
        congr 1
        simp only [c]; ring
      rw [Finset.sum_congr rfl fun b _ => hb b, ← Finset.mul_sum, sum_range_mul_char hqm hm0]
      -- the condition `m c = 0`
      have hcond : (m : ZMod q) * c = 0 ↔ (a = 1 ∨ a = m - 1) := by
        have hAA : A⁻¹ * A = 1 := ZMod.inv_mul_of_unit A hA
        have hMi : (M : ZMod q) * (hM.unit⁻¹ : (ZMod q)ˣ).val = 1 := hM.mul_val_inv
        have step1 : (m : ZMod q) * c = 0 ↔ (m : ZMod q) * (A * A - 1) = 0 := by
          constructor
          · intro h
            simp only [c] at h
            linear_combination ((hM.unit⁻¹ : (ZMod q)ˣ).val * A * A) * h +
              (m : ZMod q) * (A⁻¹ * A + 1) * hAA - (m : ZMod q) * A * A * (1 - A⁻¹ * A⁻¹) * hMi
          · intro h
            simp only [c]
            linear_combination ((M : ZMod q) * A⁻¹ * A⁻¹) * h -
              (m : ZMod q) * (M : ZMod q) * (A⁻¹ * A + 1) * hAA
        have hm2 : (m : ℤ) ≠ 0 := by exact_mod_cast hm0.ne'
        have step2 : (m : ZMod q) * (A * A - 1) = 0 ↔ (m : ℤ) ∣ (a : ℤ) ^ 2 - 1 := by
          rw [show (m : ZMod q) * (A * A - 1) = (((m : ℤ) * ((a : ℤ) ^ 2 - 1) : ℤ) : ZMod q) by
            simp only [A]; push_cast; ring, ZMod.intCast_zmod_eq_zero_iff_dvd]
          have hq' : ((q : ℕ) : ℤ) = (m : ℤ) * m := by rw [hqm]; push_cast; ring
          erw [hq']
          exact mul_dvd_mul_iff_left hm2
        have ha0 : a ≠ 0 := by rintro rfl; exact hpa (dvd_zero _)
        rw [step1, step2]
        constructor
        · intro h
          have hmp : ((m : ℕ) : ℤ) = (p : ℤ) ^ β := by simp only [m]; push_cast; ring
          rw [hmp] at h
          rcases sq_eq_one_pow hp hp2 a h with h1 | h1
          · left
            rw [← hmp] at h1
            obtain ⟨t, ht⟩ := h1
            have : t = 0 := by
              by_contra ht0
              have : (m : ℤ) ≤ |(a : ℤ) - 1| := by
                rw [ht, abs_mul, abs_of_pos (by exact_mod_cast hm0)]
                exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs ht0)
              have h3 : |(a : ℤ) - 1| < m := abs_lt.mpr ⟨by omega, by omega⟩
              linarith
            rw [this, mul_zero] at ht; omega
          · right
            rw [← hmp] at h1
            obtain ⟨t, ht⟩ := h1
            have : t = 1 := by
              have h1 : 0 < (a : ℤ) + 1 := by omega
              have h2 : (a : ℤ) + 1 ≤ m := by omega
              rw [ht] at h1 h2
              have ht1 : 0 < t := by
                by_contra h; push_neg at h
                have : (m : ℤ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
                omega
              by_contra hne
              have : (m : ℤ) * 2 ≤ m * t := mul_le_mul_of_nonneg_left (by omega) (by positivity)
              omega
            rw [this, mul_one] at ht; omega
        · rintro (rfl | rfl)
          · simp
          · rw [show ((m - 1 : ℕ) : ℤ) ^ 2 - 1 = (m : ℤ) * ((m : ℤ) - 2) by
              rw [Nat.cast_sub (by omega)]; push_cast; ring]
            exact dvd_mul_right _ _
      by_cases hc : a = 1 ∨ a = m - 1
      · rw [if_pos (hcond.mpr hc), if_pos hc]; ring
      · rw [if_neg (fun h => hc (hcond.mp h)), if_neg hc, mul_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter,
    show (range m).filter (fun a => a = 1 ∨ a = m - 1) = {1, m - 1} by
      ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton]; omega,
    Finset.sum_pair (by omega), ← mul_add, show ((m : ℕ) : ℂ) = (p : ℂ) ^ β by simp [m]]
  congr 1
  have hm1 : ((m - 1 : ℕ) : ZMod q) * (-1 - (m : ZMod q)) = 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; linear_combination -hmm
  rw [Nat.cast_one, ZMod.inv_eq_of_mul_eq_one _ 1 1 (one_mul 1),
    ZMod.inv_eq_of_mul_eq_one _ _ _ hm1]
  congr 2
  · push_cast; ring
  · rw [Nat.cast_sub (by omega)]; push_cast; ring

end ThreeSquares
