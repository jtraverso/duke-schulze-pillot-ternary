/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.PrimePowKl
public import ThreeSquaresLib.PrimeT

/-!
# Salié sums modulo `p^{2β+1}`

For an odd prime `p ∤ M`, `β ≥ 1`, `q = p^{2β+1}` and `χ` the quadratic character mod `p`:
`∑_{d ∈ (ℤ/q)ˣ} χ(d) e(M(d + d⁻¹)/q) = p^β χ(M) g (e(2M/q) + e(−2M/q))` (`salie_odd`).
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset

/-- `∑_{b < k} e_q(m b c) = k [m c = 0]` when `q = m k` and `m k ∣ m²`-type nilpotence is not needed. -/
theorem sum_range_mul_char' {q m k : ℕ} [NeZero q] (hq : q = m * k) (hm0 : 0 < m) (hk0 : 0 < k)
    (c : ZMod q) :
    ∑ b ∈ range k, (stdAddChar ((m : ZMod q) * (b : ZMod q) * c) : ℂ) =
      if (m : ZMod q) * c = 0 then (k : ℂ) else 0 := by
  have hmk : (m : ZMod q) * (k : ZMod q) = 0 := by rw [← Nat.cast_mul, ← hq, ZMod.natCast_self]
  have hfull := AddChar.sum_mulShift ((m : ZMod q) * c) (ZMod.isPrimitive_stdAddChar q)
  rw [sum_zmod_eq_range, show range q = range (k * m) by rw [hq, mul_comm], sum_range_mul _ k m]
    at hfull
  have hper : ∀ t b : ℕ, (stdAddChar (((k * t + b : ℕ) : ZMod q) * ((m : ZMod q) * c)) : ℂ) =
      stdAddChar ((m : ZMod q) * (b : ZMod q) * c) := by
    intro t b
    congr 1
    push_cast
    linear_combination (t * c) * hmk
  simp_rw [hper, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ZMod.card] at hfull
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hqC : ((q : ℕ) : ℂ) = (m : ℂ) * k := by rw [hq]; push_cast; ring
  by_cases h : (m : ZMod q) * c = 0
  · rw [if_pos h]; rw [if_pos h, hqC] at hfull
    exact mul_left_cancel₀ hm hfull
  · rw [if_neg h]; rw [if_neg h] at hfull
    simp only [Nat.cast_zero] at hfull
    exact (mul_eq_zero.mp hfull).resolve_left hm

/-- The quadratic character mod `p`, pulled back to `ℤ/p^α` (`α ≥ 1`). -/
noncomputable def chiq (p α : ℕ) [Fact p.Prime] (x : ZMod (p ^ α)) : ℂ :=
  PT.chi p (ZMod.cast x : ZMod p)

theorem chiq_natCast (p α : ℕ) [Fact p.Prime] (hα : 1 ≤ α) (a : ℕ) :
    chiq p α (a : ZMod (p ^ α)) = PT.chi p (a : ZMod p) := by
  unfold chiq
  congr 1
  have h : p ∣ p ^ α := dvd_pow_self p (by omega)
  rw [ZMod.cast_natCast h]

/-- `e_q(M k² w²) = e_p(M w²)` for `q = p^{2β+1}`, `k = p^β`. -/
theorem stdAddChar_scale {p β : ℕ} (hp : p.Prime) (M : ℤ) (w : ℕ) :
    haveI : NeZero (p ^ (2 * β + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    haveI : NeZero p := ⟨hp.ne_zero⟩
    (stdAddChar ((M : ZMod (p ^ (2 * β + 1))) * ((p ^ β : ℕ) : ZMod (p ^ (2 * β + 1))) ^ 2 *
      (w : ZMod (p ^ (2 * β + 1))) ^ 2) : ℂ) = stdAddChar ((M : ZMod p) * (w : ZMod p) ^ 2) := by
  haveI : NeZero (p ^ (2 * β + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [show (M : ZMod (p ^ (2 * β + 1))) * ((p ^ β : ℕ) : ZMod (p ^ (2 * β + 1))) ^ 2 *
      (w : ZMod (p ^ (2 * β + 1))) ^ 2 = ((M * (p : ℤ) ^ (2 * β) * (w : ℤ) ^ 2 : ℤ) : ZMod _) by
      push_cast; ring,
    show (M : ZMod p) * (w : ZMod p) ^ 2 = ((M * (w : ℤ) ^ 2 : ℤ) : ZMod p) by push_cast; ring,
    stdAddChar_int, stdAddChar_int]
  congr 1
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  push_cast
  field_simp
  ring

/-- `∑_{w < p} e_p(c w²) = χ(c) g` for `p ∤ c`. -/
theorem sum_range_gauss {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {c : ZMod p} (hc : c ≠ 0) :
    ∑ w ∈ range p, (stdAddChar (c * (w : ZMod p) ^ 2) : ℂ) = PT.chi p c * PT.gs p := by
  rw [← PT.sum_psi_sq hp2 hc, sum_zmod_eq_range]

/-- For `0 ≤ a < p^β` (odd `p`, `β ≥ 1`): `p^β ∣ a² − 1 ↔ a ∈ {1, p^β − 1}`. -/
theorem sq_one_iff {p β : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hβ : 1 ≤ β) {a : ℕ} (ha : a < p ^ β) :
    ((p ^ β : ℕ) : ℤ) ∣ (a : ℤ) ^ 2 - 1 ↔ (a = 1 ∨ a = p ^ β - 1) := by
  set m := p ^ β
  have hm0 : 0 < m := pow_pos hp.pos β
  have hmp : ((m : ℕ) : ℤ) = (p : ℤ) ^ β := by simp only [m]; push_cast; ring
  have ham : (a : ℤ) < (m : ℤ) := by exact_mod_cast ha
  have ha0 : (0 : ℤ) ≤ a := Nat.cast_nonneg a
  have hm2 : (2 : ℤ) ≤ m := by
    have h1 : 2 ≤ p ^ β := le_trans hp.two_le (by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ β := Nat.pow_le_pow_right hp.pos hβ)
    exact_mod_cast h1
  constructor
  · intro h
    rw [hmp] at h
    rcases sq_eq_one_pow hp hp2 a h with h1 | h1
    · left
      rw [← hmp] at h1
      obtain ⟨t, ht⟩ := h1
      have : t = 0 := by
        by_contra ht0
        have h2 : (m : ℤ) ≤ |(a : ℤ) - 1| := by
          rw [ht, abs_mul, abs_of_pos (by exact_mod_cast hm0)]
          exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs ht0)
        have h3 : |(a : ℤ) - 1| < m := abs_lt.mpr ⟨by linarith, by linarith⟩
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
  · rintro (rfl | h)
    · simp
    · rw [h, show ((m - 1 : ℕ) : ℤ) ^ 2 - 1 = (m : ℤ) * ((m : ℤ) - 2) by
        rw [Nat.cast_sub (by omega)]; push_cast; ring]
      exact dvd_mul_right _ _

/-- **Salié's sum modulo `p^{2β+1}`.** -/
theorem salie_odd {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (M : ℤ) (hM : ¬ (p : ℤ) ∣ M)
    {β : ℕ} (hβ : 1 ≤ β) :
    haveI : NeZero (p ^ (2 * β + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    ∑ d : (ZMod (p ^ (2 * β + 1)))ˣ, chiq p (2 * β + 1) d *
      (stdAddChar ((M : ZMod (p ^ (2 * β + 1))) * ((d : ZMod (p ^ (2 * β + 1))) +
        ((d⁻¹ : (ZMod (p ^ (2 * β + 1)))ˣ) : ZMod (p ^ (2 * β + 1))))) : ℂ) =
      (p : ℂ) ^ β * PT.chi p (M : ZMod p) * PT.gs p *
        (stdAddChar ((2 * M : ℤ) : ZMod (p ^ (2 * β + 1))) +
          stdAddChar ((-2 * M : ℤ) : ZMod (p ^ (2 * β + 1)))) := by
  haveI : NeZero (p ^ (2 * β + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hpp := hp.out
  set q := p ^ (2 * β + 1)
  set m := p ^ (β + 1)
  set k := p ^ β
  have hk0 : 0 < k := pow_pos hpp.pos β
  have hm0 : 0 < m := pow_pos hpp.pos (β + 1)
  have hqmk : q = m * k := by simp only [q, m, k]; ring
  have hmkp : m = k * p := by simp only [m, k]; ring
  have hmm : (m : ZMod q) * (m : ZMod q) = 0 := by
    rw [← Nat.cast_mul, show m * m = q * p by simp only [q, m]; ring, Nat.cast_mul,
      ZMod.natCast_self, zero_mul]
  have hk3 : (k : ZMod q) ^ 3 = 0 := by
    rw [← Nat.cast_pow, show k ^ 3 = q * p ^ (β - 1) by
      simp only [q, k]; rw [← pow_mul, ← pow_add]; congr 1; omega, Nat.cast_mul, ZMod.natCast_self,
      zero_mul]
  have hinv : ∀ d : (ZMod q)ˣ, ((d⁻¹ : (ZMod q)ˣ) : ZMod q) = (d : ZMod q)⁻¹ :=
    fun d => (ZMod.inv_coe_unit d).symm
  simp_rw [hinv]
  rw [sum_units_eq_range q (fun x => chiq p (2 * β + 1) x * stdAddChar ((M : ZMod q) * (x + x⁻¹))),
    show range q = range (m * k) by rw [hqmk], sum_range_mul _ m k, Finset.sum_comm]
  have hM' : IsUnit (M : ZMod q) := by
    have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
    have hc : IsCoprime M ((q : ℕ) : ℤ) := by
      simp only [q]; push_cast
      exact IsCoprime.pow_right ((Prime.coprime_iff_not_dvd hp').mpr hM).symm
    obtain ⟨u, v, huv⟩ := hc
    refine IsUnit.of_mul_eq_one (u : ZMod q) ?_
    have := congrArg (Int.cast : ℤ → ZMod q) huv
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, add_zero] at this
    linear_combination this
  have hpk : (p : ℤ) ∣ (k : ℤ) := by
    simp only [k]; push_cast; exact dvd_pow_self _ (by omega)
  have hpm : (p : ℤ) ∣ (m : ℤ) := by
    simp only [m]; push_cast; exact dvd_pow_self _ (by omega)
  -- the inner sum over `b`, for each `a < m`
  have hterm : ∀ a ∈ range m, (∑ b ∈ range k, if IsUnit ((m * b + a : ℕ) : ZMod q) then
      chiq p (2 * β + 1) ((m * b + a : ℕ) : ZMod q) *
        (stdAddChar ((M : ZMod q) * (((m * b + a : ℕ) : ZMod q) + ((m * b + a : ℕ) : ZMod q)⁻¹)) : ℂ)
      else 0) = if (k : ℤ) ∣ (a : ℤ) ^ 2 - 1 then (k : ℂ) * (PT.chi p (a : ZMod p) *
        stdAddChar ((M : ZMod q) * ((a : ZMod q) + (a : ZMod q)⁻¹))) else 0 := by
    intro a ha
    by_cases hpa : (p : ℤ) ∣ a
    · have hne : ¬ (k : ℤ) ∣ (a : ℤ) ^ 2 - 1 := by
        intro h
        have h1 : (p : ℤ) ∣ (a : ℤ) ^ 2 - 1 := dvd_trans hpk h
        have h2 : (p : ℤ) ∣ (a : ℤ) ^ 2 := dvd_pow hpa two_ne_zero
        have := dvd_sub h2 h1
        rw [show (a : ℤ) ^ 2 - ((a : ℤ) ^ 2 - 1) = 1 by ring] at this
        have := Int.le_of_dvd one_pos this; have := hpp.two_le; omega
      rw [if_neg hne]
      refine Finset.sum_eq_zero fun b _ => if_neg ?_
      intro hu
      rw [ZMod.isUnit_iff_coprime] at hu
      have h1 : p ∣ m * b + a := by
        have : (p : ℤ) ∣ ((m * b + a : ℕ) : ℤ) := by
          push_cast; exact dvd_add (dvd_mul_of_dvd_left hpm _) hpa
        exact_mod_cast this
      have h2 : p ∣ q := dvd_pow_self p (by omega)
      exact hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hu) h2)
    · have hA : IsUnit (a : ZMod q) := by
        rw [ZMod.isUnit_iff_coprime]
        have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
        have : IsCoprime (a : ℤ) ((q : ℕ) : ℤ) := by
          simp only [q]; push_cast
          exact IsCoprime.pow_right ((Prime.coprime_iff_not_dvd hp').mpr hpa).symm
        exact Nat.isCoprime_iff_coprime.mp this
      set A : ZMod q := (a : ZMod q)
      set c : ZMod q := (M : ZMod q) * (1 - A⁻¹ * A⁻¹)
      have hb : ∀ b : ℕ, (if IsUnit ((m * b + a : ℕ) : ZMod q) then
          chiq p (2 * β + 1) ((m * b + a : ℕ) : ZMod q) *
          (stdAddChar ((M : ZMod q) * (((m * b + a : ℕ) : ZMod q) + ((m * b + a : ℕ) : ZMod q)⁻¹)) : ℂ)
          else 0) = PT.chi p (a : ZMod p) * stdAddChar ((M : ZMod q) * (A + A⁻¹)) *
            stdAddChar ((m : ZMod q) * (b : ZMod q) * c) := by
        intro b
        have hx : ((m * b + a : ℕ) : ZMod q) = A + (m : ZMod q) * (b : ZMod q) := by push_cast; ring
        have hxy := inv_add_nilp (b := (b : ZMod q)) hA hmm
        have hchi : chiq p (2 * β + 1) ((m * b + a : ℕ) : ZMod q) = PT.chi p (a : ZMod p) := by
          rw [chiq_natCast p _ (by omega)]
          congr 1
          have : ((m : ℕ) : ZMod p) = 0 := by
            rw [ZMod.natCast_eq_zero_iff]; exact_mod_cast hpm
          push_cast; rw [this]; ring
        rw [if_pos (by rw [hx]; exact IsUnit.of_mul_eq_one _ hxy), hchi, hx,
          ZMod.inv_eq_of_mul_eq_one _ _ _ hxy,
          show PT.chi p (a : ZMod p) * stdAddChar ((M : ZMod q) * (A + A⁻¹)) *
            stdAddChar ((m : ZMod q) * (b : ZMod q) * c) = PT.chi p (a : ZMod p) *
            stdAddChar ((M : ZMod q) * (A + A⁻¹) + (m : ZMod q) * (b : ZMod q) * c) by
              rw [AddChar.map_add_eq_mul]; ring]
        congr 2
        simp only [c]; ring
      rw [Finset.sum_congr rfl fun b _ => hb b, ← Finset.mul_sum,
        sum_range_mul_char' hqmk hm0 hk0]
      have hcond : (m : ZMod q) * c = 0 ↔ (k : ℤ) ∣ (a : ℤ) ^ 2 - 1 := by
        have hAA : A⁻¹ * A = 1 := ZMod.inv_mul_of_unit A hA
        have hMi : (M : ZMod q) * (hM'.unit⁻¹ : (ZMod q)ˣ).val = 1 := hM'.mul_val_inv
        have step1 : (m : ZMod q) * c = 0 ↔ (m : ZMod q) * (A * A - 1) = 0 := by
          constructor
          · intro h
            simp only [c] at h
            linear_combination ((hM'.unit⁻¹ : (ZMod q)ˣ).val * A * A) * h +
              (m : ZMod q) * (A⁻¹ * A + 1) * hAA - (m : ZMod q) * A * A * (1 - A⁻¹ * A⁻¹) * hMi
          · intro h
            simp only [c]
            linear_combination ((M : ZMod q) * A⁻¹ * A⁻¹) * h -
              (m : ZMod q) * (M : ZMod q) * (A⁻¹ * A + 1) * hAA
        rw [step1, show (m : ZMod q) * (A * A - 1) = (((m : ℤ) * ((a : ℤ) ^ 2 - 1) : ℤ) : ZMod q) by
          simp only [A]; push_cast; ring, ZMod.intCast_zmod_eq_zero_iff_dvd]
        have hq' : ((q : ℕ) : ℤ) = (m : ℤ) * k := by rw [hqmk]; push_cast; ring
        erw [hq']
        exact mul_dvd_mul_iff_left (by exact_mod_cast hm0.ne')
      by_cases hc : (k : ℤ) ∣ (a : ℤ) ^ 2 - 1
      · rw [if_pos (hcond.mpr hc), if_pos hc]; ring
      · rw [if_neg (fun h => hc (hcond.mp h)), if_neg hc, mul_zero]
  rw [Finset.sum_congr rfl hterm, show range m = range (k * p) by rw [hmkp], sum_range_mul _ k p]
  have hk3' : 3 ≤ k := by
    have := hpp.two_le
    have h3 : 3 ≤ p := by omega
    calc 3 ≤ p := h3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ β := Nat.pow_le_pow_right hpp.pos hβ
  have hkp0 : ((k : ℕ) : ZMod p) = 0 := by rw [ZMod.natCast_eq_zero_iff]; exact_mod_cast hpk
  set F : ℕ → ℂ := fun a => if (k : ℤ) ∣ (a : ℤ) ^ 2 - 1 then (k : ℂ) * (PT.chi p (a : ZMod p) *
    stdAddChar ((M : ZMod q) * ((a : ZMod q) + (a : ZMod q)⁻¹))) else 0
  have hinner : ∀ w : ℕ, ∑ a₀ ∈ range k, F (k * w + a₀) = F (k * w + 1) + F (k * w + (k - 1)) := by
    intro w
    have hcondw : ∀ a₀ : ℕ, ((k : ℤ) ∣ (((k * w + a₀ : ℕ) : ℤ)) ^ 2 - 1) ↔ ((k : ℤ) ∣ (a₀ : ℤ) ^ 2 - 1) := by
      intro a₀
      rw [show (((k * w + a₀ : ℕ) : ℤ)) ^ 2 - 1 = (k : ℤ) * (k * w ^ 2 + 2 * w * a₀) + ((a₀ : ℤ) ^ 2 - 1) by
        push_cast; ring]
      exact (dvd_add_right (dvd_mul_right _ _))
    rw [← Finset.sum_filter_add_sum_filter_not (range k) (fun a₀ => a₀ = 1 ∨ a₀ = k - 1)]
    rw [Finset.sum_eq_zero (s := (range k).filter (fun a₀ => ¬ (a₀ = 1 ∨ a₀ = k - 1))) fun a₀ ha₀ => by
      obtain ⟨ha, hn⟩ := Finset.mem_filter.mp ha₀
      simp only [F]
      rw [if_neg]
      rw [hcondw, sq_one_iff hpp hp2 hβ (Finset.mem_range.mp ha)]
      exact hn, add_zero,
      show (range k).filter (fun a₀ => a₀ = 1 ∨ a₀ = k - 1) = {1, k - 1} by
        ext a₀; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
          Finset.mem_singleton]; omega,
      Finset.sum_pair (by omega)]
  rw [show (∑ w ∈ range p, ∑ a₀ ∈ range k, F (k * w + a₀)) =
      ∑ w ∈ range p, (F (k * w + 1) + F (k * w + (k - 1))) from
    Finset.sum_congr rfl fun w _ => hinner w] -- (beta-equal goal)
  rw [Finset.sum_add_distrib]
  -- the two families
  have hgM : (M : ZMod p) ≠ 0 := by
    intro h; rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h; exact hM h
  have hsc : ∀ (N : ℤ) (v : ℕ), (stdAddChar ((N : ZMod q) * (k : ZMod q) ^ 2 * (v : ZMod q) ^ 2) : ℂ) =
      stdAddChar ((N : ZMod p) * (v : ZMod p) ^ 2) := by
    intro N v
    have h := stdAddChar_scale (β := β) hpp N v
    exact h
  have hS1 : ∑ w ∈ range p, F (k * w + 1) =
      (k : ℂ) * (stdAddChar ((2 * M : ℤ) : ZMod q) * (PT.chi p (M : ZMod p) * PT.gs p)) := by
    rw [← sum_range_gauss hp2 hgM, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [F]
    rw [if_pos (by
      rw [show (((k * w + 1 : ℕ) : ℤ)) ^ 2 - 1 = (k : ℤ) * (k * w ^ 2 + 2 * w) by push_cast; ring]
      exact dvd_mul_right _ _)]
    have hchi : PT.chi p (((k * w + 1 : ℕ) : ZMod p)) = 1 := by
      push_cast; rw [hkp0, zero_mul, zero_add, map_one]
    have hAi : (((k * w + 1 : ℕ) : ZMod q))⁻¹ = 1 - (k : ZMod q) * w + (k : ZMod q) ^ 2 * w ^ 2 := by
      apply ZMod.inv_eq_of_mul_eq_one
      push_cast
      linear_combination (w : ZMod q) ^ 3 * hk3
    rw [hchi, hAi, one_mul, ← hsc M w, ← AddChar.map_add_eq_mul]
    congr 2
    push_cast; ring
  have hS2 : ∑ w ∈ range p, F (k * w + (k - 1)) =
      (k : ℂ) * (PT.chi p (-1) * stdAddChar ((-2 * M : ℤ) : ZMod q) *
        (PT.chi p (((-M : ℤ)) : ZMod p) * PT.gs p)) := by
    have hgM' : (((-M : ℤ)) : ZMod p) ≠ 0 := by push_cast; exact neg_ne_zero.mpr hgM
    have hshift : ∑ w ∈ range p, (stdAddChar ((((-M : ℤ)) : ZMod p) * ((w + 1 : ℕ) : ZMod p) ^ 2) : ℂ) =
        PT.chi p (((-M : ℤ)) : ZMod p) * PT.gs p := by
      have e1 : ∑ w ∈ range p, (stdAddChar ((((-M : ℤ)) : ZMod p) * ((w + 1 : ℕ) : ZMod p) ^ 2) : ℂ) =
          ∑ x : ZMod p, (stdAddChar ((((-M : ℤ)) : ZMod p) * (x + 1) ^ 2) : ℂ) := by
        rw [sum_zmod_eq_range p (fun x => (stdAddChar ((((-M : ℤ)) : ZMod p) * (x + 1) ^ 2) : ℂ))]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Nat.cast_add, Nat.cast_one]
      have e2 : ∑ x : ZMod p, (stdAddChar ((((-M : ℤ)) : ZMod p) * (x + 1) ^ 2) : ℂ) =
          ∑ x : ZMod p, (stdAddChar ((((-M : ℤ)) : ZMod p) * x ^ 2) : ℂ) :=
        Fintype.sum_equiv (Equiv.addRight (1 : ZMod p)) _ _ fun x => by
          simp only [Equiv.coe_addRight]
      rw [e1, e2, PT.sum_psi_sq hp2 hgM']
    rw [← hshift, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [F]
    have hk1 : 1 ≤ k := by omega
    rw [if_pos (by
      rw [show (((k * w + (k - 1) : ℕ) : ℤ)) ^ 2 - 1 = (k : ℤ) * (k * (w + 1) ^ 2 - 2 * (w + 1)) by
        rw [Nat.cast_add, Nat.cast_sub hk1]; push_cast; ring]
      exact dvd_mul_right _ _)]
    have hchi : PT.chi p (((k * w + (k - 1) : ℕ) : ZMod p)) = PT.chi p (-1) := by
      rw [Nat.cast_add, Nat.cast_sub hk1]; push_cast; rw [hkp0]; congr 1; ring
    have hAi : (((k * w + (k - 1) : ℕ) : ZMod q))⁻¹ =
        -1 - (k : ZMod q) * (w + 1) - (k : ZMod q) ^ 2 * (w + 1) ^ 2 := by
      apply ZMod.inv_eq_of_mul_eq_one
      rw [Nat.cast_add, Nat.cast_sub hk1]
      push_cast
      linear_combination -((w : ZMod q) + 1) ^ 3 * hk3
    rw [hchi, hAi, ← hsc (-M) (w + 1), mul_assoc (PT.chi p (-1)), ← AddChar.map_add_eq_mul]
    congr 3
    rw [Nat.cast_add, Nat.cast_sub hk1]; push_cast; ring
  rw [hS1, hS2]
  have hchi1 : PT.chi p (-1) * PT.chi p (((-M : ℤ)) : ZMod p) = PT.chi p (M : ZMod p) := by
    rw [← map_mul]; congr 1; push_cast; ring
  rw [show ((k : ℕ) : ℂ) = (p : ℂ) ^ β by simp [k]]
  linear_combination (p : ℂ) ^ β * stdAddChar ((-2 * M : ℤ) : ZMod q) * PT.gs p * hchi1

end ThreeSquares
