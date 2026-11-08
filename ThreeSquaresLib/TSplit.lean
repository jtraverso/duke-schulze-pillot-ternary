/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.RQSplit
public import ThreeSquaresLib.KlBridge
public import ThreeSquaresLib.Method1

/-!
# `T_{rq}` along unitary divisors

For `r` coprime to odd `q`, `(n, q) = 1`:
`T_{rq}(1, n) = T_r(s', n) · J(−n | q) · q · ∑_{a ∥ q} e(2n/(rq)) e_b(−4n \overline{ra}) e_r(−2n \overline{ab})`
with `s' q + r' r = 1` and `b = q / a` (`Tc_expand`).
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset

theorem zfI_cast_a (a b : ℕ) (h : a.Coprime b) : ((zfI a b : ℤ) : ZMod a) = 1 := by
  have e : zfI a b = 1 + (-2 * Nat.gcdA a b) * a := by
    have := zfI_sub_one a b h; linear_combination this
  rw [e]; push_cast; simp

theorem zfI_cast_b (a b : ℕ) : ((zfI a b : ℤ) : ZMod b) = -1 := by
  have e : zfI a b = -1 + (2 * Nat.gcdB a b) * b := by
    have := zfI_add_one a b; linear_combination this
  rw [e]; push_cast; simp

theorem mem_udiv {q a : ℕ} (ha : a ∈ udiv q) : a ∣ q ∧ q ≠ 0 ∧ a.Coprime (q / a) := by
  simp only [udiv, Finset.mem_filter, Nat.mem_divisors] at ha
  exact ⟨ha.1.1, ha.1.2, ha.2⟩

/-- One unitary divisor: the phase in terms of `rph`. -/
theorem udiv_phase (n r q a : ℕ) (hr : 0 < r) (hq : 0 < q) (hrq : r.Coprime q) (ha : a ∈ udiv q)
    (U : ZMod q) (hU : (r : ZMod q) * U = 1) :
    haveI : NeZero q := ⟨hq.ne'⟩
    (stdAddChar (U * (2 * ((n : ℤ) : ZMod q)) * zf q a) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * (2 * (n : ℤ) / (r * q))) *
        rph (q / a) (-4 * n) ((r * a : ℕ) : ℤ) * rph r (-2 * n) ((a * (q / a) : ℕ) : ℤ) := by
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨hd, hq0, hab⟩ := mem_udiv ha
  set b := q / a
  have hqab : q = a * b := (Nat.mul_div_cancel' hd).symm
  have ha0 : 0 < a := Nat.pos_of_dvd_of_pos hd hq
  have hb0 : 0 < b := Nat.div_pos (Nat.le_of_dvd hq hd) ha0
  haveI : NeZero a := ⟨ha0.ne'⟩
  haveI : NeZero b := ⟨hb0.ne'⟩
  haveI : NeZero r := ⟨hr.ne'⟩
  have hra : r.Coprime a := Nat.Coprime.coprime_dvd_right hd hrq
  have hrb : r.Coprime b := Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hd) hrq
  have hcore := phase_core r a b q hqab hra hrb hab (n : ℤ) U hU (zfI a b) (zfI_cast_a a b hab)
    (zfI_cast_b a b)
  have hzf : zf q a = ((zfI a b : ℤ) : ZMod q) := rfl
  rw [hzf, hcore]
  have hu1 : IsUnit (((r * a : ℕ) : ZMod b)) := by
    rw [ZMod.isUnit_iff_coprime]; exact Nat.coprime_mul_iff_left.mpr ⟨hrb, hab⟩
  have hu2 : IsUnit (((a * b : ℕ) : ZMod r)) := by
    rw [ZMod.isUnit_iff_coprime]; exact Nat.coprime_mul_iff_left.mpr ⟨hra.symm, hrb.symm⟩
  unfold rph
  rw [dif_neg hb0.ne', dif_neg hr.ne']
  unfold RML.ExpSum.Weil.reciprocalPhase
  push_cast at hu1 hu2 ⊢
  rw [if_pos hu1, if_pos hu2]

/-- **`T_{rq}` expanded.** -/
theorem Tc_expand (n r q : ℕ) (hr : 0 < r) (hq : 0 < q) (hrq : r.Coprime q) (hodd : Odd q)
    (hn : Nat.Coprime n q) :
    Poin.Tc n (r * q) = (haveI : NeZero r := ⟨hr.ne'⟩; Tq r ((Nat.gcdA q r : ℤ) : ZMod r) (n : ZMod r)) *
      ((jacobiSym (-(n : ℤ)) q : ℂ) * q *
        ∑ a ∈ udiv q, Complex.exp (2 * Real.pi * Complex.I * (2 * (n : ℤ) / (r * q))) *
          rph (q / a) (-4 * n) ((r * a : ℕ) : ℤ) * rph r (-2 * n) ((a * (q / a) : ℕ) : ℤ)) := by
  haveI : NeZero r := ⟨hr.ne'⟩
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : NeZero (r * q) := ⟨(Nat.mul_pos hr hq).ne'⟩
  set s' : ℤ := Nat.gcdA q r
  set r' : ℤ := Nat.gcdB q r
  have hbez : s' * q + r' * r = 1 := by
    have := Nat.gcd_eq_gcd_ab q r
    rw [Nat.Coprime.gcd_eq_one hrq.symm] at this
    push_cast at this; linear_combination -this
  unfold Poin.Tc
  rw [dif_pos (Nat.mul_pos hr hq)]
  have hT := Tq_mul hrq r' s' hbez 1 n
  simp only [Int.cast_one, mul_one, Int.cast_natCast] at hT
  rw [hT]
  congr 1
  have hnq : IsCoprime ((n : ℤ)) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hn
  have hrq' : IsCoprime r' (q : ℤ) := ⟨r, s', by linear_combination hbez⟩
  rw [show ((n : ℕ) : ZMod q) = (((n : ℤ)) : ZMod q) by push_cast; rfl,
    Tq_coprime (n : ℤ) q hodd hnq r' hrq', Rq_udiv hodd r' (n : ℤ) hnq]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  have hU : (r : ZMod q) * (r' : ZMod q) = 1 := by
    have := congrArg (fun t : ℤ => (t : ZMod q)) hbez
    push_cast at this; simpa [mul_comm] using this
  have := udiv_phase n r q a hr hq hrq ha (r' : ZMod q) hU
  push_cast at this ⊢
  rw [← this]

/-- The phase of `phase_core` in `rph` form, for any `q = ab` and `z ≡ 1 (a)`, `z ≡ −1 (b)`. -/
theorem phase_rph (r a b q : ℕ) (hq : q = a * b) (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (hra : r.Coprime a) (hrb : r.Coprime b) (hab : a.Coprime b) (n : ℤ) (U : ZMod q)
    (hU : (r : ZMod q) * U = 1) (z : ℤ) (hz1 : (z : ZMod a) = 1) (hz2 : (z : ZMod b) = -1) :
    haveI : NeZero q := ⟨by rw [hq]; positivity⟩
    (stdAddChar (U * (2 * (n : ZMod q)) * (z : ZMod q)) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * (2 * n / (r * q))) *
        rph b (-4 * n) ((r * a : ℕ) : ℤ) * rph r (-2 * n) ((a * b : ℕ) : ℤ) := by
  haveI : NeZero q := ⟨by rw [hq]; positivity⟩
  haveI : NeZero a := ⟨ha.ne'⟩
  haveI : NeZero b := ⟨hb.ne'⟩
  haveI : NeZero r := ⟨hr.ne'⟩
  rw [phase_core r a b q hq hra hrb hab n U hU z hz1 hz2]
  have hu1 : IsUnit (((r * a : ℕ) : ZMod b)) := by
    rw [ZMod.isUnit_iff_coprime]; exact Nat.coprime_mul_iff_left.mpr ⟨hrb, hab⟩
  have hu2 : IsUnit (((a * b : ℕ) : ZMod r)) := by
    rw [ZMod.isUnit_iff_coprime]; exact Nat.coprime_mul_iff_left.mpr ⟨hra.symm, hrb.symm⟩
  unfold rph
  rw [dif_neg hb.ne', dif_neg hr.ne']
  unfold RML.ExpSum.Weil.reciprocalPhase
  push_cast at hu1 hu2 ⊢
  rw [if_pos hu1, if_pos hu2]

/-- **Form 1 = form 2.** -/
theorem form_swap (r a b : ℕ) (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (hra : r.Coprime a) (hrb : r.Coprime b) (hab : a.Coprime b) (n : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (2 * n / (r * (a * b : ℕ)))) *
        rph b (-4 * n) ((r * a : ℕ) : ℤ) * rph r (-2 * n) ((a * b : ℕ) : ℤ) =
      Complex.exp (2 * Real.pi * Complex.I * (2 * (-n) / (r * (b * a : ℕ)))) *
        rph a (-4 * (-n)) ((r * b : ℕ) : ℤ) * rph r (-2 * (-n)) ((b * a : ℕ) : ℤ) := by
  set q := a * b
  haveI : NeZero q := ⟨by positivity⟩
  have hrq : r.Coprime q := Nat.Coprime.mul_right hra hrb
  -- an inverse of `r` mod `q`
  obtain ⟨U, hU⟩ : ∃ U : ZMod q, (r : ZMod q) * U = 1 :=
    ⟨((ZMod.unitOfCoprime r hrq)⁻¹ : (ZMod q)ˣ), by
      rw [← ZMod.coe_unitOfCoprime r hrq, ← Units.val_mul, mul_inv_cancel, Units.val_one]⟩
  have h1 := phase_rph r a b q rfl hr ha hb hra hrb hab n U hU (zfI a b) (zfI_cast_a a b hab)
    (zfI_cast_b a b)
  have h2 := phase_rph r b a q (mul_comm a b) hr hb ha hrb hra hab.symm (-n) U hU (-(zfI a b))
    (by push_cast; rw [zfI_cast_b]; ring) (by push_cast; rw [zfI_cast_a a b hab])
  rw [show (b * a : ℕ) = q from mul_comm b a] at h2
  rw [show (b * a : ℕ) = q from mul_comm b a, ← h1]
  push_cast at h2 ⊢
  rw [← h2]
  congr 1
  ring

end ThreeSquares
