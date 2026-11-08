/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Square roots of `1` modulo odd `q` and unitary divisors

For odd `q`, the solutions of `z² = 1` in `ℤ/q` are in bijection with the unitary divisors `a ∥ q`
(`a ∣ q`, `(a, q/a) = 1`) via `a ↦ zf q a`, the residue `≡ 1 (mod a)`, `≡ −1 (mod q/a)`.
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset

/-- Unitary divisors. -/
def udiv (q : ℕ) : Finset ℕ := q.divisors.filter (fun a => Nat.Coprime a (q / a))

/-- The integer `≡ 1 (mod a)`, `≡ −1 (mod b)` built from Bézout. -/
def zfI (a b : ℕ) : ℤ := 2 * (b : ℤ) * Nat.gcdB a b - 1

theorem zfI_sub_one (a b : ℕ) (h : a.Coprime b) : zfI a b - 1 = -2 * (a : ℤ) * Nat.gcdA a b := by
  have hb := Nat.gcd_eq_gcd_ab a b
  rw [h.gcd_eq_one] at hb
  unfold zfI; push_cast at hb; linear_combination -2 * hb

theorem zfI_add_one (a b : ℕ) : zfI a b + 1 = 2 * (b : ℤ) * Nat.gcdB a b := by
  unfold zfI; ring

/-- The residue `≡ 1 (mod a)`, `≡ −1 (mod q/a)`. -/
def zf (q a : ℕ) : ZMod q := (zfI a (q / a) : ZMod q)

theorem dvd_val_iff {q d : ℕ} [NeZero q] (hd : d ∣ q) (x : ZMod q) :
    d ∣ x.val ↔ ZMod.castHom hd (ZMod d) x = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

theorem zmod_eq_zero_iff_of_coprime {a b : ℕ} [NeZero (a * b)] (h : a.Coprime b) (x : ZMod (a * b)) :
    x = 0 ↔ ZMod.castHom (dvd_mul_right a b) (ZMod a) x = 0 ∧
      ZMod.castHom (dvd_mul_left b a) (ZMod b) x = 0 := by
  rw [← dvd_val_iff, ← dvd_val_iff]
  constructor
  · rintro rfl; simp
  · rintro ⟨h1, h2⟩
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd h h1 h2
    rw [← ZMod.natCast_zmod_val x, ZMod.natCast_eq_zero_iff]
    exact this

theorem intCast_dvd_iff {q : ℕ} [NeZero q] (t : ℤ) : ((t : ZMod q) = 0) ↔ (q : ℤ) ∣ t :=
  ZMod.intCast_zmod_eq_zero_iff_dvd t q

/-- **Roots of unity of order 2 ↔ unitary divisors.** -/
theorem sum_sq_eq_one {q : ℕ} [NeZero q] (hodd : Odd q) (f : ZMod q → ℂ) :
    ∑ z : ZMod q, (if z ^ 2 = 1 then f z else 0) = ∑ a ∈ udiv q, f (zf q a) := by
  classical
  have hq0 : q ≠ 0 := NeZero.ne q
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun a => zf q a) (fun z => Nat.gcd (z - 1).val q) ?_ ?_ ?_ ?_ ?_
  · -- `zf` is a root
    intro a ha
    simp only [udiv, Finset.mem_filter, Nat.mem_divisors] at ha
    obtain ⟨⟨⟨b, hb⟩, -⟩, hab⟩ := ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hb' : q / a = b := by
      rw [hb, Nat.mul_div_cancel_left]; exact Nat.pos_of_ne_zero (by rintro rfl; simp at hb; exact hq0 hb)
    rw [hb'] at hab
    unfold zf
    rw [hb']
    rw [← sub_eq_zero, show ((zfI a b : ℤ) : ZMod q) ^ 2 - 1 = (((zfI a b - 1) * (zfI a b + 1) : ℤ) : ZMod q) by
      push_cast; ring, intCast_dvd_iff, zfI_sub_one a b hab, zfI_add_one, hb]
    exact ⟨-4 * Nat.gcdA a b * Nat.gcdB a b, by push_cast; ring⟩
  · -- `gcd(z − 1, q)` is unitary
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [udiv, Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨Nat.gcd_dvd_right _ _, hq0⟩, ?_⟩
    set g := Nat.gcd (z - 1).val q
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hq0)
    rw [Nat.coprime_iff_gcd_eq_one]
    set d := Nat.gcd g (q / g)
    have hdq : d ∣ q := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    -- `d ∣ z − 1` and `d ∣ z + 1`
    have h1 : d ∣ (z - 1).val := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have hprod : q ∣ (z - 1).val * (z + 1).val := by
      rw [← ZMod.natCast_eq_zero_iff]; push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      linear_combination hz
    have hqg : q / g ∣ (z + 1).val := by
      have hc := Nat.coprime_div_gcd_div_gcd (m := q) (n := (z - 1).val) (by rwa [Nat.gcd_comm])
      have : q / g ∣ ((z - 1).val / g) * (z + 1).val := by
        obtain ⟨k, hk⟩ := hprod
        refine ⟨k, ?_⟩
        have hgq : g ∣ q := Nat.gcd_dvd_right _ _
        have hgz : g ∣ (z - 1).val := Nat.gcd_dvd_left _ _
        apply Nat.eq_of_mul_eq_mul_left hg0
        calc g * ((z - 1).val / g * (z + 1).val) = (z - 1).val * (z + 1).val := by
              rw [← mul_assoc, Nat.mul_div_cancel' hgz]
          _ = q * k := hk
          _ = g * (q / g * k) := by rw [← mul_assoc, Nat.mul_div_cancel' hgq]
      rw [Nat.gcd_comm] at hc
      exact hc.dvd_of_dvd_mul_left this
    have h2 : d ∣ (z + 1).val := (Nat.gcd_dvd_right _ _).trans hqg
    rw [dvd_val_iff hdq] at h1 h2
    have h3 : ZMod.castHom hdq (ZMod d) 2 = 0 := by
      have : (2 : ZMod q) = (z + 1) - (z - 1) := by ring
      rw [this, map_sub, h1, h2, sub_zero]
    rw [map_ofNat, show ((2 : ZMod d)) = ((2 : ℕ) : ZMod d) by norm_num,
      ZMod.natCast_eq_zero_iff] at h3
    have hdodd : Odd d := Odd.of_dvd_nat hodd hdq
    rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
    · exact h
    · exfalso; rw [h] at hdodd; exact (Nat.not_odd_iff_even.mpr even_two) hdodd
  · -- left inverse
    intro a ha
    simp only [udiv, Finset.mem_filter, Nat.mem_divisors] at ha
    obtain ⟨⟨⟨b, hb⟩, -⟩, hab⟩ := ha
    have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hb; exact hq0 hb)
    have hb' : q / a = b := by rw [hb, Nat.mul_div_cancel_left _ ha0]
    rw [hb'] at hab
    unfold zf
    rw [hb']
    -- `gcd(z − 1, q) = gcd(-2 a x, a b) = a`
    have hval : (((zfI a b : ℤ) : ZMod q) - 1) = ((-2 * (a : ℤ) * Nat.gcdA a b : ℤ) : ZMod q) := by
      rw [← zfI_sub_one a b hab]; push_cast; ring
    rw [hval]
    have hbodd : Odd b := Odd.of_dvd_nat hodd ⟨a, by rw [hb, mul_comm]⟩
    apply Nat.dvd_antisymm
    · -- `gcd ∣ a`: the gcd is coprime to `b`
      set g := Nat.gcd ((((-2 * (a : ℤ) * Nat.gcdA a b : ℤ)) : ZMod q).val) q
      have hgq : g ∣ q := Nat.gcd_dvd_right _ _
      have hgv : (g : ℤ) ∣ -2 * (a : ℤ) * Nat.gcdA a b := by
        have h1 : g ∣ ((((-2 * (a : ℤ) * Nat.gcdA a b : ℤ)) : ZMod q).val) := Nat.gcd_dvd_left _ _
        have h2 : ((((((-2 * (a : ℤ) * Nat.gcdA a b : ℤ)) : ZMod q).val : ℕ) : ℤ)) =
            (-2 * (a : ℤ) * Nat.gcdA a b) % q := ZMod.val_intCast _
        have h3 : (g : ℤ) ∣ (-2 * (a : ℤ) * Nat.gcdA a b) % q := by
          rw [← h2]; exact_mod_cast h1
        have h4 : (g : ℤ) ∣ (q : ℤ) := by exact_mod_cast hgq
        have h5 := Int.emod_add_mul_ediv (-2 * (a : ℤ) * Nat.gcdA a b) q
        rw [← h5]; exact dvd_add h3 (dvd_mul_of_dvd_left h4 _)
      -- `gcd(g, b) = 1`
      have hgb : Nat.Coprime g b := by
        rw [Nat.coprime_iff_gcd_eq_one]
        set e := Nat.gcd g b
        have he1 : (e : ℤ) ∣ -2 * (a : ℤ) * Nat.gcdA a b :=
          (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left g b)).trans hgv
        have he2 : (e : ℤ) ∣ (b : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right g b)
        have hbez := Nat.gcd_eq_gcd_ab a b
        rw [hab.gcd_eq_one] at hbez; push_cast at hbez
        have he3 : (e : ℤ) ∣ 2 := by
          have : (2 : ℤ) = -(-2 * (a : ℤ) * Nat.gcdA a b) + 2 * (b * Nat.gcdB a b) := by
            linear_combination 2 * hbez
          rw [this]; exact dvd_add (dvd_neg.mpr he1) (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left he2 _) _)
        have he4 : e ∣ 2 := by exact_mod_cast he3
        have heodd : Odd e := Odd.of_dvd_nat hbodd (Nat.gcd_dvd_right g b)
        rcases (Nat.dvd_prime Nat.prime_two).mp he4 with h | h
        · exact h
        · exfalso; rw [h] at heodd; exact (Nat.not_odd_iff_even.mpr even_two) heodd
      rw [hb] at hgq
      exact hgb.dvd_of_dvd_mul_right hgq
    · -- `a ∣ gcd`
      refine Nat.dvd_gcd ?_ ⟨b, hb⟩
      have hd : a ∣ q := ⟨b, hb⟩
      rw [dvd_val_iff hd, map_intCast]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ⟨-2 * Nat.gcdA a b, by ring⟩
  · -- right inverse
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    set a := Nat.gcd (z - 1).val q
    have ha0 : 0 < a := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hq0)
    have haq : a ∣ q := Nat.gcd_dvd_right _ _
    set b := q / a
    have hq : q = a * b := (Nat.mul_div_cancel' haq).symm
    -- coprimality, as in the previous step
    have hprod : q ∣ (z - 1).val * (z + 1).val := by
      rw [← ZMod.natCast_eq_zero_iff]; push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      linear_combination hz
    have hbz : b ∣ (z + 1).val := by
      have hc := Nat.coprime_div_gcd_div_gcd (m := q) (n := (z - 1).val) (by rwa [Nat.gcd_comm])
      have : q / a ∣ ((z - 1).val / a) * (z + 1).val := by
        obtain ⟨k, hk⟩ := hprod
        refine ⟨k, ?_⟩
        have hgz : a ∣ (z - 1).val := Nat.gcd_dvd_left _ _
        apply Nat.eq_of_mul_eq_mul_left ha0
        calc a * ((z - 1).val / a * (z + 1).val) = (z - 1).val * (z + 1).val := by
              rw [← mul_assoc, Nat.mul_div_cancel' hgz]
          _ = q * k := hk
          _ = a * (q / a * k) := by rw [← mul_assoc, Nat.mul_div_cancel' haq]
      rw [Nat.gcd_comm] at hc
      exact hc.dvd_of_dvd_mul_left this
    have haz : a ∣ (z - 1).val := Nat.gcd_dvd_left _ _
    have hab : a.Coprime b := by
      rw [Nat.coprime_iff_gcd_eq_one]
      set d := Nat.gcd a b
      have hdq : d ∣ q := (Nat.gcd_dvd_left _ _).trans haq
      have h1 : d ∣ (z - 1).val := (Nat.gcd_dvd_left _ _).trans haz
      have h2 : d ∣ (z + 1).val := (Nat.gcd_dvd_right _ _).trans hbz
      rw [dvd_val_iff hdq] at h1 h2
      have h3 : ZMod.castHom hdq (ZMod d) 2 = 0 := by
        have : (2 : ZMod q) = (z + 1) - (z - 1) := by ring
        rw [this, map_sub, h1, h2, sub_zero]
      rw [map_ofNat, show ((2 : ZMod d)) = ((2 : ℕ) : ZMod d) by norm_num,
        ZMod.natCast_eq_zero_iff] at h3
      have hdodd : Odd d := Odd.of_dvd_nat hodd hdq
      rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
      · exact h
      · exfalso; rw [h] at hdodd; exact (Nat.not_odd_iff_even.mpr even_two) hdodd
    -- both sides agree mod `a` and mod `b`
    have key : ∀ (q' : ℕ) [NeZero q'] (hq' : q' = a * b) (z' : ZMod q'),
        a ∣ (z' - 1).val → b ∣ (z' + 1).val → ((zfI a b : ℤ) : ZMod q') = z' := by
      intro q' _ hq' z' h1 h2
      subst hq'
      rw [← sub_eq_zero, zmod_eq_zero_iff_of_coprime hab]
      rw [dvd_val_iff (dvd_mul_right a b)] at h1
      rw [dvd_val_iff (dvd_mul_left b a)] at h2
      constructor
      · have e : ((zfI a b : ℤ) : ZMod (a * b)) - z' =
            (((zfI a b - 1 : ℤ)) : ZMod (a * b)) - (z' - 1) := by push_cast; ring
        rw [e, map_sub, h1, sub_zero, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd,
          zfI_sub_one a b hab]
        exact ⟨-2 * Nat.gcdA a b, by ring⟩
      · have e : ((zfI a b : ℤ) : ZMod (a * b)) - z' =
            (((zfI a b + 1 : ℤ)) : ZMod (a * b)) - (z' + 1) := by push_cast; ring
        rw [e, map_sub, h2, sub_zero, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd, zfI_add_one]
        exact ⟨2 * Nat.gcdB a b, by ring⟩
    unfold zf
    exact key q hq z haz hbz
  · intro a _; rfl

end ThreeSquares
