/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import rml.weil.crt_and_completion

/-!
# Kloosterman sums to general moduli

* `sfp N`: the squarefull part of `N` (product of the `p^e ∥ N` with `e ≥ 2`);
* `norm_kl_le`: `|S(a, b; N)| ≤ 2^{ω(N)} √N √(gcd(a, N)) √(sfp N)` (Weil on the squarefree part via
  the toolkit, trivial on the squarefull part);
* `norm_interval_reciprocal_le`: incomplete sums `∑_{j < L} e(a/(x+j))` over units.
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset RML.ExpSum.Weil

/-- The squarefull part of `N`. -/
noncomputable def sfp (N : ℕ) : ℕ :=
  ∏ p ∈ N.primeFactors, if N.factorization p = 1 then 1 else p ^ N.factorization p

theorem sfp_pos (N : ℕ) : 0 < sfp N := by
  unfold sfp
  refine Finset.prod_pos fun p hp => ?_
  split_ifs
  · exact one_pos
  · exact pow_pos (Nat.pos_of_mem_primeFactors hp) _

theorem sfp_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : m.Coprime n) :
    sfp (m * n) = sfp m * sfp n := by
  unfold sfp
  rw [Nat.Coprime.primeFactors_mul h, Finset.prod_union (Nat.Coprime.disjoint_primeFactors h)]
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hpn : n.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      have := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hd
      rw [h.gcd_eq_one] at this
      exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.dvd_one.mp this)
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply, hpn, add_zero]
  · refine Finset.prod_congr rfl fun p hp => ?_
    have hpm : m.factorization p = 0 := by
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hd
      have := Nat.dvd_gcd hd (Nat.dvd_of_mem_primeFactors hp)
      rw [h.gcd_eq_one] at this
      exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.dvd_one.mp this)
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply, hpm, zero_add]

theorem norm_kl_le_card (N : ℕ) [NeZero N] (a b : ZMod N) :
    ‖kloostermanUnitSum N a b‖ ≤ N := by
  unfold kloostermanUnitSum
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_stdAddChar_eq_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have : Fintype.card (ZMod N)ˣ ≤ N := by
    rw [ZMod.card_units_eq_totient]; exact Nat.totient_le N
  exact_mod_cast this

theorem gcd_val_mul_unit {m : ℕ} [NeZero m] (u x : ZMod m) (hu : IsUnit u) :
    Nat.gcd (u * x).val m = Nat.gcd x.val m := by
  have key : ∀ d, d ∣ m → (d ∣ (u * x).val ↔ d ∣ x.val) := by
    intro d hd
    have e : ∀ y : ZMod m, d ∣ y.val ↔ ZMod.castHom hd (ZMod d) y = 0 := by
      intro y
      rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
    rw [e, e, map_mul]
    exact (hu.map (ZMod.castHom hd (ZMod d))).mul_right_eq_zero
  apply Nat.dvd_antisymm
  · exact Nat.dvd_gcd ((key _ (Nat.gcd_dvd_right _ _)).mp (Nat.gcd_dvd_left _ _)) (Nat.gcd_dvd_right _ _)
  · exact Nat.dvd_gcd ((key _ (Nat.gcd_dvd_right _ _)).mpr (Nat.gcd_dvd_left _ _)) (Nat.gcd_dvd_right _ _)

theorem crt_fst_eq {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n) (y : ZMod (m * n)) :
    (ZMod.chineseRemainder h y).1 = ((y.val : ℕ) : ZMod m) := by
  have : (ZMod.chineseRemainder h y).1 = ((RingHom.fst _ _).comp (ZMod.chineseRemainder h).toRingHom) y := rfl
  rw [this]; conv_lhs => rw [← ZMod.natCast_zmod_val y]
  rw [map_natCast]

theorem crt_snd_eq {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n) (y : ZMod (m * n)) :
    (ZMod.chineseRemainder h y).2 = ((y.val : ℕ) : ZMod n) := by
  have : (ZMod.chineseRemainder h y).2 = ((RingHom.snd _ _).comp (ZMod.chineseRemainder h).toRingHom) y := rfl
  rw [this]; conv_lhs => rw [← ZMod.natCast_zmod_val y]
  rw [map_natCast]

theorem gcd_val_natCast (m k : ℕ) [NeZero m] : Nat.gcd ((k : ZMod m).val) m = Nat.gcd k m := by
  rw [ZMod.val_natCast, ← Nat.gcd_rec, Nat.gcd_comm]

/-- **General Kloosterman bound.** -/
theorem norm_kl_le_aux : ∀ N : ℕ, ∀ hN : N ≠ 0, ∀ a b : ZMod N,
    haveI : NeZero N := ⟨hN⟩
    ‖kloostermanUnitSum N a b‖ ≤ 2 ^ N.primeFactors.card * Real.sqrt N *
      Real.sqrt (Nat.gcd a.val N) * Real.sqrt (sfp N) := by
  intro N
  induction N using Nat.recOnPrimeCoprime with
  | zero => intro h; exact absurd rfl h
  | prime_pow p k hp =>
    intro hN a b
    haveI : NeZero (p ^ k) := ⟨hN⟩
    haveI : Fact p.Prime := ⟨hp⟩
    have hg1 : (1 : ℝ) ≤ Real.sqrt (Nat.gcd a.val (p ^ k)) := by
      rw [Real.one_le_sqrt]
      exact_mod_cast Nat.gcd_pos_of_pos_right _ (pow_pos hp.pos k)
    have hs1 : (1 : ℝ) ≤ Real.sqrt (sfp (p ^ k)) := by
      rw [Real.one_le_sqrt]; exact_mod_cast sfp_pos _
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · have := norm_kl_le_card (p ^ 0) a b
        simp only [pow_zero, Nat.cast_one] at this hg1 hs1 ⊢
        simp only [Nat.primeFactors_one, Finset.card_empty, pow_zero, Real.sqrt_one, one_mul]
        nlinarith [mul_le_mul hg1 hs1 zero_le_one (by positivity)]
      · -- prime modulus
        have hf : (p ^ 1).primeFactors.card = 1 := by
          rw [pow_one, hp.primeFactors, Finset.card_singleton]
        rw [hf]
        haveI : Fact (p ^ 1).Prime := ⟨by rwa [pow_one]⟩
        have key : ∀ (q : ℕ) [NeZero q] [Fact q.Prime] (a b : ZMod q),
            ‖kloostermanUnitSum q a b‖ ≤ 2 * Real.sqrt q * Real.sqrt (Nat.gcd a.val q) := by
          intro q _ _ a b
          have hgq : (1 : ℝ) ≤ Real.sqrt (Nat.gcd a.val q) := by
            rw [Real.one_le_sqrt]
            exact_mod_cast Nat.gcd_pos_of_pos_right _ (Fact.out : q.Prime).pos
          by_cases hab : a ≠ 0 ∨ b ≠ 0
          · have := kloostermanUnitSum_prime_le_two_sqrt_of_not_both_zero prime_bound q a b hab
            nlinarith [Real.sqrt_nonneg (q : ℝ)]
          · push_neg at hab
            obtain ⟨rfl, rfl⟩ := hab
            have h1 := norm_kl_le_card q 0 0
            rw [ZMod.val_zero, Nat.gcd_zero_left]
            have hq : (q : ℝ) = Real.sqrt q * Real.sqrt q :=
              (Real.mul_self_sqrt (Nat.cast_nonneg q)).symm
            nlinarith [Real.sqrt_nonneg (q : ℝ)]
        have := key (p ^ 1) a b
        have h0 : 0 ≤ 2 * Real.sqrt ((p ^ 1 : ℕ) : ℝ) * Real.sqrt ((Nat.gcd a.val (p ^ 1) : ℕ) : ℝ) := by
          positivity
        rw [pow_one 2]
        nlinarith [mul_le_mul_of_nonneg_left hs1 h0]
    · -- squarefull prime power: trivial bound
      have hsf : sfp (p ^ k) = p ^ k := by
        unfold sfp
        rw [Nat.primeFactors_prime_pow (by omega) hp, Finset.prod_singleton,
          Nat.Prime.factorization_pow hp, Finsupp.single_eq_same, if_neg (by omega)]
      rw [hsf]
      have h1 := norm_kl_le_card (p ^ k) a b
      have hq : ((p ^ k : ℕ) : ℝ) = Real.sqrt (p ^ k : ℕ) * Real.sqrt (p ^ k : ℕ) :=
        (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
      have h2 : (1 : ℝ) ≤ 2 ^ (p ^ k).primeFactors.card := one_le_pow₀ (by norm_num)
      have hs0 := Real.sqrt_nonneg ((p ^ k : ℕ) : ℝ)
      calc ‖kloostermanUnitSum (p ^ k) a b‖ ≤ Real.sqrt (p ^ k : ℕ) * Real.sqrt (p ^ k : ℕ) := by
            rw [← hq]; exact h1
        _ ≤ 2 ^ (p ^ k).primeFactors.card * Real.sqrt (p ^ k : ℕ) *
              Real.sqrt (Nat.gcd a.val (p ^ k)) * Real.sqrt (p ^ k : ℕ) := by
            have : Real.sqrt (p ^ k : ℕ) ≤ 2 ^ (p ^ k).primeFactors.card * Real.sqrt (p ^ k : ℕ) *
                Real.sqrt (Nat.gcd a.val (p ^ k)) := by
              have hx : 1 ≤ 2 ^ (p ^ k).primeFactors.card * Real.sqrt (Nat.gcd a.val (p ^ k)) := by
                nlinarith
              nlinarith [mul_le_mul_of_nonneg_left hx hs0]
            exact mul_le_mul_of_nonneg_right this hs0
  | coprime m n hm hn hmn ihm ihn =>
    intro hN a b
    haveI : NeZero m := ⟨by omega⟩
    haveI : NeZero n := ⟨by omega⟩
    haveI : NeZero (m * n) := ⟨hN⟩
    rw [norm_kloostermanUnitSum_crt hmn a b]
    have hA := ihm (by omega) (((crtLeftCoeff m n : ℤ) : ZMod m) * (ZMod.chineseRemainder hmn a).1)
      (((crtLeftCoeff m n : ℤ) : ZMod m) * (ZMod.chineseRemainder hmn b).1)
    have hB := ihn (by omega) (((crtRightCoeff m n : ℤ) : ZMod n) * (ZMod.chineseRemainder hmn a).2)
      (((crtRightCoeff m n : ℤ) : ZMod n) * (ZMod.chineseRemainder hmn b).2)
    have gA : Nat.gcd (((crtLeftCoeff m n : ℤ) : ZMod m) * (ZMod.chineseRemainder hmn a).1).val m =
        Nat.gcd a.val m := by
      rw [gcd_val_mul_unit _ _ (crtLeftCoeff_isUnit hmn), crt_fst_eq, gcd_val_natCast]
    have gB : Nat.gcd (((crtRightCoeff m n : ℤ) : ZMod n) * (ZMod.chineseRemainder hmn a).2).val n =
        Nat.gcd a.val n := by
      rw [gcd_val_mul_unit _ _ (crtRightCoeff_isUnit hmn), crt_snd_eq, gcd_val_natCast]
    rw [gA] at hA
    rw [gB] at hB
    have hg : Nat.gcd a.val (m * n) = Nat.gcd a.val m * Nat.gcd a.val n :=
      Nat.Coprime.gcd_mul a.val hmn
    rw [Nat.Coprime.primeFactors_mul hmn, Finset.card_union_of_disjoint
      (Nat.Coprime.disjoint_primeFactors hmn), pow_add, hg, sfp_mul (by omega) (by omega) hmn]
    push_cast
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    calc _ ≤ (2 ^ m.primeFactors.card * Real.sqrt m * Real.sqrt (Nat.gcd a.val m) * Real.sqrt (sfp m)) *
          (2 ^ n.primeFactors.card * Real.sqrt n * Real.sqrt (Nat.gcd a.val n) * Real.sqrt (sfp n)) :=
          mul_le_mul hA hB (norm_nonneg _) (by positivity)
      _ = _ := by ring

theorem norm_kl_le (N : ℕ) [NeZero N] (a b : ZMod N) :
    ‖kloostermanUnitSum N a b‖ ≤ 2 ^ N.primeFactors.card * Real.sqrt N *
      Real.sqrt (Nat.gcd a.val N) * Real.sqrt (sfp N) :=
  norm_kl_le_aux N (NeZero.ne N) a b

/-- The general Weil constant. -/
noncomputable def klC (N : ℕ) (a : ZMod N) : ℝ :=
  2 ^ N.primeFactors.card * Real.sqrt N * Real.sqrt (Nat.gcd a.val N) * Real.sqrt (sfp N)

theorem klC_nonneg (N : ℕ) (a : ZMod N) : 0 ≤ klC N a := by unfold klC; positivity

/-- **Incomplete Kloosterman sums**, general modulus. -/
theorem norm_interval_reciprocal_le (N : ℕ) [NeZero N] (a x : ZMod N) (L : ℕ) :
    ‖∑ j ∈ range L, reciprocalPhase N a (x + (j : ZMod N))‖ ≤
      ((L : ℝ) / N + (1 + Real.log N)) * klC N a := by
  have hcent := centeredIntervalSum_norm_le_of_dft_bound a x L (klC_nonneg N a)
    (fun h hh => by rw [dft_centeredReciprocalPhase_nonzero N a hh]; exact norm_kl_le N a (-h))
  have hsplit : ∑ j ∈ range L, reciprocalPhase N a (x + (j : ZMod N)) =
      centeredIntervalSum N a x L + L * reciprocalMean N a := by
    unfold centeredIntervalSum centeredReciprocalPhase
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hmean : ‖reciprocalMean N a‖ ≤ klC N a / N := by
    unfold reciprocalMean
    have hs := sum_reciprocalPhase_eq_kloostermanUnitSum N a 0
    simp only [zero_mul, AddChar.map_zero_eq_one, one_mul] at hs
    rw [hs, norm_mul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (norm_kl_le N a 0) (Nat.cast_nonneg _)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  rw [hsplit]
  calc _ ≤ ‖centeredIntervalSum N a x L‖ + (L : ℝ) * ‖reciprocalMean N a‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_natCast]
    _ ≤ klC N a * (1 + Real.log N) + (L : ℝ) * (klC N a / N) := by
        gcongr
    _ = _ := by field_simp; ring

end ThreeSquares
