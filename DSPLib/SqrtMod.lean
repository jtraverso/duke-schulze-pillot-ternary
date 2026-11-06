/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DSPLib.Divisor
public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Square roots modulo `M`

`rootCount c M` is the number of `t ∈ ZMod M` with `t² = c`. It is multiplicative in `M`
(`rootCount_mul`, Chinese remainder theorem). At a prime power it is at most `2` when `p` is odd
and does not divide `c`, and at most `4 |c|` in general (`rootCount_prime_pow_le`).
-/

@[expose] public section

namespace DSP

/-- The number of square roots of `c` modulo `M`. -/
noncomputable def rootCount (c : ℤ) (M : ℕ) : ℕ := Nat.card {t : ZMod M // t ^ 2 = (c : ZMod M)}

theorem rootCount_mul (c : ℤ) {m n : ℕ} (h : m.Coprime n) :
    rootCount c (m * n) = rootCount c m * rootCount c n := by
  unfold rootCount
  rw [← Nat.card_prod]
  apply Nat.card_congr
  let e := ZMod.chineseRemainder h
  refine (e.toEquiv.subtypeEquiv (p := fun t : ZMod (m * n) => t ^ 2 = (c : ZMod (m * n)))
    (q := fun x : ZMod m × ZMod n => x.1 ^ 2 = (c : ZMod m) ∧ x.2 ^ 2 = (c : ZMod n))
    (fun t => ?_)).trans (Equiv.subtypeProdEquivProd (p := fun a : ZMod m => a ^ 2 = (c : ZMod m))
      (q := fun b : ZMod n => b ^ 2 = (c : ZMod n)))
  have hc : e (c : ZMod (m * n)) = ((c : ZMod m), (c : ZMod n)) := by
    rw [map_intCast]; rfl
  constructor
  · intro ht
    have := congrArg e ht
    rw [map_pow, hc] at this
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · rintro ⟨h1, h2⟩
    apply e.injective
    rw [map_pow, hc]
    exact Prod.ext h1 h2

theorem rootCount_one (c : ℤ) : rootCount c 1 = 1 := by
  unfold rootCount
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨0, Subsingleton.elim _ _⟩, fun x => Subtype.ext (Subsingleton.elim _ _)⟩

/-- Integers in one residue class modulo `q ∣ N` among the residues modulo `N`. -/
theorem card_residue_class_le {N q : ℕ} [NeZero N] (hq : q ∣ N) (r : ℤ) :
    ((Finset.univ : Finset (ZMod N)).filter (fun t => (q : ℤ) ∣ (t.val : ℤ) - r)).card ≤ N / q := by
  calc ((Finset.univ : Finset (ZMod N)).filter (fun t => (q : ℤ) ∣ (t.val : ℤ) - r)).card
      ≤ (Finset.range (N / q)).card := by
        apply Finset.card_le_card_of_injOn (fun t => t.val / q)
        · intro t _
          simp only [Finset.coe_range, Set.mem_Iio]
          exact Nat.div_lt_div_of_lt_of_dvd hq (ZMod.val_lt t)
        · intro t ht t' ht' heq
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ht'
          apply ZMod.val_injective
          have hmod : t.val % q = t'.val % q := by
            have h1 : (q : ℤ) ∣ (t.val : ℤ) - t'.val := by
              have := dvd_sub ht ht'; simpa using this
            have h2 : ((t.val : ℤ) % q) = ((t'.val : ℤ) % q) :=
                Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
              (Int.emod_eq_zero_of_dvd h1)
            exact_mod_cast h2
          rw [← Nat.div_add_mod t.val q, ← Nat.div_add_mod t'.val q]
          simp only at heq
          rw [heq, hmod]
    _ = N / q := Finset.card_range _

/-- A prime not dividing `X` gives a power coprime to `X`. -/
theorem coprime_pow_of_not_dvd {p : ℕ} (hp : p.Prime) {X : ℤ} (hX : ¬ (p : ℤ) ∣ X) (m : ℕ) :
    IsCoprime ((p : ℤ) ^ m) X := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  have h1 : Nat.Coprime p X.natAbs :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => hX (Int.natCast_dvd.mpr h))
  have h2 := h1.pow_left m
  simpa [Int.gcd, Int.natAbs_pow] using h2

/-- An odd prime power dividing `(S - S')(S + S')` with `p ∤ S` divides one factor. -/
theorem odd_dvd_sub_or_add {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S S' : ℤ}
    (hS : ¬ (p : ℤ) ∣ S) (h : (p : ℤ) ^ m ∣ (S - S') * (S + S')) :
    (p : ℤ) ^ m ∣ S - S' ∨ (p : ℤ) ^ m ∣ S + S' := by
  by_cases h1 : (p : ℤ) ∣ S - S'
  · have h2 : ¬ (p : ℤ) ∣ S + S' := by
      intro h2
      have h3 : (p : ℤ) ∣ 2 * S := by
        have := dvd_add h1 h2; rwa [show S - S' + (S + S') = 2 * S by ring] at this
      have h4 : p ∣ 2 * S.natAbs := by
        have := Int.natCast_dvd.mp h3; simpa [Int.natAbs_mul] using this
      rcases (Nat.Prime.dvd_mul hp).mp h4 with h5 | h5
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h5)
      · exact hS (Int.natCast_dvd.mpr h5)
    exact Or.inl ((coprime_pow_of_not_dvd hp h2 m).dvd_of_dvd_mul_left (by rwa [mul_comm] at h))
  · exact Or.inr ((coprime_pow_of_not_dvd hp h1 m).dvd_of_dvd_mul_left h)

/-- An odd integer is coprime to every power of two. -/
theorem isCoprime_two_pow_of_odd {X : ℤ} (hX : Odd X) (m : ℕ) : IsCoprime ((2 : ℤ) ^ m) X := by
  obtain ⟨k, rfl⟩ := hX
  have h2 : IsCoprime (2 : ℤ) (2 * k + 1) := ⟨-k, 1, by ring⟩
  exact h2.pow_left

/-- A power of two dividing `(S - S')(S + S')` with `S, S'` odd: one factor takes all but one
factor two. -/
theorem two_dvd_sub_or_add {n : ℕ} {S S' : ℤ} (hS : ¬ (2 : ℤ) ∣ S) (hS' : ¬ (2 : ℤ) ∣ S')
    (h : (2 : ℤ) ^ (n + 1) ∣ (S - S') * (S + S')) :
    (2 : ℤ) ^ n ∣ S - S' ∨ (2 : ℤ) ^ n ∣ S + S' := by
  have hX : (2 : ℤ) ∣ S - S' := by
    rcases Int.even_or_odd S with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact absurd ⟨a, by omega⟩ hS
    · rcases Int.even_or_odd S' with ⟨b, hb⟩ | ⟨b, hb⟩
      · exact absurd ⟨b, by omega⟩ hS'
      · exact ⟨a - b, by omega⟩
  have hY : (2 : ℤ) ∣ S + S' := by
    have := dvd_add hX (⟨S', by ring⟩ : (2 : ℤ) ∣ 2 * S')
    rwa [show S - S' + 2 * S' = S + S' by ring] at this
  obtain ⟨X', hX'⟩ := hX
  obtain ⟨Y', hY'⟩ := hY
  have hcancel : ∀ Z : ℤ, (2 : ℤ) ^ (n + 1) ∣ 4 * Z → (2 : ℤ) ^ n ∣ 2 * Z := by
    intro Z hZ
    rw [pow_succ, show (4 : ℤ) * Z = 2 * Z * 2 by ring] at hZ
    exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).mp hZ
  rcases Int.even_or_odd X' with ⟨e, he⟩ | hXo
  · -- `X'` even, so `Y'` is odd
    have hYo : Odd Y' := by
      refine ⟨(S - S' + (S + S')) / 4 - e, ?_⟩
      rcases Int.even_or_odd S with ⟨a, ha⟩ | ⟨a, ha⟩
      · exact absurd ⟨a, by omega⟩ hS
      · omega
    left
    rw [hX']
    apply hcancel
    have h4 : (2 : ℤ) ^ (n + 1) ∣ (4 * X') * Y' := by
      rw [show 4 * X' * Y' = (S - S') * (S + S') by rw [hX', hY']; ring]; exact h
    exact (isCoprime_two_pow_of_odd hYo _).dvd_of_dvd_mul_right h4
  · right
    rw [hY']
    apply hcancel
    have h4 : (2 : ℤ) ^ (n + 1) ∣ (4 * Y') * X' := by
      rw [show 4 * Y' * X' = (S - S') * (S + S') by rw [hX', hY']; ring]; exact h
    exact (isCoprime_two_pow_of_odd hXo _).dvd_of_dvd_mul_right h4

/-- The exact power of a prime in a nonzero integer. -/
theorem exists_exact_pow {p : ℕ} (hp : p.Prime) {c : ℤ} (hc : c ≠ 0) :
    ∃ a : ℕ, (p : ℤ) ^ a ∣ c ∧ ¬ (p : ℤ) ^ (a + 1) ∣ c := by
  obtain ⟨e, n', hn', he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hc) p hp.ne_one
  refine ⟨e, ?_, ?_⟩
  · have : ((p ^ e : ℕ) : ℤ) ∣ c := Int.natCast_dvd.mpr (he ▸ dvd_mul_right _ _)
    exact_mod_cast this
  · intro h
    have h1 : p ^ (e + 1) ∣ c.natAbs := Int.natCast_dvd.mp (by exact_mod_cast h)
    rw [he, pow_succ] at h1
    exact hn' ((Nat.mul_dvd_mul_iff_left (pow_pos hp.pos e)).mp h1)

/-- A root of `t² ≡ c (mod p^k)` with `k` beyond the exponent `a` of `p` in `c` has exponent
`a / 2`. -/
theorem root_shape {p : ℕ} (hp : p.Prime) {c : ℤ} {a k : ℕ} (ha : (p : ℤ) ^ a ∣ c)
    (ha1 : ¬ (p : ℤ) ^ (a + 1) ∣ c) (hak : a < k) {T : ℤ} (hT : (p : ℤ) ^ k ∣ T ^ 2 - c) :
    2 * (a / 2) = a ∧ ∃ S : ℤ, T = (p : ℤ) ^ (a / 2) * S ∧ ¬ (p : ℤ) ∣ S := by
  have hT1 : (p : ℤ) ^ (a + 1) ∣ T ^ 2 - c := (pow_dvd_pow _ hak).trans hT
  have hT0 : T ≠ 0 := by
    rintro rfl
    exact ha1 (by simpa using hT1)
  obtain ⟨b, hb, hb1⟩ := exists_exact_pow hp hT0
  obtain ⟨S, hS⟩ := hb
  have hSp : ¬ (p : ℤ) ∣ S := by
    rintro ⟨u, rfl⟩
    exact hb1 ⟨u, by rw [hS]; ring⟩
  have hT2 : T ^ 2 = (p : ℤ) ^ (2 * b) * S ^ 2 := by rw [hS]; ring
  have hab : 2 * b = a := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · -- `2b < a`: then `p^{2b+1}` divides `T²`, so `p ∣ S`
      have h1 : (p : ℤ) ^ (2 * b + 1) ∣ c := (pow_dvd_pow _ hlt).trans ha
      have h2 : (p : ℤ) ^ (2 * b + 1) ∣ T ^ 2 - c := (pow_dvd_pow _ (by omega)).trans hT1
      have h3 : (p : ℤ) ^ (2 * b + 1) ∣ T ^ 2 := by
        have := dvd_add h2 h1; simpa using this
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      rw [hT2, pow_succ] at h3
      have h4 : (p : ℤ) ∣ S ^ 2 := (mul_dvd_mul_iff_left (pow_ne_zero _ hp0)).mp h3
      have h5 : p ∣ S.natAbs ^ 2 := by
        have := Int.natCast_dvd.mp h4; simpa [Int.natAbs_pow] using this
      exact hSp (Int.natCast_dvd.mpr (hp.dvd_of_dvd_pow h5))
    · -- `2b > a`: then `p^{a+1}` divides `T²`, hence `c`
      have h1 : (p : ℤ) ^ (a + 1) ∣ T ^ 2 := by
        rw [hT2]; exact ((pow_dvd_pow _ hgt).trans (dvd_refl _)).mul_right _
      exact ha1 (by have := dvd_sub h1 hT1; simpa using this)
  refine ⟨by omega, S, ?_, hSp⟩
  rw [hS, show a / 2 = b by omega]

set_option maxHeartbeats 4000000 in
-- The case analysis and `omega`/`nlinarith` calls exceed the default heartbeat budget.
/-- **Square roots modulo a prime power**: at most `4 |c|`, and at most `2` for odd `p ∤ c`. -/
theorem rootCount_prime_pow_le {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) {c : ℤ} (hc : c ≠ 0) :
    rootCount c (p ^ k) ≤ 4 * c.natAbs ∧ (p ≠ 2 → ¬ (p : ℤ) ∣ c → rootCount c (p ^ k) ≤ 2) := by
  classical
  have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  have : NeZero (p ^ k) := ⟨hpk⟩
  have hcount : rootCount c (p ^ k) = ((Finset.univ : Finset (ZMod (p ^ k))).filter
      (fun t => ((p ^ k : ℕ) : ℤ) ∣ (t.val : ℤ) ^ 2 - c)).card := by
    unfold rootCount
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, sub_eq_zero]
  obtain ⟨a, ha, ha1⟩ := exists_exact_pow hp hc
  have hpa_le : p ^ a ≤ c.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr hc) (Int.natCast_dvd.mp (by exact_mod_cast ha))
  by_cases hka : k ≤ a
  · have h1 : rootCount c (p ^ k) ≤ p ^ k := by
      rw [hcount]
      exact (Finset.card_filter_le _ _).trans (by simp [ZMod.card])
    refine ⟨h1.trans ((Nat.pow_le_pow_right hp.pos hka).trans (hpa_le.trans (by omega))),
      fun _ hpc => absurd ((dvd_pow_self (p : ℤ) (by omega : a ≠ 0)).trans ha) hpc⟩
  push Not at hka
  set b := a / 2 with hb
  have hpb_le : p ^ b ≤ c.natAbs :=
    (Nat.pow_le_pow_right hp.pos (by omega)).trans hpa_le
  have hcast : ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ k := by push_cast; rfl
  -- no root: nothing to count
  by_cases hne : ∃ t₀ : ZMod (p ^ k), ((p ^ k : ℕ) : ℤ) ∣ (t₀.val : ℤ) ^ 2 - c
  swap
  · push Not at hne
    have : rootCount c (p ^ k) = 0 := by
      rw [hcount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun t _ => hne t
    rw [this]; exact ⟨Nat.zero_le _, fun _ _ => Nat.zero_le _⟩
  obtain ⟨t₀, ht₀⟩ := hne
  rw [hcast] at ht₀
  obtain ⟨h2b, S₀, hS₀, hS₀p⟩ := root_shape hp ha ha1 hka ht₀
  rw [← hb] at hS₀
  -- every root is `±t₀` modulo `p^{k-b}` (odd `p`) or `2^{k-b-1}` (`p = 2`)
  have hdiff : ∀ t : ZMod (p ^ k), (p : ℤ) ^ k ∣ (t.val : ℤ) ^ 2 - c →
      ∃ S : ℤ, (t.val : ℤ) = (p : ℤ) ^ b * S ∧ ¬ (p : ℤ) ∣ S ∧
        (p : ℤ) ^ (k - 2 * b) ∣ (S - S₀) * (S + S₀) := by
    intro t ht
    obtain ⟨-, S, hS, hSp⟩ := root_shape hp ha ha1 hka ht
    refine ⟨S, hS, hSp, ?_⟩
    have h1 : (p : ℤ) ^ k ∣ ((t.val : ℤ) ^ 2 - c) - ((t₀.val : ℤ) ^ 2 - c) := dvd_sub ht ht₀
    rw [show ((t.val : ℤ) ^ 2 - c) - ((t₀.val : ℤ) ^ 2 - c) =
        (p : ℤ) ^ (2 * b) * ((S - S₀) * (S + S₀)) by rw [hS, hS₀]; ring,
      show k = 2 * b + (k - 2 * b) by omega, pow_add] at h1
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))).mp h1
  -- the two classes
  have hclass : ∀ (q : ℕ), q ∣ p ^ k → 0 < q →
      (∀ t : ZMod (p ^ k), (p : ℤ) ^ k ∣ (t.val : ℤ) ^ 2 - c →
        (q : ℤ) ∣ (t.val : ℤ) - t₀.val ∨ (q : ℤ) ∣ (t.val : ℤ) - (-(t₀.val : ℤ))) →
      rootCount c (p ^ k) ≤ 2 * (p ^ k / q) := by
    intro q hq hq0 hroots
    rw [hcount]
    calc _ ≤ ((Finset.univ.filter (fun t : ZMod (p ^ k) => (q : ℤ) ∣ (t.val : ℤ) - t₀.val)) ∪
          (Finset.univ.filter (fun t : ZMod (p ^ k) => (q : ℤ) ∣ (t.val : ℤ) -
              (-(t₀.val : ℤ))))).card := by
          apply Finset.card_le_card
          intro t ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at ht ⊢
          rw [hcast] at ht
          exact hroots t ht
      _ ≤ (p ^ k / q) + (p ^ k / q) :=
          (Finset.card_union_le _ _).trans (Nat.add_le_add (card_residue_class_le hq _)
            (card_residue_class_le hq _))
      _ = 2 * (p ^ k / q) := by ring
  by_cases hp2 : p = 2
  · subst hp2
    have hroots : ∀ t : ZMod (2 ^ k), (2 : ℤ) ^ k ∣ (t.val : ℤ) ^ 2 - c →
        (((2 ^ (k - b - 1) : ℕ)) : ℤ) ∣ (t.val : ℤ) - t₀.val ∨
          (((2 ^ (k - b - 1) : ℕ)) : ℤ) ∣ (t.val : ℤ) - (-(t₀.val : ℤ)) := by
      intro t ht
      obtain ⟨S, hS, hSp, hdv⟩ := hdiff t (by exact_mod_cast ht)
      rw [show k - 2 * b = (k - 2 * b - 1) + 1 by omega] at hdv
      have hS₀' : ¬ ((2 : ℕ) : ℤ) ∣ S₀ := hS₀p
      rcases two_dvd_sub_or_add (by exact_mod_cast hSp) (by exact_mod_cast hS₀')
          (by exact_mod_cast hdv) with h | h
      · left
        rw [hS, hS₀]
        push_cast
        rw [show (2 : ℤ) ^ b * S - 2 ^ b * S₀ = 2 ^ b * (S - S₀) by ring,
          show k - b - 1 = b + (k - 2 * b - 1) by omega, pow_add]
        exact mul_dvd_mul_left _ h
      · right
        rw [hS, hS₀]
        push_cast
        rw [show (2 : ℤ) ^ b * S - -(2 ^ b * S₀) = 2 ^ b * (S + S₀) by ring,
          show k - b - 1 = b + (k - 2 * b - 1) by omega, pow_add]
        exact mul_dvd_mul_left _ h
    have hle := hclass (2 ^ (k - b - 1)) (pow_dvd_pow _ (by omega)) (by positivity) hroots
    rw [Nat.pow_div (by omega) (by norm_num), show k - (k - b - 1) = b + 1 by omega] at hle
    refine ⟨hle.trans ?_, fun h => absurd rfl h⟩
    rw [pow_succ]
    omega
  · have hroots : ∀ t : ZMod (p ^ k), (p : ℤ) ^ k ∣ (t.val : ℤ) ^ 2 - c →
        (((p ^ (k - b) : ℕ)) : ℤ) ∣ (t.val : ℤ) - t₀.val ∨
          (((p ^ (k - b) : ℕ)) : ℤ) ∣ (t.val : ℤ) - (-(t₀.val : ℤ)) := by
      intro t ht
      obtain ⟨S, hS, hSp, hdv⟩ := hdiff t ht
      rcases odd_dvd_sub_or_add hp hp2 hSp hdv with h | h
      · left
        rw [hS, hS₀]
        push_cast
        rw [show (p : ℤ) ^ b * S - (p : ℤ) ^ b * S₀ = (p : ℤ) ^ b * (S - S₀) by ring,
          show k - b = b + (k - 2 * b) by omega, pow_add]
        exact mul_dvd_mul_left _ h
      · right
        rw [hS, hS₀]
        push_cast
        rw [show (p : ℤ) ^ b * S - -((p : ℤ) ^ b * S₀) = (p : ℤ) ^ b * (S + S₀) by ring,
          show k - b = b + (k - 2 * b) by omega, pow_add]
        exact mul_dvd_mul_left _ h
    have hle := hclass (p ^ (k - b)) (pow_dvd_pow _ (by omega)) (pow_pos hp.pos _) hroots
    rw [Nat.pow_div (by omega) hp.pos, show k - (k - b) = b by omega] at hle
    refine ⟨hle.trans (by omega), fun _ hpc => hle.trans ?_⟩
    -- `p ∤ c` forces `a = 0`, hence `b = 0`
    have ha0 : a = 0 := by
      by_contra h0
      exact hpc ((dvd_pow_self (p : ℤ) h0).trans ha)
    have hb0 : b = 0 := by omega
    rw [hb0]; simp

/-- **Square roots modulo `M`**: `rootCount c M ≤ (2|c|)^{|c|+2} d(M)`. -/
theorem rootCount_le {c : ℤ} (hc : c ≠ 0) {M : ℕ} (hM : M ≠ 0) :
    rootCount c M ≤ (2 * c.natAbs) ^ (c.natAbs + 2) * M.divisors.card := by
  classical
  have hfac := Nat.multiplicative_factorization (rootCount c) (fun x y h => rootCount_mul c h)
    (rootCount_one c) hM
  have hdiv : M.divisors.card = M.factorization.prod fun p k => (p ^ k).divisors.card := by
    have := Nat.multiplicative_factorization (fun n => n.divisors.card)
      (fun x y h => by
        have := (ArithmeticFunction.isMultiplicative_sigma (k := 0)).map_mul_of_coprime h
        simpa [ArithmeticFunction.sigma_zero_apply] using this)
      (by simp) hM
    exact this
  rw [hfac, hdiv, Finsupp.prod, Finsupp.prod]
  set bad : ℕ → Prop := fun p => p = 2 ∨ (p : ℤ) ∣ c with hbad
  have hcpos : 1 ≤ c.natAbs := Int.natAbs_pos.mpr hc
  -- each factor is at most `(k + 1)` times `2|c|` (bad primes) or `1` (good primes)
  have hpt : ∀ p ∈ M.factorization.support, rootCount c (p ^ M.factorization p) ≤
      (p ^ M.factorization p).divisors.card * (if bad p then 2 * c.natAbs else 1) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    have hk : 1 ≤ M.factorization p := Finsupp.mem_support_iff.mp hp |> Nat.one_le_iff_ne_zero.mpr
    rw [Nat.divisors_prime_pow hpp, Finset.card_map, Finset.card_range]
    obtain ⟨h1, h2⟩ := rootCount_prime_pow_le hpp hk hc
    split_ifs with hb
    · calc _ ≤ 4 * c.natAbs := h1
        _ ≤ (M.factorization p + 1) * (2 * c.natAbs) := by nlinarith
    · simp only [hbad, not_or] at hb
      calc _ ≤ 2 := h2 hb.1 hb.2
        _ ≤ (M.factorization p + 1) * 1 := by omega
  calc ∏ p ∈ M.factorization.support, rootCount c (p ^ M.factorization p)
      ≤ ∏ p ∈ M.factorization.support,
          ((p ^ M.factorization p).divisors.card * (if bad p then 2 * c.natAbs else 1)) :=
        Finset.prod_le_prod hpt
    _ = (∏ p ∈ M.factorization.support, (p ^ M.factorization p).divisors.card) *
          ∏ p ∈ M.factorization.support, (if bad p then 2 * c.natAbs else 1) :=
        Finset.prod_mul_distrib
    _ ≤ (∏ p ∈ M.factorization.support, (p ^ M.factorization p).divisors.card) *
          (2 * c.natAbs) ^ (c.natAbs + 2) := by
        apply Nat.mul_le_mul_left
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
        apply Nat.pow_le_pow_right (by omega)
        calc (M.factorization.support.filter bad).card
            ≤ (Finset.range (c.natAbs + 2)).card := by
              apply Finset.card_le_card
              intro p hp
              simp only [Finset.mem_filter, hbad] at hp
              rw [Finset.mem_range]
              rcases hp.2 with h | h
              · omega
              · have := Nat.le_of_dvd hcpos (Int.natCast_dvd.mp h)
                omega
          _ = c.natAbs + 2 := Finset.card_range _
    _ = (2 * c.natAbs) ^ (c.natAbs + 2) *
          ∏ p ∈ M.factorization.support, (p ^ M.factorization p).divisors.card := by ring

end DSP
