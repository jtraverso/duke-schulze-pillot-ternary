/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.B3_LocalRoots
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.Data.Nat.Factorization.Induction

/-!
# `Rcount n m ≥ (1 * χ)(m) ≥ 0`

`chi1 n m = ∑_{e ∣ m} J(e | n)` is `(1 * χ)(m)` for the Jacobi character `χ = J(· | n)`.
For `n ≡ 3 (mod 8)` and `m ≥ 1` coprime to `n`:
`chi1_le_Rcount`: `chi1 n m ≤ Rcount n m`, and `chi1_nonneg`: `0 ≤ chi1 n m`.

Proof: `Tsum n m = ∑_{g² ∣ m} sig' (m/g²)` (`sig' k = [k odd] sig n k`) is below `Rcount`
(`sig_le_rootCount`), super-multiplicative (`Tsum_mul_ge`, from `sig_mul`), and on prime powers
`Tsum(p^a) ≥ a + 1 = chi1(p^a)` if `J(p | n) = 1` (then `J(−n | p) = 1` by reciprocity and
`sig'(p^k) ≥ 2`, `two_le_sig`), `Tsum(p^a) ≥ [a even] = chi1(p^a)` if `J(p | n) = −1` (this
includes `p = 2`, `J(2 | n) = −1`). `chi1` is multiplicative (`ζ * χ`).
-/

@[expose] public section

namespace ThreeSquares.B3

open Finset

/-- `(1 * χ)(m) = ∑_{e ∣ m} J(e | n)`. -/
def chi1 (n m : ℕ) : ℤ := ∑ e ∈ m.divisors, jacobiSym e n

/-- `[k odd] · sig n k`. -/
noncomputable def sigp (n k : ℕ) : ℕ := if Odd k then sig n k else 0

/-- `∑_{g² ∣ m} sigp n (m / g²)`. -/
noncomputable def Tsum (n m : ℕ) : ℕ := ∑ g ∈ sqDiv m, sigp n (m / g ^ 2)

theorem Tsum_le_Rcount {n : ℕ} (hn : n % 8 = 3) (m : ℕ) : Tsum n m ≤ Rcount n m := by
  refine sum_le_sum fun g _ => ?_
  unfold sigp
  split_ifs with h
  · exact sig_le_rootCount hn h
  · exact Nat.zero_le _

theorem sigp_mul (n : ℕ) {a b : ℕ} (h : a.Coprime b) : sigp n (a * b) = sigp n a * sigp n b := by
  unfold sigp
  rw [sig_mul n h]
  by_cases ha : Odd a <;> by_cases hb : Odd b <;> simp [ha, hb, Nat.odd_mul]

theorem mem_sqDiv {m g : ℕ} (hm : 0 < m) : g ∈ sqDiv m ↔ 1 ≤ g ∧ g ^ 2 ∣ m := by
  unfold sqDiv
  rw [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, ?_⟩, h2⟩
    have := Nat.le_of_dvd hm h2
    nlinarith

theorem Tsum_one (n : ℕ) : Tsum n 1 = 1 := by
  have : sqDiv 1 = {1} := by decide
  simp [Tsum, this, sigp, sig_one]

theorem Tsum_mul_ge (n : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a.Coprime b) :
    Tsum n a * Tsum n b ≤ Tsum n (a * b) := by
  classical
  unfold Tsum
  rw [sum_mul_sum, ← sum_product']
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) ↑(sqDiv a ×ˢ sqDiv b) := by
    rintro ⟨g₁, g₂⟩ h₁ ⟨g₁', g₂'⟩ h₂ heq
    simp only [coe_product, Set.mem_prod, mem_coe, mem_sqDiv ha, mem_sqDiv hb] at h₁ h₂
    simp only at heq
    have d1 : g₁ ∣ a := dvd_trans (dvd_pow_self g₁ two_ne_zero) h₁.1.2
    have d1' : g₁' ∣ a := dvd_trans (dvd_pow_self g₁' two_ne_zero) h₂.1.2
    have d2 : g₂ ∣ b := dvd_trans (dvd_pow_self g₂ two_ne_zero) h₁.2.2
    have d2' : g₂' ∣ b := dvd_trans (dvd_pow_self g₂' two_ne_zero) h₂.2.2
    have c1 : (g₁ * g₂).gcd a = g₁ :=
      (Nat.Coprime.gcd_mul_right_cancel g₁ ((Nat.Coprime.coprime_dvd_left d2 h.symm))).trans
        (Nat.gcd_eq_left d1)
    have c1' : (g₁' * g₂').gcd a = g₁' :=
      (Nat.Coprime.gcd_mul_right_cancel g₁' ((Nat.Coprime.coprime_dvd_left d2' h.symm))).trans
        (Nat.gcd_eq_left d1')
    have e1 : g₁ = g₁' := by rw [← c1, ← c1', heq]
    subst e1
    have e2 : g₂ = g₂' := Nat.eq_of_mul_eq_mul_left (by omega) heq
    rw [e2]
  calc ∑ p ∈ sqDiv a ×ˢ sqDiv b, sigp n (a / p.1 ^ 2) * sigp n (b / p.2 ^ 2)
      = ∑ p ∈ sqDiv a ×ˢ sqDiv b, sigp n (a * b / (p.1 * p.2) ^ 2) := by
        refine sum_congr rfl fun p hp => ?_
        simp only [mem_product, mem_sqDiv ha, mem_sqDiv hb] at hp
        have hc : (a / p.1 ^ 2).Coprime (b / p.2 ^ 2) :=
          Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hp.1.2)
            (Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hp.2.2) h)
        rw [← sigp_mul n hc, mul_pow, Nat.div_mul_div_comm hp.1.2 hp.2.2]
    _ = ∑ g ∈ (sqDiv a ×ˢ sqDiv b).image (fun p : ℕ × ℕ => p.1 * p.2),
          sigp n (a * b / g ^ 2) :=
        (sum_image (f := fun g => sigp n (a * b / g ^ 2)) hinj).symm
    _ ≤ ∑ g ∈ sqDiv (a * b), sigp n (a * b / g ^ 2) := by
        refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
        intro g hg
        obtain ⟨p, hp, rfl⟩ := mem_image.mp hg
        simp only [mem_product, mem_sqDiv ha, mem_sqDiv hb] at hp
        rw [mem_sqDiv hab, mul_pow]
        exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
          Nat.mul_dvd_mul hp.1.2 hp.2.2⟩

theorem Tsum_step (n : ℕ) {p k : ℕ} (hp : 2 ≤ p) (hk : 0 < k) :
    sigp n (p ^ 2 * k) + Tsum n k ≤ Tsum n (p ^ 2 * k) := by
  classical
  have hpk : 0 < p ^ 2 * k := by positivity
  unfold Tsum
  have hsub : insert 1 ((sqDiv k).image (p * ·)) ⊆ sqDiv (p ^ 2 * k) := by
    intro g hg
    rw [mem_insert, mem_image] at hg
    rw [mem_sqDiv hpk]
    rcases hg with rfl | ⟨g', hg', rfl⟩
    · exact ⟨le_rfl, by simp⟩
    · rw [mem_sqDiv hk] at hg'
      refine ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
      rw [mul_pow]
      exact Nat.mul_dvd_mul_left _ hg'.2
  have hnot : (1 : ℕ) ∉ (sqDiv k).image (p * ·) := by
    rw [mem_image]
    rintro ⟨g', hg', h⟩
    rw [mem_sqDiv hk] at hg'
    nlinarith
  have hinj : Set.InjOn (p * ·) ↑(sqDiv k) := fun x _ y _ h =>
    Nat.eq_of_mul_eq_mul_left (by omega) h
  calc sigp n (p ^ 2 * k) + ∑ g ∈ sqDiv k, sigp n (k / g ^ 2)
      = ∑ g ∈ insert 1 ((sqDiv k).image (p * ·)), sigp n (p ^ 2 * k / g ^ 2) := by
        rw [sum_insert hnot, sum_image hinj]
        congr 1
        · simp
        · refine sum_congr rfl fun g _ => ?_
          rw [mul_pow, Nat.mul_div_mul_left _ _ (by positivity)]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

theorem sigp_le_Tsum (n : ℕ) {m : ℕ} (hm : 0 < m) : sigp n m ≤ Tsum n m := by
  unfold Tsum
  have h1 : 1 ∈ sqDiv m := (mem_sqDiv hm).mpr ⟨le_rfl, by simp⟩
  have := single_le_sum (f := fun g => sigp n (m / g ^ 2)) (fun _ _ => Nat.zero_le _) h1
  simpa using this

/-- The Jacobi character as an arithmetic function. -/
def chiA (n : ℕ) : ArithmeticFunction ℤ := ⟨fun e => if e = 0 then 0 else jacobiSym e n, rfl⟩

theorem chiA_mult (n : ℕ) : (chiA n).IsMultiplicative := by
  refine ⟨by simp [chiA], fun {a b} _ => ?_⟩
  simp only [chiA, ArithmeticFunction.coe_mk]
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [if_neg (Nat.mul_ne_zero ha hb), if_neg ha, if_neg hb, Nat.cast_mul, jacobiSym.mul_left]

theorem chi1_eq (n m : ℕ) : chi1 n m = ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) *
    chiA n) m := by
  rw [ArithmeticFunction.coe_zeta_mul_apply, chi1]
  refine sum_congr rfl fun e he => ?_
  simp [chiA, Nat.ne_of_gt (Nat.pos_of_mem_divisors he)]

theorem chi1_mul (n : ℕ) {a b : ℕ} (h : a.Coprime b) : chi1 n (a * b) = chi1 n a * chi1 n b := by
  rw [chi1_eq, chi1_eq, chi1_eq]
  exact (ArithmeticFunction.isMultiplicative_zeta.natCast.mul (chiA_mult n)).map_mul_of_coprime h

theorem chi1_prime_pow (n : ℕ) {p : ℕ} (hp : p.Prime) (a : ℕ) :
    chi1 n (p ^ a) = ∑ i ∈ range (a + 1), jacobiSym p n ^ i := by
  rw [chi1, Nat.divisors_prime_pow hp, sum_map]
  refine sum_congr rfl fun i _ => ?_
  simp [jacobiSym.pow_left]

theorem jacobi_neg_of_chi_one {n p : ℕ} (hn : n % 4 = 3) (hp : p.Prime) (hp2 : p ≠ 2)
    (h : jacobiSym p n = 1) : jacobiSym (-(n : ℤ)) p = 1 := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hno : Odd n := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hpo]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpo) with h4 | h4
  · rw [ZMod.χ₄_nat_one_mod_four h4, jacobiSym.quadratic_reciprocity_one_mod_four' hno h4, h]
    rfl
  · rw [ZMod.χ₄_nat_three_mod_four h4, jacobiSym.quadratic_reciprocity_three_mod_four hn h4, h]
    rfl

theorem chi_two {n : ℕ} (hn : n % 8 = 3) : jacobiSym 2 n = -1 := by
  have hno : Odd n := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.at_two hno, ZMod.χ₈_nat_eq_if_mod_eight]
  simp [hn, show n % 2 = 1 by omega]

/-- The prime power case. -/
theorem chi1_le_Tsum_pp {n : ℕ} (hn : n % 8 = 3) {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (a : ℕ) : chi1 n (p ^ a) ≤ Tsum n (p ^ a) ∧ 0 ≤ chi1 n (p ^ a) := by
  have hgcd : (p : ℤ).gcd n = 1 := by
    have : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
    simpa [Int.gcd] using this
  have hpp : 2 ≤ p := hp.two_le
  rcases jacobiSym.eq_one_or_neg_one hgcd with hχ | hχ
  · -- `χ(p) = 1`: `p` is odd and `sigp (p^(k+1)) ≥ 2`
    have hp2 : p ≠ 2 := by
      rintro rfl
      simp only [Nat.cast_ofNat] at hχ
      rw [chi_two hn] at hχ
      norm_num at hχ
    have hJ := jacobi_neg_of_chi_one (by omega) hp hp2 hχ
    have hsig : ∀ j, 2 ≤ sigp n (p ^ (j + 1)) := by
      intro j
      unfold sigp
      rw [if_pos ((hp.odd_of_ne_two hp2).pow)]
      exact two_le_sig hp hp2 hpn hJ j
    have key : ∀ a : ℕ, ((a : ℤ) + 1) ≤ Tsum n (p ^ a) := by
      intro a
      induction a using Nat.strong_induction_on with
      | _ a ih =>
        match a, ih with
        | 0, _ => simp [Tsum_one]
        | 1, _ =>
          have := le_trans (hsig 0) (sigp_le_Tsum n (by positivity : 0 < p ^ 1))
          simp only [zero_add] at this
          push_cast
          omega
        | a + 2, ih =>
          have h1 := ih a (by omega)
          have h2 := Tsum_step n (k := p ^ a) hpp (by positivity)
          rw [← pow_add, add_comm 2 a] at h2
          have h3 := hsig (a + 1)
          rw [show a + 1 + 1 = a + 2 by ring] at h3
          push_cast at h1 ⊢
          omega
    rw [chi1_prime_pow n hp, hχ]
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    push_cast
    exact ⟨key a, by positivity⟩
  · -- `χ(p) = −1`
    have key : ∀ a : ℕ, (∑ i ∈ range (a + 1), (-1 : ℤ) ^ i) ≤ Tsum n (p ^ a) ∧
        0 ≤ ∑ i ∈ range (a + 1), (-1 : ℤ) ^ i := by
      intro a
      induction a using Nat.strong_induction_on with
      | _ a ih =>
        match a, ih with
        | 0, _ => simp [Tsum_one]
        | 1, _ => simp [sum_range_succ]
        | a + 2, ih =>
          obtain ⟨h1, h1'⟩ := ih a (by omega)
          have h2 := Tsum_step n (k := p ^ a) hpp (by positivity)
          rw [← pow_add, add_comm 2 a] at h2
          have e : ∑ i ∈ range (a + 2 + 1), (-1 : ℤ) ^ i = ∑ i ∈ range (a + 1), (-1 : ℤ) ^ i := by
            rw [sum_range_succ, sum_range_succ, pow_succ, pow_succ]
            ring
          rw [e]
          refine ⟨le_trans h1 ?_, h1'⟩
          exact_mod_cast le_trans (Nat.le_add_left _ _) h2
    rw [chi1_prime_pow n hp, hχ]
    exact key a

/-- **`Tsum ≥ chi1 ≥ 0`** for `m` coprime to `n`. -/
theorem chi1_le_Tsum {n : ℕ} (hn : n % 8 = 3) :
    ∀ m : ℕ, m.Coprime n → chi1 n m ≤ Tsum n m ∧ 0 ≤ chi1 n m := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hc
    have hpn : ¬ p ∣ n := by
      intro h
      have := Nat.Coprime.coprime_dvd_left (dvd_pow_self p hk.ne') hc
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this h)
    exact chi1_le_Tsum_pp hn hp hpn k
  | zero => intro _; simp [chi1, Tsum, sqDiv]
  | one => intro _; simp [chi1, Tsum_one]
  | coprime a b ha hb hab iha ihb =>
    intro hc
    obtain ⟨h1, h1'⟩ := iha (Nat.Coprime.coprime_mul_right hc)
    obtain ⟨h2, h2'⟩ := ihb (Nat.Coprime.coprime_mul_left hc)
    rw [chi1_mul n hab]
    refine ⟨?_, mul_nonneg h1' h2'⟩
    calc chi1 n a * chi1 n b ≤ (Tsum n a : ℤ) * Tsum n b :=
          mul_le_mul h1 h2 h2' (le_trans h1' h1)
      _ ≤ Tsum n (a * b) := by exact_mod_cast Tsum_mul_ge n (by omega) (by omega) hab

theorem chi1_le_Rcount {n : ℕ} (hn : n % 8 = 3) {m : ℕ} (hm : m.Coprime n) :
    chi1 n m ≤ Rcount n m :=
  le_trans (chi1_le_Tsum hn m hm).1 (by exact_mod_cast Tsum_le_Rcount hn m)

theorem chi1_nonneg {n : ℕ} (hn : n % 8 = 3) {m : ℕ} (hm : m.Coprime n) : 0 ≤ chi1 n m :=
  (chi1_le_Tsum hn m hm).2

end ThreeSquares.B3
