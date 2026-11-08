/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.B3_LocalMult
public import ThreeSquaresLib.JacobiGauss
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# The Jacobi character and partial sums of Dirichlet characters

* `chiN n`: `x ↦ J(x | n)` as a Dirichlet character mod `n`; for `n ≡ 3 (mod 8)`:
  `chiN_ne_one`, `chiN_sq` (real), `chiN_neg_half_sq` (`χ(−z²/2) = 1` for units `z`).
* `psum f x = ∑_{0 < k ≤ x} f k`; `norm_psum_sub_le`: for `f` periodic mod `n`, `|f| ≤ 1`,
  `‖psum f x − (x/n) psum f n‖ ≤ 2n`.
* `psum_char`: `psum ψ n = φ(n)` for `ψ = 1` and `0` otherwise.
-/

@[expose] public section

namespace ThreeSquares.B3

open Finset

/-- The Jacobi character `J(· | n)` mod `n`. -/
noncomputable def chiN (n : ℕ) [NeZero n] : DirichletCharacter ℂ n where
  toFun := jac n
  map_one' := by
    have := jac_intCast n 1
    simpa using this
  map_mul' := jac_mul n
  map_nonunit' := by
    intro x hx
    unfold jac
    have : ¬ (x.val).Coprime n := by
      rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
      exact hx
    have h0 : jacobiSym (x.val : ℤ) n = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      exact this
    rw [h0, Int.cast_zero]

theorem chiN_int (n : ℕ) [NeZero n] (a : ℤ) : chiN n a = (jacobiSym a n : ℂ) := jac_intCast n a

theorem chiN_nat (n : ℕ) [NeZero n] (m : ℕ) : chiN n m = (jacobiSym m n : ℂ) := by
  have := chiN_int n m
  simpa using this

theorem chiN_neg_one {n : ℕ} [NeZero n] (hn : n % 4 = 3) : chiN n (-1) = -1 := by
  have := chiN_int n (-1)
  push_cast at this
  rw [this, jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)), ZMod.χ₄_nat_three_mod_four hn]
  simp

theorem chiN_two {n : ℕ} [NeZero n] (hn : n % 8 = 3) : chiN n 2 = -1 := by
  have := chiN_int n 2
  push_cast at this
  rw [this, chi_two hn]
  simp

theorem chiN_ne_one {n : ℕ} [NeZero n] (hn : n % 4 = 3) : chiN n ≠ 1 := by
  intro h
  have h1 := chiN_neg_one (n := n) hn
  rw [h, MulChar.one_apply (isUnit_one.neg)] at h1
  norm_num at h1

theorem chiN_sq_unit (n : ℕ) [NeZero n] {z : ZMod n} (hz : IsUnit z) : chiN n z ^ 2 = 1 := by
  change jac n z ^ 2 = 1
  unfold jac
  apply jacobiSym_sq_eq_one
  have : (z.val).Coprime n := by
    rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
    exact hz
  rw [Int.gcd_natCast_natCast]
  exact this

theorem chiN_sq (n : ℕ) [NeZero n] : chiN n ^ 2 = 1 := by
  refine MulChar.ext fun a => ?_
  rw [MulChar.pow_apply' _ two_ne_zero, MulChar.one_apply_coe]
  exact chiN_sq_unit n a.isUnit

theorem isUnit_two {n : ℕ} (hn : Odd n) : IsUnit (2 : ZMod n) := by
  have := (ZMod.isUnit_iff_coprime 2 n).mpr (Nat.coprime_two_left.mpr hn)
  simpa using this

theorem chiN_neg_half_sq {n : ℕ} [NeZero n] (hn : n % 8 = 3) {z : ZMod n} (hz : IsUnit z) :
    chiN n (-z ^ 2 * 2⁻¹) = 1 := by
  have h2 : IsUnit (2 : ZMod n) := isUnit_two (Nat.odd_iff.mpr (by omega))
  have hinv : chiN n 2 * chiN n (2⁻¹) = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit _ h2, map_one]
  rw [chiN_two hn] at hinv
  have hinv' : chiN n (2⁻¹) = -1 := by linear_combination -hinv
  rw [neg_eq_neg_one_mul, map_mul, map_mul, map_pow, chiN_neg_one (by omega), hinv',
    chiN_sq_unit n hz]
  ring

/-- `∑_{0 < k ≤ x} f k`. -/
def psum (f : ℕ → ℂ) (x : ℕ) : ℂ := ∑ k ∈ Ioc 0 x, f k

theorem norm_psum_le {f : ℕ → ℂ} (hf : ∀ k, ‖f k‖ ≤ 1) (x : ℕ) : ‖psum f x‖ ≤ x := by
  unfold psum
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (sum_le_sum fun k _ => hf k) ?_
  simp

theorem block_sum {f : ℕ → ℂ} {n : ℕ} (hper : ∀ k, f (k + n) = f k) (a : ℕ) :
    ∑ k ∈ Ioc a (a + n), f k = psum f n := by
  induction a with
  | zero => simp [psum]
  | succ a ih =>
    rw [← ih]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have e1 : ∑ k ∈ Ioc a (a + n), f k = f (a + 1) + ∑ k ∈ Ioc (a + 1) (a + n), f k := by
      rw [← sum_Ioc_consecutive _ (Nat.le_succ a) (by omega)]
      congr 1
      rw [show a + 1 = a.succ from rfl, Nat.Ioc_succ_singleton, sum_singleton]
    have e2 : ∑ k ∈ Ioc (a + 1) (a + 1 + n), f k =
        ∑ k ∈ Ioc (a + 1) (a + n), f k + f (a + n + 1) := by
      rw [show a + 1 + n = (a + n) + 1 by ring, sum_Ioc_succ_top (by omega)]
    rw [e1, e2, show a + n + 1 = (a + 1) + n by ring, hper]
    ring

theorem psum_mul_add {f : ℕ → ℂ} {n : ℕ} (hper : ∀ k, f (k + n) = f k) (q r : ℕ) :
    psum f (n * q + r) = q * psum f n + psum f r := by
  induction q with
  | zero => simp
  | succ q ih =>
    have e : psum f (n * (q + 1) + r) = psum f (n * q + r) +
        ∑ k ∈ Ioc (n * q + r) (n * q + r + n), f k := by
      unfold psum
      rw [show n * (q + 1) + r = n * q + r + n by ring]
      exact (sum_Ioc_consecutive _ (Nat.zero_le _) (by omega)).symm
    rw [e, ih, block_sum hper]
    push_cast
    ring

theorem norm_psum_sub_le {f : ℕ → ℂ} {n : ℕ} (hn : 0 < n) (hper : ∀ k, f (k + n) = f k)
    (hf : ∀ k, ‖f k‖ ≤ 1) (x : ℕ) :
    ‖psum f x - (x / n : ℂ) * psum f n‖ ≤ 2 * n := by
  have hx : x = n * (x / n) + x % n := (Nat.div_add_mod x n).symm
  have hr : x % n < n := Nat.mod_lt x hn
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have e : psum f x - (x / n : ℂ) * psum f n = psum f (x % n) - ((x % n : ℕ) / n : ℂ) * psum f n := by
    conv_lhs => rw [hx, psum_mul_add hper]
    push_cast
    field_simp
    ring
  rw [e]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 := norm_psum_le hf (x % n)
  have h2 := norm_psum_le hf n
  have h3 : ‖((x % n : ℕ) / n : ℂ) * psum f n‖ ≤ ((x % n : ℕ) : ℝ) := by
    rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    calc ((x % n : ℕ) : ℝ) / n * ‖psum f n‖ ≤ ((x % n : ℕ) : ℝ) / n * n := by gcongr
      _ = ((x % n : ℕ) : ℝ) := by field_simp
  have : ((x % n : ℕ) : ℝ) ≤ n := by exact_mod_cast hr.le
  linarith

/-- A Dirichlet character as a function on `ℕ`. -/
noncomputable def chf {n : ℕ} (ψ : DirichletCharacter ℂ n) (k : ℕ) : ℂ := ψ k

theorem chf_per {n : ℕ} (ψ : DirichletCharacter ℂ n) (k : ℕ) : chf ψ (k + n) = chf ψ k := by
  simp [chf]

theorem chf_norm {n : ℕ} (ψ : DirichletCharacter ℂ n) (k : ℕ) : ‖chf ψ k‖ ≤ 1 :=
  DirichletCharacter.norm_le_one ψ _

theorem psum_eq_sum_zmod {n : ℕ} [NeZero n] (ψ : DirichletCharacter ℂ n) :
    psum (chf ψ) n = ∑ a : ZMod n, ψ a := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  unfold psum chf
  refine sum_nbij (fun k : ℕ => (k : ZMod n)) (fun _ _ => mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro k hk k' hk' h
    simp only [coe_Ioc, Set.mem_Ioc] at hk hk'
    have := (ZMod.natCast_eq_natCast_iff' k k' n).mp h
    rcases lt_or_eq_of_le hk.2 with h1 | h1 <;> rcases lt_or_eq_of_le hk'.2 with h2 | h2
    · rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
    · rw [Nat.mod_eq_of_lt h1, h2, Nat.mod_self] at this; omega
    · rw [Nat.mod_eq_of_lt h2, h1, Nat.mod_self] at this; omega
    · omega
  · intro a _
    by_cases ha : a.val = 0
    · refine ⟨n, by simp [hn], ?_⟩
      simp only [ZMod.natCast_self]
      exact ((ZMod.val_eq_zero a).mp ha).symm
    · refine ⟨a.val, ?_, ZMod.natCast_zmod_val a⟩
      simp only [coe_Ioc, Set.mem_Ioc]
      exact ⟨Nat.pos_of_ne_zero ha, (ZMod.val_lt a).le⟩

theorem psum_char {n : ℕ} [NeZero n] (ψ : DirichletCharacter ℂ n) :
    psum (chf ψ) n = if ψ = 1 then (n.totient : ℂ) else 0 := by
  classical
  rw [psum_eq_sum_zmod]
  split_ifs with h
  · subst h
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  · exact MulChar.sum_eq_zero_of_ne_one h

end ThreeSquares.B3
