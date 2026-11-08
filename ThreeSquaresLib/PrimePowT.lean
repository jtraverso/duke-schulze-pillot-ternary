/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.PrimePowSalie
public import ThreeSquaresLib.SqfT

/-!
# `T_q` for all odd `q` coprime to `N`

* `gauss_even`, `gauss_odd`: `G(A; p^{2β}) = p^β`, `G(A; p^{2β+1}) = p^β χ(A) g` (`p ∤ 2A`);
* `Tq_prime_pow`: `T_{p^α}(U, N) = J(−N | p)^α p^α (e(2UN/p^α) + e(−2UN/p^α))`;
* `Tq_coprime`: `T_q(U, N) = J(−N | q) q ∑_{y² ≡ 4N²} e_q(U y)` for odd `q` with `(N, q) = (U, q) = 1`.
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset

theorem gaussQ_congr {q q' : ℕ} [NeZero q] [NeZero q'] (h : q = q') (A : ℤ) :
    gaussQ ((A : ℤ) : ZMod q) 0 = gaussQ ((A : ℤ) : ZMod q') 0 := by
  subst h; rfl

theorem gaussQ_one_mod (A : ℤ) : gaussQ ((A : ℤ) : ZMod 1) 0 = 1 := by
  have hz : ∀ z : ZMod 1, z = 0 := fun z => Subsingleton.elim _ _
  unfold gaussQ; simp [hz]

theorem gaussQ_prime_mod {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {q : ℕ} [NeZero q] (hq : q = p)
    (A : ℤ) (hA : ¬ (p : ℤ) ∣ A) :
    gaussQ ((A : ℤ) : ZMod q) 0 = PT.chi p (A : ZMod p) * PT.gs p := by
  subst hq
  have hA' : (A : ZMod q) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hA
  rw [← PT.sum_psi_sq hp2 hA']
  unfold gaussQ
  simp

theorem gauss_even {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (A : ℤ) (hA : ¬ (p : ℤ) ∣ A) :
    ∀ β : ℕ, haveI : NeZero (p ^ (2 * β)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
      gaussQ ((A : ℤ) : ZMod (p ^ (2 * β))) 0 = (p : ℂ) ^ β
  | 0 => by simp only [mul_zero, pow_zero]; exact gaussQ_one_mod A
  | β + 1 => by
    haveI : NeZero (p ^ (2 * β)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    haveI : NeZero (p ^ (2 * β + 2)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    haveI : NeZero (p ^ (2 * (β + 1))) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    rw [gaussQ_congr (show p ^ (2 * (β + 1)) = p ^ (2 * β + 2) by ring) A,
      gaussQ_pow_add_two hp.out hp2 A hA (2 * β), gauss_even hp2 A hA β, pow_succ]
    ring

theorem gauss_odd {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (A : ℤ) (hA : ¬ (p : ℤ) ∣ A) :
    ∀ β : ℕ, haveI : NeZero (p ^ (2 * β + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
      gaussQ ((A : ℤ) : ZMod (p ^ (2 * β + 1))) 0 = (p : ℂ) ^ β * PT.chi p (A : ZMod p) * PT.gs p
  | 0 => by
    haveI : NeZero (p ^ (2 * 0 + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    rw [gaussQ_prime_mod hp2 (by ring) A hA]; ring
  | β + 1 => by
    haveI : NeZero (p ^ (2 * β + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    haveI : NeZero (p ^ (2 * β + 1 + 2)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    haveI : NeZero (p ^ (2 * (β + 1) + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    rw [gaussQ_congr (show p ^ (2 * (β + 1) + 1) = p ^ (2 * β + 1 + 2) by ring) A,
      gaussQ_pow_add_two hp.out hp2 A hA (2 * β + 1), gauss_odd hp2 A hA β, pow_succ]
    ring

/-- `G(a; q)` for a unit `a`, via an integer lift. -/
theorem gaussQ_eq_lift {q : ℕ} [NeZero q] (a : ZMod q) :
    gaussQ a 0 = gaussQ (((a.val : ℕ) : ℤ) : ZMod q) 0 := by
  congr 1; push_cast; rw [ZMod.natCast_zmod_val]

theorem not_dvd_val_of_unit {p q : ℕ} [NeZero q] (hp : p.Prime) (hpq : p ∣ q) {a : ZMod q}
    (ha : IsUnit a) : ¬ (p : ℤ) ∣ (((a.val : ℕ) : ℤ)) := by
  intro h
  have h1 : p ∣ a.val := by exact_mod_cast h
  have hu := (ZMod.isUnit_iff_coprime a.val q).mp (by rw [ZMod.natCast_zmod_val]; exact ha)
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hu) hpq)

theorem Tq_congr {q q' : ℕ} [NeZero q] [NeZero q'] (h : q = q') (U N : ℤ) :
    Tq q (U : ZMod q) (N : ZMod q) = Tq q' (U : ZMod q') (N : ZMod q') := by
  subst h; rfl

/-- The inner `x`-sum of `T`: `∑_x e(U(d⁻¹(x² + N) + N d)) = e(UN(d + d⁻¹)) G(U d⁻¹)`. -/
theorem Tq_inner {q : ℕ} [NeZero q] (U N : ZMod q) (d : (ZMod q)ˣ) :
    ∑ x : ZMod q, (stdAddChar (U * (((d⁻¹ : (ZMod q)ˣ) : ZMod q) * (x ^ 2 + N) + N * (d : ZMod q))) : ℂ) =
      stdAddChar (U * N * ((d : ZMod q) + ((d⁻¹ : (ZMod q)ˣ) : ZMod q))) *
        gaussQ (U * ((d⁻¹ : (ZMod q)ˣ) : ZMod q)) 0 := by
  unfold gaussQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← AddChar.map_add_eq_mul]; congr 1; ring

theorem chi_cast_unit {p q : ℕ} [Fact p.Prime] [NeZero q] (hpq : p ∣ q) (d : (ZMod q)ˣ) :
    PT.chi p (ZMod.cast ((d⁻¹ : (ZMod q)ˣ) : ZMod q) : ZMod p) = PT.chi p (ZMod.cast (d : ZMod q)) := by
  have h1 : (ZMod.cast ((d⁻¹ : (ZMod q)ˣ) : ZMod q) : ZMod p) * ZMod.cast (d : ZMod q) = 1 := by
    rw [← ZMod.cast_mul hpq, Units.inv_mul, ZMod.cast_one hpq]
  have h2 : (ZMod.cast (d : ZMod q) : ZMod p) ≠ 0 := by
    intro h; rw [h, mul_zero] at h1; exact zero_ne_one h1
  rw [show (ZMod.cast ((d⁻¹ : (ZMod q)ˣ) : ZMod q) : ZMod p) = (ZMod.cast (d : ZMod q))⁻¹ from
    eq_inv_of_mul_eq_one_left h1, PT.chi_inv]

/-- **`T` at odd prime powers.** -/
theorem Tq_prime_pow {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (N U : ℤ) (hN : ¬ (p : ℤ) ∣ N)
    (hU : ¬ (p : ℤ) ∣ U) (α : ℕ) (hα : 1 ≤ α) :
    haveI : NeZero (p ^ α) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
    Tq (p ^ α) (U : ZMod (p ^ α)) (N : ZMod (p ^ α)) = PT.chi p ((-N : ℤ) : ZMod p) ^ α * (p : ℂ) ^ α *
      (stdAddChar ((2 * (U * N) : ℤ) : ZMod (p ^ α)) + stdAddChar ((-2 * (U * N) : ℤ) : ZMod (p ^ α))) := by
  haveI : NeZero (p ^ α) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have hpp := hp.out
  have hpq : p ∣ p ^ α := dvd_pow_self p (by omega)
  have hUN : ¬ (p : ℤ) ∣ U * N := by
    intro h
    rcases (Nat.prime_iff_prime_int.mp hpp).dvd_or_dvd h with h' | h'
    · exact hU h'
    · exact hN h'
  have hNp : (N : ZMod p) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hN
  have hUp : (U : ZMod p) ≠ 0 := by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hU
  have hchiN : PT.chi p ((-N : ℤ) : ZMod p) ^ 2 = 1 := by
    apply PT.chi_sq; push_cast; exact neg_ne_zero.mpr hNp
  -- `U d⁻¹` is a unit, with lift prime to `p`
  have hlift : ∀ d : (ZMod (p ^ α))ˣ, ¬ (p : ℤ) ∣ ((((U : ZMod (p ^ α)) *
      ((d⁻¹ : (ZMod (p ^ α))ˣ) : ZMod (p ^ α))).val : ℕ) : ℤ) := by
    intro d
    apply not_dvd_val_of_unit hpp hpq
    refine IsUnit.mul ?_ (Units.isUnit _)
    have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
    have hc : IsCoprime U ((p ^ α : ℕ) : ℤ) := by
      push_cast; exact IsCoprime.pow_right ((Prime.coprime_iff_not_dvd hp').mpr hU).symm
    obtain ⟨u, v, huv⟩ := hc
    refine IsUnit.of_mul_eq_one (u : ZMod (p ^ α)) ?_
    have := congrArg (Int.cast : ℤ → ZMod (p ^ α)) huv
    push_cast at this
    rw [← Nat.cast_pow, ZMod.natCast_self, mul_zero, add_zero] at this
    linear_combination this
  rcases (show α = 1 ∨ 2 ≤ α by omega) with h1 | h2
  · subst h1
    have key : ∀ (q : ℕ) [NeZero q], q = p → Tq q (U : ZMod q) (N : ZMod q) =
        PT.chi p ((-N : ℤ) : ZMod p) ^ 1 * (p : ℂ) ^ 1 *
          (stdAddChar ((2 * (U * N) : ℤ) : ZMod q) + stdAddChar ((-2 * (U * N) : ℤ) : ZMod q)) := by
      intro q _ hq
      subst hq
      rw [Tq_prime hp2 hUp hNp]
      push_cast
      ring
    exact key (p ^ 1) (pow_one p)
  unfold Tq
  simp_rw [Tq_inner]
  obtain ⟨β, hβ | hβ⟩ := Nat.even_or_odd' α
  · -- even
    subst hβ
    have hβ1 : 1 ≤ β := by omega
    have hG : ∀ d : (ZMod (p ^ (2 * β)))ˣ, gaussQ ((U : ZMod (p ^ (2 * β))) *
        ((d⁻¹ : (ZMod (p ^ (2 * β)))ˣ) : ZMod (p ^ (2 * β)))) 0 = (p : ℂ) ^ β := by
      intro d
      rw [gaussQ_eq_lift, gauss_even hp2 _ (hlift d) β]
    simp_rw [hG]
    rw [← Finset.sum_mul]
    have hK := kloosterman_even hpp hp2 (U * N) hUN hβ1
    push_cast at hK
    rw [hK, show PT.chi p ((-N : ℤ) : ZMod p) ^ (2 * β) = 1 by rw [pow_mul, hchiN, one_pow],
      show (p : ℂ) ^ (2 * β) = (p : ℂ) ^ β * (p : ℂ) ^ β by ring]
    push_cast
    ring
  · subst hβ
    have hβ1 : 1 ≤ β := by omega
    set q := p ^ (2 * β + 1)
    have hG : ∀ d : (ZMod q)ˣ, gaussQ ((U : ZMod q) * ((d⁻¹ : (ZMod q)ˣ) : ZMod q)) 0 =
        (p : ℂ) ^ β * (PT.chi p (U : ZMod p) * chiq p (2 * β + 1) d) * PT.gs p := by
      intro d
      rw [gaussQ_eq_lift, gauss_odd hp2 _ (hlift d) β]
      congr 2
      unfold chiq
      rw [show ((((((U : ZMod q) * ((d⁻¹ : (ZMod q)ˣ) : ZMod q)).val : ℕ) : ℤ)) : ZMod p) =
          ZMod.cast ((U : ZMod q) * ((d⁻¹ : (ZMod q)ˣ) : ZMod q)) by
        rw [ZMod.cast_eq_val]; push_cast; rfl,
        ZMod.cast_mul hpq, ZMod.cast_intCast hpq, map_mul, chi_cast_unit hpq]
    simp_rw [hG]
    have hS := salie_odd hp2 (U * N) hUN hβ1
    rw [show (∑ d : (ZMod q)ˣ, stdAddChar ((U : ZMod q) * (N : ZMod q) * ((d : ZMod q) +
        ((d⁻¹ : (ZMod q)ˣ) : ZMod q))) * ((p : ℂ) ^ β * (PT.chi p (U : ZMod p) *
          chiq p (2 * β + 1) d) * PT.gs p)) = (p : ℂ) ^ β * PT.chi p (U : ZMod p) * PT.gs p *
        ∑ d : (ZMod q)ˣ, chiq p (2 * β + 1) d * stdAddChar (((U * N : ℤ) : ZMod q) * ((d : ZMod q) +
          ((d⁻¹ : (ZMod q)ˣ) : ZMod q))) by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => ?_; push_cast; ring]
    rw [hS]
    have hgs := PT.gs_sq (p := p) hp2
    have hU2 := PT.chi_sq hUp
    have hpow : PT.chi p ((-N : ℤ) : ZMod p) ^ (2 * β + 1) = PT.chi p ((-N : ℤ) : ZMod p) := by
      rw [pow_succ, pow_mul, hchiN, one_pow, one_mul]
    rw [hpow, show PT.chi p ((-N : ℤ) : ZMod p) = PT.chi p (-1) * PT.chi p (N : ZMod p) by
      rw [← map_mul]; push_cast; ring_nf,
      show PT.chi p (((U * N : ℤ)) : ZMod p) = PT.chi p (U : ZMod p) * PT.chi p (N : ZMod p) by
      rw [← map_mul]; push_cast; ring_nf]
    push_cast
    linear_combination (p : ℂ) ^ (2 * β) * PT.chi p (N : ZMod p) *
      (stdAddChar (2 * ((U : ZMod q) * (N : ZMod q))) + stdAddChar (-2 * ((U : ZMod q) * (N : ZMod q)))) *
      (PT.chi p (U : ZMod p) ^ 2 * hgs + PT.chi p (-1) * p * hU2)

end ThreeSquares
