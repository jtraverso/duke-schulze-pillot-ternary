/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# The sum `T_p` at an odd prime

For an odd prime `p`, `ψ = e(·/p)`, `χ` the quadratic character, `g` its Gauss sum:
* `sum_psi_sq`: `∑_x ψ(a x²) = χ(a) g` (`a ≠ 0`);
* `williams`: `∑_{d ≠ 0, d + d⁻¹ = y} χ(d) = χ(y − 2) + χ(y + 2)`;
* `salie_prime`: `∑_d χ(d) ψ(m(d + d⁻¹)) = χ(m) g (ψ(2m) + ψ(−2m))` (`m ≠ 0`);
* `T_prime`: `∑_{d ∈ 𝔽_p^×} ∑_x ψ(u(d⁻¹(x² + n) + nd)) = χ(−n) p (ψ(2un) + ψ(−2un))` (`u, n ≠ 0`).
-/

@[expose] public section

namespace ThreeSquares.PT

open Finset

variable (p : ℕ) [hp : Fact p.Prime]

/-- The quadratic character of `𝔽_p` with complex values. -/
noncomputable def chi : MulChar (ZMod p) ℂ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

/-- The standard additive character `e(·/p)`. -/
noncomputable abbrev psi : AddChar (ZMod p) ℂ := ZMod.stdAddChar

/-- The quadratic Gauss sum. -/
noncomputable def gs : ℂ := gaussSum (chi p) (psi p)

variable {p}

theorem chi_apply (a : ZMod p) : chi p a = ((quadraticChar (ZMod p) a : ℤ) : ℂ) := rfl

theorem ringChar_ne_two (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hp2

theorem two_ne_zero' (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)

theorem chi_sq {a : ZMod p} (ha : a ≠ 0) : chi p a ^ 2 = 1 := by
  rw [chi_apply]; exact_mod_cast quadraticChar_sq_one ha

theorem chi_zero : chi p 0 = 0 := by rw [chi_apply]; simp

theorem chi_isQuadratic : (chi p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp _

theorem chi_inv (a : ZMod p) : chi p a⁻¹ = chi p a := by
  by_cases ha : a = 0
  · simp [ha]
  · have h1 : chi p a * chi p a⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ ha, map_one]
    have h2 := chi_sq ha
    linear_combination chi p a * h1 - chi p a⁻¹ * h2

theorem chi_ne_one (hp2 : p ≠ 2) : chi p ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (ringChar_ne_two hp2)
  have := congrArg (fun χ : MulChar (ZMod p) ℂ => χ a) h
  simp only [chi_apply, ha] at this
  have ha0 : a ≠ 0 := by intro h0; rw [h0] at ha; simp at ha
  rw [MulChar.one_apply (IsUnit.mk0 a ha0)] at this
  norm_num at this

theorem gs_sq (hp2 : p ≠ 2) : gs p ^ 2 = chi p (-1) * p := by
  have h := gaussSum_sq (χ := chi p) (ψ := psi p) (chi_ne_one hp2) chi_isQuadratic
    (ZMod.isPrimitive_stdAddChar p)
  rw [ZMod.card] at h
  exact h

theorem sum_psi_mul {b : ZMod p} (hb : b ≠ 0) : ∑ x : ZMod p, psi p (x * b) = 0 := by
  have := AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar p)
  simpa [hb] using this

theorem sum_chi_psi {m : ZMod p} (hm : m ≠ 0) :
    ∑ y : ZMod p, chi p y * psi p (m * y) = chi p m * gs p := by
  have hu := gaussSum_mulShift_eq (chi p) (psi p) (Units.mk0 m hm)
  rw [chi_isQuadratic.inv, Units.val_mk0] at hu
  unfold gs
  rw [← hu]
  rfl

/-- **`∑_x ψ(a x²) = χ(a) g`.** -/
theorem sum_psi_sq (hp2 : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    ∑ x : ZMod p, psi p (a * x ^ 2) = chi p a * gs p := by
  classical
  have hfib : ∑ x : ZMod p, psi p (a * x ^ 2) =
      ∑ y : ZMod p, ((#{x : ZMod p | x ^ 2 = y}.toFinset : ℕ) : ℂ) * psi p (a * y) := by
    rw [← Finset.sum_fiberwise (s := univ) (g := fun x : ZMod p => x ^ 2)
      (f := fun x => psi p (a * x ^ 2))]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const,
      nsmul_eq_mul, Set.toFinset_ofPred]
  rw [hfib]
  have hc : ∀ y : ZMod p, ((#{x : ZMod p | x ^ 2 = y}.toFinset : ℕ) : ℂ) = chi p y + 1 := by
    intro y
    have := quadraticChar_card_sqrts (ringChar_ne_two hp2) y
    rw [chi_apply]
    exact_mod_cast this
  simp_rw [hc, add_mul, one_mul, Finset.sum_add_distrib]
  rw [show ∑ y : ZMod p, psi p (a * y) = 0 by
    rw [← sum_psi_mul ha]; exact Finset.sum_congr rfl fun y _ => by rw [mul_comm]]
  rw [add_zero, sum_chi_psi ha]

/-- **Williams' identity.** -/
theorem williams (hp2 : p ≠ 2) (y : ZMod p) :
    ∑ d ∈ univ.filter (fun d : ZMod p => d ≠ 0 ∧ d + d⁻¹ = y), chi p d =
      chi p (y - 2) + chi p (y + 2) := by
  classical
  have h2 := two_ne_zero' hp2
  by_cases hy : y + 2 = 0
  · -- `y = −2`: the only `d` is `−1`
    have hy' : y = -2 := by linear_combination hy
    have hset : univ.filter (fun d : ZMod p => d ≠ 0 ∧ d + d⁻¹ = y) = {-1} := by
      ext d
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · rintro ⟨hd0, hd⟩
        have e : d * (d + d⁻¹) = d ^ 2 + 1 := by field_simp
        rw [hd, hy'] at e
        have : (d + 1) ^ 2 = 0 := by linear_combination -e
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
        linear_combination this
      · rintro rfl
        refine ⟨neg_ne_zero.mpr one_ne_zero, ?_⟩
        rw [hy', inv_neg, inv_one]; ring
    rw [hset, sum_singleton, show y - 2 = -1 * 2 ^ 2 by linear_combination hy, hy, chi_zero, add_zero,
      map_mul, map_pow, chi_sq h2, mul_one]
  · -- generic `y`
    set S := univ.filter (fun d : ZMod p => d ≠ 0 ∧ d + d⁻¹ = y)
    have hval : ∀ d ∈ S, chi p d = chi p (y + 2) := by
      intro d hd
      obtain ⟨hd0, hd'⟩ := (mem_filter.mp hd).2
      have e : (d + 1) ^ 2 = d * (y + 2) := by
        rw [← hd']; field_simp; ring
      have hd1 : d + 1 ≠ 0 := by
        intro h1
        have : d * (y + 2) = 0 := by rw [← e, h1]; ring
        rcases mul_eq_zero.mp this with h | h
        · exact hd0 h
        · exact hy h
      have hsq : chi p ((d + 1) ^ 2) = 1 := by rw [map_pow, chi_sq hd1]
      rw [e, map_mul] at hsq
      have hy2 := chi_sq hy
      calc chi p d = chi p d * (chi p (y + 2) ^ 2) := by rw [hy2, mul_one]
        _ = chi p d * chi p (y + 2) * chi p (y + 2) := by ring
        _ = chi p (y + 2) := by rw [hsq, one_mul]
    rw [sum_congr rfl hval, sum_const, nsmul_eq_mul]
    have hcount : (S.card : ℂ) = chi p (y ^ 2 - 4) + 1 := by
      have hbij : S.card = #{e : ZMod p | e ^ 2 = y ^ 2 - 4}.toFinset := by
        refine Finset.card_bij (fun d _ => 2 * d - y) ?_ ?_ ?_
        · intro d hd
          obtain ⟨hd0, hd'⟩ := (mem_filter.mp hd).2
          simp only [Set.mem_toFinset, Set.mem_setOf_eq]
          rw [← hd']; field_simp; ring
        · intro d₁ _ d₂ _ h
          have : 2 * (d₁ - d₂) = 0 := by linear_combination h
          rcases mul_eq_zero.mp this with h' | h'
          · exact absurd h' h2
          · linear_combination h'
        · intro e he
          simp only [Set.mem_toFinset, Set.mem_setOf_eq] at he
          have hey : e + y ≠ 0 := by
            intro h0
            have : e = -y := by linear_combination h0
            rw [this] at he
            have h4 : (2 : ZMod p) * 2 = 0 := by linear_combination he
            exact h2 (mul_self_eq_zero.mp h4)
          refine ⟨(e + y) / 2, ?_, by field_simp; ring⟩
          simp only [S, mem_filter, mem_univ, true_and]
          refine ⟨div_ne_zero hey h2, ?_⟩
          field_simp
          linear_combination he
      rw [hbij]
      have := quadraticChar_card_sqrts (ringChar_ne_two hp2) (y ^ 2 - 4)
      rw [chi_apply]; exact_mod_cast this
    rw [hcount, show y ^ 2 - 4 = (y - 2) * (y + 2) by ring, map_mul]
    have hy2 := chi_sq hy
    linear_combination chi p (y - 2) * hy2

/-- **Salié's sum at a prime.** -/
theorem salie_prime (hp2 : p ≠ 2) {m : ZMod p} (hm : m ≠ 0) :
    ∑ d : ZMod p, chi p d * psi p (m * (d + d⁻¹)) =
      chi p m * gs p * (psi p (2 * m) + psi p (-2 * m)) := by
  classical
  rw [← Finset.sum_fiberwise (s := univ) (g := fun d : ZMod p => d + d⁻¹)
    (f := fun d => chi p d * psi p (m * (d + d⁻¹)))]
  have h1 : ∀ y : ZMod p, ∑ d ∈ univ.filter (fun d : ZMod p => d + d⁻¹ = y),
      chi p d * psi p (m * (d + d⁻¹)) = psi p (m * y) * (chi p (y - 2) + chi p (y + 2)) := by
    intro y
    rw [sum_congr rfl (fun d hd => by rw [(mem_filter.mp hd).2]), ← sum_mul, ← williams hp2, mul_comm]
    congr 1
    rw [← Finset.sum_filter_of_ne (p := fun d : ZMod p => d ≠ 0) (fun d _ h => by
      intro h0; rw [h0, chi_zero] at h; exact h rfl), Finset.filter_filter]
    congr 1
    ext d; simp [and_comm]
  simp_rw [h1, mul_add, Finset.sum_add_distrib, sub_eq_add_neg]
  have hs : ∀ t : ZMod p, ∑ y : ZMod p, psi p (m * y) * chi p (y + t) =
      psi p (-(m * t)) * (chi p m * gs p) := by
    intro t
    rw [← Equiv.sum_comp (Equiv.addRight (-t))]
    simp only [Equiv.coe_addRight, neg_add_cancel_right]
    rw [← sum_chi_psi hm, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [show m * (y + -t) = m * y + -(m * t) by ring, AddChar.map_add_eq_mul]; ring
  rw [hs (-2), hs 2]
  rw [show -(m * -2) = 2 * m by ring, show -(m * 2) = -2 * m by ring]
  ring

/-- **`T_p(u) = χ(−n) p (ψ(2un) + ψ(−2un))`.** -/
theorem T_prime (hp2 : p ≠ 2) {u n : ZMod p} (hu : u ≠ 0) (hn : n ≠ 0) :
    ∑ d : (ZMod p)ˣ, ∑ x : ZMod p, psi p (u * ((d : ZMod p)⁻¹ * (x ^ 2 + n) + n * d)) =
      chi p (-n) * p * (psi p (2 * (u * n)) + psi p (-2 * (u * n))) := by
  classical
  set F : ZMod p → ℂ := fun d => chi p u * gs p * (chi p d * psi p (u * n * (d + d⁻¹)))
  have hinner : ∀ d : (ZMod p)ˣ, ∑ x : ZMod p, psi p (u * ((d : ZMod p)⁻¹ * (x ^ 2 + n) + n * d)) =
      F d := by
    intro d
    have hd : u * (d : ZMod p)⁻¹ ≠ 0 := mul_ne_zero hu (inv_ne_zero d.ne_zero)
    have h := sum_psi_sq hp2 hd
    rw [map_mul, chi_inv] at h
    simp only [F]
    rw [show chi p u * gs p * (chi p d * psi p (u * n * (d + (d : ZMod p)⁻¹))) =
      psi p (u * n * (d + (d : ZMod p)⁻¹)) * (chi p u * chi p d * gs p) by ring, ← h, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  simp_rw [hinner]
  have hconv : ∑ d : (ZMod p)ˣ, F d = ∑ d : ZMod p, F d := by
    rw [← Equiv.sum_comp unitsEquivNeZero.symm]
    simp only [unitsEquivNeZero_symm_apply, Units.val_mk0]
    rw [← Finset.sum_subtype (univ.filter (fun d : ZMod p => d ≠ 0)) (fun d => by simp)]
    exact Finset.sum_filter_of_ne fun d _ h => by
      intro h0; apply h; simp [F, h0, chi_zero]
  rw [hconv]
  simp only [F]
  rw [← mul_sum, salie_prime hp2 (mul_ne_zero hu hn)]
  have hgs := gs_sq (p := p) hp2
  have hu2 := chi_sq hu
  rw [show chi p (-n) = chi p (-1) * chi p n by rw [← map_mul]; ring_nf, map_mul]
  linear_combination (chi p n * (psi p (2 * (u * n)) + psi p (-2 * (u * n)))) *
    (chi p u ^ 2 * hgs + chi p (-1) * p * hu2)

end ThreeSquares.PT
