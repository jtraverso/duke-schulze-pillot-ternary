/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.Blocks

/-!
# Conversions used by the block analysis

* `ker1_congr`: the kernel only sees the weight on `(y, Y]`;
* `jac_neg_n`: `J(−n | a) = J(a | n)` for odd `a` and `n ≡ 3 (mod 4)`;
* `chiR_eq_jac`: on a unit class `a ≡ t (mod r)`, `χ(a) = J(t | n₁) J(a | n₀)` with `n₁ = gcd(n, r)`,
  `n₀ = n / n₁` coprime to `r`.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open ZMod Finset

theorem ker1_congr (r y Y : ℕ) (W W' : ℕ → ℂ) (hW : ∀ c, y < c → c ≤ Y → W c = W' c) (h : ℤ)
    (p a b : ℕ) : ker1 r y Y W h p a b = ker1 r y Y W' h p a b := by
  unfold ker1
  split_ifs with hc
  · rw [hW _ hc.1 hc.2]
  · rfl

theorem jac_neg_n (n a : ℕ) (hn : n % 4 = 3) (ha : Odd a) :
    jacobiSym (-(n : ℤ)) a = jacobiSym (a : ℤ) n := by
  have hn' : Odd n := Nat.odd_iff.mpr (by omega)
  rw [show (-(n : ℤ)) = (-1) * n by ring, jacobiSym.mul_left, jacobiSym.at_neg_one ha,
    jacobiSym.quadratic_reciprocity hn' ha]
  have hn2 : Odd (n / 2) := Nat.odd_iff.mpr (by omega)
  rcases Nat.odd_iff.mp ha |> fun h => (show a % 4 = 1 ∨ a % 4 = 3 by omega) with h4 | h4
  · rw [ZMod.χ₄_nat_one_mod_four h4]
    have : Even (n / 2 * (a / 2)) := Nat.even_mul.mpr (Or.inr (Nat.even_iff.mpr (by omega)))
    rw [this.neg_one_pow]; ring
  · rw [ZMod.χ₄_nat_three_mod_four h4]
    have : Odd (n / 2 * (a / 2)) := Nat.odd_mul.mpr ⟨hn2, Nat.odd_iff.mpr (by omega)⟩
    rw [this.neg_one_pow]; ring

theorem gcd_dvd_of_smooth_part {n r : ℕ} : Nat.gcd n r ∣ r := Nat.gcd_dvd_right n r

theorem coprime_div_gcd {n r : ℕ} (hn : Squarefree n) (hn0 : n ≠ 0) : Nat.Coprime (n / Nat.gcd n r) r := by
  by_contra h
  obtain ⟨ℓ, hℓ, h1, h2⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hg : Nat.gcd n r ∣ n := Nat.gcd_dvd_left n r
  have hℓn : ℓ ∣ n := h1.trans (Nat.div_dvd_of_dvd hg)
  have hℓg : ℓ ∣ Nat.gcd n r := Nat.dvd_gcd hℓn h2
  have : ℓ * ℓ ∣ n := by
    have e : n = Nat.gcd n r * (n / Nat.gcd n r) := (Nat.mul_div_cancel' hg).symm
    rw [e]; exact Nat.mul_dvd_mul hℓg h1
  exact hℓ.one_lt.ne' (Nat.isUnit_iff.mp (hn ℓ this))

/-- **`χ` on a unit class.** -/
theorem chiR_eq_jac (n r a t : ℕ) (hn : Squarefree n) (hn0 : n ≠ 0) (hn4 : n % 4 = 3) (h8 : 8 ∣ r)
    (hr0 : 0 < r) (hrs : Smooth (S2 n) r) (hat : a % r = t) (ht : IsUnit ((t : ZMod r))) :
    chiR n a = (jacobiSym (t : ℤ) (Nat.gcd n r) : ℂ) * (jacobiSym (a : ℤ) (n / Nat.gcd n r) : ℂ) := by
  set n₁ := Nat.gcd n r
  set n₀ := n / n₁
  have hn₁r : n₁ ∣ r := Nat.gcd_dvd_right n r
  have hn₁n : n₁ ∣ n := Nat.gcd_dvd_left n r
  have hnn : n = n₁ * n₀ := (Nat.mul_div_cancel' hn₁n).symm
  have hn₁0 : n₁ ≠ 0 := by intro h; rw [h] at hnn; simp at hnn; exact hn0 hnn
  have hn₀0 : n₀ ≠ 0 := by intro h; rw [h] at hnn; simp at hnn; exact hn0 hnn
  haveI : NeZero n₁ := ⟨hn₁0⟩
  haveI : NeZero n₀ := ⟨hn₀0⟩
  have htr : t < r := by rw [← hat]; exact Nat.mod_lt _ hr0
  have hcop : Nat.Coprime t r := (ZMod.isUnit_iff_coprime t r).mp ht
  have hamod : a ≡ t [MOD r] := by rw [Nat.ModEq, hat, Nat.mod_eq_of_lt htr]
  have hacop : Nat.Coprime a r := by
    rw [Nat.Coprime, Nat.ModEq.gcd_eq hamod]; exact hcop
  by_cases hro : Rough (S2 n) a
  · unfold chiR
    rw [if_pos hro]
    have ha0 : 0 < a := Nat.pos_of_ne_zero (by
      rintro rfl; exact hro 2 Nat.prime_two (dvd_zero 2) (dvd_mul_right 2 n))
    rw [jac_neg_n n a hn4 (rough_odd hro ha0), hnn, jacobiSym.mul_right]
    have hmod : jacobiSym (a : ℤ) n₁ = jacobiSym (t : ℤ) n₁ := by
      apply jacobiSym.mod_left'
      have h1 := Nat.ModEq.of_dvd hn₁r hamod
      rw [Nat.ModEq] at h1
      have h2 := congrArg (fun x : ℕ => (x : ℤ)) h1
      simp only [Int.natCast_mod] at h2
      exact h2
    rw [hmod]; push_cast; ring
  · rw [chiR_eq_zero_of_not_rough hro]
    -- a prime of `n₀` divides `a`
    unfold Rough at hro
    push_neg at hro
    obtain ⟨ℓ, hℓ, hℓa, hℓ2n⟩ := hro
    have hℓr : ¬ ℓ ∣ r := fun h => by
      have := Nat.dvd_gcd hℓa h
      rw [hacop.gcd_eq_one] at this
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp this)
    have hℓ2 : ℓ ≠ 2 := by
      rintro rfl; exact hℓr ((by norm_num : 2 ∣ 8).trans h8)
    have hℓn : ℓ ∣ n := by
      rcases (Nat.Prime.dvd_mul hℓ).mp hℓ2n with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h) hℓ2
      · exact h
    have hℓn₀ : ℓ ∣ n₀ := by
      rw [hnn] at hℓn
      rcases (Nat.Prime.dvd_mul hℓ).mp hℓn with h | h
      · exact absurd (h.trans hn₁r) hℓr
      · exact h
    have hz : jacobiSym (a : ℤ) n₀ = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime]
      intro hg
      have h1 : (ℓ : ℤ) ∣ (a : ℤ) := Int.natCast_dvd_natCast.mpr hℓa
      have h2 : (ℓ : ℤ) ∣ (n₀ : ℤ) := Int.natCast_dvd_natCast.mpr hℓn₀
      have := Int.dvd_gcd h1 h2
      rw [hg] at this
      have h3 : (ℓ : ℤ) ∣ 1 := by exact_mod_cast this
      have h4 : ℓ ∣ 1 := by exact_mod_cast h3
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp h4)
    rw [hz]; simp

theorem rph_mul_rph_neg (r : ℕ) (h : ℤ) (x : ℕ) (hr : 0 < r) (hx : x.Coprime r) :
    rph r h (x : ℤ) * rph r (-h) (x : ℤ) = 1 := by
  haveI : NeZero r := ⟨hr.ne'⟩
  unfold rph
  rw [dif_neg hr.ne', dif_neg hr.ne']
  unfold RML.ExpSum.Weil.reciprocalPhase
  have hu : IsUnit ((x : ℤ) : ZMod r) := by push_cast; rw [ZMod.isUnit_iff_coprime]; exact hx
  rw [if_pos hu, if_pos hu, ← AddChar.map_add_eq_mul]
  push_cast
  rw [show (h : ZMod r) * ((x : ZMod r))⁻¹ + -(h : ZMod r) * ((x : ZMod r))⁻¹ = 0 by ring,
    AddChar.map_zero_eq_one]

/-- **From the Method-1 kernel to the Method-2 kernel** (case `p ∣ a`). -/
theorem ker1_eq_ker2 (ℓ n r y Y p a b : ℕ) (hr0 : 0 < r) (hp : p.Prime) (hpn : ¬ p ∣ 2 * n)
    (hrs : Smooth (S2 n) r) (ha : Rough (S2 n) a) (hb : Rough (S2 n) b) (ha0 : 0 < a) (hb0 : 0 < b) :
    ker1 r y Y (W1 ℓ n) (hInv (-4 * n) r b) p a b =
      rph r (2 * n) ((p * a * b : ℕ) : ℤ) ^ 2 * ker2 r y Y (W2 ℓ n) (4 * n) p b a := by
  have hpa : Rough (S2 n) (p * a) := rough_mul_iff.mpr ⟨rough_prime hp hpn, ha⟩
  have hrb : r.Coprime b := coprime_of_smooth_rough hrs hb
  have hrpa : r.Coprime (p * a) := coprime_of_smooth_rough hrs hpa
  unfold ker1 ker2
  rw [show r * p * b * a = r * p * a * b by ring]
  split_ifs with hR
  · by_cases hc : (p * a).Coprime b
    · have hsw := form_swap' r (p * a) b hr0 (Nat.mul_pos hp.pos ha0) hb0 hrpa hrb hc n
      have hx : ((p * a) * b).Coprime r := (coprime_of_smooth_rough hrs
        (rough_mul_iff.mpr ⟨hpa, hb⟩)).symm
      have hprod := rph_mul_rph_neg r (2 * n) ((p * a) * b) hr0 hx
      rw [show (-(2 * (n : ℤ))) = -2 * n by ring] at hprod
      rw [show ((b * (p * a) : ℕ) : ℤ) = (((p * a) * b : ℕ) : ℤ) by push_cast; ring,
        show (2 * ((-(n : ℤ) : ℤ) : ℂ)) = -(2 * ((n : ℤ) : ℂ)) by push_cast; ring] at hsw
      rw [rph_mul_r (-4 * n) r b (p * a) hb0 hrb |>.symm]
      unfold W1 W2
      rw [show r * p * a * b = r * (p * a) * b by ring, show p * a * b = (p * a) * b by ring]
      set K := ((r * (p * a) * b : ℕ) : ℂ) * Poin.cfac ℓ n (r * (p * a) * b)
      set E1 := Complex.exp (2 * Real.pi * Complex.I * (2 * ((n : ℤ) : ℂ) / ((r * (p * a) * b : ℕ) : ℂ)))
      set E2 := Complex.exp (2 * Real.pi * Complex.I * (-(2 * ((n : ℤ) : ℂ)) / ((r * (p * a) * b : ℕ) : ℂ)))
      set A1 := rph b (-4 * n) ((r * (p * a) : ℕ) : ℤ)
      set A2 := rph (p * a) (4 * n) ((r * b : ℕ) : ℤ)
      set Rm := rph r (-2 * n) (((p * a) * b : ℕ) : ℤ)
      set Rp := rph r (2 * n) (((p * a) * b : ℕ) : ℤ)
      have hE : Complex.exp (2 * Real.pi * Complex.I * (2 * -((n : ℤ) : ℂ) / ((r * (p * a) * b : ℕ) : ℂ))) = E2 := by
        simp only [E2]; congr 1; ring
      rw [hE]
      calc K * E1 * A1 = K * E1 * A1 * (Rp * Rm) := by rw [hprod, mul_one]
        _ = K * Rp * (E1 * (A1 * Rm)) := by ring
        _ = K * Rp * (E2 * (A2 * Rp)) := by rw [hsw]
        _ = Rp ^ 2 * (K * E2 * A2) := by ring
    · rw [rph_eq_zero_of_not_coprime b _ (p * a) hc,
        rph_eq_zero_of_not_coprime (p * a) _ (r * b) (fun h => hc (by
          have := Nat.Coprime.coprime_dvd_left (dvd_mul_left b r) h
          exact this.symm))]
      ring
  · simp

/-- **From the Method-1 kernel to the Method-2 kernel** (case `p ∣ b`, weights swapped). -/
theorem ker1_eq_ker2' (ℓ n r y Y p a b : ℕ) (hr0 : 0 < r) (hp : p.Prime) (hpn : ¬ p ∣ 2 * n)
    (hrs : Smooth (S2 n) r) (ha : Rough (S2 n) a) (hb : Rough (S2 n) b) (ha0 : 0 < a) (hb0 : 0 < b) :
    ker1 r y Y (W2 ℓ n) (hInv (4 * n) r b) p a b =
      rph r (-2 * n) ((p * a * b : ℕ) : ℤ) ^ 2 * ker2 r y Y (W1 ℓ n) (-4 * n) p b a := by
  have hpa : Rough (S2 n) (p * a) := rough_mul_iff.mpr ⟨rough_prime hp hpn, ha⟩
  have hrb : r.Coprime b := coprime_of_smooth_rough hrs hb
  have hrpa : r.Coprime (p * a) := coprime_of_smooth_rough hrs hpa
  unfold ker1 ker2
  rw [show r * p * b * a = r * p * a * b by ring]
  split_ifs with hR
  · by_cases hc : (p * a).Coprime b
    · have hsw := form_swap' r b (p * a) hr0 hb0 (Nat.mul_pos hp.pos ha0) hrb hrpa hc.symm n
      have hx : ((p * a) * b).Coprime r := (coprime_of_smooth_rough hrs
        (rough_mul_iff.mpr ⟨hpa, hb⟩)).symm
      have hprod := rph_mul_rph_neg r (-2 * n) ((p * a) * b) hr0 hx
      rw [show (-(-2 * (n : ℤ))) = 2 * n by ring] at hprod
      rw [show ((b * (p * a) : ℕ) : ℤ) = (((p * a) * b : ℕ) : ℤ) by push_cast; ring,
        show r * b * (p * a) = r * (p * a) * b by ring,
        show (2 * ((-(n : ℤ) : ℤ) : ℂ)) = -(2 * ((n : ℤ) : ℂ)) by push_cast; ring] at hsw
      rw [rph_mul_r (4 * n) r b (p * a) hb0 hrb |>.symm]
      unfold W1 W2
      rw [show r * p * a * b = r * (p * a) * b by ring, show p * a * b = (p * a) * b by ring]
      set K := ((r * (p * a) * b : ℕ) : ℂ) * Poin.cfac ℓ n (r * (p * a) * b)
      set E1 := Complex.exp (2 * Real.pi * Complex.I * (2 * ((n : ℤ) : ℂ) / ((r * (p * a) * b : ℕ) : ℂ)))
      set E2 := Complex.exp (2 * Real.pi * Complex.I * (-(2 * ((n : ℤ) : ℂ)) / ((r * (p * a) * b : ℕ) : ℂ)))
      set A1 := rph (p * a) (-4 * n) ((r * b : ℕ) : ℤ)
      set A2 := rph b (4 * n) ((r * (p * a) : ℕ) : ℤ)
      set Rm := rph r (-2 * n) (((p * a) * b : ℕ) : ℤ)
      set Rp := rph r (2 * n) (((p * a) * b : ℕ) : ℤ)
      have hE : Complex.exp (2 * Real.pi * Complex.I * (2 * -((n : ℤ) : ℂ) / ((r * (p * a) * b : ℕ) : ℂ))) = E2 := by
        simp only [E2]; congr 1; ring
      rw [hE]
      calc K * E2 * A2 = K * E2 * A2 * (Rm * Rp) := by rw [hprod, mul_one]
        _ = K * Rm * (E2 * (A2 * Rp)) := by ring
        _ = K * Rm * (E1 * (A1 * Rm)) := by rw [← hsw]
        _ = Rm ^ 2 * (K * E1 * A1) := by ring
    · rw [rph_eq_zero_of_not_coprime b _ (p * a) hc,
        rph_eq_zero_of_not_coprime (p * a) _ (r * b) (fun h => hc (by
          have := Nat.Coprime.coprime_dvd_left (dvd_mul_left b r) h
          exact this.symm))]
      ring
  · simp

end ThreeSquares
