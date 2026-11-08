/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.ThetaMult

/-!
# The two-variable theta function on `Γ₀(4)`

`Θ(z, ζ) = ∑_{n ∈ ℤ} e(n² z + n ζ)`.

* `thetaJ_rat`: `Θ(a/c + w, ζ) = (−2iwc²)^{−1/2} ∑_n G(a, n; c) e(−(n − cζ)²/(4wc²))`.
* `thetaJ_gamma`: for `γ = (a b; c d) ∈ Γ₀(4)` with `c > 0`,
  `Θ(γz, ζ/(cz+d)) = G(a,0;c)/((1+i)√c) · (cz+d)^{1/2} · e(cζ²/(4(cz+d))) · Θ(z, ζ)`.
-/

@[expose] public section

namespace ThreeSquares

open Complex Finset Real

/-- `Θ(z, ζ) = ∑_{n ∈ ℤ} e(n² z + n ζ)`. -/
noncomputable def thetaJ (z ζ : ℂ) : ℂ := ∑' n : ℤ, cexp (2 * π * I * ((n : ℂ) ^ 2 * z + n * ζ))

theorem summable_thetaJ_term {z : ℂ} (hz : 0 < z.im) (ζ : ℂ) :
    Summable (fun n : ℤ => cexp (2 * π * I * ((n : ℂ) ^ 2 * z + n * ζ))) := by
  have hre : 0 < (-2 * I * z).re := by simp; linarith
  refine (summable_cexp_quad (-2 * I * z) (2 * π * I * ζ) 0 hre).congr fun n => ?_
  congr 1
  ring_nf

theorem thetaJ_term_rat (c : ℕ) [NeZero c] (a y b : ℤ) (w ζ : ℂ) :
    cexp (2 * π * I * ((((y * c + b : ℤ) : ℂ)) ^ 2 * ((a : ℂ) / c + w) + ((y * c + b : ℤ) : ℂ) * ζ)) =
      cexp (2 * π * I * a * b ^ 2 / c) *
        cexp (-π * (-2 * I * w * (c : ℂ) ^ 2) * (y : ℂ) ^ 2 +
          2 * π * (2 * I * w * c * b + I * c * ζ) * y + 2 * π * I * (w * b ^ 2 + b * ζ)) := by
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨a * (y ^ 2 * c + 2 * y * b), ?_⟩
  push_cast
  field_simp
  ring_nf

theorem exp_complete_wJ (c : ℕ) [NeZero c] (w : ℂ) (hw : w ≠ 0) (b n ζ : ℂ) :
    cexp (2 * π * I * (w * b ^ 2 + b * ζ)) *
      cexp (-π / (-2 * I * w * (c : ℂ) ^ 2) * (n + I * (2 * I * w * c * b + I * c * ζ)) ^ 2) =
      cexp (2 * π * I * n * b / c) * cexp (-π * I * (n - c * ζ) ^ 2 / (2 * w * (c : ℂ) ^ 2)) := by
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  field_simp
  ring_nf
  have h4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, I_sq]; ring
  simp only [I_sq, h4]
  ring

/-- **Two-variable theta at a rational point plus `w`.** -/
theorem thetaJ_rat (c : ℕ) [NeZero c] (a : ℤ) (w : ℂ) (hw : 0 < w.im) (ζ : ℂ) :
    thetaJ ((a : ℂ) / c + w) ζ =
      1 / (-2 * I * w * (c : ℂ) ^ 2) ^ (1 / 2 : ℂ) *
        ∑' n : ℤ, gaussQ (a : ZMod c) (n : ZMod c) *
          cexp (-π * I * ((n : ℂ) - c * ζ) ^ 2 / (2 * w * (c : ℂ) ^ 2)) := by
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_im] at hw; exact lt_irrefl 0 hw
  set aq := -2 * I * w * (c : ℂ) ^ 2 with haq
  have haq_re : 0 < aq.re := by
    rw [haq]
    have : (-2 * I * w * (c : ℂ) ^ 2).re = 2 * c ^ 2 * w.im := by
      simp [mul_re, mul_im, pow_two]; ring
    rw [this]
    have hcr : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
    positivity
  have haq0 : aq ≠ 0 := fun h => by rw [h, zero_re] at haq_re; exact lt_irrefl 0 haq_re
  have hzim : 0 < ((a : ℂ) / c + w).im := by
    simp only [add_im, div_natCast_im, intCast_im, zero_div, zero_add]; exact hw
  unfold thetaJ
  let e : ℤ ≃ Fin c × ℤ := (Int.divModEquiv c).trans (Equiv.prodComm _ _)
  rw [← e.symm.tsum_eq]
  have hs : Summable (fun p : Fin c × ℤ => cexp (2 * π * I *
      ((((e.symm p : ℤ)) : ℂ) ^ 2 * ((a : ℂ) / c + w) + ((e.symm p : ℤ) : ℂ) * ζ))) :=
    (summable_thetaJ_term hzim ζ).comp_injective e.symm.injective
  rw [hs.tsum_prod' (fun b => (summable_thetaJ_term hzim ζ).comp_injective
    (e.symm.injective.comp (Prod.mk_right_injective b))), tsum_fintype]
  have hsum : ∀ b : ℂ, Summable (fun n : ℤ => cexp (2 * π * I * n * b / c) *
      cexp (-π * I * ((n : ℂ) - c * ζ) ^ 2 / (2 * w * (c : ℂ) ^ 2))) := by
    intro b
    have hre : 0 < (1 / aq).re := by
      rw [one_div, inv_re]; exact div_pos haq_re (normSq_pos.mpr haq0)
    refine (summable_cexp_quad (1 / aq) (2 * π * I * b / c + π * I * ζ / (w * c))
      (-π * I * ζ ^ 2 / (2 * w)) hre).congr fun n => ?_
    rw [← Complex.exp_add]
    congr 1
    rw [haq]
    field_simp
    ring_nf
    rw [I_sq]; ring
  have hb : ∀ b : Fin c, ∑' y : ℤ, cexp (2 * π * I *
      ((((e.symm (b, y) : ℤ)) : ℂ) ^ 2 * ((a : ℂ) / c + w) + ((e.symm (b, y) : ℤ) : ℂ) * ζ)) =
      1 / aq ^ (1 / 2 : ℂ) * ∑' n : ℤ, cexp (2 * π * I * a * ((b : ℕ) : ℂ) ^ 2 / c) *
        (cexp (2 * π * I * n * ((b : ℕ) : ℂ) / c) *
          cexp (-π * I * ((n : ℂ) - c * ζ) ^ 2 / (2 * w * (c : ℂ) ^ 2))) := by
    intro b
    have he : ∀ y : ℤ, (e.symm (b, y) : ℤ) = y * c + (b : ℕ) := by
      intro y
      simp [e, Int.divModEquiv, Equiv.prodComm]
    set bc : ℂ := (((b : ℕ) : ℤ) : ℂ) with hbc
    set B : ℂ := 2 * I * w * c * bc + I * c * ζ with hB
    set C : ℂ := 2 * π * I * (w * bc ^ 2 + bc * ζ) with hC
    set E : ℂ := cexp (2 * π * I * a * bc ^ 2 / c) with hE
    have hbc' : bc = ((b : ℕ) : ℂ) := by rw [hbc]; push_cast; rfl
    calc ∑' y : ℤ, cexp (2 * π * I *
          ((((e.symm (b, y) : ℤ)) : ℂ) ^ 2 * ((a : ℂ) / c + w) + ((e.symm (b, y) : ℤ) : ℂ) * ζ))
        = ∑' y : ℤ, E * (cexp (-π * aq * (y : ℂ) ^ 2 + 2 * π * B * y) * cexp C) := by
          refine tsum_congr fun y => ?_
          rw [he y, thetaJ_term_rat c a y ((b : ℕ) : ℤ) w ζ]
          simp only [hE, hB, hC, haq, hbc, ← Complex.exp_add]
      _ = E * ((1 / aq ^ (1 / 2 : ℂ) * ∑' n : ℤ, cexp (-π / aq * (n + I * B) ^ 2)) * cexp C) := by
          rw [tsum_mul_left, tsum_mul_right, Complex.tsum_exp_neg_quadratic haq_re]
      _ = 1 / aq ^ (1 / 2 : ℂ) * ∑' n : ℤ, E * (cexp C * cexp (-π / aq * (n + I * B) ^ 2)) := by
          rw [← tsum_mul_left, ← tsum_mul_right, ← tsum_mul_left, ← tsum_mul_left]
          refine tsum_congr fun n => ?_
          ring
      _ = _ := by
          congr 1
          refine tsum_congr fun n => ?_
          rw [hC, hB, haq, exp_complete_wJ c w hw0 bc n ζ, hE, hbc']
  rw [sum_congr rfl fun b _ => hb b, ← mul_sum]
  congr 1
  rw [← Summable.tsum_finsetSum (fun b _ => (hsum _).mul_left _)]
  refine tsum_congr fun n => ?_
  rw [← sum_fin_eq_gaussQ c a n, sum_mul]
  refine sum_congr rfl fun b _ => ?_
  ring

theorem thetaJ_neg (z ζ : ℂ) : thetaJ z (-ζ) = thetaJ z ζ := by
  unfold thetaJ
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Equiv.neg_apply, Int.cast_neg]
  congr 1
  ring

/-- **The two-variable theta transformation on `Γ₀(4)`.** -/
theorem thetaJ_gamma (c : ℕ) [NeZero c] (hc4 : 4 ∣ c) (a b d : ℤ) (hdet : a * d - b * c = 1)
    (z : ℂ) (hz : 0 < z.im) (ζ : ℂ) :
    thetaJ ((a * z + b) / (c * z + d)) (ζ / (c * z + d)) =
      gaussQ (a : ZMod c) 0 / ((1 + I) * (Real.sqrt c : ℂ)) * ((c : ℂ) * z + d) ^ (1 / 2 : ℂ) *
        cexp (2 * π * I * (c * ζ ^ 2 / (4 * (c * z + d)))) * thetaJ z ζ := by
  have hcr : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  set ζ₀ := (c : ℂ) * z + d with hζ₀
  have hζim : 0 < ζ₀.im := by
    rw [hζ₀]; simp only [add_im, mul_im, natCast_re, natCast_im, zero_mul, add_zero, intCast_im]
    positivity
  have hζ0 : ζ₀ ≠ 0 := fun h => by rw [h, zero_im] at hζim; exact lt_irrefl 0 hζim
  set w := -1 / ((c : ℂ) * ζ₀) with hw
  have hwim : 0 < w.im := by
    rw [hw, div_im]
    simp only [neg_re, one_re, neg_im, one_im, neg_zero, zero_mul, zero_div, zero_sub]
    have h1 : ((c : ℂ) * ζ₀).im = c * ζ₀.im := by simp [mul_im]
    rw [h1, neg_mul, neg_div, neg_neg]
    have : 0 < normSq ((c : ℂ) * ζ₀) := normSq_pos.mpr (mul_ne_zero hc' hζ0)
    positivity
  have hγ : (a * z + b) / (c * z + d) = (a : ℂ) / c + w := by
    have := gamma_sub a b c d hdet z (by exact_mod_cast NeZero.ne c) (by exact_mod_cast hζ0)
    push_cast at this
    rw [this, hw, hζ₀]
  rw [hγ, thetaJ_rat c a w hwim]
  have haq : -2 * I * w * (c : ℂ) ^ 2 = 2 * I * c / ζ₀ := by
    rw [hw]; field_simp
  have hinv := inv_sqrt_aq (c : ℝ) hcr ζ₀ hζim
  push_cast at hinv
  rw [haq, hinv]
  have had : (a : ZMod c) * (d : ZMod c) = 1 := by
    have : ((a * d - b * c : ℤ) : ZMod c) = 1 := by rw [hdet]; simp
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, sub_zero] at this
    exact this
  set f : ℤ → ℂ := fun n => gaussQ (a : ZMod c) (n : ZMod c) *
    cexp (-π * I * ((n : ℂ) - c * (ζ / ζ₀)) ^ 2 / (2 * w * (c : ℂ) ^ 2)) with hf
  have hsupp : Function.support f ⊆ Set.range (fun l : ℤ => 2 * l) := by
    intro n hn
    rcases Int.even_or_odd n with ⟨l, rfl⟩ | ho
    · exact ⟨l, by ring⟩
    · exfalso; apply hn; simp only [hf, gaussQ_odd_eq_zero c hc4 _ n ho, zero_mul]
  have hinj : Function.Injective (fun l : ℤ => 2 * l) := fun x y h => by simpa using h
  have hterm : ∀ l : ℤ, f (2 * l) = gaussQ (a : ZMod c) 0 *
      cexp (2 * π * I * (c * ζ ^ 2 / (4 * ζ₀))) *
        cexp (2 * π * I * ((l : ℂ) ^ 2 * z + ((-l : ℤ) : ℂ) * ζ)) := by
    intro l
    simp only [hf]
    rw [show (((2 * l : ℤ)) : ZMod c) = 2 * (l : ZMod c) by push_cast; ring,
      gaussQ_even c _ _ had,
      show -((d : ZMod c) * (l : ZMod c) ^ 2) = ((-(d * l ^ 2) : ℤ) : ZMod c) by push_cast; ring,
      ZMod.stdAddChar_coe]
    rw [mul_comm (cexp _) (gaussQ _ _), mul_assoc, ← Complex.exp_add]
    rw [mul_assoc (gaussQ _ _), ← Complex.exp_add]
    congr 2
    rw [hw]
    push_cast
    rw [show (d : ℂ) = ζ₀ - c * z by rw [hζ₀]; ring]
    field_simp
    ring
  rw [← hinj.tsum_eq hsupp]
  simp only [hterm]
  rw [tsum_mul_left]
  have hneg : ∑' l : ℤ, cexp (2 * π * I * ((l : ℂ) ^ 2 * z + ((-l : ℤ) : ℂ) * ζ)) = thetaJ z ζ := by
    rw [← thetaJ_neg z ζ]
    unfold thetaJ
    refine tsum_congr fun l => ?_
    push_cast
    ring_nf
  rw [hneg]
  ring

end ThreeSquares
