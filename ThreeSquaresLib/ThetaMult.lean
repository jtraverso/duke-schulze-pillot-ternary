/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Theta

/-!
# The theta multiplier on `Γ₀(4)`

`θ(z) = ∑_{n ∈ ℤ} e(n² z)` on the upper half plane.

* `thetaFn_rat`: for `c ≥ 1`, any integer `a` and `Im w > 0`,
  `θ(a/c + w) = (−2iwc²)^{−1/2} ∑_n G(a, n; c) e(−n²/(4wc²))` (Poisson summation in each residue
  class mod `c`).
* `thetaFn_gamma`: for `γ = (a b; c d)` with `ad − bc = 1`, `c > 0`, `4 ∣ c` and `Im z > 0`,
  `θ(γz) = G(a, 0; c)/((1+i)√c) · (cz+d)^{1/2} · θ(z)`.
-/

@[expose] public section

namespace ThreeSquares

open Complex Finset Real

/-- `θ(z) = ∑_{n ∈ ℤ} e(n² z)`. -/
noncomputable def thetaFn (z : ℂ) : ℂ := ∑' n : ℤ, cexp (2 * π * I * (n : ℂ) ^ 2 * z)

theorem summable_thetaFn_term {z : ℂ} (hz : 0 < z.im) :
    Summable (fun n : ℤ => cexp (2 * π * I * (n : ℂ) ^ 2 * z)) := by
  have hre : 0 < (-2 * I * z).re := by simp; linarith
  refine (summable_cexp_quad (-2 * I * z) 0 0 hre).congr fun n => ?_
  congr 1
  ring_nf

/-- The `b`-th residue class of the theta series at `a/c + w`. -/
theorem theta_term_rat (c : ℕ) [NeZero c] (a y b : ℤ) (w : ℂ) :
    cexp (2 * π * I * (((y * c + b : ℤ) : ℂ)) ^ 2 * ((a : ℂ) / c + w)) =
      cexp (2 * π * I * a * b ^ 2 / c) *
        cexp (-π * (-2 * I * w * (c : ℂ) ^ 2) * (y : ℂ) ^ 2 + 2 * π * (2 * I * w * c * b) * y +
          2 * π * I * w * b ^ 2) := by
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  rw [← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨a * (y ^ 2 * c + 2 * y * b), ?_⟩
  push_cast
  field_simp
  ring_nf

theorem exp_complete_w (c : ℕ) [NeZero c] (w : ℂ) (hw : w ≠ 0) (b n : ℂ) :
    cexp (2 * π * I * w * b ^ 2) *
      cexp (-π / (-2 * I * w * (c : ℂ) ^ 2) * (n + I * (2 * I * w * c * b)) ^ 2) =
      cexp (2 * π * I * n * b / c) * cexp (-π * I * n ^ 2 / (2 * w * (c : ℂ) ^ 2)) := by
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  field_simp
  ring_nf
  have h4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, I_sq]; ring
  simp only [I_sq, h4]
  ring

/-- **Theta at a rational point plus `w`.** -/
theorem thetaFn_rat (c : ℕ) [NeZero c] (a : ℤ) (w : ℂ) (hw : 0 < w.im) :
    thetaFn ((a : ℂ) / c + w) =
      1 / (-2 * I * w * (c : ℂ) ^ 2) ^ (1 / 2 : ℂ) *
        ∑' n : ℤ, gaussQ (a : ZMod c) (n : ZMod c) * cexp (-π * I * (n : ℂ) ^ 2 / (2 * w * (c : ℂ) ^ 2)) := by
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hcr : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_im] at hw; exact lt_irrefl 0 hw
  set aq := -2 * I * w * (c : ℂ) ^ 2 with haq
  have haq_re : 0 < aq.re := by
    rw [haq]
    have : (-2 * I * w * (c : ℂ) ^ 2).re = 2 * c ^ 2 * w.im := by
      simp [mul_re, mul_im, pow_two]; ring
    rw [this]; positivity
  have haq0 : aq ≠ 0 := fun h => by rw [h, zero_re] at haq_re; exact lt_irrefl 0 haq_re
  have hzim : 0 < ((a : ℂ) / c + w).im := by
    simp only [add_im, div_natCast_im, intCast_im, zero_div, zero_add]; exact hw
  -- split by residues mod `c`
  unfold thetaFn
  let e : ℤ ≃ Fin c × ℤ := (Int.divModEquiv c).trans (Equiv.prodComm _ _)
  rw [← e.symm.tsum_eq]
  have hs : Summable (fun p : Fin c × ℤ =>
      cexp (2 * π * I * (((e.symm p : ℤ)) : ℂ) ^ 2 * ((a : ℂ) / c + w))) :=
    (summable_thetaFn_term hzim).comp_injective e.symm.injective
  rw [hs.tsum_prod' (fun b => (summable_thetaFn_term hzim).comp_injective
    (e.symm.injective.comp (Prod.mk_right_injective b))), tsum_fintype]
  -- the transformed terms are summable
  have hsum : ∀ b : ℂ, Summable (fun n : ℤ =>
      cexp (2 * π * I * n * b / c) * cexp (-π * I * (n : ℂ) ^ 2 / (2 * w * (c : ℂ) ^ 2))) := by
    intro b
    have hre : 0 < (1 / aq).re := by
      rw [one_div, inv_re]; exact div_pos haq_re (normSq_pos.mpr haq0)
    refine (summable_cexp_quad (1 / aq) (2 * π * I * b / c) 0 hre).congr fun n => ?_
    rw [← Complex.exp_add]
    congr 1
    rw [haq]
    field_simp
    ring_nf
    rw [I_sq]; ring
  have hb : ∀ b : Fin c, ∑' y : ℤ, cexp (2 * π * I *
      (((e.symm (b, y) : ℤ)) : ℂ) ^ 2 * ((a : ℂ) / c + w)) =
      1 / aq ^ (1 / 2 : ℂ) * ∑' n : ℤ, cexp (2 * π * I * a * ((b : ℕ) : ℂ) ^ 2 / c) *
        (cexp (2 * π * I * n * ((b : ℕ) : ℂ) / c) *
          cexp (-π * I * (n : ℂ) ^ 2 / (2 * w * (c : ℂ) ^ 2))) := by
    intro b
    have he : ∀ y : ℤ, (e.symm (b, y) : ℤ) = y * c + (b : ℕ) := by
      intro y
      simp [e, Int.divModEquiv, Equiv.prodComm]
    set bc : ℂ := (((b : ℕ) : ℤ) : ℂ) with hbc
    set B : ℂ := 2 * I * w * c * bc with hB
    set C : ℂ := 2 * π * I * w * bc ^ 2 with hC
    set E : ℂ := cexp (2 * π * I * a * bc ^ 2 / c) with hE
    have hbc' : bc = ((b : ℕ) : ℂ) := by rw [hbc]; push_cast; rfl
    calc ∑' y : ℤ, cexp (2 * π * I * (((e.symm (b, y) : ℤ)) : ℂ) ^ 2 * ((a : ℂ) / c + w))
        = ∑' y : ℤ, E * (cexp (-π * aq * (y : ℂ) ^ 2 + 2 * π * B * y) * cexp C) := by
          refine tsum_congr fun y => ?_
          rw [he y, theta_term_rat c a y ((b : ℕ) : ℤ) w]
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
          rw [hC, hB, haq, exp_complete_w c w hw0 bc n, hE, hbc']
  rw [sum_congr rfl fun b _ => hb b, ← mul_sum]
  congr 1
  rw [← Summable.tsum_finsetSum (fun b _ => (hsum _).mul_left _)]
  refine tsum_congr fun n => ?_
  rw [← sum_fin_eq_gaussQ c a n, sum_mul]
  refine sum_congr rfl fun b _ => ?_
  ring

/-! ### Specialization to `Γ₀(4)` -/

theorem gaussQ_odd_eq_zero (c : ℕ) [NeZero c] (hc : 4 ∣ c) (a : ZMod c) (n : ℤ) (hn : Odd n) :
    gaussQ a (n : ZMod c) = 0 := by
  obtain ⟨m, rfl⟩ := hc
  set h : ZMod (4 * m) := ((2 * m : ℕ) : ZMod (4 * m)) with hh
  have h2 : 2 * h = 0 := by
    rw [hh]; push_cast
    rw [show (2 : ZMod (4 * m)) * (2 * m) = ((4 * m : ℕ) : ZMod (4 * m)) by push_cast; ring,
      ZMod.natCast_self]
  have hsq : h ^ 2 = 0 := by
    rw [hh, ← Nat.cast_pow, show (2 * m) ^ 2 = (4 * m) * m by ring, Nat.cast_mul, ZMod.natCast_self,
      zero_mul]
  have hchar : (ZMod.stdAddChar ((n : ZMod (4 * m)) * h) : ℂ) = -1 := by
    rw [hh, show ((n : ZMod (4 * m)) * ((2 * m : ℕ) : ZMod (4 * m))) =
      ((n * (2 * m : ℕ) : ℤ) : ZMod (4 * m)) by push_cast; ring, ZMod.stdAddChar_coe]
    obtain ⟨k, rfl⟩ := hn
    have hm : (m : ℂ) ≠ 0 := by
      intro h0; apply NeZero.ne (4 * m); exact_mod_cast (by rw [Nat.cast_mul, h0, mul_zero] : ((4 * m : ℕ) : ℂ) = 0)
    rw [show 2 * π * I * (((2 * k + 1) * (2 * m : ℕ) : ℤ) : ℂ) / ((4 * m : ℕ) : ℂ) =
      (k : ℂ) * (2 * π * I) + π * I by push_cast; field_simp; ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_pi_mul_I]
  have key0 : gaussQ a (n : ZMod (4 * m)) =
      ZMod.stdAddChar ((n : ZMod (4 * m)) * h) * gaussQ a (n : ZMod (4 * m)) := by
    unfold gaussQ
    conv_lhs => rw [← Equiv.sum_comp (Equiv.addRight h)]
    rw [mul_sum]
    refine sum_congr rfl fun b _ => ?_
    simp only [Equiv.coe_addRight]
    rw [← AddChar.map_add_eq_mul]
    congr 1
    linear_combination (a * b) * h2 + a * hsq
  rw [hchar] at key0
  have key : gaussQ a (n : ZMod (4 * m)) = -gaussQ a (n : ZMod (4 * m)) := by
    rw [neg_one_mul] at key0; exact key0
  have : (2 : ℂ) * gaussQ a (n : ZMod (4 * m)) = 0 := by linear_combination key
  simpa using this

theorem gaussQ_even (c : ℕ) [NeZero c] (a d : ZMod c) (had : a * d = 1) (l : ZMod c) :
    gaussQ a (2 * l) = ZMod.stdAddChar (-(d * l ^ 2)) * gaussQ a 0 := by
  unfold gaussQ
  rw [mul_sum, ← Equiv.sum_comp (Equiv.addRight (-(d * l)))]
  refine sum_congr rfl fun b _ => ?_
  simp only [Equiv.coe_addRight, zero_mul, add_zero]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  linear_combination (-(2 * b * l) + d * l ^ 2) * had

/-- `(az + b)/(cz + d) − a/c = −1/(c(cz + d))`. -/
theorem gamma_sub (a b c d : ℤ) (hdet : a * d - b * c = 1) (z : ℂ) (hc : (c : ℂ) ≠ 0)
    (hz : (c : ℂ) * z + d ≠ 0) :
    (a * z + b) / (c * z + d) = (a : ℂ) / c + (-1 / (c * (c * z + d))) := by
  have h : ((a * d - b * c : ℤ) : ℂ) = 1 := by rw [hdet]; simp
  push_cast at h
  calc (a * z + b) / (c * z + d) = (c * (a * z + b)) / (c * (c * z + d)) := by
        rw [mul_div_mul_left _ _ hc]
    _ = (a * (c * z + d) - 1) / (c * (c * z + d)) := by
        congr 1; linear_combination (-1 : ℂ) * h
    _ = (a : ℂ) / c + (-1 / (c * (c * z + d))) := by
        field_simp
        ring

/-- Square roots: `1 / (2ic/ζ)^{1/2} = ζ^{1/2} / ((1+i)√c)` for `Im ζ > 0`, `c > 0`. -/
theorem inv_sqrt_aq (c : ℝ) (hc : 0 < c) (ζ : ℂ) (hζ : 0 < ζ.im) :
    1 / (2 * I * c / ζ) ^ (1 / 2 : ℂ) = ζ ^ (1 / 2 : ℂ) / ((1 + I) * (Real.sqrt c : ℂ)) := by
  have hζ0 : ζ ≠ 0 := fun h => by rw [h, zero_im] at hζ; exact lt_irrefl 0 hζ
  set A := 2 * I * c / ζ with hA
  have hA0 : A ≠ 0 := by
    rw [hA]; exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (by exact_mod_cast hc.ne')) hζ0
  have hAre : 0 < A.re := by
    rw [hA, div_re]
    have h1 : (2 * I * (c : ℂ)).re = 0 := by simp
    have h2 : (2 * I * (c : ℂ)).im = 2 * c := by simp
    rw [h1, h2, zero_mul, zero_div, zero_add]
    have : 0 < normSq ζ := normSq_pos.mpr hζ0
    positivity
  -- the right side
  set x := 1 / A ^ (1 / 2 : ℂ) with hx
  set y := ζ ^ (1 / 2 : ℂ) / ((1 + I) * (Real.sqrt c : ℂ)) with hy
  have hsqA : (A ^ (1 / 2 : ℂ)) ^ 2 = A := by
    rw [show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by norm_num, Complex.cpow_ofNat_inv_pow]
  have hsqζ : (ζ ^ (1 / 2 : ℂ)) ^ 2 = ζ := by
    rw [show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by norm_num, Complex.cpow_ofNat_inv_pow]
  have hsc : ((Real.sqrt c : ℝ) : ℂ) ^ 2 = c := by
    rw [← ofReal_pow, Real.sq_sqrt hc.le]
  have hx2 : x ^ 2 = 1 / A := by rw [hx, div_pow, hsqA, one_pow]
  have hy2 : y ^ 2 = 1 / A := by
    rw [hy, div_pow, mul_pow, hsqζ, hsc, hA]
    have : (1 + I) ^ 2 = 2 * I := by ring_nf; rw [I_sq]; ring
    rw [this]
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    field_simp
  -- positive real parts
  have hre_cpow : ∀ B : ℂ, B ≠ 0 → |B.arg| < π → 0 < (B ^ (1 / 2 : ℂ)).re ∧
      (0 < B.arg → 0 < (B ^ (1 / 2 : ℂ)).im) := by
    intro B hB harg
    rw [Complex.cpow_def_of_ne_zero hB, Complex.exp_re, Complex.exp_im]
    have him : (Complex.log B * (1 / 2 : ℂ)).im = B.arg / 2 := by
      rw [mul_im, log_re, log_im]; norm_num; ring
    rw [him]
    constructor
    · apply mul_pos (Real.exp_pos _)
      apply Real.cos_pos_of_mem_Ioo
      constructor <;> linarith [abs_lt.mp harg]
    · intro hpos
      apply mul_pos (Real.exp_pos _)
      apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [abs_lt.mp harg]
  have hargA : |A.arg| < π := by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hAre)
    linarith [Real.pi_pos]
  have hxre : 0 < x.re := by
    rw [hx, one_div, inv_re]
    have hA2 : A ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; tauto
    exact div_pos (hre_cpow A hA0 hargA).1 (normSq_pos.mpr hA2)
  have hargζ : 0 < ζ.arg ∧ ζ.arg < π := by
    constructor
    · refine lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr hζ.le) (fun h => ?_)
      have := (Complex.arg_eq_zero_iff.mp h.symm).2
      linarith
    · refine lt_of_le_of_ne (Complex.arg_le_pi ζ) (fun h => ?_)
      have := (Complex.arg_eq_pi_iff.mp h).2
      linarith
  obtain ⟨hζre, hζim⟩ := hre_cpow ζ hζ0 (by rw [abs_lt]; constructor <;> linarith [hargζ.1, hargζ.2])
  have hyre : 0 < y.re := by
    rw [hy, div_re]
    have hsq : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc
    simp only [mul_re, mul_im, add_re, add_im, one_re, one_im, I_re, I_im, ofReal_re, ofReal_im,
      normSq_apply]
    have h1 := hζim hargζ.1
    have hden : 0 < (Real.sqrt c) ^ 2 * 2 := by positivity
    field_simp
    nlinarith [mul_pos hsq h1, mul_pos hsq hζre]
  -- conclude
  have hsum : (x - y) * (x + y) = 0 := by
    rw [show (x - y) * (x + y) = x ^ 2 - y ^ 2 by ring, hx2, hy2, sub_self]
  rcases mul_eq_zero.mp hsum with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have := congrArg Complex.re h
    rw [add_re, zero_re] at this
    linarith

/-- **The theta multiplier on `Γ₀(4)`.** -/
theorem thetaFn_gamma (c : ℕ) [NeZero c] (hc4 : 4 ∣ c) (a b d : ℤ) (hdet : a * d - b * c = 1)
    (z : ℂ) (hz : 0 < z.im) :
    thetaFn ((a * z + b) / (c * z + d)) =
      gaussQ (a : ZMod c) 0 / ((1 + I) * (Real.sqrt c : ℂ)) * ((c : ℂ) * z + d) ^ (1 / 2 : ℂ) *
        thetaFn z := by
  have hcr : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne c)
  have hc : ((c : ℤ) : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne c
  set ζ := (c : ℂ) * z + d with hζ
  have hζim : 0 < ζ.im := by
    rw [hζ]; simp only [add_im, mul_im, natCast_re, natCast_im, zero_mul, add_zero, intCast_im]
    positivity
  have hζ0 : ζ ≠ 0 := fun h => by rw [h, zero_im] at hζim; exact lt_irrefl 0 hζim
  set w := -1 / ((c : ℂ) * ζ) with hw
  have hwim : 0 < w.im := by
    rw [hw, div_im]
    simp only [neg_re, one_re, neg_im, one_im, neg_zero, zero_mul, zero_div, zero_sub]
    have h1 : ((c : ℂ) * ζ).im = c * ζ.im := by simp [mul_im]
    rw [h1, neg_mul, neg_div, neg_neg]
    have : 0 < normSq ((c : ℂ) * ζ) := normSq_pos.mpr (mul_ne_zero hc' hζ0)
    positivity
  have hγ : (a * z + b) / (c * z + d) = (a : ℂ) / c + w := by
    have := gamma_sub a b c d hdet z (by exact_mod_cast NeZero.ne c) (by exact_mod_cast hζ0)
    push_cast at this
    rw [this, hw, hζ]
  rw [hγ, thetaFn_rat c a w hwim]
  have haq : -2 * I * w * (c : ℂ) ^ 2 = 2 * I * c / ζ := by
    rw [hw]; field_simp
  have hinv := inv_sqrt_aq (c : ℝ) hcr ζ hζim
  push_cast at hinv
  rw [haq, hinv]
  -- the sum
  have had : (a : ZMod c) * (d : ZMod c) = 1 := by
    have : ((a * d - b * c : ℤ) : ZMod c) = 1 := by rw [hdet]; simp
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, sub_zero] at this
    exact this
  set f : ℤ → ℂ := fun n => gaussQ (a : ZMod c) (n : ZMod c) *
    cexp (-π * I * (n : ℂ) ^ 2 / (2 * w * (c : ℂ) ^ 2)) with hf
  have hsupp : Function.support f ⊆ Set.range (fun l : ℤ => 2 * l) := by
    intro n hn
    rcases Int.even_or_odd n with ⟨l, rfl⟩ | ho
    · exact ⟨l, by ring⟩
    · exfalso; apply hn; simp only [hf, gaussQ_odd_eq_zero c hc4 _ n ho, zero_mul]
  have hinj : Function.Injective (fun l : ℤ => 2 * l) := fun x y h => by simpa using h
  have hterm : ∀ l : ℤ, f (2 * l) = gaussQ (a : ZMod c) 0 * cexp (2 * π * I * (l : ℂ) ^ 2 * z) := by
    intro l
    simp only [hf]
    rw [show (((2 * l : ℤ)) : ZMod c) = 2 * (l : ZMod c) by push_cast; ring,
      gaussQ_even c _ _ had,
      show -((d : ZMod c) * (l : ZMod c) ^ 2) = ((-(d * l ^ 2) : ℤ) : ZMod c) by push_cast; ring,
      ZMod.stdAddChar_coe]
    rw [mul_comm (cexp _) (gaussQ _ _), mul_assoc, ← Complex.exp_add]
    congr 2
    rw [hw, hζ]
    field_simp
    push_cast
    ring
  rw [← hinj.tsum_eq hsupp]
  simp only [hterm]
  rw [tsum_mul_left]
  unfold thetaFn
  ring

end ThreeSquares
