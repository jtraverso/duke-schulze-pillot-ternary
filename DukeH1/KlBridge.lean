/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.FourierP
public import DukeH1.KappaFour
public import DukeH1.TSum
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# From the double-coset terms to the sums `T_c`

* `Jk_unit`: for `u ∈ (ℤ/c)ˣ`, `J_k(c, u) = (−2πi)^k n^{k−1} c^{−k} S_k(4π²n²/c²) / ((1+i)√c) ·
  ∑_x e_c(u⁻¹(x² + n) + n u)`;
* `sum_Jk_eq`: `∑_{d₀} J_k(c, d₀) = (−2πi)^k n^{k−1} c^{−k} S_k(4π²n²/c²) T_c(1, n) / ((1+i)√c)`.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares.Poin

open Complex UpperHalfPlane ModularGroup MeasureTheory ThreeSquares.FD ThreeSquares.Mult
  ThreeSquares.Lip Filter Topology Set ZMod

open scoped MatrixGroups Real ComplexConjugate Nat

variable (ℓ : ℕ) (n : ℕ)

/-- The common factor `(−2πi)^k n^{k−1} c^{−k} S_k(4π²n²/c²) / ((1+i)√c)`. -/
noncomputable def cfac (c : ℕ) : ℂ :=
  (-(2 * π * Complex.I)) ^ (kw ℓ : ℂ) * ((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1) *
    ((c : ℝ) : ℂ) ^ (-(kw ℓ : ℂ)) * besS (kw ℓ) (4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n) /
      ((1 + Complex.I) * (Real.sqrt c : ℂ))

theorem gam_rowK_10 (p : ℤ × ℤ) (h : IsCoprime p.1 p.2) : (gam (rowK p h)) 1 0 = p.1 :=
  congrFun (gam_row (rowK p h)) 0

theorem gam_rowK_11 (p : ℤ × ℤ) (h : IsCoprime p.1 p.2) : (gam (rowK p h)) 1 1 = p.2 :=
  congrFun (gam_row (rowK p h)) 1

theorem kcond_unit {Q c : ℕ} [NeZero c] (hc : 0 < c) (hQ : Q ∣ c) (u : (ZMod c)ˣ) :
    KCond Q ((c : ℤ), (((u : ZMod c).val : ℕ) : ℤ)) := by
  refine ⟨show (0 : ℤ) < c by exact_mod_cast hc, show (Q : ℤ) ∣ c by exact_mod_cast hQ,
    show (0 : ℤ) ≤ (((u : ZMod c).val : ℕ) : ℤ) by positivity,
    show (((u : ZMod c).val : ℕ) : ℤ) < c by exact_mod_cast (u : ZMod c).val_lt, ?_⟩
  have := ZMod.val_coe_unit_coprime u
  exact (Nat.isCoprime_iff_coprime.mpr this).symm

theorem Jk_unit {Q c : ℕ} [NeZero c] (hc : 0 < c) (hQ : Q ∣ c) (h4 : 4 ∣ Q) (u : (ZMod c)ˣ) :
    Jk ℓ n Q ((c : ℤ), (((u : ZMod c).val : ℕ) : ℤ)) = cfac ℓ n c *
      ∑ x : ZMod c, (stdAddChar (((u⁻¹ : (ZMod c)ˣ) : ZMod c) * (x ^ 2 + (n : ZMod c)) +
        (n : ZMod c) * (u : ZMod c)) : ℂ) := by
  have hK := kcond_unit hc hQ u
  unfold Jk
  rw [dif_pos hK]
  set p : ℤ × ℤ := ((c : ℤ), (((u : ZMod c).val : ℕ) : ℤ))
  set γ := gam (rowK p hK.2.2.2.2)
  have h10 : γ 1 0 = c := gam_rowK_10 p _
  have h11 : γ 1 1 = ((u : ZMod c).val : ℤ) := gam_rowK_11 p _
  have hdet := det_eq γ
  rw [h10, h11] at hdet
  have hc4 : (4 : ℤ) ∣ (c : ℤ) := by exact_mod_cast dvd_trans h4 hQ
  have hcz : (0 : ℤ) < c := by exact_mod_cast hc
  have hcong : γ 0 0 * ((u : ZMod c).val : ℤ) ≡ 1 [ZMOD (c : ℤ)] :=
    Int.modEq_iff_dvd.mpr ⟨-(γ 0 1), by linear_combination (-1 : ℤ) * hdet⟩
  rw [h10, h11, kap_cube_inv hcz hc4 ⟨_, hcong⟩]
  -- `a ≡ u⁻¹ (mod c)`
  have ha : ((γ 0 0 : ℤ) : ZMod c) = ((u⁻¹ : (ZMod c)ˣ) : ZMod c) := by
    have h1 : ((γ 0 0 : ℤ) : ZMod c) * (u : ZMod c) = 1 := by
      have := (ZMod.intCast_eq_intCast_iff _ _ c).mpr hcong
      push_cast at this
      rwa [ZMod.natCast_zmod_val] at this
    calc ((γ 0 0 : ℤ) : ZMod c) = ((γ 0 0 : ℤ) : ZMod c) * (u : ZMod c) *
          ((u⁻¹ : (ZMod c)ˣ) : ZMod c) := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  -- `κ(a, c) = G(u⁻¹)/((1+i)√c)`
  have hkap : kap (γ 0 0) (c : ℤ) =
      gaussQ (((u⁻¹ : (ZMod c)ˣ) : ZMod c)) 0 / ((1 + Complex.I) * (Real.sqrt c : ℂ)) := by
    unfold kap
    rw [dif_pos hcz]
    simp only [Int.toNat_natCast]
    rw [ha]
  -- the exponential
  set v : ZMod c := ((u⁻¹ : (ZMod c)ˣ) : ZMod c)
  have hexp : cexp (2 * π * Complex.I * n * (((γ 0 0 : ℂ) + (((u : ZMod c).val : ℕ) : ℤ)) /
      (((c : ℕ) : ℤ) : ℂ))) =
      stdAddChar ((n : ZMod c) * (v + (u : ZMod c))) := by
    have e1 : (n : ZMod c) * (v + (u : ZMod c)) =
        (((n : ℤ) * (γ 0 0 + (((u : ZMod c).val : ℕ) : ℤ)) : ℤ) : ZMod c) := by
      push_cast; rw [ha, ZMod.natCast_zmod_val]
    rw [e1, ZMod.stdAddChar_coe]
    congr 1; push_cast; ring
  have hs : ∑ x : ZMod c, (stdAddChar (v * (x ^ 2 + (n : ZMod c)) + (n : ZMod c) * (u : ZMod c)) : ℂ) =
      gaussQ v 0 * stdAddChar ((n : ZMod c) * (v + (u : ZMod c))) := by
    unfold gaussQ
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← AddChar.map_add_eq_mul]; congr 1; ring
  rw [hkap, hexp, hs]
  unfold cfac
  simp only [Int.cast_natCast]
  ring

/-! ### The sum over `d₀` -/

/-- `T_c(1, n)`, set to `0` for `c = 0`. -/
noncomputable def Tc (c : ℕ) : ℂ := if h : 0 < c then (haveI : NeZero c := ⟨h.ne'⟩; Tq c 1 n) else 0

theorem exists_unit_of_kcond {Q c : ℕ} [NeZero c] {d₀ : ℤ} (h : KCond Q ((c : ℤ), d₀)) :
    ∃ u : (ZMod c)ˣ, (((u : ZMod c).val : ℕ) : ℤ) = d₀ := by
  obtain ⟨-, -, h0, hlt, hcop⟩ := h
  simp only at h0 hlt hcop
  have hz : IsUnit ((d₀ : ℤ) : ZMod c) := by
    rw [show ((d₀ : ℤ) : ZMod c) = ((d₀.toNat : ℕ) : ZMod c) by
      rw [← Int.toNat_of_nonneg h0]; push_cast; rw [Int.toNat_of_nonneg h0]]
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    have : IsCoprime ((d₀.toNat : ℕ) : ℤ) (c : ℤ) := by
      rw [Int.toNat_of_nonneg h0]; exact hcop.symm
    exact Nat.isCoprime_iff_coprime.mp this
  refine ⟨hz.unit, ?_⟩
  rw [IsUnit.unit_spec, ZMod.val_intCast, Int.emod_eq_of_lt h0 hlt]

theorem tsum_Jk_c {Q c : ℕ} [NeZero c] (hc : 0 < c) (hQ : Q ∣ c) (h4 : 4 ∣ Q) :
    ∑' d₀ : ℤ, Jk ℓ n Q ((c : ℤ), d₀) = cfac ℓ n c * Tc n c := by
  classical
  set s : Finset ℤ := Finset.univ.image (fun u : (ZMod c)ˣ => (((u : ZMod c).val : ℕ) : ℤ))
  have hinj : Function.Injective (fun u : (ZMod c)ˣ => (((u : ZMod c).val : ℕ) : ℤ)) := by
    intro u v h
    simp only [Nat.cast_inj] at h
    exact Units.ext (ZMod.val_injective c h)
  rw [tsum_eq_sum (s := s) fun d₀ hd₀ => ?_]
  · rw [Finset.sum_image fun u _ v _ h => hinj h]
    simp_rw [Jk_unit ℓ n hc hQ h4]
    rw [← Finset.mul_sum, Tc, dif_pos hc]
    congr 1
    unfold Tq
    simp only [one_mul]
  · unfold Jk
    rw [dif_neg]
    intro hK
    obtain ⟨u, hu⟩ := exists_unit_of_kcond hK
    exact hd₀ (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, hu⟩)

theorem Jk_eq_zero_of_not {Q : ℕ} {c : ℤ} (hc : ¬ (0 < c ∧ (Q : ℤ) ∣ c)) (d₀ : ℤ) :
    Jk ℓ n Q (c, d₀) = 0 := by
  unfold Jk
  rw [dif_neg]
  rintro ⟨h1, h2, -⟩
  exact hc ⟨h1, h2⟩

/-! ### Bounds for summability -/

theorem besS_norm_le {k : ℝ} (hk : 2 ≤ k) {X : ℝ} (hX : 0 ≤ X) : ‖besS k X‖ ≤ Real.exp X := by
  have hterm : ∀ j : ℕ, ‖(-(X : ℂ)) ^ j / ((j ! : ℂ) * Gamma (k + j))‖ ≤ X ^ j / (j ! : ℝ) := by
    intro j
    have hG : 1 ≤ Real.Gamma (k + j) := by
      rw [← Real.Gamma_two]
      exact Real.Gamma_strictMonoOn_Ici.monotoneOn (by simp) (by
        simp only [Set.mem_Ici]; have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith) (by
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    rw [show (k : ℂ) + j = ((k + j : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal, norm_div,
      norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX,
      Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hf : (0 : ℝ) < j ! := by exact_mod_cast Nat.factorial_pos j
    rw [div_le_div_iff₀ (by positivity) hf]
    have : 0 ≤ X ^ j * (j ! : ℝ) := by positivity
    nlinarith
  have hs : Summable fun j : ℕ => X ^ j / (j ! : ℝ) := Real.summable_pow_div_factorial X
  have hsn : Summable fun j : ℕ => ‖(-(X : ℂ)) ^ j / ((j ! : ℂ) * Gamma (k + j))‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hterm hs
  calc ‖besS k X‖ ≤ ∑' j : ℕ, ‖(-(X : ℂ)) ^ j / ((j ! : ℂ) * Gamma (k + j))‖ :=
        norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' j : ℕ, X ^ j / (j ! : ℝ) := hsn.tsum_le_tsum hterm hs
    _ = Real.exp X := by
        rw [Real.exp_eq_exp_ℝ]
        exact (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) X).tsum_eq

/-- The constant `A = |(−2πi)^k| |n^{k−1}| e^{4π²n²}`. -/
noncomputable def cA : ℝ :=
  ‖(-(2 * π * Complex.I)) ^ (kw ℓ : ℂ)‖ * ‖((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1)‖ *
    Real.exp (4 * π ^ 2 * n ^ 2)

theorem cA_nonneg : 0 ≤ cA ℓ n := by unfold cA; positivity

theorem norm_cfac_le (hℓ : 1 ≤ ℓ) {c : ℕ} (hc : 0 < c) :
    ‖cfac ℓ n c‖ ≤ cA ℓ n * (c : ℝ) ^ (-(kw ℓ) - 1 / 2) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hk2 : 2 ≤ kw ℓ := by
    unfold kw; have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hX : (0 : ℝ) ≤ 4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n := by positivity
  have hX' : 4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n ≤ 4 * π ^ 2 * n ^ 2 := by
    have h1 : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ c := by exact_mod_cast hc
      nlinarith
    have h2 : (n : ℝ) / (c : ℝ) ^ 2 ≤ n := div_le_self (Nat.cast_nonneg n) h1
    have hpi : 0 ≤ 4 * π ^ 2 * (n : ℝ) := by positivity
    calc 4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n = (4 * π ^ 2 * n) * ((n : ℝ) / (c : ℝ) ^ 2) := by
          ring
      _ ≤ (4 * π ^ 2 * n) * n := mul_le_mul_of_nonneg_left h2 hpi
      _ = 4 * π ^ 2 * n ^ 2 := by ring
  have hb := besS_norm_le hk2 hX
  have hb' : ‖besS (kw ℓ) ((4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n : ℝ) : ℂ)‖ ≤
      Real.exp (4 * π ^ 2 * n ^ 2) := hb.trans (Real.exp_le_exp.mpr hX')
  have h1i : (1 : ℝ) ≤ ‖(1 + Complex.I : ℂ)‖ := by
    rw [Complex.norm_def, Complex.normSq_apply]; simp
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.mpr hcR
  unfold cfac cA
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsq, Complex.norm_cpow_eq_rpow_re_of_pos hcR]
  simp only [Complex.neg_re, Complex.ofReal_re]
  have hcs : (c : ℝ) ^ (-(kw ℓ) - 1 / 2) = (c : ℝ) ^ (-(kw ℓ)) / Real.sqrt c := by
    rw [Real.rpow_sub hcR, Real.sqrt_eq_rpow]
  rw [hcs]
  have e : (4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n : ℂ) =
      ((4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  rw [div_le_iff₀ (by positivity)]
  calc ‖(-(2 * π * Complex.I)) ^ (kw ℓ : ℂ)‖ * ‖((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1)‖ *
        (c : ℝ) ^ (-kw ℓ) * ‖besS (kw ℓ) ((4 * π ^ 2 * ((n : ℝ) / (c : ℝ) ^ 2) * n : ℝ) : ℂ)‖
      ≤ ‖(-(2 * π * Complex.I)) ^ (kw ℓ : ℂ)‖ * ‖((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1)‖ *
        (c : ℝ) ^ (-kw ℓ) * Real.exp (4 * π ^ 2 * n ^ 2) := by gcongr
    _ ≤ ‖(-(2 * π * Complex.I)) ^ (kw ℓ : ℂ)‖ * ‖((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1)‖ *
          Real.exp (4 * π ^ 2 * n ^ 2) * ((c : ℝ) ^ (-kw ℓ) / Real.sqrt c) *
          (‖(1 + Complex.I : ℂ)‖ * Real.sqrt c) := by
        rw [show ‖(-(2 * π * Complex.I)) ^ (kw ℓ : ℂ)‖ * ‖((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1)‖ *
          Real.exp (4 * π ^ 2 * n ^ 2) * ((c : ℝ) ^ (-kw ℓ) / Real.sqrt c) *
          (‖(1 + Complex.I : ℂ)‖ * Real.sqrt c) = ‖(-(2 * π * Complex.I)) ^ (kw ℓ : ℂ)‖ *
          ‖((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1)‖ * (c : ℝ) ^ (-kw ℓ) * Real.exp (4 * π ^ 2 * n ^ 2) *
          ‖(1 + Complex.I : ℂ)‖ by field_simp]
        exact le_mul_of_one_le_right (by positivity) h1i

theorem norm_Jk_le (hℓ : 1 ≤ ℓ) {Q : ℕ} (hQ4 : 4 ∣ Q) (p : ℤ × ℤ) :
    ‖Jk ℓ n Q p‖ ≤ {p : ℤ × ℤ | KCond Q p}.indicator
      (fun p => cA ℓ n * ((p.1 : ℝ)) ^ ((1 : ℝ) / 2 - kw ℓ)) p := by
  classical
  by_cases hK : KCond Q p
  · rw [Set.indicator_of_mem (show p ∈ {p : ℤ × ℤ | KCond Q p} from hK)]
    obtain ⟨c, d₀⟩ := p
    have hc : 0 < c := hK.1
    lift c to ℕ using hc.le
    have hc' : 0 < c := by exact_mod_cast hc
    haveI : NeZero c := ⟨hc'.ne'⟩
    obtain ⟨u, rfl⟩ := exists_unit_of_kcond hK
    have hQc : Q ∣ c := by have := hK.2.1; simp only at this; exact_mod_cast this
    rw [Jk_unit ℓ n hc' hQc hQ4]
    have hs : ‖∑ x : ZMod c, (stdAddChar (((u⁻¹ : (ZMod c)ˣ) : ZMod c) * (x ^ 2 + (n : ZMod c)) +
        (n : ZMod c) * (u : ZMod c)) : ℂ)‖ ≤ c := by
      refine (norm_sum_le _ _).trans ?_
      simp only [AddChar.norm_apply, ZMod.stdAddChar_apply, Circle.norm_coe, Finset.sum_const,
        Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one, le_refl]
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc'
    rw [norm_mul]
    calc ‖cfac ℓ n c‖ * ‖_‖ ≤ (cA ℓ n * (c : ℝ) ^ (-(kw ℓ) - 1 / 2)) * c :=
          mul_le_mul (norm_cfac_le ℓ n hℓ hc') hs (norm_nonneg _) (by
            have := cA_nonneg ℓ n; positivity)
      _ = cA ℓ n * ((c : ℤ) : ℝ) ^ ((1 : ℝ) / 2 - kw ℓ) := by
          rw [Int.cast_natCast, mul_assoc, show (c : ℝ) ^ (-(kw ℓ) - 1 / 2) * c =
            (c : ℝ) ^ ((1 : ℝ) / 2 - kw ℓ) by
              rw [show (1 : ℝ) / 2 - kw ℓ = (-(kw ℓ) - 1 / 2) + 1 by ring,
                Real.rpow_add hcR, Real.rpow_one]]
  · rw [Set.indicator_of_notMem (show p ∉ {p : ℤ × ℤ | KCond Q p} from hK)]
    unfold Jk
    rw [dif_neg hK, norm_zero]

theorem summable_Jk (hℓ : 2 ≤ ℓ) {Q : ℕ} (hQ4 : 4 ∣ Q) : Summable (Jk ℓ n Q) := by
  classical
  set g : ℤ × ℤ → ℝ := {p : ℤ × ℤ | KCond Q p}.indicator
    (fun p => cA ℓ n * ((p.1 : ℝ)) ^ ((1 : ℝ) / 2 - kw ℓ))
  have hk : (5 : ℝ) / 2 < kw ℓ := by
    unfold kw; have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hg0 : 0 ≤ g := fun p => by
    simp only [g]; apply Set.indicator_nonneg; intro p hp
    have : (0 : ℝ) < p.1 := by exact_mod_cast hp.1
    have := cA_nonneg ℓ n; positivity
  have hfin : ∀ c : ℤ, ∀ d₀ ∉ Finset.Ico (0 : ℤ) c, g (c, d₀) = 0 := by
    intro c d₀ hd
    refine Set.indicator_of_notMem (fun hK => hd ?_) _
    exact Finset.mem_Ico.mpr ⟨hK.2.2.1, hK.2.2.2.1⟩
  have hg : Summable g := by
    refine (summable_prod_of_nonneg hg0).mpr ⟨fun c => summable_of_ne_finset_zero (hfin c), ?_⟩
    refine Summable.of_nonneg_of_le (fun c => tsum_nonneg fun d => hg0 _) (fun c => ?_)
      ((Real.summable_abs_int_rpow (b := kw ℓ - 3 / 2) (by linarith)).mul_left (cA ℓ n))
    rw [tsum_eq_sum (s := Finset.Ico (0 : ℤ) c) fun d hd => hfin c d hd]
    by_cases hc : 0 < c
    · have hcR : (0 : ℝ) < c := by exact_mod_cast hc
      calc ∑ d ∈ Finset.Ico (0 : ℤ) c, g (c, d) ≤ ∑ _d ∈ Finset.Ico (0 : ℤ) c,
            cA ℓ n * ((c : ℝ)) ^ ((1 : ℝ) / 2 - kw ℓ) := by
            refine Finset.sum_le_sum fun d _ => ?_
            simp only [g]
            by_cases hK : (c, d) ∈ {p : ℤ × ℤ | KCond Q p}
            · rw [Set.indicator_of_mem hK]
            · rw [Set.indicator_of_notMem hK]; have := cA_nonneg ℓ n; positivity
        _ = (c.toNat : ℝ) * (cA ℓ n * ((c : ℝ)) ^ ((1 : ℝ) / 2 - kw ℓ)) := by
            rw [Finset.sum_const, Int.card_Ico, sub_zero, nsmul_eq_mul]
        _ = cA ℓ n * |(c : ℝ)| ^ (-(kw ℓ - 3 / 2)) := by
            rw [abs_of_pos hcR, show (c.toNat : ℝ) = (c : ℝ) by
              rw [show ((c.toNat : ℕ) : ℝ) = (((c.toNat : ℕ) : ℤ) : ℝ) by push_cast; rfl,
                Int.toNat_of_nonneg hc.le]]
            rw [show (c : ℝ) * (cA ℓ n * (c : ℝ) ^ ((1 : ℝ) / 2 - kw ℓ)) =
              cA ℓ n * ((c : ℝ) ^ (1 : ℝ) * (c : ℝ) ^ ((1 : ℝ) / 2 - kw ℓ)) by rw [Real.rpow_one]; ring,
              ← Real.rpow_add hcR]
            congr 2; ring
    · rw [show Finset.Ico (0 : ℤ) c = ∅ by ext; simp; omega, Finset.sum_empty]
      have := cA_nonneg ℓ n; positivity
  exact Summable.of_norm_bounded hg fun p => norm_Jk_le ℓ n (by omega) hQ4 p

/-- **`P̂_Q(n) = 2 + 2 ∑_{c > 0, Q ∣ c} c_k(c) T_c(1, n)`.** -/
theorem Phat_eq (hℓ : 2 ≤ ℓ) {Q : ℕ} (hQ4 : 4 ∣ Q) :
    Phat ℓ n Q = 2 + 2 * ∑' c : ℕ, (if 0 < c ∧ Q ∣ c then cfac ℓ n c * Tc n c else 0) := by
  classical
  unfold Phat
  congr 2
  rw [(summable_Jk ℓ n hℓ hQ4).tsum_prod]
  set F : ℕ → ℂ := fun c => if 0 < c ∧ Q ∣ c then cfac ℓ n c * Tc n c else 0
  have hF : ∀ c : ℤ, ∑' d₀ : ℤ, Jk ℓ n Q (c, d₀) =
      Function.extend (fun m : ℕ => (m : ℤ)) F 0 c := by
    intro c
    by_cases hc : 0 < c ∧ (Q : ℤ) ∣ c
    · obtain ⟨hc0, hQc⟩ := hc
      lift c to ℕ using hc0.le
      have hc' : 0 < c := by exact_mod_cast hc0
      haveI : NeZero c := ⟨hc'.ne'⟩
      rw [Function.Injective.extend_apply Nat.cast_injective, tsum_Jk_c ℓ n hc'
        (by exact_mod_cast hQc) hQ4]
      simp only [F, if_pos (show 0 < c ∧ Q ∣ c from ⟨hc', by exact_mod_cast hQc⟩)]
    · rw [tsum_congr (Jk_eq_zero_of_not ℓ n hc), tsum_zero]
      by_cases hr : ∃ m : ℕ, (m : ℤ) = c
      · obtain ⟨m, rfl⟩ := hr
        rw [Function.Injective.extend_apply Nat.cast_injective]
        simp only [F]
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact hc ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      · rw [Function.extend_apply' _ _ _ (by simpa using hr)]; rfl
  rw [tsum_congr hF, ← Function.Injective.tsum_eq Nat.cast_injective (f := Function.extend
    (fun m : ℕ => (m : ℤ)) F 0) (fun c hc => by
      by_contra h
      exact hc (Function.extend_apply' _ _ _ (by simpa using h)))]
  refine tsum_congr fun c => ?_
  rw [Function.Injective.extend_apply Nat.cast_injective]

end ThreeSquares.Poin
