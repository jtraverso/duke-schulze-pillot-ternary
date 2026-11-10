/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.Mult
public import DukeH1.Level

/-!
# Poincaré series of half-integral weight

Fix `k > 2` and `n ≥ 1`. Put `ψ₀(t) = t^{k/2} e^{−2πnt}`.

* `Estar k n z = ∑_{coprime rows r} ψ₀(Im γ_r z)` is `SL(2, ℤ)`-invariant (`Estar_smul`) and bounded on
  the fundamental domain, hence on `ℍ` (`Estar_bdd`).
* The Poincaré series `poin ℓ Q n z = ∑_{r : Q ∣ r₀} j_k(γ_r, z)⁻¹ e(n γ_r z)` (level `Q`, `4 ∣ Q`,
  weight `k = 3/2 + ℓ`) converges absolutely, with `(Im z)^{k/2} |P(z)| ≤ M` (`norm_poin_le`).
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares.Poin

open Complex UpperHalfPlane ModularGroup MeasureTheory ThreeSquares.FD ThreeSquares.Mult

open scoped MatrixGroups Real

/-! ### An elementary bound -/

theorem rpow_mul_exp_neg_le' {α a t : ℝ} (hα : 0 < α) (ha : 0 < a) (ht : 0 < t) :
    t ^ α * Real.exp (-(a * t)) ≤ (α / a) ^ α * Real.exp (-α) := by
  rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos (by positivity), ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hx : 0 < t * a / α := by positivity
  have hl := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div (by positivity) hα.ne', Real.log_mul ht.ne' ha.ne'] at hl
  rw [Real.log_div hα.ne' ha.ne']
  have : α * (t * a / α - 1) = a * t - α := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hl hα.le]

/-! ### The auxiliary Eisenstein series -/

/-- `ψ₀(t) = t^{k/2} e^{−2πnt}`. -/
noncomputable def psi0 (k : ℝ) (n : ℕ) (t : ℝ) : ℝ := t ^ (k / 2) * Real.exp (-(2 * π * n * t))

theorem psi0_nonneg (k : ℝ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ psi0 k n t := by
  unfold psi0; positivity

/-- `ψ₀ ≤ B₀`. -/
theorem psi0_le_B0 {k : ℝ} (hk : 0 < k) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    psi0 k n t ≤ (k / 2 / (2 * π * n)) ^ (k / 2) * Real.exp (-(k / 2)) := by
  unfold psi0
  have := rpow_mul_exp_neg_le' (α := k / 2) (a := 2 * π * n) (t := t) (by positivity)
    (by positivity) ht
  rwa [show 2 * π * n * t = 2 * π * n * t from rfl] at this

/-- `ψ₀(t) ≤ C_σ t^σ` for `σ < k/2`. -/
theorem psi0_le_rpow {k σ : ℝ} (hσ : σ < k / 2) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    psi0 k n t ≤ ((k / 2 - σ) / (2 * π * n)) ^ (k / 2 - σ) * Real.exp (-(k / 2 - σ)) * t ^ σ := by
  unfold psi0
  have h := rpow_mul_exp_neg_le' (α := k / 2 - σ) (a := 2 * π * n) (t := t) (by linarith)
    (by positivity) ht
  have e : t ^ (k / 2) = t ^ (k / 2 - σ) * t ^ σ := by
    rw [← Real.rpow_add ht]; ring_nf
  rw [e]
  calc t ^ (k / 2 - σ) * t ^ σ * Real.exp (-(2 * π * n * t))
      = (t ^ (k / 2 - σ) * Real.exp (-(2 * π * n * t))) * t ^ σ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)

/-- The `T`-periodic function `w ↦ ψ₀(Im w)` with values in `ℝ≥0∞`. -/
noncomputable def psiE (k : ℝ) (n : ℕ) (w : ℍ) : ENNReal := ENNReal.ofReal (psi0 k n w.im)

theorem psiE_T (k : ℝ) (n : ℕ) (w : ℍ) : psiE k n (T • w) = psiE k n w := by
  unfold psiE; congr 2
  rw [show (T • w).im = w.im by
    rw [show T • w = ((1 : ℤ) : ℝ) +ᵥ w by simpa using modular_T_smul w]; simp]

/-- `E*(z) = ∑_r ψ₀(Im γ_r z)`. -/
noncomputable def Estar (k : ℝ) (n : ℕ) (z : ℍ) : ENNReal := ∑' r : Rows, psiE k n (gam r • z)

/-- Right multiplication permutes the coprime rows. -/
noncomputable def rowMap (g : SL(2, ℤ)) : Rows ≃ Rows where
  toFun r := rowOf (gam r * g)
  invFun r := rowOf (gam r * g⁻¹)
  left_inv r := by
    obtain ⟨m, hm⟩ := eq_T_mul_gam (gam r * g)
    have h2 : gam (rowOf (gam r * g)) = T ^ (-m) * (gam r * g) := by
      conv_rhs => rw [hm]
      group
    simp only
    rw [h2, show T ^ (-m) * (gam r * g) * g⁻¹ = T ^ (-m) * gam r by group, row_T_mul]
  right_inv r := by
    obtain ⟨m, hm⟩ := eq_T_mul_gam (gam r * g⁻¹)
    have h2 : gam (rowOf (gam r * g⁻¹)) = T ^ (-m) * (gam r * g⁻¹) := by
      conv_rhs => rw [hm]
      group
    simp only
    rw [h2, show T ^ (-m) * (gam r * g⁻¹) * g = T ^ (-m) * gam r by group, row_T_mul]

theorem Estar_smul (k : ℝ) (n : ℕ) (g : SL(2, ℤ)) (z : ℍ) : Estar k n (g • z) = Estar k n z := by
  unfold Estar
  conv_rhs => rw [← (rowMap g).tsum_eq]
  refine tsum_congr fun r => ?_
  rw [← mul_smul, psi_eq_gam (psiE_T k n)]
  rfl

/-! ### The bound on the fundamental domain -/

theorem im_gam_smul (r : Rows) (z : ℍ) :
    (gam r • z).im = z.im / normSq ((r.1 0 : ℂ) * z + r.1 1) := by
  rw [ModularGroup.im_smul_eq_div_normSq, denom_apply]
  have h0 : (gam r) 1 0 = r.1 0 := congrFun (gam_row r) 0
  have h1 : (gam r) 1 1 = r.1 1 := congrFun (gam_row r) 1
  simp [h0, h1]

theorem normSq_lin (c d : ℤ) (z : ℍ) :
    normSq ((c : ℂ) * z + d) = (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
  rw [Complex.normSq_apply]; simp; ring

/-- On `𝒟`: `|c| · max(1,|d|) · y ≤ √2 · |cz + d|²` for `c ≠ 0`. -/
theorem key_fd {z : ℍ} (hz : z ∈ fd) {c d : ℤ} (hc : c ≠ 0) :
    |(c : ℝ)| * max 1 |(d : ℝ)| * z.im ≤ Real.sqrt 2 * normSq ((c : ℂ) * z + d) := by
  obtain ⟨hn, hre⟩ := hz
  rw [normSq_lin]
  set x := z.re; set y := z.im
  have hy : 0 < y := z.im_pos
  have hn' : 1 ≤ x ^ 2 + y ^ 2 := by
    rw [Complex.normSq_apply] at hn; simpa [sq] using hn
  have hx : 4 * x ^ 2 ≤ 1 := by
    have := abs_le.mp hre; nlinarith
  have hc1 : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ c ^ 2 := by
      have := sq_pos_of_ne_zero hc; omega
    exact_mod_cast this
  set N := (c * x + d) ^ 2 + (c * y) ^ 2
  have hN1 : (c * y) ^ 2 ≤ N := by simp only [N]; nlinarith [sq_nonneg ((c:ℝ) * x + d)]
  have hN2 : (max 1 |(d : ℝ)|) ^ 2 / 2 ≤ N := by
    have base : ((c : ℝ) ^ 2 + (d : ℝ) ^ 2) / 2 ≤ N := by
      simp only [N]
      nlinarith [sq_nonneg ((c : ℝ) + 2 * x * d), mul_nonneg (sq_nonneg (d : ℝ))
        (by linarith : (0 : ℝ) ≤ 1 - 4 * x ^ 2), mul_nonneg (sq_nonneg (c : ℝ))
        (by linarith : (0 : ℝ) ≤ x ^ 2 + y ^ 2 - 1)]
    rcases le_total 1 |(d : ℝ)| with h | h
    · rw [max_eq_right h, sq_abs]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have hN0 : 0 ≤ N := le_trans (sq_nonneg _) hN1
  have hlhs : 0 ≤ |(c : ℝ)| * max 1 |(d : ℝ)| * y := by positivity
  rw [← Real.sqrt_sq hlhs, ← Real.sqrt_sq hN0, ← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  have e : (|(c : ℝ)| * max 1 |(d : ℝ)| * y) ^ 2 = (c * y) ^ 2 * (max 1 |(d : ℝ)|) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, sq_abs]; ring
  rw [e]
  have hm : 0 ≤ (max 1 |(d : ℝ)|) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul hN1 hN2 (by positivity) hN0]

/-- The weights `u(c) = max(1,|c|)^{−σ}`. -/
noncomputable def wt (σ : ℝ) (c : ℤ) : ℝ := (max 1 |(c : ℝ)|) ^ (-σ)

theorem wt_pos (σ : ℝ) (c : ℤ) : 0 < wt σ c := by unfold wt; positivity

theorem tsum_wt_lt_top {σ : ℝ} (hσ : 1 < σ) : ∑' c : ℤ, ENNReal.ofReal (wt σ c) < ⊤ := by
  have hle : ∀ c : ℤ, ENNReal.ofReal (wt σ c) ≤
      ENNReal.ofReal (|(c : ℝ)| ^ (-σ)) + (if c = 0 then 1 else 0) := by
    intro c
    by_cases h : c = 0
    · subst h; simp [wt]
    · have h1 : 1 ≤ |(c : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
      simp [wt, h, max_eq_right h1]
  calc _ ≤ ∑' c : ℤ, (ENNReal.ofReal (|(c : ℝ)| ^ (-σ)) + (if c = 0 then 1 else 0)) :=
        ENNReal.tsum_le_tsum hle
    _ = ∑' c : ℤ, ENNReal.ofReal (|(c : ℝ)| ^ (-σ)) + 1 := by
        rw [ENNReal.tsum_add, tsum_ite_eq]
    _ < ⊤ := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun c => by positivity)
          (Real.summable_abs_int_rpow hσ)]
        exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.one_lt_top⟩

theorem psiE_le_fd {k σ : ℝ} (hk : 0 < k) (hσ0 : 0 < σ) (hσ : σ < k / 2) {n : ℕ} (hn : 0 < n)
    {z : ℍ} (hz : z ∈ fd) (r : Rows) :
    psiE k n (gam r • z) ≤ ENNReal.ofReal (((k / 2 / (2 * π * n)) ^ (k / 2) * Real.exp (-(k / 2)) +
      ((k / 2 - σ) / (2 * π * n)) ^ (k / 2 - σ) * Real.exp (-(k / 2 - σ)) * Real.sqrt 2 ^ σ) *
        (wt σ (r.1 0) * wt σ (r.1 1))) := by
  set B0 := (k / 2 / (2 * π * n)) ^ (k / 2) * Real.exp (-(k / 2))
  set Cσ := ((k / 2 - σ) / (2 * π * n)) ^ (k / 2 - σ) * Real.exp (-(k / 2 - σ))
  have hB0 : 0 ≤ B0 := by positivity
  have hCσ : 0 ≤ Cσ := by positivity
  apply ENNReal.ofReal_le_ofReal
  have him := (gam r • z).im_pos
  by_cases hc : r.1 0 = 0
  · -- `c = 0`, so `d = ±1`
    have hd : r.1 1 = 1 ∨ r.1 1 = -1 := by
      have hu := r.2
      rw [hc] at hu
      exact Int.isUnit_iff.mp (isCoprime_zero_left.mp hu)
    have hw : wt σ (r.1 0) * wt σ (r.1 1) = 1 := by
      rcases hd with h | h <;> simp [wt, hc, h]
    rw [hw, mul_one]
    calc psi0 k n (gam r • z).im ≤ B0 := psi0_le_B0 hk hn him
      _ ≤ B0 + Cσ * Real.sqrt 2 ^ σ := le_add_of_nonneg_right (by positivity)
  · have hkey := key_fd hz (d := r.1 1) hc
    have hN : 0 < normSq ((r.1 0 : ℂ) * z + r.1 1) := by
      have := im_gam_smul r z
      by_contra h
      push_neg at h
      have h0 : normSq ((r.1 0 : ℂ) * z + r.1 1) = 0 := le_antisymm h (normSq_nonneg _)
      rw [h0, div_zero] at this
      linarith
    have hc1 : 1 ≤ |(r.1 0 : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hc
    have hm1 : 1 ≤ max 1 |(r.1 1 : ℝ)| := le_max_left _ _
    -- `Im(γz) ≤ √2 / (|c| m)`
    have hIm : (gam r • z).im ≤ Real.sqrt 2 / (|(r.1 0 : ℝ)| * max 1 |(r.1 1 : ℝ)|) := by
      rw [im_gam_smul, div_le_div_iff₀ hN (by positivity)]
      linarith
    have hpow : (gam r • z).im ^ σ ≤ Real.sqrt 2 ^ σ * (wt σ (r.1 0) * wt σ (r.1 1)) := by
      calc (gam r • z).im ^ σ ≤ (Real.sqrt 2 / (|(r.1 0 : ℝ)| * max 1 |(r.1 1 : ℝ)|)) ^ σ :=
            Real.rpow_le_rpow him.le hIm hσ0.le
        _ = Real.sqrt 2 ^ σ * (wt σ (r.1 0) * wt σ (r.1 1)) := by
            unfold wt
            rw [max_eq_right hc1, Real.div_rpow (by positivity) (by positivity),
              Real.mul_rpow (by positivity) (by positivity), div_eq_mul_inv,
              Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), mul_inv]
    calc psi0 k n (gam r • z).im ≤ Cσ * (gam r • z).im ^ σ := psi0_le_rpow hσ hn him
      _ ≤ Cσ * (Real.sqrt 2 ^ σ * (wt σ (r.1 0) * wt σ (r.1 1))) :=
          mul_le_mul_of_nonneg_left hpow hCσ
      _ ≤ (B0 + Cσ * Real.sqrt 2 ^ σ) * (wt σ (r.1 0) * wt σ (r.1 1)) := by
          have := mul_pos (wt_pos σ (r.1 0)) (wt_pos σ (r.1 1))
          nlinarith

/-- **`E*` is bounded on `ℍ`** (for `k > 2`). -/
theorem Estar_bdd {k : ℝ} (hk : 2 < k) {n : ℕ} (hn : 0 < n) :
    ∃ M : ENNReal, M < ⊤ ∧ ∀ z : ℍ, Estar k n z ≤ M := by
  set σ := 1 / 2 + k / 4
  have hσ1 : 1 < σ := by simp only [σ]; linarith
  have hσk : σ < k / 2 := by simp only [σ]; linarith
  set K := (k / 2 / (2 * π * n)) ^ (k / 2) * Real.exp (-(k / 2)) +
      ((k / 2 - σ) / (2 * π * n)) ^ (k / 2 - σ) * Real.exp (-(k / 2 - σ)) * Real.sqrt 2 ^ σ
  have hK : 0 ≤ K := by positivity
  set M := ENNReal.ofReal K * ((∑' c : ℤ, ENNReal.ofReal (wt σ c)) *
    ∑' d : ℤ, ENNReal.ofReal (wt σ d))
  refine ⟨M, ?_, fun z => ?_⟩
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (tsum_wt_lt_top hσ1) (tsum_wt_lt_top hσ1))
  obtain ⟨g, hg⟩ := exists_smul_mem_fd z
  rw [← Estar_smul k n g z]
  unfold Estar
  calc ∑' r : Rows, psiE k n (gam r • g • z)
      ≤ ∑' r : Rows, ENNReal.ofReal (K * (wt σ (r.1 0) * wt σ (r.1 1))) :=
        ENNReal.tsum_le_tsum fun r =>
          psiE_le_fd (by linarith) (by linarith) hσk hn hg r
    _ ≤ ∑' p : ℤ × ℤ, ENNReal.ofReal (K * (wt σ p.1 * wt σ p.2)) := by
        refine (ENNReal.tsum_comp_le_tsum_of_injective (f := fun r : Rows => (r.1 0, r.1 1))
          ?_ (fun p : ℤ × ℤ => ENNReal.ofReal (K * (wt σ p.1 * wt σ p.2))))
        intro r s h
        simp only [Prod.mk.injEq] at h
        apply Subtype.ext
        ext i; fin_cases i
        · exact h.1
        · exact h.2
    _ = M := by
        simp only [M]
        rw [ENNReal.tsum_prod (f := fun (a b : ℤ) => ENNReal.ofReal (K * (wt σ a * wt σ b)))]
        simp_rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_mul (wt_pos σ _).le, ENNReal.tsum_mul_left,
          ENNReal.tsum_mul_right]

/-! ### The Poincaré series -/

theorem mob_eq (γ : SL(2, ℤ)) (z : ℍ) : mob γ z = ((γ • z : ℍ) : ℂ) := by
  rw [coe_specialLinearGroup_apply]; simp [mob]

theorem den_eq (γ : SL(2, ℤ)) (z : ℍ) : den γ z = denom γ z := by
  rw [denom_apply]; simp [den]

variable (ℓ : ℕ) (Q n : ℕ)

/-- The weight `k = 3/2 + ℓ`. -/
noncomputable def kw : ℝ := 3 / 2 + ℓ

/-- `φ_γ(z) = j_k(γ, z)⁻¹ e(n γz)`. -/
noncomputable def phi (γ : SL(2, ℤ)) (z : ℂ) : ℂ := (jk ℓ γ z)⁻¹ * cexp (2 * π * Complex.I * n * mob γ z)

/-- The Poincaré series of level `Q`. -/
noncomputable def poin (z : ℂ) : ℂ := ∑' r : RowsQ Q, phi ℓ n (gam r.1) z

theorem norm_cexp_n (w : ℂ) : ‖cexp (2 * π * Complex.I * n * w)‖ = Real.exp (-(2 * π * n * w.im)) := by
  rw [Complex.norm_exp]; congr 1; simp

/-- `|φ_γ(z)| (Im z)^{k/2} = ψ₀(Im γz)`. -/
theorem norm_phi (γ : SL(2, ℤ)) (h4 : (4 : ℤ) ∣ γ 1 0) (z : ℍ) :
    ‖phi ℓ n γ z‖ * z.im ^ (kw ℓ / 2) = psi0 (kw ℓ) n (γ • z).im := by
  have hz := z.im_pos
  have hd := den_ne_zero γ hz
  have hD : 0 < ‖den γ z‖ := norm_pos_iff.mpr hd
  have hIm : (γ • z).im = z.im / ‖den γ z‖ ^ 2 := by
    rw [ModularGroup.im_smul_eq_div_normSq, ← Complex.normSq_eq_norm_sq, den_eq]
  unfold phi psi0
  rw [norm_mul, norm_inv, norm_jk ℓ γ h4 hz, norm_cexp_n, mob_eq]
  simp only [UpperHalfPlane.coe_im]
  rw [hIm, Real.div_rpow hz.le (by positivity),
    show (‖den γ z‖ ^ 2) ^ (kw ℓ / 2) = ‖den γ z‖ ^ ((3 : ℝ) / 2 + ℓ) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le]; unfold kw; push_cast; ring_nf]
  rw [div_eq_mul_inv]
  ring

theorem dvd4_gam {Q : ℕ} (hQ : 4 ∣ Q) (r : RowsQ Q) : (4 : ℤ) ∣ (gam r.1) 1 0 := by
  have h0 : (gam r.1) 1 0 = r.1.1 0 := congrFun (gam_row r.1) 0
  rw [h0]
  exact dvd_trans (by exact_mod_cast hQ) r.2

theorem tsum_nnnorm_phi_le {Q : ℕ} (hQ : 4 ∣ Q) (z : ℍ) :
    ∑' r : RowsQ Q, (‖phi ℓ n (gam r.1) z‖₊ : ENNReal) ≤
      ENNReal.ofReal (z.im ^ (-(kw ℓ / 2))) * Estar (kw ℓ) n z := by
  have hz := z.im_pos
  have hpt : ∀ r : RowsQ Q, (‖phi ℓ n (gam r.1) z‖₊ : ENNReal) =
      ENNReal.ofReal (z.im ^ (-(kw ℓ / 2))) * psiE (kw ℓ) n (gam r.1 • z) := by
    intro r
    have h := norm_phi ℓ n (gam r.1) (dvd4_gam hQ r) z
    unfold psiE
    rw [← h, ← ENNReal.ofReal_mul (by positivity)]
    rw [show z.im ^ (-(kw ℓ / 2)) * (‖phi ℓ n (gam r.1) z‖ * z.im ^ (kw ℓ / 2)) =
        ‖phi ℓ n (gam r.1) z‖ by
      rw [mul_comm, mul_assoc, ← Real.rpow_add hz, add_neg_cancel, Real.rpow_zero, mul_one]]
    rw [ofReal_norm_eq_enorm]; rfl
  simp_rw [hpt]
  rw [ENNReal.tsum_mul_left]
  gcongr
  exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
    (fun r : Rows => psiE (kw ℓ) n (gam r • z))

/-- **The Poincaré series converges absolutely, and `(Im z)^{k/2}|P(z)| ≤ M`.** -/
theorem poin_bound (hℓ : 1 ≤ ℓ) {Q : ℕ} (hQ : 4 ∣ Q) (hn : 0 < n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℍ, Summable (fun r : RowsQ Q => ‖phi ℓ n (gam r.1) z‖) ∧
      z.im ^ (kw ℓ / 2) * ∑' r : RowsQ Q, ‖phi ℓ n (gam r.1) z‖ ≤ M := by
  have hk : 2 < kw ℓ := by unfold kw; have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
                           linarith
  obtain ⟨M, hM, hEM⟩ := Estar_bdd hk hn
  refine ⟨M.toReal, ENNReal.toReal_nonneg, fun z => ?_⟩
  have hz := z.im_pos
  have hle := tsum_nnnorm_phi_le ℓ n hQ z
  have hfin : ∑' r : RowsQ Q, (‖phi ℓ n (gam r.1) z‖₊ : ENNReal) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hle
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top hM.ne (hEM z))
  have hsum : Summable (fun r : RowsQ Q => ‖phi ℓ n (gam r.1) z‖₊) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp hfin
  have hsum' : Summable (fun r : RowsQ Q => ‖phi ℓ n (gam r.1) z‖) := NNReal.summable_coe.mpr hsum
  refine ⟨hsum', ?_⟩
  have h1 : ENNReal.ofReal (∑' r : RowsQ Q, ‖phi ℓ n (gam r.1) z‖) =
      ∑' r : RowsQ Q, (‖phi ℓ n (gam r.1) z‖₊ : ENNReal) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun r => norm_nonneg _) hsum']
    simp [ofReal_norm_eq_enorm]; rfl
  have h2 : ENNReal.ofReal (z.im ^ (kw ℓ / 2) * ∑' r : RowsQ Q, ‖phi ℓ n (gam r.1) z‖) ≤ M := by
    rw [ENNReal.ofReal_mul (by positivity), h1]
    calc ENNReal.ofReal (z.im ^ (kw ℓ / 2)) * ∑' r : RowsQ Q, (‖phi ℓ n (gam r.1) z‖₊ : ENNReal)
        ≤ ENNReal.ofReal (z.im ^ (kw ℓ / 2)) * (ENNReal.ofReal (z.im ^ (-(kw ℓ / 2))) *
            Estar (kw ℓ) n z) := by gcongr
      _ = Estar (kw ℓ) n z := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hz,
            add_neg_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ M := hEM z
  exact (ENNReal.ofReal_le_iff_le_toReal hM.ne).mp h2

end ThreeSquares.Poin
