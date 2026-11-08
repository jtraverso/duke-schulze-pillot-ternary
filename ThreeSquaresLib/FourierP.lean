/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.FourierAux
public import ThreeSquaresLib.ThetaAut

/-!
# The Fourier coefficient of the Poincaré series: splitting the rows

For `y > 0`, `F_r = ∫_0^1 φ_{γ_r}(x + iy) e(−nx) dx`.
* `integral_poin_eq_tsum`: `∫_0^1 P(x + iy) e(−nx) dx = ∑_r F_r`;
* `tsum_Fr_split`: `∑_r F_r = 2 e^{−2πny} + 2 ∑_{r₀ > 0} F_r` (even `ℓ`).
-/

@[expose] public section

namespace ThreeSquares.Poin

open Complex UpperHalfPlane ModularGroup MeasureTheory ThreeSquares.FD ThreeSquares.Mult
  ThreeSquares.Lip Filter Topology Set

open scoped MatrixGroups Real ComplexConjugate

variable (ℓ : ℕ) (n : ℕ)

/-- The point `x + iy` of `ℍ`. -/
def ptH {y : ℝ} (hy : 0 < y) (x : ℝ) : ℍ := ⟨(x : ℂ) + y * Complex.I, by simp [hy]⟩

theorem ptH_coe {y : ℝ} (hy : 0 < y) (x : ℝ) : ((ptH hy x : ℍ) : ℂ) = (x : ℂ) + y * Complex.I := rfl

theorem ptH_im {y : ℝ} (hy : 0 < y) (x : ℝ) : (ptH hy x).im = y := by
  show ((x : ℂ) + y * Complex.I).im = y; simp

/-- `F_r = ∫_0^1 φ_{γ_r}(x + iy) e(−nx) dx`. -/
noncomputable def Fr {Q : ℕ} (y : ℝ) (r : RowsQ Q) : ℂ :=
  ∫ x in Ico (0 : ℝ) 1, phi ℓ n (gam r.1) ((x : ℂ) + y * Complex.I) * cexp (-(2 * π * Complex.I * n * x))

theorem norm_cexp_neg (x : ℝ) : ‖cexp (-(2 * π * Complex.I * n * x))‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- The uniform bound on `∑_r |φ_r(x + iy)|`. -/
theorem lintegral_tsum_phi_lt_top (hℓ : 1 ≤ ℓ) {Q : ℕ} (hQ : 4 ∣ Q) (hn : 0 < n) {y : ℝ}
    (hy : 0 < y) :
    ∑' r : RowsQ Q, ∫⁻ x in Ico (0 : ℝ) 1,
      ‖phi ℓ n (gam r.1) ((x : ℂ) + y * Complex.I) * cexp (-(2 * π * Complex.I * n * x))‖ₑ < ⊤ := by
  have hk : 2 < kw ℓ := by
    unfold kw; have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  obtain ⟨M, hM, hEM⟩ := Estar_bdd hk hn
  have hmeas : ∀ r : RowsQ Q, Measurable fun x : ℝ =>
      ‖phi ℓ n (gam r.1) ((x : ℂ) + y * Complex.I) * cexp (-(2 * π * Complex.I * n * x))‖ₑ :=
    fun r => (((measurable_phi ℓ n _).comp (by fun_prop)).mul (by fun_prop)).enorm
  rw [← lintegral_tsum fun r => (hmeas r).aemeasurable]
  calc ∫⁻ x in Ico (0 : ℝ) 1, ∑' r : RowsQ Q,
        ‖phi ℓ n (gam r.1) ((x : ℂ) + y * Complex.I) * cexp (-(2 * π * Complex.I * n * x))‖ₑ
      ≤ ∫⁻ _x in Ico (0 : ℝ) 1, ENNReal.ofReal (y ^ (-(kw ℓ / 2))) * M := by
        refine setLIntegral_mono measurable_const fun x _ => ?_
        have h := tsum_nnnorm_phi_le ℓ n hQ (ptH hy x)
        rw [ptH_im] at h
        calc ∑' r : RowsQ Q, ‖phi ℓ n (gam r.1) ((x : ℂ) + y * Complex.I) *
              cexp (-(2 * π * Complex.I * n * x))‖ₑ
            = ∑' r : RowsQ Q, (‖phi ℓ n (gam r.1) (ptH hy x)‖₊ : ENNReal) := by
              refine tsum_congr fun r => ?_
              rw [enorm_mul, ← ofReal_norm_eq_enorm (cexp _), norm_cexp_neg, ENNReal.ofReal_one,
                mul_one]; rfl
          _ ≤ ENNReal.ofReal (y ^ (-(kw ℓ / 2))) * Estar (kw ℓ) n (ptH hy x) := h
          _ ≤ _ := by gcongr; exact hEM _
    _ < ⊤ := by
        rw [setLIntegral_const, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, mul_one]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM

theorem integral_poin_eq_tsum (hℓ : 1 ≤ ℓ) {Q : ℕ} (hQ : 4 ∣ Q) (hn : 0 < n) {y : ℝ} (hy : 0 < y) :
    ∫ x in Ico (0 : ℝ) 1, poin ℓ Q n ((x : ℂ) + y * Complex.I) * cexp (-(2 * π * Complex.I * n * x)) =
      ∑' r : RowsQ Q, Fr ℓ n y r := by
  unfold poin Fr
  simp_rw [← tsum_mul_right]
  exact integral_tsum (fun r => (((measurable_phi ℓ n _).comp (by fun_prop)).mul
    (by fun_prop)).aestronglyMeasurable) (lintegral_tsum_phi_lt_top ℓ n hℓ hQ hn hy).ne

theorem summable_Fr (hℓ : 1 ≤ ℓ) {Q : ℕ} (hQ : 4 ∣ Q) (hn : 0 < n) {y : ℝ} (hy : 0 < y) :
    Summable (Fr ℓ n y (Q := Q)) := by
  have h := lintegral_tsum_phi_lt_top ℓ n hℓ hQ hn hy
  refine Summable.of_norm_bounded (ENNReal.summable_toReal h.ne) fun r => ?_
  exact norm_integral_le_lintegral_norm _ |>.trans (le_of_eq (by
    congr 1; refine lintegral_congr fun x => ?_; rw [ofReal_norm_eq_enorm]))

/-! ### The rows with `c = 0` and the symmetry `r ↦ −r` -/

/-- Negation of a coprime row with `Q ∣ r₀`. -/
def negRow {Q : ℕ} (r : RowsQ Q) : RowsQ Q :=
  ⟨⟨-r.1.1, by
    have h := r.1.2
    simpa using h.neg_neg⟩, by simpa using r.2⟩

theorem negRow_negRow {Q : ℕ} (r : RowsQ Q) : negRow (negRow r) = r := by
  apply Subtype.ext; apply Subtype.ext; simp [negRow]

/-- `r ↦ −r` as an equivalence. -/
def negEquiv (Q : ℕ) : RowsQ Q ≃ RowsQ Q where
  toFun := negRow
  invFun := negRow
  left_inv := negRow_negRow
  right_inv := negRow_negRow

theorem Fr_neg (hℓe : Even ℓ) {Q : ℕ} (hQ : 4 ∣ Q) {y : ℝ} (hy : 0 < y) (r : RowsQ Q) :
    Fr ℓ n y (negRow r) = Fr ℓ n y r := by
  unfold Fr
  refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
  have hz : 0 < ((x : ℂ) + y * Complex.I).im := by simp [hy]
  congr 1
  -- `γ_{−r}` and `−γ_r` have the same bottom row
  have h4 : (4 : ℤ) ∣ (-gam r.1) 1 0 := by rw [neg_10]; exact dvd_neg.mpr (dvd4_gam hQ r)
  have e : rowOf (-gam r.1) = rowOf (gam (negRow r).1) := by
    rw [rowOf_gam]
    apply Subtype.ext
    ext i
    have := congrFun (gam_row r.1) i
    fin_cases i
    · simp [rowOf, negRow, Matrix.SpecialLinearGroup.coe_neg] at this ⊢; exact this
    · simp [rowOf, negRow, Matrix.SpecialLinearGroup.coe_neg] at this ⊢; exact this
  rw [phi_eq_of_row ℓ n h4 e hz, phi_neg n hℓe]

theorem phi_one (z : ℂ) : phi ℓ n 1 z = cexp (2 * π * Complex.I * n * z) := by
  simp [phi, jk, jm, den, mob]

theorem Fr_zero_row (hℓe : Even ℓ) {Q : ℕ} {y : ℝ} (hy : 0 < y) (r : RowsQ Q) (h0 : r.1.1 0 = 0) :
    Fr ℓ n y r = Real.exp (-(2 * π * n * y)) := by
  have hu : IsUnit (r.1.1 1) := by
    have := r.1.2; rw [h0] at this; exact isCoprime_zero_left.mp this
  have hphi : ∀ z : ℂ, 0 < z.im → phi ℓ n (gam r.1) z = cexp (2 * π * Complex.I * n * z) := by
    intro z hz
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · have e : rowOf (1 : SL(2, ℤ)) = rowOf (gam r.1) := by
        rw [rowOf_gam]; apply Subtype.ext; ext i; fin_cases i <;> simp [rowOf, h0, h1]
      rw [phi_eq_of_row ℓ n (by simp) e hz, phi_one]
    · have e : rowOf (-1 : SL(2, ℤ)) = rowOf (gam r.1) := by
        rw [rowOf_gam]; apply Subtype.ext; ext i; fin_cases i <;>
          simp [rowOf, h0, h1, Matrix.SpecialLinearGroup.coe_neg]
      rw [phi_eq_of_row ℓ n (by simp [Matrix.SpecialLinearGroup.coe_neg]) e hz, phi_neg n hℓe,
        phi_one]
  unfold Fr
  have hpt : ∀ x ∈ Ico (0 : ℝ) 1, phi ℓ n (gam r.1) ((x : ℂ) + y * Complex.I) *
      cexp (-(2 * π * Complex.I * n * x)) = ((Real.exp (-(2 * π * n * y)) : ℝ) : ℂ) := by
    intro x _
    rw [hphi _ (by simp [hy]), ← Complex.exp_add, Complex.ofReal_exp]
    congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [setIntegral_congr_fun measurableSet_Ico hpt, setIntegral_const]
  simp

/-- The two rows `(0, ±1)`. -/
def rowP1 (Q : ℕ) : RowsQ Q := ⟨⟨![0, 1], by simp [isCoprime_zero_left]⟩, by simp⟩
def rowM1 (Q : ℕ) : RowsQ Q := ⟨⟨![0, -1], by simp [isCoprime_zero_left]⟩, by simp⟩

theorem rowP1_ne_rowM1 (Q : ℕ) : rowP1 Q ≠ rowM1 Q := by
  intro h
  have := congrFun (congrArg (fun r : RowsQ Q => r.1.1) h) 1
  simp [rowP1, rowM1] at this

theorem mem_zero_rows {Q : ℕ} (r : RowsQ Q) (h0 : r.1.1 0 = 0) : r = rowP1 Q ∨ r = rowM1 Q := by
  have hu : IsUnit (r.1.1 1) := by
    have := r.1.2; rw [h0] at this; exact isCoprime_zero_left.mp this
  rcases Int.isUnit_iff.mp hu with h1 | h1
  · left; apply Subtype.ext; apply Subtype.ext; ext i; fin_cases i <;> simp [rowP1, h0, h1]
  · right; apply Subtype.ext; apply Subtype.ext; ext i; fin_cases i <;> simp [rowM1, h0, h1]

/-- **`∑_r F_r = 2 e^{−2πny} + 2 ∑_{r₀ > 0} F_r`.** -/
theorem tsum_Fr_split (hℓ : 1 ≤ ℓ) (hℓe : Even ℓ) {Q : ℕ} (hQ : 4 ∣ Q) (hn : 0 < n) {y : ℝ}
    (hy : 0 < y) :
    ∑' r : RowsQ Q, Fr ℓ n y r = 2 * Real.exp (-(2 * π * n * y)) +
      2 * ∑' r : RowsQ Q, {r : RowsQ Q | 0 < r.1.1 0}.indicator (Fr ℓ n y) r := by
  classical
  have hs := summable_Fr ℓ n hℓ hQ hn hy
  set S0 := {r : RowsQ Q | r.1.1 0 = 0}
  set Sp := {r : RowsQ Q | 0 < r.1.1 0}
  set Sn := {r : RowsQ Q | r.1.1 0 < 0}
  have hsplit : ∀ r, Fr ℓ n y r = S0.indicator (Fr ℓ n y) r +
      (Sp.indicator (Fr ℓ n y) r + Sn.indicator (Fr ℓ n y) r) := by
    intro r
    rcases lt_trichotomy (r.1.1 0) 0 with h | h | h
    · have h1 : r ∉ S0 := by simp [S0]; omega
      have h2 : r ∉ Sp := by simp [Sp]; omega
      have h3 : r ∈ Sn := h
      simp [indicator_of_notMem h1, indicator_of_notMem h2, indicator_of_mem h3]
    · have h1 : r ∈ S0 := h
      have h2 : r ∉ Sp := by simp [Sp]; omega
      have h3 : r ∉ Sn := by simp [Sn]; omega
      simp [indicator_of_mem h1, indicator_of_notMem h2, indicator_of_notMem h3]
    · have h1 : r ∉ S0 := by simp [S0]; omega
      have h2 : r ∈ Sp := h
      have h3 : r ∉ Sn := by simp [Sn]; omega
      simp [indicator_of_notMem h1, indicator_of_mem h2, indicator_of_notMem h3]
  rw [tsum_congr hsplit, (hs.indicator S0).tsum_add ((hs.indicator Sp).add (hs.indicator Sn)),
    (hs.indicator Sp).tsum_add (hs.indicator Sn)]
  -- the negative rows
  have hneg : ∑' r, Sn.indicator (Fr ℓ n y) r = ∑' r, Sp.indicator (Fr ℓ n y) r := by
    rw [← (negEquiv Q).tsum_eq]
    refine tsum_congr fun r => ?_
    show Sn.indicator (Fr ℓ n y) (negRow r) = Sp.indicator (Fr ℓ n y) r
    by_cases h : r ∈ Sp
    · have h' : negRow r ∈ Sn := by simp [Sn, negRow]; exact h
      rw [indicator_of_mem h', indicator_of_mem h, Fr_neg ℓ n hℓe hQ hy]
    · have h' : negRow r ∉ Sn := by
        simp only [Sp, mem_setOf_eq, not_lt] at h
        simp [Sn, negRow]; exact h
      rw [indicator_of_notMem h', indicator_of_notMem h]
  -- the rows `(0, ±1)`
  have hzero : ∑' r, S0.indicator (Fr ℓ n y) r = 2 * Real.exp (-(2 * π * n * y)) := by
    rw [tsum_eq_sum (s := {rowP1 Q, rowM1 Q}) fun r hr => ?_]
    · rw [Finset.sum_pair (rowP1_ne_rowM1 Q),
        indicator_of_mem (show rowP1 Q ∈ S0 by simp [S0, rowP1]),
        indicator_of_mem (show rowM1 Q ∈ S0 by simp [S0, rowM1]),
        Fr_zero_row ℓ n hℓe hy _ (by simp [rowP1]), Fr_zero_row ℓ n hℓe hy _ (by simp [rowM1])]
      ring
    · refine indicator_of_notMem (fun h => hr ?_) _
      rcases mem_zero_rows r h with h' | h' <;> simp [h']
  rw [hneg, hzero]
  ring

/-! ### Grouping the rows with `c > 0` by `(c, d mod c)` -/

/-- `0 < c`, `Q ∣ c`, `0 ≤ d₀ < c`, `(c, d₀) = 1`. -/
def KCond (Q : ℕ) (p : ℤ × ℤ) : Prop :=
  0 < p.1 ∧ (Q : ℤ) ∣ p.1 ∧ 0 ≤ p.2 ∧ p.2 < p.1 ∧ IsCoprime p.1 p.2

/-- The coprime row `(c, d₀)`. -/
def rowK (p : ℤ × ℤ) (h : IsCoprime p.1 p.2) : Rows := ⟨![p.1, p.2], by simpa using h⟩

/-- The double-coset integral. -/
noncomputable def Ik (y : ℝ) (Q : ℕ) (p : ℤ × ℤ) : ℂ := by
  classical
  exact if h : KCond Q p then ∫ x : ℝ, phi ℓ n (gam (rowK p h.2.2.2.2)) ((x : ℂ) + y * Complex.I) *
    cexp (-(2 * π * Complex.I * n * x)) else 0

/-- The grouping key `r ↦ (c, d mod c)`. -/
def keyR {Q : ℕ} (r : RowsQ Q) : ℤ × ℤ := (r.1.1 0, r.1.1 1 % r.1.1 0)

theorem kcond_of_key {Q : ℕ} (r : RowsQ Q) (hc : 0 < r.1.1 0) : KCond Q (keyR r) := by
  refine ⟨hc, r.2, Int.emod_nonneg _ hc.ne', Int.emod_lt_of_pos _ hc, ?_⟩
  simp only [keyR]
  have h := r.1.2
  rw [Int.emod_def]
  have : IsCoprime (r.1.1 0) (r.1.1 1 + (-(r.1.1 1 / r.1.1 0)) * r.1.1 0) := h.add_mul_right_right _
  convert this using 1; ring

/-- The `m`-th row `(c, d₀ + cm)` of the fiber over `(c, d₀)`. -/
def fibRow {Q : ℕ} (p : ℤ × ℤ) (hp : KCond Q p) (m : ℤ) : RowsQ Q :=
  ⟨⟨![p.1, p.2 + p.1 * m], hp.2.2.2.2.add_mul_left_right m⟩, hp.2.1⟩

theorem keyR_fibRow {Q : ℕ} (p : ℤ × ℤ) (hp : KCond Q p) (m : ℤ) : keyR (fibRow p hp m) = p := by
  show (p.1, (p.2 + p.1 * m) % p.1) = p
  rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hp.2.2.1 hp.2.2.2.1]

/-- The fiber over a key satisfying `KCond` is a copy of `ℤ`. -/
def fiberEquiv {Q : ℕ} (p : ℤ × ℤ) (hp : KCond Q p) : ℤ ≃ {r : RowsQ Q // keyR r = p} where
  toFun m := ⟨fibRow p hp m, keyR_fibRow p hp m⟩
  invFun r := r.1.1.1 1 / p.1
  left_inv m := by
    show (p.2 + p.1 * m) / p.1 = m
    rw [Int.add_mul_ediv_left _ _ hp.1.ne', Int.ediv_eq_zero_of_lt hp.2.2.1 hp.2.2.2.1, zero_add]
  right_inv r := by
    obtain ⟨r, hr⟩ := r
    have h0 : r.1.1 0 = p.1 := congrArg Prod.fst hr
    have h1 : r.1.1 1 % r.1.1 0 = p.2 := congrArg Prod.snd hr
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    ext i; fin_cases i
    · show p.1 = r.1.1 0; rw [h0]
    · show p.2 + p.1 * (r.1.1 1 / p.1) = r.1.1 1
      rw [← h1, ← h0]
      have := Int.mul_ediv_add_emod (r.1.1 1) (r.1.1 0)
      linarith

/-- `φ` of the `m`-th element of the fiber. -/
theorem phi_fiber {Q : ℕ} (hQ : 4 ∣ Q) (p : ℤ × ℤ) (hp : KCond Q p) (m : ℤ) {z : ℂ}
    (hz : 0 < z.im) :
    phi ℓ n (gam (fibRow p hp m).1) z = phi ℓ n (gam (rowK p hp.2.2.2.2)) (z + m) := by
  set γ₀ := gam (rowK p hp.2.2.2.2)
  have h10 : γ₀ 1 0 = p.1 := congrFun (gam_row (rowK p hp.2.2.2.2)) 0
  have h11 : γ₀ 1 1 = p.2 := congrFun (gam_row (rowK p hp.2.2.2.2)) 1
  have h4 : (4 : ℤ) ∣ γ₀ 1 0 := by
    rw [h10]; exact dvd_trans (show (4 : ℤ) ∣ (Q : ℤ) by exact_mod_cast hQ) hp.2.1
  have h4' : (4 : ℤ) ∣ (γ₀ * T ^ m) 1 0 := by
    rw [mul_10']; simp [coe_T_zpow, h4]
  have e : rowOf (γ₀ * T ^ m) = rowOf (gam (fibRow p hp m).1) := by
    rw [rowOf_gam]
    apply Subtype.ext; ext i; fin_cases i
    · show (γ₀ * T ^ m) 1 0 = p.1
      rw [mul_10']; simp [coe_T_zpow, h10]
    · show (γ₀ * T ^ m) 1 1 = p.2 + p.1 * m
      rw [mul_11']; simp [coe_T_zpow, h10, h11]; ring
  rw [phi_eq_of_row ℓ n h4' e hz, phi_mul_T ℓ n γ₀ h4 m hz]

theorem cexp_neg_shift (x : ℝ) (m : ℤ) :
    cexp (-(2 * π * Complex.I * n * ((x + m : ℝ) : ℂ))) = cexp (-(2 * π * Complex.I * n * x)) := by
  rw [show -(2 * π * Complex.I * n * ((x + m : ℝ) : ℂ)) = -(2 * π * Complex.I * n * x) +
    ((-(n * m) : ℤ) : ℂ) * (2 * π * Complex.I) by push_cast; ring, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The sum over one fiber. -/
theorem tsum_fiber (hℓ : 1 ≤ ℓ) {Q : ℕ} (hQ : 4 ∣ Q) (hn : 0 < n) {y : ℝ} (hy : 0 < y)
    (p : ℤ × ℤ) (hp : KCond Q p) :
    ∑' f : {r : RowsQ Q // keyR r = p}, Fr ℓ n y f.1 =
      ∫ x : ℝ, phi ℓ n (gam (rowK p hp.2.2.2.2)) ((x : ℂ) + y * Complex.I) *
        cexp (-(2 * π * Complex.I * n * x)) := by
  set γ₀ := gam (rowK p hp.2.2.2.2)
  have h10 : γ₀ 1 0 = p.1 := congrFun (gam_row (rowK p hp.2.2.2.2)) 0
  have h4 : (4 : ℤ) ∣ γ₀ 1 0 := by
    rw [h10]; exact dvd_trans (show (4 : ℤ) ∣ (Q : ℤ) by exact_mod_cast hQ) hp.2.1
  set g : ℝ → ℂ := fun x => phi ℓ n γ₀ ((x : ℂ) + y * Complex.I) * cexp (-(2 * π * Complex.I * n * x))
  have hg : Integrable g := by
    refine (integrable_phi_pos ℓ n γ₀ (by rw [h10]; exact hp.1) h4 hy).mono
      (((measurable_phi ℓ n _).comp (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_cexp_neg, mul_one]
  rw [integral_eq_tsum_Ico hg, ← (fiberEquiv p hp).tsum_eq]
  refine tsum_congr fun m => ?_
  unfold Fr
  refine setIntegral_congr_fun measurableSet_Ico fun x _ => ?_
  simp only [g]
  show phi ℓ n (gam (fibRow p hp m).1) ((x : ℂ) + y * Complex.I) * cexp (-(2 * π * Complex.I * n * x)) =
    phi ℓ n γ₀ (((x + m : ℝ) : ℂ) + y * Complex.I) * cexp (-(2 * π * Complex.I * n * ((x + m : ℝ) : ℂ)))
  rw [phi_fiber ℓ n hQ p hp m (by simp [hy]), cexp_neg_shift n x m]
  congr 2; push_cast; ring

/-- **The rows with `c > 0`.** -/
theorem tsum_pos_rows (hℓ : 1 ≤ ℓ) {Q : ℕ} (hQ : 4 ∣ Q) (hn : 0 < n) {y : ℝ} (hy : 0 < y) :
    ∑' r : RowsQ Q, {r : RowsQ Q | 0 < r.1.1 0}.indicator (Fr ℓ n y) r =
      ∑' p : ℤ × ℤ, Ik ℓ n y Q p := by
  classical
  set G := {r : RowsQ Q | 0 < r.1.1 0}.indicator (Fr ℓ n y)
  have hs : Summable G := (summable_Fr ℓ n hℓ hQ hn hy).indicator _
  rw [← (Equiv.sigmaFiberEquiv (keyR (Q := Q))).tsum_eq]
  rw [Summable.tsum_sigma (f := fun c => G ((Equiv.sigmaFiberEquiv (keyR (Q := Q))) c))
    ((Equiv.sigmaFiberEquiv (keyR (Q := Q))).summable_iff.mpr hs)]
  refine tsum_congr fun p => ?_
  unfold Ik
  by_cases hp : KCond Q p
  · rw [dif_pos hp, ← tsum_fiber ℓ n hℓ hQ hn hy p hp]
    refine tsum_congr fun f => ?_
    simp only [Equiv.sigmaFiberEquiv_apply]
    have hc : 0 < f.1.1.1 0 := by
      have : (keyR f.1).1 = p.1 := by rw [f.2]
      simp only [keyR] at this; rw [this]; exact hp.1
    exact indicator_of_mem (show f.1 ∈ {r : RowsQ Q | 0 < r.1.1 0} from hc) _
  · rw [dif_neg hp]
    refine (tsum_congr fun f => ?_).trans tsum_zero
    simp only [Equiv.sigmaFiberEquiv_apply]
    refine indicator_of_notMem (fun hc => hp ?_) _
    have := kcond_of_key f.1 hc
    rwa [f.2] at this

/-! ### The Fourier coefficient and the unfolded `⟨P, P⟩` -/

/-- The `y`-independent double-coset term
`κ(a,c)^{−3} c^{−k} e(n(a+d)/c) (−2πi)^k n^{k−1} S_k(4π²n²/c²)`. -/
noncomputable def Jk (Q : ℕ) (p : ℤ × ℤ) : ℂ := by
  classical
  exact if h : KCond Q p then
    (kap ((gam (rowK p h.2.2.2.2)) 0 0) ((gam (rowK p h.2.2.2.2)) 1 0) ^ 3)⁻¹ *
      (((gam (rowK p h.2.2.2.2)) 1 0 : ℝ) : ℂ) ^ (-(kw ℓ : ℂ)) *
      cexp (2 * π * Complex.I * n * ((((gam (rowK p h.2.2.2.2)) 0 0 : ℂ) +
        (gam (rowK p h.2.2.2.2)) 1 1) / ((gam (rowK p h.2.2.2.2)) 1 0))) *
      ((-(2 * π * Complex.I)) ^ (kw ℓ : ℂ) * ((n : ℝ) : ℂ) ^ ((kw ℓ : ℂ) - 1) *
        besS (kw ℓ) (4 * π ^ 2 * ((n : ℝ) / ((gam (rowK p h.2.2.2.2)) 1 0 : ℝ) ^ 2) * n))
  else 0

theorem Ik_eq {Q : ℕ} (hn : 0 < n) {y : ℝ} (hy : 0 < y) (p : ℤ × ℤ) :
    Ik ℓ n y Q p = Real.exp (-(2 * π * n * y)) * Jk ℓ n Q p := by
  unfold Ik Jk
  by_cases hp : KCond Q p
  · have hc : 0 < (gam (rowK p hp.2.2.2.2)) 1 0 := by
      rw [show (gam (rowK p hp.2.2.2.2)) 1 0 = p.1 from congrFun (gam_row _) 0]; exact hp.1
    rw [dif_pos hp, dif_pos hp, integral_phi_pos ℓ n _ hc hy hn]
    ring
  · rw [dif_neg hp, dif_neg hp, mul_zero]

/-- **The Fourier coefficient of the Poincaré series.** -/
theorem fourier_poin (hℓ : 1 ≤ ℓ) (hℓe : Even ℓ) {Q : ℕ} (hQ : 4 ∣ Q) (hn : 0 < n) {y : ℝ}
    (hy : 0 < y) :
    ∫ x in Ico (0 : ℝ) 1, poin ℓ Q n ((x : ℂ) + y * Complex.I) * cexp (-(2 * π * Complex.I * n * x)) =
      Real.exp (-(2 * π * n * y)) * (2 + 2 * ∑' p : ℤ × ℤ, Jk ℓ n Q p) := by
  rw [integral_poin_eq_tsum ℓ n hℓ hQ hn hy, tsum_Fr_split ℓ n hℓ hℓe hQ hn hy,
    tsum_pos_rows ℓ n hℓ hQ hn hy, tsum_congr (Ik_eq ℓ n hn hy), tsum_mul_left]
  ring

/-- `P̂(n) = 2 + 2 ∑_{(c, d₀)} J_k(c, d₀)`. -/
noncomputable def Phat (Q : ℕ) : ℂ := 2 + 2 * ∑' p : ℤ × ℤ, Jk ℓ n Q p

/-- **The unfolded `⟨P, P⟩`:** `∫_{strip} P(z) conj(e(nz)) y^k = Γ(k−1) (4πn)^{1−k} P̂(n)`. -/
theorem strip_PhiF_poin (hℓ : 1 ≤ ℓ) (hℓe : Even ℓ) {Q : ℕ} (hQ : 4 ∣ Q) (hn : 0 < n) :
    ∫ z in strip, PhiF ℓ n (poin ℓ Q n) z =
      ((Real.Gamma (kw ℓ - 1) * (1 / (4 * π * n)) ^ (kw ℓ - 1) : ℝ) : ℂ) * Phat ℓ n Q := by
  have hF := isAut_poin ℓ n hℓ hQ hn
  set G : ℂ → ℂ := fun w => poin ℓ Q n w * conj (en n w) * ((w.im ^ kw ℓ : ℝ) : ℂ)
  have hint : IntegrableOn (fun z : ℍ => G z) strip :=
    ⟨(measurable_PhiF ℓ n hF).aestronglyMeasurable, lintegral_PhiF_lt_top ℓ n hℓ hn hF⟩
  show ∫ z in strip, G z = _
  rw [integral_strip G hint]
  have hk : 0 < kw ℓ - 1 := by
    unfold kw; have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    linarith
  have inner : ∀ y : ℝ, 0 < y → ∫ x : ℝ in Ico 0 1, G ((x : ℂ) + (y : ℂ) * Complex.I) =
      ((y ^ kw ℓ * Real.exp (-(4 * π * n * y)) : ℝ) : ℂ) * Phat ℓ n Q := by
    intro y hy
    have hc := fourier_poin ℓ n hℓ hℓe hQ hn hy
    have e : ∀ x ∈ Ico (0 : ℝ) 1, G ((x : ℂ) + (y : ℂ) * Complex.I) =
        ((y ^ kw ℓ * Real.exp (-(2 * π * n * y)) : ℝ) : ℂ) *
          (poin ℓ Q n ((x : ℂ) + y * Complex.I) * cexp (-(2 * π * Complex.I * n * x))) := by
      intro x _
      simp only [G]
      rw [conj_en]
      simp only [add_im, ofReal_im, mul_im, ofReal_re, Complex.I_re, mul_zero, Complex.I_im, mul_one,
        zero_add]
      have e2 : cexp (-(2 * π * Complex.I * n * ((x : ℂ) + y * Complex.I))) =
          cexp (-(2 * π * Complex.I * n * x)) * ((Real.exp (2 * π * n * y) : ℝ) : ℂ) := by
        rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring_nf
        rw [Complex.I_sq]; ring
      have e3 : (Real.exp (2 * π * n * y) : ℂ) * (Real.exp (-(4 * π * n * y)) : ℂ) =
          (Real.exp (-(2 * π * n * y)) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
      rw [e2, Complex.ofReal_mul, ← e3]
      ring
    rw [setIntegral_congr_fun measurableSet_Ico e, integral_const_mul, hc, Phat]
    have e4 : (Real.exp (-(2 * π * n * y)) : ℂ) * (Real.exp (-(2 * π * n * y)) : ℂ) =
        (Real.exp (-(4 * π * n * y)) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
    rw [Complex.ofReal_mul, Complex.ofReal_mul]
    linear_combination ((y ^ kw ℓ : ℝ) : ℂ) * (2 + 2 * ∑' p : ℤ × ℤ, Jk ℓ n Q p) * e4
  rw [setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => by rw [inner y hy]]
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi hk (by positivity : (0 : ℝ) < 4 * π * n)
  have e : ∀ y ∈ Set.Ioi (0 : ℝ), (1 / y ^ 2 : ℝ) • (((y ^ kw ℓ * Real.exp (-(4 * π * n * y)) : ℝ)
      : ℂ) * Phat ℓ n Q) = ((y ^ (kw ℓ - 1 - 1) * Real.exp (-(4 * π * n * y)) : ℝ) : ℂ) *
        Phat ℓ n Q := by
    intro y (hy : 0 < y)
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    rw [show kw ℓ - 1 - 1 = kw ℓ - 2 by ring, Real.rpow_sub hy, Real.rpow_two]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi e, integral_mul_const, integral_complex_ofReal, hg]
  push_cast
  ring

end ThreeSquares.Poin
