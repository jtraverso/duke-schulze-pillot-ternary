/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DSPLib.BinaryCount
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Representations by a positive definite ternary form

For a symmetric integer matrix `A` with `Q(y) = ∑ A_{ij} y_i y_j > 0` on nonzero integer vectors,
the number of `y ∈ ℤ³` with `Q(y) = N` is at most `C_ε N^{1/2+ε}` (`ternary_count_le`).

Completing the square twice, `a b₁₁ Q(y) = b₁₁ z² + X² + Δ y₂²` with `a = A₀₀`,
`b₁₁ = a A₁₁ − A₀₁²`, `b₁₂ = a A₁₂ − A₀₁A₀₂`, `b₂₂ = a A₂₂ − A₀₂²`, `Δ = b₁₁ b₂₂ − b₁₂²`,
`z = a y₀ + A₀₁ y₁ + A₀₂ y₂`, `X = b₁₁ y₁ + b₁₂ y₂`. The map `y ↦ (z, X, y₂)` is injective, `z`
ranges over at most `2√(aN) + 1` values, and for each `z` the pairs `(X, y₂)` are representations
of `b₁₁ (aN − z²)` by `X² + ΔY²`, at most `C_ε (aN)^ε` of them.
-/

@[expose] public section

namespace DSP

/-- The quadratic form `∑ A_{ij} y_i y_j`. -/
def Qf (A : Fin 3 → Fin 3 → ℤ) (y : Fin 3 → ℤ) : ℤ := ∑ i, ∑ j, A i j * y i * y j

section Coefficients

variable (A : Fin 3 → Fin 3 → ℤ)

/-- `a = A₀₀`. -/
def ca : ℤ := A 0 0
/-- `b₁₁ = a A₁₁ − A₀₁²`. -/
def cb11 : ℤ := A 0 0 * A 1 1 - A 0 1 ^ 2
/-- `b₁₂ = a A₁₂ − A₀₁ A₀₂`. -/
def cb12 : ℤ := A 0 0 * A 1 2 - A 0 1 * A 0 2
/-- `b₂₂ = a A₂₂ − A₀₂²`. -/
def cb22 : ℤ := A 0 0 * A 2 2 - A 0 2 ^ 2
/-- `Δ = b₁₁ b₂₂ − b₁₂²`. -/
def cΔ : ℤ := cb11 A * cb22 A - cb12 A ^ 2

theorem Qf_expand (hsym : ∀ i j, A i j = A j i) (y : Fin 3 → ℤ) :
    Qf A y = A 0 0 * y 0 ^ 2 + A 1 1 * y 1 ^ 2 + A 2 2 * y 2 ^ 2 + 2 * A 0 1 * y 0 * y 1 +
      2 * A 0 2 * y 0 * y 2 + 2 * A 1 2 * y 1 * y 2 := by
  simp only [Qf, Fin.sum_univ_three]
  rw [hsym 1 0, hsym 2 0, hsym 2 1]
  ring

/-- **Completing the square twice.** -/
theorem key_identity (hsym : ∀ i j, A i j = A j i) (y : Fin 3 → ℤ) :
    ca A * cb11 A * Qf A y = cb11 A * (ca A * y 0 + A 0 1 * y 1 + A 0 2 * y 2) ^ 2 +
      (cb11 A * y 1 + cb12 A * y 2) ^ 2 + cΔ A * y 2 ^ 2 := by
  rw [Qf_expand A hsym]
  simp only [ca, cb11, cb12, cb22, cΔ]
  ring

end Coefficients

section Positivity

variable (A : Fin 3 → Fin 3 → ℤ) (hsym : ∀ i j, A i j = A j i)
  (hpos : ∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < Qf A y)

include hsym hpos in
theorem ca_pos : 0 < ca A := by
  have h := hpos ![1, 0, 0] (fun h => by simpa using congrFun h 0)
  rw [Qf_expand A hsym] at h
  simpa [ca] using h

include hsym hpos in
theorem cb11_pos : 0 < cb11 A := by
  have ha := ca_pos A hsym hpos
  have h := hpos ![-A 0 1, A 0 0, 0] (fun h => by
    have := congrFun h 1; exact (ne_of_gt ha) (by simpa [ca] using this))
  rw [Qf_expand A hsym] at h
  have e : A 0 0 * (-A 0 1) ^ 2 + A 1 1 * A 0 0 ^ 2 + A 2 2 * 0 ^ 2 + 2 * A 0 1 * (-A 0 1) * A 0 0 +
      2 * A 0 2 * (-A 0 1) * 0 + 2 * A 1 2 * A 0 0 * 0 = ca A * cb11 A := by
    simp only [ca, cb11]; ring
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h
  rw [e] at h
  exact pos_of_mul_pos_right h ha.le

include hsym hpos in
theorem cΔ_pos : 0 < cΔ A := by
  have ha := ca_pos A hsym hpos
  have hb := cb11_pos A hsym hpos
  set y : Fin 3 → ℤ := ![A 0 1 * cb12 A - A 0 2 * cb11 A, -(ca A * cb12 A), ca A * cb11 A] with hy
  have hy2 : y 2 = ca A * cb11 A := rfl
  have hyne : y ≠ 0 := fun h => by
    have h0 : ca A * cb11 A = 0 := by rw [← hy2]; exact congrFun h 2
    rcases mul_eq_zero.mp h0 with h1 | h1 <;> omega
  have hq := hpos y hyne
  have hk := key_identity A hsym y
  have hz : ca A * y 0 + A 0 1 * y 1 + A 0 2 * y 2 = 0 := by
    simp only [hy, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  have hX : cb11 A * y 1 + cb12 A * y 2 = 0 := by
    simp only [hy, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [hz, hX, hy2] at hk
  have hab : 0 < ca A * cb11 A := mul_pos ha hb
  have hQ : Qf A y = cΔ A * (ca A * cb11 A) := by
    apply mul_left_cancel₀ hab.ne'
    rw [hk]; ring
  rw [hQ] at hq
  exact pos_of_mul_pos_left hq hab.le

end Positivity

theorem solBox_zero_card_le {Δ : ℤ} (hΔ : 1 ≤ Δ) : (solBox Δ 0).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  have h1 := (mem_solBox hΔ).mp hv
  have h2 := (mem_solBox hΔ).mp hw
  simp only [Nat.cast_zero] at h1 h2
  have a1 : v.1 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg v.2]
  have a2 : v.2 = 0 := by nlinarith [sq_nonneg v.1, sq_nonneg v.2]
  have b1 : w.1 = 0 := by nlinarith [sq_nonneg w.1, sq_nonneg w.2]
  have b2 : w.2 = 0 := by nlinarith [sq_nonneg w.1, sq_nonneg w.2]
  exact Prod.ext (a1.trans b1.symm) (a2.trans b2.symm)

set_option maxHeartbeats 8000000 in
-- The case analysis and `omega`/`nlinarith` calls exceed the default heartbeat budget.
/-- **Ternary forms**: `#{y ∈ ℤ³ : Q(y) = N} ≤ C_ε N^{1/2+ε}`. -/
theorem ternary_count_le (A : Fin 3 → Fin 3 → ℤ) (hsym : ∀ i j, A i j = A j i)
    (hpos : ∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < Qf A y) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (Nat.card {y : Fin 3 → ℤ // Qf A y = N} : ℝ) ≤ C * (N : ℝ) ^ (1 / 2 + ε) := by
  classical
  have ha := ca_pos A hsym hpos
  have hb := cb11_pos A hsym hpos
  have hΔ := cΔ_pos A hsym hpos
  obtain ⟨C₂, hC₂, hbin⟩ := solBox_card_le_rpow (Δ := cΔ A) (by omega) hε
  set a := ca A with ha_def
  set b := cb11 A with hb_def
  set Δ := cΔ A with hΔ_def
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  refine ⟨3 * Real.sqrt a * (C₂ * ((b : ℝ) * a) ^ ε + 1), by positivity, fun N hN => ?_⟩
  set s := Nat.sqrt (a.toNat * N) with hs
  let Mz : ℤ → ℕ := fun z => (b * (a * N - z ^ 2)).toNat
  let T : Finset (Σ _ : ℤ, ℤ × ℤ) := (Finset.Icc (-(s : ℤ)) s).sigma (fun z => solBox Δ (Mz z))
  -- the injection `y ↦ (z, X, y₂)`
  have hmap : ∀ y : Fin 3 → ℤ, Qf A y = N →
      (⟨a * y 0 + A 0 1 * y 1 + A 0 2 * y 2, (b * y 1 + cb12 A * y 2, y 2)⟩ : Σ _ : ℤ,
          ℤ × ℤ) ∈ T := by
    intro y hy
    have hk := key_identity A hsym y
    rw [hy] at hk
    set z := a * y 0 + A 0 1 * y 1 + A 0 2 * y 2
    set X := b * y 1 + cb12 A * y 2
    have hz2 : z ^ 2 ≤ a * N := by
      have : b * z ^ 2 ≤ b * (a * N) := by nlinarith [sq_nonneg X, sq_nonneg (y 2)]
      exact le_of_mul_le_mul_left this hb
    simp only [T, Finset.mem_sigma, Finset.mem_Icc]
    refine ⟨?_, (mem_solBox (by omega)).mpr ?_⟩
    · have hnat : z.natAbs ≤ s := by
        rw [hs, Nat.le_sqrt']
        have : ((z.natAbs ^ 2 : ℕ) : ℤ) ≤ ((a.toNat * N : ℕ) : ℤ) := by
          push_cast
          rw [sq_abs, Int.toNat_of_nonneg ha.le]
          exact hz2
        exact_mod_cast this
      constructor <;> omega
    · simp only [Mz]
      rw [Int.toNat_of_nonneg (by nlinarith)]
      linarith
  let f : {y : Fin 3 → ℤ // Qf A y = N} → T := fun y => ⟨_, hmap y.1 y.2⟩
  have hf : Function.Injective f := by
    intro y y' hyy
    have h := congrArg Subtype.val hyy
    simp only [f, Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h2' := eq_of_heq h2
    simp only [Prod.mk.injEq] at h2'
    obtain ⟨hX, h22⟩ := h2'
    have h21 : y.1 1 = y'.1 1 := by
      rw [h22] at hX
      exact mul_left_cancel₀ hb.ne' (by linarith)
    have h20 : y.1 0 = y'.1 0 := by
      rw [h22, h21] at h1
      exact mul_left_cancel₀ ha.ne' (by linarith)
    apply Subtype.ext
    funext i
    fin_cases i
    · exact h20
    · exact h21
    · exact h22
  have hcard : Nat.card {y : Fin 3 → ℤ // Qf A y = N} ≤ T.card := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_finsetCard] at this
  -- each fibre over `z`
  have hfib : ∀ z ∈ Finset.Icc (-(s : ℤ)) s,
      ((solBox Δ (Mz z)).card : ℝ) ≤ C₂ * ((b : ℝ) * a) ^ ε * (N : ℝ) ^ ε + 1 := by
    intro z _
    rcases Nat.eq_zero_or_pos (Mz z) with h0 | hpos'
    · rw [h0]
      have := solBox_zero_card_le (Δ := Δ) (by omega)
      have : ((solBox Δ 0).card : ℝ) ≤ 1 := by exact_mod_cast this
      have : (0 : ℝ) ≤ C₂ * ((b : ℝ) * a) ^ ε * (N : ℝ) ^ ε := by positivity
      linarith
    · have h1 := hbin (Mz z) hpos'
      have hMle : (Mz z : ℝ) ≤ (b : ℝ) * a * N := by
        simp only [Mz]
        have : ((b * (a * N - z ^ 2)).toNat : ℤ) ≤ b * a * N := by
          rcases le_or_gt 0 (b * (a * N - z ^ 2)) with h | h
          · rw [Int.toNat_of_nonneg h]; nlinarith [sq_nonneg z]
          · rw [Int.toNat_of_nonpos h.le]; push_cast; positivity
        exact_mod_cast this
      have h2 : (Mz z : ℝ) ^ ε ≤ ((b : ℝ) * a) ^ ε * (N : ℝ) ^ ε := by
        rw [← Real.mul_rpow (by positivity) (Nat.cast_nonneg _)]
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) hMle hε.le
      calc ((solBox Δ (Mz z)).card : ℝ) ≤ C₂ * (Mz z : ℝ) ^ ε := h1
        _ ≤ C₂ * (((b : ℝ) * a) ^ ε * (N : ℝ) ^ ε) := by gcongr
        _ ≤ C₂ * ((b : ℝ) * a) ^ ε * (N : ℝ) ^ ε + 1 := by linarith
  -- the number of values of `z`
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have haN : (1 : ℝ) ≤ a * N := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hsR : (s : ℝ) ≤ Real.sqrt (a * N) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (by positivity)]
    have h1 : s ^ 2 ≤ a.toNat * N := Nat.sqrt_le' _
    have h2 : ((s ^ 2 : ℕ) : ℝ) ≤ ((a.toNat * N : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h2
    have : ((a.toNat : ℕ) : ℝ) = (a : ℝ) := by exact_mod_cast Int.toNat_of_nonneg ha.le
    rw [this] at h2
    exact h2
  have hcount : ((Finset.Icc (-(s : ℤ)) s).card : ℝ) ≤ 3 * Real.sqrt (a * N) := by
    rw [Int.card_Icc]
    have : ((s : ℤ) + 1 - -(s : ℤ)).toNat = 2 * s + 1 := by omega
    rw [this]
    push_cast
    have : 1 ≤ Real.sqrt (a * N) :=
        by rw [Real.le_sqrt (by norm_num) (by positivity)]; simpa using haN
    linarith
  have hT : (T.card : ℝ) ≤ 3 * Real.sqrt (a * N) *
      (C₂ * ((b : ℝ) * a) ^ ε * (N : ℝ) ^ ε + 1) := by
    rw [Finset.card_sigma]
    push_cast
    calc ∑ z ∈ Finset.Icc (-(s : ℤ)) s, ((solBox Δ (Mz z)).card : ℝ)
        ≤ ∑ _z ∈ Finset.Icc (-(s : ℤ)) s, (C₂ * ((b : ℝ) * a) ^ ε * (N : ℝ) ^ ε + 1) :=
          Finset.sum_le_sum hfib
      _ = ((Finset.Icc (-(s : ℤ)) s).card : ℝ) * (C₂ * ((b : ℝ) * a) ^ ε * (N : ℝ) ^ ε + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 3 * Real.sqrt (a * N) * (C₂ * ((b : ℝ) * a) ^ ε * (N : ℝ) ^ ε + 1) := by
          gcongr
  have hNe : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hNR hε.le
  have hsq : Real.sqrt (a * N) = Real.sqrt a * (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_mul haR.le]
    simp only [Real.sqrt_eq_rpow]
  have hpow : (N : ℝ) ^ (1 / 2 + ε) = (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ ε :=
    Real.rpow_add (by positivity) _ _
  calc (Nat.card {y : Fin 3 → ℤ // Qf A y = N} : ℝ) ≤ T.card := by exact_mod_cast hcard
    _ ≤ 3 * Real.sqrt (a * N) * (C₂ * ((b : ℝ) * a) ^ ε * (N : ℝ) ^ ε + 1) := hT
    _ ≤ 3 * Real.sqrt (a * N) * ((C₂ * ((b : ℝ) * a) ^ ε + 1) * (N : ℝ) ^ ε) := by
        gcongr
        nlinarith
    _ = 3 * Real.sqrt a * (C₂ * ((b : ℝ) * a) ^ ε + 1) * (N : ℝ) ^ (1 / 2 + ε) := by
        rw [hsq, hpow]; ring

/-- The solutions of `Q(y) = N` form a finite set. -/
theorem ternary_finite (A : Fin 3 → Fin 3 → ℤ) (hsym : ∀ i j, A i j = A j i)
    (hpos : ∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < Qf A y) (N : ℕ) :
    Finite {y : Fin 3 → ℤ // Qf A y = N} := by
  classical
  have ha := ca_pos A hsym hpos
  have hb := cb11_pos A hsym hpos
  have hΔ := cΔ_pos A hsym hpos
  set a := ca A
  set b := cb11 A
  set Δ := cΔ A
  set s := Nat.sqrt (a.toNat * N) with hs
  let Mz : ℤ → ℕ := fun z => (b * (a * N - z ^ 2)).toNat
  let T : Finset (Σ _ : ℤ, ℤ × ℤ) := (Finset.Icc (-(s : ℤ)) s).sigma (fun z => solBox Δ (Mz z))
  have hmap : ∀ y : Fin 3 → ℤ, Qf A y = N →
      (⟨a * y 0 + A 0 1 * y 1 + A 0 2 * y 2, (b * y 1 + cb12 A * y 2, y 2)⟩ : Σ _ : ℤ,
          ℤ × ℤ) ∈ T := by
    intro y hy
    have hk := key_identity A hsym y
    rw [hy] at hk
    set z := a * y 0 + A 0 1 * y 1 + A 0 2 * y 2
    set X := b * y 1 + cb12 A * y 2
    have hz2 : z ^ 2 ≤ a * N := by
      have : b * z ^ 2 ≤ b * (a * N) := by nlinarith [sq_nonneg X, sq_nonneg (y 2)]
      exact le_of_mul_le_mul_left this hb
    simp only [T, Finset.mem_sigma, Finset.mem_Icc]
    refine ⟨?_, (mem_solBox (by omega)).mpr ?_⟩
    · have hnat : z.natAbs ≤ s := by
        rw [hs, Nat.le_sqrt']
        have : ((z.natAbs ^ 2 : ℕ) : ℤ) ≤ ((a.toNat * N : ℕ) : ℤ) := by
          push_cast
          rw [sq_abs, Int.toNat_of_nonneg ha.le]
          exact hz2
        exact_mod_cast this
      constructor <;> omega
    · simp only [Mz]
      rw [Int.toNat_of_nonneg (by nlinarith)]
      linarith
  let f : {y : Fin 3 → ℤ // Qf A y = N} → T := fun y => ⟨_, hmap y.1 y.2⟩
  have hf : Function.Injective f := by
    intro y y' hyy
    have h := congrArg Subtype.val hyy
    simp only [f, Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h2' := eq_of_heq h2
    simp only [Prod.mk.injEq] at h2'
    obtain ⟨hX, h22⟩ := h2'
    have h21 : y.1 1 = y'.1 1 := by
      rw [h22] at hX
      exact mul_left_cancel₀ hb.ne' (by linarith)
    have h20 : y.1 0 = y'.1 0 := by
      rw [h22, h21] at h1
      exact mul_left_cancel₀ ha.ne' (by linarith)
    apply Subtype.ext
    funext i
    fin_cases i
    · exact h20
    · exact h21
    · exact h22
  exact Finite.of_injective f hf

end DSP
