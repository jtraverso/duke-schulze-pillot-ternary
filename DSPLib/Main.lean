/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DSPLib.Ternary
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Duke–Schulze-Pillot: the upper bound of Lemma 5(ii) and Theorem 3(ii)

`q(x) = ½ xᵗ A x` for a symmetric integer `3 × 3` matrix `A` with `q > 0` on `ℚ³ \ {0}`, and a
shift `h ∈ ℚ³`. `repCount A h n = #{x ∈ h + ℤ³ : q(x) = n}` and, for `F ⊆ ℝ³`,
`repCountF A h F n = #{x ∈ h + ℤ³ : q(x) = n, x/√n ∈ F}`.

* `repCount_le`: `r(q, h, n) ≤ C_ε n^{1/2+ε}`; `average_le`: the same for every weighted
  average of such counts, in particular for `r(spn_N q, h, n)` (the upper bound of Lemma 5(ii)).
* `thm3_ii`: Theorem 3(ii), `r(q, F, h, n) = r(spn_N q, h, n) μ(F) + O(n^{1/2 − 1/175 + ε})`,
  deduced from Theorem 1 and Theorem 3(i) of the paper, taken as hypotheses.
-/

@[expose] public section

namespace DSP

open Matrix

/-- `q(x) = ½ xᵗ A x`. -/
def qform (A : Matrix (Fin 3) (Fin 3) ℤ) (x : Fin 3 → ℚ) : ℚ :=
  (1 / 2 : ℚ) * (x ⬝ᵥ (A.map (Int.cast : ℤ → ℚ)) *ᵥ x)

/-- `r(q, h, n)`: the points of `h + ℤ³` on the ellipsoid `q(x) = n`. -/
noncomputable def repCount (A : Matrix (Fin 3) (Fin 3) ℤ) (h : Fin 3 → ℚ) (n : ℕ) : ℕ :=
  Nat.card {z : Fin 3 → ℤ // qform A (h + fun i => (z i : ℚ)) = n}

theorem qform_eq (A : Matrix (Fin 3) (Fin 3) ℤ) (x : Fin 3 → ℚ) :
    qform A x = (1 / 2 : ℚ) * ∑ i, ∑ j, (A i j : ℚ) * x i * x j := by
  unfold qform
  congr 1
  simp only [dotProduct, mulVec, Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- A common denominator for the shift. -/
theorem exists_denom (h : Fin 3 → ℚ) :
    ∃ (D : ℕ) (w : Fin 3 → ℤ), 0 < D ∧ ∀ i, (w i : ℚ) = D * h i := by
  refine ⟨∏ i, (h i).den, fun i => ((∏ j, (h j).den) / (h i).den : ℕ) * (h i).num,
    Finset.prod_pos fun i _ => (h i).den_pos, fun i => ?_⟩
  have hdvd : (h i).den ∣ ∏ j, (h j).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  obtain ⟨k, hk⟩ := hdvd
  have hk' : (∏ j, (h j).den) / (h i).den = k := by
    rw [hk, Nat.mul_div_cancel_left _ (h i).den_pos]
  have hden : ((h i).den : ℚ) ≠ 0 := by exact_mod_cast (h i).den_pos.ne'
  simp only [hk']
  rw [show ((∏ j, (h j).den : ℕ) : ℚ) = ((h i).den : ℚ) * k by exact_mod_cast hk]
  push_cast
  rw [show ((h i).den : ℚ) * k * h i = k * (h i * (h i).den) by ring, Rat.mul_den_eq_num]

theorem qform_smul (A : Matrix (Fin 3) (Fin 3) ℤ) (c : ℚ) (x : Fin 3 → ℚ) :
    qform A (fun i => c * x i) = c ^ 2 * qform A x := by
  rw [qform_eq, qform_eq]
  simp_rw [show ∀ i j, (A i j : ℚ) * (c * x i) * (c * x j) = c ^ 2 * ((A i j : ℚ) * x i * x j)
    from fun i j => by ring, ← Finset.mul_sum]
  ring

set_option maxHeartbeats 4000000 in
-- The case analysis and `omega`/`nlinarith` calls exceed the default heartbeat budget.
/-- **Upper bound of Lemma 5(ii)** for one form: `r(q, h, n) ≤ C_ε n^{1/2+ε}`. -/
theorem repCount_le (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm)
    (hpos : ∀ x : Fin 3 → ℚ, x ≠ 0 → 0 < qform A x) (h : Fin 3 → ℚ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (repCount A h n : ℝ) ≤ C * (n : ℝ) ^ (1 / 2 + ε) := by
  classical
  have hsym : ∀ i j, A i j = A j i := fun i j => by
    have := congrFun (congrFun hA i) j; simpa [Matrix.transpose_apply] using this.symm
  have hQ : ∀ y : Fin 3 → ℤ, (Qf A y : ℚ) = 2 * qform A (fun i => (y i : ℚ)) := by
    intro y
    rw [qform_eq]
    simp only [Qf]
    push_cast
    ring
  have hposZ : ∀ y : Fin 3 → ℤ, y ≠ 0 → 0 < Qf A y := by
    intro y hy
    have hx : (fun i => (y i : ℚ)) ≠ 0 := fun h0 => hy (funext fun i => by
      have := congrFun h0 i; simpa using this)
    have := hpos _ hx
    have h2 : (0 : ℚ) < Qf A y := by rw [hQ]; linarith
    exact_mod_cast h2
  obtain ⟨C₃, hC₃, hter⟩ := ternary_count_le (fun i j => A i j) hsym hposZ hε
  obtain ⟨D, w, hD, hw⟩ := exists_denom h
  refine ⟨C₃ * (2 * (D : ℝ) ^ 2) ^ (1 / 2 + ε), by positivity, fun n hn => ?_⟩
  -- `z ↦ D (h + z)` maps into the integer solutions of `Q(y) = 2 D² n`
  have hmapQ : ∀ z : Fin 3 → ℤ, qform A (h + fun i => (z i : ℚ)) = n →
      Qf A (fun i => w i + D * z i) = 2 * D ^ 2 * n := by
    intro z hz
    have e : (fun i => ((w i + D * z i : ℤ) : ℚ)) = fun i => (D : ℚ) * (h +
        fun i => (z i : ℚ)) i := by
      funext i; push_cast; rw [hw i]; simp; ring
    have h1 := hQ (fun i => w i + D * z i)
    rw [e] at h1
    have h2 : qform A (fun i => (D : ℚ) * (h + fun i => (z i : ℚ)) i) =
        (D : ℚ) ^ 2 * qform A (h + fun i => (z i : ℚ)) := qform_smul A _ _
    rw [h2, hz] at h1
    have : ((Qf A (fun i => w i + D * z i) : ℤ) : ℚ) = ((2 * D ^ 2 * n : ℤ) : ℚ) := by
      rw [h1]; push_cast; ring
    exact_mod_cast this
  let f : {z : Fin 3 → ℤ // qform A (h + fun i => (z i : ℚ)) = n} →
      {y : Fin 3 → ℤ // Qf (fun i j => A i j) y = (2 * D ^ 2 * n : ℕ)} :=
    fun z => ⟨fun i => w i + D * z.1 i, by rw [hmapQ z.1 z.2]; push_cast; ring⟩
  have hf : Function.Injective f := by
    intro z z' hzz
    apply Subtype.ext
    funext i
    have := congrFun (congrArg Subtype.val hzz) i
    simp only [f] at this
    have hDz : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
    exact mul_left_cancel₀ hDz (by linarith)
  have hcard : repCount A h n ≤ Nat.card {y : Fin 3 → ℤ // Qf (fun i j => A i j) y = (2 * D ^ 2 *
      n : ℕ)} := by
    have := ternary_finite (fun i j => A i j) hsym hposZ (2 * D ^ 2 * n)
    exact Nat.card_le_card_of_injective f hf
  have h2 := hter (2 * D ^ 2 * n) (Nat.one_le_iff_ne_zero.mpr (by positivity))
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (repCount A h n : ℝ) ≤ Nat.card {y : Fin 3 → ℤ // Qf (fun i j => A i j) y = (2 * D ^ 2 *
      n : ℕ)} := by
        exact_mod_cast hcard
    _ ≤ C₃ * ((2 * D ^ 2 * n : ℕ) : ℝ) ^ (1 / 2 + ε) := h2
    _ = C₃ * (2 * (D : ℝ) ^ 2) ^ (1 / 2 + ε) * (n : ℝ) ^ (1 / 2 + ε) := by
        push_cast
        rw [Real.mul_rpow (by positivity) hnR]
        ring

/-- **Upper bound of Lemma 5(ii)** for weighted averages (such as `r(spn_N q, h, n)`). -/
theorem average_le {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin 3) (Fin 3) ℤ)
    (hA : ∀ i ∈ s, (A i).IsSymm) (hpos : ∀ i ∈ s, ∀ x : Fin 3 → ℚ, x ≠ 0 → 0 < qform (A i) x)
    (h : ι → Fin 3 → ℚ) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (∑ i ∈ s, w i * repCount (A i) (h i) n) / (∑ i ∈ s, w i) ≤ C * (n : ℝ) ^ (1 / 2 + ε) := by
  classical
  have hC : ∀ i ∈ s, ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (repCount (A i) (h i) n : ℝ) ≤ C * (n : ℝ) ^ (1 / 2 + ε) :=
    fun i hi => repCount_le (A i) (hA i hi) (hpos i hi) (h i) hε
  choose! C hCpos hCb using hC
  refine ⟨∑ i ∈ s, C i + 1, by
    have : 0 ≤ ∑ i ∈ s, C i := Finset.sum_nonneg fun i hi => (hCpos i hi).le
    linarith, fun n hn => ?_⟩
  have hx : (0 : ℝ) ≤ (n : ℝ) ^ (1 / 2 + ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hW : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  have hCmax : ∀ i ∈ s, C i ≤ ∑ j ∈ s, C j + 1 := fun i hi => by
    have := Finset.single_le_sum (fun j hj => (hCpos j hj).le) hi
    linarith
  have hsum : ∑ i ∈ s, w i * repCount (A i) (h i) n ≤
      (∑ i ∈ s, w i) * ((∑ i ∈ s, C i + 1) * (n : ℝ) ^ (1 / 2 + ε)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hw i hi)
    exact (hCb i hi n hn).trans (mul_le_mul_of_nonneg_right (hCmax i hi) hx)
  rcases hW.lt_or_eq with hWpos | hW0
  · rw [div_le_iff₀ hWpos]
    linarith
  · rw [← hW0, div_zero]
    exact mul_nonneg (by
      have : 0 ≤ ∑ i ∈ s, C i := Finset.sum_nonneg fun i hi => (hCpos i hi).le
      linarith) hx

/-- `r(q, F, h, n)`: the points of `h + ℤ³` on `q(x) = n` with `x / √n ∈ F`. -/
noncomputable def repCountF (A : Matrix (Fin 3) (Fin 3) ℤ) (h : Fin 3 → ℚ) (F : Set (Fin 3 → ℝ))
    (n : ℕ) : ℕ :=
  Nat.card {z : Fin 3 → ℤ // qform A (h + fun i => (z i : ℚ)) = n ∧
    (fun i => ((h i + z i : ℚ) : ℝ) / Real.sqrt n) ∈ F}

/-- **Theorem 3(ii)**, from Theorem 1 and Theorem 3(i) of the paper (hypotheses `hThm1`,
`hThm3i`): `r(q, F, h, n) = R(n) μ(F) + O(n^{1/2 − 1/175 + ε})` on the restricted set `S`, where
`R(n) = r(spn_N q, h, n)`. -/
theorem thm3_ii (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm)
    (hpos : ∀ x : Fin 3 → ℚ, x ≠ 0 → 0 < qform A x) (h : Fin 3 → ℚ) (F : Set (Fin 3 → ℝ))
    (μF : ℝ) (hμ0 : 0 ≤ μF) (hμ1 : μF ≤ 1) (S : Set ℕ) (R : ℕ → ℝ)
    (hThm1 : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n ∈ S, 1 ≤ n →
      |(repCountF A h F n : ℝ) - repCount A h n * μF| ≤
        C * ((n : ℝ) ^ (-(1 / 175 : ℝ)) * repCount A h n + (n : ℝ) ^ (1 / 2 - 1 / 175 + ε)))
    (hThm3i : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n ∈ S, 1 ≤ n →
      |(repCount A h n : ℝ) - R n| ≤ C * (n : ℝ) ^ (1 / 2 - 1 / 28 + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n ∈ S, 1 ≤ n →
      |(repCountF A h F n : ℝ) - R n * μF| ≤ C * (n : ℝ) ^ (1 / 2 - 1 / 175 + ε) := by
  intro ε hε
  obtain ⟨C₁, hC₁⟩ := hThm1 ε hε
  obtain ⟨C₂, hC₂⟩ := hThm3i ε hε
  obtain ⟨C₃, hC₃, hr⟩ := repCount_le A hA hpos h hε
  refine ⟨|C₁| * (C₃ + 1) + |C₂|, fun n hn hn1 => ?_⟩
  have hx1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hx0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hxα : 0 ≤ (n : ℝ) ^ (1 / 2 - 1 / 175 + ε) := Real.rpow_nonneg hx0.le _
  have h1 := hC₁ n hn hn1
  have h2 := hC₂ n hn hn1
  have h3 := hr n hn1
  -- `n^{-1/175} (repCount A h n : ℝ) ≤ C₃ n^(1 / 2 - 1 / 175 + ε)`
  have hdecay : (n : ℝ) ^ (-(1 / 175 : ℝ)) * (repCount A h n : ℝ) ≤ C₃ * (n : ℝ) ^ (1 / 2 -
      1 / 175 + ε) := by
    calc (n : ℝ) ^ (-(1 / 175 : ℝ)) * (repCount A h n : ℝ) ≤ (n : ℝ) ^ (-(1 / 175 : ℝ)) * (C₃ *
        (n : ℝ) ^ (1 / 2 + ε)) :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hx0.le _)
      _ = C₃ * ((n : ℝ) ^ (-(1 / 175 : ℝ)) * (n : ℝ) ^ (1 / 2 + ε)) := by ring
      _ = C₃ * (n : ℝ) ^ (1 / 2 - 1 / 175 + ε) := by
          rw [← Real.rpow_add hx0]; congr 2; ring
  have hX : 0 ≤ (n : ℝ) ^ (-(1 / 175 : ℝ)) * (repCount A h n : ℝ) + (n : ℝ) ^ (1 / 2 - 1 / 175 +
      ε) :=
    add_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (Nat.cast_nonneg _)) hxα
  have hA1 : |(repCountF A h F n : ℝ) - (repCount A h n : ℝ) * μF| ≤ |C₁| * (C₃ + 1) *
      (n : ℝ) ^ (1 / 2 - 1 / 175 + ε) := by
    calc |(repCountF A h F n : ℝ) - (repCount A h n : ℝ) * μF| ≤ C₁ *
        ((n : ℝ) ^ (-(1 / 175 : ℝ)) * (repCount A h n : ℝ) + (n : ℝ) ^ (1 / 2 - 1 / 175 + ε)) := h1
      _ ≤ |C₁| * ((n : ℝ) ^ (-(1 / 175 : ℝ)) * (repCount A h n : ℝ) + (n : ℝ) ^ (1 / 2 - 1 / 175 +
          ε)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hX
      _ ≤ |C₁| * (C₃ * (n : ℝ) ^ (1 / 2 - 1 / 175 + ε) + (n : ℝ) ^ (1 / 2 - 1 / 175 + ε)) :=
          by gcongr
      _ = |C₁| * (C₃ + 1) * (n : ℝ) ^ (1 / 2 - 1 / 175 + ε) := by ring
  have hA2 : |(repCount A h n : ℝ) - R n| * μF ≤ |C₂| * (n : ℝ) ^ (1 / 2 - 1 / 175 + ε) := by
    have hexp : (n : ℝ) ^ (1 / 2 - 1 / 28 + ε) ≤ (n : ℝ) ^ (1 / 2 - 1 / 175 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    calc |(repCount A h n : ℝ) - R n| * μF ≤ |(repCount A h n : ℝ) - R n| * 1 :=
        mul_le_mul_of_nonneg_left hμ1 (abs_nonneg _)
      _ = |(repCount A h n : ℝ) - R n| := mul_one _
      _ ≤ C₂ * (n : ℝ) ^ (1 / 2 - 1 / 28 + ε) := h2
      _ ≤ |C₂| * (n : ℝ) ^ (1 / 2 - 1 / 28 + ε) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hx0.le _)
      _ ≤ |C₂| * (n : ℝ) ^ (1 / 2 - 1 / 175 + ε) := mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
  calc |(repCountF A h F n : ℝ) - R n * μF| = |((repCountF A h F n : ℝ) - (repCount A h n : ℝ) *
      μF) + ((repCount A h n : ℝ) - R n) * μF| := by ring_nf
    _ ≤ |(repCountF A h F n : ℝ) - (repCount A h n : ℝ) * μF| + |((repCount A h n : ℝ) - R n) *
        μF| := abs_add_le _ _
    _ = |(repCountF A h F n : ℝ) - (repCount A h n : ℝ) * μF| + |(repCount A h n : ℝ) - R n| *
        μF := by rw [abs_mul, abs_of_nonneg hμ0]
    _ ≤ |C₁| * (C₃ + 1) * (n : ℝ) ^ (1 / 2 - 1 / 175 + ε) + |C₂| * (n : ℝ) ^ (1 / 2 - 1 / 175 +
        ε) := add_le_add hA1 hA2
    _ = (|C₁| * (C₃ + 1) + |C₂|) * (n : ℝ) ^ (1 / 2 - 1 / 175 + ε) := by ring

/-- The main term inherits the upper bound of Lemma 5(ii) from Theorem 3(i). -/
theorem spn_upper (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm)
    (hpos : ∀ x : Fin 3 → ℚ, x ≠ 0 → 0 < qform A x) (h : Fin 3 → ℚ) (S : Set ℕ) (R : ℕ → ℝ)
    (hThm3i : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n ∈ S, 1 ≤ n →
      |(repCount A h n : ℝ) - R n| ≤ C * (n : ℝ) ^ (1 / 2 - 1 / 28 + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n ∈ S, 1 ≤ n → R n ≤ C * (n : ℝ) ^ (1 / 2 + ε) := by
  intro ε hε
  obtain ⟨C₂, hC₂⟩ := hThm3i ε hε
  obtain ⟨C₃, hC₃, hr⟩ := repCount_le A hA hpos h hε
  refine ⟨C₃ + |C₂|, fun n hn hn1 => ?_⟩
  have hx1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hexp : (n : ℝ) ^ (1 / 2 - 1 / 28 + ε) ≤ (n : ℝ) ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have h2 := hC₂ n hn hn1
  have h3 := hr n hn1
  have h4 : R n ≤ repCount A h n + |(repCount A h n : ℝ) - R n| := by
    have := neg_abs_le ((repCount A h n : ℝ) - R n); linarith
  have hpow : 0 ≤ (n : ℝ) ^ (1 / 2 - 1 / 28 + ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc R n ≤ repCount A h n + |(repCount A h n : ℝ) - R n| := h4
    _ ≤ C₃ * (n : ℝ) ^ (1 / 2 + ε) + |C₂| * (n : ℝ) ^ (1 / 2 + ε) := by
        gcongr
        calc |(repCount A h n : ℝ) - R n| ≤ C₂ * (n : ℝ) ^ (1 / 2 - 1 / 28 + ε) := h2
          _ ≤ |C₂| * (n : ℝ) ^ (1 / 2 - 1 / 28 + ε) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) hpow
          _ ≤ |C₂| * (n : ℝ) ^ (1 / 2 + ε) := mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
    _ = (C₃ + |C₂|) * (n : ℝ) ^ (1 / 2 + ε) := by ring

end DSP
