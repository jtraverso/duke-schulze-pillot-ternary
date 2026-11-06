/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DSPLib.SqrtMod

/-!
# Representations by `X² + ΔY²`

For `Δ ≥ 1` and `M ≥ 1`, a primitive solution `(X, Y)` of `X² + ΔY² = M` gives the square root
`X Y⁻¹` of `-Δ` modulo `M`; a fibre of this map has at most four elements, because
`(X₀² + ΔY₀²)(X² + ΔY²) = (X₀X + ΔY₀Y)² + Δ(X₀Y − XY₀)²` with `M ∣ X₀Y − XY₀` leaves only the
values `(0, ±M)` and `(±M, 0)` for `(X₀Y − XY₀, X₀X + ΔY₀Y)` (`primBox_card_le`).
-/

@[expose] public section

namespace DSP

/-- The integer solutions of `X² + ΔY² = M` (all lie in the box `[-M, M]²`). -/
def solBox (Δ : ℤ) (M : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(M : ℤ)) M ×ˢ Finset.Icc (-(M : ℤ)) M).filter
    (fun v => v.1 ^ 2 + Δ * v.2 ^ 2 = M)

/-- The primitive solutions. -/
def primBox (Δ : ℤ) (M : ℕ) : Finset (ℤ × ℤ) :=
  (solBox Δ M).filter (fun v => Int.gcd v.1 v.2 = 1)

theorem mem_solBox {Δ : ℤ} (hΔ : 1 ≤ Δ) {M : ℕ} {v : ℤ × ℤ} :
    v ∈ solBox Δ M ↔ v.1 ^ 2 + Δ * v.2 ^ 2 = M := by
  unfold solBox
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, h⟩ <;> nlinarith [sq_nonneg v.1, sq_nonneg v.2, sq_abs v.1,
      sq_abs v.2, abs_nonneg v.1, abs_nonneg v.2, neg_abs_le v.1, le_abs_self v.1,
      neg_abs_le v.2, le_abs_self v.2]

/-- The fibre values. -/
def fibreVals (M : ℕ) : Finset (ℤ × ℤ) :=
  [((0 : ℤ), (M : ℤ)), (0, -(M : ℤ)), ((M : ℤ), 0), (-(M : ℤ), 0)].toFinset

theorem fibreVals_card (M : ℕ) : (fibreVals M).card ≤ 4 :=
  (List.toFinset_card_le _).trans (by simp)

/-- Two solutions congruent modulo `M` in the sense `M ∣ X₀Y − XY₀`. -/
theorem fibre_mem {Δ : ℤ} (hΔ : 1 ≤ Δ) {M : ℕ} {X₀ Y₀ X Y : ℤ}
    (h₀ : X₀ ^ 2 + Δ * Y₀ ^ 2 = M) (h : X ^ 2 + Δ * Y ^ 2 = M)
    (hd : (M : ℤ) ∣ X₀ * Y - X * Y₀) :
    (X₀ * Y - X * Y₀, X₀ * X + Δ * Y₀ * Y) ∈ fibreVals M := by
  set D := X₀ * Y - X * Y₀ with hD
  set E := X₀ * X + Δ * Y₀ * Y with hE
  have hid : (M : ℤ) * M = E ^ 2 + Δ * D ^ 2 := by
    rw [show (M : ℤ) * M = (X₀ ^ 2 + Δ * Y₀ ^ 2) * (X ^ 2 + Δ * Y ^ 2) by rw [h₀, h], hD, hE]
    ring
  have hM0 : (0 : ℤ) ≤ M := Nat.cast_nonneg M
  obtain ⟨k, hk⟩ := hd
  have hk1 : k ^ 2 * (M : ℤ) ^ 2 ≤ (M : ℤ) ^ 2 := by
    have : Δ * D ^ 2 ≤ (M : ℤ) * M := by nlinarith [sq_nonneg E]
    rw [hk] at this
    nlinarith [sq_nonneg ((M : ℤ) * k), sq_nonneg (k : ℤ)]
  unfold fibreVals
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  rcases Nat.eq_zero_or_pos M with hM | hM
  · -- `M = 0`: every term vanishes
    subst hM
    have hE0 : E = 0 := by simp at hid; nlinarith [sq_nonneg E, sq_nonneg D]
    simp only [Nat.cast_zero, zero_mul] at hk
    left; exact ⟨hk, hE0⟩
  have hMpos : (0 : ℤ) < M := by exact_mod_cast hM
  have hk2 : k ^ 2 ≤ 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith [sq_nonneg (M : ℤ)]
  have hkv : k = 0 ∨ k = 1 ∨ k = -1 := by
    have : -1 ≤ k ∧ k ≤ 1 := ⟨by nlinarith, by nlinarith⟩
    omega
  rcases hkv with rfl | rfl | rfl
  · -- `D = 0`, `E = ±M`
    rw [mul_zero] at hk
    rw [hk] at hid
    have hE2 : E ^ 2 = (M : ℤ) ^ 2 := by nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hE2 with he | he
    · left; exact ⟨hk, he⟩
    · right; left; exact ⟨hk, he⟩
  · -- `D = M`: then `Δ = 1` and `E = 0`
    rw [mul_one] at hk
    rw [hk] at hid
    have hE0 : E = 0 := by nlinarith [sq_nonneg E]
    right; right; left; exact ⟨hk, hE0⟩
  · rw [show (M : ℤ) * -1 = -M by ring] at hk
    rw [hk] at hid
    have hE0 : E = 0 := by nlinarith [sq_nonneg E]
    right; right; right; exact ⟨hk, hE0⟩

theorem coprime_of_prim {Δ X Y : ℤ} {M : ℕ} (h : X ^ 2 + Δ * Y ^ 2 = M)
    (hg : Int.gcd X Y = 1) : IsCoprime Y (M : ℤ) := by
  have h1 : IsCoprime X Y := Int.isCoprime_iff_gcd_eq_one.mpr hg
  have h2 : IsCoprime Y (X ^ 2) := h1.symm.pow_right
  rw [← h]
  have := h2.add_mul_left_right (Δ * Y)
  convert this using 1
  ring

theorem isUnit_of_coprime {Y : ℤ} {M : ℕ} (h : IsCoprime Y (M : ℤ)) : IsUnit (Y : ZMod M) := by
  obtain ⟨u, v, huv⟩ := h
  have h1 := congrArg (Int.cast : ℤ → ZMod M) huv
  push_cast at h1
  rw [ZMod.natCast_self, mul_zero, add_zero] at h1
  exact ⟨⟨(Y : ZMod M), (u : ZMod M), by rw [mul_comm]; exact h1, h1⟩, rfl⟩

set_option maxHeartbeats 4000000 in
-- The case analysis and `omega`/`nlinarith` calls exceed the default heartbeat budget.
/-- **Primitive solutions**: at most four for each square root of `-Δ` modulo `M`. -/
theorem primBox_card_le {Δ : ℤ} (hΔ : 1 ≤ Δ) {M : ℕ} (hM : 1 ≤ M) :
    (primBox Δ M).card ≤ 4 * rootCount (-Δ) M := by
  classical
  have : NeZero M := ⟨by omega⟩
  let φ : ℤ × ℤ → ZMod M := fun v => (v.1 : ZMod M) * (v.2 : ZMod M)⁻¹
  have hmem : ∀ v ∈ primBox Δ M, v.1 ^ 2 + Δ * v.2 ^ 2 = M ∧ IsUnit (v.2 : ZMod M) := by
    intro v hv
    simp only [primBox, Finset.mem_filter] at hv
    have h1 := (mem_solBox hΔ).mp hv.1
    exact ⟨h1, isUnit_of_coprime (coprime_of_prim h1 hv.2)⟩
  have hroot : ∀ v ∈ primBox Δ M, φ v ^ 2 = ((-Δ : ℤ) : ZMod M) := by
    intro v hv
    obtain ⟨h1, hu⟩ := hmem v hv
    have hc : (v.1 : ZMod M) ^ 2 = -((Δ : ZMod M) * (v.2 : ZMod M) ^ 2) := by
      have := congrArg (Int.cast : ℤ → ZMod M) h1
      push_cast at this
      rw [ZMod.natCast_self] at this
      linear_combination this
    have hinv : (v.2 : ZMod M) * (v.2 : ZMod M)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
    simp only [φ]
    rw [mul_pow, hc]
    push_cast
    linear_combination (-(Δ : ZMod M) * ((v.2 : ZMod M) * (v.2 : ZMod M)⁻¹ + 1)) * hinv
  have hcard_img : ((primBox Δ M).image φ).card ≤ rootCount (-Δ) M := by
    unfold rootCount
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply Finset.card_le_card
    intro t ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hroot v hv
  refine (Finset.card_le_mul_card_image _ 4 ?_).trans (Nat.mul_le_mul_left 4 hcard_img)
  intro t ht
  obtain ⟨v₀, hv₀, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨h₀, hu₀⟩ := hmem v₀ hv₀
  have hinv₀ : (v₀.2 : ZMod M) * (v₀.2 : ZMod M)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu₀
  calc ((primBox Δ M).filter (fun v => φ v = φ v₀)).card ≤ (fibreVals M).card := by
        apply Finset.card_le_card_of_injOn
          (fun v => (v₀.1 * v.2 - v.1 * v₀.2, v₀.1 * v.1 + Δ * v₀.2 * v.2))
        · intro v hv
          simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hv
          obtain ⟨h, hu⟩ := hmem v hv.1
          have hinv : (v.2 : ZMod M) * (v.2 : ZMod M)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
          have heq : (v.1 : ZMod M) * (v.2 : ZMod M)⁻¹ = (v₀.1 : ZMod M) * (v₀.2 : ZMod M)⁻¹ := hv.2
          have hd : (M : ℤ) ∣ v₀.1 * v.2 - v.1 * v₀.2 := by
            apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
            push_cast
            linear_combination (-((v.2 : ZMod M) * (v₀.2 : ZMod M))) * heq +
              ((v.1 : ZMod M) * (v₀.2 : ZMod M)) * hinv - ((v₀.1 : ZMod M) * (v.2 : ZMod M)) * hinv₀
          exact fibre_mem hΔ h₀ h hd
        · intro v hv w hw hvw
          simp only [Prod.mk.injEq] at hvw
          have hMz : (M : ℤ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
          have h1 : (M : ℤ) * (v.1 - w.1) = 0 := by
            rw [← h₀]; linear_combination (v₀.1) * hvw.2 - (Δ * v₀.2) * hvw.1
          have h2 : (M : ℤ) * (v.2 - w.2) = 0 := by
            rw [← h₀]; linear_combination (v₀.2) * hvw.2 + (v₀.1) * hvw.1
          have e1 := (mul_eq_zero.mp h1).resolve_left hMz
          have e2 := (mul_eq_zero.mp h2).resolve_left hMz
          exact Prod.ext (by linarith) (by linarith)
    _ ≤ 4 := fibreVals_card M

set_option maxHeartbeats 4000000 in
-- The case analysis and `omega`/`nlinarith` calls exceed the default heartbeat budget.
/-- **All solutions**: `#{X² + ΔY² = M} ≤ 4 K d(M)²` with `K = (2Δ)^{Δ+2}`. -/
theorem solBox_card_le {Δ : ℤ} (hΔ : 1 ≤ Δ) {M : ℕ} (hM : 1 ≤ M) :
    (solBox Δ M).card ≤
      M.divisors.card * (4 * ((2 * (-Δ).natAbs) ^ ((-Δ).natAbs + 2) * M.divisors.card)) := by
  classical
  set K := (2 * (-Δ).natAbs) ^ ((-Δ).natAbs + 2) with hK
  have hΔ0 : -Δ ≠ 0 := by omega
  -- the gcd of a solution divides `M`
  have hgcd : ∀ v ∈ solBox Δ M, Int.gcd v.1 v.2 ∈ M.divisors := by
    intro v hv
    have h := (mem_solBox hΔ).mp hv
    rw [Nat.mem_divisors]
    refine ⟨?_, by omega⟩
    have h1 : ((Int.gcd v.1 v.2 : ℕ) : ℤ) ∣ v.1 := Int.gcd_dvd_left _ _
    have h2 : ((Int.gcd v.1 v.2 : ℕ) : ℤ) ∣ v.2 := Int.gcd_dvd_right _ _
    have h3 : ((Int.gcd v.1 v.2 : ℕ) : ℤ) ∣ (M : ℤ) := by
      rw [← h]
      exact dvd_add (dvd_pow h1 (by norm_num)) (dvd_mul_of_dvd_right (dvd_pow h2 (by norm_num)) _)
    exact_mod_cast h3
  rw [Finset.card_eq_sum_card_fiberwise hgcd]
  calc ∑ g ∈ M.divisors, ((solBox Δ M).filter (fun v => Int.gcd v.1 v.2 = g)).card
      ≤ ∑ _g ∈ M.divisors, 4 * (K * M.divisors.card) := by
        apply Finset.sum_le_sum
        intro g hg
        have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
        by_cases hfib : ((solBox Δ M).filter (fun v => Int.gcd v.1 v.2 = g)).Nonempty
        swap
        · rw [Finset.not_nonempty_iff_eq_empty.mp hfib]; simp
        -- `g² ∣ M`
        obtain ⟨v₁, hv₁⟩ := hfib
        simp only [Finset.mem_filter] at hv₁
        have hg2 : g ^ 2 ∣ M := by
          have h := (mem_solBox hΔ).mp hv₁.1
          obtain ⟨a, ha⟩ : (g : ℤ) ∣ v₁.1 := hv₁.2 ▸ Int.gcd_dvd_left _ _
          obtain ⟨b, hb⟩ : (g : ℤ) ∣ v₁.2 := hv₁.2 ▸ Int.gcd_dvd_right _ _
          have : ((g ^ 2 : ℕ) : ℤ) ∣ (M : ℤ) :=
            ⟨a ^ 2 + Δ * b ^ 2, by rw [← h, ha, hb]; push_cast; ring⟩
          exact_mod_cast this
        have hMg : 1 ≤ M / g ^ 2 :=
          (Nat.one_le_div_iff (by positivity)).mpr (Nat.le_of_dvd (by omega) hg2)
        calc ((solBox Δ M).filter (fun v => Int.gcd v.1 v.2 = g)).card
            ≤ (primBox Δ (M / g ^ 2)).card := by
              apply Finset.card_le_card_of_injOn (fun v : ℤ × ℤ => (v.1 / (g : ℤ), v.2 / (g : ℤ)))
              · intro v hv
                simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hv
                have h := (mem_solBox hΔ).mp hv.1
                obtain ⟨a, ha⟩ : (g : ℤ) ∣ v.1 := hv.2 ▸ Int.gcd_dvd_left _ _
                obtain ⟨b, hb⟩ : (g : ℤ) ∣ v.2 := hv.2 ▸ Int.gcd_dvd_right _ _
                have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
                have ea : v.1 / g = a := by rw [ha]; exact Int.mul_ediv_cancel_left _ hgz
                have eb : v.2 / g = b := by rw [hb]; exact Int.mul_ediv_cancel_left _ hgz
                simp only [Finset.mem_coe, primBox, Finset.mem_filter]
                rw [ea, eb]
                refine ⟨(mem_solBox hΔ).mpr ?_, ?_⟩
                · have hM' : ((M / g ^ 2 : ℕ) : ℤ) * (g : ℤ) ^ 2 = M := by
                    have := Nat.div_mul_cancel hg2; exact_mod_cast this
                  have hgg : (g : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ hgz
                  apply mul_right_cancel₀ hgg
                  rw [hM', ← h, ha, hb]; ring
                · have := Int.gcd_div_gcd_div_gcd (i := v.1) (j := v.2) (by rw [hv.2]; exact hg0)
                  rw [hv.2, ea, eb] at this
                  exact this
              · intro v hv w hw hvw
                simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hv hw
                simp only [Prod.mk.injEq] at hvw
                have hgz : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
                have a1 := Int.ediv_mul_cancel (hv.2 ▸ Int.gcd_dvd_left v.1 v.2 : (g : ℤ) ∣ v.1)
                have a2 := Int.ediv_mul_cancel (hw.2 ▸ Int.gcd_dvd_left w.1 w.2 : (g : ℤ) ∣ w.1)
                have b1 := Int.ediv_mul_cancel (hv.2 ▸ Int.gcd_dvd_right v.1 v.2 : (g : ℤ) ∣ v.2)
                have b2 := Int.ediv_mul_cancel (hw.2 ▸ Int.gcd_dvd_right w.1 w.2 : (g : ℤ) ∣ w.2)
                have e1 : v.1 = w.1 := by rw [← a1, ← a2, hvw.1]
                have e2 : v.2 = w.2 := by rw [← b1, ← b2, hvw.2]
                exact Prod.ext e1 e2
          _ ≤ 4 * rootCount (-Δ) (M / g ^ 2) := primBox_card_le hΔ hMg
          _ ≤ 4 * (K * (M / g ^ 2).divisors.card) :=
              Nat.mul_le_mul_left 4 (rootCount_le hΔ0 (by omega))
          _ ≤ 4 * (K * M.divisors.card) := by
              apply Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left K _)
              exact Finset.card_le_card (Nat.divisors_subset_of_dvd (by omega)
                (Nat.div_dvd_of_dvd hg2))
    _ = M.divisors.card * (4 * (K * M.divisors.card)) := by rw [Finset.sum_const, smul_eq_mul]

/-- **Representations by `X² + ΔY²`**: at most `C_ε M^ε`. -/
theorem solBox_card_le_rpow {Δ : ℤ} (hΔ : 1 ≤ Δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → ((solBox Δ M).card : ℝ) ≤ C * (M : ℝ) ^ ε := by
  obtain ⟨C₁, hC₁, hd⟩ := card_divisors_le_rpow (half_pos hε)
  set K : ℝ := (((2 * (-Δ).natAbs) ^ ((-Δ).natAbs + 2) : ℕ) : ℝ)
  refine ⟨4 * K * C₁ ^ 2 + 1, by positivity, fun M hM => ?_⟩
  have h1 := solBox_card_le hΔ hM
  have h2 := hd M (by omega)
  have hpos : (0 : ℝ) ≤ (M : ℝ) ^ (ε / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsq : ((M : ℝ) ^ (ε / 2)) ^ 2 = (M : ℝ) ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
  have hd0 : (0 : ℝ) ≤ M.divisors.card := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  calc ((solBox Δ M).card : ℝ) ≤ (M.divisors.card : ℝ) * (4 * (K * M.divisors.card)) := by
        simp only [K]; exact_mod_cast h1
    _ = 4 * K * (M.divisors.card : ℝ) ^ 2 := by ring
    _ ≤ 4 * K * (C₁ * (M : ℝ) ^ (ε / 2)) ^ 2 := by gcongr
    _ = 4 * K * C₁ ^ 2 * (M : ℝ) ^ ε := by rw [mul_pow, hsq]; ring
    _ ≤ (4 * K * C₁ ^ 2 + 1) * (M : ℝ) ^ ε := by
        have : (0 : ℝ) ≤ (M : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg _) _
        nlinarith

end DSP
