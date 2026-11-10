/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.Glue2
public import DukeH1.TBound

/-!
# Helper lemmas for the per-level inequality

`chiR` is multiplicative; `rph` absorbs a unit; `Γ_r` and `e_r` only see residues mod `r`;
`|Γ_r(x)| ≤ √(2r)` on units; classes of non-units carry no rough integers.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open ZMod Finset

theorem chiR_mul (n x y : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) : chiR n (x * y) = chiR n x * chiR n y := by
  haveI : NeZero x := ⟨hx⟩
  haveI : NeZero y := ⟨hy⟩
  unfold chiR
  by_cases h1 : Rough (S2 n) x
  · by_cases h2 : Rough (S2 n) y
    · rw [if_pos (rough_mul_iff.mpr ⟨h1, h2⟩), if_pos h1, if_pos h2, jacobiSym.mul_right]; push_cast; ring
    · rw [if_neg (fun h => h2 (rough_mul_iff.mp h).2), if_neg h2, mul_zero]
  · rw [if_neg (fun h => h1 (rough_mul_iff.mp h).1), if_neg h1, zero_mul]

theorem norm_chiR_le (n m : ℕ) : ‖chiR n m‖ ≤ 1 := by
  unfold chiR
  split_ifs
  · rcases jacobiSym.trichotomy (-(n : ℤ)) m with h | h | h <;> rw [h] <;> simp
  · simp

/-- `e_b(h \overline{r x}) = e_b(h r̄ \overline{x})` with an integer representative of `h r̄`. -/
noncomputable def hInv (h : ℤ) (r b : ℕ) : ℤ :=
  if hb : b = 0 then 0 else ((@HMul.hMul (ZMod b) (ZMod b) (ZMod b) _ (h : ZMod b) ((r : ZMod b))⁻¹).val : ℤ)

theorem rph_mul_r (h : ℤ) (r b x : ℕ) (hb : 0 < b) (hrb : r.Coprime b) :
    rph b h ((r * x : ℕ) : ℤ) = rph b (hInv h r b) (x : ℤ) := by
  haveI : NeZero b := ⟨hb.ne'⟩
  unfold rph hInv
  rw [dif_neg hb.ne', dif_neg hb.ne', dif_neg hb.ne']
  have hu : IsUnit (r : ZMod b) := by rw [ZMod.isUnit_iff_coprime]; exact hrb
  push_cast
  rw [reciprocalPhase_mul_unit _ _ _ _ hu]
  congr 1
  simp

theorem rph_mod (b : ℕ) (h : ℤ) (x : ℕ) : rph b h (x : ℤ) = rph b h ((x % b : ℕ) : ℤ) := by
  unfold rph
  split_ifs with hb
  · rfl
  · congr 1
    haveI : NeZero b := ⟨hb⟩
    simp

theorem Gam_mod (n r x : ℕ) : Gam n r x = Gam n r (x % r) := by
  unfold Gam
  split_ifs with hr
  · rfl
  · rw [ZMod.natCast_mod]

theorem norm_Gam_le (n m x : ℕ) (hm : 0 < m) (hx : IsUnit ((x : ZMod (4 * m)))) :
    ‖Gam n (4 * m) x‖ ≤ Real.sqrt (2 * (4 * m : ℕ)) := by
  unfold Gam
  rw [dif_neg (by omega)]
  haveI : NeZero (4 * m) := ⟨by omega⟩
  rw [norm_div, Complex.norm_natCast]
  have hu : IsUnit (((x : ZMod (4 * m)))⁻¹) := by
    rw [← hx.unit_spec, ZMod.inv_coe_unit]; exact Units.isUnit _
  have := norm_Tq_four_le m hm _ (n : ZMod (4 * m)) hu
  have h4 : (0 : ℝ) < ((4 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 4 * m)
  rw [div_le_iff₀ h4]
  linarith [this]

theorem chiR_eq_zero_of_not_unit (n r a : ℕ) (hr : Smooth (S2 n) r) (ha : ¬ IsUnit ((a : ZMod r))) :
    chiR n a = 0 := by
  unfold chiR
  rw [if_neg]
  intro hro
  apply ha
  rw [ZMod.isUnit_iff_coprime]
  by_contra hc
  obtain ⟨ℓ, hℓ, h1, h2⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  exact hro ℓ hℓ h1 (hr ℓ hℓ h2)

end ThreeSquares
