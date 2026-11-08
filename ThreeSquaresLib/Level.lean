/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.FundDom
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Cosets of `Γ₀(Q)` and unfolding at level `Q`

* `key Q σ`: the orbit of the bottom row of `σ` mod `Q` under `(ℤ/Q)ˣ`; two matrices lie in the
  same right coset of `Γ₀(Q)` iff they have the same key (`dvd_iff_key_eq`).
* `Keys Q`: the (finite) set of keys, i.e. the right cosets `Γ₀(Q)\SL(2, ℤ)`, with representatives
  `pick Q k`; `card_keys_mul_totient`: `#Keys · φ(Q) ≤ Q²`.
* `unfold_level`: `∑_k ∫_𝒟 ∑_{r : rows, Q ∣ r₀} ψ(γ_r σ_k z) = 2 ∫_{strip} ψ` for `T`-periodic
  measurable `ψ ≥ 0`.
-/

@[expose] public section

namespace ThreeSquares.FD

open UpperHalfPlane ModularGroup MeasureTheory Matrix.SpecialLinearGroup

open scoped MatrixGroups

theorem inv_10 (σ : SL(2, ℤ)) : σ⁻¹ 1 0 = -σ 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem inv_11 (σ : SL(2, ℤ)) : σ⁻¹ 1 1 = σ 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem mul_10' (g h : SL(2, ℤ)) : (g * h) 1 0 = g 1 0 * h 0 0 + g 1 1 * h 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_11' (g h : SL(2, ℤ)) : (g * h) 1 1 = g 1 0 * h 0 1 + g 1 1 * h 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem det2 (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have := g.det_coe
  rwa [Matrix.det_fin_two] at this

/-- `Γ₀(Q)` membership. -/
def InG0 (Q : ℕ) (g : SL(2, ℤ)) : Prop := (Q : ℤ) ∣ g 1 0

theorem inG0_mul {Q : ℕ} {g h : SL(2, ℤ)} (hg : InG0 Q g) (hh : InG0 Q h) : InG0 Q (g * h) := by
  unfold InG0 at *
  rw [mul_10']
  exact dvd_add (dvd_mul_of_dvd_left hg _) (dvd_mul_of_dvd_right hh _)

theorem inG0_inv {Q : ℕ} {g : SL(2, ℤ)} (hg : InG0 Q g) : InG0 Q g⁻¹ := by
  unfold InG0 at *
  rw [inv_10]; exact dvd_neg.mpr hg

theorem inG0_T_zpow (Q : ℕ) (m : ℤ) : InG0 Q (T ^ m) := by
  unfold InG0; simp [coe_T_zpow]

theorem inG0_gam {Q : ℕ} {r : Rows} (hr : (Q : ℤ) ∣ r.1 0) : InG0 Q (gam r) := by
  have e : (gam r) 1 0 = r.1 0 := congrFun (gam_row r) 0
  unfold InG0; rw [e]; exact hr

/-- Two matrices with the same bottom row differ by a power of `T` on the left. -/
theorem eq_T_mul_of_rowOf_eq {h h' : SL(2, ℤ)} (e : rowOf h = rowOf h') :
    ∃ m : ℤ, h' = T ^ m * h := by
  have h0 : h 1 0 = h' 1 0 := congrFun (congrArg Subtype.val e) 0
  have h1 : h 1 1 = h' 1 1 := congrFun (congrArg Subtype.val e) 1
  have hd := det2 h
  have e0 : (h' * h⁻¹) 1 0 = 0 := by
    rw [mul_10', inv_10, show h⁻¹ 0 0 = h 1 1 by
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two], ← h0, ← h1]; ring
  have e1 : (h' * h⁻¹) 1 1 = 1 := by
    rw [mul_11', inv_11, show h⁻¹ 0 1 = -h 0 1 by
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two], ← h0, ← h1]
    linear_combination hd
  refine ⟨(h' * h⁻¹) 0 1, ?_⟩
  rw [← bottom_row_eq_T _ e0 e1, inv_mul_cancel_right]

theorem rowOf_gam (r : Rows) : rowOf (gam r) = r := by simpa using row_T_mul 0 r

theorem eq_T_mul_gam (h : SL(2, ℤ)) : ∃ m : ℤ, h = T ^ m * gam (rowOf h) :=
  eq_T_mul_of_rowOf_eq (h := gam (rowOf h)) (h' := h) (rowOf_gam _)

variable (Q : ℕ) [NeZero Q]

/-- The `(ℤ/Q)ˣ`-orbit of the bottom row of `σ` mod `Q`. -/
noncomputable def key (σ : SL(2, ℤ)) : Finset (ZMod Q × ZMod Q) :=
  Finset.univ.image fun u : (ZMod Q)ˣ => ((u : ZMod Q) * (σ 1 0 : ZMod Q), (u : ZMod Q) * (σ 1 1 : ZMod Q))

theorem self_mem_key (σ : SL(2, ℤ)) : ((σ 1 0 : ZMod Q), (σ 1 1 : ZMod Q)) ∈ key Q σ :=
  Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp⟩

theorem dvd_iff_key_eq (h σ : SL(2, ℤ)) : InG0 Q (h * σ⁻¹) ↔ key Q h = key Q σ := by
  unfold InG0
  rw [mul_10', inv_10, show σ⁻¹ 0 0 = σ 1 1 by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]]
  constructor
  · intro hdvd
    -- `g = h σ⁻¹` has `Q ∣ c`, so `g₁₁` is a unit mod `Q` and `row(h) ≡ g₁₁ row(σ)`
    set g := h * σ⁻¹ with hg
    have hg10 : (Q : ℤ) ∣ g 1 0 := by
      rw [hg, mul_10', inv_10, show σ⁻¹ 0 0 = σ 1 1 by
        simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]]; exact hdvd
    have hz : ((g 1 0 : ℤ) : ZMod Q) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hg10
    have hdg := det2 g
    have hunit : ((g 0 0 : ℤ) : ZMod Q) * ((g 1 1 : ℤ) : ZMod Q) = 1 := by
      have := congrArg (fun x : ℤ => (x : ZMod Q)) hdg
      push_cast at this; rw [hz, mul_zero, sub_zero] at this; exact this
    let w : (ZMod Q)ˣ := ⟨(g 1 1 : ZMod Q), (g 0 0 : ZMod Q), by rw [mul_comm]; exact hunit, hunit⟩
    have hgs : h = g * σ := by rw [hg, inv_mul_cancel_right]
    have r0 : ((h 1 0 : ℤ) : ZMod Q) = (w : ZMod Q) * (σ 1 0 : ZMod Q) := by
      rw [hgs, mul_10']; push_cast; rw [hz]; simp [w]
    have r1 : ((h 1 1 : ℤ) : ZMod Q) = (w : ZMod Q) * (σ 1 1 : ZMod Q) := by
      rw [hgs, mul_11']; push_cast; rw [hz]; simp [w]
    unfold key
    rw [r0, r1]
    ext p
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, rfl⟩; exact ⟨u * w, by push_cast; ring_nf⟩
    · rintro ⟨u, rfl⟩; exact ⟨u * w⁻¹, by
        simp only [Units.val_mul]
        rw [show (u : ZMod Q) * ((w⁻¹ : (ZMod Q)ˣ) : ZMod Q) * ((w : ZMod Q) * (σ 1 0 : ZMod Q)) =
          u * (((w⁻¹ : (ZMod Q)ˣ) : ZMod Q) * w) * σ 1 0 by ring,
          show (u : ZMod Q) * ((w⁻¹ : (ZMod Q)ˣ) : ZMod Q) * ((w : ZMod Q) * (σ 1 1 : ZMod Q)) =
          u * (((w⁻¹ : (ZMod Q)ˣ) : ZMod Q) * w) * σ 1 1 by ring, Units.inv_mul, mul_one]⟩
  · intro hk
    have hm := self_mem_key Q σ
    rw [← hk] at hm
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hm
    simp only [Prod.mk.injEq] at hv
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [← hv.1, ← hv.2]
    ring

/-- The set of keys: right cosets `Γ₀(Q)\SL(2, ℤ)`. -/
noncomputable def Keys : Set (Finset (ZMod Q × ZMod Q)) := Set.range (key Q)

noncomputable instance : Fintype (Keys Q) := Fintype.ofFinite _

/-- A representative of a coset. -/
noncomputable def pick (k : Keys Q) : SL(2, ℤ) := k.2.choose

theorem key_pick (k : Keys Q) : key Q (pick Q k) = k.1 := k.2.choose_spec

/-- The key of a matrix, as an element of `Keys Q`. -/
noncomputable def keyOf (h : SL(2, ℤ)) : Keys Q := ⟨key Q h, h, rfl⟩

theorem inG0_pick (h : SL(2, ℤ)) : InG0 Q (h * (pick Q (keyOf Q h))⁻¹) :=
  (dvd_iff_key_eq Q _ _).mpr (by rw [key_pick]; rfl)

theorem card_key (σ : SL(2, ℤ)) : (key Q σ).card = Nat.totient Q := by
  unfold key
  rw [Finset.card_image_of_injective _ ?_, Finset.card_univ, ZMod.card_units_eq_totient]
  intro u v huv
  simp only [Prod.mk.injEq] at huv
  -- `x c + y d = 1` gives `u = v`
  obtain ⟨x, y, hxy⟩ := row_coprime σ
  have : ((x * σ 1 0 + y * σ 1 1 : ℤ) : ZMod Q) = 1 := by rw [hxy]; simp
  push_cast at this
  apply Units.ext
  calc (u : ZMod Q) = u * ((x : ZMod Q) * σ 1 0 + y * σ 1 1) := by rw [this, mul_one]
    _ = x * (u * σ 1 0) + y * (u * σ 1 1) := by ring
    _ = x * (v * σ 1 0) + y * (v * σ 1 1) := by rw [huv.1, huv.2]
    _ = v * ((x : ZMod Q) * σ 1 0 + y * σ 1 1) := by ring
    _ = v := by rw [this, mul_one]

theorem key_disjoint {σ σ' : SL(2, ℤ)} (hne : key Q σ ≠ key Q σ') :
    Disjoint (key Q σ) (key Q σ') := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  apply hne
  obtain ⟨u, -, hu⟩ := Finset.mem_image.mp hp
  obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hp'
  rw [← dvd_iff_key_eq]
  unfold InG0
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, mul_10', inv_10,
    show σ'⁻¹ 0 0 = σ' 1 1 by simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]]
  push_cast
  rw [← hv] at hu
  simp only [Prod.mk.injEq] at hu
  have e0 : (σ 1 0 : ZMod Q) = ((u⁻¹ * v : (ZMod Q)ˣ) : ZMod Q) * σ' 1 0 := by
    rw [Units.val_mul, mul_assoc, ← hu.1, ← mul_assoc, Units.inv_mul, one_mul]
  have e1 : (σ 1 1 : ZMod Q) = ((u⁻¹ * v : (ZMod Q)ˣ) : ZMod Q) * σ' 1 1 := by
    rw [Units.val_mul, mul_assoc, ← hu.2, ← mul_assoc, Units.inv_mul, one_mul]
  rw [e0, e1]; ring

/-- **`#(Γ₀(Q)\SL(2, ℤ)) · φ(Q) ≤ Q²`.** -/
theorem card_keys_mul_totient : Fintype.card (Keys Q) * Nat.totient Q ≤ Q ^ 2 := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Keys Q)) : Set (Keys Q))
      (fun k : Keys Q => k.1) := by
    intro k _ k' _ hne
    obtain ⟨σ, hσ⟩ := k.2
    obtain ⟨σ', hσ'⟩ := k'.2
    have : k.1 ≠ k'.1 := fun h => hne (Subtype.ext h)
    rw [← hσ, ← hσ'] at this
    show Disjoint k.1 k'.1
    rw [← hσ, ← hσ']
    exact key_disjoint Q this
  have hcard := Finset.card_biUnion hdisj
  have hle : (Finset.univ.biUnion fun k : Keys Q => k.1).card ≤ Q ^ 2 := by
    calc _ ≤ (Finset.univ : Finset (ZMod Q × ZMod Q)).card := Finset.card_le_univ _
      _ = Q ^ 2 := by simp [ZMod.card, sq]
  have hk : ∀ k : Keys Q, k.1.card = Nat.totient Q := by
    intro k; obtain ⟨σ, hσ⟩ := k.2; rw [← hσ]; exact card_key Q σ
  rw [hcard] at hle
  simp only [hk, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
  exact hle

/-! ### Unfolding at level `Q` -/

/-- Coprime rows with `Q ∣ r₀`. -/
abbrev RowsQ : Type := {r : Rows // (Q : ℤ) ∣ r.1 0}

instance : Countable (RowsQ Q) := Subtype.countable

/-- The map `(k, r) ↦ row(γ_r σ_k)`. -/
noncomputable def unfoldMap (p : Keys Q × RowsQ Q) : Rows := rowOf (gam p.2.1 * pick Q p.1)

theorem unfoldMap_bijective : Function.Bijective (unfoldMap Q) := by
  constructor
  · rintro ⟨k, r⟩ ⟨k', r'⟩ e
    simp only [unfoldMap] at e
    obtain ⟨m, hm⟩ := eq_T_mul_of_rowOf_eq e
    -- `σ_{k'} σ_k⁻¹ ∈ Γ₀(Q)`
    have hG : InG0 Q (pick Q k' * (pick Q k)⁻¹) := by
      have hp : pick Q k' = (gam r'.1)⁻¹ * (T ^ m * (gam r.1 * pick Q k)) := by
        rw [← hm]; group
      have : pick Q k' * (pick Q k)⁻¹ = (gam r'.1)⁻¹ * T ^ m * gam r.1 := by
        rw [hp]; group
      rw [this]
      exact inG0_mul (inG0_mul (inG0_inv (inG0_gam r'.2)) (inG0_T_zpow Q m)) (inG0_gam r.2)
    have hkk : k' = k := by
      apply Subtype.ext
      rw [← key_pick Q k', ← key_pick Q k]
      exact (dvd_iff_key_eq Q _ _).mp hG
    subst hkk
    have hg : gam r'.1 = T ^ m * gam r.1 := mul_right_cancel (hm.trans (mul_assoc _ _ _).symm)
    have hr : r'.1 = r.1 := by
      have := congrArg rowOf hg
      rwa [rowOf_gam, row_T_mul] at this
    exact Prod.ext rfl (Subtype.ext hr.symm)
  · intro r'
    set h := gam r'
    set k := keyOf Q h
    set g := h * (pick Q k)⁻¹
    have hg : InG0 Q g := inG0_pick Q h
    obtain ⟨m, hm⟩ := eq_T_mul_gam g
    have hr0 : (Q : ℤ) ∣ (rowOf g).1 0 := hg
    refine ⟨(k, ⟨rowOf g, hr0⟩), ?_⟩
    simp only [unfoldMap]
    have hg' : gam (rowOf g) = T ^ (-m) * g := by
      conv_rhs => rw [hm]
      group
    have : gam (rowOf g) * pick Q k = T ^ (-m) * h := by
      rw [hg']; simp [g, mul_assoc]
    rw [this, row_T_mul]

/-- `ψ(h z) = ψ(γ_{row(h)} z)` for `T`-periodic `ψ`. -/
theorem psi_eq_gam {ψ : ℍ → ENNReal} (hper : ∀ z, ψ (T • z) = ψ z) (h : SL(2, ℤ)) (z : ℍ) :
    ψ (h • z) = ψ (gam (rowOf h) • z) := by
  obtain ⟨m, hm⟩ := eq_T_mul_gam h
  conv_lhs => rw [hm, mul_smul]
  exact psi_T_zpow hper m _

/-- **Unfolding at level `Q`.** -/
theorem unfold_level (ψ : ℍ → ENNReal) (hψ : Measurable ψ) (hper : ∀ z, ψ (T • z) = ψ z) :
    ∑ k : Keys Q, ∫⁻ z in fd, ∑' r : RowsQ Q, ψ ((gam r.1 * pick Q k) • z) =
      2 * ∫⁻ z in strip, ψ z := by
  rw [unfold_strip ψ hψ hper, ← mul_assoc, show (2 : ENNReal) * (1 / 2) = 1 by
    rw [one_div, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top], one_mul]
  rw [← lintegral_finset_sum (s := Finset.univ)
    (f := fun k z => ∑' r : RowsQ Q, ψ ((gam r.1 * pick Q k) • z)) fun k _ =>
      Measurable.ennreal_tsum fun r => hψ.comp (measurable_smul_SL _)]
  rw [← lintegral_tsum (f := fun (r : Rows) z => ψ (gam r • z))
    fun r => (hψ.comp (measurable_smul_SL _)).aemeasurable]
  refine lintegral_congr fun z => ?_
  rw [← tsum_fintype (L := SummationFilter.unconditional _), ← ENNReal.tsum_prod (f := fun (k : Keys Q) (r : RowsQ Q) => ψ ((gam r.1 * pick Q k) • z))]
  rw [← (Equiv.ofBijective _ (unfoldMap_bijective Q)).tsum_eq]
  refine tsum_congr fun p => ?_
  simp only [Equiv.ofBijective_apply, unfoldMap]
  exact psi_eq_gam hper _ z

end ThreeSquares.FD
