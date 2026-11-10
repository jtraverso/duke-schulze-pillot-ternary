/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.B3_Ternary

/-!
# At most 18 good reduced forms per point of the sphere

For a good reduced form `f` choose a basis `E = (e₁, e₂, e₃)` (`IsBasis f E`: Gram matrix of
`e₁, e₂` is `[[2a, b], [b, 2c]]`, `det(e₁, e₂, e₃) = 1`) and put `xpt n f = e₁ × e₂ ∈ reps3 n`.
If `xpt n f' = xpt n f`, then `e₁' = k e₁ + l e₂` (Cramer, `eq_comb`), the two forms have the same
first coefficient (the minimum of the lattice `x^⊥ ∩ ℤ³`), `|k|, |l| ≤ 1` (`fiber_coeff`), and
`f'` is determined by `(k, l)` and the sign of `b'` (`fiber_inj`).
`card_goodSet_le`: `#GoodSet n ≤ 18 · r₃(n)`.
-/

@[expose] public section

namespace ThreeSquares.B3

open Matrix ThreeSquares

/-- `E` is an oriented basis adapted to `f`. -/
def IsBasis (f : Form) (E : (Fin 3 → ℤ) × (Fin 3 → ℤ) × (Fin 3 → ℤ)) : Prop :=
  E.1 ⬝ᵥ E.1 = 2 * f.a ∧ E.1 ⬝ᵥ E.2.1 = f.b ∧ E.2.1 ⬝ᵥ E.2.1 = 2 * f.c ∧
    E.2.2 ⬝ᵥ cr E.1 E.2.1 = 1

theorem exists_isBasis {n : ℕ} (hn : 0 < n) {f : Form} (hf : f ∈ Red n) (hg : Good n f) :
    ∃ E, IsBasis f E := by
  obtain ⟨e₁, e₂, e₃, h⟩ := exists_basis_of_good hn hf hg
  exact ⟨(e₁, e₂, e₃), h⟩

open scoped Classical in
/-- The chosen basis. -/
noncomputable def basisOf (n : ℕ) (f : Form) : (Fin 3 → ℤ) × (Fin 3 → ℤ) × (Fin 3 → ℤ) :=
  if h : 0 < n ∧ f ∈ Red n ∧ Good n f then Classical.choose (exists_isBasis h.1 h.2.1 h.2.2)
  else (0, 0, 0)

theorem basisOf_spec {n : ℕ} (hn : 0 < n) {f : Form} (hf : f ∈ Red n) (hg : Good n f) :
    IsBasis f (basisOf n f) := by
  have h : 0 < n ∧ f ∈ Red n ∧ Good n f := ⟨hn, hf, hg⟩
  rw [basisOf, dif_pos h]
  exact Classical.choose_spec (exists_isBasis h.1 h.2.1 h.2.2)

/-- The point of the sphere attached to a good reduced form. -/
noncomputable def xpt (n : ℕ) (f : Form) : Fin 3 → ℤ := cr (basisOf n f).1 (basisOf n f).2.1

theorem cramer (e₁ e₂ e₃ v : Fin 3 → ℤ) :
    (e₃ ⬝ᵥ cr e₁ e₂) • v = (e₃ ⬝ᵥ cr v e₂) • e₁ + (e₃ ⬝ᵥ cr e₁ v) • e₂ +
      (v ⬝ᵥ cr e₁ e₂) • e₃ := by
  funext i
  fin_cases i <;> simp [cr, dotProduct, Fin.sum_univ_three] <;> ring

theorem eq_comb {e₁ e₂ e₃ v : Fin 3 → ℤ} (h1 : e₃ ⬝ᵥ cr e₁ e₂ = 1)
    (h0 : v ⬝ᵥ cr e₁ e₂ = 0) : v = (e₃ ⬝ᵥ cr v e₂) • e₁ + (e₃ ⬝ᵥ cr e₁ v) • e₂ := by
  have := cramer e₁ e₂ e₃ v
  rw [h1, h0, one_smul, zero_smul, add_zero] at this
  exact this

theorem dot_comb (e₁ e₂ : Fin 3 → ℤ) (k l k' l' : ℤ) :
    (k • e₁ + l • e₂) ⬝ᵥ (k' • e₁ + l' • e₂) =
      k * k' * (e₁ ⬝ᵥ e₁) + (k * l' + l * k') * (e₁ ⬝ᵥ e₂) + l * l' * (e₂ ⬝ᵥ e₂) := by
  simp only [dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem cr_comb (e₁ e₂ : Fin 3 → ℤ) (k l k' l' : ℤ) :
    cr (k • e₁ + l • e₂) (k' • e₁ + l' • e₂) = (k * l' - l * k') • cr e₁ e₂ := by
  funext i
  fin_cases i <;> simp [cr] <;> ring

theorem norm_comb {f : Form} {E : (Fin 3 → ℤ) × (Fin 3 → ℤ) × (Fin 3 → ℤ)} (hE : IsBasis f E)
    (k l : ℤ) : (k • E.1 + l • E.2.1) ⬝ᵥ (k • E.1 + l • E.2.1) = 2 * f.eval k l := by
  rw [dot_comb, hE.1, hE.2.1, hE.2.2.1]
  simp only [Form.eval]
  ring

theorem cr_ne_zero {n : ℕ} (hn : 0 < n) {f : Form} (hf : f ∈ Red n)
    {E : (Fin 3 → ℤ) × (Fin 3 → ℤ) × (Fin 3 → ℤ)} (hE : IsBasis f E) {s : ℤ}
    (h : s • cr E.1 E.2.1 = cr E.1 E.2.1) : s = 1 := by
  have hsum := cr_mem_reps3 hf hE.1 hE.2.1 hE.2.2.1
  rw [Duke.mem_reps3] at hsum
  by_contra hs
  have h0 : ∀ i, cr E.1 E.2.1 i = 0 := by
    intro i
    have := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have : (s - 1) * cr E.1 E.2.1 i = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd (by linarith : s = 1) hs
    · exact h1
  simp [h0] at hsum
  omega

/-- **Fibre, coefficients.** -/
theorem fiber_coeff {n : ℕ} {f f' : Form} (hf : f ∈ Red n) (hf' : f' ∈ Red n)
    {E E' : (Fin 3 → ℤ) × (Fin 3 → ℤ) × (Fin 3 → ℤ)} (hE : IsBasis f E) (hE' : IsBasis f' E')
    (hx : cr E'.1 E'.2.1 = cr E.1 E.2.1) :
    E'.1 = (E.2.2 ⬝ᵥ cr E'.1 E.2.1) • E.1 + (E.2.2 ⬝ᵥ cr E.1 E'.1) • E.2.1 ∧
      f'.a = f.eval (E.2.2 ⬝ᵥ cr E'.1 E.2.1) (E.2.2 ⬝ᵥ cr E.1 E'.1) ∧ f'.a = f.a ∧
      |E.2.2 ⬝ᵥ cr E'.1 E.2.1| ≤ 1 ∧ |E.2.2 ⬝ᵥ cr E.1 E'.1| ≤ 1 := by
  obtain ⟨-, hred, ha⟩ := mem_Red.mp hf
  obtain ⟨-, hred', ha'⟩ := mem_Red.mp hf'
  set k := E.2.2 ⬝ᵥ cr E'.1 E.2.1
  set l := E.2.2 ⬝ᵥ cr E.1 E'.1
  have h0 : E'.1 ⬝ᵥ cr E.1 E.2.1 = 0 := by rw [← hx]; exact cr_dot_left _ _
  have hkl : E'.1 = k • E.1 + l • E.2.1 := eq_comb hE.2.2.2 h0
  have h0' : E.1 ⬝ᵥ cr E'.1 E'.2.1 = 0 := by rw [hx]; exact cr_dot_left _ _
  set K := E'.2.2 ⬝ᵥ cr E.1 E'.2.1
  set L := E'.2.2 ⬝ᵥ cr E'.1 E.1
  have hKL : E.1 = K • E'.1 + L • E'.2.1 := eq_comb hE'.2.2.2 h0'
  have hfa' : f'.a = f.eval k l := by
    have := norm_comb hE k l
    rw [← hkl, hE'.1] at this
    linarith
  have hfa : f.a = f'.eval K L := by
    have := norm_comb hE' K L
    rw [← hKL, hE.1] at this
    linarith
  have hkl0 : k ≠ 0 ∨ l ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [hc.1, hc.2] at hfa'
    simp [Form.eval] at hfa'
    omega
  have hKL0 : K ≠ 0 ∨ L ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [hc.1, hc.2] at hfa
    simp [Form.eval] at hfa
    omega
  have q1 := Form.quad_ge_one hkl0
  have q2 := Form.quad_ge_one hKL0
  have m1 := Form.min_le_eval hred k l
  have m2 := Form.min_le_eval hred' K L
  have le1 : f.a ≤ f'.a := by nlinarith
  have le2 : f'.a ≤ f.a := by nlinarith
  have heq : f'.a = f.a := le_antisymm le2 le1
  have hq : k ^ 2 - |k * l| + l ^ 2 ≤ 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  obtain ⟨hk1, hl1⟩ := Form.abs_le_one_of_quad_le_one hq
  exact ⟨hkl, hfa', heq, hk1, hl1⟩

theorem shift_zero {A b₁ b₂ t : ℤ} (hA : 0 < A) (h₁ : -A ≤ b₁ ∧ b₁ ≤ A)
    (h₂ : -A ≤ b₂ ∧ b₂ ≤ A) (hs : b₂ = b₁ + 2 * t * A) (hb : (0 < b₁ ↔ 0 < b₂)) : t = 0 := by
  obtain ⟨h₁a, h₁b⟩ := h₁
  obtain ⟨h₂a, h₂b⟩ := h₂
  rcases lt_trichotomy t 0 with h | h | h
  · exfalso
    have : t * A ≤ -A := by nlinarith
    have := hb.mp (by linarith)
    linarith
  · exact h
  · exfalso
    have : A ≤ t * A := by nlinarith
    have := hb.mpr (by linarith)
    linarith

/-- **Fibre, injectivity.** -/
theorem fiber_inj {n : ℕ} (hn : 0 < n) {f f₁ f₂ : Form} (hf : f ∈ Red n) (hf₁ : f₁ ∈ Red n)
    (hf₂ : f₂ ∈ Red n) {E E₁ E₂ : (Fin 3 → ℤ) × (Fin 3 → ℤ) × (Fin 3 → ℤ)} (hE : IsBasis f E)
    (hE₁ : IsBasis f₁ E₁) (hE₂ : IsBasis f₂ E₂) (hx₁ : cr E₁.1 E₁.2.1 = cr E.1 E.2.1)
    (hx₂ : cr E₂.1 E₂.2.1 = cr E.1 E.2.1)
    (hk : E.2.2 ⬝ᵥ cr E₁.1 E.2.1 = E.2.2 ⬝ᵥ cr E₂.1 E.2.1)
    (hl : E.2.2 ⬝ᵥ cr E.1 E₁.1 = E.2.2 ⬝ᵥ cr E.1 E₂.1) (hb : (0 < f₁.b ↔ 0 < f₂.b)) :
    f₁ = f₂ := by
  obtain ⟨hw₁, ha₁, hA₁, -, -⟩ := fiber_coeff hf hf₁ hE hE₁ hx₁
  obtain ⟨hw₂, ha₂, hA₂, -, -⟩ := fiber_coeff hf hf₂ hE hE₂ hx₂
  rw [← hk, ← hl] at hw₂ ha₂
  set k := E.2.2 ⬝ᵥ cr E₁.1 E.2.1
  set l := E.2.2 ⬝ᵥ cr E.1 E₁.1
  have hd₁ := (mem_Red.mp hf₁).1
  have hd₂ := (mem_Red.mp hf₂).1
  obtain ⟨hb₁, -⟩ := (mem_Red.mp hf₁).2.1
  obtain ⟨hb₂, -⟩ := (mem_Red.mp hf₂).2.1
  have ha₀ := (mem_Red.mp hf₁).2.2
  -- second vectors
  have h0₁ : E₁.2.1 ⬝ᵥ cr E.1 E.2.1 = 0 := by rw [← hx₁]; exact cr_dot_right _ _
  have h0₂ : E₂.2.1 ⬝ᵥ cr E.1 E.2.1 = 0 := by rw [← hx₂]; exact cr_dot_right _ _
  have hv₁ := eq_comb hE.2.2.2 h0₁
  have hv₂ := eq_comb hE.2.2.2 h0₂
  set k₁ := E.2.2 ⬝ᵥ cr E₁.2.1 E.2.1
  set l₁ := E.2.2 ⬝ᵥ cr E.1 E₁.2.1
  set k₂ := E.2.2 ⬝ᵥ cr E₂.2.1 E.2.1
  set l₂ := E.2.2 ⬝ᵥ cr E.1 E₂.2.1
  -- orientation
  have o₁ : k * l₁ - l * k₁ = 1 := by
    apply cr_ne_zero hn hf hE
    rw [← cr_comb, ← hw₁, ← hv₁, hx₁]
  have o₂ : k * l₂ - l * k₂ = 1 := by
    apply cr_ne_zero hn hf hE
    rw [← cr_comb, ← hw₂, ← hv₂, hx₂]
  -- the shift
  have hcop : IsCoprime k l := ⟨l₁, -k₁, by linarith⟩
  obtain ⟨α, β, hαβ⟩ := hcop
  set t := α * (k₂ - k₁) + β * (l₂ - l₁)
  have hΔk : k₂ - k₁ = t * k := by linear_combination (-(k₂ - k₁)) * hαβ - β * (o₂ - o₁)
  have hΔl : l₂ - l₁ = t * l := by linear_combination (-(l₂ - l₁)) * hαβ + α * (o₂ - o₁)
  -- the middle coefficients
  have eb₁ : f₁.b = k * k₁ * (2 * f.a) + (k * l₁ + l * k₁) * f.b + l * l₁ * (2 * f.c) := by
    rw [← hE₁.2.1, hw₁, hv₁, dot_comb, hE.1, hE.2.1, hE.2.2.1]
  have eb₂ : f₂.b = k * k₂ * (2 * f.a) + (k * l₂ + l * k₂) * f.b + l * l₂ * (2 * f.c) := by
    rw [← hE₂.2.1, hw₂, hv₂, dot_comb, hE.1, hE.2.1, hE.2.2.1]
  have hshift : f₂.b = f₁.b + 2 * t * f₁.a := by
    rw [eb₁, eb₂, ha₁]
    simp only [Form.eval]
    have e1 : k₂ = k₁ + t * k := by linarith
    have e2 : l₂ = l₁ + t * l := by linarith
    rw [e1, e2]
    ring
  rw [abs_le] at hb₁ hb₂
  rw [ha₂] at hb₂
  rw [ha₁] at hb₁ ha₀ hshift
  have ht : t = 0 := shift_zero ha₀ hb₁ hb₂ hshift hb
  rw [ht] at hshift
  have hbb : f₂.b = f₁.b := by linarith
  have haa : f₂.a = f₁.a := by rw [hA₁, hA₂]
  have hcc : f₂.c = f₁.c := by
    unfold Form.disc at hd₁ hd₂
    rw [hbb, haa] at hd₂
    have h4 : 4 * f₁.a * f₂.c = 4 * f₁.a * f₁.c := by linarith
    have : (4 * f₁.a) ≠ 0 := by rw [hA₁] at *; omega
    exact mul_left_cancel₀ this h4
  ext
  · exact haa.symm
  · exact hbb.symm
  · exact hcc.symm

/-- The good reduced forms. -/
noncomputable def GoodSet (n : ℕ) : Finset Form := by
  classical exact (Red n).filter (fun f => Good n f)

theorem mem_GoodSet {n : ℕ} {f : Form} : f ∈ GoodSet n ↔ f ∈ Red n ∧ Good n f := by
  classical
  simp [GoodSet]

theorem card_goodSet_le {n : ℕ} (hn : 0 < n) : (GoodSet n).card ≤ 18 * Duke.r3 n := by
  classical
  have himg : (GoodSet n).image (xpt n) ⊆ Duke.reps3 n := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hr, hg⟩ := mem_GoodSet.mp hf
    have hE := basisOf_spec hn hr hg
    exact cr_mem_reps3 hr hE.1 hE.2.1 hE.2.2.1
  have hcard := Finset.card_le_card himg
  refine le_trans (Finset.card_le_mul_card_image (f := xpt n) (GoodSet n) 18 ?_) ?_
  · intro y hy
    obtain ⟨f₀, hf₀, hfy⟩ := Finset.mem_image.mp hy
    obtain ⟨hr₀, hg₀⟩ := mem_GoodSet.mp hf₀
    have hE₀ := basisOf_spec hn hr₀ hg₀
    set E := basisOf n f₀
    let key : Form → ℤ × ℤ × Bool := fun f =>
      (E.2.2 ⬝ᵥ cr (basisOf n f).1 E.2.1, E.2.2 ⬝ᵥ cr E.1 (basisOf n f).1, decide (0 < f.b))
    let T : Finset (ℤ × ℤ × Bool) := Finset.Icc (-1) 1 ×ˢ Finset.Icc (-1) 1 ×ˢ Finset.univ
    have hT : T.card = 18 := by simp [T]
    rw [← hT]
    refine Finset.card_le_card_of_injOn key ?_ ?_
    · intro f hf
      rw [Finset.mem_coe, Finset.mem_filter] at hf
      obtain ⟨hf, hxy⟩ := hf
      obtain ⟨hr, hg⟩ := mem_GoodSet.mp hf
      have hE := basisOf_spec hn hr hg
      have hx : cr (basisOf n f).1 (basisOf n f).2.1 = cr E.1 E.2.1 := by
        have : xpt n f = xpt n f₀ := by rw [hxy, hfy]
        exact this
      obtain ⟨-, -, -, hk, hl⟩ := fiber_coeff hr₀ hr hE₀ hE hx
      rw [abs_le] at hk hl
      simp only [Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc,
        Finset.coe_univ, Set.mem_univ, and_true, key, T]
      exact ⟨hk, hl⟩
    · intro f₁ hf₁ f₂ hf₂ heq
      rw [Finset.mem_coe, Finset.mem_filter] at hf₁ hf₂
      obtain ⟨hf₁, hxy₁⟩ := hf₁
      obtain ⟨hf₂, hxy₂⟩ := hf₂
      obtain ⟨hr₁, hg₁⟩ := mem_GoodSet.mp hf₁
      obtain ⟨hr₂, hg₂⟩ := mem_GoodSet.mp hf₂
      have hE₁ := basisOf_spec hn hr₁ hg₁
      have hE₂ := basisOf_spec hn hr₂ hg₂
      have hx₁ : cr (basisOf n f₁).1 (basisOf n f₁).2.1 = cr E.1 E.2.1 := by
        have : xpt n f₁ = xpt n f₀ := by rw [hxy₁, hfy]
        exact this
      have hx₂ : cr (basisOf n f₂).1 (basisOf n f₂).2.1 = cr E.1 E.2.1 := by
        have : xpt n f₂ = xpt n f₀ := by rw [hxy₂, hfy]
        exact this
      simp only [key, Prod.mk.injEq] at heq
      obtain ⟨hk, hl, hb⟩ := heq
      exact fiber_inj hn hr₀ hr₁ hr₂ hE₀ hE₁ hE₂ hx₁ hx₂ hk hl (by simpa using hb)
  · exact Nat.mul_le_mul_left 18 hcard

end ThreeSquares.B3
