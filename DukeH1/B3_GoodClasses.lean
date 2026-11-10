/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.B3_Squares
public import DukeH1.B3_Ellipse

/-! # Counting the good residue classes for the lower bound

The image of z ↦ -z²/2 on units has at least φ(n)/τ(n) elements.
No class-number formula or analytic estimate is assumed in this module.
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares.B3
open Finset
set_option maxHeartbeats 4000000

noncomputable def goodClasses (n : ℕ) [NeZero n] : Finset (ZMod n) := by
  classical
  exact (univ : Finset (ZMod n)ˣ).image (fun (z : (ZMod n)ˣ) => -(z : ZMod n)^2*2⁻¹)

theorem mem_goodClasses {n : ℕ} [NeZero n] {c : ZMod n} :
    c ∈ goodClasses n ↔ ∃ z : ZMod n, IsUnit z ∧ -z^2*2⁻¹=c := by
  classical
  simp only [goodClasses, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨z,z.isUnit,rfl⟩
  · rintro ⟨z,⟨u,hu⟩,hz⟩
    exact ⟨u,by simpa only [hu] using hz⟩

theorem goodClasses_properties {n : ℕ} [NeZero n] (hn : n%8=3)
    {c : ZMod n} (hc : c ∈ goodClasses n) : IsUnit c ∧ chiN n c=1 := by
  obtain ⟨z,hz,rfl⟩ := mem_goodClasses.mp hc
  refine ⟨?_,chiN_neg_half_sq hn hz⟩
  have h2 := isUnit_two (Nat.odd_iff.mpr (by omega : n%2=1))
  exact ((hz.pow 2).neg).mul ⟨⟨2⁻¹,2,ZMod.inv_mul_of_unit _ h2,ZMod.mul_inv_of_unit _ h2⟩,rfl⟩

theorem goodClasses_card_lower {n : ℕ} [NeZero n] (hsq : Squarefree n) (hodd : Odd n) :
    n.totient ≤ n.divisors.card*(goodClasses n).card := by
  classical
  have hbound : ∀ c ∈ goodClasses n,
      ((univ : Finset (ZMod n)ˣ).filter (fun (z : (ZMod n)ˣ) => -(z : ZMod n)^2*2⁻¹=c)).card ≤
        n.divisors.card := by
    intro c _
    apply le_trans (card_le_card_of_injOn (fun z : (ZMod n)ˣ => (z : ZMod n)) ?_ ?_)
      (card_half_sq_le hsq hodd c)
    · intro z hz
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hz ⊢
      exact ⟨z.isUnit,hz⟩
    · intro z _ w _ h
      exact Units.val_injective h
  have h := card_le_mul_card_image (f := fun z : (ZMod n)ˣ => -(z : ZMod n)^2*2⁻¹)
    (univ : Finset (ZMod n)ˣ) n.divisors.card hbound
  simpa only [card_univ,ZMod.card_units_eq_totient,goodClasses] using h

/-- A useful elementary replacement for a lower bound on φ(n)/n. -/
theorem order_le_totient_mul_divisors {n : ℕ} (hn : 0<n) :
    n ≤ n.divisors.card*n.totient := by
  calc n = ∑ d ∈ n.divisors,d.totient := (Nat.sum_totient n).symm
    _ ≤ ∑ _d ∈ n.divisors,n.totient := by
      apply sum_le_sum
      intro d hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr hn)
        (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = _ := by simp

noncomputable def goodSum (n : ℕ) [NeZero n] (M : ℕ) : ℝ :=
  ∑ m ∈ (Icc 1 M).filter (fun (m : ℕ) => (m : ZMod n) ∈ goodClasses n),(chi1 n m : ℝ)

theorem goodSum_le_ellipses {n : ℕ} [NeZero n] (hn : n%8=3) {M : ℕ} (hM : 1≤M) :
    goodSum n M ≤ ∑ f ∈ GoodSet n,
      (8*(M:ℝ)/Real.sqrt n+6*Real.sqrt f.a*Real.sqrt M+1) := by
  classical
  let P : ℕ → Prop := fun m => (m : ZMod n) ∈ goodClasses n
  have hg : ∀ m,P m → m.Coprime n ∧ ∃ t : ℤ,(n:ℤ) ∣ 2*t^2*m+1 := by
    intro m hm
    obtain ⟨z,hz,hzEq⟩ := mem_goodClasses.mp hm
    exact good_of_class (Nat.odd_iff.mpr (by omega)) hz hzEq.symm
  calc goodSum n M ≤ ((∑ m ∈ (Icc 1 M).filter P,Rcount n m : ℕ) : ℝ) := by
        unfold goodSum
        push_cast
        exact sum_le_sum fun m hm => by
          have hcop := (hg m (mem_filter.mp hm).2).1
          exact_mod_cast chi1_le_Rcount hn hcop
    _ ≤ ((∑ f ∈ GoodSet n,ellCount f M : ℕ) : ℝ) := by
        exact_mod_cast sum_Rcount_le (by omega : 0<n) M P (fun m hm => (hg m hm).2)
    _ ≤ _ := by
        push_cast
        apply sum_le_sum
        intro f hf
        exact ellCount_le (by omega : 0<n) (mem_GoodSet.mp hf).1 hM

end ThreeSquares.B3
