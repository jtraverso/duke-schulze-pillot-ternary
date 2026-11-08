/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.B3_GoodClasses
public import ThreeSquaresLib.B3_SchiLimit

/-! # The average over the good residue classes -/

@[expose] public section

namespace ThreeSquares.B3
open Finset Filter Topology

theorem tendsto_Schi {n : ℕ} [NeZero n] (hn : n%8=3) :
    Tendsto (Schi n) atTop (𝓝 (DirichletCharacter.LFunction (chiN n) 1)) := by
  have h := character_sum_at_one (chiN n) (chiN_ne_one (by omega))
  convert h using 1
  funext M
  unfold Schi chf
  apply sum_subset
  · intro k hk
    rw [mem_Ioc] at hk
    exact mem_Icc.mpr ⟨by omega,hk.2⟩
  · intro k hk hnot
    have hk0 : k=0 := by
      simp only [mem_Icc,mem_Ioc] at hk hnot
      omega
    simp [hk0]

theorem sum_classSum_good_eq {n : ℕ} [NeZero n] (M : ℕ) :
    ∑ c ∈ goodClasses n,classSum n c M = ((goodSum n M : ℝ) : ℂ) := by
  classical
  have hi : Icc 1 M=Ioc 0 M := by ext k; simp only [mem_Icc,mem_Ioc]; omega
  unfold classSum goodSum
  rw [hi]
  push_cast
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro m _
  simp

theorem goodSum_tendsto {n : ℕ} [NeZero n] (hn : n%8=3) :
    Tendsto (fun M : ℕ => goodSum n M/(M:ℝ)) atTop
      (𝓝 ((goodClasses n).card*2*(DirichletCharacter.LFunction (chiN n) 1).re/n)) := by
  classical
  have h := tendsto_finset_sum (goodClasses n) (fun c hc =>
    tendsto_classSum hn (tendsto_Schi hn) (goodClasses_properties hn hc).1
      (goodClasses_properties hn hc).2)
  have he (M : ℕ) : ∑ c ∈ goodClasses n,classSum n c M/(M:ℂ) =
      ((goodSum n M/(M:ℝ) : ℝ) : ℂ) := by
    rw [←sum_div,sum_classSum_good_eq]
    push_cast
    rfl
  simp_rw [he] at h
  have hreal := Complex.continuous_re.continuousAt.tendsto.comp h
  simpa [Function.comp_def,Complex.re_sum,mul_div_assoc,mul_assoc] using hreal

theorem goodSum_nonnegative {n : ℕ} [NeZero n] (hn : n%8=3) (M : ℕ) :
    0≤goodSum n M := by
  classical
  unfold goodSum
  apply sum_nonneg
  intro m hm
  obtain ⟨z,hz,he⟩ := mem_goodClasses.mp (mem_filter.mp hm).2
  have hc := (good_of_class (Nat.odd_iff.mpr (by omega)) hz he.symm).1
  exact_mod_cast chi1_nonneg hn hc

/-- The limiting L-value is real: every partial sum has zero imaginary part. -/
theorem L_one_im_zero {n : ℕ} [NeZero n] (hn : n%8=3) :
    (DirichletCharacter.LFunction (chiN n) 1).im=0 := by
  have h := Complex.continuous_im.continuousAt.tendsto.comp (tendsto_Schi hn)
  have he (M : ℕ) : (Schi n M).im=0 := by
    unfold Schi chf
    simp_rw [chiN_nat]
    simp
  simp only [Function.comp_def,he] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem L_one_re_nonnegative {n : ℕ} [NeZero n] (hn : n%8=3) :
    0≤(DirichletCharacter.LFunction (chiN n) 1).re := by
  have hG : 0<((goodClasses n).card : ℝ) := by
    apply Nat.cast_pos.mpr
    apply card_pos.mpr
    exact ⟨-(1:ZMod n)^2*2⁻¹,mem_goodClasses.mpr ⟨1,isUnit_one,rfl⟩⟩
  have hlim := le_of_tendsto_of_tendsto tendsto_const_nhds (goodSum_tendsto hn)
    (Filter.Eventually.of_forall (fun M => div_nonneg (goodSum_nonnegative hn M)
      (Nat.cast_nonneg M)))
  rw [le_div_iff₀ (show (0:ℝ)<n by exact_mod_cast (show 0<n by omega))] at hlim
  simp only [zero_mul] at hlim
  by_contra hneg
  have hbad := mul_neg_of_pos_of_neg (show (0:ℝ)<(goodClasses n).card*2 by positivity)
    (lt_of_not_ge hneg)
  exact (not_lt_of_ge hlim) hbad

theorem L_one_norm_eq_re {n : ℕ} [NeZero n] (hn : n%8=3) :
    ‖DirichletCharacter.LFunction (chiN n) 1‖=
      (DirichletCharacter.LFunction (chiN n) 1).re := by
  have he : DirichletCharacter.LFunction (chiN n) 1=
      (((DirichletCharacter.LFunction (chiN n) 1).re : ℝ) : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using L_one_im_zero hn
  conv_lhs => rw [he]
  simp [Complex.norm_real,abs_of_nonneg (L_one_re_nonnegative hn)]

end ThreeSquares.B3
