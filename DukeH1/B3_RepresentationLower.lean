/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.B3_GoodLimit
public import DukeH1.B3_VerifiedInputs
public import DukeH1.DivisorBound

/-! # The squarefree three-square representation lower bound

The comparison of averages gives
sqrt(n) L(1,chi_n) ≤ 72 τ(n)² r₃(n).
Siegel and the elementary divisor bound then give every positive power saving.
The constant inherited from Siegel is ineffective.
-/

@[expose] public section
open FourSquaresCaps

namespace ThreeSquares.B3
open Finset Filter Topology

theorem good_average_upper {n : ℕ} [NeZero n] (hn : n%8=3) :
    (goodClasses n).card*2*(DirichletCharacter.LFunction (chiN n) 1).re/(n:ℝ) ≤
      8*(GoodSet n).card/Real.sqrt n := by
  classical
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  let A : ℝ := 8*(GoodSet n).card/Real.sqrt n
  let E : ℝ := ∑ f ∈ GoodSet n,6*Real.sqrt f.a
  have hsqrt : Tendsto (fun M : ℕ => Real.sqrt (M:ℝ)/(M:ℝ)) atTop (𝓝 0) := by
    have h : Tendsto (fun M : ℕ => (1:ℝ)/Real.sqrt (M:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with M hM
    have hMR : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
    apply (div_eq_div_iff (Real.sqrt_pos.mpr hMR).ne' hMR.ne').mpr
    nlinarith [Real.sq_sqrt hMR.le]
  have hdiv : Tendsto (fun M : ℕ => ((GoodSet n).card:ℝ)/(M:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hright : Tendsto (fun M : ℕ => A+E*(Real.sqrt (M:ℝ)/(M:ℝ))+
      ((GoodSet n).card:ℝ)/(M:ℝ)) atTop (𝓝 A) := by
    simpa using (tendsto_const_nhds.add (hsqrt.const_mul E)).add hdiv
  apply le_of_tendsto_of_tendsto (goodSum_tendsto hn) hright
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hMR : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have h := div_le_div_of_nonneg_right (goodSum_le_ellipses hn hM) hMR.le
  have he : (∑ f ∈ GoodSet n,(8*(M:ℝ)/Real.sqrt n+6*Real.sqrt f.a*Real.sqrt M+1))/(M:ℝ)=
      A+E*(Real.sqrt (M:ℝ)/(M:ℝ))+((GoodSet n).card:ℝ)/(M:ℝ) := by
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←sum_mul,A,E]
    field_simp
    <;> ring
  rwa [he] at h

theorem sqrt_mul_L_le_divisors_r3 {n : ℕ} [NeZero n] (hn : n%8=3) (hsq : Squarefree n) :
    Real.sqrt n*‖DirichletCharacter.LFunction (chiN n) 1‖ ≤
      72*(n.divisors.card:ℝ)^2*Duke.r3 n := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hsR : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnR
  have hL := L_one_re_nonnegative hn
  have hcard : (n.totient:ℝ) ≤ (n.divisors.card:ℝ)*(goodClasses n).card := by
    exact_mod_cast goodClasses_card_lower hsq (Nat.odd_iff.mpr (by omega))
  have hphi : (n:ℝ) ≤ (n.divisors.card:ℝ)*n.totient := by
    exact_mod_cast order_le_totient_mul_divisors (by omega : 0<n)
  have hg : ((GoodSet n).card:ℝ) ≤ 18*Duke.r3 n := by
    exact_mod_cast card_goodSet_le (by omega : 0<n)
  have havg := mul_le_mul_of_nonneg_right (good_average_upper hn) (mul_nonneg hnR.le hsR.le)
  have he1 : ((goodClasses n).card*2*(DirichletCharacter.LFunction (chiN n) 1).re/(n:ℝ))*
      ((n:ℝ)*Real.sqrt n)=(goodClasses n).card*2*(DirichletCharacter.LFunction (chiN n) 1).re*Real.sqrt n := by
    field_simp
  have he2 : (8*((GoodSet n).card:ℝ)/Real.sqrt n)*((n:ℝ)*Real.sqrt n)=8*(GoodSet n).card*n := by
    field_simp
  rw [he1,he2] at havg
  have h1 := mul_le_mul_of_nonneg_right hcard
    (mul_nonneg (show 0≤2*(DirichletCharacter.LFunction (chiN n) 1).re by linarith) hsR.le)
  have h2 := mul_le_mul_of_nonneg_right havg (Nat.cast_nonneg n.divisors.card : (0:ℝ)≤n.divisors.card)
  have h3 := mul_le_mul_of_nonneg_right hg
    (show (0:ℝ)≤8*(n:ℝ)*n.divisors.card by positivity)
  have h4 : (n.totient:ℝ)*(DirichletCharacter.LFunction (chiN n) 1).re*Real.sqrt n ≤
      72*(n:ℝ)*n.divisors.card*Duke.r3 n := by
    nlinarith only [h1,h2,h3]
  have h5 := mul_le_mul_of_nonneg_right hphi
    (mul_nonneg hL hsR.le)
  have h6 := mul_le_mul_of_nonneg_right h4
    (Nat.cast_nonneg n.divisors.card : (0:ℝ)≤n.divisors.card)
  have h7 : (n:ℝ)*((DirichletCharacter.LFunction (chiN n) 1).re*Real.sqrt n) ≤
      (n:ℝ)*(72*(n.divisors.card:ℝ)^2*Duke.r3 n) := by
    nlinarith only [h5,h6]
  have h8 := le_of_mul_le_mul_left h7 hnR
  rw [L_one_norm_eq_re hn]
  simpa only [mul_comm] using h8

/-- The actual uniform lower bound required by the cap argument. -/
theorem r3_lower (ε : ℝ) (hε : 0<ε) :
    ∃ c>0,∀ n : ℕ,Squarefree n → n%8=3 → c*(n:ℝ)^((1:ℝ)/2-ε) ≤ Duke.r3 n := by
  let δ := min ε 1
  have hδ : 0<δ := lt_min hε (by norm_num)
  have hδ1 : δ≤1 := min_le_right _ _
  obtain ⟨cs,hcs,hs⟩ := siegel_verified (δ/2) (by positivity)
  obtain ⟨ct,hct,ht⟩ := ThreeSquares.card_divisors_le_rpow (δ/4) (by positivity) (by linarith)
  refine ⟨cs/(72*ct^2),by positivity,fun n hn hn8 => ?_⟩
  have hn0 : 0<n := by omega
  letI : NeZero n := ⟨by omega⟩
  have hnR : (0:ℝ)<n := by exact_mod_cast hn0
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hLS := hs n (chiN n) (chiN_ne_one (by omega)) (chiN_sq n)
  have hτ := ht n hn0.ne'
  have hbase := sqrt_mul_L_le_divisors_r3 hn8 hn
  have hpow : 0<(n:ℝ)^(δ/2) := Real.rpow_pos_of_pos hnR _
  have hτ2 : (n.divisors.card:ℝ)^2≤ct^2*(n:ℝ)^(δ/2) := by
    calc (n.divisors.card:ℝ)^2 ≤ (ct*(n:ℝ)^(δ/4))^2 :=
      pow_le_pow_left₀ (by positivity) hτ 2
      _ = _ := by
        have hePow : ((n:ℝ)^(δ/4))^2=(n:ℝ)^(δ/2) := by
          rw [←Real.rpow_natCast,←Real.rpow_mul hnR.le]
          congr 1
          push_cast
          ring
        rw [mul_pow,hePow]
  have h1 := mul_le_mul_of_nonneg_left hLS (Real.sqrt_nonneg (n:ℝ))
  have h2 := mul_le_mul_of_nonneg_right hτ2 (show (0:ℝ)≤72*Duke.r3 n by positivity)
  have hcancel : cs*(n:ℝ)^((1:ℝ)/2-δ) ≤ 72*ct^2*Duke.r3 n := by
    have hp : Real.sqrt n*(cs*(n:ℝ)^(-(δ/2)))=
        (cs*(n:ℝ)^((1:ℝ)/2-δ))*(n:ℝ)^(δ/2) := by
      rw [Real.sqrt_eq_rpow,mul_left_comm,←Real.rpow_add hnR,
        mul_assoc,←Real.rpow_add hnR]
      congr 1
      congr 1
      ring
    have hh : (cs*(n:ℝ)^((1:ℝ)/2-δ))*(n:ℝ)^(δ/2) ≤
        (72*ct^2*Duke.r3 n)*(n:ℝ)^(δ/2) := by
      rw [←hp]
      nlinarith only [h1,h2,hbase]
    exact le_of_mul_le_mul_right hh hpow
  have hout : (cs/(72*ct^2))*(n:ℝ)^((1:ℝ)/2-δ) ≤ Duke.r3 n := by
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    nlinarith only [hcancel]
  apply le_trans _ hout
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [min_le_left ε 1])

end ThreeSquares.B3
