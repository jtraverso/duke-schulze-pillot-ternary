/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.B3_Hyperbola

/-!
# Averages of `(1 * χ)` twisted by Dirichlet characters, and in residue classes

`χ = chiN n`, `n ≡ 3 (mod 8)`, `Sχ(y) = ∑_{e ≤ y} χ(e)/e → L` (hypothesis `hL`).
* `sum_char_chi1`: `∑_{m ≤ M} ψ(m) (1*χ)(m) = conv (ψχ) ψ M`.
* `tendsto_conv_nonprincipal`: `ψ ∉ {1, χ}` ⇒ `conv (ψχ) ψ M / M → 0`.
* `tendsto_conv_one`, `tendsto_conv_chi`: `ψ = 1` or `ψ = χ` ⇒ `→ (φ(n)/n) L`.
* `tendsto_classSum`: for a unit `c` with `χ(c) = 1`,
  `(1/M) ∑_{m ≤ M, m ≡ c} (1*χ)(m) → 2L/n`.
-/

@[expose] public section

namespace ThreeSquares.B3

open Finset Filter Topology

variable {n : ℕ} [NeZero n]

theorem conv_comm (a b : ℕ → ℂ) (M : ℕ) : conv a b M = conv b a M := by
  unfold conv
  refine sum_congr rfl fun m hm => ?_
  rw [mem_Ioc] at hm
  rw [← Nat.sum_div_divisors m]
  refine sum_congr rfl fun e he => ?_
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors he) (by omega), mul_comm]

theorem sum_char_chi1 (ψ : DirichletCharacter ℂ n) (M : ℕ) :
    ∑ m ∈ Ioc 0 M, ψ m * (chi1 n m : ℂ) = conv (chf (ψ * chiN n)) (chf ψ) M := by
  unfold conv
  refine sum_congr rfl fun m hm => ?_
  rw [chi1, Int.cast_sum, mul_sum]
  refine sum_congr rfl fun e he => ?_
  have hm : (m : ZMod n) = (e : ZMod n) * ((m / e : ℕ) : ZMod n) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)]
  simp only [chf, MulChar.coeToFun_mul, Pi.mul_apply, hm, map_mul, chiN_nat]
  ring

/-- `∑_{e ≤ y} χ(e)/e`. -/
noncomputable def Schi (n : ℕ) [NeZero n] (y : ℕ) : ℂ := ∑ e ∈ Ioc 0 y, chf (chiN n) e / e

theorem psum_nonprincipal {ψ : DirichletCharacter ℂ n} (hψ : ψ ≠ 1) (x : ℕ) :
    ‖psum (chf ψ) x‖ ≤ 2 * n := by
  have h := norm_psum_sub_le (Nat.pos_of_ne_zero (NeZero.ne n)) (chf_per ψ) (chf_norm ψ) x
  rwa [psum_char, if_neg hψ, mul_zero, sub_zero] at h

theorem tendsto_sqrt_div :
    Tendsto (fun M : ℕ => (Nat.sqrt M : ℝ) / M) atTop (𝓝 0) := by
  have h : ∀ M : ℕ, 1 ≤ M → (Nat.sqrt M : ℝ) / M ≤ 1 / Nat.sqrt M := by
    intro M hM
    have hs : 0 < Nat.sqrt M := Nat.sqrt_pos.mpr hM
    have hs' : (0 : ℝ) < Nat.sqrt M := by exact_mod_cast hs
    have hle : (Nat.sqrt M : ℝ) * Nat.sqrt M ≤ M := by exact_mod_cast Nat.sqrt_le M
    rw [div_le_div_iff₀ (by exact_mod_cast hM) hs']
    linarith
  have h2 : Tendsto (fun M : ℕ => 1 / (Nat.sqrt M : ℝ)) atTop (𝓝 0) := by
    have : Tendsto (fun M : ℕ => (Nat.sqrt M : ℝ)) atTop atTop := by
      refine tendsto_natCast_atTop_atTop.comp ?_
      refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨b * b, fun M hM => ?_⟩
      exact Nat.le_sqrt.mpr hM
    have h3 := tendsto_inv_atTop_zero.comp this
    simpa [one_div, Function.comp_def] using h3
  refine squeeze_zero' (Eventually.of_forall fun M => by positivity) ?_ h2
  filter_upwards [eventually_ge_atTop 1] with M hM
  exact h M hM

theorem tendsto_of_norm_le {f g : ℕ → ℂ} {L : ℂ} {C : ℝ} (hg : Tendsto g atTop (𝓝 L))
    (h : ∀ M : ℕ, ‖f M - g M‖ ≤ C * ((Nat.sqrt M : ℝ) / M)) : Tendsto f atTop (𝓝 L) := by
  have h0 : Tendsto (fun M => f M - g M) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun M => norm_nonneg _) h ?_
    simpa using tendsto_sqrt_div.const_mul C
  simpa using h0.add hg

theorem tendsto_conv_nonprincipal {ψ : DirichletCharacter ℂ n} (h1 : ψ ≠ 1)
    (h2 : ψ * chiN n ≠ 1) :
    Tendsto (fun M : ℕ => conv (chf (ψ * chiN n)) (chf ψ) M / M) atTop (𝓝 0) := by
  refine tendsto_of_norm_le (g := fun _ => 0) (C := 3 * (2 * n)) tendsto_const_nhds fun M => ?_
  rw [sub_zero]
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have := norm_conv_le (chf_norm _) (chf_norm ψ) (psum_nonprincipal h2) (psum_nonprincipal h1) M
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hM']
  calc ‖conv (chf (ψ * chiN n)) (chf ψ) M‖ ≤ 3 * (2 * n) * Nat.sqrt M := this
    _ = 3 * (2 * n) * ((Nat.sqrt M : ℝ) / M) * M := by field_simp

theorem tendsto_conv_one (hn : n % 8 = 3) {L : ℂ} (hL : Tendsto (Schi n) atTop (𝓝 L)) :
    Tendsto (fun M : ℕ => conv (chf (chiN n)) (chf (1 : DirichletCharacter ℂ n)) M / M) atTop
      (𝓝 ((n.totient : ℂ) / n * L)) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hχ : chiN n ≠ 1 := chiN_ne_one (by omega)
  have hP : ‖(n.totient : ℂ)‖ ≤ n := by
    rw [Complex.norm_natCast]; exact_mod_cast Nat.totient_le n
  have hB : ∀ x, ‖psum (chf (1 : DirichletCharacter ℂ n)) x - (x / n : ℂ) * n.totient‖ ≤ 2 * n := by
    intro x
    have := norm_psum_sub_le hn0 (chf_per 1) (chf_norm 1) x
    rwa [psum_char, if_pos rfl] at this
  have hg : Tendsto (fun M : ℕ => (n.totient : ℂ) / n * Schi n (Nat.sqrt M)) atTop
      (𝓝 ((n.totient : ℂ) / n * L)) := by
    refine (hL.comp ?_).const_mul _
    refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨b * b, fun M hM => ?_⟩
    exact Nat.le_sqrt.mpr hM
  refine tendsto_of_norm_le hg (C := 1 + 2 * n + 2 * (2 * n)) fun M => ?_
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp [Schi]
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have := norm_conv_sub_le hn0 (chf_norm _) (chf_norm 1) (psum_nonprincipal hχ) hP hB M
  have e : conv (chf (chiN n)) (chf (1 : DirichletCharacter ℂ n)) M / M -
      (n.totient : ℂ) / n * Schi n (Nat.sqrt M) =
      (conv (chf (chiN n)) (chf (1 : DirichletCharacter ℂ n)) M - (n.totient : ℂ) / n * M *
        ∑ e ∈ Ioc 0 (Nat.sqrt M), chf (chiN n) e / e) / M := by
    unfold Schi
    have : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
  rw [e, norm_div, Complex.norm_natCast, div_le_iff₀ hM']
  refine le_trans this (le_of_eq ?_)
  rw [mul_assoc _ ((Nat.sqrt M : ℝ) / M), div_mul_cancel₀ _ hM'.ne']

theorem tendsto_conv_chi (hn : n % 8 = 3) {L : ℂ} (hL : Tendsto (Schi n) atTop (𝓝 L)) :
    Tendsto (fun M : ℕ => conv (chf (chiN n * chiN n)) (chf (chiN n)) M / M) atTop
      (𝓝 ((n.totient : ℂ) / n * L)) := by
  have : chiN n * chiN n = 1 := by rw [← sq]; exact chiN_sq n
  simp_rw [this, conv_comm (chf 1)]
  exact tendsto_conv_one hn hL

/-- `∑_{m ≤ M, m ≡ c} (1*χ)(m)`. -/
noncomputable def classSum (n : ℕ) (c : ZMod n) (M : ℕ) : ℂ :=
  ∑ m ∈ (Ioc 0 M).filter (fun m : ℕ => (m : ZMod n) = c), (chi1 n m : ℂ)

theorem classSum_eq {c : ZMod n} (hc : IsUnit c) (M : ℕ) :
    classSum n c M = (n.totient : ℂ)⁻¹ * ∑ ψ : DirichletCharacter ℂ n,
      ψ c⁻¹ * conv (chf (ψ * chiN n)) (chf ψ) M := by
  have hφ : (n.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))).ne'
  rw [classSum, sum_filter]
  simp_rw [← sum_char_chi1]
  rw [mul_sum]
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  have key : ∑ ψ : DirichletCharacter ℂ n, (n.totient : ℂ)⁻¹ * (ψ c⁻¹ * (ψ m * (chi1 n m : ℂ))) =
      ((n.totient : ℂ)⁻¹ * ∑ ψ : DirichletCharacter ℂ n, ψ c⁻¹ * ψ m) * (chi1 n m : ℂ) := by
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun ψ _ => ?_
    ring
  rw [key, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hc]
  split_ifs with h1 h2 h2
  · field_simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

theorem tendsto_classSum (hn : n % 8 = 3) {L : ℂ} (hL : Tendsto (Schi n) atTop (𝓝 L))
    {c : ZMod n} (hc : IsUnit c) (hχc : chiN n c = 1) :
    Tendsto (fun M : ℕ => classSum n c M / M) atTop (𝓝 (2 * L / n)) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hφ : (n.totient : ℂ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hn0).ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hχ : chiN n ≠ 1 := chiN_ne_one (by omega)
  have hχinv : chiN n c⁻¹ = 1 := by
    have : chiN n c * chiN n c⁻¹ = 1 := by
      rw [← map_mul, ZMod.mul_inv_of_unit _ hc, map_one]
    rw [hχc, one_mul] at this
    exact this
  set g : DirichletCharacter ℂ n → ℂ := fun ψ =>
    if ψ = 1 then (n.totient : ℂ) / n * L else if ψ = chiN n then (n.totient : ℂ) / n * L else 0
  have hterm : ∀ ψ : DirichletCharacter ℂ n,
      Tendsto (fun M : ℕ => ψ c⁻¹ * conv (chf (ψ * chiN n)) (chf ψ) M / M) atTop (𝓝 (g ψ)) := by
    intro ψ
    simp_rw [mul_div_assoc]
    by_cases h1 : ψ = 1
    · subst h1
      have hu : IsUnit c⁻¹ := by
        obtain ⟨u, rfl⟩ := hc
        exact ⟨u⁻¹, (ZMod.inv_coe_unit u).symm⟩
      simpa [g, MulChar.one_apply hu] using tendsto_conv_one hn hL
    by_cases h2 : ψ = chiN n
    · subst h2
      simp only [g, if_neg h1, if_pos rfl, hχinv, one_mul]
      exact tendsto_conv_chi hn hL
    · simp only [g, if_neg h1, if_neg h2]
      have h3 : ψ * chiN n ≠ 1 := by
        intro h
        apply h2
        have := congrArg (· * chiN n) h
        simp only [mul_assoc, ← sq, chiN_sq, mul_one, one_mul] at this
        exact this
      simpa using (tendsto_conv_nonprincipal h1 h3).const_mul (ψ c⁻¹)
  have hsum := tendsto_finset_sum (Finset.univ : Finset (DirichletCharacter ℂ n))
    (fun ψ _ => hterm ψ)
  have hval : ∑ ψ : DirichletCharacter ℂ n, g ψ = 2 * ((n.totient : ℂ) / n * L) := by
    rw [Finset.sum_eq_add (1 : DirichletCharacter ℂ n) (chiN n) hχ.symm]
    · simp [g, hχ.symm, two_mul]
    · intro ψ _ hψ
      simp [g, hψ.1, hψ.2]
    · simp
    · simp
  rw [hval] at hsum
  have := hsum.const_mul (n.totient : ℂ)⁻¹
  convert this using 1
  · funext M
    rw [classSum_eq hc, mul_div_assoc, sum_div]
  · field_simp

end ThreeSquares.B3
