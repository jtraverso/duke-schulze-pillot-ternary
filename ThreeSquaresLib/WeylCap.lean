/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Weyl
public import ThreeSquaresLib.Reduction

/-!
# From Weyl sums to points in caps

`dukeSquarefree_of_weyl`: if, on `S = {t squarefree, t ≡ 3 (mod 8)}`, the Weyl sums of harmonic
polynomials of degree `d ≥ 1` are `O(t^{d/2 + 1/2 − η})` and `r₃(t) ≥ c t^{1/2 − η/2}` for large
`t`, then `DukeSquarefree` holds.

The kernel is `((1 + u·x/√t)/2)^K`: its spherical mean is `1/(K+1)` (`kap_lin_pow`,
`sum_even_choose_div`), and outside the cap it is at most `(1 − ε²/4)^K`.
-/

@[expose] public section

namespace ThreeSquares.Duke

open MvPolynomial Finset

/-! ### Powers of a linear form -/

/-- The linear form `u · x`. -/
noncomputable def lin (u : Fin 3 → ℝ) : R3 := ∑ i, C (u i) * X i

theorem isHomogeneous_lin (u : Fin 3 → ℝ) : (lin u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _

theorem pderiv_lin (u : Fin 3 → ℝ) (i : Fin 3) : pderiv i (lin u) = C (u i) := by
  simp only [lin, map_sum, pderiv_C_mul, pderiv_X]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · simp

theorem pderiv_lin_pow (u : Fin 3 → ℝ) (i : Fin 3) (m : ℕ) :
    pderiv i (lin u ^ m) = C ((m : ℝ) * u i) * lin u ^ (m - 1) := by
  rw [pderiv_pow, pderiv_lin, map_mul, map_natCast]; ring

theorem lap_lin_pow (u : Fin 3 → ℝ) (hu : ∑ i, u i ^ 2 = 1) (n : ℕ) :
    lap (lin u ^ (n + 2)) = (((n + 2) * (n + 1) : ℕ) : ℝ) • lin u ^ n := by
  rw [lap_apply]
  have h : ∀ i : Fin 3, pderiv i (pderiv i (lin u ^ (n + 2))) =
      C (((n + 2) * (n + 1) : ℕ) : ℝ) * C (u i ^ 2) * lin u ^ n := by
    intro i
    rw [pderiv_lin_pow, pderiv_C_mul, pderiv_lin_pow, show n + 2 - 1 - 1 = n by omega, ← mul_assoc,
      ← map_mul, ← map_mul]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ => h i, ← Finset.sum_mul, ← Finset.mul_sum, ← map_sum, hu,
    map_one, mul_one, smul_eq_C_mul]

theorem lap_iter_lin_pow (u : Fin 3 → ℝ) (hu : ∑ i, u i ^ 2 = 1) :
    ∀ j, lap^[j] (lin u ^ (2 * j)) = C ((2 * j).factorial : ℝ)
  | 0 => by simp
  | j + 1 => by
    rw [Function.iterate_succ_apply, show 2 * (j + 1) = 2 * j + 2 by ring, lap_lin_pow u hu,
      ← lap_pow_apply, map_smul, lap_pow_apply, lap_iter_lin_pow u hu j, smul_eq_C_mul, ← map_mul,
      show 2 * j + 2 = (2 * j + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring_nf

theorem kap_lin_pow (u : Fin 3 → ℝ) (hu : ∑ i, u i ^ 2 = 1) (d : ℕ) :
    kap d (lin u ^ d) = if Even d then 1 / ((d : ℝ) + 1) else 0 := by
  unfold kap
  split_ifs with he
  · obtain ⟨j, rfl⟩ := he
    rw [show j + j = 2 * j by ring, Nat.mul_div_cancel_left j (by norm_num), lap_pow_apply,
      lap_iter_lin_pow u hu, constantCoeff_C, Nat.factorial_succ]
    have : ((2 * j).factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  · rfl

theorem eval_lin (u : Fin 3 → ℝ) (x : Fin 3 → ℤ) : eval (pt3 x) (lin u) = ∑ i, u i * x i := by
  simp [lin, pt3]

/-! ### The spherical mean of the kernel -/

theorem sum_odd_choose (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ range (n + 1), (if Odd i then (n.choose i : ℝ) else 0) = 2 ^ (n - 1) := by
  have h1 : ∑ i ∈ range (n + 1), (n.choose i : ℝ) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  have h2 : ∑ i ∈ range (n + 1), ((-1 : ℝ) ^ i * n.choose i) = 0 := by
    have := Int.alternating_sum_range_choose (n := n)
    rw [if_neg (by omega)] at this
    exact_mod_cast this
  have h3 : ∀ i, (if Odd i then (n.choose i : ℝ) else 0) =
      ((n.choose i : ℝ) - (-1) ^ i * n.choose i) / 2 := by
    intro i
    rcases Nat.even_or_odd i with he | ho
    · rw [if_neg (Nat.not_odd_iff_even.mpr he), he.neg_one_pow]; ring
    · rw [if_pos ho, ho.neg_one_pow]; ring
  rw [sum_congr rfl fun i _ => h3 i, ← sum_div, sum_sub_distrib, h1, h2, sub_zero]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [pow_succ, Nat.add_sub_cancel]; ring

theorem sum_even_choose_div (K : ℕ) :
    ∑ j ∈ range (K + 1), (if Even j then (K.choose j : ℝ) / ((j : ℝ) + 1) else 0) =
      2 ^ K / ((K : ℝ) + 1) := by
  have hK : (0 : ℝ) < K + 1 := by positivity
  have h : ∀ j, (if Even j then (K.choose j : ℝ) / ((j : ℝ) + 1) else 0) =
      (if Odd (j + 1) then ((K + 1).choose (j + 1) : ℝ) else 0) / ((K : ℝ) + 1) := by
    intro j
    have hc : ((K + 1) * K.choose j : ℝ) = (K + 1).choose (j + 1) * (j + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq K j
    by_cases he : Even j
    · rw [if_pos he, if_pos (Even.add_one he)]
      field_simp
      linarith
    · rw [if_neg he, if_neg (by rw [Nat.odd_add_one, not_not]; exact Nat.not_even_iff_odd.mp he),
        zero_div]
  rw [sum_congr rfl fun j _ => h j, ← sum_div]
  congr 1
  have := sum_odd_choose (K + 1) (by omega)
  rw [sum_range_succ'] at this
  simpa using this

/-! ### The kernel sum -/

/-- The kernel `((1 + u·x/√t)/2)^K` at a point of the sphere `|x|² = t`. -/
noncomputable def kern (u : Fin 3 → ℝ) (K t : ℕ) (x : Fin 3 → ℤ) : ℝ :=
  ((1 + (∑ i, u i * x i) / Real.sqrt t) / 2) ^ K

theorem kern_expand (u : Fin 3 → ℝ) (K t : ℕ) (_ht : 1 ≤ t) (x : Fin 3 → ℤ) :
    kern u K t x = ∑ j ∈ range (K + 1), ((K.choose j : ℝ) / 2 ^ K) *
      ((Real.sqrt t)⁻¹ ^ j * eval (pt3 x) (lin u ^ j)) := by
  unfold kern
  rw [div_pow, add_comm, add_pow]
  rw [sum_div]
  refine sum_congr rfl fun j _ => ?_
  rw [eval_pow, eval_lin]
  simp only [one_pow, mul_one]
  rw [div_eq_mul_inv (∑ i, u i * (x i : ℝ)), mul_pow]
  ring

theorem kern_sum (u : Fin 3 → ℝ) (K t : ℕ) (ht : 1 ≤ t) :
    ∑ x ∈ reps3 t, kern u K t x = ∑ j ∈ range (K + 1), ((K.choose j : ℝ) / 2 ^ K) *
      ((Real.sqrt t)⁻¹ ^ j * weylSum (lin u ^ j) t) := by
  simp_rw [kern_expand u K t ht]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [weylSum, mul_sum, mul_sum]

theorem kern_main (u : Fin 3 → ℝ) (hu : ∑ i, u i ^ 2 = 1) (K : ℕ) :
    ∑ j ∈ range (K + 1), ((K.choose j : ℝ) / 2 ^ K) * kap j (lin u ^ j) = 1 / ((K : ℝ) + 1) := by
  simp_rw [kap_lin_pow u hu]
  have h : ∀ j, ((K.choose j : ℝ) / 2 ^ K) * (if Even j then 1 / ((j : ℝ) + 1) else 0) =
      (if Even j then (K.choose j : ℝ) / ((j : ℝ) + 1) else 0) / 2 ^ K := by
    intro j; split_ifs
    · field_simp
    · simp
  rw [sum_congr rfl fun j _ => h j, ← sum_div, sum_even_choose_div]
  field_simp

/-- The kernel sum is `r₃(t)/(K+1) + O(t^{1/2 − η})`. -/
theorem kern_asymp {S : Set ℕ} {η : ℝ} (hW : WeylBound S η) (u : Fin 3 → ℝ)
    (hu : ∑ i, u i ^ 2 = 1) (K : ℕ) :
    ∃ C : ℝ, ∀ t ∈ S, 1 ≤ t →
      |∑ x ∈ reps3 t, kern u K t x - r3 t / ((K : ℝ) + 1)| ≤ C * (t : ℝ) ^ ((1 : ℝ) / 2 - η) := by
  have hj : ∀ j, ∃ C : ℝ, ∀ t ∈ S, 1 ≤ t →
      |weylSum (lin u ^ j) t - kap j (lin u ^ j) * (t : ℝ) ^ ((j : ℝ) / 2) * r3 t| ≤
        C * (t : ℝ) ^ ((j : ℝ) / 2 + 1 / 2 - η) :=
    fun j => weyl_hom hW j _ (by simpa using (isHomogeneous_lin u).pow j)
  choose C hC using hj
  refine ⟨∑ j ∈ range (K + 1), ((K.choose j : ℝ) / 2 ^ K) * |C j|, fun t ht ht1 => ?_⟩
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr htpos).ne'
  have hsq : ∀ j : ℕ, (Real.sqrt t)⁻¹ ^ j * (t : ℝ) ^ ((j : ℝ) / 2) = 1 := by
    intro j
    have : (t : ℝ) ^ ((j : ℝ) / 2) = Real.sqrt t ^ j := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul htpos.le]; ring_nf
    rw [this, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hs)]
  have hsq2 : ∀ j : ℕ, (Real.sqrt t)⁻¹ ^ j * (t : ℝ) ^ ((j : ℝ) / 2 + 1 / 2 - η) =
      (t : ℝ) ^ ((1 : ℝ) / 2 - η) := by
    intro j
    rw [show (j : ℝ) / 2 + 1 / 2 - η = (j : ℝ) / 2 + (1 / 2 - η) by ring,
      Real.rpow_add htpos, ← mul_assoc, hsq, one_mul]
  rw [kern_sum u K t ht1, show (r3 t : ℝ) / ((K : ℝ) + 1) = r3 t * (1 / ((K : ℝ) + 1)) by ring,
    ← kern_main u hu K, mul_sum, ← sum_sub_distrib]
  have e : ∀ j ∈ range (K + 1), ((K.choose j : ℝ) / 2 ^ K) *
      ((Real.sqrt t)⁻¹ ^ j * weylSum (lin u ^ j) t) - (r3 t : ℝ) *
      (((K.choose j : ℝ) / 2 ^ K) * kap j (lin u ^ j)) =
      ((K.choose j : ℝ) / 2 ^ K) * ((Real.sqrt t)⁻¹ ^ j *
        (weylSum (lin u ^ j) t - kap j (lin u ^ j) * (t : ℝ) ^ ((j : ℝ) / 2) * r3 t)) := by
    intro j _
    have := hsq j
    linear_combination (((K.choose j : ℝ) / 2 ^ K) * kap j (lin u ^ j) * r3 t) * this
  rw [sum_congr rfl e, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  have hpos : 0 ≤ (K.choose j : ℝ) / 2 ^ K := by positivity
  have hinv : 0 ≤ (Real.sqrt t)⁻¹ ^ j := by positivity
  rw [abs_mul, abs_of_nonneg hpos, abs_mul, abs_of_nonneg hinv,
    mul_assoc ((K.choose j : ℝ) / 2 ^ K) |C j|]
  refine mul_le_mul_of_nonneg_left ?_ hpos
  calc (Real.sqrt t)⁻¹ ^ j * |weylSum (lin u ^ j) t - kap j (lin u ^ j) *
        (t : ℝ) ^ ((j : ℝ) / 2) * r3 t|
      ≤ (Real.sqrt t)⁻¹ ^ j * (|C j| * (t : ℝ) ^ ((j : ℝ) / 2 + 1 / 2 - η)) := by
        refine mul_le_mul_of_nonneg_left ((hC j t ht ht1).trans ?_) hinv
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg htpos.le _)
    _ = |C j| * (t : ℝ) ^ ((1 : ℝ) / 2 - η) := by rw [← hsq2 j]; ring

/-! ### The cap argument -/

theorem kern_bounds (u : Fin 3 → ℝ) (hu : ∑ i, u i ^ 2 = 1) (K t : ℕ) (ht : 1 ≤ t)
    {x : Fin 3 → ℤ} (hx : x ∈ reps3 t) (ε : ℝ) :
    0 ≤ kern u K t x ∧ (¬ Near u ε t x → 0 ≤ ε → kern u K t x ≤ (1 - ε ^ 2 / 4) ^ K) := by
  rw [mem_reps3] at hx
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  set r := Real.sqrt t with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr htpos
  have hr2 : r ^ 2 = t := Real.sq_sqrt htpos.le
  have hx' : ((x 0 : ℝ)) ^ 2 + (x 1 : ℝ) ^ 2 + (x 2 : ℝ) ^ 2 = t := by
    have : ((∑ i, x i ^ 2 : ℤ) : ℝ) = (t : ℝ) := by rw [hx]; simp
    simpa [Fin.sum_univ_three] using this
  have hu' : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by simpa [Fin.sum_univ_three] using hu
  set s := ∑ i, u i * (x i : ℝ) with hs
  have hs' : s = u 0 * x 0 + u 1 * x 1 + u 2 * x 2 := by simp [hs, Fin.sum_univ_three]
  have hplus : ((x 0 : ℝ) + r * u 0) ^ 2 + ((x 1 : ℝ) + r * u 1) ^ 2 + ((x 2 : ℝ) + r * u 2) ^ 2 =
      2 * t + 2 * r * s := by
    rw [hs']; linear_combination hx' + r ^ 2 * hu' + hr2
  have hlow : -r ≤ s := by
    have h0 : 0 ≤ 2 * t + 2 * r * s := by rw [← hplus]; positivity
    have : r * (-r) ≤ r * s := by nlinarith [hr2]
    exact le_of_mul_le_mul_left this hr0
  have hbase0 : 0 ≤ (1 + s / r) / 2 := by
    have : -1 ≤ s / r := by rw [le_div_iff₀ hr0]; linarith
    linarith
  refine ⟨pow_nonneg hbase0 K, fun hnot hε => ?_⟩
  unfold kern
  rw [← hs, ← hr]
  apply pow_le_pow_left₀ hbase0
  unfold Near at hnot
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  rw [← hr] at hi
  have h0 : 0 ≤ ε * r := by positivity
  have hsq : (ε * r) ^ 2 < ((x i : ℝ) - r * u i) ^ 2 := by
    have := pow_lt_pow_left₀ hi h0 (by norm_num : (2 : ℕ) ≠ 0)
    rwa [sq_abs] at this
  have htot : ((x 0 : ℝ) - r * u 0) ^ 2 + ((x 1 : ℝ) - r * u 1) ^ 2 + ((x 2 : ℝ) - r * u 2) ^ 2 =
      2 * t - 2 * r * s := by
    rw [hs']; linear_combination hx' + r ^ 2 * hu' + hr2
  have hge : ((x i : ℝ) - r * u i) ^ 2 ≤ 2 * t - 2 * r * s := by
    rw [← htot]
    have a0 := sq_nonneg ((x 0 : ℝ) - r * u 0)
    have a1 := sq_nonneg ((x 1 : ℝ) - r * u 1)
    have a2 := sq_nonneg ((x 2 : ℝ) - r * u 2)
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]; linarith
    · simp only [Fin.mk_one, Fin.isValue]; linarith
    · simp only [Fin.reduceFinMk, Fin.isValue]; linarith
  have key : ε ^ 2 * t < 2 * t - 2 * r * s := by
    have : (ε * r) ^ 2 = ε ^ 2 * t := by rw [mul_pow, hr2]
    linarith
  have e : 2 * r * (r * (1 - ε ^ 2 / 2)) = 2 * t - ε ^ 2 * t := by rw [← hr2]; ring
  have h7 : 2 * r * s < 2 * r * (r * (1 - ε ^ 2 / 2)) := by rw [e]; linarith
  have h8 := lt_of_mul_lt_mul_left h7 (by positivity)
  have : s / r < 1 - ε ^ 2 / 2 := by
    rw [div_lt_iff₀ hr0]; linarith
  linarith

theorem exists_K_small {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    ∃ K : ℕ, ((K : ℝ) + 1) * ρ ^ K < 1 / 2 := by
  have t1 := tendsto_self_mul_const_pow_of_lt_one h0 h1
  have t2 := tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have t3 := t1.add t2
  rw [add_zero] at t3
  have := (t3.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).exists
  obtain ⟨K, hK⟩ := this
  exact ⟨K, by simpa [add_mul] using hK⟩

/-- **Weyl criterion for caps.** -/
theorem dukeSquarefree_of_weyl {η : ℝ} (hη : 0 < η)
    (hW : WeylBound {t | Squarefree t ∧ t % 8 = 3} η)
    (hL : ∃ c > 0, ∃ T : ℕ, ∀ t : ℕ, T ≤ t → Squarefree t → t % 8 = 3 →
      c * (t : ℝ) ^ ((1 : ℝ) / 2 - η / 2) ≤ r3 t) :
    DukeSquarefree := by
  intro u hu ε hε
  set ε₁ := min ε 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  set ρ := 1 - ε₁ ^ 2 / 4 with hρ
  have hρ0 : 0 ≤ ρ := by nlinarith
  have hρ1 : ρ < 1 := by have := pow_pos hε₁0 2; linarith
  obtain ⟨K, hK⟩ := exists_K_small hρ0 hρ1
  obtain ⟨C, hC⟩ := kern_asymp hW u hu K
  obtain ⟨c, hc, T, hT⟩ := hL
  set B := 2 * ((K : ℝ) + 1) * |C| / c with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (B ^ (2 / η))
  refine ⟨max (max T (N + 1)) 1, fun t ht hsq ht8 => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_right _ _) ht
  have htT : T ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htN : N + 1 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  have hS : t ∈ {t | Squarefree t ∧ t % 8 = 3} := ⟨hsq, ht8⟩
  by_contra hno
  push Not at hno
  -- every point is outside the smaller cap
  have hout : ∀ x ∈ reps3 t, kern u K t x ≤ ρ ^ K := by
    intro x hx
    refine (kern_bounds u hu K t ht1 hx ε₁).2 (fun hnear => ?_) hε₁0.le
    refine hno x ((mem_reps3 t x).mp hx) (fun i => (hnear i).trans ?_)
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
  have hsum_le : ∑ x ∈ reps3 t, kern u K t x ≤ ρ ^ K * r3 t := by
    calc ∑ x ∈ reps3 t, kern u K t x ≤ ∑ _x ∈ reps3 t, ρ ^ K := sum_le_sum hout
      _ = ρ ^ K * r3 t := by rw [sum_const, nsmul_eq_mul, r3, mul_comm]
  have hasym := hC t hS ht1
  have hlow := hT t htT hsq ht8
  have hr3 : 0 ≤ (r3 t : ℝ) := by positivity
  have hM : ρ ^ K < 1 / (2 * ((K : ℝ) + 1)) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  -- `r₃ (1/(K+1) − ρ^K) ≤ |C| t^{1/2 − η}`
  have h1 : (r3 t : ℝ) / ((K : ℝ) + 1) - |C| * (t : ℝ) ^ ((1 : ℝ) / 2 - η) ≤ ρ ^ K * r3 t := by
    have := (abs_le.mp hasym).1
    have hCt : C * (t : ℝ) ^ ((1 : ℝ) / 2 - η) ≤ |C| * (t : ℝ) ^ ((1 : ℝ) / 2 - η) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg htpos.le _)
    linarith
  have h2 : (r3 t : ℝ) / (2 * ((K : ℝ) + 1)) ≤ |C| * (t : ℝ) ^ ((1 : ℝ) / 2 - η) := by
    have : (r3 t : ℝ) / (2 * ((K : ℝ) + 1)) = (r3 t : ℝ) / ((K : ℝ) + 1) -
        (r3 t : ℝ) * (1 / (2 * ((K : ℝ) + 1))) := by field_simp; ring
    rw [this]
    nlinarith
  have hsplit : (t : ℝ) ^ ((1 : ℝ) / 2 - η / 2) =
      (t : ℝ) ^ (η / 2) * (t : ℝ) ^ ((1 : ℝ) / 2 - η) := by
    rw [← Real.rpow_add htpos]; ring_nf
  have hpos2 : 0 < (t : ℝ) ^ ((1 : ℝ) / 2 - η) := Real.rpow_pos_of_pos htpos _
  have h3 : c * (t : ℝ) ^ (η / 2) ≤ 2 * ((K : ℝ) + 1) * |C| := by
    have h4 : c * (t : ℝ) ^ ((1 : ℝ) / 2 - η / 2) ≤
        2 * ((K : ℝ) + 1) * (|C| * (t : ℝ) ^ ((1 : ℝ) / 2 - η)) := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((K : ℝ) + 1))).mp h2
      linarith
    rw [hsplit] at h4
    have : (c * (t : ℝ) ^ (η / 2)) * (t : ℝ) ^ ((1 : ℝ) / 2 - η) ≤
        (2 * ((K : ℝ) + 1) * |C|) * (t : ℝ) ^ ((1 : ℝ) / 2 - η) := by linarith
    exact le_of_mul_le_mul_right this hpos2
  have h5 : (t : ℝ) ^ (η / 2) ≤ B := by
    rw [hB, le_div_iff₀ hc]; linarith
  -- but `t > B^{2/η}`
  have h6 : B < (t : ℝ) ^ (η / 2) := by
    have htB : B ^ (2 / η) < t := by
      have : (N : ℝ) + 1 ≤ t := by exact_mod_cast htN
      linarith
    have := Real.rpow_lt_rpow (Real.rpow_nonneg hB0 _) htB (by positivity : 0 < η / 2)
    rwa [← Real.rpow_mul hB0, show 2 / η * (η / 2) = 1 by field_simp, Real.rpow_one] at this
  linarith

end ThreeSquares.Duke
