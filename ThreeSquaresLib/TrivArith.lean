/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.CritTotal

/-!
# Arithmetic for the trivial ranges

* `sum_split_real`: `∑_{c ∈ T} F c = ∑_{r smooth} ∑_{q rough} [rq ∈ T] F(rq)` (real version);
* `norm_Tc_split`: `‖T_{rq}‖ ≤ rq √(2r) τ(q)` (`4 ∣ r` smooth, `q` rough);
* `sum_pdiv_le`: `∑_{r, q, rq ∈ T} r^{1/2 − s} q^{−s} ≤ p^{−s} ζ(s) ∏_{ℓ ∣ 2n} (1 − ℓ^{1/2−s})^{−1}`
  when every element of `T` is divisible by the prime `p ∤ 2n`.
-/

@[expose] public section

namespace ThreeSquares

open Finset

open Classical in
/-- **Reindexing real sums along the split.** -/
theorem sum_split_real (S : ℕ → Prop) (T : Finset ℕ) (N : ℕ) (hT : ∀ c ∈ T, 0 < c ∧ c ≤ N)
    (F : ℕ → ℝ) :
    ∑ c ∈ T, F c = ∑ r ∈ (range (N + 1)).filter (Smooth S), ∑ q ∈ (range (N + 1)).filter (Rough S),
      if r * q ∈ T then F (r * q) else 0 := by
  classical
  rw [← Finset.sum_product', ← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun x _ => x.1 * x.2) (fun x hx => (Finset.mem_filter.mp hx).2) ?_ ?_ ?_
  · intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_product] at hx hy
    have h0 : x.1 * x.2 ≠ 0 := (hT _ hx.2).1.ne'
    obtain ⟨e1, e2⟩ := split_unique hxy hx.1.1.2 hx.1.2.2 hy.1.1.2 hy.1.2.2 h0
    exact Prod.ext e1 e2
  · intro c hc
    obtain ⟨hc0, hcN⟩ := hT c hc
    obtain ⟨r, q, hrq, hr, hq⟩ := exists_split S c hc0.ne'
    have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; simp at hrq; omega)
    have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hrq; omega)
    have hrc : r ≤ c := by rw [hrq]; exact Nat.le_mul_of_pos_right _ hq0
    have hqc : q ≤ c := by rw [hrq]; exact Nat.le_mul_of_pos_left _ hr0
    refine ⟨(r, q), ?_, hrq.symm⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨⟨by omega, hr⟩, by omega, hq⟩, by rw [← hrq]; exact hc⟩
  · intro x _; rfl

/-- **`‖T_{rq}‖ ≤ rq √(2r) τ(q)`.** -/
theorem norm_Tc_split (n r q : ℕ) (hr : Smooth (S2 n) r) (hq : Rough (S2 n) q) (h4 : 4 ∣ r)
    (hr0 : 0 < r) (hq0 : 0 < q) :
    ‖Poin.Tc n (r * q)‖ ≤ ((r * q : ℕ) : ℝ) * Real.sqrt (2 * r) * q.divisors.card := by
  obtain ⟨m, rfl⟩ := h4
  have hm : 0 < m := by omega
  have hcop : (4 * m).Coprime q := coprime_of_smooth_rough hr hq
  have hodd : Odd q := by
    rw [Nat.odd_iff]
    have : ¬ 2 ∣ q := fun h2 => hq 2 Nat.prime_two h2 (show 2 ∣ 2 * n from dvd_mul_right 2 n)
    omega
  have hnq : Nat.Coprime n q :=
    Nat.coprime_of_dvd fun ℓ hℓ h1 h2 => hq ℓ hℓ h2 (show ℓ ∣ 2 * n from dvd_mul_of_dvd_right h1 2)
  refine (norm_Tc_le n m q hm hq0 hcop hodd hnq).trans (le_of_eq ?_)
  push_cast; ring

theorem sum_mult_rpow_le (p N : ℕ) (hp : 0 < p) (s : ℝ) (hs : 1 < s) :
    ∑ q ∈ (range (N + 1)).filter (fun q => 0 < q ∧ p ∣ q), (q : ℝ) ^ (-s) ≤
      (p : ℝ) ^ (-s) * ∑' q : ℕ, (q : ℝ) ^ (-s) := by
  have hsum : Summable (fun q : ℕ => (q : ℝ) ^ (-s)) := Real.summable_nat_rpow.mpr (by linarith)
  have hsub : (range (N + 1)).filter (fun q => 0 < q ∧ p ∣ q) ⊆ (Icc 1 N).image (fun q' => p * q') := by
    intro q hq
    simp only [mem_filter, mem_range] at hq
    obtain ⟨hqN, hq0, q', rfl⟩ := hq
    refine mem_image.mpr ⟨q', mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · exact Nat.pos_of_ne_zero (by rintro rfl; simp at hq0)
    · exact le_trans (Nat.le_mul_of_pos_left q' hp) (by omega)
  calc ∑ q ∈ (range (N + 1)).filter (fun q => 0 < q ∧ p ∣ q), (q : ℝ) ^ (-s)
      ≤ ∑ q ∈ (Icc 1 N).image (fun q' => p * q'), (q : ℝ) ^ (-s) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ q' ∈ Icc 1 N, ((p * q' : ℕ) : ℝ) ^ (-s) :=
        sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp h)
    _ = (p : ℝ) ^ (-s) * ∑ q' ∈ Icc 1 N, (q' : ℝ) ^ (-s) := by
        rw [mul_sum]; refine sum_congr rfl fun q' _ => ?_
        push_cast; rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    _ ≤ (p : ℝ) ^ (-s) * ∑' q : ℕ, (q : ℝ) ^ (-s) :=
        mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun _ _ => by positivity)) (by positivity)

open Classical in
theorem sum_smooth_rpow_le (n N : ℕ) (hn : 0 < n) (σ : ℝ) (hσ : 0 < σ) :
    ∑ r ∈ (range (N + 1)).filter (Smooth (S2 n)), (r : ℝ) ^ (-σ) ≤
      ∏ ℓ ∈ (2 * n).primeFactors, (1 - (ℓ : ℝ) ^ (-σ))⁻¹ := by
  classical
  rw [← sum_filter_of_ne (p := fun r => 0 < r) (fun r _ hne => by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0; simp [Real.zero_rpow (show -σ ≠ 0 by linarith)] at hne
      · exact h0)]
  refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity))
    (sum_smooth_le σ hσ (2 * n).primeFactors (fun q hq => Nat.prime_of_mem_primeFactors hq) (N + 1))
  intro r hr
  simp only [mem_filter, mem_range] at hr ⊢
  exact ⟨hr.1.1, hr.2, fun q hq hqr => Nat.mem_primeFactors.mpr ⟨hq, hr.1.2 q hq hqr, by omega⟩⟩

open Classical in
/-- **The split sum over multiples of `p`.** -/
theorem sum_pdiv_le (n p N : ℕ) (hn : 0 < n) (hp : p.Prime) (hpn : ¬ p ∣ 2 * n) (s : ℝ) (hs : 1 < s)
    (T : Finset ℕ) (hT : ∀ c ∈ T, 0 < c ∧ p ∣ c) :
    ∑ r ∈ (range (N + 1)).filter (Smooth (S2 n)), ∑ q ∈ (range (N + 1)).filter (Rough (S2 n)),
      (if r * q ∈ T then (r : ℝ) ^ (-(s - 1 / 2)) * (q : ℝ) ^ (-s) else 0) ≤
    (p : ℝ) ^ (-s) * (∑' q : ℕ, (q : ℝ) ^ (-s)) *
      ∏ ℓ ∈ (2 * n).primeFactors, (1 - (ℓ : ℝ) ^ (-(s - 1 / 2)))⁻¹ := by
  set Z := ∑' q : ℕ, (q : ℝ) ^ (-s)
  have hZ : 0 ≤ Z := tsum_nonneg fun _ => by positivity
  have hinner : ∀ r ∈ (range (N + 1)).filter (Smooth (S2 n)),
      ∑ q ∈ (range (N + 1)).filter (Rough (S2 n)),
        (if r * q ∈ T then (r : ℝ) ^ (-(s - 1 / 2)) * (q : ℝ) ^ (-s) else 0) ≤
      (r : ℝ) ^ (-(s - 1 / 2)) * ((p : ℝ) ^ (-s) * Z) := by
    intro r hr
    have hrs : Smooth (S2 n) r := (mem_filter.mp hr).2
    have hr4 : 0 ≤ (r : ℝ) ^ (-(s - 1 / 2)) := by positivity
    calc ∑ q ∈ (range (N + 1)).filter (Rough (S2 n)),
          (if r * q ∈ T then (r : ℝ) ^ (-(s - 1 / 2)) * (q : ℝ) ^ (-s) else 0)
        ≤ ∑ q ∈ (range (N + 1)).filter (Rough (S2 n)),
          (if 0 < q ∧ p ∣ q then (r : ℝ) ^ (-(s - 1 / 2)) * (q : ℝ) ^ (-s) else 0) := by
          refine sum_le_sum fun q _ => ?_
          by_cases h : r * q ∈ T
          · obtain ⟨h0, hd⟩ := hT _ h
            have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at h0)
            have hpq : p ∣ q := ((Nat.Prime.dvd_mul hp).mp hd).resolve_left
              (fun h' => hpn (hrs p hp h'))
            rw [if_pos h, if_pos ⟨hq0, hpq⟩]
          · rw [if_neg h]; split_ifs <;> positivity
      _ ≤ ∑ q ∈ range (N + 1),
          (if 0 < q ∧ p ∣ q then (r : ℝ) ^ (-(s - 1 / 2)) * (q : ℝ) ^ (-s) else 0) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun q _ _ => by split_ifs <;> positivity)
      _ = (r : ℝ) ^ (-(s - 1 / 2)) * ∑ q ∈ (range (N + 1)).filter (fun q => 0 < q ∧ p ∣ q),
            (q : ℝ) ^ (-s) := by rw [← sum_filter, mul_sum]
      _ ≤ (r : ℝ) ^ (-(s - 1 / 2)) * ((p : ℝ) ^ (-s) * Z) :=
          mul_le_mul_of_nonneg_left (sum_mult_rpow_le p N hp.pos s hs) hr4
  refine (sum_le_sum hinner).trans ?_
  rw [← sum_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (sum_smooth_rpow_le n N hn (s - 1 / 2) (by linarith))
    (by positivity)

end ThreeSquares
