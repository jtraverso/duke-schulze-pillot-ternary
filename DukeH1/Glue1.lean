/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.RootsUnitary
public import DukeH1.Split

/-!
# Reindexing lemmas for the glue

* `sum_udiv_pairs`: `∑_{q ∈ Q} ∑_{a ∥ q} F(q, a) = ∑_{(a, b) coprime, ab ∈ Q} F(ab, a)`;
* `sum_dvd_mul`: `∑_{a ≤ N, p ∣ a} G(a) = ∑_{a' ≤ N/p} G(p a')`.
-/

@[expose] public section

namespace ThreeSquares

open Finset

theorem sum_udiv_pairs (Q : Finset ℕ) (N : ℕ) (hQ : ∀ q ∈ Q, 0 < q ∧ q ≤ N) (F : ℕ → ℕ → ℂ) :
    ∑ q ∈ Q, ∑ a ∈ udiv q, F q a =
      ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), if a.Coprime b ∧ a * b ∈ Q then F (a * b) a else 0 := by
  classical
  rw [Finset.sum_sigma', ← Finset.sum_product', ← Finset.sum_filter]
  refine Finset.sum_bij' (fun x _ => (x.2, x.1 / x.2)) (fun y _ => ⟨y.1 * y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_sigma] at hx
    obtain ⟨hq, ha⟩ := hx
    have ha' : (x.2 ∣ x.1 ∧ x.1 ≠ 0) ∧ x.2.Coprime (x.1 / x.2) := by
      simpa [udiv, Nat.mem_divisors] using ha
    obtain ⟨⟨hd, hq0⟩, hab⟩ := ha'
    have hle := (hQ _ hq).2
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨?_, ?_⟩, hab, ?_⟩
    · have := Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hd; omega
    · have := Nat.div_le_self x.1 x.2; omega
    · rw [Nat.mul_div_cancel' hd]; exact hq
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hy
    simp only [Finset.mem_sigma, udiv, Finset.mem_filter, Nat.mem_divisors]
    have h0 := (hQ _ hy.2.2).1
    have ha0 : 0 < y.1 := Nat.pos_of_ne_zero (by rintro h; rw [h] at h0; simp at h0)
    refine ⟨hy.2.2, ⟨⟨dvd_mul_right _ _, h0.ne'⟩, ?_⟩⟩
    rw [Nat.mul_div_cancel_left _ ha0]; exact hy.2.1
  · intro x hx
    simp only [Finset.mem_sigma] at hx
    have hd : x.2 ∣ x.1 := by
      have := hx.2; simp only [udiv, Finset.mem_filter, Nat.mem_divisors] at this; exact this.1.1
    simp only
    rw [Nat.mul_div_cancel' hd]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hy
    have h0 := (hQ _ hy.2.2).1
    have ha0 : 0 < y.1 := Nat.pos_of_ne_zero (by rintro h; rw [h] at h0; simp at h0)
    simp only
    rw [Nat.mul_div_cancel_left _ ha0]
  · intro x hx
    have hd : x.2 ∣ x.1 := by
      have := (Finset.mem_sigma.mp hx).2; simp only [udiv, Finset.mem_filter, Nat.mem_divisors] at this
      exact this.1.1
    simp only
    rw [Nat.mul_div_cancel' hd]

theorem sum_dvd_mul (N p : ℕ) (hp : 0 < p) (G : ℕ → ℂ) :
    ∑ a ∈ (range (N + 1)).filter (fun a => p ∣ a), G a = ∑ a' ∈ range (N / p + 1), G (p * a') := by
  classical
  symm
  refine Finset.sum_nbij' (fun a' => p * a') (fun a => a / p) ?_ ?_ ?_ ?_ ?_
  · intro a' ha'
    simp only [Finset.mem_range] at ha'
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, dvd_mul_right _ _⟩
    have h1 : a' ≤ N / p := Nat.lt_succ_iff.mp ha'
    have h2 := (Nat.le_div_iff_mul_le hp).mp h1
    rw [mul_comm]; omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.lt_succ_iff.mp ha.1))
  · intro a' _
    rw [Nat.mul_div_cancel_left _ hp]
  · intro a ha
    simp only [Finset.mem_filter] at ha
    exact Nat.mul_div_cancel' ha.2
  · intro a' _; rfl

end ThreeSquares
