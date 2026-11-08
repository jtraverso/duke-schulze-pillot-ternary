/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.TSplit
public import ThreeSquaresLib.Glue1

/-!
# The per-level decomposition of the Kloosterman sum

`critSum ℓ n p y Y = ∑_{y < c ≤ Y, 8p ∣ c} cfac(c) T_c` equals
`∑_{r smooth, 8 ∣ r} ∑_{(a,b) coprime, p ∣ ab, y < rab ≤ Y} W₁(rab) Γ_r(ab) χ(a) χ(b) e_b(−4n \overline{ra}) e_r(−2n \overline{ab})`
(`critSum_eq`).
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset

/-- The primes dividing `2n`. -/
def S2 (n : ℕ) : ℕ → Prop := fun ℓ => ℓ ∣ 2 * n

/-- The critical sum at level `8p`. -/
noncomputable def critSum (ℓ n p y Y : ℕ) : ℂ :=
  ∑ c ∈ (Ioc y Y).filter (fun c => 8 * p ∣ c), Poin.cfac ℓ n c * Poin.Tc n c

open Classical in
/-- `χ(m) = J(−n | m)` on integers coprime to `2n`, zero otherwise. -/
noncomputable def chiR (n m : ℕ) : ℂ := if Rough (S2 n) m then (jacobiSym (-(n : ℤ)) m : ℂ) else 0

/-- The weight `c · cfac(c) · e(2n/c)`. -/
noncomputable def W1 (ℓ n c : ℕ) : ℂ :=
  (c : ℂ) * Poin.cfac ℓ n c * Complex.exp (2 * Real.pi * Complex.I * (2 * (n : ℤ) / c))

/-- `Γ_r(x) = T_r(x̄, n) / r`. -/
noncomputable def Gam (n r x : ℕ) : ℂ :=
  if hr : r = 0 then 0 else (@Tq r ⟨hr⟩ (((x : ZMod r))⁻¹) (n : ZMod r)) / r

theorem gcdA_cast_eq_inv (q r : ℕ) (h : r.Coprime q) (hr : 0 < r) :
    ((Nat.gcdA q r : ℤ) : ZMod r) = ((q : ZMod r))⁻¹ := by
  haveI : NeZero r := ⟨hr.ne'⟩
  have hb := Nat.gcd_eq_gcd_ab q r
  rw [Nat.Coprime.gcd_eq_one h.symm] at hb
  have h1 : (q : ZMod r) * ((Nat.gcdA q r : ℤ) : ZMod r) = 1 := by
    have := congrArg (fun t : ℤ => (t : ZMod r)) hb
    push_cast at this
    rw [ZMod.natCast_self, zero_mul, add_zero] at this
    exact this.symm
  exact (ZMod.inv_eq_of_mul_eq_one _ _ _ h1).symm

theorem rough_mul_iff {n a b : ℕ} : Rough (S2 n) (a * b) ↔ Rough (S2 n) a ∧ Rough (S2 n) b := by
  constructor
  · intro h
    exact ⟨fun ℓ hℓ hd => h ℓ hℓ (dvd_mul_of_dvd_left hd _), fun ℓ hℓ hd => h ℓ hℓ (dvd_mul_of_dvd_right hd _)⟩
  · rintro ⟨ha, hb⟩ ℓ hℓ hd
    rcases (Nat.Prime.dvd_mul hℓ).mp hd with h | h
    · exact ha ℓ hℓ h
    · exact hb ℓ hℓ h

theorem rough_odd {n q : ℕ} (hq : Rough (S2 n) q) (hq0 : 0 < q) : Odd q := by
  rw [Nat.odd_iff]
  by_contra h
  have h2 : 2 ∣ q := Nat.dvd_of_mod_eq_zero (by omega)
  exact hq 2 Nat.prime_two h2 (dvd_mul_right 2 n)

theorem rough_coprime_n {n q : ℕ} (hq : Rough (S2 n) q) : Nat.Coprime n q := by
  by_contra h
  obtain ⟨ℓ, hℓ, h1, h2⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact hq ℓ hℓ h2 (dvd_mul_of_dvd_right h1 2)

open Classical in
/-- The inner identity for a fixed smooth `r` with `8 ∣ r`. -/
theorem critSum_inner (ℓ n p y Y r : ℕ) (hp : p.Prime) (hpn : ¬ p ∣ 2 * n) (hr : Smooth (S2 n) r)
    (h8 : 8 ∣ r) (hr0 : 0 < r) :
    ∑ q ∈ (range (Y + 1)).filter (Rough (S2 n)),
        (if r * q ∈ (Ioc y Y).filter (fun c => 8 * p ∣ c) then Poin.cfac ℓ n (r * q) * Poin.Tc n (r * q) else 0) =
      ∑ a ∈ range (Y + 1), ∑ b ∈ range (Y + 1),
          if a.Coprime b ∧ p ∣ a * b ∧ y < r * a * b ∧ r * a * b ≤ Y then
            W1 ℓ n (r * a * b) * Gam n r (a * b) * (chiR n a * chiR n b) *
              (rph b (-4 * n) ((r * a : ℕ) : ℤ) * rph r (-2 * n) ((a * b : ℕ) : ℤ))
          else 0 := by
  set T := (Ioc y Y).filter (fun c => 8 * p ∣ c)
  set Qs := (range (Y + 1)).filter (Rough (S2 n))
  -- Step A: expand `T_{rq}`
  have hA : ∀ q ∈ Qs, (if r * q ∈ T then Poin.cfac ℓ n (r * q) * Poin.Tc n (r * q) else 0) =
      if r * q ∈ T then ∑ a ∈ udiv q, W1 ℓ n (r * q) * Gam n r q * (jacobiSym (-(n : ℤ)) q : ℂ) *
        (rph (q / a) (-4 * n) ((r * a : ℕ) : ℤ) * rph r (-2 * n) ((a * (q / a) : ℕ) : ℤ)) else 0 := by
    intro q hq
    split_ifs with hT
    · simp only [Qs, Finset.mem_filter, Finset.mem_range] at hq
      simp only [T, Finset.mem_filter, Finset.mem_Ioc] at hT
      have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hT)
      have hrq : r.Coprime q := coprime_of_smooth_rough hr hq.2
      rw [Tc_expand n r q hr0 hq0 hrq (rough_odd hq.2 hq0) (rough_coprime_n hq.2)]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      unfold W1 Gam
      rw [dif_neg hr0.ne']
      haveI : NeZero r := ⟨hr0.ne'⟩
      rw [gcdA_cast_eq_inv q r hrq hr0]
      have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
      push_cast
      field_simp
    · rfl
  rw [Finset.sum_congr rfl hA, ← Finset.sum_filter]
  rw [sum_udiv_pairs (Qs.filter (fun q => r * q ∈ T)) Y (fun q hq => by
      simp only [Qs, T, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hq
      refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hq), by omega⟩) _]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  simp only [Qs, T, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  by_cases hc : a.Coprime b ∧ ((a * b < Y + 1 ∧ Rough (S2 n) (a * b)) ∧
      (y < r * (a * b) ∧ r * (a * b) ≤ Y) ∧ 8 * p ∣ r * (a * b))
  · obtain ⟨hab, ⟨-, hro⟩, ⟨h1, h2⟩, h3⟩ := hc
    have hpab : p ∣ a * b := by
      have : p ∣ r * (a * b) := (dvd_mul_left p 8).trans h3
      rcases (Nat.Prime.dvd_mul hp).mp this with h | h
      · exact absurd (hr p hp h) hpn
      · exact h
    have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
    have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
    haveI : NeZero a := ⟨ha0.ne'⟩
    haveI : NeZero b := ⟨hb0.ne'⟩
    have hle : a * b ≤ r * (a * b) := Nat.le_mul_of_pos_left _ hr0
    rw [if_pos ⟨hab, ⟨by omega, hro⟩, ⟨h1, h2⟩, h3⟩, if_pos ⟨hab, hpab, by rw [mul_assoc]; exact h1,
      by rw [mul_assoc]; exact h2⟩]
    obtain ⟨hra, hrb⟩ := rough_mul_iff.mp hro
    unfold chiR
    rw [if_pos hra, if_pos hrb, Nat.mul_div_cancel_left _ ha0, jacobiSym.mul_right, mul_assoc r a b]
    push_cast; ring
  · rw [if_neg hc]
    split_ifs with hc'
    · -- then `ab` is not rough, so a character vanishes
      obtain ⟨hab, hpab, h1, h2⟩ := hc'
      have hnr : ¬ Rough (S2 n) (a * b) := by
        intro hro
        apply hc
        refine ⟨hab, ⟨?_, hro⟩, ⟨by rw [← mul_assoc]; exact h1, by rw [← mul_assoc]; exact h2⟩, ?_⟩
        · have : a * b ≤ r * a * b := by rw [mul_assoc]; exact Nat.le_mul_of_pos_left _ hr0
          omega
        · exact Nat.mul_dvd_mul h8 hpab
      rw [rough_mul_iff, not_and_or] at hnr
      unfold chiR
      rcases hnr with h | h
      · rw [if_neg h]; ring
      · rw [if_neg h]; ring
    · rfl

open Classical in
/-- **The per-level decomposition.** -/
theorem critSum_eq (ℓ n p y Y : ℕ) (hp : p.Prime) (hpn : ¬ p ∣ 2 * n) :
    critSum ℓ n p y Y =
      ∑ r ∈ (range (Y + 1)).filter (fun r => Smooth (S2 n) r ∧ 8 ∣ r),
        ∑ a ∈ range (Y + 1), ∑ b ∈ range (Y + 1),
          if a.Coprime b ∧ p ∣ a * b ∧ y < r * a * b ∧ r * a * b ≤ Y then
            W1 ℓ n (r * a * b) * Gam n r (a * b) * (chiR n a * chiR n b) *
              (rph b (-4 * n) ((r * a : ℕ) : ℤ) * rph r (-2 * n) ((a * b : ℕ) : ℤ))
          else 0 := by
  unfold critSum
  set T := (Ioc y Y).filter (fun c => 8 * p ∣ c)
  rw [sum_split (S2 n) T Y (fun c hc => by
      simp only [T, Finset.mem_filter, Finset.mem_Ioc] at hc; exact ⟨by omega, hc.1.2⟩)]
  conv_rhs => rw [← Finset.filter_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun r hr => ?_
  simp only [Finset.mem_filter] at hr
  split_ifs with h8
  · rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
      · intro a _; refine Finset.sum_eq_zero fun b _ => ?_; simp
      · intro q _; simp [T]
    · exact critSum_inner ℓ n p y Y r hp hpn hr.2 h8 h0
  · refine Finset.sum_eq_zero fun q hq => ?_
    rw [if_neg]
    intro hT
    simp only [T, Finset.mem_filter] at hT
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    apply h8
    have h1 : 8 ∣ r * q := (dvd_mul_right 8 p).trans hT.2
    have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hT)
    have hc : Nat.Coprime 8 q := by
      have hodd := rough_odd hq.2 hq0
      exact Nat.Coprime.pow_left 3 ((Nat.coprime_two_left).mpr hodd) |> fun h => by simpa using h
    exact hc.dvd_of_dvd_mul_right h1

end ThreeSquares
