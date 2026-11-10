/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.BlockConv

/-!
# Bounds for one block

`ABsum` is the class-restricted bilinear sum over a block `I × J`. We bound `∑_p ‖ABsum_p‖` by
Method 1 (`m1_block`), Method 2 (`m2_block`, `m2_block'`) or Pólya–Vinogradov (`pv_block'`).
-/

@[expose] public section

open FourSquaresCaps

namespace ThreeSquares

open ZMod Finset

/-- The block sum. -/
noncomputable def ABsum (n p y Y r t₁ t₂ : ℕ) (I J : Finset ℕ) (W : ℕ → ℂ) (h : ℕ → ℤ) : ℂ :=
  ∑ a ∈ I.filter (fun a => a % r = t₁), ∑ b ∈ J.filter (fun b => b % r = t₂),
    chiR n a * chiR n b * ker1 r y Y W (h b) p a b

theorem ker2_congr (r y Y : ℕ) (W W' : ℕ → ℂ) (hW : ∀ c, y < c → c ≤ Y → W c = W' c) (m : ℤ)
    (p a b : ℕ) : ker2 r y Y W m p a b = ker2 r y Y W' m p a b := by
  unfold ker2
  split_ifs with hc
  · rw [hW _ hc.1 hc.2]
  · rfl

open Classical in
theorem sum_filter_rough (n r t : ℕ) (J : Finset ℕ) (f : ℕ → ℂ) :
    ∑ b ∈ J.filter (fun b => b % r = t), chiR n b * f b =
      ∑ b ∈ J.filter (fun b => b % r = t ∧ Rough (S2 n) b), chiR n b * f b := by
  conv_rhs => rw [← Finset.filter_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rfl
  · rw [chiR_eq_zero_of_not_rough h, zero_mul]

theorem isUnit_hInv (n r b : ℕ) (σ : ℤ) (hσ : IsCoprime σ b) (hb : 0 < b) (hrb : r.Coprime b) :
    IsUnit ((hInv σ r b : ℤ) : ZMod b) := by
  haveI : NeZero b := ⟨hb.ne'⟩
  unfold hInv
  rw [dif_neg hb.ne']
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  have h1 : IsUnit ((σ : ZMod b)) := isUnit_of_isCoprime hσ
  have h2 : IsUnit ((r : ZMod b)) := by rw [ZMod.isUnit_iff_coprime]; exact hrb
  exact h1.mul (isUnit_inv_of_isUnit h2)

theorem isCoprime_four_n (n b : ℕ) (hb : Rough (S2 n) b) (s : ℤ) (hs : s = 4 ∨ s = -4) :
    IsCoprime (s * n) (b : ℤ) := by
  have hbn : Nat.Coprime (4 * n) b := by
    have h2 : Nat.Coprime 2 b := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      (fun h => hb 2 Nat.prime_two h (dvd_mul_right 2 n))
    have h4 : Nat.Coprime 4 b := by simpa using Nat.Coprime.pow_left 2 h2
    exact Nat.coprime_mul_iff_left.mpr ⟨h4, rough_coprime_n hb⟩
  rcases hs with rfl | rfl
  · exact_mod_cast Nat.isCoprime_iff_coprime.mpr hbn
  · have := Nat.isCoprime_iff_coprime.mpr hbn
    push_cast at this
    rw [show (-4 : ℤ) * n = -(4 * n) by ring]; exact this.neg_left

open Classical in
/-- Rewriting a block sum with rough `b` and a smooth weight. -/
theorem ABsum_eq (n p y Y r t₁ t₂ : ℕ) (I J : Finset ℕ) (W W' : ℕ → ℂ)
    (hWW : ∀ c, y < c → c ≤ Y → W c = W' c) (h : ℕ → ℤ) (ht₁ : t₁ < r) :
    ABsum n p y Y r t₁ t₂ I J W h =
      ∑ a ∈ I.filter (fun a => a % r = t₁ % r), ∑ b ∈ J.filter (fun b => b % r = t₂ ∧ Rough (S2 n) b),
        chiR n a * chiR n b * ker1 r y Y W' (h b) p a b := by
  unfold ABsum
  rw [Nat.mod_eq_of_lt ht₁]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e := sum_filter_rough n r t₂ J (fun b => chiR n a * ker1 r y Y W (h b) p a b)

  calc ∑ b ∈ J.filter (fun b => b % r = t₂), chiR n a * chiR n b * ker1 r y Y W (h b) p a b
      = ∑ b ∈ J.filter (fun b => b % r = t₂), chiR n b * (chiR n a * ker1 r y Y W (h b) p a b) :=
        Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ b ∈ J.filter (fun b => b % r = t₂ ∧ Rough (S2 n) b), chiR n b * (chiR n a * ker1 r y Y W (h b) p a b) := e
    _ = _ := Finset.sum_congr rfl fun b _ => by rw [ker1_congr r y Y W W' hWW]; ring

open Classical in
/-- **A Method-1 block.** -/
theorem m1_block (Ps : Finset ℕ) (P n r y Y t₁ t₂ A : ℕ) (J : Finset ℕ) (W W' : ℕ → ℂ) {W₀ W₁ : ℝ}
    (hW' : SmoothW W' W₀ W₁) (hWW : ∀ c, y < c → c ≤ Y → W c = W' c) (σ : ℤ)
    (hσ : σ = 4 * n ∨ σ = -4 * n) (hr : 0 < r) (hrA : r ≤ A) (ht₁ : t₁ < r) (hrs : Smooth (S2 n) r)
    (hJ : ∀ b ∈ J, 0 < b) (hPs : ∀ p ∈ Ps, 1 ≤ p ∧ p ≤ P) :
    (∑ p ∈ Ps, ‖ABsum n p y Y r t₁ t₂ (Ioc A (2 * A)) J W (hInv σ r)‖) ^ 2 ≤
      (((Ioc A (2 * A)).filter (fun a => a % r = t₁ % r)).card *
        (J.filter (fun b => b % r = t₂ ∧ Rough (S2 n) b)).card : ℝ) *
      ((Ps.card * (J.filter (fun b => b % r = t₂ ∧ Rough (S2 n) b)).card *
          ((Ioc A (2 * A)).filter (fun a => a % r = t₁ % r)).card : ℝ) * W₀ ^ 2 +
        (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (P : ℝ) ^ 2 *
          ∑ b ∈ J.filter (fun b => b % r = t₂ ∧ Rough (S2 n) b),
            ((((2 * A / r + 1 : ℕ) : ℝ) / b + (1 + Real.log b)) *
              (2 ^ b.primeFactors.card * Real.sqrt b * Real.sqrt (sfp b) * b.divisors.card))) := by
  simp_rw [ABsum_eq n _ y Y r t₁ t₂ _ J W W' hWW _ ht₁]
  refine method1_bound Ps P r y Y W' hW' A t₁ _ (fun b hb => hJ b (Finset.mem_filter.mp hb).1) hr hrA
    (hInv σ r) (chiR n) (chiR n) (norm_chiR_le n) (norm_chiR_le n) hPs (fun b hb => ?_) (fun b hb => ?_)
  · have hb := (Finset.mem_filter.mp hb).2.2
    rw [ZMod.isUnit_iff_coprime]; exact coprime_of_smooth_rough hrs hb
  · have hb' := Finset.mem_filter.mp hb
    have hs : σ = (4 : ℤ) * n ∨ σ = (-4 : ℤ) * n := hσ
    rcases hs with hs | hs
    · exact isUnit_hInv n r b σ (by rw [hs]; exact isCoprime_four_n n b hb'.2.2 4 (Or.inl rfl))
        (hJ b hb'.1) (coprime_of_smooth_rough hrs hb'.2.2)
    · exact isUnit_hInv n r b σ (by rw [hs]; exact isCoprime_four_n n b hb'.2.2 (-4) (Or.inr rfl))
        (hJ b hb'.1) (coprime_of_smooth_rough hrs hb'.2.2)

theorem coprime_4n_prime {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ 2 * n) : Nat.Coprime (4 * n) p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h4 | hn
  · have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4)
    exact hpn (this.trans (dvd_mul_right 2 n))
  · exact hpn (hn.trans (dvd_mul_left n 2))

theorem coprime_4n_rough {n b : ℕ} (hb : Rough (S2 n) b) : Nat.Coprime (4 * n) b := by
  have h2 : Nat.Coprime 2 b := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
    (fun h => hb 2 Nat.prime_two h (dvd_mul_right 2 n))
  have h4 : Nat.Coprime 4 b := by simpa using Nat.Coprime.pow_left 2 h2
  exact Nat.coprime_mul_iff_left.mpr ⟨h4, rough_coprime_n hb⟩

open Classical in
/-- The Method-2 rewriting of a block (case `p ∣ a`). -/
theorem ABsum_eq_m2 (ℓ n p y Y r t₁ t₂ : ℕ) (I J : Finset ℕ) (W2' : ℕ → ℂ)
    (hWW : ∀ c, y < c → c ≤ Y → W2 ℓ n c = W2' c) (hr : 0 < r) (hp : p.Prime) (hpn : ¬ p ∣ 2 * n)
    (hrs : Smooth (S2 n) r) (hI : ∀ a ∈ I, 0 < a) (hJ : ∀ b ∈ J, 0 < b) :
    ABsum n p y Y r t₁ t₂ I J (W1 ℓ n) (hInv (-4 * n) r) =
      rph r (2 * n) ((p * t₁ * t₂ : ℕ) : ℤ) ^ 2 *
        ∑ b ∈ J.filter (fun b => b % r = t₂), ∑ a ∈ I.filter (fun a => a % r = t₁ ∧ Rough (S2 n) a),
          chiR n b * chiR n a * ker2 r y Y W2' (4 * n) p b a := by
  unfold ABsum
  -- restrict `a` to rough integers
  have e1 : ∀ a ∈ I.filter (fun a => a % r = t₁),
      ∑ b ∈ J.filter (fun b => b % r = t₂), chiR n a * chiR n b * ker1 r y Y (W1 ℓ n) (hInv (-4 * n) r b) p a b =
        chiR n a * ∑ b ∈ J.filter (fun b => b % r = t₂), chiR n b * ker1 r y Y (W1 ℓ n) (hInv (-4 * n) r b) p a b := by
    intro a _; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl e1, sum_filter_rough n r t₁ I]
  conv_lhs => simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp only [Finset.mem_filter] at ha hb
  by_cases hbr : Rough (S2 n) b
  · rw [ker1_eq_ker2 ℓ n r y Y p a b hr hp hpn hrs ha.2.2 hbr (hI a ha.1) (hJ b hb.1),
      ker2_congr r y Y (W2 ℓ n) W2' hWW]
    have hρ : rph r (2 * n) ((p * a * b : ℕ) : ℤ) = rph r (2 * n) ((p * t₁ * t₂ : ℕ) : ℤ) := by
      rw [rph_mod r _ (p * a * b), rph_mod r _ (p * t₁ * t₂)]
      congr 2
      rw [← ha.2.1, ← hb.2]
      exact Nat.ModEq.mul (Nat.ModEq.mul_left p (Nat.mod_modEq a r).symm) (Nat.mod_modEq b r).symm
    rw [hρ]; ring
  · rw [chiR_eq_zero_of_not_rough hbr]; ring

theorem norm_rph_sq_le (r : ℕ) (h : ℤ) (x : ℤ) : ‖rph r h x ^ 2‖ ≤ 1 := by
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_rph_le _ _ _)

open Classical in
/-- **A Method-2 block** (case `p ∣ a`). -/
theorem m2_block (Ps : Finset ℕ) (P₀ P ℓ n r y Y t₁ t₂ B : ℕ) (I : Finset ℕ) (W2' : ℕ → ℂ) {W₀ W₁ : ℝ}
    (hW' : SmoothW W2' W₀ W₁) (hWW : ∀ c, y < c → c ≤ Y → W2 ℓ n c = W2' c) (hP₀ : 0 < P₀)
    (hr : 0 < r) (hrB : r ≤ B) (ht₂ : t₂ < r) (hrs : Smooth (S2 n) r) (hI : ∀ a ∈ I, 0 < a ∧ a < P₀)
    (hPs : ∀ p ∈ Ps, p.Prime ∧ ¬ p ∣ 2 * n ∧ P₀ ≤ p ∧ p ≤ P) :
    (∑ p ∈ Ps, ‖ABsum n p y Y r t₁ t₂ I (Ioc B (2 * B)) (W1 ℓ n) (hInv (-4 * n) r)‖) ^ 2 ≤
      (((Ioc B (2 * B)).filter (fun b => b % r = t₂ % r)).card *
        (I.filter (fun a => a % r = t₁ ∧ Rough (S2 n) a)).card : ℝ) *
      ((Ps.card * (I.filter (fun a => a % r = t₁ ∧ Rough (S2 n) a)).card *
          ((Ioc B (2 * B)).filter (fun b => b % r = t₂ % r)).card : ℝ) * W₀ ^ 2 +
        (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (4 * (P : ℝ) ^ 3) *
          ∑ a ∈ I.filter (fun a => a % r = t₁ ∧ Rough (S2 n) a),
            ((((2 * B / r + 1 : ℕ) : ℝ) / ((P₀ : ℝ) ^ 2 * a) + (1 + Real.log ((P : ℝ) ^ 2 * a))) *
              (2 ^ a.primeFactors.card * Real.sqrt a * Real.sqrt (sfp a) * a.divisors.card))) := by
  have hle : ∀ p ∈ Ps, ‖ABsum n p y Y r t₁ t₂ I (Ioc B (2 * B)) (W1 ℓ n) (hInv (-4 * n) r)‖ ≤
      ‖∑ b ∈ (Ioc B (2 * B)).filter (fun b => b % r = t₂ % r),
        ∑ a ∈ I.filter (fun a => a % r = t₁ ∧ Rough (S2 n) a),
          chiR n b * chiR n a * ker2 r y Y W2' (4 * n) p b a‖ := by
    intro p hp
    obtain ⟨hpp, hpn, -, -⟩ := hPs p hp
    rw [ABsum_eq_m2 ℓ n p y Y r t₁ t₂ I _ W2' hWW hr hpp hpn hrs (fun a ha => (hI a ha).1)
      (fun b hb => by simp only [Finset.mem_Ioc] at hb; omega), norm_mul, Nat.mod_eq_of_lt ht₂]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_rph_sq_le _ _ _)
  refine le_trans (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (Finset.sum_le_sum hle) 2) ?_
  refine method2_bound' Ps P₀ P hP₀ r y Y W2' hW' B t₂ _ hr hrB (4 * n) (chiR n) (chiR n)
    (norm_chiR_le n) (norm_chiR_le n) (fun p hp => ⟨(hPs p hp).1, (hPs p hp).2.2⟩) ?_ ?_ ?_ ?_
  · intro p hp a ha
    have ha' := hI a (Finset.mem_filter.mp ha).1
    exact Nat.coprime_of_lt_prime ha'.1.ne' (lt_of_lt_of_le ha'.2 (hPs p hp).2.2.1) (hPs p hp).1
  · intro p hp
    exact coprime_of_smooth_rough hrs (rough_prime (hPs p hp).1 (hPs p hp).2.1)
  · intro p hp
    have := coprime_4n_prime (hPs p hp).1 (hPs p hp).2.1
    simpa [Int.natAbs_mul] using this
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    refine ⟨coprime_of_smooth_rough hrs ha'.2.2, (hI a ha'.1).1, ?_⟩
    have := coprime_4n_rough ha'.2.2
    simpa [Int.natAbs_mul] using this

open Classical in
/-- The Method-2 rewriting of a block (mirror: weights `W₂`, sign `−`). -/
theorem ABsum_eq_m2' (ℓ n p y Y r t₁ t₂ : ℕ) (I J : Finset ℕ) (W2' : ℕ → ℂ)
    (hWW : ∀ c, y < c → c ≤ Y → W1 ℓ n c = W2' c) (hr : 0 < r) (hp : p.Prime) (hpn : ¬ p ∣ 2 * n)
    (hrs : Smooth (S2 n) r) (hI : ∀ a ∈ I, 0 < a) (hJ : ∀ b ∈ J, 0 < b) :
    ABsum n p y Y r t₁ t₂ I J (W2 ℓ n) (hInv (4 * n) r) =
      rph r (-2 * n) ((p * t₁ * t₂ : ℕ) : ℤ) ^ 2 *
        ∑ b ∈ J.filter (fun b => b % r = t₂), ∑ a ∈ I.filter (fun a => a % r = t₁ ∧ Rough (S2 n) a),
          chiR n b * chiR n a * ker2 r y Y W2' (-4 * n) p b a := by
  unfold ABsum
  -- restrict `a` to rough integers
  have e1 : ∀ a ∈ I.filter (fun a => a % r = t₁),
      ∑ b ∈ J.filter (fun b => b % r = t₂), chiR n a * chiR n b * ker1 r y Y (W2 ℓ n) (hInv (4 * n) r b) p a b =
        chiR n a * ∑ b ∈ J.filter (fun b => b % r = t₂), chiR n b * ker1 r y Y (W2 ℓ n) (hInv (4 * n) r b) p a b := by
    intro a _; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl e1, sum_filter_rough n r t₁ I]
  conv_lhs => simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp only [Finset.mem_filter] at ha hb
  by_cases hbr : Rough (S2 n) b
  · rw [ker1_eq_ker2' ℓ n r y Y p a b hr hp hpn hrs ha.2.2 hbr (hI a ha.1) (hJ b hb.1),
      ker2_congr r y Y (W1 ℓ n) W2' hWW]
    have hρ : rph r (-2 * n) ((p * a * b : ℕ) : ℤ) = rph r (-2 * n) ((p * t₁ * t₂ : ℕ) : ℤ) := by
      rw [rph_mod r _ (p * a * b), rph_mod r _ (p * t₁ * t₂)]
      congr 2
      rw [← ha.2.1, ← hb.2]
      exact Nat.ModEq.mul (Nat.ModEq.mul_left p (Nat.mod_modEq a r).symm) (Nat.mod_modEq b r).symm
    rw [hρ]; ring
  · rw [chiR_eq_zero_of_not_rough hbr]; ring

open Classical in
/-- **A Method-2 block** (mirror: weights `W₂`, sign `−`). -/
theorem m2_block' (Ps : Finset ℕ) (P₀ P ℓ n r y Y t₁ t₂ B : ℕ) (I : Finset ℕ) (W2' : ℕ → ℂ) {W₀ W₁ : ℝ}
    (hW' : SmoothW W2' W₀ W₁) (hWW : ∀ c, y < c → c ≤ Y → W1 ℓ n c = W2' c) (hP₀ : 0 < P₀)
    (hr : 0 < r) (hrB : r ≤ B) (ht₂ : t₂ < r) (hrs : Smooth (S2 n) r) (hI : ∀ a ∈ I, 0 < a ∧ a < P₀)
    (hPs : ∀ p ∈ Ps, p.Prime ∧ ¬ p ∣ 2 * n ∧ P₀ ≤ p ∧ p ≤ P) :
    (∑ p ∈ Ps, ‖ABsum n p y Y r t₁ t₂ I (Ioc B (2 * B)) (W2 ℓ n) (hInv (4 * n) r)‖) ^ 2 ≤
      (((Ioc B (2 * B)).filter (fun b => b % r = t₂ % r)).card *
        (I.filter (fun a => a % r = t₁ ∧ Rough (S2 n) a)).card : ℝ) *
      ((Ps.card * (I.filter (fun a => a % r = t₁ ∧ Rough (S2 n) a)).card *
          ((Ioc B (2 * B)).filter (fun b => b % r = t₂ % r)).card : ℝ) * W₀ ^ 2 +
        (3 * W₀ ^ 2 + 4 * W₀ * W₁) * (4 * (P : ℝ) ^ 3) *
          ∑ a ∈ I.filter (fun a => a % r = t₁ ∧ Rough (S2 n) a),
            ((((2 * B / r + 1 : ℕ) : ℝ) / ((P₀ : ℝ) ^ 2 * a) + (1 + Real.log ((P : ℝ) ^ 2 * a))) *
              (2 ^ a.primeFactors.card * Real.sqrt a * Real.sqrt (sfp a) * a.divisors.card))) := by
  have hle : ∀ p ∈ Ps, ‖ABsum n p y Y r t₁ t₂ I (Ioc B (2 * B)) (W2 ℓ n) (hInv (4 * n) r)‖ ≤
      ‖∑ b ∈ (Ioc B (2 * B)).filter (fun b => b % r = t₂ % r),
        ∑ a ∈ I.filter (fun a => a % r = t₁ ∧ Rough (S2 n) a),
          chiR n b * chiR n a * ker2 r y Y W2' (-4 * n) p b a‖ := by
    intro p hp
    obtain ⟨hpp, hpn, -, -⟩ := hPs p hp
    rw [ABsum_eq_m2' ℓ n p y Y r t₁ t₂ I _ W2' hWW hr hpp hpn hrs (fun a ha => (hI a ha).1)
      (fun b hb => by simp only [Finset.mem_Ioc] at hb; omega), norm_mul, Nat.mod_eq_of_lt ht₂]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_rph_sq_le _ _ _)
  refine le_trans (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (Finset.sum_le_sum hle) 2) ?_
  refine method2_bound' Ps P₀ P hP₀ r y Y W2' hW' B t₂ _ hr hrB (-4 * n) (chiR n) (chiR n)
    (norm_chiR_le n) (norm_chiR_le n) (fun p hp => ⟨(hPs p hp).1, (hPs p hp).2.2⟩) ?_ ?_ ?_ ?_
  · intro p hp a ha
    have ha' := hI a (Finset.mem_filter.mp ha).1
    exact Nat.coprime_of_lt_prime ha'.1.ne' (lt_of_lt_of_le ha'.2 (hPs p hp).2.2.1) (hPs p hp).1
  · intro p hp
    exact coprime_of_smooth_rough hrs (rough_prime (hPs p hp).1 (hPs p hp).2.1)
  · intro p hp
    have := coprime_4n_prime (hPs p hp).1 (hPs p hp).2.1
    simpa [Int.natAbs_mul] using this
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    refine ⟨coprime_of_smooth_rough hrs ha'.2.2, (hI a ha'.1).1, ?_⟩
    have := coprime_4n_rough ha'.2.2
    simpa [Int.natAbs_mul] using this

open Classical in
/-- **A Pólya–Vinogradov block.** -/
theorem pv_block' (Ps : Finset ℕ) (n r y Y t₁ t₂ A : ℕ) (J : Finset ℕ) (W W' : ℕ → ℂ) {W₀ W₁ : ℝ}
    (hW' : SmoothW W' W₀ W₁) (hWW : ∀ c, y < c → c ≤ Y → W c = W' c) (h : ℕ → ℤ) (hn : Squarefree n)
    (hn4 : n % 4 = 3) (h8 : 8 ∣ r) (hr0 : 0 < r) (hrs : Smooth (S2 n) r) (ht₁ : t₁ < r)
    (hu₁ : IsUnit ((t₁ : ZMod r))) (hn₀ : 1 < n / Nat.gcd n r) (hJ : ∀ b ∈ J, 0 < b ∧ r * b ≤ A)
    (hPs : ∀ p ∈ Ps, 0 < p) :
    ∑ p ∈ Ps, ‖ABsum n p y Y r t₁ t₂ (Ioc A (2 * A)) J W h‖ ≤
      ∑ p ∈ Ps, ∑ b ∈ J.filter (fun b => b % r = t₂ ∧ Rough (S2 n) b),
        (b : ℝ) * ((3 * W₀ + 2 * W₁) * (Real.sqrt (n / Nat.gcd n r : ℕ) * (1 + Real.log (n / Nat.gcd n r : ℕ)))) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn4
  set n₀ := n / Nat.gcd n r
  have hn₀0 : n₀ ≠ 0 := by omega
  haveI : NeZero n₀ := ⟨hn₀0⟩
  have hn₀dvd : n₀ ∣ n := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n r)
  have hsq₀ : Squarefree n₀ := hn.squarefree_of_dvd hn₀dvd
  have hodd₀ : Odd n₀ := Odd.of_dvd_nat (Nat.odd_iff.mpr (by omega)) hn₀dvd
  have hcop₀ : Nat.Coprime n₀ r := coprime_div_gcd hn hn0
  refine Finset.sum_le_sum fun p hp => ?_
  rw [ABsum_eq n p y Y r t₁ t₂ _ J W W' hWW h ht₁, Finset.sum_comm]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b hb => ?_)
  have hb' := Finset.mem_filter.mp hb
  obtain ⟨hb0, hrbA⟩ := hJ b hb'.1
  have hbr := hb'.2.2
  -- factor `χ(b)` and `J(t₁ | n₁)`
  have hfac : ∀ a ∈ (Ioc A (2 * A)).filter (fun a => a % r = t₁ % r),
      chiR n a * chiR n b * ker1 r y Y W' (h b) p a b =
        chiR n b * (jacobiSym (t₁ : ℤ) (Nat.gcd n r) : ℂ) * ((jacobiSym (a : ℤ) n₀ : ℂ) * ker1 r y Y W' (h b) p a b) := by
    intro a ha
    have ha' := (Finset.mem_filter.mp ha).2
    rw [Nat.mod_eq_of_lt ht₁] at ha'
    rw [chiR_eq_jac n r a t₁ hn hn0 hn4 h8 hr0 hrs ha' hu₁]; ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum, norm_mul]
  have hc : ‖chiR n b * (jacobiSym (t₁ : ℤ) (Nat.gcd n r) : ℂ)‖ ≤ 1 := by
    rw [norm_mul]
    refine mul_le_one₀ (norm_chiR_le n b) (norm_nonneg _) ?_
    rcases jacobiSym.trichotomy (t₁ : ℤ) (Nat.gcd n r) with e | e | e <;> rw [e] <;> simp
  refine le_trans (mul_le_of_le_one_left (norm_nonneg _) hc) ?_
  have hu : IsUnit (((r * b : ℕ)) : ZMod n₀) := by
    rw [ZMod.isUnit_iff_coprime]
    have h2 : Nat.Coprime b n₀ := (Nat.Coprime.coprime_dvd_left hn₀dvd (rough_coprime_n hbr)).symm
    exact Nat.coprime_mul_iff_left.mpr ⟨hcop₀.symm, h2⟩
  exact pv_block hsq₀ hodd₀ hn₀ r y Y W' hW' (h b) A t₁ b p hr0 hb0 (coprime_of_smooth_rough hrs hbr)
    hrbA (hPs p hp) hu

end ThreeSquares
