/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.Glue3

/-!
# The per-level inequality

`‖critSum‖ ≤ ∑_{r} ∑_{t₁, t₂ < r} √(2r) (‖A_{r,t₁,t₂}(W₁, h_A)‖ + ‖A_{r,t₁,t₂}(W₂, h_B)‖)` where `A` is a
bilinear sum of the shape of Method 1 (`critSum_le`).
-/

@[expose] public section

namespace ThreeSquares

open ZMod Finset

/-- The weight `c · cfac(c) · e(−2n/c)`. -/
noncomputable def W2 (ℓ n c : ℕ) : ℂ :=
  (c : ℂ) * Poin.cfac ℓ n c * Complex.exp (2 * Real.pi * Complex.I * (2 * (-(n : ℤ)) / c))

/-- The class-restricted bilinear sum. -/
noncomputable def Asum (n p y Y r t₁ t₂ : ℕ) (W : ℕ → ℂ) (h : ℕ → ℤ) : ℂ :=
  ∑ a ∈ (range (Y + 1)).filter (fun a => a % r = t₁), ∑ b ∈ (range (Y + 1)).filter (fun b => b % r = t₂),
    chiR n a * chiR n b * ker1 r y Y W (h b) p a b

theorem rph_eq_zero_of_not_coprime (b : ℕ) (h : ℤ) (x : ℕ) (hx : ¬ x.Coprime b) : rph b h (x : ℤ) = 0 := by
  unfold rph
  split_ifs with hb
  · rfl
  · haveI : NeZero b := ⟨hb⟩
    unfold RML.ExpSum.Weil.reciprocalPhase
    rw [if_neg]
    push_cast
    rw [ZMod.isUnit_iff_coprime]; exact hx

/-- The class factor `Φ_r(x) = Γ_r(x) e_r(h x̄)`. -/
noncomputable def Phi (n r : ℕ) (h : ℤ) (x : ℕ) : ℂ := Gam n r x * rph r h (x : ℤ)

theorem Phi_mod (n r : ℕ) (h : ℤ) (x : ℕ) : Phi n r h x = Phi n r h (x % r) := by
  unfold Phi; rw [Gam_mod, rph_mod r h x]

/-- Splitting a double sum along classes mod `r` with a class factor. -/
theorem sum_class_split (r : ℕ) (hr : 0 < r) (s₁ s₂ : Finset ℕ) (Φ : ℕ → ℕ → ℂ) (X : ℕ → ℕ → ℂ)
    (hΦ : ∀ a b, Φ a b = Φ (a % r) (b % r)) :
    ∑ a ∈ s₁, ∑ b ∈ s₂, Φ a b * X a b =
      ∑ t₁ ∈ range r, ∑ t₂ ∈ range r, Φ t₁ t₂ *
        ∑ a ∈ s₁.filter (fun a => a % r = t₁), ∑ b ∈ s₂.filter (fun b => b % r = t₂), X a b := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun a => a % r) (t := range r)
    (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hr))]
  refine Finset.sum_congr rfl fun t₁ ht₁ => ?_
  have h2 : ∀ a ∈ s₁.filter (fun a => a % r = t₁), ∑ b ∈ s₂, Φ a b * X a b =
      ∑ t₂ ∈ range r, ∑ b ∈ s₂.filter (fun b => b % r = t₂), Φ a b * X a b := fun a _ =>
    (Finset.sum_fiberwise_of_maps_to (g := fun b => b % r) (t := range r)
      (fun b _ => Finset.mem_range.mpr (Nat.mod_lt _ hr)) _).symm
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t₂ ht₂ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  simp only [Finset.mem_filter] at ha hb
  rw [hΦ a b, ha.2, hb.2]

/-- The term of `critSum_eq`. -/
noncomputable def TermG (ℓ n r a b : ℕ) : ℂ :=
  W1 ℓ n (r * a * b) * Gam n r (a * b) * (chiR n a * chiR n b) *
    (rph b (-4 * n) ((r * a : ℕ) : ℤ) * rph r (-2 * n) ((a * b : ℕ) : ℤ))

theorem chiR_eq_zero_of_not_rough {n m : ℕ} (h : ¬ Rough (S2 n) m) : chiR n m = 0 := by
  unfold chiR; rw [if_neg h]

theorem rough_prime {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ 2 * n) : Rough (S2 n) p := by
  intro ℓ hℓ hd
  rw [(Nat.prime_dvd_prime_iff_eq hℓ hp).mp hd]
  exact hpn

/-- **Case `p ∣ a`, termwise.** -/
theorem caseA_term (ℓ n p y Y r a b : ℕ) (hp : p.Prime) (hpn : ¬ p ∣ 2 * n) (hr : Smooth (S2 n) r)
    (hr0 : 0 < r) :
    (if (p * a).Coprime b ∧ y < r * (p * a) * b ∧ r * (p * a) * b ≤ Y then TermG ℓ n r (p * a) b else 0) =
      chiR n p * (Phi n r (-2 * n) (p * a * b) *
        (chiR n a * chiR n b * ker1 r y Y (W1 ℓ n) (hInv (-4 * n) r b) p a b)) := by
  unfold ker1 TermG Phi
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  by_cases hro : Rough (S2 n) b
  · have hrb : r.Coprime b := coprime_of_smooth_rough hr hro
    by_cases hc : (p * a).Coprime b
    · by_cases hR : y < r * (p * a) * b ∧ r * (p * a) * b ≤ Y
      · rw [if_pos ⟨hc, hR⟩, if_pos (by rw [show r * p * a * b = r * (p * a) * b by ring]; exact hR)]
        rw [chiR_mul n p a hp.ne_zero ha.ne', show r * (p * a) = r * (p * a) from rfl,
          rph_mul_r (-4 * n) r b (p * a) hb hrb,
          show r * p * a * b = r * (p * a) * b by ring, show p * a * b = (p * a) * b from rfl]
        ring
      · rw [if_neg (fun h => hR h.2), if_neg (by rw [show r * p * a * b = r * (p * a) * b by ring]; exact hR)]
        ring
    · rw [if_neg (fun h => hc h.1)]
      split_ifs
      · rw [rph_eq_zero_of_not_coprime b _ (p * a) hc]; ring
      · ring
  · rw [chiR_eq_zero_of_not_rough hro]
    split_ifs <;> ring

theorem form_swap' (r a b : ℕ) (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (hra : r.Coprime a) (hrb : r.Coprime b) (hab : a.Coprime b) (n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (2 * ((n : ℤ) : ℂ) / ((r * a * b : ℕ) : ℂ))) *
        (rph b (-4 * n) ((r * a : ℕ) : ℤ) * rph r (-2 * n) ((a * b : ℕ) : ℤ)) =
      Complex.exp (2 * Real.pi * Complex.I * (2 * ((-(n : ℤ) : ℤ) : ℂ) / ((r * a * b : ℕ) : ℂ))) *
        (rph a (4 * n) ((r * b : ℕ) : ℤ) * rph r (2 * n) ((b * a : ℕ) : ℤ)) := by
  have h := form_swap r a b hr ha hb hra hrb hab (n : ℤ)
  have e1 : ((r : ℂ) * ((a * b : ℕ) : ℂ)) = ((r * a * b : ℕ) : ℂ) := by push_cast; ring
  have e2 : ((r : ℂ) * ((b * a : ℕ) : ℂ)) = ((r * a * b : ℕ) : ℂ) := by push_cast; ring
  rw [e1, e2, show (-4 * -(n : ℤ)) = 4 * n by ring, show (-2 * -(n : ℤ)) = 2 * n by ring] at h
  rw [← mul_assoc, h, mul_assoc]
  push_cast; ring

/-- **Case `p ∣ b`, termwise** (via `form_swap`). -/
theorem caseB_term (ℓ n p y Y r a b : ℕ) (hp : p.Prime) (hpn : ¬ p ∣ 2 * n) (hr : Smooth (S2 n) r)
    (hr0 : 0 < r) :
    (if a.Coprime (p * b) ∧ y < r * a * (p * b) ∧ r * a * (p * b) ≤ Y then TermG ℓ n r a (p * b) else 0) =
      chiR n p * (Phi n r (2 * n) (p * b * a) *
        (chiR n b * chiR n a * ker1 r y Y (W2 ℓ n) (hInv (4 * n) r a) p b a)) := by
  unfold ker1 TermG Phi
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha; simp
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  by_cases hro : Rough (S2 n) a
  · have hra : r.Coprime a := coprime_of_smooth_rough hr hro
    by_cases hrob : Rough (S2 n) b
    · have hrb : r.Coprime (p * b) := coprime_of_smooth_rough hr
        (rough_mul_iff.mpr ⟨rough_prime hp hpn, hrob⟩)
      by_cases hc : a.Coprime (p * b)
      · by_cases hR : y < r * a * (p * b) ∧ r * a * (p * b) ≤ Y
        · rw [if_pos ⟨hc, hR⟩, if_pos (by rw [show r * p * b * a = r * a * (p * b) by ring]; exact hR)]
          have hsw := form_swap' r a (p * b) hr0 ha (Nat.mul_pos hp.pos hb) hra hrb hc n
          rw [chiR_mul n p b hp.ne_zero hb.ne', ← rph_mul_r (4 * n) r a (p * b) ha hra,
            show r * p * b * a = r * a * (p * b) by ring]
          unfold W1 W2
          have eG : Gam n r (a * (p * b)) = Gam n r (p * b * a) := by rw [mul_comm a]
          have eR : (((a * (p * b)) : ℕ) : ℤ) = (((p * b) * a : ℕ) : ℤ) := by rw [mul_comm a]
          rw [eG]
          calc ((r * a * (p * b) : ℕ) : ℂ) * Poin.cfac ℓ n (r * a * (p * b)) *
                Complex.exp (2 * Real.pi * Complex.I * (2 * ((n : ℤ) : ℂ) / ((r * a * (p * b) : ℕ) : ℂ))) *
                Gam n r (p * b * a) * (chiR n a * (chiR n p * chiR n b)) *
                (rph (p * b) (-4 * n) ((r * a : ℕ) : ℤ) * rph r (-2 * n) ((a * (p * b) : ℕ) : ℤ))
              = ((r * a * (p * b) : ℕ) : ℂ) * Poin.cfac ℓ n (r * a * (p * b)) * Gam n r (p * b * a) *
                (chiR n a * (chiR n p * chiR n b)) *
                (Complex.exp (2 * Real.pi * Complex.I * (2 * ((n : ℤ) : ℂ) / ((r * a * (p * b) : ℕ) : ℂ))) *
                  (rph (p * b) (-4 * n) ((r * a : ℕ) : ℤ) * rph r (-2 * n) ((a * (p * b) : ℕ) : ℤ))) := by ring
            _ = ((r * a * (p * b) : ℕ) : ℂ) * Poin.cfac ℓ n (r * a * (p * b)) * Gam n r (p * b * a) *
                (chiR n a * (chiR n p * chiR n b)) *
                (Complex.exp (2 * Real.pi * Complex.I * (2 * ((-(n : ℤ) : ℤ) : ℂ) / ((r * a * (p * b) : ℕ) : ℂ))) *
                  (rph a (4 * n) ((r * (p * b) : ℕ) : ℤ) * rph r (2 * n) (((p * b) * a : ℕ) : ℤ))) := by rw [hsw]
            _ = _ := by push_cast; ring
        · rw [if_neg (fun h => hR h.2), if_neg (by rw [show r * p * b * a = r * a * (p * b) by ring]; exact hR)]
          ring
      · rw [if_neg (fun h => hc h.1)]
        split_ifs
        · rw [rph_eq_zero_of_not_coprime a _ (p * b) (fun h => hc h.symm)]; ring
        · ring
    · rw [chiR_eq_zero_of_not_rough hrob]
      have : chiR n (p * b) = 0 := by
        unfold chiR; rw [if_neg (fun h => hrob (rough_mul_iff.mp h).2)]
      split_ifs <;> simp [this]
  · rw [chiR_eq_zero_of_not_rough hro]
    split_ifs <;> ring

end ThreeSquares
