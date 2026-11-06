# Duke–Schulze-Pillot (Invent. Math. 99 (1990) 49–57) — working notes (2026-11-06)

Author's request: Theorem 3(ii) with Lemma 5(ii). Route chosen by the author: unconditional upper
bound + conditional deduction (option "1 + 2").

* Paper scan: Duke's page https://www.math.ucla.edu/~wdduke/preprints/lattice2.pdf (read as images).
* Theorem 3(ii): r(q,F,h,n) = r(spn_N q,h,n) μ(F) + O(n^{1/2−1/175+ε}) for n → ∞ restricted
  (n = t m², t squarefree, gcd(m, N₂^∞) ∈ S). Proof: Theorem 1 (Lemmas 1–3: Golubeva–Fomenko
  harmonics, Iwaniec + Shimura + Deligne) and the upper bound of Lemma 5(ii).
* Lemma 5(ii): n^{1/2−ε} ≪ r(spn_N q,h,n) ≪ n^{1/2+ε} on R*(spn q,h) (lower bound: Siegel's
  ineffective L(1,χ) bound + spinor mass formula [SP2] Korollar 2).
* Not in Mathlib / registry: Kloosterman/Kuznetsov, half-integral weight forms, Shimura, Deligne,
  Siegel mass formula, Siegel's theorem, spinor genus. Mathlib has: Jacobi theta, L(1,χ) ≠ 0.

## Plan
1. Divisor bound d(n) ≤ C_ε n^ε.
2. Square roots mod M: #{t : t² = c in ZMod M} ≤ K_c d(M) (CRT + prime powers via valuations).
3. Primitive solutions of X² + ΔY² = M ≤ 4 #roots(−Δ mod M) (Cauchy–Schwarz identity); all
   solutions ≤ Σ_{g² | M} primitive(M/g²) ≪ M^ε.
4. Positive definite integral binary forms: r_B(m) ≪ m^ε (complete the square).
5. Ternary: r_Q(N) ≪ N^{1/2+ε} (fix a coordinate, complete the square); shifted lattice h + ℤ³,
   q = ½ xᵀAx: r(q,h,n) ≪ n^{1/2+ε} (upper half of Lemma 5(ii) for one form).
6. Conditional Theorem 3(ii): from Theorem 1 and Theorem 3(i) of the paper as hypotheses
   (abstract main term R(n) = r(spn_N q,h,n), μ(F) ∈ [0,1], restricted set 𝒩), plus
   R(n) ≪ n^{1/2+ε}.
