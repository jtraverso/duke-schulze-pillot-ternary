/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import DukeH1.B3_Hyp
public import SiegelThmSolution

/-! # Discharging the registered analytic contracts of B3

The proofs come from the lake dependency `jtraverso/siegel-theorem` @ `dbe9353` (Siegel's theorem by
Goldfeld's argument, Mathlib only), not new axioms.
-/

@[expose] public section
namespace ThreeSquares.B3

theorem siegel_verified : SiegelHyp := SiegelThm.siegel

theorem lOneIntegral_verified : LOneIntegralHyp := SiegelThm.LFunction_eq_integral

end ThreeSquares.B3
