/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.B3_Hyp
public import LeanLab.PNTPort.DirichletZF.Siegel

/-! # Discharging the registered analytic contracts of B3

The imported proofs are the exact source closure of goldbach-lean commit
6d7ae7b40fb5550e836456fd2ff4d8587157aee7, not new axioms.
-/

@[expose] public section
namespace ThreeSquares.B3

theorem siegel_verified : SiegelHyp := LeanLab.PNTPort.DirichletZF.siegel

theorem lOneIntegral_verified : LOneIntegralHyp := by
  intro N _ χ hχ s hs
  exact LeanLab.PNTPort.DirichletZF.LFunction_eq_integral hχ hs

end ThreeSquares.B3
