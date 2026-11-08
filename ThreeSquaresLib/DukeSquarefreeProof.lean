/-
Copyright (c) 2026 Juan Pablo Traverso Gianini.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import ThreeSquaresLib.IsoDegreewiseWeyl
public import ThreeSquaresLib.B3_RepresentationLower

/-! # H1: squarefree three squares in every fixed cap

All analytic inputs are supplied by imported proofs. The constant in the
representation lower bound is ineffective, as in Siegel's theorem.
-/

@[expose] public section
namespace ThreeSquares

theorem dukeSquarefree : DukeSquarefree := by
  apply Duke.dukeSquarefree_of_degreewise Duke.weyl_bound_through
  intro η hη
  obtain ⟨c,hc,h⟩ := B3.r3_lower η hη
  exact ⟨c,hc,0,fun t _ hs h8 => h t hs h8⟩

end ThreeSquares
