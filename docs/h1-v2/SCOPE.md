# H1 submission: scope and verification

This revision is intended as version 2 of `PALOMAR-2026-11-07-000007`.
It retains the five existing declarations and their mathematical hypotheses,
and adds `DukeSchulzePillot.squarefree_three_squares_in_caps`.

The new declaration says that every fixed cap about every unit direction
contains a representation of every sufficiently large squarefree integer
congruent to 3 modulo 8 by three integer squares. It has no analytic assumption.
The cutoff depends on the direction and cap width and is ineffective.

The exact 192-module import closure of `ThreeSquares.dukeSquarefree` was copied
from the compiled and audited source at commit
`c2049f5db7e4f34e7fad6445e8db16fc9007c1cd`. `SOURCE_SELECTION.json` records
each original source hash. The proof sources are byte-identical to that audit.
The private working repository is not a build dependency: all needed proof
sources, licenses and pinned Mathlib dependencies are present here.

The cap proof first fixes its polynomial degree. It then takes a positive minimum
of finitely many harmonic-degree savings; no saving uniform in all degrees is
assumed. Odd-degree sums cancel antipodally. The representation lower bound
comes from a comparison of character-sum averages with reduced binary-form
counts, the elementary divisor bound and the verified Siegel theorem.
The imported Siegel and integral-representation proofs discharge both analytic
contracts, rather than leaving them as parameters of H1.

The older general-form `thm3_ii` and `spn_upper` remain conditional. H1 is a
sphere-specific cap consequence and does not prove the full general
Duke–Schulze-Pillot theorem, its sharp rate, or a spinor-genus lower bound.
The nonsquarefree cap theorem and H2 are not selected for this submission.

`UPSTREAM_AXIOMS.log` and `ASSEMBLY_BACKGROUND_ES.md` describe the larger
upstream development and are explicitly historical background. Only the H1
source cone listed in `SOURCE_SELECTION.json` is copied here; H2-specific files
mentioned by that background are not needed or submitted. The general
Gauss–Legendre registered repository and its `main` branch are unchanged.

Local interface/type and axiom checks are separate from the official Palomar
full preflight. A source hash or local build is not presented as a Palomar
verification. Actual submission is gated on the passing official report for
this exact commit and Comparator configuration. Registration is a separate
author decision after the service returns its review.
