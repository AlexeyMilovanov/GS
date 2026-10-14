import Tilings.Control.Composition

/-!
# Regression targets for the composition chapter (statements only)

One regression target required by the blueprint
(`main.tex`, "Implementation boundaries and acceptance criteria"):

1. the old mixed exterior-flag example (`C_0`/`C_q`, two half-plane
   exhaustions): with the article's boundary clause (boundary fourth cell =
   parent *type*, instead of the full parent header) proper legal tilings
   need not have an exact legal composition.

It is stated schematically, as the negation of the universally quantified
statement over all macrocertificates; the concrete construction is not
given here (`sorry`).

Removed (2026-10-14): the former second regression target
`alignment_fails_without_mode_uniformity` (the three-block counterexample to
the alignment lemma without the mode-uniformity hypothesis).  After the
repair of `headerLegal` (13 October 2026) every macroblock of a proper
legal tiling has a common boundary header, so mode uniformity follows from
legality and the negated statement became TRUE; the regression theorem was
therefore false.  Its text and the explanation are kept in
`docs/removed-alignment-regression.md`; it was never used by any theorem.

Notes.
* The `C_0`/`C_q` example lives on the regular square subdivision
  (`q = 2`, `S = 3^m`), which has hereditary listed sides; the statement
  therefore keeps the hereditary hypothesis.
-/

open Set Pointwise

noncomputable section

namespace Tilings

namespace Planned

namespace Regression

open Geometry

/-- The article's child relation: identical to the repaired one except that
a boundary fourth cell carries only the parent type. -/
def oldChildOf {P : Protoset} (c : MacroCertificate P) (A B : DecTile c) : Prop :=
  IsChildOfWith c (fun A => typeU c A.typ) A B

/-- Legality for the article's child relation (boundary fourth cells are
origins, as in the repaired definition). -/
def oldLegal {P : Protoset} (c : MacroCertificate P) (A : DecTile c) : Prop :=
  IsLegalWith c (oldChildOf c) A

/-- The old mixed exterior-flag example (`C_0`/`C_q`): with the article's
boundary clause, the exact coloured composition theorem fails — some proper
plane tiling of old-legal tiles has no proper exact old composition with
old-legal tiles.  (The repaired version is `compose_legal_exists`.) -/
theorem old_typeflag_composition_fails :
    ¬ ∀ (P : Protoset) (c : MacroCertificate P), c.Hereditary →
      ∀ T : PlaneTiling (typedDecoration c), IsProper c T →
        (∀ X ∈ T.tiles, oldLegal c (tileDec X)) →
        ∃ T' : PlaneTiling (typedDecoration c), IsProper c T' ∧
          (∀ X ∈ T'.tiles, oldLegal c (tileDec X)) ∧
          IsExactCompositionWith c (oldChildOf c) T' T := by
  sorry

end Regression

end Planned

end Tilings

end
