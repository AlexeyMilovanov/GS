import Tilings.Control.Composition

/-!
# Regression targets for the composition chapter (statements only)

Two of the regression targets required by the blueprint
(`main.tex`, "Implementation boundaries and acceptance criteria"):

1. the three-block counterexample to the alignment lemma
   (`lem:comp/alignment`) without the mode-uniformity hypothesis;
2. the old mixed exterior-flag example (`C_0`/`C_q`, two half-plane
   exhaustions): with the article's boundary clause (boundary fourth cell =
   parent *type*, instead of the full parent header) proper legal tilings
   need not have an exact legal composition.

Both are stated schematically, as negations of the universally quantified
statement over all macrocertificates; the concrete constructions are not
given here (`sorry`).

Notes.
* The blueprint's three-block example uses ranks `1,2,3` against an opposing
  macroside with five children.  A certificate instance must satisfy (G3)
  (at least five outer children per declared side), so an instance proving
  `alignment_fails_without_mode_uniformity` must scale the example (e.g.
  `L` children against `L + 2`).
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

/-- The alignment lemma *without* the mode-uniformity hypothesis is false:
there is a hereditary certificate, a plane partition into macroblocks and a
macroside all of whose children are completely matched with equal positive
ranks, but which has no complete opposing macroside with the same
subdivision (the opposing macroside has more children, the extra ones facing
trivial sides of a third block). -/
theorem alignment_fails_without_mode_uniformity :
    ¬ ∀ (P : Protoset) (c : MacroCertificate P), c.Hereditary →
      ∀ (T : PlaneTiling (typedDecoration c)) (part : MacroPartition c T)
        (j : part.ι) (d : Fin (c.Q.disk (part.block j).α).n),
        RankMatched c part j d → OpposingMacroside c part j d := by
  sorry

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
