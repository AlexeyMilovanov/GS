# Removed regression targets (module `Tilings/Control/Regression.lean`, deleted 2026-10-15)

Both regression statements of the blueprint's acceptance criteria were kept in Lean as sorried
theorems and are now removed from the code: the first because it became false after the
legality repair (below), the second by decision of the author on 2026-10-15, because it is a
counterexample about the article's original rule, not a part of the proof, and building the
concrete certificate instance is a separate project. The examples stay as prose in the blueprint.

## 2. `old_typeflag_composition_fails` (removed 2026-10-15, never used by any theorem)

Full text of the removed module (definitions `oldChildOf`, `oldLegal` and the statement):

```lean
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
```

## 1. `alignment_fails_without_mode_uniformity` (removed 2026-10-14)

_Removed from `Tilings/Control/Regression.lean` on 2026-10-14 (audit by codex gpt-6-astra and
gemini-4-argon; confirmed by hand). It was never used by any theorem of the project._

## The former statement

```lean
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
        IsProper c T → (∀ X ∈ T.tiles, headerLegal c (tileDec X)) →
        RankMatched c part j d → OpposingMacroside c part j d := by
  sorry
```

## Why it was removed

The theorem recorded, as a Lean target, the blueprint's three-block counterexample showing
that the alignment lemma (`lem:comp/alignment`) needs its mode-uniformity hypothesis.

On 13 October 2026 the legality predicate `headerLegal` was strengthened (every outer child
records the full parent header, not only the parent type) to repair
`composed_proper_step3_properties` / `IsReconstruction`.  Under the strengthened legality
every macroblock of a proper legal tiling has a common boundary header
(`macroblock_is_decomposition`, `boundary_header_constant`), hence the outer fourth cells
along each macroside are all `0` or all generated ranks: mode uniformity follows from
`IsProper` + `headerLegal` automatically.  Consequently the universally quantified statement
negated above is TRUE, and the regression theorem is FALSE as stated.

The three-block example of `composition.tex` remains a valid counterexample for the WEAKER
legality "every outer fourth cell is `0` or the generated rank of its side" (the condition
named in the parenthesis of the alignment lemma), i.e. for the article's original rule.  It is
kept as prose in the blueprint, not as a Lean statement, to avoid confusion.
