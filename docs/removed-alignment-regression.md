# Removed regression target: `alignment_fails_without_mode_uniformity`

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
