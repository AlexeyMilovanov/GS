# Matching rules for substitution and hierarchical tilings — a Lean 4 formalization

This repository contains a complete, `sorry`-free Lean 4 formalization of the
main theorems of

> Nikolay Vereshchagin, *Matching Rules for Substitution and Hierarchical
> Tilings for any Substitution with Finite Local Complexity*,
> arXiv:2606.25005v2 (August 2026),

in the corrected form of the accompanying blueprint (a pre-formalization
review found several intermediate claims of the paper to be false; the repaired
proofs are what is formalized here, see "Relation to the paper" below).

## Status (19 October 2026)

* Toolchain: `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0`.
* `lake build`: 0 errors, 0 warnings, 0 `sorry` (8042 jobs).
* Axioms of the principal theorems (`Tilings/Main.lean`):

```
'Tilings.sts_substitution_sofic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tilings.sts_side_to_side_hierarchy_sofic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tilings.sts_hierarchy_sofic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tilings.flc_substitution_sofic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Tilings.flc_hierarchy_sofic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

  No custom axioms, no `native_decide`, no `admit`.

## Building

```
lake exe cache get   # Mathlib cache
lake build
```

To re-check the axioms:

```
echo 'import Tilings.Main
#print axioms Tilings.sts_substitution_sofic
#print axioms Tilings.sts_side_to_side_hierarchy_sofic
#print axioms Tilings.sts_hierarchy_sofic
#print axioms Tilings.flc_substitution_sofic
#print axioms Tilings.flc_hierarchy_sofic' > ax.lean && lake env lean ax.lean
```

## Layout

| Module | Content (blueprint chapter) |
|---|---|
| `Tilings/Basic.lean` | geometric model: polygonal disks (dummy collinear vertices allowed), protosets, placed tiles, patches, plane tilings, substitutions, hierarchies, crowns, FLC / STS / hereditary sides, local rules, soficity (`models.tex`) |
| `Tilings/Hierarchy.lean` | local finiteness, compositions, powers, STS ⇒ FLC, allowed-crown hierarchies (`models.tex`) |
| `Tilings/Crowns.lean` | the corrected uniform crown-cover lemma (`crowns.tex`) |
| `Tilings/FLC/Clones.lean` | genuine-corner collared clones and the FLC reduction (`main.tex`) |
| `Tilings/HeaderKernel.lean` | finite boundary headers |
| `Tilings/Control/Certificate.lean` | the finite macrocertificate, properties (G1)–(G7) (`def:certificate`) |
| `Tilings/Control/Decoration.lean` | typed decorations, header substitution, origins, legality (`composition.tex`) |
| `Tilings/Control/Composition.lean` | the boundary-header repair of coloured composition (`composition.tex`) |
| `Tilings/Control/Strict.lean` | the strict (endpoint-schedule) variant of the control chapter |
| `Tilings/Geometry/Grouping/Foundation.lean` | mesh constants, anchored groupings, spokes, quantitative sectors, fingerprints, PL routing; polygonal Jordan / Schoenflies / annulus lemmas proved from scratch (`grouping.tex`) |
| `Tilings/Geometry/Grouping.lean` | existence of the macrocertificate (`lem:certificate-exists`) |
| `Tilings/Alignment.lean` | endpoint schedules, alignment, whole-side ports (`main.tex`) |
| `Tilings/StrictPresentation.lean` | strict presentation of an STS substitution (Theorem 1(b)) |
| `Tilings/LocalRules.lean` | collar conversion, glues, grouping lift, the hereditary-STS core theorems (`main.tex`) |
| `Tilings/Main.lean` | the five principal theorems: Theorem 1(a,b,c) and Theorem 2(a,b) |

`docs/removed-regressions.md` records two regression statements that were
removed during the formalization (one turned out to be false after a
strengthening of the legality notion; the other became obsolete).

## Relation to the paper

The formalization follows the blueprint in `blueprint/`
(`tilings-blueprint.tex`, revision of 12 October 2026, with the change log
`CHANGES-2026-10-12-review.txt`), not the paper verbatim.  The blueprint
repairs the defects found in v2 of the paper:

1. the coloured σ''-composition claim in the proof of Theorem 1(c)
   (replaced by finite boundary headers carrying the zero/nonzero flags);
2. the unconstrained assignment of tiles to grid squares in §3.1, which need
   not produce disk-like quasi-squares (replaced by anchored groupings and
   quantitative PL routing);
3. the sign of `sin μ` and the use of the minimal side length as a distance
   bound in the proof of Lemma 3(b) (replaced by the finite crown catalogue
   constants `r_*`, `δ_*` and a reflex-only angle bound);
4. the missing uniform width argument for the routing paths;
5. STS does not give hereditary listed sides when dummy collinear vertices
   are allowed (handled by endpoint schedules for Theorem 1(b) and by
   genuine-corner clones for Theorem 2).

Further statement-level corrections made while proving (all recorded in the
change log, items 8–33) concern the precise contracts of the certificate
and of the composition lemmas; none of them changed the principal theorems.

with mechanical acceptance gates, an independent judge and per-commit
audits), with hand decompositions and interface repairs where needed.
