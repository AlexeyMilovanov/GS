import Enforce.Tiling

/-!
# Hereditary source geometry and first providers

Cells retain their prototype names. Their carriers are placed by the full affine
prototype frame, so the same interface covers native tiles and positive-height nodes.
Ancestors are indexed by the number of parent steps, starting with the node itself.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

/-- P1, V4 1.1: a listed cell name in a prototype complex. -/
abbrev CellName (S : SubstSystem d) (A : S.ι) := {e // e ∈ (S.cx A).cells}

/-- P3, V4 1.3: a listed facet name in a prototype complex. -/
abbrev FacetName (S : SubstSystem d) (A : S.ι) := {e // e ∈ (S.cx A).facets}

/-- P1, V4 1.1: place a prototype cell at the actual height of a framed node. -/
def FramedNode.cell (N : FramedNode S) (n : ℕ) (e : Cell d) : Set (E d) :=
  N.prototypeFrame n '' e.carrier

/-- P5, V4 1.5: a listed vertex of a placed node, including flat listed vertices. -/
def FramedNode.Lists (N : FramedNode S) (n : ℕ) (p : E d) : Prop :=
  ∃ e ∈ (S.cx N.ty).vertices, p ∈ N.cell n e

/-- P1, V4 1.1: descendant relation retaining the exact recursive frame. -/
def FramedNode.IsDescendant (C : FramedNode S) (h : ℕ)
    (P : FramedNode S) (n : ℕ) : Prop :=
  ∃ r : ℕ, n = h + r ∧ ∃ w : S.RoleWord P.ty r,
    C = (S.descendantNode P.ty h r w).move P.frame

/-- P1, V4 1.1: hereditary trace, for descendants of arbitrary depth. -/
theorem hereditary_trace (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (F g : Cell d)
    (hF : F ∈ (S.cx P.ty).cells) (hg : g ∈ (S.cx C.ty).cells)
    (hmeet : (relint (C.cell h g) ∩ P.cell n F).Nonempty) :
    C.cell h g ⊆ P.cell n F := by
  sorry

/-- P1, V4 1.1: the entire trace on a descendant is a union of its listed cells. -/
theorem hereditary_trace_union (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (F : Cell d) (hF : F ∈ (S.cx P.ty).cells) :
    P.cell n F ∩ C.carrier h =
      ⋃ e ∈ (S.cx C.ty).cells, ⋃ (_ : C.cell h e ⊆ P.cell n F), C.cell h e := by
  sorry

/-- P2, V4 1.2: existence and uniqueness of the ancestral stratum.
Nonempty relative interior of the listed cell supplies an actual point. -/
theorem ancestralStratum_exists_unique (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (g : CellName S C.ty)
    (hg : C.cell h g.val ⊆ frontier (P.carrier n)) :
    ∃! F : CellName S P.ty,
      relint (C.cell h g.val) ⊆ relint (P.cell n F.val) := by
  sorry

/-- P2, V4 1.2: the unique ancestral stratum, chosen from the existence lemma. -/
def ancestralStratum (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (g : CellName S C.ty)
    (hg : C.cell h g.val ⊆ frontier (P.carrier n)) : CellName S P.ty :=
  Classical.choose (ancestralStratum_exists_unique P C n h hC g hg)

/-- P2, V4 1.2: relative-interior characterization and dimension monotonicity. -/
theorem ancestralStratum_spec (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (g : CellName S C.ty)
    (hg : C.cell h g.val ⊆ frontier (P.carrier n)) :
    relint (C.cell h g.val) ⊆
        relint (P.cell n (ancestralStratum P C n h hC g hg).val) ∧
      g.val.dim ≤ (ancestralStratum P C n h hC g hg).val.dim := by
  sorry

/-- P2, V4 1.2: ancestral strata preserve inclusion of incident cells. -/
theorem ancestralStratum_mono (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (g g' : CellName S C.ty)
    (hg : C.cell h g.val ⊆ frontier (P.carrier n))
    (hg' : C.cell h g'.val ⊆ frontier (P.carrier n))
    (hsub : C.cell h g'.val ⊆ C.cell h g.val) :
    P.cell n (ancestralStratum P C n h hC g' hg').val ⊆
      P.cell n (ancestralStratum P C n h hC g hg).val := by
  sorry

/-- P3, V4 1.3: exactly one ancestral facet contains a boundary facet;
otherwise its entire relative interior is interior to the ancestor. -/
theorem facet_dichotomy (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (f : FacetName S C.ty) :
    (∃! F : FacetName S P.ty, C.cell h f.val ⊆ P.cell n F.val) ∨
      relint (C.cell h f.val) ⊆ interior (P.carrier n) := by
  sorry

/-- P4, V4 1.4(a): sibling minimal cells agree as placed carriers.
The relative-interior hypotheses name the minimal cells without boundary casts. -/
theorem sibling_minimalCell_eq (P : FramedNode S) (n : ℕ)
    (i j : S.I P.ty) (hij : i ≠ j) (p : E d)
    (e : CellName S (P.child n i).ty) (f : CellName S (P.child n j).ty)
    (he : p ∈ relint ((P.child n i).cell n e.val))
    (hf : p ∈ relint ((P.child n j).cell n f.val)) :
    (P.child n i).cell n e.val = (P.child n j).cell n f.val := by
  sorry

/-- P4, V4 1.4(a): sibling intersections are unions of common listed cells. -/
theorem sibling_intersection_cells (P : FramedNode S) (n : ℕ)
    (i j : S.I P.ty) (hij : i ≠ j) :
    (P.child n i).carrier n ∩ (P.child n j).carrier n =
      ⋃ e : CellName S (P.child n i).ty,
        ⋃ f : CellName S (P.child n j).ty,
          ⋃ (_ : (P.child n i).cell n e.val = (P.child n j).cell n f.val),
            (P.child n i).cell n e.val := by
  sorry

/-- P4, V4 1.4(b): positive facet measure, expressed by Hausdorff measure. -/
def PositiveFacetOverlap (K L : Set (E d)) : Prop :=
  0 < MeasureTheory.Measure.hausdorffMeasure (d - 1 : ℝ) (K ∩ L)

/-- P4, V4 1.4(b): positive-measure sibling facet overlap forces whole equality,
and the children occupy opposite closed half-balls at every relative-interior point. -/
theorem sibling_facet_eq (P : FramedNode S) (n : ℕ)
    (i j : S.I P.ty) (hij : i ≠ j)
    (e : FacetName S (P.child n i).ty) (f : FacetName S (P.child n j).ty)
    (hover : PositiveFacetOverlap ((P.child n i).cell n e.val)
      ((P.child n j).cell n f.val)) :
    (P.child n i).cell n e.val = (P.child n j).cell n f.val ∧
      ∀ p ∈ relint ((P.child n i).cell n e.val), ∃ r : ℝ, 0 < r ∧
        ∃ v : E d, ‖v‖ = 1 ∧
          (P.child n i).carrier n ∩ ball p r =
            {x | 0 ≤ inner ℝ v (x - p)} ∩ ball p r ∧
          (P.child n j).carrier n ∩ ball p r =
            {x | inner ℝ v (x - p) ≤ 0} ∩ ball p r := by
  sorry

/-- P4, V4 1.4(c): an internal facet has one other owning child;
all remaining children have zero facet measure on it. Existence comes from coverage. -/
theorem internal_facet_pairing (P : FramedNode S) (n : ℕ) (i : S.I P.ty)
    (f : FacetName S (P.child n i).ty)
    (hint : (relint ((P.child n i).cell n f.val) ∩
      interior (P.carrier (n + 1))).Nonempty) :
    relint ((P.child n i).cell n f.val) ⊆ interior (P.carrier (n + 1)) ∧
      ∃! j : S.I P.ty, j ≠ i ∧
        ∃ g : FacetName S (P.child n j).ty,
          (P.child n j).cell n g.val = (P.child n i).cell n f.val ∧
          ∀ l : S.I P.ty, l ≠ i → l ≠ j →
            MeasureTheory.Measure.hausdorffMeasure (d - 1 : ℝ)
              ((P.child n l).carrier n ∩ (P.child n i).cell n f.val) = 0 := by
  sorry

/-- P5, V4 1.5(a): listed vertices pass to every containing child. -/
theorem vertex_inherited (P : FramedNode S) (n : ℕ) (p : E d)
    (hp : P.Lists (n + 1) p) (i : S.I P.ty)
    (hi : p ∈ (P.child n i).carrier n) : (P.child n i).Lists n p := by
  sorry

/-- P5, V4 1.5(b): listedness passes to all containing descendants.
This node form also applies separately to every member of a compatible patch. -/
theorem commonListed_inherited (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (p : E d) (hp : P.Lists n p)
    (hpC : p ∈ C.carrier h) : C.Lists h p := by
  sorry

/-- P5, V4 1.5(c): a listed vertex on an internal facet is common-listed
in the entire immediate subdivision, including children meeting only at that vertex. -/
theorem primitive_vertex_listed (P : FramedNode S) (n : ℕ) (i : S.I P.ty)
    (f : FacetName S (P.child n i).ty)
    (hint : relint ((P.child n i).cell n f.val) ⊆ interior (P.carrier (n + 1)))
    (p : E d) (hp : (P.child n i).Lists n p)
    (hpf : p ∈ (P.child n i).cell n f.val)
    (j : S.I P.ty) (hpj : p ∈ (P.child n j).carrier n) :
    (P.child n j).Lists n p := by
  sorry

/-- P6, V4 1.6: finite primitive incidence, with both cell names and both roles.
The roles are ordered to record the serving side; exchanging them gives the other side. -/
structure PrimitiveIncidence (S : SubstSystem d) where
  /-- P6, V4 1.6: birth-parent prototype. -/
  ty : S.ι
  /-- P6, V4 1.6: serving child role. -/
  left : S.I ty
  /-- P6, V4 1.6: opposite child role. -/
  right : S.I ty
  /-- P6, V4 1.6: paired children are distinct. -/
  distinct : left ≠ right
  /-- P6, V4 1.6: provider name in the serving child's complex. -/
  leftFacet : FacetName S (S.child ty left).ty
  /-- P6, V4 1.6: provider name in the opposite child's complex. -/
  rightFacet : FacetName S (S.child ty right).ty
  /-- P6, V4 1.6: the two names have identical placed carriers in `σ A`. -/
  paired : placedSet (S.child ty left).frame leftFacet.val.carrier =
    placedSet (S.child ty right).frame rightFacet.val.carrier
  /-- P6, V4 1.6: the common facet is first-generation internal. -/
  internal : relint (placedSet (S.child ty left).frame leftFacet.val.carrier) ⊆
    interior (S.supertile 1 ty)

/-- P6, V4 1.6: the catalogue of primitive incidences is finite. -/
theorem primitiveIncidence_finite (S : SubstSystem d) : Finite (PrimitiveIncidence S) := by
  sorry

namespace CoherentHierarchy

variable {T : Tiling S} (H : CoherentHierarchy S T)

/-- P6, V4 1.6: the ancestor after `r` parent steps, including step zero. -/
def ancestor (q : H.Node) (r : ℕ) : H.Node := (H.parentNode^[r]) q

/-- P6, V4 1.6: the height of an ancestor is the original height plus its offset. -/
theorem ancestor_height (q : H.Node) (r : ℕ) : (H.ancestor q r).1 = q.1 + r := by
  sorry

/-- P6, V4 1.6: actual ancestors satisfy the recursive framed descendant relation. -/
theorem ancestor_descendant (q : H.Node) (r : ℕ) :
    q.2.val.IsDescendant q.1 (H.ancestor q r).2.val (H.ancestor q r).1 := by
  sorry

/-- P6, V4 1.6: offsets for which the original facet remains on the boundary. -/
def boundaryOffsets (q : H.Node) (f : FacetName S q.2.val.ty) : Set ℕ :=
  {r | q.2.val.cell q.1 f.val ⊆
    frontier ((H.ancestor q r).2.val.carrier (H.ancestor q r).1)}

/-- P6, V4 1.6: persistent boundary facets have no finite provider. -/
def IsFault (q : H.Node) (f : FacetName S q.2.val.ty) : Prop :=
  ∀ r : ℕ, r ∈ H.boundaryOffsets q f

/-- P6, V4 1.6: boundary heights form an initial segment, or persist forever.
A finite segment includes offset zero and ends immediately before the birth. -/
theorem boundaryOffsets_initial (q : H.Node) (f : FacetName S q.2.val.ty) :
    (∃ b : ℕ, 1 ≤ b ∧ H.boundaryOffsets q f = {r | r < b}) ∨ H.IsFault q f := by
  sorry

/-- P6, V4 1.6: possible serving-child offsets and named provider facets. -/
abbrev ProviderCandidate (q : H.Node) :=
  Σ r : ℕ, FacetName S (H.ancestor q r).2.val.ty

/-- P6, V4 1.6: a candidate is the first provider precisely when it is the
unique serving facet at the last boundary offset and is internal to the next ancestor. -/
def IsProvider (q : H.Node) (f : FacetName S q.2.val.ty)
    (v : H.ProviderCandidate q) : Prop :=
  H.boundaryOffsets q f = {r | r < v.1 + 1} ∧
    q.2.val.cell q.1 f.val ⊆
      (H.ancestor q v.1).2.val.cell (H.ancestor q v.1).1 v.2.val ∧
    relint ((H.ancestor q v.1).2.val.cell (H.ancestor q v.1).1 v.2.val) ⊆
      interior ((H.ancestor q (v.1 + 1)).2.val.carrier (H.ancestor q (v.1 + 1)).1)

/-- P6/P7, V4 1.6, 1.7(a): a nonfault facet has exactly one first provider.
Nonfaultness gives a finite endpoint of the initial segment. -/
theorem provider_exists_unique (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : ∃! v : H.ProviderCandidate q, H.IsProvider q f v := by
  sorry

/-- P6, V4 1.6: first provider, with the serving ancestor and its facet name. -/
def firstProvider (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : H.ProviderCandidate q :=
  Classical.choose (H.provider_exists_unique q f hf)

/-- P6, V4 1.6: specification of the chosen finite provider. -/
theorem firstProvider_spec (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : H.IsProvider q f (H.firstProvider q f hf) :=
  (Classical.choose_spec (H.provider_exists_unique q f hf)).1

/-- P6, V4 1.6: the serving child at the last boundary height. -/
def servingChild (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : H.Node := H.ancestor q (H.firstProvider q f hf).1

/-- P6, V4 1.6: birth parent, one parent step above the serving child. -/
def birthParent (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : H.Node := H.parentNode (H.servingChild q f hf)

/-- P6, V4 1.6: absolute birth height. -/
def birthHeight (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : ℕ := (H.birthParent q f hf).1

/-- P6, V4 1.6: provider age relative to the original node. -/
def age (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : ℕ := H.birthHeight q f hf - q.1

/-- P6, V4 1.6: the geometric carrier of the first provider. -/
def providerCarrier (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : Set (E d) :=
  (H.servingChild q f hf).2.val.cell (H.servingChild q f hf).1
    (H.firstProvider q f hf).2.val

/-- P6, V4 1.6: exact incidence realization, including the serving role and
its named facet. This fixes the side rather than allowing the opposite orientation. -/
def RealizesProviderIncidence (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (ι : PrimitiveIncidence S) : Prop :=
  ι.ty = (H.birthParent q f hf).2.val.ty ∧
    (⟨ι.ty, ι.left⟩ : S.Role) = H.nodeRole (H.servingChild q f hf) ∧
    ι.leftFacet.val = (H.firstProvider q f hf).2.val ∧
    H.providerCarrier q f hf =
      (H.birthParent q f hf).2.val.prototypeFrame (H.birthHeight q f hf) ''
        (S.σ.symm '' placedSet (S.child ι.ty ι.left).frame ι.leftFacet.val.carrier)

/-- P6, V4 1.6: the actual paired children and their two cell names determine
one primitive incidence. Existence is supplied by whole-facet sibling pairing. -/
theorem provider_incidence_exists (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) :
    ∃! ι : PrimitiveIncidence S, H.RealizesProviderIncidence q f hf ι := by
  sorry

/-- P6, V4 1.6: the finite primitive incidence with its distinguished serving side. -/
def providerIncidence (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) : PrimitiveIncidence S :=
  Classical.choose (H.provider_incidence_exists q f hf)

/-- P6, V4 1.6: specification of the chosen incidence, with both paired roles. -/
theorem providerIncidence_spec (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) :
    H.RealizesProviderIncidence q f hf (H.providerIncidence q f hf) :=
  (Classical.choose_spec (H.provider_incidence_exists q f hf)).1

/-- P7, V4 1.7(a): uniqueness of the provider as a serving offset and facet name. -/
theorem provider_unique (q : H.Node) (f : FacetName S q.2.val.ty)
    (v w : H.ProviderCandidate q) (hv : H.IsProvider q f v) (hw : H.IsProvider q f w) :
    v = w := by
  sorry

/-- P7, V4 1.7(a): restriction to any contained descendant facet preserves the
provider carrier and the exact birth parent; existence of the restricted provider
is part of the conclusion. -/
theorem provider_inherited (q c : H.Node) (r : ℕ) (hc : H.ancestor c r = q)
    (f : FacetName S q.2.val.ty) (g : FacetName S c.2.val.ty)
    (hf : ¬ H.IsFault q f) (hsub : c.2.val.cell c.1 g.val ⊆ q.2.val.cell q.1 f.val) :
    ∃ hg : ¬ H.IsFault c g,
      H.providerCarrier c g hg = H.providerCarrier q f hf ∧
        H.birthParent c g hg = H.birthParent q f hf := by
  sorry

/-- P7, V4 1.7(b): existence of the provider stratum for any cell in the facet. -/
theorem stratum_exists_unique (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (s : CellName S q.2.val.ty)
    (hs : q.2.val.cell q.1 s.val ⊆ q.2.val.cell q.1 f.val) :
    ∃! t : CellName S (H.servingChild q f hf).2.val.ty,
      relint (q.2.val.cell q.1 s.val) ⊆
        relint ((H.servingChild q f hf).2.val.cell (H.servingChild q f hf).1 t.val) := by
  sorry

/-- P7, V4 1.7(b): the provider stratum map `τ_f`, defined by unique existence. -/
def stratumMap (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (s : CellName S q.2.val.ty)
    (hs : q.2.val.cell q.1 s.val ⊆ q.2.val.cell q.1 f.val) :
    CellName S (H.servingChild q f hf).2.val.ty :=
  Classical.choose (H.stratum_exists_unique q f hf s hs)

/-- P7, V4 1.7(b): characterization, dimension bound, and containment in the provider. -/
theorem stratumMap_spec (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (s : CellName S q.2.val.ty)
    (hs : q.2.val.cell q.1 s.val ⊆ q.2.val.cell q.1 f.val) :
    relint (q.2.val.cell q.1 s.val) ⊆
        relint ((H.servingChild q f hf).2.val.cell (H.servingChild q f hf).1
          (H.stratumMap q f hf s hs).val) ∧
      s.val.dim ≤ (H.stratumMap q f hf s hs).val.dim ∧
      (H.servingChild q f hf).2.val.cell (H.servingChild q f hf).1
        (H.stratumMap q f hf s hs).val ⊆ H.providerCarrier q f hf := by
  sorry

/-- P7, V4 1.7(b): incidence preservation of the provider stratum map. -/
theorem stratumMap_mono (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (s t : CellName S q.2.val.ty)
    (hs : q.2.val.cell q.1 s.val ⊆ q.2.val.cell q.1 f.val)
    (ht : q.2.val.cell q.1 t.val ⊆ q.2.val.cell q.1 f.val)
    (hst : s.val.carrier ⊆ t.val.carrier) :
    (H.stratumMap q f hf s hs).val.carrier ⊆
      (H.stratumMap q f hf t ht).val.carrier := by
  sorry

/-- P7, V4 1.7(b): the facet itself maps to the whole first provider. -/
theorem stratumMap_facet (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (s : CellName S q.2.val.ty) (hs : s.val = f.val) :
    ∃ hsub : q.2.val.cell q.1 s.val ⊆ q.2.val.cell q.1 f.val,
      (H.stratumMap q f hf s hsub).val = (H.firstProvider q f hf).2.val := by
  sorry

/-- P7, V4 1.7(c): an internal child facet is its own provider, of age one. -/
theorem restriction_det_internal (c : H.Node) (f : FacetName S c.2.val.ty)
    (hint : relint (c.2.val.cell c.1 f.val) ⊆
      interior ((H.parentNode c).2.val.carrier (H.parentNode c).1)) :
    ∃ hf : ¬ H.IsFault c f,
      H.providerCarrier c f hf = c.2.val.cell c.1 f.val ∧
        H.birthParent c f hf = H.parentNode c ∧ H.age c f hf = 1 := by
  sorry

/-- P7, V4 1.7(c): inherited finite facets retain provider and birth, gain one
unit of age, and their strata compose with the immediate ancestral strata. -/
theorem restriction_det_inherited (c : H.Node)
    (f : FacetName S (H.parentNode c).2.val.ty) (g : FacetName S c.2.val.ty)
    (hf : ¬ H.IsFault (H.parentNode c) f)
    (hsub : c.2.val.cell c.1 g.val ⊆
      (H.parentNode c).2.val.cell (H.parentNode c).1 f.val) :
    ∃ hg : ¬ H.IsFault c g,
      H.providerCarrier c g hg = H.providerCarrier (H.parentNode c) f hf ∧
      H.birthParent c g hg = H.birthParent (H.parentNode c) f hf ∧
      H.age c g hg = H.age (H.parentNode c) f hf + 1 ∧
      ∀ (s : CellName S c.2.val.ty)
        (hs : c.2.val.cell c.1 s.val ⊆ c.2.val.cell c.1 g.val),
        ∃ (t : CellName S (H.parentNode c).2.val.ty)
          (ht : (H.parentNode c).2.val.cell (H.parentNode c).1 t.val ⊆
            (H.parentNode c).2.val.cell (H.parentNode c).1 f.val),
          relint (c.2.val.cell c.1 s.val) ⊆
            relint ((H.parentNode c).2.val.cell (H.parentNode c).1 t.val) ∧
          (H.servingChild c g hg).2.val.cell (H.servingChild c g hg).1
            (H.stratumMap c g hg s hs).val =
          (H.servingChild (H.parentNode c) f hf).2.val.cell
            (H.servingChild (H.parentNode c) f hf).1
            (H.stratumMap (H.parentNode c) f hf t ht).val := by
  sorry

/-- P7, V4 1.7(c): faults restrict to faults. -/
theorem restriction_det_fault (c : H.Node)
    (f : FacetName S (H.parentNode c).2.val.ty) (g : FacetName S c.2.val.ty)
    (hf : H.IsFault (H.parentNode c) f)
    (hsub : c.2.val.cell c.1 g.val ⊆
      (H.parentNode c).2.val.cell (H.parentNode c).1 f.val) : H.IsFault c g := by
  sorry

end CoherentHierarchy

/-- P7/P17, V4 1.7(d), 1.22: a positive-dimensional full flag ending at a facet.
Vertices are omitted, as in 1.7(d); the edge is indexed by `1`. -/
structure FacetFlag (S : SubstSystem d) (A : S.ι) where
  /-- P7, V4 1.7(d): cell at each positive boundary dimension. -/
  cell : {j : ℕ // 1 ≤ j ∧ j < d} → CellName S A
  /-- P7, V4 1.7(d): exact dimensions. -/
  dimension : ∀ j, (cell j).val.dim = j.val
  /-- P7, V4 1.7(d): nested carriers. -/
  nested : ∀ i j, i.val ≤ j.val → (cell i).val.carrier ⊆ (cell j).val.carrier

namespace CoherentHierarchy

variable {T : Tiling S} (H : CoherentHierarchy S T)

/-- P7, V4 1.7(d): a full flag is active when every stratum is the prescribed
provider cell; carrier equalities avoid dependent casts between serving nodes. -/
def ActiveFlag (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (s : FacetFlag S q.2.val.ty)
    (F : FacetFlag S (H.servingChild q f hf).2.val.ty) : Prop :=
  ∀ j, ∃ hs : q.2.val.cell q.1 (s.cell j).val ⊆ q.2.val.cell q.1 f.val,
    (H.stratumMap q f hf (s.cell j) hs).val = (F.cell j).val

/-- P7, V4 1.7(d): active descendant flags lift through every intermediate
ancestor with exact dimensions and nestedness, and the provider strata stay equal. -/
theorem active_flags_hereditary (q c : H.Node) (r : ℕ) (hc : H.ancestor c r = q)
    (f : FacetName S q.2.val.ty) (g : FacetName S c.2.val.ty)
    (hf : ¬ H.IsFault q f) (hg : ¬ H.IsFault c g)
    (hsub : c.2.val.cell c.1 g.val ⊆ q.2.val.cell q.1 f.val)
    (s : FacetFlag S c.2.val.ty)
    (F : FacetFlag S (H.servingChild c g hg).2.val.ty)
    (ha : H.ActiveFlag c g hg s F) :
    ∃ t : FacetFlag S q.2.val.ty, ∀ j,
      relint (c.2.val.cell c.1 (s.cell j).val) ⊆
        relint (q.2.val.cell q.1 (t.cell j).val) ∧
      ∃ ht : q.2.val.cell q.1 (t.cell j).val ⊆ q.2.val.cell q.1 f.val,
        (H.servingChild q f hf).2.val.cell (H.servingChild q f hf).1
          (H.stratumMap q f hf (t.cell j) ht).val =
        (H.servingChild c g hg).2.val.cell (H.servingChild c g hg).1 (F.cell j).val := by
  sorry

end CoherentHierarchy

/-- P8, V4 1.8: a child facet occurrence inside a specified parent facet. -/
abbrev BoundaryFacet (P : FramedNode S) (n : ℕ) (g : FacetName S P.ty) :=
  {q : Σ i : S.I P.ty, FacetName S (P.child n i).ty //
    (P.child n q.1).cell n q.2.val ⊆ P.cell (n + 1) g.val}

/-- P8, V4 1.8: adjacency through a common listed codimension-two cell. -/
def boundaryFacetAdjacent (P : FramedNode S) (n : ℕ) (g : FacetName S P.ty)
    (a b : BoundaryFacet P n g) : Prop :=
  a ≠ b ∧ ∃ (e : CellName S (P.child n a.val.1).ty)
    (f : CellName S (P.child n b.val.1).ty),
    e.val.dim = d - 2 ∧ f.val.dim = d - 2 ∧
    (P.child n a.val.1).cell n e.val = (P.child n b.val.1).cell n f.val ∧
    (P.child n a.val.1).cell n e.val ⊆ (P.child n a.val.1).cell n a.val.2.val ∧
    (P.child n b.val.1).cell n f.val ⊆ (P.child n b.val.1).cell n b.val.2.val

/-- P8, V4 1.8: the boundary tiling and connected adjacency graph.
The nonempty facet guarantees at least one graph vertex. -/
theorem boundary_facet_adjacency (P : FramedNode S) (n : ℕ)
    (g : FacetName S P.ty) :
    (⋃ a : BoundaryFacet P n g, (P.child n a.val.1).cell n a.val.2.val) =
        P.cell (n + 1) g.val ∧
      Pairwise (fun a b : BoundaryFacet P n g => Disjoint
        (relint ((P.child n a.val.1).cell n a.val.2.val))
        (relint ((P.child n b.val.1).cell n b.val.2.val))) ∧
      Nonempty (BoundaryFacet P n g) ∧
      ∀ a b : BoundaryFacet P n g,
        Relation.ReflTransGen (boundaryFacetAdjacent P n g) a b := by
  sorry

/-- P8, V4 1.8 (moreover): distinct-child adjacency supplies a primitive facet
containing the common cell, with all of that cell's vertices common-listed. -/
theorem adjacency_primitive_seed (P : FramedNode S) (n : ℕ)
    (g : FacetName S P.ty) (a b : BoundaryFacet P n g)
    (hab : boundaryFacetAdjacent P n g a b) (hchild : a.val.1 ≠ b.val.1)
    (κ : CellName S (P.child n a.val.1).ty) (hκ : κ.val.dim = d - 2)
    (hκa : (P.child n a.val.1).cell n κ.val ⊆
      (P.child n a.val.1).cell n a.val.2.val)
    (hκb : (P.child n a.val.1).cell n κ.val ⊆
      (P.child n b.val.1).cell n b.val.2.val) :
    ∃ (i : S.I P.ty) (h : FacetName S (P.child n i).ty),
      relint ((P.child n i).cell n h.val) ⊆ interior (P.carrier (n + 1)) ∧
      (P.child n a.val.1).cell n κ.val ⊆ (P.child n i).cell n h.val ∧
      ∀ q : E d, (P.child n a.val.1).Lists n q →
        q ∈ (P.child n a.val.1).cell n κ.val →
        (P.child n i).Lists n q ∧ q ∈ (P.child n i).cell n h.val ∧
          ∀ j : S.I P.ty, q ∈ (P.child n j).carrier n → (P.child n j).Lists n q := by
  sorry

/-- P1/P2, V4 1.1--1.2: placed minimal cells exist uniquely at every boundary
point, including at positive height. This extends the stage-1 prototype API. -/
theorem placedMinimalCell_exists_unique (N : FramedNode S) (n : ℕ) (p : E d)
    (hp : p ∈ frontier (N.carrier n)) :
    ∃! e : CellName S N.ty, p ∈ relint (N.cell n e.val) := by
  sorry

/-- P1/P2, V4 1.1--1.2: the unique placed minimal cell, retaining its prototype name. -/
def placedMinimalCell (N : FramedNode S) (n : ℕ) (p : E d)
    (hp : p ∈ frontier (N.carrier n)) : CellName S N.ty :=
  Classical.choose (placedMinimalCell_exists_unique N n p hp)

/-- P1/P2, V4 1.1--1.2: the chosen cell contains the point in its relative interior. -/
theorem placedMinimalCell_spec (N : FramedNode S) (n : ℕ) (p : E d)
    (hp : p ∈ frontier (N.carrier n)) :
    p ∈ relint (N.cell n (placedMinimalCell N n p hp).val) :=
  (Classical.choose_spec (placedMinimalCell_exists_unique N n p hp)).1

/-- P2, V4 1.2: the ancestral stratum is the ancestor's minimal cell at every
relative-interior point of the descendant cell, rather than just one chosen anchor. -/
theorem ancestralStratum_eq_minimalCell (P C : FramedNode S) (n h : ℕ)
    (hC : C.IsDescendant h P n) (g : CellName S C.ty)
    (hg : C.cell h g.val ⊆ frontier (P.carrier n)) (p : E d)
    (hp : p ∈ relint (C.cell h g.val)) (hpP : p ∈ frontier (P.carrier n)) :
    ancestralStratum P C n h hC g hg = placedMinimalCell P n p hpP := by
  sorry

namespace CoherentHierarchy

variable {T : Tiling S} (H : CoherentHierarchy S T)

/-- P6, V4 1.6: ancestor iteration is additive, including zero parent steps. -/
theorem ancestor_add (q : H.Node) (r s : ℕ) :
    H.ancestor (H.ancestor q r) s = H.ancestor q (r + s) := by
  sorry

/-- P6, V4 1.6: boundary offsets are downward closed and contain zero. -/
theorem boundaryOffsets_downward (q : H.Node) (f : FacetName S q.2.val.ty) :
    0 ∈ H.boundaryOffsets q f ∧
      ∀ r s : ℕ, r ≤ s → s ∈ H.boundaryOffsets q f → r ∈ H.boundaryOffsets q f := by
  sorry

/-- P6, V4 1.6: all offsets from the finite birth on are interior alternatives. -/
theorem after_birth_interior (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (r : ℕ) (hr : (H.firstProvider q f hf).1 < r) :
    relint (q.2.val.cell q.1 f.val) ⊆
      interior ((H.ancestor q r).2.val.carrier (H.ancestor q r).1) := by
  sorry

/-- P6, V4 1.6: birth height and age are exactly the serving offset plus one. -/
theorem birthHeight_age_spec (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) :
    H.birthHeight q f hf = q.1 + (H.firstProvider q f hf).1 + 1 ∧
      H.age q f hf = (H.firstProvider q f hf).1 + 1 ∧ 1 ≤ H.age q f hf := by
  sorry

/-- P6, V4 1.6: a total provider record, using `none = NULL` on persistent faults. -/
def providerOrNull (q : H.Node) (f : FacetName S q.2.val.ty) :
    Option (H.ProviderCandidate q) := by
  classical
  exact if hf : H.IsFault q f then none else some (H.firstProvider q f hf)

/-- P6, V4 1.6: the NULL case is exactly persistent boundary, not a failed choice. -/
theorem providerOrNull_eq_none (q : H.Node) (f : FacetName S q.2.val.ty) :
    H.providerOrNull q f = none ↔ H.IsFault q f := by
  classical
  simp only [providerOrNull]
  split <;> simp_all

/-- P7, V4 1.7(b): at age one, the stratum map is the identity on every named cell. -/
theorem stratumMap_age_one (q : H.Node) (f : FacetName S q.2.val.ty)
    (hf : ¬ H.IsFault q f) (hage : H.age q f hf = 1)
    (s : CellName S q.2.val.ty)
    (hs : q.2.val.cell q.1 s.val ⊆ q.2.val.cell q.1 f.val) :
    (H.stratumMap q f hf s hs).val = s.val := by
  sorry

/-- P7, V4 1.7(d), final clause: an active edge lies in an edge of every
intermediate ancestor, with the same one-dimensional provider stratum. -/
theorem active_edge_hereditary (q c : H.Node) (r : ℕ) (hc : H.ancestor c r = q)
    (f : FacetName S q.2.val.ty) (g : FacetName S c.2.val.ty)
    (hf : ¬ H.IsFault q f) (hg : ¬ H.IsFault c g)
    (hsub : c.2.val.cell c.1 g.val ⊆ q.2.val.cell q.1 f.val)
    (s : CellName S c.2.val.ty) (hdim : s.val.dim = 1)
    (hs : c.2.val.cell c.1 s.val ⊆ c.2.val.cell c.1 g.val)
    (hactive : (H.stratumMap c g hg s hs).val.dim = 1) :
    ∃ (t : CellName S q.2.val.ty)
      (ht : q.2.val.cell q.1 t.val ⊆ q.2.val.cell q.1 f.val),
      t.val.dim = 1 ∧ relint (c.2.val.cell c.1 s.val) ⊆
        relint (q.2.val.cell q.1 t.val) ∧
      (H.servingChild q f hf).2.val.cell (H.servingChild q f hf).1
        (H.stratumMap q f hf t ht).val =
      (H.servingChild c g hg).2.val.cell (H.servingChild c g hg).1
        (H.stratumMap c g hg s hs).val := by
  sorry

end CoherentHierarchy

/-- P6/P7/T9, V4 1.6--1.7, 1.13(c): exact scale transfer preserves faults
on the entire surviving tails, including their arbitrarily high ancestors. -/
theorem ScaleTailEquiv.faults {U V : HonestSource S} {a b : ℕ} {J : Iso d}
    (e : ScaleTailEquiv U V a b J) (q : U.hierarchy.Tail a)
    (f : FacetName S q.val.2.val.ty)
    (g : FacetName S (e.toEquiv q).val.2.val.ty) (hfg : f.val = g.val) :
    U.hierarchy.IsFault q.val f ↔ V.hierarchy.IsFault (e.toEquiv q).val g := by
  sorry

/-- P6/P7/T9, V4 1.6--1.7, 1.13(c): finite providers keep their exact serving
offset, facet name, primitive incidence, and age under exact scale transfer. -/
theorem ScaleTailEquiv.providers {U V : HonestSource S} {a b : ℕ} {J : Iso d}
    (e : ScaleTailEquiv U V a b J) (q : U.hierarchy.Tail a)
    (f : FacetName S q.val.2.val.ty)
    (g : FacetName S (e.toEquiv q).val.2.val.ty) (hfg : f.val = g.val)
    (hf : ¬ U.hierarchy.IsFault q.val f)
    (hg : ¬ V.hierarchy.IsFault (e.toEquiv q).val g) :
    (U.hierarchy.firstProvider q.val f hf).1 =
        (V.hierarchy.firstProvider (e.toEquiv q).val g hg).1 ∧
      (U.hierarchy.firstProvider q.val f hf).2.val =
        (V.hierarchy.firstProvider (e.toEquiv q).val g hg).2.val ∧
      U.hierarchy.providerIncidence q.val f hf =
        V.hierarchy.providerIncidence (e.toEquiv q).val g hg ∧
      U.hierarchy.age q.val f hf = V.hierarchy.age (e.toEquiv q).val g hg ∧
      J '' ((U.expansion ^ ((b : ℤ) - (a : ℤ))) ''
        U.hierarchy.providerCarrier q.val f hf) =
          V.hierarchy.providerCarrier (e.toEquiv q).val g hg := by
  sorry

/-- P7/T9, V4 1.7(b), 1.13(c): provider strata retain literal prototype names
under the same full-tail transfer as the nodes and the provider incidences. -/
theorem ScaleTailEquiv.strata {U V : HonestSource S} {a b : ℕ} {J : Iso d}
    (e : ScaleTailEquiv U V a b J) (q : U.hierarchy.Tail a)
    (f : FacetName S q.val.2.val.ty)
    (g : FacetName S (e.toEquiv q).val.2.val.ty) (hfg : f.val = g.val)
    (hf : ¬ U.hierarchy.IsFault q.val f)
    (hg : ¬ V.hierarchy.IsFault (e.toEquiv q).val g)
    (s : CellName S q.val.2.val.ty) (t : CellName S (e.toEquiv q).val.2.val.ty)
    (hst : s.val = t.val)
    (hs : q.val.2.val.cell q.val.1 s.val ⊆ q.val.2.val.cell q.val.1 f.val)
    (ht : (e.toEquiv q).val.2.val.cell (e.toEquiv q).val.1 t.val ⊆
      (e.toEquiv q).val.2.val.cell (e.toEquiv q).val.1 g.val) :
    (U.hierarchy.stratumMap q.val f hf s hs).val =
      (V.hierarchy.stratumMap (e.toEquiv q).val g hg t ht).val := by
  sorry

end Enforce
