import Enforce.Observer

/-!
# Recognition, point uniqueness, and one all-source family

O7--O10, V4 4.7--4.10. Well-formedness uses the all-honest-source language;
`all_source_section` identifies it with the language of a single chosen family.
The chosen family is not asserted to be equivariant. Intrinsic recognition retains
full isometric frames, all descendants, and their actual parent and role maps.
No membership in the source species is imposed on a proper output.
-/

open Set

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d} {P : Params S}
variable {C : ClusterData S P}

/-- O7, V4 4.7: every positive-height parsed node is a WF copy in the full
source language, in its actual assigned frame. The proof obligation uses observer
saturation, congruent exact-scale transfer and common rendering above K; lower
nodes are restrictions of the matching height-K source pattern. -/
theorem node_is_WF (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : 1 ≤ n) (N : FramedNode S)
    (hN : N ∈ (parsedHierarchy Y hY).nodes n) :
    IsWFConfig (sourceLanguage C) Y n N := by
  sorry

/-- O8, V4 4.8: exact transport of the inner hierarchy of one framed node.
The ambient comparison is `M.frame ∘ N.frame⁻¹`. The biconditional retains every
inner node in both directions. Strictly inner nodes retain parents and globally
distinct roles, so neither a geometric support nor a set of unframed tiles suffices. -/
structure InnerStructure {T T' : Tiling S} (H : CoherentHierarchy S T)
    (H' : CoherentHierarchy S T') (n : ℕ) (N M : FramedNode S) : Prop where
  /-- O8, V4 4.8: every inner node corresponds with its full transported frame. -/
  nodes : ∀ m, m ≤ n → ∀ D : FramedNode S,
    (D ∈ H.nodes m ∧ D.IsDescendant m N n) ↔
      (D.move (N.frame.symm.trans M.frame) ∈ H'.nodes m ∧
        (D.move (N.frame.symm.trans M.frame)).IsDescendant m M n)
  /-- O8, V4 4.8: exact parent frame transport below the root. -/
  parents : ∀ (q : H.Node), q.1 < n → q.2.val.IsDescendant q.1 N n →
    ∀ hm : q.2.val.move (N.frame.symm.trans M.frame) ∈ H'.nodes q.1,
      (H'.parent q.1 ⟨q.2.val.move (N.frame.symm.trans M.frame), hm⟩).val =
        (H.parent q.1 q.2).val.move (N.frame.symm.trans M.frame)
  /-- O8, V4 4.8: exact child role transport below the root. -/
  roles : ∀ (q : H.Node), q.1 < n → q.2.val.IsDescendant q.1 N n →
    ∀ hm : q.2.val.move (N.frame.symm.trans M.frame) ∈ H'.nodes q.1,
      H'.nodeRole ⟨q.1, ⟨q.2.val.move (N.frame.symm.trans M.frame), hm⟩⟩ = H.nodeRole q

/-- O8, V4 4.8: every WF copy is the parsed node with precisely that frame,
and its inner hierarchy is the transported inner hierarchy of every source node
realizing its pattern. The source-language premise supplies an actual realization;
no pre-existing node or agreement of inner structures is assumed. -/
theorem WF_is_node (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : 1 ≤ n) (A : S.ι) (ψ : Iso d)
    (q : Pattern S (Colour S P) n A) (hq : q ∈ sourceLanguage C n A)
    (hpattern : normalisedPattern Y n A ψ = q) :
    (⟨A, ψ⟩ : FramedNode S) ∈ (parsedHierarchy Y hY).nodes n ∧
      ∀ (U : HonestSource S) (φ : Iso d),
        (⟨A, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n →
        normalisedPattern (honestLift C U) n A φ = q →
          InnerStructure U.hierarchy (parsedHierarchy Y hY) n ⟨A, φ⟩ ⟨A, ψ⟩ := by
  sorry

/-- O7/O8, V4 4.7--4.8: positive-height nodes are exactly the framed WF copies. -/
theorem parsed_nodes_iff (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : 1 ≤ n) (N : FramedNode S) :
    N ∈ (parsedHierarchy Y hY).nodes n ↔ IsWFConfig (sourceLanguage C) Y n N := by
  constructor
  · exact node_is_WF Y hY n hn N
  · intro h
    exact (WF_is_node Y hY n hn N.ty N.frame
      (normalisedPattern Y n N.ty N.frame) h rfl).1

/-- O9, V4 4.9, 1.0(d): exactly one parsed node contains any physical
 tile-interior point, using closed node supports in the containment test.
Regular closedness rules out an additional node touching the point only on its
boundary. The unique node includes its type and assigned frame. -/
theorem parsed_node_through_interior (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (n : ℕ) (x : E d) (hx : Y.IsTileInterior x) :
    ∃! N : FramedNode S, x ∈ N.carrier n ∧ N ∈ (parsedHierarchy Y hY).nodes n := by
  sorry

/-- O9, V4 4.9: every tile-interior point lies in exactly one framed WF copy
at each positive height. Closed containment is used, and uniqueness includes both
the prototype and full isometry. -/
theorem point_uniqueness (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (n : ℕ) (hn : 1 ≤ n) (x : E d) (hx : Y.IsTileInterior x) :
    ∃! N : FramedNode S, x ∈ N.carrier n ∧ IsWFConfig (sourceLanguage C) Y n N := by
  obtain ⟨N, hN, huniq⟩ := parsed_node_through_interior Y hY n x hx
  refine ⟨N, ⟨hN.1, node_is_WF Y hY n hn N hN.2⟩, ?_⟩
  intro M hM
  exact huniq M ⟨hM.1, (parsed_nodes_iff Y hY n hn M).mpr hM.2⟩

/-- O10, V4 4.10: specifications of a single all-source section.
An actual source has a proper lift on precisely its native tiles. Family languages
are the full honest languages, hence finite and empty exactly at absent honest
height/type nodes. Height zero is included under the inherited extension D8. -/
structure AllSourceSection (C : ClusterData S P)
    (s : S.Species → HonestSource S) : Prop where
  /-- O10, V4 4.10: the section lies over the exact given physical source. -/
  tiling_eq : ∀ Z, (s Z).tiling = Z.val
  /-- O10, V4 4.10(1): every selected honest lift is proper. -/
  proper : ∀ Z, MProper (honestLift C (s Z))
  /-- O10, V4 4.10(1), 2.14(a): projection preserves the entire typed partition. -/
  tiles : ∀ Z, (honestLift C (s Z)).project (nativeDecoration S P C) = Z.val
  /-- O10, V4 4.10(1): pointwise recovery of the native old marking. -/
  projection : ∀ Z x, π S P ((honestLift C (s Z)).marking x) = oldMarking Z.val x
  /-- O10, V4 4.10(2): equality with the full joint honest-source language. -/
  languages : ∀ n A,
    sectionLanguage (fun U : HonestSource S => (honestLift C U).marking) s n A =
      sourceLanguage C n A
  /-- O10, V4 4.10(2): each resulting language is finite. -/
  finite_languages : ∀ n A,
    (sectionLanguage (fun U : HonestSource S => (honestLift C U).marking) s n A).Finite
  /-- O10, V4 4.10(2): emptiness means no honest source node at that height/type. -/
  empty_iff : ∀ n A,
    sectionLanguage (fun U : HonestSource S => (honestLift C U).marking) s n A = ∅ ↔
      ¬ ∃ (U : HonestSource S) (φ : Iso d),
        (⟨A, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n

/-- O10, V4 4.10: a section realizes every source pattern simultaneously.
This is proved from C2's translated-witness section, compiler covariance, and finite
languages. The empty-species case is included; the theorem assumes no source exists. -/
theorem all_source_section (C : ClusterData S P) :
    ∃ s : S.Species → HonestSource S, AllSourceSection C s := by
  obtain ⟨s, hs, hl, _⟩ := translated_witness_section
    (fun U : HonestSource S => (honestLift C U).marking)
    (honestLift_translationCovariant C) (sourceLanguage_finite C)
  have languages : ∀ n A,
      sectionLanguage (fun U : HonestSource S => (honestLift C U).marking) s n A =
        sourceLanguage C n A := hl
  refine ⟨s, {
    tiling_eq := hs
    proper := fun Z => honestLift_proper C (s Z)
    tiles := fun Z => (honestLift_tiles C (s Z)).trans (hs Z)
    projection := ?_
    languages := languages
    finite_languages := ?_
    empty_iff := ?_ }⟩
  · intro Z x
    rw [honestLift_projection, hs Z]
  · intro n A
    rw [languages n A]
    exact sourceLanguage_finite C n A
  · intro n A
    rw [languages n A]
    exact sourceLanguage_eq_empty_iff C n A

/-- O10, V4 4.10: the chosen all-source section, from its complete existence theorem.
The choice is a section over every species member and is not required to commute
with translations. All language equalities refer to this same section. -/
def sourceSection (C : ClusterData S P) : S.Species → HonestSource S :=
  Classical.choose (all_source_section C)

/-- O10, V4 4.10: every clause holds for the very same selected section. -/
theorem sourceSection_spec (C : ClusterData S P) : AllSourceSection C (sourceSection C) :=
  Classical.choose_spec (all_source_section C)

/-- O10, V4 4.10, 1.12: the selected hierarchy transported along exact tiling equality. -/
def sectionHierarchy (C : ClusterData S P) (Z : Tiling S) (hZ : Z ∈ S.Species) :
    CoherentHierarchy S Z :=
  cast (congrArg (CoherentHierarchy S) ((sourceSection_spec C).tiling_eq ⟨Z, hZ⟩))
    (sourceSection C ⟨Z, hZ⟩).hierarchy

/-- O10, V4 4.10, 1.12: transport along equality does not change framed node sets. -/
theorem hierarchy_cast_nodes {T T' : Tiling S} (h : T = T')
    (H : CoherentHierarchy S T) (n : ℕ) :
    (cast (congrArg (CoherentHierarchy S) h) H).nodes n = H.nodes n := by
  cases h
  rfl

/-- O10, V4 4.10: the selected hierarchy has exactly its honest source's nodes. -/
theorem sectionHierarchy_nodes (C : ClusterData S P) (Z : Tiling S)
    (hZ : Z ∈ S.Species) (n : ℕ) :
    (sectionHierarchy C Z hZ).nodes n = (sourceSection C ⟨Z, hZ⟩).hierarchy.nodes n :=
  hierarchy_cast_nodes ((sourceSection_spec C).tiling_eq ⟨Z, hZ⟩) _ n

/-- O10, V4 4.10(2): every full source-language pattern occurs in the selected family.
Nonemptiness is conditional on the supplied pattern, rather than asserted globally. -/
theorem sourceSection_realizes (C : ClusterData S P) (n : ℕ) (A : S.ι)
    (q : Pattern S (Colour S P) n A) (hq : q ∈ sourceLanguage C n A) :
    ∃ (Z : S.Species) (φ : Iso d),
      (⟨A, φ⟩ : FramedNode S) ∈ (sourceSection C Z).hierarchy.nodes n ∧
        q = normalisedPattern (honestLift C (sourceSection C Z)) n A φ := by
  rw [← (sourceSection_spec C).languages n A] at hq
  exact hq

/-- O7/O8/F, V4 4.7--4.8, §5.5: positive-height node equality determines
height zero, including frames, because the ground nodes are exactly all children
of the height-one nodes. The underlying tilings may be different. -/
theorem CoherentHierarchy.ground_eq_of_one_eq {T T' : Tiling S}
    (H : CoherentHierarchy S T) (H' : CoherentHierarchy S T')
    (h : H.nodes 1 = H'.nodes 1) : H.nodes 0 = H'.nodes 0 := by
  ext N
  constructor
  · intro hN
    let q : {N // N ∈ H.nodes 0} := ⟨N, hN⟩
    have he : N = (H.parent 0 q).val.child 0 (H.role 0 q) := H.child_eq 0 q
    rw [he]
    exact H'.children_mem 0 _ (h ▸ (H.parent 0 q).property) (H.role 0 q)
  · intro hN
    let q : {N // N ∈ H'.nodes 0} := ⟨N, hN⟩
    have he : N = (H'.parent 0 q).val.child 0 (H'.role 0 q) := H'.child_eq 0 q
    rw [he]
    exact H.children_mem 0 _ (h.symm ▸ (H'.parent 0 q).property) (H'.role 0 q)

/-- O8/F, V4 4.8, §5.5: moving a child transports its full substitution frame. -/
theorem FramedNode.move_child (N : FramedNode S) (n : ℕ) (i : S.I N.ty) (g : Iso d) :
    (N.child n i).move g = (N.move g).child n i := by
  apply FramedNode.ext
  · rfl
  · ext x : 1
    rfl

/-- O8/F, V4 4.8, §5.5: inverse transport recovers a node including its frame. -/
theorem FramedNode.move_symm_move (N : FramedNode S) (g : Iso d) :
    (N.move g.symm).move g = N := by
  apply FramedNode.ext
  · rfl
  · ext x : 1
    exact g.apply_symm_apply (N.frame x)

omit [Fact (2 ≤ d)] in
/-- O8/F, V4 4.8, §5.5: equality of complete marked carriers gives equality
of their marks at every common point, independently of subtype membership proofs. -/
theorem MarkedSet.mark_eq_of_eq {X : Type} {Q Q' : MarkedSet d X}
    (h : Q = Q') (x : E d) (hx : x ∈ Q.carrier) (hx' : x ∈ Q'.carrier) :
    Q.mark ⟨x, hx⟩ = Q'.mark ⟨x, hx'⟩ := by
  cases h
  rfl

/-- O8/F/Y1, V4 4.8, 5.7: a tile-and-marking symmetry preserves the entire
global marking. This is the action on full marked carriers, including boundaries. -/
theorem symmetry_marking (Y : MarkedTiling (systemM S P C)) (g : Iso d)
    (hg : Y.IsSymmetry g) (x : E d) : Y.marking (g x) = Y.marking x := by
  obtain ⟨t, ht, hxt⟩ := Y.cover x
  have hmem : t.toMarkedSet.move g ∈ Y.markedCarriers := by
    change (fun Q : MarkedSet d (Colour S P) => Q.move g) '' Y.markedCarriers =
      Y.markedCarriers at hg
    rw [← hg]
    exact ⟨t.toMarkedSet, ⟨t, ht, rfl⟩, rfl⟩
  obtain ⟨u, hu, he⟩ := hmem
  have hmove : g x ∈ (t.toMarkedSet.move g).carrier := ⟨x, hxt, rfl⟩
  have hxu : g x ∈ u.carrier :=
    Eq.mpr (congrArg (fun Q : MarkedSet d (Colour S P) => g x ∈ Q.carrier) he) hmove
  calc
    Y.marking (g x) = u.mark ⟨g x, hxu⟩ := Y.marking_eq_tile u hu (g x) hxu
    _ = (t.toMarkedSet.move g).mark ⟨g x, hmove⟩ :=
      MarkedSet.mark_eq_of_eq he (g x) hxu hmove
    _ = t.mark ⟨x, hxt⟩ := by
      change t.mark ⟨g.symm (g x), _⟩ = t.mark ⟨x, hxt⟩
      congr 1
      exact Subtype.ext (g.symm_apply_apply x)
    _ = Y.marking x := (Y.marking_eq_tile t ht x hxt).symm

/-- O8/F, V4 4.8, §5.5: symmetry preserves normalized patterns in transported frames. -/
theorem normalisedPattern_symmetry (Y : MarkedTiling (systemM S P C)) (g : Iso d)
    (hg : Y.IsSymmetry g) (n : ℕ) (N : FramedNode S) :
    normalisedPattern Y n N.ty (N.move g).frame =
      normalisedPattern Y n N.ty N.frame := by
  funext x
  exact symmetry_marking Y g hg (N.frame x)

/-- O8/F, V4 4.8, §5.5: a symmetry carries every parsed node to a parsed node.
Positive heights follow from nodes = WF. Height zero follows by transporting the
children of height-one nodes, so arbitrary ground-frame choices are not assumed. -/
theorem parsed_node_move_mem (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Iso d) (hg : Y.IsSymmetry g) (n : ℕ) (N : FramedNode S)
    (hN : N ∈ (parsedHierarchy Y hY).nodes n) :
    N.move g ∈ (parsedHierarchy Y hY).nodes n := by
  have positive : ∀ m, 1 ≤ m → ∀ M : FramedNode S,
      M ∈ (parsedHierarchy Y hY).nodes m →
        M.move g ∈ (parsedHierarchy Y hY).nodes m := by
    intro m hm M hM
    apply (parsed_nodes_iff Y hY m hm (M.move g)).mpr
    change normalisedPattern Y m M.ty (M.move g).frame ∈ sourceLanguage C m M.ty
    rw [normalisedPattern_symmetry Y g hg]
    exact node_is_WF Y hY m hm M hM
  cases n with
  | zero =>
    let H := parsedHierarchy Y hY
    let q : {N // N ∈ H.nodes 0} := ⟨N, hN⟩
    have hp := positive 1 le_rfl (H.parent 0 q).val (H.parent 0 q).property
    have he : N = (H.parent 0 q).val.child 0 (H.role 0 q) := H.child_eq 0 q
    rw [he, FramedNode.move_child]
    exact H.children_mem 0 _ hp (H.role 0 q)
  | succ n => exact positive (n + 1) (by omega) N hN

/-- O8/F, V4 4.8, §5.5: the entire parsed hierarchy is equivariant, at all heights. -/
theorem parsedHierarchy_equivariant (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Iso d) (hg : Y.IsSymmetry g) (n : ℕ) :
    (fun N : FramedNode S => N.move g) '' (parsedHierarchy Y hY).nodes n =
      (parsedHierarchy Y hY).nodes n := by
  ext N
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact parsed_node_move_mem Y hY g hg n M hM
  · intro hN
    have hinv : Y.IsSymmetry g.symm := Y.symmetry_group_laws.2.2 g hg
    exact ⟨N.move g.symm, parsed_node_move_mem Y hY g.symm hinv n N hN,
      N.move_symm_move g⟩

end Enforce
