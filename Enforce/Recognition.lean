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

/-- Step 1 of the V4 proof of `WF_is_node` (V4 4.8):
"with their roles and frames". An ambient isometry loses no frame information. -/
private theorem WF_is_node_step1_move_injective (g : Iso d) :
    Function.Injective (fun N : FramedNode S => N.move g) := by
  intro N M h
  apply FramedNode.ext
  · have ht := congrArg FramedNode.ty h
    exact ht
  · ext x : 1
    have hf := congrArg (fun N : FramedNode S => N.frame x) h
    exact g.injective hf

/-- Step 1 of the V4 proof of `WF_is_node` (V4 4.8):
"with their roles and frames". Descendant addresses commute with ambient motion. -/
private theorem WF_is_node_step1_descendant_move (D N : FramedNode S)
    (m n : ℕ) (g : Iso d) :
    (D.move g).IsDescendant m (N.move g) n ↔ D.IsDescendant m N n := by
  constructor
  · rintro ⟨r, hr, w, hw⟩
    refine ⟨r, hr, w, ?_⟩
    apply WF_is_node_step1_move_injective g
    exact hw
  · rintro ⟨r, hr, w, rfl⟩
    exact ⟨r, hr, w, rfl⟩

/-- Step 1 of the V4 proof of `WF_is_node` (V4 4.8):
"the frame of the descendant". A zero-depth descendant is the root itself. -/
private theorem WF_is_node_step1_descendant_eq (D N : FramedNode S) (n : ℕ)
    (h : D.IsDescendant n N n) : D = N := by
  obtain ⟨r, hr, w, rfl⟩ := h
  have : r = 0 := by omega
  subst r
  cases N
  rfl

/-- Step 1 of the V4 proof of `WF_is_node` (V4 4.8):
"the restriction of q". Every prescribed child lies in its closed parent. -/
private theorem WF_is_node_step1_child_subset (N : FramedNode S) (n : ℕ)
    (i : S.I N.ty) : (N.child n i).carrier n ⊆ N.carrier (n + 1) := by
  have hplace (x : E d) : S.placeChild n i ((S.σ ^ n) x) =
      (S.σ ^ n) ((S.child N.ty i).frame x) := by
    change linearConj S.σ (n : ℤ) (S.child N.ty i).rotation.toLinearEquiv
        ((S.σ ^ n) x) + (S.σ ^ n) (S.child N.ty i).offset =
      (S.σ ^ n) ((S.child N.ty i).rotation x + (S.child N.ty i).offset)
    simp [linearConj, zpow_neg, LinearEquiv.mul_apply]
  rintro z ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hmem : (S.child N.ty i).frame x ∈ S.σ '' (S.proto N.ty).carrier := by
    rw [S.children_cover]
    exact mem_iUnion.mpr ⟨i, ⟨x, hx, rfl⟩⟩
  obtain ⟨y, hy, he⟩ := hmem
  refine ⟨(S.σ ^ (n + 1)) y, ⟨y, hy, rfl⟩, ?_⟩
  change N.frame ((S.σ ^ (n + 1)) y) = N.frame (S.placeChild n i ((S.σ ^ n) x))
  rw [hplace, ← he, pow_succ]
  rfl

/-- Step 1 of the V4 proof of `WF_is_node` (V4 4.8):
"the descendants ... in their positions". Descendant carriers are contained. -/
private theorem WF_is_node_step1_descendant_subset (D N : FramedNode S) (m n : ℕ)
    (h : D.IsDescendant m N n) : D.carrier m ⊆ N.carrier n := by
  obtain ⟨r, rfl, w, rfl⟩ := h
  induction r generalizing N with
  | zero => simpa [SubstSystem.descendantNode, FramedNode.move] using
      (Subset.rfl : N.carrier m ⊆ N.carrier m)
  | succ r ih =>
    have he : (S.descendantNode N.ty m (r + 1) w).move N.frame =
        (S.descendantNode (N.child (m + r) w.1).ty m r w.2).move
          (N.child (m + r) w.1).frame := rfl
    rw [he]
    exact (ih (N.child (m + r) w.1) w.2).trans
      (WF_is_node_step1_child_subset N (m + r) w.1)

/-- Step 1 of the V4 proof of `WF_is_node` (V4 4.8):
"with their roles and frames". A strict descendant has a prescribed predecessor
inside the same standard subdivision. -/
private theorem WF_is_node_step1_predecessor (D N : FramedNode S) (m n : ℕ)
    (hm : m < n) (h : D.IsDescendant m N n) :
    ∃ B : FramedNode S, B.IsDescendant (m + 1) N n ∧
      ∃ i : S.I B.ty, D = B.child m i := by
  obtain ⟨r, rfl, w, rfl⟩ := h
  induction r generalizing N with
  | zero => omega
  | succ r ih =>
    cases r with
    | zero =>
      refine ⟨N, Parser.descendant_refl N (m + 1), w.1, ?_⟩
      rfl
    | succ r =>
      obtain ⟨B, hB, i, hi⟩ := ih (N.child (m + (r + 1)) w.1) (by omega) w.2
      exact ⟨B, Parser.descendant_trans B _ N (m + 1) (m + (r + 1))
        (m + (r + 1 + 1)) hB (Parser.child_descendant N _ w.1), i, hi⟩

/-- Step 1 of the V4 proof of `WF_is_node` (V4 4.8):
"with their roles and frames". The actual parent of a strict inner node stays inside. -/
private theorem WF_is_node_step1_parent_inside {T : Tiling S}
    (H : CoherentHierarchy S T) (q : H.Node) (N : FramedNode S) (n : ℕ)
    (hN : N ∈ H.nodes n) (hq : q.1 < n) (hd : q.2.val.IsDescendant q.1 N n) :
    (H.parent q.1 q.2).val.IsDescendant (q.1 + 1) N n := by
  obtain ⟨B, hB, i, hi⟩ := WF_is_node_step1_predecessor q.2.val N q.1 n hq hd
  have hm := Parser.hierarchy_descendant_mem H n (q.1 + 1) N B hN hB
  have he := H.parent_unique q.1 q.2 B hm ⟨i, hi⟩
  exact he ▸ hB

/-- Step 1 of the V4 proof of `WF_is_node` (V4 4.8):
"with their roles and frames". Distinct substitution roles give distinct children. -/
private theorem WF_is_node_step1_child_injective (N : FramedNode S) (n : ℕ) :
    Function.Injective (N.child n) := by
  intro i j h
  have ht : (S.child N.ty i).ty = (S.child N.ty j).ty := congrArg FramedNode.ty h
  have hf : (S.child N.ty i).frame = (S.child N.ty j).frame := by
    ext x : 1
    apply (S.σ ^ n).injective
    have hi (a : S.I N.ty) : S.placeChild n a ((S.σ ^ n) x) =
        (S.σ ^ n) ((S.child N.ty a).frame x) := by
      change linearConj S.σ (n : ℤ) (S.child N.ty a).rotation.toLinearEquiv
          ((S.σ ^ n) x) + (S.σ ^ n) (S.child N.ty a).offset =
        (S.σ ^ n) ((S.child N.ty a).rotation x + (S.child N.ty a).offset)
      simp [linearConj, zpow_neg, LinearEquiv.mul_apply]
    have he' := congrArg (fun X : FramedNode S => X.frame ((S.σ ^ n) x)) h
    have he := N.frame.injective he'
    exact (hi i).symm.trans (he.trans (hi j))
  by_contra hne
  have hd := S.children_disjoint N.ty hne
  have hs : placedSet (S.child N.ty i).frame (S.proto (S.child N.ty i).ty).carrier =
      placedSet (S.child N.ty j).frame (S.proto (S.child N.ty j).ty).carrier := by
    rw [ht, hf]
  dsimp only at hd
  rw [hs] at hd
  have hn : (interior (placedSet (S.child N.ty j).frame
      (S.proto (S.child N.ty j).ty).carrier)).Nonempty := by
    have hi := (S.child N.ty j).frame.toHomeomorph.image_interior
      (S.proto (S.child N.ty j).ty).carrier
    change (S.child N.ty j).frame '' interior (S.proto (S.child N.ty j).ty).carrier =
      interior ((S.child N.ty j).frame '' (S.proto (S.child N.ty j).ty).carrier) at hi
    rw [placedSet, ← hi]
    exact (S.proto _).interior_nonempty.image _
  exact hn.ne_empty (disjoint_self.mp hd)

/-- Step 1 of the V4 proof of `WF_is_node` (V4 4.8):
"with their roles and frames". A prescribed child has exactly its prescribed role. -/
private theorem WF_is_node_step1_role_of_child {T : Tiling S}
    (H : CoherentHierarchy S T) (n : ℕ) (D N : FramedNode S)
    (hD : D ∈ H.nodes n) (hN : N ∈ H.nodes (n + 1))
    (i : S.I N.ty) (he : D = N.child n i) :
    H.nodeRole ⟨n, ⟨D, hD⟩⟩ = ⟨N.ty, i⟩ := by
  have hp := H.parent_unique n ⟨D, hD⟩ N hN ⟨i, he⟩
  have hc := H.child_eq n ⟨D, hD⟩
  have aux : ∀ (B : FramedNode S) (j : S.I B.ty), B = N →
      B.child n j = N.child n i → (⟨B.ty, j⟩ : S.Role) = ⟨N.ty, i⟩ := by
    intro B j hb hj
    subst B
    exact congrArg (fun a => (⟨N.ty, a⟩ : S.Role))
      (WF_is_node_step1_child_injective N n hj)
  exact aux _ _ hp.symm (hc.symm.trans he)

/-- Step 2 of the V4 proof of `WF_is_node` (V4 4.8):
"its node structure is given by its children". Once the two equally typed roots
are actual nodes, their complete prescribed inner subdivisions correspond. -/
private theorem WF_is_node_step2_inner {T T' : Tiling S}
    (H : CoherentHierarchy S T) (H' : CoherentHierarchy S T')
    (n : ℕ) (A : S.ι) (φ ψ : Iso d)
    (hN : (⟨A, φ⟩ : FramedNode S) ∈ H.nodes n)
    (hM : (⟨A, ψ⟩ : FramedNode S) ∈ H'.nodes n) :
    InnerStructure H H' n ⟨A, φ⟩ ⟨A, ψ⟩ := by
  let g := φ.symm.trans ψ
  have hroot : (⟨A, φ⟩ : FramedNode S).move g = ⟨A, ψ⟩ := by
    apply FramedNode.ext
    · rfl
    · ext x : 1
      exact congrArg ψ (φ.symm_apply_apply x)
  have transport (m : ℕ) (D : FramedNode S) :
      (D.move g).IsDescendant m ⟨A, ψ⟩ n ↔ D.IsDescendant m ⟨A, φ⟩ n := by
    rw [← hroot]
    exact WF_is_node_step1_descendant_move D _ m n g
  have parent_mem (q : H.Node) (hq : q.1 < n)
      (hd : q.2.val.IsDescendant q.1 ⟨A, φ⟩ n) :
      (H.parent q.1 q.2).val.move g ∈ H'.nodes (q.1 + 1) := by
    apply Parser.hierarchy_descendant_mem H' n (q.1 + 1) _ _ hM
    exact (transport _ _).mpr (WF_is_node_step1_parent_inside H q _ n hN hq hd)
  constructor
  · intro m hm D
    constructor
    · rintro ⟨_, hd⟩
      exact ⟨Parser.hierarchy_descendant_mem H' n m _ _ hM
        ((transport m D).mpr hd), (transport m D).mpr hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨Parser.hierarchy_descendant_mem H n m _ _ hN
        ((transport m D).mp hd), (transport m D).mp hd⟩
  · intro q hq hd hm
    apply Eq.symm
    apply H'.parent_unique q.1 ⟨q.2.val.move g, hm⟩ _ (parent_mem q hq hd)
    exact ⟨H.role q.1 q.2, congrArg (fun D : FramedNode S => D.move g)
      (H.child_eq q.1 q.2)⟩
  · intro q hq hd hm
    exact WF_is_node_step1_role_of_child H' q.1 (q.2.val.move g)
      ((H.parent q.1 q.2).val.move g) hm (parent_mem q hq hd) (H.role q.1 q.2)
      (congrArg (fun D : FramedNode S => D.move g) (H.child_eq q.1 q.2))

/-- Step 3 of the V4 proof of `WF_is_node` (V4 4.8):
"the whole CORE cluster ... is matched, so Lemma 2.13 gives a tile".
Every source leaf inside the matched closed pattern is pinned with its full label
and transported frame. Properness is not needed for this local step. -/
private theorem WF_is_node_step3_pin_leaf (Y : MarkedTiling (systemM S P C))
    (U : HonestSource S) (n : ℕ) (A : S.ι) (φ ψ : Iso d)
    (hpattern : normalisedPattern Y n A ψ = normalisedPattern (honestLift C U) n A φ)
    (t : Compiler.GroundNode U)
    (hd : t.val.IsDescendant 0 (⟨A, φ⟩ : FramedNode S) n) :
    ∃ u ∈ Y.tiles, compilerLeaf C u = leafTypeOf U P ⟨0, t⟩ rfl ∧
      compilerFrame C u = t.val.frame.trans (φ.symm.trans ψ) := by
  let l := leafTypeOf U P ⟨0, t⟩ rfl
  have ht : l.prototype = t.val.ty := leafTypeOf_type U P ⟨0, t⟩ rfl
  obtain ⟨u, hu, hl, hf⟩ := cluster_rigidity C Y l .core
    (t.val.frame.trans (φ.symm.trans ψ)) (by
      intro x hx
      have hxl : x ∈ (S.proto l.prototype).carrier :=
        interior_subset (C.cluster_inside l .core hx)
      have hxt : t.val.frame x ∈ t.val.carrier 0 := by
        exact ⟨x, ⟨x, ht ▸ hxl, rfl⟩, rfl⟩
      have hxN := WF_is_node_step1_descendant_subset t.val ⟨A, φ⟩ 0 n hd hxt
      have hxstd : φ.symm (t.val.frame x) ∈ S.supertile n A := by
        obtain ⟨z, hz, he⟩ := hxN
        simpa [← he] using hz
      have hmark := congrFun hpattern ⟨φ.symm (t.val.frame x), hxstd⟩
      change Y.marking (ψ (φ.symm (t.val.frame x))) =
        (honestLift C U).marking (φ (φ.symm (t.val.frame x))) at hmark
      rw [φ.apply_symm_apply] at hmark
      change Y.marking (ψ (φ.symm (t.val.frame x))) = augmentedColour C l x
      rw [hmark]
      have htile : t.val.frame x ∈ (Compiler.honestTile C U t).carrier := ⟨x, hxl, rfl⟩
      rw [(honestLift C U).marking_eq_tile _ (honestLift_tile C U t) _ htile]
      change augmentedColour C l (t.val.frame.symm (t.val.frame x)) = augmentedColour C l x
      rw [t.val.frame.symm_apply_apply])
  exact ⟨u, hu, hl, hf.symm⟩

/-- Step 4 of the V4 proof of `WF_is_node` (V4 4.8):
"the K-ancestor". The actual ancestor of a prescribed descendant is its root. -/
private theorem WF_is_node_step4_ancestor_eq {T : Tiling S}
    (H : CoherentHierarchy S T) (q : H.Node) (r : ℕ) (N : FramedNode S)
    (hN : N ∈ H.nodes (q.1 + r)) (hd : q.2.val.IsDescendant q.1 N (q.1 + r)) :
    (H.ancestor q r).2.val = N := by
  induction r generalizing q with
  | zero => exact WF_is_node_step1_descendant_eq _ _ _ hd
  | succ r ih =>
    have hm : N ∈ H.nodes ((H.parentNode q).1 + r) := by
      simpa only [CoherentHierarchy.parentNode, Nat.add_assoc, Nat.add_comm 1 r] using hN
    have hp : (H.parentNode q).2.val.IsDescendant (H.parentNode q).1 N
        ((H.parentNode q).1 + r) := by
      simpa only [CoherentHierarchy.parentNode, Nat.add_assoc, Nat.add_comm 1 r] using
        (WF_is_node_step1_parent_inside H q N (q.1 + (r + 1)) hN (by omega) hd)
    exact ih (H.parentNode q) hm hp

/-- Step 4 of the V4 proof of `WF_is_node` (V4 4.8):
"Pick one native descendant". Every actual prototype has a role word of any depth. -/
private theorem WF_is_node_step4_word_nonempty (A : S.ι) (n : ℕ) :
    Nonempty (S.RoleWord A n) := by
  induction n generalizing A with
  | zero => exact ⟨()⟩
  | succ n ih =>
    obtain ⟨i⟩ := Parser.roles_nonempty A
    obtain ⟨w⟩ := ih (S.child A i).ty
    exact ⟨⟨i, w⟩⟩

/-- Step 4 of the V4 proof of `WF_is_node` (V4 4.8):
"the frame of the descendant of β with role word η". The pinned leaf forces
its entire K-certificate, and cancellation recovers the proposed low root frame. -/
private theorem WF_is_node_step4_low (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (U : HonestSource S) (n : ℕ) (hn : n ≤ P.K)
    (A : S.ι) (φ ψ : Iso d)
    (hN : (⟨A, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n)
    (hpattern : normalisedPattern Y n A ψ = normalisedPattern (honestLift C U) n A φ) :
    (⟨A, ψ⟩ : FramedNode S) ∈ (parsedHierarchy Y hY).nodes n := by
  obtain ⟨w⟩ := WF_is_node_step4_word_nonempty A n
  let D := (S.nativeTile A n w).move φ
  have hd : D.IsDescendant 0 (⟨A, φ⟩ : FramedNode S) n := ⟨n, by omega, w, rfl⟩
  have hm := Parser.hierarchy_descendant_mem U.hierarchy n 0 ⟨A, φ⟩ D hN hd
  let t : Compiler.GroundNode U := ⟨D, hm⟩
  let q : U.Node := ⟨0, t⟩
  let l := leafTypeOf U P q rfl
  let g := φ.symm.trans ψ
  let B₀ := (U.hierarchy.ancestor q P.K).2.val
  obtain ⟨u, hu, hl, hf⟩ := WF_is_node_step3_pin_leaf Y U n A φ ψ hpattern t hd
  obtain ⟨B, hcert, hframe, _, _⟩ := (compiler_certificates C Y hY).1 u hu
  rw [hl] at hcert hframe
  rw [hf] at hframe
  have hpos : l.position.trans B₀.frame = t.val.frame := by
    have he := (Classical.choose_spec (U.leafIndex_exists P q rfl)).1
    exact congrArg FramedNode.frame he
  have hb : B.node = B₀.move g := by
    apply FramedNode.ext
    · exact congrArg (fun D : CertificateSymbol S P => D.val.ty) hcert
    · change B.frame = B₀.frame.trans g
      rw [hframe, ← hpos]
      ext x : 1
      exact congrArg (fun y => g (B₀.frame y)) (l.position.apply_symm_apply x)
  have hancestor : (U.hierarchy.ancestor q n).2.val = (⟨A, φ⟩ : FramedNode S) :=
    WF_is_node_step4_ancestor_eq U.hierarchy q n ⟨A, φ⟩
      (by simpa only [q, zero_add] using hN) (by simpa only [q, zero_add] using hd)
  have hinside := U.hierarchy.ancestor_descendant (U.hierarchy.ancestor q n) (P.K - n)
  rw [U.hierarchy.ancestor_add, Nat.add_sub_of_le hn] at hinside
  have hheight (r : ℕ) : (U.hierarchy.ancestor q r).1 = r := by
    simpa only [CoherentHierarchy.ancestor_height, q, zero_add]
  have hrootdesc : (⟨A, φ⟩ : FramedNode S).IsDescendant n B₀ P.K := by
    simpa only [hheight, hancestor] using hinside
  have hroot : (⟨A, φ⟩ : FramedNode S).move g = (⟨A, ψ⟩ : FramedNode S) := by
    apply FramedNode.ext
    · rfl
    · ext x : 1
      exact congrArg ψ (φ.symm_apply_apply x)
  have hparsed : B.node ∈ (parsedHierarchy Y hY).nodes P.K := by
    rw [← parsedHierarchy_nodes Y hY P.K, parsedDecodedLevel_upper Y hY P.K le_rfl,
      (parsedHierarchy_base Y hY).1]
    exact ⟨B, rfl⟩
  apply Parser.hierarchy_descendant_mem (parsedHierarchy Y hY) P.K n B.node _ hparsed
  rw [hb, ← hroot]
  exact (WF_is_node_step1_descendant_move _ _ n P.K g).mpr hrootdesc

/-- Step 5 of the V4 proof of `WF_is_node` (V4 4.8):
"the normalised pattern ... is the restriction of q". Restricting equal closed
patterns gives equality in each child's exact composed frame. -/
private theorem WF_is_node_step5_child_pattern
    (Y : MarkedTiling (systemM S P C)) (U : HonestSource S)
    (n : ℕ) (A : S.ι) (φ ψ : Iso d) (i : S.I A)
    (hpattern : normalisedPattern Y (n + 1) A ψ =
      normalisedPattern (honestLift C U) (n + 1) A φ) :
    normalisedPattern Y n (S.child A i).ty ((S.placeChild n i).trans ψ) =
      normalisedPattern (honestLift C U) n (S.child A i).ty
        ((S.placeChild n i).trans φ) := by
  funext x
  have hx : S.placeChild n i x ∈ S.supertile (n + 1) A := by
    have hh := WF_is_node_step1_child_subset
      (⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩ : FramedNode S) n i
      (show S.placeChild n i x ∈
        ((⟨A, AffineIsometryEquiv.refl ℝ (E d)⟩ : FramedNode S).child n i).carrier n from
        ⟨x, x.property, rfl⟩)
    obtain ⟨z, hz, he⟩ := hh
    exact he ▸ hz
  exact congrFun hpattern ⟨S.placeChild n i x, hx⟩

/-- Step 6 of the V4 proof of `WF_is_node` (V4 4.8):
"a first-generation facet". Every internal prototype facet has a canonical
paired incidence with exactly its positioned carrier. -/
private theorem WF_is_node_step6_incidence (A : S.ι) (f : PrimitiveFacet S A) :
    ∃ ι : P.Incidence, ι.val.ty = f.birthType ∧ ι.val.positioned = f.localCarrier := by
  obtain ⟨i, F, hcarrier, hint⟩ := f.realization
  let N : FramedNode S := ⟨f.birthType, AffineIsometryEquiv.refl ℝ (E d)⟩
  have hcell (j : S.I f.birthType) (G : FacetName S (S.child f.birthType j).ty) :
      (N.child 0 j).cell 0 G.val = placedSet (S.child f.birthType j).frame G.val.carrier := by
    ext x
    rfl
  have hroot : N.carrier (0 + 1) = S.supertile 1 f.birthType := by
    exact image_id _
  have hnonempty : (relint (placedSet (S.child f.birthType i).frame F.val.carrier)).Nonempty := by
    have he := (S.child f.birthType i).frame.toAffineIsometry.image_intrinsicInterior F.val.carrier
    change relint (placedSet (S.child f.birthType i).frame F.val.carrier) =
      (S.child f.birthType i).frame '' relint F.val.carrier at he
    rw [he]
    exact F.val.flat.relint_nonempty.image _
  have hmeet : (relint ((N.child 0 i).cell 0 F.val) ∩ interior (N.carrier (0 + 1))).Nonempty := by
    rw [hcell, hroot]
    obtain ⟨x, hx⟩ := hnonempty
    exact ⟨x, hx, hint (hcarrier ▸ hx)⟩
  obtain ⟨j, ⟨hji, G, hGF, _⟩, _⟩ := (internal_facet_pairing N 0 i F hmeet).2
  let ι : PrimitiveIncidence S := {
    ty := f.birthType
    left := i
    right := j
    distinct := Ne.symm hji
    leftFacet := F
    rightFacet := G
    paired := by simpa only [hcell] using hGF.symm
    internal := by simpa only [hcarrier] using hint }
  refine ⟨P.canonical ι, (P.canonical_spec ι).1.symm, ?_⟩
  exact (P.canonical_spec ι).2.symm.trans hcarrier.symm

/-- Step 6 of the V4 proof of `WF_is_node` (V4 4.8):
"the first non-placeholder descendant ... depth s ≤ p". A high source node
has an internal primitive packet whose PRESENT slot reads that very node. -/
private theorem WF_is_node_step6_readable (U : HonestSource S) (q : U.Node)
    (hq : P.K ≤ q.1) :
    ∃ (g : PrimitiveOccurrence U P) (j : Fin P.k),
      1 < g.birth.1 ∧ j.val ≤ P.p ∧ U.hierarchy.ancestor g.birth j.val = q ∧
        mask U P g j := by
  obtain ⟨f, hf⟩ := firstBranchingFacets_nonempty q.2.val.ty
  have hdepth : f.depth ≤ P.p := by
    have he : f.depth = (firstBranching q.2.val.ty).1 := congrArg Sigma.fst hf
    rw [he, P.p_eq]
    exact (firstBranching_spec q.2.val.ty).2.2
  have hdn : f.depth ≤ q.1 := by have := P.K_placeholder; omega
  have hdk : f.depth < P.k := by have := P.k_lower; omega
  have hpos : 1 < q.1 - f.depth := by have := P.K_placeholder; omega
  let b := U.descendant q f.depth hdn f.word
  obtain ⟨ι, hι, hcarrier⟩ := WF_is_node_step6_incidence (P := P) q.2.val.ty f
  let g : PrimitiveOccurrence U P := {
    birth := b
    positive := by exact Nat.le_of_lt hpos
    incidence := ι
    parent_type := hι.trans (U.descendant_type q f.depth hdn f.word).symm }
  let j : Fin P.k := ⟨f.depth, hdk⟩
  have hh : b.1 + f.depth = q.1 := Nat.sub_add_cancel hdn
  have hd : b.2.val.IsDescendant b.1 q.2.val (b.1 + f.depth) := by
    exact ⟨f.depth, rfl, f.word, rfl⟩
  have ha : U.hierarchy.ancestor b f.depth = q := by
    apply Sigma.ext
    · rw [U.hierarchy.ancestor_height, hh]
    · apply (Subtype.heq_iff_coe_eq (fun N => by rw [U.hierarchy.ancestor_height, hh])).mpr
      exact WF_is_node_step4_ancestor_eq U.hierarchy b f.depth q.2.val
        (hh.symm ▸ q.2.property) hd
  refine ⟨g, j, hpos, hdepth, ha, ?_⟩
  change P.InPrincipal (U.hierarchy.ancestor b f.depth).2.val
    (U.hierarchy.ancestor b f.depth).1 g.carrier
  rw [ha]
  have hreq : f ∈ P.required q.2.val.ty := by
    rw [P.required_eq, mem_required_list]
    exact Or.inr (Or.inl hf)
  refine ⟨f, P.required_mem _ f hreq, ?_⟩
  have hframe := (f.birthFrame_spec q.1 hdn).2
  have hpoint (x : E d) : b.2.val.prototypeFrame b.1 x =
      q.2.val.prototypeFrame q.1 (f.birthFrame x) := by
    have he := congrArg (fun e : E d ≃ᵃ[ℝ] E d => e x) hframe
    change q.2.val.frame ((f.birthNode q.1).frame ((S.σ ^ (q.1 - f.depth)) x)) =
      q.2.val.frame ((S.σ ^ q.1) (f.birthFrame x))
    apply congrArg q.2.val.frame
    apply (S.σ ^ q.1).symm.injective
    simpa only [LinearEquiv.symm_apply_apply] using he
  ext x
  change x ∈ q.2.val.prototypeFrame q.1 '' (f.birthFrame '' (S.σ.symm '' f.localCarrier)) ↔
    x ∈ (P.incidencePlacement b.2.val b.1 ι) '' ι.val.leftFacet.val.carrier
  rw [← hcarrier]
  simp only [PrimitiveIncidence.positioned, placedSet, Set.image_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, hpoint (S.σ.symm ((S.child ι.val.ty ι.val.left).frame y))⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (hpoint (S.σ.symm ((S.child ι.val.ty ι.val.left).frame y))).symm⟩

/-- Step 7 of the V4 proof of `WF_is_node` (V4 4.8):
"the corresponding source tiles". The honest lift retains each native frame. -/
private theorem WF_is_node_step7_honest_tile (U : HonestSource S)
    (t : Compiler.GroundNode U) : tileNode (Compiler.honestTile C U t) = t.val := by
  apply FramedNode.ext
  · change (compilerLeaf C (Compiler.honestTile C U t)).prototype = _
    rw [(honestLift_tile_data C U t).1]
    exact leafTypeOf_type U P ⟨0, t⟩ rfl
  · exact (honestLift_tile_data C U t).2

/-- Step 7 of the V4 proof of `WF_is_node` (V4 4.8):
"the corresponding source tiles". Source nodes have all their actual lifted leaves. -/
private theorem WF_is_node_step7_source_block (U : HonestSource S) (n : ℕ)
    (N : FramedNode S) (hN : N ∈ U.hierarchy.nodes n) : IsBlock (honestLift C U) n N := by
  intro w
  let D := (S.nativeTile N.ty n w).move N.frame
  have hd : D.IsDescendant 0 N n := ⟨n, by omega, w, rfl⟩
  let t : Compiler.GroundNode U :=
    ⟨D, Parser.hierarchy_descendant_mem U.hierarchy n 0 N D hN hd⟩
  exact ⟨Compiler.honestTile C U t, honestLift_tile C U t, WF_is_node_step7_honest_tile U t⟩

/-- Step 7 of the V4 proof of `WF_is_node` (V4 4.8):
"the corresponding facet f". Regard a source birth as a geometric birth. -/
private def WF_is_node_step7_source_birth {U : HonestSource S}
    (g : PrimitiveOccurrence U P) : Parser.BornFacet P where
  height := g.birth.1
  positive := g.positive
  birth := g.birth.2.val
  incidence := g.incidence
  parent_type := g.parent_type

/-- Step 7 of the V4 proof of `WF_is_node` (V4 4.8):
"the corresponding facet f". Transport a primitive birth with its canonical incidence. -/
private def WF_is_node_step7_moved_birth {U : HonestSource S}
    (g : PrimitiveOccurrence U P) (γ : Iso d) : Parser.BornFacet P where
  height := g.birth.1
  positive := g.positive
  birth := g.birth.2.val.move γ
  incidence := g.incidence
  parent_type := g.parent_type

/-- Step 7 of the V4 proof of `WF_is_node` (V4 4.8):
"the corresponding facet f". Ambient motion transports every named cell. -/
private theorem WF_is_node_step7_cell_move (N : FramedNode S) (n : ℕ)
    (F : Cell d) (γ : Iso d) : (N.move γ).cell n F = γ '' N.cell n F := by
  simp only [FramedNode.cell, Set.image_image]
  rfl

/-- Step 7 of the V4 proof of `WF_is_node` (V4 4.8):
"their leaf types equal those of the corresponding source tiles, hence the packet
attached to f in Y equals the source packet". One actual native facet piece,
pinned by its CORE, identifies the whole primitive packet. -/
private theorem WF_is_node_step7_packet_match (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (U : HonestSource S) (n : ℕ) (A : S.ι) (φ ψ : Iso d)
    (hpattern : normalisedPattern Y n A ψ = normalisedPattern (honestLift C U) n A φ)
    (g : PrimitiveOccurrence U P)
    (hd : g.birth.2.val.IsDescendant g.birth.1 (⟨A, φ⟩ : FramedNode S) n)
    (hg : (WF_is_node_step7_moved_birth g (φ.symm.trans ψ)).birth ∈
      (parsedHierarchy Y hY).nodes g.birth.1) :
    parsedPrimitivePacket Y hY (WF_is_node_step7_moved_birth g (φ.symm.trans ψ)) hg =
      some (packetOf U P g) := by
  let γ := φ.symm.trans ψ
  let gs := WF_is_node_step7_source_birth g
  let gy := WF_is_node_step7_moved_birth g γ
  have hs : gs.leftNode ∈ U.hierarchy.nodes (g.birth.1 - 1) :=
    gs.left_mem U.hierarchy g.birth.2.property
  obtain ⟨t, f, ht, htd, htf⟩ := Parser.facet_piece_exists (honestLift C U)
    (g.birth.1 - 1) gs.leftNode (WF_is_node_step7_source_block U _ _ hs)
    g.incidence.val.leftFacet
  obtain ⟨t₀, rfl⟩ := ht
  have ht₀ := WF_is_node_step7_honest_tile (C := C) U t₀
  let f₀ : FacetName S t₀.val.ty := ⟨f.val,
    (congrArg (fun N : FramedNode S => f.val ∈ (S.cx N.ty).facets) ht₀).mp f.property⟩
  have htd₀ : t₀.val.IsDescendant 0 gs.leftNode (g.birth.1 - 1) := by
    simpa only [ht₀] using htd
  have htf₀ : t₀.val.cell 0 f₀.val ⊆ gs.leftNode.cell (g.birth.1 - 1)
      g.incidence.val.leftFacet.val := by simpa only [ht₀] using htf
  have htroot : t₀.val.IsDescendant 0 (⟨A, φ⟩ : FramedNode S) n :=
    Parser.descendant_trans _ _ _ 0 g.birth.1 n
      (Parser.descendant_trans _ _ _ 0 (g.birth.1 - 1) g.birth.1
        htd₀ gs.sides_descendant.1) hd
  obtain ⟨u, hu, hl, hframe⟩ := WF_is_node_step3_pin_leaf Y U n A φ ψ hpattern t₀ htroot
  have hnode : tileNode u = t₀.val.move γ := by
    apply FramedNode.ext
    · change (compilerLeaf C u).prototype = t₀.val.ty
      rw [hl]
      exact leafTypeOf_type U P ⟨0, t₀⟩ rfl
    · exact hframe
  let fy : FacetName S (tileNode u).ty := ⟨f₀.val,
    (congrArg (fun N : FramedNode S => f₀.val ∈ (S.cx N.ty).facets) hnode).mpr f₀.property⟩
  have hleft : gy.leftNode = gs.leftNode.move γ := rfl
  have hpiece : Parser.IsFacetPiece Y (g.birth.1 - 1) gy.leftNode
      g.incidence.val.leftFacet u fy := by
    refine ⟨hu, ?_, ?_⟩
    · rw [hnode, hleft]
      exact (WF_is_node_step1_descendant_move _ _ 0 (g.birth.1 - 1) γ).mpr htd₀
    · change (tileNode u).cell 0 f₀.val ⊆ gy.leftNode.cell (g.birth.1 - 1)
        g.incidence.val.leftFacet.val
      rw [hnode, hleft, WF_is_node_step7_cell_move, WF_is_node_step7_cell_move]
      exact image_mono htf₀
  have hread := parsedFacetPacket_spec Y hY
    ⟨g.birth.1 - 1, ⟨gy.leftNode, gy.left_mem (parsedHierarchy Y hY) hg⟩⟩
    g.incidence.val.leftFacet u fy hpiece
  change leafPacket (compilerLeaf C u) f₀.val =
    parsedPrimitivePacket Y hY gy hg at hread
  rw [← hread, hl]
  have hleaf : leafPacket (leafTypeOf U P ⟨0, t₀⟩ rfl) f₀.val =
      U.facetPacket P ⟨0, t₀⟩ f₀ := by
    unfold leafPacket
    rw [← prePattern_of_leafType U P ⟨0, t₀⟩ rfl]
    simp only [prePatternOf, dif_pos f₀.property]
  rw [hleaf]
  apply (packet_attached U P g ⟨0, t₀⟩ rfl f₀ ?_).2
  exact htf₀.trans_eq gs.sides_carrier.1

/-- Step 7 of the V4 proof of `WF_is_node` (V4 4.8):
"by W4 ... the C-slot is S(C). Hence S(C) = S(C̃)". On already recognized
high nodes, the common internal packet recovers the exact source state. -/
private theorem WF_is_node_step7_state_match (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (U : HonestSource S) (n : ℕ) (hn : P.K ≤ n)
    (A : S.ι) (φ ψ : Iso d)
    (hN : (⟨A, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n)
    (hM : (⟨A, ψ⟩ : FramedNode S) ∈ (parsedHierarchy Y hY).nodes n)
    (hpattern : normalisedPattern Y n A ψ = normalisedPattern (honestLift C U) n A φ) :
    parsedState Y hY ⟨n, ⟨⟨A, ψ⟩, hM⟩⟩ = stateOf U P ⟨n, ⟨⟨A, φ⟩, hN⟩⟩ := by
  let q : U.Node := ⟨n, ⟨⟨A, φ⟩, hN⟩⟩
  obtain ⟨g, j, _, _, ha, hmask⟩ := WF_is_node_step6_readable U q hn
  let γ := φ.symm.trans ψ
  let gy := WF_is_node_step7_moved_birth g γ
  have hroot : (⟨A, φ⟩ : FramedNode S).move γ = (⟨A, ψ⟩ : FramedNode S) := by
    apply FramedNode.ext
    · rfl
    · ext x : 1
      exact congrArg ψ (φ.symm_apply_apply x)
  have hd : g.birth.2.val.IsDescendant g.birth.1 (⟨A, φ⟩ : FramedNode S) n := by
    have hv := congrArg (fun r : U.Node => r.2.val) ha
    have hh := congrArg Sigma.fst ha
    simpa only [hv, hh] using U.hierarchy.ancestor_descendant g.birth j.val
  have hd' : gy.birth.IsDescendant gy.height (⟨A, ψ⟩ : FramedNode S) n := by
    rw [← hroot]
    exact (WF_is_node_step1_descendant_move _ _ g.birth.1 n γ).mpr hd
  have hg : gy.birth ∈ (parsedHierarchy Y hY).nodes gy.height :=
    Parser.hierarchy_descendant_mem (parsedHierarchy Y hY) n gy.height _ _ hM hd'
  have hpacket := WF_is_node_step7_packet_match Y hY U n A φ ψ hpattern g hd hg
  have hheight : g.birth.1 + j.val = n := by
    have he := congrArg Sigma.fst ha
    simpa only [CoherentHierarchy.ancestor_height] using he
  let by' := gy.hierarchyBirth (parsedHierarchy Y hY) hg
  have hay : (parsedHierarchy Y hY).ancestor by' j.val = ⟨n, ⟨⟨A, ψ⟩, hM⟩⟩ := by
    have hh : ((parsedHierarchy Y hY).ancestor by' j.val).1 = n := by
      rw [CoherentHierarchy.ancestor_height]
      exact hheight
    apply Sigma.ext hh
    apply (Subtype.heq_iff_coe_eq (fun N => by rw [hh])).mpr
    exact WF_is_node_step4_ancestor_eq (parsedHierarchy Y hY) by' j.val ⟨A, ψ⟩
      (hheight.symm ▸ hM) (hheight.symm ▸ hd')
  have hpresent : (packetOf U P g).mask j := by
    change packetMask P g.incidence (packetOf U P g).head j
    rw [packet_head]
    exact (packet_mask_fn U P g j).mp hmask
  have hy := (calibration_W4_readout Y hY gy hg (packetOf U P g) hpacket j).2 hpresent
  change decode (packetOf U P g) j = some (parsedState Y hY ((parsedHierarchy Y hY).ancestor by' j.val)) at hy
  rw [hay] at hy
  have hs := decode_spec U P g j
  rw [if_pos hmask, ha] at hs
  exact Option.some.inj (hy.symm.trans hs)

/-- Step 8 of the V4 proof of `WF_is_node` (V4 4.8):
"the parent ... is the placed σⁿA whose child of role i is C". A child's full
frame and globally distinct parent role determine the full parent frame. -/
private theorem WF_is_node_step8_parent_from_role {T : Tiling S}
    (H : CoherentHierarchy S T) (n : ℕ) (D N : FramedNode S)
    (hD : D ∈ H.nodes n) (i : S.I N.ty) (he : D = N.child n i)
    (hr : H.nodeRole ⟨n, ⟨D, hD⟩⟩ = ⟨N.ty, i⟩) : N ∈ H.nodes (n + 1) := by
  let parentFrom (r : S.Role) : FramedNode S :=
    ⟨r.1, (S.placeChild n r.2).symm.trans D.frame⟩
  have hactual : parentFrom (H.nodeRole ⟨n, ⟨D, hD⟩⟩) = (H.parent n ⟨D, hD⟩).val := by
    apply FramedNode.ext
    · rfl
    · have hc := congrArg FramedNode.frame (H.child_eq n ⟨D, hD⟩)
      change (S.placeChild n (H.role n ⟨D, hD⟩)).symm.trans D.frame = _
      rw [hc]
      ext x : 1
      exact congrArg (H.parent n ⟨D, hD⟩).val.frame
        ((S.placeChild n (H.role n ⟨D, hD⟩)).apply_symm_apply x)
  have hproposed : parentFrom ⟨N.ty, i⟩ = N := by
    apply FramedNode.ext
    · rfl
    · change (S.placeChild n i).symm.trans D.frame = N.frame
      rw [he]
      ext x : 1
      exact congrArg N.frame ((S.placeChild n i).apply_symm_apply x)
  rw [hr, hproposed] at hactual
  exact hactual.symm ▸ (H.parent n ⟨D, hD⟩).property

/-- Step 8 of the V4 proof of `WF_is_node` (V4 4.8):
"By induction ... a node ... with frame ψ ∘ χᵢ". Recognition of one child,
its readable state, and its first address letter force the proposed parent. -/
private theorem WF_is_node_step8_recognize (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (n : ℕ) (U : HonestSource S) (A : S.ι) (φ ψ : Iso d)
    (hN : (⟨A, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n)
    (hpattern : normalisedPattern Y n A ψ = normalisedPattern (honestLift C U) n A φ) :
    (⟨A, ψ⟩ : FramedNode S) ∈ (parsedHierarchy Y hY).nodes n := by
  induction n generalizing A φ ψ with
  | zero => exact WF_is_node_step4_low Y hY U 0 (Nat.zero_le _) A φ ψ hN hpattern
  | succ n ih =>
    by_cases hn : n + 1 ≤ P.K
    · exact WF_is_node_step4_low Y hY U (n + 1) hn A φ ψ hN hpattern
    · have hnK : P.K ≤ n := by omega
      obtain ⟨i⟩ := Parser.roles_nonempty A
      have hchild := U.hierarchy.children_mem n ⟨A, φ⟩ hN i
      have hp := WF_is_node_step5_child_pattern Y U n A φ ψ i hpattern
      have hm := ih (S.child A i).ty ((S.placeChild n i).trans φ)
        ((S.placeChild n i).trans ψ) hchild hp
      have hs := WF_is_node_step7_state_match Y hY U n hnK (S.child A i).ty
        ((S.placeChild n i).trans φ) ((S.placeChild n i).trans ψ) hchild hm hp
      have hr : (parsedHierarchy Y hY).nodeRole
          ⟨n, ⟨(⟨A, ψ⟩ : FramedNode S).child n i, hm⟩⟩ = (⟨A, i⟩ : S.Role) := by
        rw [← parsedState_role]
        have haddress := congrArg (fun s : State P => s.address ⟨0, P.k_pos⟩) hs
        exact haddress.trans (WF_is_node_step1_role_of_child U.hierarchy n _
          ⟨A, φ⟩ hchild hN i rfl)
      exact WF_is_node_step8_parent_from_role (parsedHierarchy Y hY) n _ ⟨A, ψ⟩ hm i rfl hr

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
  obtain ⟨U, φ, hN, hqU⟩ := hq
  have hM := WF_is_node_step8_recognize Y hY n U A φ ψ hN (hpattern.trans hqU)
  refine ⟨hM, ?_⟩
  intro V χ hV _
  exact WF_is_node_step2_inner V.hierarchy (parsedHierarchy Y hY) n A χ ψ hV hM

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
