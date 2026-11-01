import Enforce.Source.Routing
import Enforce.Rules

/-!
# Finite descent saturation and a translated-witness section

The descent lemma is independent of substitution geometry. Children are ordered
actual nodes, and their list of states is exactly the list prescribed by `D`.
The section lemma concerns all honest sources and arbitrary translation-covariant
markings. No equivariance of the resulting section is asserted.
C3, V4 1.28, is already in `Substitution.lean` and is reused unchanged.
-/

open Set

noncomputable section

namespace Enforce

universe u v

/-- C1, V4 1.26: a state set is forward closed under the prescribed lists. -/
def ForwardClosed {α : Type u} (D : α → List α) (B : Set α) : Prop :=
  ∀ a ∈ B, ∀ b ∈ D a, b ∈ B

/-- C1, V4 1.26: a forest with a parent above every node and the exact ordered
children prescribed by each positive-level node's state. Repeated states in `D`
are permitted; the actual child nodes are distinct. -/
structure DescentForest (α : Type u) (D : α → List α) where
  /-- C1, V4 1.26: actual forest nodes, with no finiteness hypothesis. -/
  Node : Type v
  /-- C1, V4 1.26: nonnegative levels. -/
  level : Node → ℕ
  /-- C1, V4 1.26: parent at the next higher level. -/
  parent : Node → Node
  /-- C1, V4 1.26: parent increases the level by one. -/
  parent_level : ∀ x, level (parent x) = level x + 1
  /-- C1, V4 1.26: state of each actual node. -/
  state : Node → α
  /-- C1, V4 1.26: ordered actual child list. -/
  children : Node → List Node
  /-- C1, V4 1.26: each actual child occurs once, even if child states repeat. -/
  children_nodup : ∀ x, (children x).Nodup
  /-- C1, V4 1.26: children are one level below their parent. -/
  child_level : ∀ x y, y ∈ children x → level x = level y + 1
  /-- C1, V4 1.26: every node occurs in the list of its parent. -/
  mem_parent : ∀ x, x ∈ children (parent x)
  /-- C1, V4 1.26: children have the stated unique parent. -/
  child_parent : ∀ x y, y ∈ children x → parent y = x
  /-- C1, V4 1.26: exact order and multiplicity of prescribed child states. -/
  prescribed : ∀ x, 1 ≤ level x → (children x).map state = D (state x)

/-- C1, V4 8.2: the paper's increasing rank sets `B₀ = B`,
`Bᵣ₊₁ = {a | every prescribed child lies in Bᵣ}`. -/
def rankSets {α : Type u} (D : α → List α) (B : Set α) : ℕ → Set α
  | 0 => B
  | r + 1 => {a | ∀ b ∈ D a, b ∈ rankSets D B r}

/-- C1, V4 8.2, first rank lemma: forward closure makes the rank sets increasing,
and a finite state space makes them stabilize at one finite rank. -/
theorem rankSets_mono_stabilizes {α : Type u} [Finite α] (D : α → List α)
    (B : Set α) (hB : ForwardClosed D B) :
    (∀ r, rankSets D B r ⊆ rankSets D B (r + 1)) ∧
      ∃ R : ℕ, ∀ r : ℕ, R ≤ r → rankSets D B r = rankSets D B R := by
  classical
  have hmono : ∀ r, rankSets D B r ⊆ rankSets D B (r + 1) := by
    intro r
    induction r with
    | zero => exact hB
    | succ r ih =>
      intro a ha b hb
      exact ih (ha b hb)
  have hfixed : ∃ R, rankSets D B R = rankSets D B (R + 1) := by
    by_contra h
    have hstrict : StrictMono (rankSets D B) := by
      apply strictMono_nat_of_lt_succ
      intro r
      apply lt_of_le_of_ne (hmono r)
      intro heq
      exact h ⟨r, heq⟩
    exact not_injective_infinite_finite (rankSets D B) hstrict.injective
  obtain ⟨R, hR⟩ := hfixed
  refine ⟨hmono, R, ?_⟩
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => rfl
  | succ r hr ih =>
    calc
      rankSets D B (r + 1) = rankSets D B (R + 1) :=
        congrArg (fun T : Set α => {a | ∀ b ∈ D a, b ∈ T}) ih
      _ = rankSets D B R := hR.symm

/-- C1, V4 8.2, second rank lemma: induction on the actual forest level puts
every occurring state in its level's rank set. This uses exact prescribed children. -/
theorem forest_state_mem_rankSet {α : Type u} (D : α → List α) (B : Set α)
    (F : DescentForest.{u, v} α D)
    (ground : ∀ x, F.level x = 0 → F.state x ∈ B) (x : F.Node) :
    F.state x ∈ rankSets D B (F.level x) := by
  generalize h_lvl : F.level x = l
  induction' l with l ih generalizing x
  · exact ground x h_lvl
  · dsimp [rankSets]
    intro b hb
    have h_presc := F.prescribed x (by omega)
    rw [← h_presc] at hb
    rcases List.mem_map.mp hb with ⟨y, hy_mem, hy_eq⟩
    subst hy_eq
    have h_lvl_child := F.child_level x y hy_mem
    have h_lvl_y : F.level y = l := by omega
    exact ih y h_lvl_y

/-- C1, V4 8.2: rank of a state known to occur in the union of the rank sets.
The least index is a genuine `Nat.find` definition, with explicit existence. -/
def descentRank {α : Type u} (D : α → List α) (B : Set α) (a : α)
    (ha : ∃ r, a ∈ rankSets D B r) : ℕ := by
  classical
  exact Nat.find ha

/-- C1, V4 8.2: rank membership and minimality of the chosen index. -/
theorem descentRank_spec {α : Type u} (D : α → List α) (B : Set α) (a : α)
    (ha : ∃ r, a ∈ rankSets D B r) :
    a ∈ rankSets D B (descentRank D B a ha) ∧
      ∀ r, a ∈ rankSets D B r → descentRank D B a ha ≤ r := by
  classical
  exact ⟨Nat.find_spec ha, fun _ hr => Nat.find_min' ha hr⟩

/-- C1, V4 8.2: finite-state ranks have a common bound. The finite state space
may be empty; rank existence is only requested for elements of its rank-set union. -/
theorem descentRank_bounded {α : Type u} [Finite α] (D : α → List α)
    (B : Set α) (hB : ForwardClosed D B) :
    ∃ R : ℕ, ∀ (a : α) (ha : ∃ r, a ∈ rankSets D B r),
      descentRank D B a ha ≤ R := by
  obtain ⟨h_mono, ⟨R, h_stab⟩⟩ := rankSets_mono_stabilizes D B hB
  use R
  intro a ha
  have hR : a ∈ rankSets D B R := by
    obtain ⟨r, hr⟩ := ha
    by_cases h : r ≤ R
    · induction' k : R - r with n ih generalizing r
      · have : r = R := by omega
        subst this
        exact hr
      · have h_le : r + 1 ≤ R := by omega
        have hr_next : a ∈ rankSets D B (r + 1) := h_mono r hr
        have h_k_next : R - (r + 1) = n := by omega
        exact ih (r + 1) hr_next h_le h_k_next
    · have heq := h_stab r (by omega)
      rwa [heq] at hr
  exact (descentRank_spec D B a ha).2 R hR

/-- C1, V4 8.2: a bad node has a bad parent of strictly larger rank.
Together with bounded ranks this rules out an infinite chain of bad ancestors. -/
theorem bad_parent_rank_increases {α : Type u} (D : α → List α) (B : Set α)
    (hB : ForwardClosed D B) (F : DescentForest.{u, v} α D)
    (ground : ∀ x, F.level x = 0 → F.state x ∈ B) (x : F.Node)
    (hx : F.state x ∉ B)
    (ha : ∃ r, F.state x ∈ rankSets D B r)
    (hp : ∃ r, F.state (F.parent x) ∈ rankSets D B r) :
    F.state (F.parent x) ∉ B ∧
      descentRank D B (F.state x) ha + 1 ≤
        descentRank D B (F.state (F.parent x)) hp := by
  have h_child_in_D : F.state x ∈ D (F.state (F.parent x)) := by
    have h1 := F.mem_parent x
    have h_level : 1 ≤ F.level (F.parent x) := by
      rw [F.parent_level x]
      exact Nat.le_add_left 1 (F.level x)
    have h_presc := F.prescribed (F.parent x) h_level
    have h_mem_map : F.state x ∈ List.map F.state (F.children (F.parent x)) := by
      apply List.mem_map_of_mem
      exact h1
    rw [h_presc] at h_mem_map
    exact h_mem_map
  constructor
  · intro hp_in_B
    have h_child_in_B := hB (F.state (F.parent x)) hp_in_B (F.state x) h_child_in_D
    exact hx h_child_in_B
  · have hp_prop := (descentRank_spec D B (F.state (F.parent x)) hp).1
    generalize h_hp_rank : descentRank D B (F.state (F.parent x)) hp = hp_rank
    rw [h_hp_rank] at hp_prop
    cases hp_rank with
    | zero =>
      have hp_in_B : F.state (F.parent x) ∈ B := hp_prop
      have h_child_in_B := hB (F.state (F.parent x)) hp_in_B (F.state x) h_child_in_D
      exact (hx h_child_in_B).elim
    | succ r =>
      have h_child_in_rank : F.state x ∈ rankSets D B r := by
        exact hp_prop (F.state x) h_child_in_D
      have h_child_rank_le : descentRank D B (F.state x) ha ≤ r := by
        exact (descentRank_spec D B (F.state x) ha).2 r h_child_in_rank
      have h_ineq : descentRank D B (F.state x) ha + 1 ≤ r + 1 := Nat.add_le_add_right h_child_rank_le 1
      exact h_hp_rank ▸ h_ineq

/-- C1, V4 1.26, rank proof V4 8.2: finite descent saturation, abstract over
all finite alphabets, nonempty ordered transition lists, forward-closed sets, and
actual forests. No geometric or substitution hypothesis is used. -/
theorem descent_saturation {α : Type u} [Finite α] (D : α → List α)
    (nonempty : ∀ a, D a ≠ []) (B : Set α) (hB : ForwardClosed D B)
    (F : DescentForest.{u, v} α D)
    (ground : ∀ x, F.level x = 0 → F.state x ∈ B) :
    ∀ x : F.Node, F.state x ∈ B := by
  obtain ⟨R, hR⟩ := descentRank_bounded D B hB
  intro x
  by_contra hx
  have H : ∀ k y, R - descentRank D B (F.state y) ⟨F.level y, forest_state_mem_rankSet D B F ground y⟩ = k → F.state y ∉ B → False := by
    intro k
    induction' k using Nat.strong_induction_on with k ih
    intro y hk hy
    have ha_y : ∃ r, F.state y ∈ rankSets D B r := ⟨F.level y, forest_state_mem_rankSet D B F ground y⟩
    have hp_y : ∃ r, F.state (F.parent y) ∈ rankSets D B r := ⟨F.level (F.parent y), forest_state_mem_rankSet D B F ground (F.parent y)⟩
    have ⟨hp_bad, h_inc⟩ := bad_parent_rank_increases D B hB F ground y hy ha_y hp_y
    have h_bound_y := hR (F.state y) ha_y
    have h_bound_py := hR (F.state (F.parent y)) hp_y
    have h_diff_py_lt_y : R - descentRank D B (F.state (F.parent y)) hp_y < R - descentRank D B (F.state y) ha_y := by
      omega
    apply ih (R - descentRank D B (F.state (F.parent y)) hp_y)
    · rw [← hk]
      exact h_diff_py_lt_y
    · rfl
    · exact hp_bad
  exact H (R - descentRank D B (F.state x) ⟨F.level x, forest_state_mem_rankSet D B F ground x⟩) x rfl hx

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

/-- C2, V4 1.27: the Euclidean translation by an arbitrary vector. -/
def translation (v : E d) : Iso d := AffineIsometryEquiv.vaddConst ℝ v

/-- C2, V4 1.27: exact transport of an honest source under translation.
Full framed node sets, parents, roles and the frame-coset representative are retained. -/
structure TranslatedSource (U V : HonestSource S) (v : E d) : Prop where
  /-- C2, V4 1.27: the precise translated physical tiling. -/
  tiling : V.tiling = U.tiling.move (translation v)
  /-- C2, V4 1.27: all hierarchy nodes with their translated frames. -/
  nodes : ∀ n, V.hierarchy.nodes n =
    (fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes n
  /-- C2, V4 1.27: translations preserve the chosen orthogonal coset representative. -/
  coset : V.coset = U.coset
  /-- C2, V4 1.27: actual parent maps commute with the translation. -/
  parents : ∀ n (N : {N // N ∈ U.hierarchy.nodes n})
    (hN : N.val.move (translation v) ∈ V.hierarchy.nodes n),
    (V.hierarchy.parent n ⟨N.val.move (translation v), hN⟩).val =
      (U.hierarchy.parent n N).val.move (translation v)
  /-- C2, V4 1.27: both the parent type and its child role are unchanged. -/
  roles : ∀ n (N : {N // N ∈ U.hierarchy.nodes n})
    (hN : N.val.move (translation v) ∈ V.hierarchy.nodes n),
    V.hierarchy.nodeRole ⟨n, ⟨N.val.move (translation v), hN⟩⟩ =
      U.hierarchy.nodeRole ⟨n, N⟩

/-- Step 1 of the V4 proof of `honest_translate_exists` (V4 1.27):
the translated physical tiling is legal. -/
private lemma honest_translate_exists_step1_tiling_mem_species (U : HonestSource S) (v : E d) :
    U.tiling.move (translation v) ∈ S.Species := by
  rw [Enforce.species_move_iff]
  exact U.mem_species

open private exists_honest_step7_move_toTile exists_honest_step7_node_move_carrier from Enforce.Tiling in
/-- Step 1 of the V4 proof of `honest_translate_exists_step2_translated_hierarchy` (V4 1.27):
translated nodes generate the translated ground tiles natively. -/
private lemma honest_translate_exists_step2_translated_hierarchy_step1_tiles (U : HonestSource S) (v : E d) :
  ({t | ∃ N ∈ (fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes 0, N.toTile = t} = (U.tiling.move (translation v)).tiles) ∧
  (∀ n N, N ∈ (fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes n →
    {t | t ∈ (U.tiling.move (translation v)).tiles ∧ t.carrier ⊆ N.carrier n} =
      {t | ∃ w : S.RoleWord N.ty n, ((S.nativeTile N.ty n w).move N.frame).toTile = t}) := by
  constructor
  · ext t
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨N, ⟨M, hM, rfl⟩, rfl⟩
      have h := U.hierarchy.ground
      rw [exists_honest_step7_move_toTile M (translation v)]
      have h1 : M.toTile ∈ U.tiling.tiles := by
        rw [← h]
        exact ⟨M, hM, rfl⟩
      exact ⟨M.toTile, h1, rfl⟩
    · rintro ⟨t', ht', rfl⟩
      have h := U.hierarchy.ground
      rw [← h] at ht'
      rcases ht' with ⟨M, hM, rfl⟩
      refine ⟨M.move (translation v), ⟨M, hM, rfl⟩, ?_⟩
      rw [exists_honest_step7_move_toTile M (translation v)]
  · intro n N hN
    rcases hN with ⟨M, hM, rfl⟩
    let ψ : Iso d := translation v
    have he (w : S.RoleWord M.ty n) :
        ((S.nativeTile (M.move ψ).ty n w).move
          (M.move ψ).frame).toTile =
        ((S.nativeTile M.ty n w).move M.frame).toTile.move ψ :=
      exists_honest_step7_move_toTile
        ((S.nativeTile M.ty n w).move M.frame) ψ
    apply Set.ext
    intro t
    change (t ∈ (fun u : PlacedTile S => u.move ψ) ''
      U.tiling.tiles ∧ t.carrier ⊆ (M.move ψ).carrier n) ↔ _
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hsub⟩
      have hs : u.carrier ⊆ M.carrier n := by
        apply (Set.image_subset_image_iff ψ.injective).mp
        simpa only [PlacedTile.move_carrier,
          exists_honest_step7_node_move_carrier] using hsub
      have hn : ∃ w : S.RoleWord M.ty n,
          ((S.nativeTile M.ty n w).move M.frame).toTile = u :=
        (Set.ext_iff.mp (U.hierarchy.native_tiles n M hM) u).mp
          ⟨hu, hs⟩
      obtain ⟨w, hw⟩ := hn
      exact ⟨w, (he w).trans
        (congrArg (fun u : PlacedTile S => u.move ψ) hw)⟩
    · rintro ⟨w, rfl⟩
      rw [he w]
      let u := ((S.nativeTile M.ty n w).move M.frame).toTile
      have hu : u ∈ U.tiling.tiles ∧ u.carrier ⊆ M.carrier n :=
        (Set.ext_iff.mp (U.hierarchy.native_tiles n M hM) u).mpr
          ⟨w, rfl⟩
      refine ⟨⟨u, hu.1, rfl⟩, ?_⟩
      simpa only [PlacedTile.move_carrier,
        exists_honest_step7_node_move_carrier] using
        (Set.image_mono hu.2 : ψ '' u.carrier ⊆ ψ '' M.carrier n)

/-- Step 2 of the V4 proof of `honest_translate_exists_step2_translated_hierarchy` (V4 1.27):
translated nodes cover the space and have disjoint interiors. -/
private lemma honest_translate_exists_step2_translated_hierarchy_step2_cover (U : HonestSource S) (v : E d) :
  (∀ n x, ∃ N ∈ (fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes n, x ∈ N.carrier n) ∧
  (∀ n, ((fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes n).PairwiseDisjoint (fun N => interior (N.carrier n))) := by
  constructor
  · intro n x
    obtain ⟨N, hN_mem, hN_x⟩ := U.hierarchy.cover n ((translation v).symm x)
    use N.move (translation v)
    constructor
    · exact Set.mem_image_of_mem _ hN_mem
    · dsimp [FramedNode.carrier, FramedNode.move, placedSet] at hN_x ⊢
      obtain ⟨y, hy, heq⟩ := hN_x
      use y
      refine ⟨hy, ?_⟩
      dsimp
      rw [heq]
      exact AffineIsometryEquiv.apply_symm_apply _ _
  · intro n N₁ hN₁ N₂ hN₂ h_neq
    obtain ⟨M₁, hM₁_mem, rfl⟩ := hN₁
    obtain ⟨M₂, hM₂_mem, rfl⟩ := hN₂
    dsimp [FramedNode.carrier, FramedNode.move, placedSet]
    have h_disj := U.hierarchy.disjoint n hM₁_mem hM₂_mem (by
      intro h
      apply h_neq
      rw [h])
    dsimp [FramedNode.carrier, placedSet] at h_disj
    have himg : ∀ M : FramedNode S, interior ((translation v) ∘ M.frame '' S.supertile n M.ty) = (translation v) '' interior (M.frame '' S.supertile n M.ty) := by
      intro M
      rw [Set.image_comp]
      exact (Homeomorph.image_interior (translation v).toHomeomorph _).symm
    change Disjoint (interior ((translation v) ∘ M₁.frame '' S.supertile n M₁.ty)) (interior ((translation v) ∘ M₂.frame '' S.supertile n M₂.ty))
    rw [himg M₁, himg M₂]
    exact Set.disjoint_image_of_injective (translation v).injective h_disj

private lemma honest_translate_exists_step2_translated_hierarchy_step3_tree_move_inj (g : Iso d) :
    Function.Injective (fun N : FramedNode S => N.move g) := by
  intro ⟨N_ty, N_frame⟩ ⟨M_ty, M_frame⟩ h
  dsimp [FramedNode.move] at h
  injection h with h1 h2
  subst h1
  congr
  ext1 x
  have hh : (N_frame.trans g) x = (M_frame.trans g) x := by rw [h2]
  exact EquivLike.injective g hh

private lemma honest_translate_exists_step2_translated_hierarchy_step3_tree_child_move (M : FramedNode S) (n : ℕ) (i : S.I M.ty) (g : Iso d) :
    (M.child n i).move g = (M.move g).child n i := by
  cases M
  rfl

/-- Step 3 of the V4 proof of `honest_translate_exists_step2_translated_hierarchy` (V4 1.27):
translated tree structure is coherent. -/
private lemma honest_translate_exists_step2_translated_hierarchy_step3_tree (U : HonestSource S) (v : E d) :
  ∃ (parent : ∀ n, {N // N ∈ (fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes n} → {P // P ∈ (fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes (n + 1)})
    (role : ∀ n N, S.I (parent n N).val.ty),
      (∀ n N, N.val = (parent n N).val.child n (role n N)) ∧
      (∀ n P, P ∈ (fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes (n + 1) → ∀ i : S.I P.ty, P.child n i ∈ (fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes n) ∧
      (∀ n N P, P ∈ (fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes (n + 1) → (∃ i : S.I P.ty, N.val = P.child n i) → P = (parent n N).val) ∧
      (∀ n (N : {N // N ∈ U.hierarchy.nodes n}) (hN : N.val.move (translation v) ∈ (fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes n),
        (parent n ⟨N.val.move (translation v), hN⟩).val = (U.hierarchy.parent n N).val.move (translation v)) ∧
      (∀ n (N : {N // N ∈ U.hierarchy.nodes n}) (hN : N.val.move (translation v) ∈ (fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes n),
        (⟨(parent n ⟨N.val.move (translation v), hN⟩).val.ty, role n ⟨N.val.move (translation v), hN⟩⟩ : S.Role) = U.hierarchy.nodeRole ⟨n, N⟩) := by
  let g := translation v
  let nodes' := fun n => (fun N : FramedNode S => N.move g) '' U.hierarchy.nodes n
  have hpull : ∀ n (N' : {N // N ∈ nodes' n}), ∃! N, N ∈ U.hierarchy.nodes n ∧ N.move g = N'.val := by
    intro n N'
    rcases N'.2 with ⟨N, hN1, hN2⟩
    use N
    refine ⟨⟨hN1, hN2⟩, ?_⟩
    intro M hM
    exact honest_translate_exists_step2_translated_hierarchy_step3_tree_move_inj g (hM.2.trans hN2.symm)
  let pull : ∀ n, {N // N ∈ nodes' n} → {N // N ∈ U.hierarchy.nodes n} := fun n N' =>
    ⟨Classical.choose (hpull n N'), (Classical.choose_spec (hpull n N')).1.1⟩
  have hpull_spec : ∀ n (N' : {N // N ∈ nodes' n}), (pull n N').val.move g = N'.val := fun n N' =>
    (Classical.choose_spec (hpull n N')).1.2
  let parent' : ∀ n, {N // N ∈ nodes' n} → {P // P ∈ nodes' (n + 1)} := fun n N' =>
    ⟨(U.hierarchy.parent n (pull n N')).val.move g, Set.mem_image_of_mem _ (U.hierarchy.parent n (pull n N')).2⟩
  let role' : ∀ n (N' : {N // N ∈ nodes' n}), S.I (parent' n N').val.ty := fun n N' =>
    U.hierarchy.role n (pull n N')
  use parent', role'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n N'
    have hN' : N'.val = (pull n N').val.move g := (hpull_spec n N').symm
    rw [hN']
    have hc := U.hierarchy.child_eq n (pull n N')
    rw [hc, honest_translate_exists_step2_translated_hierarchy_step3_tree_child_move]
  · intro n P' hP'
    have hP'_eq : P' = (pull (n + 1) ⟨P', hP'⟩).val.move g := (hpull_spec (n + 1) ⟨P', hP'⟩).symm
    rw [hP'_eq]
    intro i
    rw [← honest_translate_exists_step2_translated_hierarchy_step3_tree_child_move]
    exact Set.mem_image_of_mem _ (U.hierarchy.children_mem n (pull (n + 1) ⟨P', hP'⟩) (pull (n + 1) ⟨P', hP'⟩).2 i)
  · intro n N' P' hP'
    have hP : P' = (pull (n + 1) ⟨P', hP'⟩).val.move g := (hpull_spec (n + 1) ⟨P', hP'⟩).symm
    have hN : N'.val = (pull n N').val.move g := (hpull_spec n N').symm
    rw [hP, hN]
    rintro ⟨i, hi⟩
    rw [← honest_translate_exists_step2_translated_hierarchy_step3_tree_child_move] at hi
    have h_inj := honest_translate_exists_step2_translated_hierarchy_step3_tree_move_inj g hi
    have h_parent := U.hierarchy.parent_unique n (pull n N') (pull (n + 1) ⟨P', hP'⟩) (pull (n + 1) ⟨P', hP'⟩).2 ⟨i, h_inj⟩
    rw [h_parent]
  · intro n N hN
    have h_pull : (pull n ⟨N.val.move g, hN⟩).val = N.val := by
      have h1 := hpull_spec n ⟨N.val.move g, hN⟩
      exact honest_translate_exists_step2_translated_hierarchy_step3_tree_move_inj g h1
    have h_eq : pull n ⟨N.val.move g, hN⟩ = N := Subtype.ext h_pull
    dsimp [parent']
    congr 1
    rw [h_eq]
  · intro n N hN
    have h_pull : (pull n ⟨N.val.move g, hN⟩).val = N.val := by
      have h1 := hpull_spec n ⟨N.val.move g, hN⟩
      exact honest_translate_exists_step2_translated_hierarchy_step3_tree_move_inj g h1
    have h_eq : pull n ⟨N.val.move g, hN⟩ = N := Subtype.ext h_pull
    dsimp [role', parent']
    have hr : U.hierarchy.nodeRole ⟨n, N⟩ = ⟨(U.hierarchy.parent n N).val.ty, U.hierarchy.role n N⟩ := rfl
    rw [hr]
    rw [h_eq]
    rfl

/-- Step 2 of the V4 proof of `honest_translate_exists` (V4 1.27):
the translated hierarchy is coherent. We state this as the existence of a coherent hierarchy
whose nodes, parents, and roles are exactly the translations of the original hierarchy's. -/
private lemma honest_translate_exists_step2_translated_hierarchy (U : HonestSource S) (v : E d) :
    ∃ H : CoherentHierarchy S (U.tiling.move (translation v)),
      (∀ n, H.nodes n = (fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes n) ∧
      (∀ n (N : {N // N ∈ U.hierarchy.nodes n}) (hN : N.val.move (translation v) ∈ H.nodes n),
        (H.parent n ⟨N.val.move (translation v), hN⟩).val = (U.hierarchy.parent n N).val.move (translation v)) ∧
      (∀ n (N : {N // N ∈ U.hierarchy.nodes n}) (hN : N.val.move (translation v) ∈ H.nodes n),
        H.nodeRole ⟨n, ⟨N.val.move (translation v), hN⟩⟩ = U.hierarchy.nodeRole ⟨n, N⟩) := by
  have h1 := honest_translate_exists_step2_translated_hierarchy_step1_tiles U v
  have h2 := honest_translate_exists_step2_translated_hierarchy_step2_cover U v
  obtain ⟨parent, role, h_child, h_mem, h_uniq, h_parent, h_role⟩ :=
    honest_translate_exists_step2_translated_hierarchy_step3_tree U v
  let nodes := fun n => (fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes n
  have h_ground : {t | ∃ N ∈ nodes 0, N.toTile = t} = (U.tiling.move (translation v)).tiles := h1.1
  have h_cover : ∀ n x, ∃ N ∈ nodes n, x ∈ N.carrier n := h2.1
  have h_disjoint : ∀ n, (nodes n).PairwiseDisjoint (fun N => interior (N.carrier n)) := h2.2
  have h_native : ∀ n N, N ∈ nodes n →
    {t | t ∈ (U.tiling.move (translation v)).tiles ∧ t.carrier ⊆ N.carrier n} =
      {t | ∃ w : S.RoleWord N.ty n, ((S.nativeTile N.ty n w).move N.frame).toTile = t} := h1.2
  let H : CoherentHierarchy S (U.tiling.move (translation v)) := {
    nodes := nodes
    ground := h_ground
    cover := h_cover
    disjoint := h_disjoint
    parent := parent
    role := role
    child_eq := h_child
    children_mem := h_mem
    parent_unique := h_uniq
    native_tiles := h_native
  }
  use H
  refine ⟨fun _ => rfl, h_parent, ?_⟩
  intro n N hN
  exact h_role n N hN

/-- Step 3 of the V4 proof of `honest_translate_exists` (V4 1.27):
the translated hierarchy has legal contexts for all finite sets of nodes. -/
private lemma honest_translate_exists_step3_contexts (U : HonestSource S) (v : E d)
    (H : CoherentHierarchy S (U.tiling.move (translation v)))
    (hnodes : ∀ n, H.nodes n = (fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes n)
    (hparents : ∀ n (N : {N // N ∈ U.hierarchy.nodes n}) (hN : N.val.move (translation v) ∈ H.nodes n),
      (H.parent n ⟨N.val.move (translation v), hN⟩).val = (U.hierarchy.parent n N).val.move (translation v))
    (hroles : ∀ n (N : {N // N ∈ U.hierarchy.nodes n}) (hN : N.val.move (translation v) ∈ H.nodes n),
      H.nodeRole ⟨n, ⟨N.val.move (translation v), hN⟩⟩ = U.hierarchy.nodeRole ⟨n, N⟩) :
    ∀ F : Finset H.Node, Nonempty (LegalContext H F) :=
  sorry

/-- Step 4 of the V4 proof of `honest_translate_exists` (V4 1.27):
the translated nodes have frames in the same coset. -/
private lemma honest_translate_exists_step4_coset (U : HonestSource S) (v : E d)
    (H : CoherentHierarchy S (U.tiling.move (translation v)))
    (hnodes : ∀ n, H.nodes n = (fun N : FramedNode S => N.move (translation v)) '' U.hierarchy.nodes n) :
    ∀ n N, N ∈ H.nodes n → ∃ R ∈ S.rotGroup, N.frame.linearIsometryEquiv = U.coset * R := by
  intro n N hN
  rw [hnodes n] at hN
  obtain ⟨M, hM, rfl⟩ := hN
  have H_coset := U.frames_in_coset n M hM
  obtain ⟨R, hR, H'⟩ := H_coset
  use R, hR
  dsimp [FramedNode.move]
  have H_trans : (AffineIsometryEquiv.trans M.frame (translation v)).linearIsometryEquiv = (translation v).linearIsometryEquiv * M.frame.linearIsometryEquiv := rfl
  rw [H_trans]
  have H_trans2 : (translation v).linearIsometryEquiv = 1 := by
    dsimp [translation]
    ext x
    rfl
  rw [H_trans2]
  rw [one_mul]
  exact H'

/-- C2, V4 1.27, 1.11: honest sources are closed under translation.
Existence follows by translating the actual hierarchy and every finite legal context. -/

theorem honest_translate_exists (U : HonestSource S) (v : E d) :
    ∃ V : HonestSource S, TranslatedSource U V v := by
  have h1 := honest_translate_exists_step1_tiling_mem_species U v
  obtain ⟨H, hnodes, hparents, hroles⟩ := honest_translate_exists_step2_translated_hierarchy U v
  have h3 := honest_translate_exists_step3_contexts U v H hnodes hparents hroles
  have h4 := honest_translate_exists_step4_coset U v H hnodes
  let V : HonestSource S := {
    tiling := U.tiling.move (translation v)
    mem_species := h1
    hierarchy := H
    contexts := h3
    coset := U.coset
    frames_in_coset := h4
  }
  use V
  exact ⟨rfl, hnodes, rfl, hparents, hroles⟩

/-- C2, V4 1.27: translate an honest source, using the exact transport lemma. -/
def HonestSource.translate (U : HonestSource S) (v : E d) : HonestSource S :=
  Classical.choose (honest_translate_exists U v)

/-- C2, V4 1.27: the chosen translated source has the full transported data. -/
theorem HonestSource.translate_spec (U : HonestSource S) (v : E d) :
    TranslatedSource U (U.translate v) v := Classical.choose_spec (honest_translate_exists U v)

/-- C2, V4 1.27: translation covariance of a marking on the entire honest class. -/
def TranslationCovariant {X : Type} (ρ : HonestSource S → E d → X) : Prop :=
  ∀ (U : HonestSource S) (v x : E d), ρ (U.translate v) (x + v) = ρ U x

/-- C2, V4 1.27: the complete normalized restriction of an arbitrary marking. -/
def honestPattern {X : Type} (ρ : HonestSource S → E d → X) (U : HonestSource S)
    (n : ℕ) (A : S.ι) (φ : Iso d) : Pattern S X n A := fun x => ρ U (φ x)

/-- C2, V4 1.27: source language over all honest hierarchies, with no finite
alphabet or locality assumption on the arbitrary marking `ρ`. -/
def honestLanguage {X : Type} (ρ : HonestSource S → E d → X)
    (n : ℕ) (A : S.ι) : Set (Pattern S X n A) :=
  {q | ∃ (U : HonestSource S) (φ : Iso d),
    (⟨A, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n ∧ q = honestPattern ρ U n A φ}

/-- C2, V4 1.27: normalized patterns are unchanged at the translated node. -/
theorem translated_pattern {X : Type} (ρ : HonestSource S → E d → X)
    (hρ : TranslationCovariant ρ) (U : HonestSource S) (v : E d)
    (n : ℕ) (A : S.ι) (φ : Iso d) :
    honestPattern ρ (U.translate v) n A (φ.trans (translation v)) =
      honestPattern ρ U n A φ := by
  ext x
  dsimp [honestPattern]
  have h := hρ U v (φ x)
  exact h

/-- C2, V4 1.27: indexed pattern requests retain both height and type,
even when equal underlying functions occur at different indices. -/
abbrev PatternRequest {X : Type} (ρ : HonestSource S → E d → X) :=
  Σ n : ℕ, Σ A : S.ι, {q // q ∈ honestLanguage ρ n A}

/-- C2, V4 1.27: finite languages make the full request set countable. -/
theorem patternRequests_countable {X : Type} (ρ : HonestSource S → E d → X)
    (hfinite : ∀ n A, (honestLanguage ρ n A).Finite) : Countable (PatternRequest ρ) := by
  have _inst1 : Fintype S.ι := S.types_finite
  have _inst2 : Countable S.ι := inferInstance
  have _inst3 (n A) : Countable {q // q ∈ honestLanguage ρ n A} := (hfinite n A).countable.to_subtype
  exact @instCountableSigma _ _ inferInstance (fun n => @instCountableSigma _ _ _inst2 (fun A => _inst3 n A))

/-- C2, V4 1.27: the translation stabilizer of a physical tiling. -/
def translationStabilizer (T : Tiling S) : Set (E d) :=
  {v | T.move (translation v) = T}

/-- V4 1.27: equality of translates of a nonempty compact carrier forces the
translation vectors to agree ("impossible for a bounded carrier and v ≠ 0").
Maximizing the linear functional in direction `v - w` excludes a nonzero period. -/
private lemma translation_stabilizer_discrete_compact_translates (K : Set (E d)) (hK : IsCompact K)
    (hKne : K.Nonempty) (v w : E d)
    (h : translation v '' K = translation w '' K) : v = w := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hKne
    (f := fun x => inner ℝ (v - w) x) (by fun_prop)
  have hxv : translation v x ∈ translation w '' K := by
    rw [← h]
    exact Set.mem_image_of_mem _ hx
  obtain ⟨y, hy, hyx⟩ := hxv
  have hyx' : y + w = x + v := hyx
  have hy_eq : y = x + (v - w) := by
    rw [← add_sub_assoc, eq_sub_iff_add_eq]
    exact hyx'
  have hle := hmax hy
  dsimp at hle
  rw [hy_eq, inner_add_right] at hle
  have hz : v - w = 0 := real_inner_self_nonpos.mp (by linarith)
  exact sub_eq_zero.mp hz

/-- C2, V4 1.27: bounded full-dimensional tiles force a discrete, countable
translation stabilizer. This is proved from the tiling hypotheses, not assumed. -/
theorem translation_stabilizer_discrete (T : Tiling S) :
    DiscreteTopology (translationStabilizer T) ∧ Countable (translationStabilizer T) := by
  obtain ⟨t, ht, _⟩ := T.cover 0
  have hK : IsCompact t.carrier := by
    rw [t.frame_carrier]
    exact (S.proto t.ty).compact.image t.frame.continuous
  have hne : (interior t.carrier).Nonempty := by
    rw [t.frame_carrier]
    change (interior (t.frame.toHomeomorph '' (S.proto t.ty).carrier)).Nonempty
    rw [← t.frame.toHomeomorph.image_interior]
    exact (S.proto t.ty).interior_nonempty.image _
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hdiscrete : DiscreteTopology (translationStabilizer T) := by
    apply DiscreteTopology.of_forall_le_dist hr
    intro v w hvw
    by_contra! hdist
    apply hvw
    apply Subtype.ext
    have hv : t.move (translation v.val) ∈ T.tiles := by
      have hm : t.move (translation v.val) ∈ (T.move (translation v.val)).tiles :=
        ⟨t, ht, rfl⟩
      rw [v.property] at hm
      exact hm
    have hw : t.move (translation w.val) ∈ T.tiles := by
      have hm : t.move (translation w.val) ∈ (T.move (translation w.val)).tiles :=
        ⟨t, ht, rfl⟩
      rw [w.property] at hm
      exact hm
    have hptv : translation w.val x ∈ interior (t.move (translation v.val)).carrier := by
      rw [PlacedTile.move_carrier]
      change translation w.val x ∈ interior ((translation v.val).toHomeomorph '' t.carrier)
      rw [← (translation v.val).toHomeomorph.image_interior]
      refine ⟨x + (w.val - v.val), hball ?_, ?_⟩
      · simpa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_sub_rev] using hdist
      · change x + (w.val - v.val) + v.val = x + w.val
        abel
    have hptw : translation w.val x ∈ interior (t.move (translation w.val)).carrier := by
      rw [PlacedTile.move_carrier]
      change translation w.val x ∈ interior ((translation w.val).toHomeomorph '' t.carrier)
      rw [← (translation w.val).toHomeomorph.image_interior]
      exact ⟨x, hx, rfl⟩
    have htile : t.move (translation v.val) = t.move (translation w.val) := by
      by_contra hne
      exact Set.disjoint_left.mp (T.disjoint hv hw hne) hptv hptw
    apply translation_stabilizer_discrete_compact_translates t.carrier hK ⟨x, interior_subset hx⟩
    simpa only [PlacedTile.move_carrier] using congrArg PlacedTile.carrier htile
  letI := hdiscrete
  exact ⟨hdiscrete, TopologicalSpace.separableSpace_iff_countable.mp inferInstance⟩

/-- Step 1 of the V4 proof of `translated_witnesses_distinct` (V4 1.27):
translations of physical tilings compose by addition of their vectors. -/
private lemma translated_witnesses_distinct_step1_move_add (T : Tiling S) (v w : E d) :
    (T.move (translation v)).move (translation w) = T.move (translation (v + w)) := by
  have ht : ∀ t : PlacedTile S,
      (t.move (translation v)).move (translation w) = t.move (translation (v + w)) := by
    intro t
    have hg : (fun y : E d => translation w (translation v y)) =
        (fun y => translation (v + w) y) := by
      funext y
      change (y + v) + w = y + (v + w)
      exact add_assoc y v w
    ext x
    · rfl
    · rw [PlacedTile.move_carrier, PlacedTile.move_carrier,
        PlacedTile.move_carrier, Set.image_image, hg]
  obtain ⟨tiles, c, dj⟩ := T
  dsimp [Tiling.move]
  congr 1
  ext t
  simp only [Set.mem_image]
  constructor
  · rintro ⟨u, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, (ht s).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.move (translation v), ⟨s, hs, rfl⟩, ht s⟩

/-- Step 2 of the V4 proof of `translated_witnesses_distinct` (V4 1.27):
"the set of v with T_i + v = T_j is empty or a coset of the stabiliser ...,
hence countable". Subtracting one such vector embeds this set in the stabilizer. -/
private lemma translated_witnesses_distinct_step2_fiber_countable (T U : Tiling S) :
    {v : E d | T.move (translation v) = U}.Countable := by
  classical
  by_cases h : ∃ w : E d, T.move (translation w) = U
  · obtain ⟨w, hw⟩ := h
    have hm : Set.MapsTo (fun v : E d => v - w)
        {v : E d | T.move (translation v) = U} (translationStabilizer U) := by
      intro v hv
      change U.move (translation (v - w)) = U
      rw [← hw, translated_witnesses_distinct_step1_move_add]
      have he : w + (v - w) = v := by abel
      rw [he]
      exact hv.trans hw.symm
    exact hm.countable_of_injOn (by
      intro v _ z _ hvz
      exact sub_left_injective hvz) (translation_stabilizer_discrete U).2
  · have he : {v : E d | T.move (translation v) = U} = ∅ := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hv
      exact h ⟨v, hv⟩
    rw [he]
    exact Set.countable_empty

/-- Step 3 of the V4 proof of `translated_witnesses_distinct` (V4 1.27):
"all but countably many v make T_i + v distinct" from the prescribed tilings.
A line in positive-dimensional Euclidean space supplies uncountably many vectors. -/
private lemma translated_witnesses_distinct_step3_avoid {β : Type} [Countable β]
    (T : Tiling S) (forbidden : β → Tiling S) :
    ∃ v : E d, ∀ j, T.move (translation v) ≠ forbidden j := by
  classical
  have hd : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) Fact.out
  let e : ℝ → E d := fun r => (WithLp.equiv 2 (Fin d → ℝ)).symm (fun _ => r)
  have he : Function.Injective e := by
    intro r s hrs
    exact congrFun (congrArg (WithLp.equiv 2 (Fin d → ℝ)) hrs) ⟨0, hd⟩
  haveI : Uncountable (E d) := he.uncountable
  have hc : (⋃ j, {v : E d | T.move (translation v) = forbidden j}).Countable :=
    Set.countable_iUnion fun j => translated_witnesses_distinct_step2_fiber_countable T (forbidden j)
  have hn : ∃ v : E d, v ∉ ⋃ j, {v : E d | T.move (translation v) = forbidden j} := by
    by_contra h
    push_neg at h
    exact Set.not_countable_univ (hc.mono (fun v _ => h v))
  obtain ⟨v, hv⟩ := hn
  refine ⟨v, ?_⟩
  intro j hj
  exact hv (Set.mem_iUnion.mpr ⟨j, hj⟩)

/-- C2, V4 1.27: any countable family of honest witnesses can be translated
so that their underlying physical tilings are pairwise distinct. Translated sources
exist because the given witnesses are honest; an empty family is harmless. -/
theorem translated_witnesses_distinct {α : Type} [Countable α]
    (witness : α → HonestSource S) :
    ∃ v : α → E d, Function.Injective (fun i => ((witness i).translate (v i)).tiling) := by
  classical
  cases isEmpty_or_nonempty α
  · exact ⟨fun a => isEmptyElim a, fun a => isEmptyElim a⟩
  · obtain ⟨g, hg⟩ := exists_surjective_nat α
    have hchoose (n : ℕ) (previous : ∀ m, m < n → E d) :
        ∃ v : E d, ∀ j : Fin n,
          ((witness (g n)).translate v).tiling ≠
            ((witness (g j)).translate (previous j j.isLt)).tiling := by
      obtain ⟨v, hv⟩ := translated_witnesses_distinct_step3_avoid
        (witness (g n)).tiling
        (fun j : Fin n => ((witness (g j)).translate (previous j j.isLt)).tiling)
      refine ⟨v, ?_⟩
      intro j
      rw [((witness (g n)).translate_spec v).tiling]
      exact hv j
    let step : ∀ n : ℕ, (∀ m, m < n → E d) → E d :=
      fun n previous => Classical.choose (hchoose n previous)
    let v : ℕ → E d := Nat.strongRec' step
    have hv (n : ℕ) : ∀ j : Fin n,
        ((witness (g n)).translate (v n)).tiling ≠
          ((witness (g j)).translate (v j)).tiling := by
      have hs : v n = step n (fun m _ => v m) := Nat.strongRec'_spec step
      rw [hs]
      exact Classical.choose_spec (hchoose n (fun m _ => v m))
    have hinj : Function.Injective (fun n => ((witness (g n)).translate (v n)).tiling) := by
      intro i j hij
      rcases lt_trichotomy i j with h | h | h
      · exact (hv j ⟨i, h⟩ hij.symm).elim
      · exact h
      · exact (hv i ⟨j, h⟩ hij).elim
    choose f hf using hg
    refine ⟨fun a => v (f a), ?_⟩
    intro a b hab
    have h : f a = f b := hinj (by simpa only [hf] using hab)
    exact (hf a).symm.trans ((congrArg g h).trans (hf b))

/-- C2, V4 1.27: the language contributed by one chosen honest source per
species member. The domain is the actual species subtype, including an empty species. -/
def sectionLanguage {X : Type} (ρ : HonestSource S → E d → X)
    (s : S.Species → HonestSource S) (n : ℕ) (A : S.ι) : Set (Pattern S X n A) :=
  {q | ∃ (Z : S.Species) (φ : Iso d),
    (⟨A, φ⟩ : FramedNode S) ∈ (s Z).hierarchy.nodes n ∧
      q = honestPattern ρ (s Z) n A φ}

/-- Step 1 of the V4 proof of `translated_witness_section` (V4 1.27):
"Enumerate the indexed requests (n,A,q) with q ∈ L_n(A) ... and choose witnesses (T_i, H_i) ∈ S
realising ρ_i at a node of the requested height and type". -/
private lemma translated_witness_section_step1_witnesses {X : Type}
    (ρ : HonestSource S → E d → X) :
    ∃ (witness : PatternRequest ρ → HonestSource S) (node : ∀ _i : PatternRequest ρ, Iso d),
      ∀ i, (⟨i.2.1, node i⟩ : FramedNode S) ∈ (witness i).hierarchy.nodes i.1 ∧
        honestPattern ρ (witness i) i.1 i.2.1 (node i) = i.2.2.val := by
  have H : ∀ i : PatternRequest ρ, ∃ U φ, (⟨i.2.1, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes i.1 ∧ i.2.2.val = honestPattern ρ U i.1 i.2.1 φ := by
    intro i
    exact i.2.2.property
  choose witness node hw using H
  refine ⟨witness, node, ?_⟩
  intro i
  exact ⟨(hw i).1, (hw i).2.symm⟩

/-- Step 2 of the V4 proof of `translated_witness_section` (V4 1.27):
"We translate them so that the underlying tilings become pairwise distinct...
Translation covariance means the normalised pattern at the translated node is still q_i". -/
private lemma translated_witness_section_step2_translation {X : Type}
    (ρ : HonestSource S → E d → X)
    (hρ : TranslationCovariant ρ)
    (hfinite : ∀ n A, (honestLanguage ρ n A).Finite)
    (witness : PatternRequest ρ → HonestSource S)
    (node : ∀ _i : PatternRequest ρ, Iso d)
    (hwit : ∀ i, (⟨i.2.1, node i⟩ : FramedNode S) ∈ (witness i).hierarchy.nodes i.1 ∧
      honestPattern ρ (witness i) i.1 i.2.1 (node i) = i.2.2.val) :
    ∃ (witness_trans : PatternRequest ρ → HonestSource S) (node_trans : ∀ _i : PatternRequest ρ, Iso d),
      Function.Injective (fun i => (witness_trans i).tiling) ∧
      ∀ i, (⟨i.2.1, node_trans i⟩ : FramedNode S) ∈ (witness_trans i).hierarchy.nodes i.1 ∧
        honestPattern ρ (witness_trans i) i.1 i.2.1 (node_trans i) = i.2.2.val := by
  have _inst_countable : Countable (PatternRequest ρ) := patternRequests_countable ρ hfinite
  obtain ⟨v, hinj⟩ := translated_witnesses_distinct witness
  let witness_trans i := (witness i).translate (v i)
  let node_trans i := (node i).trans (translation (v i))
  refine ⟨witness_trans, node_trans, hinj, ?_⟩
  intro i
  have ht := (witness i).translate_spec (v i)
  constructor
  · rw [ht.nodes i.1]
    refine ⟨⟨i.2.1, node i⟩, (hwit i).1, ?_⟩
    rfl
  · rw [translated_pattern ρ hρ (witness i) (v i) i.1 i.2.1 (node i)]
    exact (hwit i).2

/-- Step 3 of the V4 proof of `translated_witness_section` (V4 1.27):
"Define s(T_i) = (T_i, H_i) for the (now distinct) T_i, and s(T) arbitrary in S
over T for all other T (Lemma 1.12)". -/
private lemma translated_witness_section_step3_extend {X : Type}
    (ρ : HonestSource S → E d → X)
    (witness_trans : PatternRequest ρ → HonestSource S)
    (hinj : Function.Injective (fun i => (witness_trans i).tiling))
    (node_trans : ∀ _i : PatternRequest ρ, Iso d)
    (h_wit_trans : ∀ i, (⟨i.2.1, node_trans i⟩ : FramedNode S) ∈ (witness_trans i).hierarchy.nodes i.1 ∧
      honestPattern ρ (witness_trans i) i.1 i.2.1 (node_trans i) = i.2.2.val) :
    ∃ s : S.Species → HonestSource S,
      (∀ Z, (s Z).tiling = Z.val) ∧
      ∀ i : PatternRequest ρ,
        (⟨i.2.1, node_trans i⟩ : FramedNode S) ∈ (s ⟨(witness_trans i).tiling, (witness_trans i).mem_species⟩).hierarchy.nodes i.1 ∧
        honestPattern ρ (s ⟨(witness_trans i).tiling, (witness_trans i).mem_species⟩) i.1 i.2.1 (node_trans i) = i.2.2.val := by
  classical
  let s : S.Species → HonestSource S := fun Z =>
    if h : ∃ i, (witness_trans i).tiling = Z.val then
      witness_trans (Classical.choose h)
    else
      Classical.choose (exists_honest Z.val Z.property)
  refine ⟨s, ?_, ?_⟩
  · intro Z
    dsimp [s]
    split_ifs with h
    · exact Classical.choose_spec h
    · exact Classical.choose_spec (exists_honest Z.val Z.property)
  · intro i
    have heq : s ⟨(witness_trans i).tiling, (witness_trans i).mem_species⟩ = witness_trans i := by
      dsimp [s]
      have h : ∃ j, (witness_trans j).tiling = (witness_trans i).tiling := ⟨i, rfl⟩
      rw [dif_pos h]
      have h_inj : Classical.choose h = i := hinj (Classical.choose_spec h)
      rw [h_inj]
    rw [heq]
    exact h_wit_trans i

/-- C2, V4 1.27: there is a section over every source tiling realizing every
pattern of every finite honest language, including height zero. Onto projection
is supplied by stage-1 `exists_honest`; no existence of a species member is assumed.
There is no claim that this section commutes with translations or other isometries. -/
theorem translated_witness_section {X : Type} (ρ : HonestSource S → E d → X)
    (hρ : TranslationCovariant ρ) (hfinite : ∀ n A, (honestLanguage ρ n A).Finite) :
    ∃ s : S.Species → HonestSource S,
      (∀ Z, (s Z).tiling = Z.val) ∧
      (∀ n A, sectionLanguage ρ s n A = honestLanguage ρ n A) ∧
      ∀ n A (q : Pattern S X n A), q ∈ honestLanguage ρ n A →
        ∃ (Z : S.Species) (φ : Iso d),
          (⟨A, φ⟩ : FramedNode S) ∈ (s Z).hierarchy.nodes n ∧
            honestPattern ρ (s Z) n A φ = q := by
  obtain ⟨witness, node, hwit⟩ := translated_witness_section_step1_witnesses ρ
  obtain ⟨witness_trans, node_trans, hinj, hwit_trans⟩ := translated_witness_section_step2_translation ρ hρ hfinite witness node hwit
  obtain ⟨s, hs_tiling, hs_wit⟩ := translated_witness_section_step3_extend ρ witness_trans hinj node_trans hwit_trans
  refine ⟨s, hs_tiling, ?_, ?_⟩
  · intro n A
    ext q
    constructor
    · intro hq
      obtain ⟨Z, φ, hZ, hq_eq⟩ := hq
      dsimp [honestLanguage]
      exact ⟨s Z, φ, hZ, hq_eq⟩
    · intro hq
      let i : PatternRequest ρ := ⟨n, ⟨A, ⟨q, hq⟩⟩⟩
      have hi := hs_wit i
      dsimp [sectionLanguage]
      refine ⟨⟨(witness_trans i).tiling, (witness_trans i).mem_species⟩, node_trans i, hi.1, ?_⟩
      exact hi.2.symm
  · intro n A q hq
    let i : PatternRequest ρ := ⟨n, ⟨A, ⟨q, hq⟩⟩⟩
    have hi := hs_wit i
    refine ⟨⟨(witness_trans i).tiling, (witness_trans i).mem_species⟩, node_trans i, hi.1, ?_⟩
    exact hi.2

/-- Equality of nodes, parent values and full role pairs determines a hierarchy. -/
private theorem unique_hierarchy_ext {T : Tiling S} {H K : CoherentHierarchy S T}
    (hn : H.nodes = K.nodes)
    (hp : ∀ n N (hH : N ∈ H.nodes n) (hK : N ∈ K.nodes n),
      (H.parent n ⟨N, hH⟩).val = (K.parent n ⟨N, hK⟩).val)
    (hr : ∀ n N (hH : N ∈ H.nodes n) (hK : N ∈ K.nodes n),
      H.nodeRole ⟨n, ⟨N, hH⟩⟩ = K.nodeRole ⟨n, ⟨N, hK⟩⟩) : H = K := by
  cases H with
  | mk nodes ground cover disjoint parent role child_eq children_mem parent_unique native_tiles =>
    cases K with
    | mk nodes' ground' cover' disjoint' parent' role' child_eq' children_mem' parent_unique' native_tiles' =>
      dsimp only [CoherentHierarchy.nodeRole] at hn hp hr
      subst nodes'
      have hparent : parent = parent' := by
        funext n N
        exact Subtype.ext (hp n N.val N.property N.property)
      subst parent'
      have hrole : role = role' := by
        funext n N
        exact eq_of_heq (Sigma.mk.inj_iff.mp (hr n N.val N.property N.property)).2
      subst role'
      rfl

/-- C2, V4 1.27: exact translation data determine one honest source, including
the hierarchy parents, child roles, and fixed orthogonal coset representative. -/
theorem TranslatedSource.unique {U V W : HonestSource S} {v : E d}
    (hV : TranslatedSource U V v) (hW : TranslatedSource U W v) : V = W := by
  have ht := hV.tiling.trans hW.tiling.symm
  have hc := hV.coset.trans hW.coset.symm
  have hn : V.hierarchy.nodes = W.hierarchy.nodes := by
    funext n
    exact (hV.nodes n).trans (hW.nodes n).symm
  have hp : ∀ n N (hNV : N ∈ V.hierarchy.nodes n) (hNW : N ∈ W.hierarchy.nodes n),
      (V.hierarchy.parent n ⟨N, hNV⟩).val =
        (W.hierarchy.parent n ⟨N, hNW⟩).val := by
    intro n N hNV hNW
    have hN := hNV
    rw [hV.nodes n] at hN
    obtain ⟨M, hM, rfl⟩ := hN
    exact (hV.parents n ⟨M, hM⟩ hNV).trans (hW.parents n ⟨M, hM⟩ hNW).symm
  have hr : ∀ n N (hNV : N ∈ V.hierarchy.nodes n) (hNW : N ∈ W.hierarchy.nodes n),
      V.hierarchy.nodeRole ⟨n, ⟨N, hNV⟩⟩ =
        W.hierarchy.nodeRole ⟨n, ⟨N, hNW⟩⟩ := by
    intro n N hNV hNW
    have hN := hNV
    rw [hV.nodes n] at hN
    obtain ⟨M, hM, rfl⟩ := hN
    exact (hV.roles n ⟨M, hM⟩ hNV).trans (hW.roles n ⟨M, hM⟩ hNW).symm
  cases V
  cases W
  dsimp only at ht hc hn hp hr
  subst ht
  have hh := unique_hierarchy_ext hn hp hr
  subst hh
  subst hc
  rfl

private lemma translate_zero_identity {d : ℕ} [Fact (2 ≤ d)] :
    translation (0 : E d) = AffineIsometryEquiv.refl ℝ (E d) := by
  ext x
  simp [translation, vadd_eq_add]

private lemma translate_zero_PlacedTile_move_refl {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d} (t : PlacedTile S) :
    t.move (translation 0) = t := by
  rw [translate_zero_identity]
  ext
  · rfl
  · dsimp [PlacedTile.move, PlacedTile.ofFrame]
    have h : t.frame.trans (AffineIsometryEquiv.refl ℝ (E d)) = t.frame := by ext; rfl
    rw [h, ← t.frame_carrier]

private lemma translate_zero_Tiling_move_refl {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d} (T : Tiling S) :
    T.move (translation 0) = T := by
  cases T
  dsimp [Tiling.move]
  congr 1
  have h : (fun t : PlacedTile S => t.move (translation 0)) = id := by
    funext t
    exact translate_zero_PlacedTile_move_refl t
  rw [h, Set.image_id]

private lemma translate_zero_FramedNode_move_refl {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d} (N : FramedNode S) :
    N.move (translation 0) = N := by
  rw [translate_zero_identity]
  cases N
  rfl

/-- Step 1 of the V4 proof of `translate_zero` (V4 1.27): moving tiling by zero is identity. -/
private lemma translate_zero_step1_tiling (U : HonestSource S) :
    U.tiling = U.tiling.move (translation 0) := by
  rw [translate_zero_Tiling_move_refl]

/-- Step 2 of the V4 proof of `translate_zero` (V4 1.27): moving nodes by zero is identity. -/
private lemma translate_zero_step2_nodes (U : HonestSource S) :
    ∀ n, U.hierarchy.nodes n = (fun N : FramedNode S => N.move (translation 0)) '' U.hierarchy.nodes n := by
  intro n
  have h : (fun N : FramedNode S => N.move (translation 0)) = id := by
    funext N
    exact translate_zero_FramedNode_move_refl N
  rw [h, Set.image_id]

/-- Step 3 of the V4 proof of `translate_zero` (V4 1.27): coset is preserved. -/
private lemma translate_zero_step3_coset (U : HonestSource S) :
    U.coset = U.coset := rfl

/-- Step 4 of the V4 proof of `translate_zero` (V4 1.27): parents commute with zero translation. -/
private lemma translate_zero_step4_parents (U : HonestSource S) :
    ∀ n (N : {N // N ∈ U.hierarchy.nodes n})
      (hN : N.val.move (translation 0) ∈ U.hierarchy.nodes n),
      (U.hierarchy.parent n ⟨N.val.move (translation 0), hN⟩).val =
        (U.hierarchy.parent n N).val.move (translation 0) := by
  intro n N hN
  have h : N.val.move (translation 0) = N.val := translate_zero_FramedNode_move_refl N.val
  rw [show (⟨N.val.move (translation 0), hN⟩ : {N // N ∈ U.hierarchy.nodes n}) = N from Subtype.ext h]
  rw [translate_zero_FramedNode_move_refl]

/-- Step 5 of the V4 proof of `translate_zero` (V4 1.27): roles are preserved by zero translation. -/
private lemma translate_zero_step5_roles (U : HonestSource S) :
    ∀ n (N : {N // N ∈ U.hierarchy.nodes n})
      (hN : N.val.move (translation 0) ∈ U.hierarchy.nodes n),
      U.hierarchy.nodeRole ⟨n, ⟨N.val.move (translation 0), hN⟩⟩ =
        U.hierarchy.nodeRole ⟨n, N⟩ := by
  intro n N hN
  have h : N.val.move (translation 0) = N.val := translate_zero_FramedNode_move_refl N.val
  rw [show (⟨N.val.move (translation 0), hN⟩ : {N // N ∈ U.hierarchy.nodes n}) = N from Subtype.ext h]

/-- Step 6 of the V4 proof of `translate_zero` (V4 1.27): collect fields to form TranslatedSource. -/
private lemma translate_zero_step6_translatedSource (U : HonestSource S) :
    TranslatedSource U U (0 : E d) :=
  ⟨translate_zero_step1_tiling U, translate_zero_step2_nodes U, translate_zero_step3_coset U,
   translate_zero_step4_parents U, translate_zero_step5_roles U⟩

/-- C2, V4 1.27: translating by zero retains the complete original source. -/
theorem HonestSource.translate_zero (U : HonestSource S) : U.translate 0 = U := by
  exact TranslatedSource.unique (U.translate_spec 0) (translate_zero_step6_translatedSource U)

private lemma PlacedTile.move_move (t : PlacedTile S) (g h : Iso d) :
  (t.move g).move h = t.move (g.trans h) := by
  ext x
  · rfl
  · rw [PlacedTile.move_carrier, PlacedTile.move_carrier, PlacedTile.move_carrier, Set.image_image]
    rfl

private lemma Tiling.move_move (T : Tiling S) (g h : Iso d) :
  (T.move g).move h = T.move (g.trans h) := by
  obtain ⟨tiles, c, dj⟩ := T
  dsimp [Tiling.move]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, (PlacedTile.move_move z g h).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.move g, ⟨z, hz, rfl⟩, PlacedTile.move_move z g h⟩

omit [Fact (2 ≤ d)] in
private lemma translation_add (v w : E d) :
  translation (v + w) = (translation v).trans (translation w) := by
  ext x
  dsimp [translation, AffineIsometryEquiv.vaddConst, AffineIsometryEquiv.trans]
  abel

private lemma FramedNode.move_move (N : FramedNode S) (g h : Iso d) :
  (N.move g).move h = N.move (g.trans h) := by
  rcases N with ⟨ty, fr⟩
  rfl

private theorem translatedSource_comp {U V W : HonestSource S} {v w : E d}
    (h1 : TranslatedSource U V v) (h2 : TranslatedSource V W w) :
    TranslatedSource U W (v + w) := by
  have mm : ∀ N : FramedNode S, (N.move (translation v)).move (translation w) = N.move (translation (v + w)) := by
    intro N; rw [FramedNode.move_move, ← translation_add]
  have hmem : ∀ n (N : {N // N ∈ U.hierarchy.nodes n}), N.val.move (translation v) ∈ V.hierarchy.nodes n := by
    intro n N; rw [h1.nodes n]; exact ⟨N.val, N.property, rfl⟩
  have hmem2 : ∀ n (N : {N // N ∈ U.hierarchy.nodes n}) (hN : N.val.move (translation (v + w)) ∈ W.hierarchy.nodes n), (N.val.move (translation v)).move (translation w) ∈ W.hierarchy.nodes n := by
    intro n N hN; rw [mm]; exact hN
  have e : ∀ n (N : {N // N ∈ U.hierarchy.nodes n}) (hN : N.val.move (translation (v + w)) ∈ W.hierarchy.nodes n), (⟨N.val.move (translation (v + w)), hN⟩ : {N // N ∈ W.hierarchy.nodes n}) = ⟨(N.val.move (translation v)).move (translation w), hmem2 n N hN⟩ := fun n N hN => Subtype.ext (mm N.val).symm
  refine ⟨?tiling, ?nodes, h2.coset.trans h1.coset, ?parents, ?roles⟩
  case tiling => rw [h2.tiling, h1.tiling, Tiling.move_move, ← translation_add]
  case nodes =>
    intro n
    rw [h2.nodes n, h1.nodes n, ← Set.image_comp]
    exact congrArg (fun f => f '' U.hierarchy.nodes n) (funext mm)
  case parents =>
    intro n N hN
    have c := congrArg (fun q : {N // N ∈ W.hierarchy.nodes n} => (W.hierarchy.parent n q).val) (e n N hN)
    have p2 := h2.parents n ⟨N.val.move (translation v), hmem n N⟩ (hmem2 n N hN)
    have p1 := h1.parents n N (hmem n N)
    exact c.trans (p2.trans ((congrArg (fun x => x.move (translation w)) p1).trans (mm _)))
  case roles =>
    intro n N hN
    have c := congrArg (fun q : {N // N ∈ W.hierarchy.nodes n} => W.hierarchy.nodeRole ⟨n, q⟩) (e n N hN)
    exact c.trans ((h2.roles n ⟨N.val.move (translation v), hmem n N⟩ (hmem2 n N hN)).trans (h1.roles n N (hmem n N)))

/-- C2, V4 1.27: the chosen exact transports form the ordinary translation action. -/
theorem HonestSource.translate_add (U : HonestSource S) (v w : E d) :
    (U.translate v).translate w = U.translate (v + w) := by
  exact TranslatedSource.unique (translatedSource_comp (U.translate_spec v) ((U.translate v).translate_spec w)) (U.translate_spec (v + w))


/-- C2, V4 1.27: a source language is empty exactly when its height and type
have no honest node. No finiteness or covariance assumption is needed for this fact. -/
theorem honestLanguage_eq_empty_iff {X : Type} (ρ : HonestSource S → E d → X)
    (n : ℕ) (A : S.ι) :
    honestLanguage ρ n A = ∅ ↔
      ¬ ∃ (U : HonestSource S) (φ : Iso d),
        (⟨A, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n := by
  dsimp [honestLanguage]
  constructor
  · intro h
    rintro ⟨U, φ, hU⟩
    have : honestPattern ρ U n A φ ∈ (∅ : Set (Pattern S X n A)) := by
      rw [← h]
      simp only [Set.mem_setOf_eq]
      exact ⟨U, φ, hU, rfl⟩
    exact this
  · intro h
    ext q
    simp only [Set.mem_empty_iff_false, Set.mem_setOf_eq, iff_false, not_exists, not_and]
    intro U φ hU hq
    exact h ⟨U, φ, hU⟩

end Enforce
