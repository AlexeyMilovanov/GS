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
  sorry

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

/-- C2, V4 1.27, 1.11: honest sources are closed under translation.
Existence follows by translating the actual hierarchy and every finite legal context. -/
theorem honest_translate_exists (U : HonestSource S) (v : E d) :
    ∃ V : HonestSource S, TranslatedSource U V v := by
  sorry

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

/-- C2, V4 1.27: bounded full-dimensional tiles force a discrete, countable
translation stabilizer. This is proved from the tiling hypotheses, not assumed. -/
theorem translation_stabilizer_discrete (T : Tiling S) :
    DiscreteTopology (translationStabilizer T) ∧ Countable (translationStabilizer T) := by
  sorry

/-- C2, V4 1.27: any countable family of honest witnesses can be translated
so that their underlying physical tilings are pairwise distinct. Translated sources
exist because the given witnesses are honest; an empty family is harmless. -/
theorem translated_witnesses_distinct {α : Type} [Countable α]
    (witness : α → HonestSource S) :
    ∃ v : α → E d, Function.Injective (fun i => ((witness i).translate (v i)).tiling) := by
  sorry

/-- C2, V4 1.27: the language contributed by one chosen honest source per
species member. The domain is the actual species subtype, including an empty species. -/
def sectionLanguage {X : Type} (ρ : HonestSource S → E d → X)
    (s : S.Species → HonestSource S) (n : ℕ) (A : S.ι) : Set (Pattern S X n A) :=
  {q | ∃ (Z : S.Species) (φ : Iso d),
    (⟨A, φ⟩ : FramedNode S) ∈ (s Z).hierarchy.nodes n ∧
      q = honestPattern ρ (s Z) n A φ}

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
  sorry

/-- C2, V4 1.27: exact translation data determine one honest source, including
the hierarchy parents, child roles, and fixed orthogonal coset representative. -/
theorem TranslatedSource.unique {U V W : HonestSource S} {v : E d}
    (hV : TranslatedSource U V v) (hW : TranslatedSource U W v) : V = W := by
  sorry

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
