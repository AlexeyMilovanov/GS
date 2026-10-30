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
  sorry

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
  sorry

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
  sorry

/-- C1, V4 1.26, rank proof V4 8.2: finite descent saturation, abstract over
all finite alphabets, nonempty ordered transition lists, forward-closed sets, and
actual forests. No geometric or substitution hypothesis is used. -/
theorem descent_saturation {α : Type u} [Finite α] (D : α → List α)
    (nonempty : ∀ a, D a ≠ []) (B : Set α) (hB : ForwardClosed D B)
    (F : DescentForest.{u, v} α D)
    (ground : ∀ x, F.level x = 0 → F.state x ∈ B) :
    ∀ x : F.Node, F.state x ∈ B := by
  sorry

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
  sorry

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

/-- C2, V4 1.27: translating by zero retains the complete original source. -/
theorem HonestSource.translate_zero (U : HonestSource S) : U.translate 0 = U := by
  sorry

/-- C2, V4 1.27: the chosen exact transports form the ordinary translation action. -/
theorem HonestSource.translate_add (U : HonestSource S) (v w : E d) :
    (U.translate v).translate w = U.translate (v + w) := by
  sorry

/-- C2, V4 1.27: a source language is empty exactly when its height and type
have no honest node. No finiteness or covariance assumption is needed for this fact. -/
theorem honestLanguage_eq_empty_iff {X : Type} (ρ : HonestSource S → E d → X)
    (n : ℕ) (A : S.ι) :
    honestLanguage ρ n A = ∅ ↔
      ¬ ∃ (U : HonestSource S) (φ : Iso d),
        (⟨A, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n := by
  sorry

end Enforce
