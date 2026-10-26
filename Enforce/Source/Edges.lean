import Enforce.Source.Trace

/-!
# Hereditary edge graph and the opposite-root bound

Graph vertices include the prototype type and its listed edge name. Edge vectors
are chosen endpoints of actual listed segments, with no preferred orientation.
The bounds apply to every reachable ordered pair and every common expansion power.
-/

open Set

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

/-- P15, V4 1.20: a graph vertex is a prototype and one of its listed edges. -/
abbrev EdgeName (S : SubstSystem d) := Σ A : S.ι, {e // e ∈ (S.cx A).edges}

/-- P15, V4 1.20: a listed one-cell is a nondegenerate closed segment.
Connectedness and regular closedness in its one-dimensional affine span give this. -/
theorem edge_endpoints_exist (e : EdgeName S) :
    ∃ ab : E d × E d, ab.1 ≠ ab.2 ∧ e.2.val.carrier = segment ℝ ab.1 ab.2 := by
  sorry

/-- P15, V4 1.20: an arbitrary orientation of the actual edge vector. -/
def edgeVector (e : EdgeName S) : E d :=
  (Classical.choose (edge_endpoints_exist e)).2 -
    (Classical.choose (edge_endpoints_exist e)).1

/-- P15, V4 1.20: the selected endpoints represent the listed edge and are distinct. -/
theorem edgeVector_spec (e : EdgeName S) :
    edgeVector e ≠ 0 ∧
      Metric.diam e.2.val.carrier = ‖edgeVector e‖ := by
  sorry

/-- P15, V4 1.20: the finite directed hereditary graph `Γ`.
An arrow records an actual child edge occurrence in the expanded source edge. -/
def edgeGraph (S : SubstSystem d) (e f : EdgeName S) : Prop :=
  ∃ i : S.I e.1, (S.child e.1 i).ty = f.1 ∧
    placedSet (S.child e.1 i).frame f.2.val.carrier ⊆ S.σ '' e.2.val.carrier

/-- P15, V4 1.20: finite graph vertex set, including the empty-catalogue case. -/
theorem edgeNames_finite (S : SubstSystem d) : Finite (EdgeName S) := by
  sorry

/-- P15, V4 1.20: the length of an edge after a common power of the expansion. -/
def expandedEdgeLength (r : ℕ) (e : EdgeName S) : ℝ := ‖(S.σ ^ r) (edgeVector e)‖

/-- P15, V4 1.20: constants controlling all reachable edge pairs. -/
structure EdgeBounds (S : SubstSystem d) where
  /-- P15, V4 1.20: positive lower ratio bound. -/
  lower : ℝ
  /-- P15, V4 1.20: finite upper ratio bound. -/
  upper : ℝ
  /-- P15, V4 1.20: strict positivity. -/
  lower_pos : 0 < lower
  /-- P15, V4 1.20: ordered bounds. -/
  lower_le_upper : lower ≤ upper
  /-- P15, V4 1.20: the same bounds for every path and every power. -/
  bounds : ∀ e f : EdgeName S, Relation.ReflTransGen (edgeGraph S) e f →
    ∀ r : ℕ, lower ≤ expandedEdgeLength r f / expandedEdgeLength r e ∧
      expandedEdgeLength r f / expandedEdgeLength r e ≤ upper

/-- P15, V4 1.20: uniform hereditary edge ratio bounds exist.
Even an empty graph admits positive constants; no source tiling is assumed. -/
theorem edge_ratio_bounds (S : SubstSystem d) : Nonempty (EdgeBounds S) := by
  sorry

/-- P16, V4 1.21: the exact paper bound `M = floor (1 / ℓ)`. -/
def oppositeRootBound (B : EdgeBounds S) : ℕ := ⌊1 / B.lower⌋₊

/-- P16, V4 1.21: disjoint reachable root edges at a common height inside one
edge are bounded in number by the reciprocal lower ratio. The nodes need not be
siblings or form a side-to-side patch. -/
theorem opposite_root_edges_bound (B : EdgeBounds S) (n : ℕ)
    (H : FramedNode S) (h : {e // e ∈ (S.cx H.ty).edges})
    {α : Type} [Fintype α] (t : α → FramedNode S)
    (e : ∀ a, {e // e ∈ (S.cx (t a).ty).edges})
    (hsub : ∀ a, (t a).cell n (e a).val ⊆ H.cell n h.val)
    (hdisj : Pairwise (fun a b => Disjoint
      (relint ((t a).cell n (e a).val)) (relint ((t b).cell n (e b).val))))
    (hreach : ∀ a, Relation.ReflTransGen (edgeGraph S) ⟨H.ty, h⟩ ⟨(t a).ty, e a⟩) :
    Fintype.card α ≤ oppositeRootBound B := by
  sorry

/-- P16, V4 1.21: the bound is positive whenever a root edge is present. -/
theorem oppositeRootBound_pos (B : EdgeBounds S) (e : EdgeName S) :
    1 ≤ oppositeRootBound B := by
  sorry

end Enforce
