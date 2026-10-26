import Enforce.Source.Trace

/-!
# Incident forests, power factorisation, and finite headers

Compatible patches retain their actual frames, rather than choosing frames of physical
carriers. Cones in header tuples are direction cones at the origin. Translating an
apex to the origin before supplying the tuple gives exactly the notation of V4 1.17.
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

/-- P9, V4 1.14: a finite patch with specified compatible ground frames. -/
structure CompatiblePatch (S : SubstSystem d) where
  /-- P9, V4 1.14: the framed ground tiles. -/
  tiles : Finset (FramedNode S)
  /-- P9, V4 1.14: disjoint interiors of distinct patch members. -/
  disjoint : (tiles : Set (FramedNode S)).PairwiseDisjoint (fun t => interior (t.carrier 0))
  /-- P9, V4 1.14: every specified frame belongs to the compatible group. -/
  compatible : ∀ t ∈ tiles, t.frame.linearIsometryEquiv ∈ S.rotGroup

/-- P9, V4 1.14: conjugated frame under ambient expansion of a compatible tile. -/
def compatibleInflatedFrame (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup) (n : ℕ) : Iso d :=
  rigidMotion (Classical.choose (S.rotGroup_conj_zpow (n : ℤ)
    t.frame.linearIsometryEquiv ht)) ((S.σ ^ n) (t.frame 0))

namespace CompatiblePatch

variable (P : CompatiblePatch S)

/-- P9, V4 1.14: addresses in the depth-`n` subdivision of the inflated patch. -/
abbrev Address (n : ℕ) := Σ t : {t // t ∈ P.tiles}, S.RoleWord t.val.ty n

/-- P9, V4 1.14: the native tile at an address of `σⁿ Π`. -/
def native (n : ℕ) (a : P.Address n) : FramedNode S :=
  (S.nativeTile a.1.val.ty n a.2).move
    (compatibleInflatedFrame a.1.val (P.compatible a.1.val a.1.property) n)

/-- P9, V4 1.14: every native frame is still compatible. -/
theorem native_compatible (n : ℕ) (a : P.Address n) :
    (P.native n a).frame.linearIsometryEquiv ∈ S.rotGroup := by
  sorry

/-- P9, V4 1.14: incident native tiles, with their unambiguous addresses. -/
abbrev Incident (p : E d) (n : ℕ) :=
  {a : P.Address n // (S.σ ^ n) p ∈ (P.native n a).carrier 0}

/-- P9, V4 1.14: the geometric child relation between consecutive inflated levels.
Containment in `σ t` determines the actual substitution parent. -/
def IncidentChild (p : E d) (n : ℕ) (a : P.Incident p n)
    (b : P.Incident p (n + 1)) : Prop :=
  (P.native (n + 1) b.val).carrier 0 ⊆ S.σ '' (P.native n a.val).carrier 0

/-- P9, V4 1.14: every incident native tile has a unique incident parent.
The original address prevents identifying distinct occurrences by a chosen frame. -/
theorem incident_parent_exists_unique (p : E d) (n : ℕ)
    (b : P.Incident p (n + 1)) :
    ∃! a : P.Incident p n, P.IncidentChild p n a b := by
  sorry

/-- P9, V4 1.14: the incident-forest parent chosen from unique existence. -/
def incidentParent (p : E d) (n : ℕ) (b : P.Incident p (n + 1)) : P.Incident p n :=
  Classical.choose (P.incident_parent_exists_unique p n b)

/-- P9, V4 1.14: specification of the incident parent. -/
theorem incidentParent_spec (p : E d) (n : ℕ) (b : P.Incident p (n + 1)) :
    P.IncidentChild p n (P.incidentParent p n b) b :=
  (Classical.choose_spec (P.incident_parent_exists_unique p n b)).1

/-- P9, V4 1.14: a tail after level `N`, retaining all actual incident tiles. -/
structure IncidentTail (p : E d) (N : ℕ) where
  /-- P9, V4 1.14: the successive incident addresses. -/
  node : ∀ r : ℕ, P.Incident p (N + r)
  /-- P9, V4 1.14: successive nodes are geometric substitution children. -/
  step : ∀ r, (P.native (N + (r + 1)) (node (r + 1)).val).carrier 0 ⊆
    S.σ '' (P.native (N + r) (node r).val).carrier 0

/-- P9, V4 1.14: bounded width, no dying branches, and eventual unique children.
DEVIATION: the exact minimum-angle constant uses the nonempty catalogue, as in D3. -/
theorem incidentForest [Nonempty S.ι] (p : E d) :
    (∀ n, Finite (P.Incident p n) ∧
      Nat.card (P.Incident p n) ≤ multiplicityBound S.proto S.cx) ∧
    (∀ n (a : P.Incident p n),
      ∃ b : P.Incident p (n + 1), P.IncidentChild p n a b) ∧
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ a : P.Incident p n,
      ∃! b : P.Incident p (n + 1), P.IncidentChild p n a b := by
  sorry

/-- P9, V4 1.14: beyond a splitting cutoff, tails are in bijection with the
incident tiles there, so there are at most `M₀` infinite tails.
DEVIATION: the exact `M₀` requires the nonempty angle catalogue, as in D3. -/
theorem incident_tails [Nonempty S.ι] (p : E d) :
    ∃ N : ℕ, Function.Bijective (fun t : P.IncidentTail p N => t.node 0) ∧
      Finite (P.IncidentTail p N) ∧
      Nat.card (P.IncidentTail p N) ≤ multiplicityBound S.proto S.cx := by
  sorry

/-- P9/P5, V4 1.14, 1.5(b): common-listed points in the original patch. -/
def CommonListed (p : E d) : Prop :=
  ∀ t ∈ P.tiles, p ∈ t.carrier 0 → t.Lists 0 p

/-- P9, V4 1.14: listedness persists across every incident child step. -/
theorem incident_listed_step (p : E d) (n : ℕ) (a : P.Incident p n)
    (b : P.Incident p (n + 1)) (hab : P.IncidentChild p n a b)
    (ha : (P.native n a.val).Lists 0 ((S.σ ^ n) p)) :
    (P.native (n + 1) b.val).Lists 0 ((S.σ ^ (n + 1)) p) := by
  sorry

/-- P9/P5, V4 1.14, 1.5(b): a common-listed point is listed at every depth. -/
theorem incident_commonListed (p : E d) (hp : P.CommonListed p)
    (n : ℕ) (a : P.Incident p n) : (P.native n a.val).Lists 0 ((S.σ ^ n) p) := by
  sorry

end CompatiblePatch

/-- P10, V4 1.15: every complex root of the characteristic polynomial is positive
real. This formulation allows Jordan blocks and imposes no self-adjointness. -/
def PositiveRealSpectrum (L : E d ≃ₗ[ℝ] E d) : Prop :=
  ∀ z : ℂ, (L.toLinearMap.charpoly.map (algebraMap ℝ ℂ)).IsRoot z →
    z.im = 0 ∧ 0 < z.re

/-- P10, V4 1.15: the full data of a power factorisation. -/
structure PowerFactorisation (S : SubstSystem d) where
  /-- P10, V4 1.15: positive integral exponent. -/
  power : ℕ
  /-- P10, V4 1.15: nonzero power. -/
  power_pos : 1 ≤ power
  /-- P10, V4 1.15: compatible orthogonal factor. -/
  R : Ortho d
  /-- P10, V4 1.15: membership in the closed compatible group. -/
  R_mem : R ∈ S.rotGroup
  /-- P10, V4 1.15: invertible positive-spectrum factor. -/
  L : E d ≃ₗ[ℝ] E d
  /-- P10, V4 1.15: equality of the actual linear maps. -/
  factor : S.σ ^ power = R.toLinearEquiv * L
  /-- P10, V4 1.15: normalization, as equality of sets of linear equivalences. -/
  normalizes : (fun h : Ortho d => L * h.toLinearEquiv * L⁻¹) ''
      (S.rotGroup : Set (Ortho d)) =
    (fun h : Ortho d => h.toLinearEquiv) '' (S.rotGroup : Set (Ortho d))
  /-- P10, V4 1.15: positive real spectrum without a diagonalizability assumption. -/
  positive : PositiveRealSpectrum L

/-- P10, V4 1.15: a power admits the prescribed factorisation.
DEVIATION: `Nonempty S.ι` is explicit because stage 1 allows an empty catalogue.
V4's proof chooses a prototile and vertex; without any tiles an arbitrary expansion
need not have a positive-spectrum power modulo the trivial compatible group. -/
theorem power_factorisation (S : SubstSystem d) [Nonempty S.ι] :
    Nonempty (PowerFactorisation S) := by
  sorry

/-- P11, V4 1.16(a): the positive factor centralizes the full compatible group. -/
theorem L_commutes (F : PowerFactorisation S) (h : Ortho d) (hh : h ∈ S.rotGroup) :
    F.L * h.toLinearEquiv = h.toLinearEquiv * F.L := by
  sorry

/-- P11, V4 1.16(b): every direction and every oriented side is fixed. -/
theorem L_fixes_directions_sides (F : PowerFactorisation S) :
    (∀ V ∈ S.hPi, V.map F.L.toLinearMap = V) ∧
      ∀ K : Set (E d), IsClosedSide S.hPi K → F.L '' K = K := by
  sorry

/-- P11, V4 1.16(b): every finite union/intersection `HΠ`-cone is fixed. -/
theorem L_fixes_HPiCones (F : PowerFactorisation S) (K : Set (E d))
    (hK : HPiCone S.hPi K) : F.L '' K = K := by
  sorry

/-- P11, V4 1.16(b'): tangent cones of listed cells of compatible ground tiles
at their listed vertices are `HΠ`-cones. This includes all lower dimensions. -/
theorem tangentCone_isHPiCone (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup) (C : CellName S t.ty)
    (p : E d) (hp : t.Lists 0 p) (hpC : p ∈ t.cell 0 C.val) :
    HPiCone S.hPi (tangentCone (t.cell 0 C.val) p) := by
  sorry

/-- P11, V4 1.16(b'): cones of finite unions of compatible cells at a listed
anchor are `HΠ`-cones, as are full tile cones at listed vertices. -/
theorem tangentCone_tile_isHPiCone (t : FramedNode S)
    (ht : t.frame.linearIsometryEquiv ∈ S.rotGroup) (p : E d) (hp : t.Lists 0 p) :
    HPiCone S.hPi (tangentCone (t.carrier 0) p) := by
  sorry

/-- P11, V4 1.16(c): the factors commute. -/
theorem RL_commute (F : PowerFactorisation S) :
    F.R.toLinearEquiv * F.L = F.L * F.R.toLinearEquiv := by
  sorry

/-- P11, V4 1.16(c): power decomposition and compatible residual rotations. -/
theorem power_cone_formula (F : PowerFactorisation S) (a r : ℕ) (hr : r < F.power) :
    S.σ ^ (a * F.power + r) = S.σ ^ r * F.R.toLinearEquiv ^ a * F.L ^ a ∧
      ∃ Q ∈ S.rotGroup, Q.toLinearEquiv =
        linearConj S.σ (r : ℤ) (F.R.toLinearEquiv ^ a) ∧
        ∀ K : Set (E d), HPiCone S.hPi K →
          (S.σ ^ (a * F.power + r)) '' K = Q '' ((S.σ ^ r) '' K) := by
  sorry

/-- P12, V4 1.17: a header is a literal tuple of cones, a type, and a vertex name. -/
structure Header (S : SubstSystem d) (s : ℕ) where
  /-- P12, V4 1.17: type of the listing native tile. -/
  ty : S.ι
  /-- P12, V4 1.17: vertex in that type's boundary complex. -/
  vertex : {e // e ∈ (S.cx ty).vertices}
  /-- P12, V4 1.17: direction cones in the tile's isometric prototype frame. -/
  cones : Fin s → Set (E d)

namespace CompatiblePatch

variable (P : CompatiblePatch S)

/-- P12, V4 1.17: all headers at one anchor, over all depths and listing tiles.
The supplied cones have already been translated from the apex to the origin. -/
def headers (p : E d) {s : ℕ} (G : Fin s → Set (E d)) : Set (Header S s) :=
  {h | ∃ (n : ℕ) (a : P.Incident p n),
    (S.σ ^ n) p ∈ (P.native n a.val).cell 0 h.vertex.val ∧
    h.ty = (P.native n a.val).ty ∧
      ∀ j, h.cones j = (P.native n a.val).frame.linearIsometryEquiv.symm ''
        ((S.σ ^ n) '' G j)}

/-- P12, V4 1.17: finite actual header tuples over all listing incident tiles.
No common-listed hypothesis is needed: only tiles listing the anchor contribute. -/
theorem header_finiteness (p : E d) {s : ℕ} (G : Fin s → Set (E d))
    (hG : ∀ j, HPiCone S.hPi (G j)) : (P.headers p G).Finite := by
  sorry

/-- P13, V4 1.18: a complete star in a chosen incident tile's isometric frame,
with arbitrary labels from `Y`. Every incident tile and its vertex name is retained. -/
def positionedStar {Y : Type} (p : E d) (n : ℕ) (anchor : P.Incident p n)
    (label : P.Incident p n → Y) : Set (FramedNode S × Cell d × Y) :=
  {z | ∃ (a : P.Incident p n) (v : Cell d),
    v ∈ (S.cx (P.native n a.val).ty).vertices ∧
    (S.σ ^ n) p ∈ (P.native n a.val).cell 0 v ∧
    z = ((P.native n a.val).move (P.native n anchor.val).frame.symm, v, label a)}

/-- P13, V4 1.18: all possible complete positioned stars, allowing every
labelling at every depth and every choice of reference tile. -/
def positionedStars (Y : Type) (p : E d) :
    Set (Set (FramedNode S × Cell d × Y)) :=
  {s | ∃ (n : ℕ) (anchor : P.Incident p n) (label : P.Incident p n → Y),
    s = P.positionedStar p n anchor label}

/-- P13, V4 1.18: finitely many full positioned stars, with an arbitrary finite
label alphabet. This includes the unlabelled case by taking `Y = Unit`. -/
theorem positioned_stars_finite (Y : Type) [Finite Y] (p : E d)
    (hp : P.CommonListed p) : (P.positionedStars Y p).Finite := by
  sorry

/-- P14, V4 1.19: uniform native-scale cone radius and the union formula for
any selected collection of original tiles whose cones form the chosen cone.
A single positive radius works at every depth and for every selected subpatch. -/
theorem uniform_cone_radius (p : E d) (hp : P.CommonListed p) :
    ∃ r₀ : ℝ, 0 < r₀ ∧
      (∀ (n : ℕ) (a : P.Incident p n),
        (P.native n a.val).carrier 0 ∩ ball ((S.σ ^ n) p) r₀ =
          ((fun v => (S.σ ^ n) p + v) ''
            tangentCone ((P.native n a.val).carrier 0) ((S.σ ^ n) p)) ∩
              ball ((S.σ ^ n) p) r₀) ∧
      ∀ Q : Finset (FramedNode S), Q ⊆ P.tiles → ∀ n : ℕ,
        (⋃ a : P.Incident p n, ⋃ (_ : a.val.1.val ∈ Q),
          (P.native n a.val).carrier 0) ∩ ball ((S.σ ^ n) p) r₀ =
        ((fun v => (S.σ ^ n) p + v) ''
          ((S.σ ^ n) '' tangentCone (⋃ t ∈ Q, t.carrier 0) p)) ∩
            ball ((S.σ ^ n) p) r₀ := by
  sorry

end CompatiblePatch

/-- P11, V4 1.16(b): the cone language is closed under arbitrary finite unions. -/
theorem HPiCone_finite_union {α : Type} [Finite α] (K : α → Set (E d))
    (hK : ∀ a, HPiCone S.hPi (K a)) : HPiCone S.hPi (⋃ a, K a) := by
  sorry

/-- P11, V4 1.16(b): the cone language is closed under arbitrary finite intersections. -/
theorem HPiCone_finite_inter {α : Type} [Finite α] (K : α → Set (E d))
    (hK : ∀ a, HPiCone S.hPi (K a)) : HPiCone S.hPi (⋂ a, K a) := by
  sorry

/-- P11, V4 1.16(b'): the tangent cone of a finite union of compatible listed
cells at a common listed anchor remains an `HΠ`-cone, in all dimensions. -/
theorem tangentCone_union_isHPiCone (P : CompatiblePatch S)
    (Q : Finset (Σ t : {t // t ∈ P.tiles}, CellName S t.val.ty)) (p : E d)
    (hlisted : ∀ q ∈ Q, q.1.val.Lists 0 p)
    (hcontains : ∀ q ∈ Q, p ∈ q.1.val.cell 0 q.2.val) :
    HPiCone S.hPi (tangentCone (⋃ q ∈ Q, q.1.val.cell 0 q.2.val) p) := by
  sorry

/-- P14, V4 1.19: a single prototype-catalogue radius works for every placed
ground tile at every listed vertex, independently of patches and their depth.
An empty catalogue admits any positive radius. -/
theorem uniform_prototype_cone_radius (S : SubstSystem d) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (t : FramedNode S) (p : E d), t.Lists 0 p →
      t.carrier 0 ∩ ball p r₀ =
        ((fun v => p + v) '' tangentCone (t.carrier 0) p) ∩ ball p r₀ := by
  sorry

namespace CompatiblePatch

variable (P : CompatiblePatch S)

/-- P9, V4 1.14: the native subdivision has no repeated framed tile occurrences. -/
theorem native_injective (n : ℕ) : Function.Injective (P.native n) := by
  sorry

/-- P9, V4 1.14: all native tiles have disjoint interiors, with no side-to-side
hypothesis, and they cover exactly the ambient expansion of the original patch. -/
theorem native_subdivision (n : ℕ) :
    Pairwise (fun a b : P.Address n => Disjoint
      (interior ((P.native n a).carrier 0)) (interior ((P.native n b).carrier 0))) ∧
      (⋃ a : P.Address n, (P.native n a).carrier 0) =
        (S.σ ^ n) '' (⋃ t ∈ P.tiles, t.carrier 0) := by
  sorry

/-- P9, V4 1.14: the number of incident tiles never decreases with depth. -/
theorem incident_width_monotone (p : E d) (n : ℕ) :
    Nat.card (P.Incident p n) ≤ Nat.card (P.Incident p (n + 1)) := by
  sorry

/-- P12, V4 1.17: every incident tile listing the anchor contributes its full
header, with the actual named vertex. This supplies witnesses to the header set. -/
theorem header_occurs (p : E d) {s : ℕ} (G : Fin s → Set (E d)) (n : ℕ)
    (a : P.Incident p n)
    (v : {e // e ∈ (S.cx (P.native n a.val).ty).vertices})
    (hv : (S.σ ^ n) p ∈ (P.native n a.val).cell 0 v.val) :
    (⟨(P.native n a.val).ty, v,
      fun j => (P.native n a.val).frame.linearIsometryEquiv.symm ''
        ((S.σ ^ n) '' G j)⟩ : Header S s) ∈ P.headers p G := by
  sorry

end CompatiblePatch

end Enforce
