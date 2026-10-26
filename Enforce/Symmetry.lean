import Enforce.Recognition

/-!
# Finite Euclidean symmetry groups

Y1, V4 5.6--5.7. The proof uses the intrinsic native hierarchy, general expanding
linear σ, and every Euclidean isometry, including reflections. It does not use
the geometric fitting compiler. The polyhedral stabilizer lemma Sym1 already lives
in Geometry/Polyhedral; the obligations below expose the component, torsion and
Schur steps of 5.7 separately from the final assembly.
-/

open Set

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d} {P : Params S}
variable {C : ClusterData S P}

namespace Symmetry

/-- Y1, V4 5.7, Step 1: the component of a parsed node is the union of all
its ancestors' closed supports. It retains arbitrarily high ancestors and does
not assume a bounded window or a single component for the whole tiling. -/
def component (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) : Set (E d) :=
  ⋃ r : ℕ, ((parsedHierarchy Y hY).ancestor q r).2.val.carrier
    ((parsedHierarchy Y hY).ancestor q r).1

/-- Y1, V4 5.7, Step 1: a translated closed solid cone lies in a component.
Closure and positive-scalar stability describe a cone; nonempty interior excludes
a lower-dimensional or empty cone. The apex is an arbitrary actual point. -/
def ContainsSolidCone (D : Set (E d)) : Prop :=
  ∃ (q : E d) (K : Set (E d)), IsClosed K ∧ (interior K).Nonempty ∧
    (∀ t : ℝ, 0 ≤ t → ∀ v ∈ K, t • v ∈ K) ∧ (fun v => q + v) '' K ⊆ D

/-- Y1, V4 5.7, Step 1: components of ground tiles coincide precisely when
they have a common ancestor. An actual ground tile supplies nonempty geometry. -/
theorem component_eq_iff (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q r : (parsedHierarchy Y hY).Node) (hq : q.1 = 0) (hr : r.1 = 0) :
    component Y hY q = component Y hY r ↔
      ∃ n : ℕ, (parsedHierarchy Y hY).ancestor q n =
        (parsedHierarchy Y hY).ancestor r n := by
  sorry

/-- Y1, V4 5.7, Step 1: different ground components have disjoint interiors. -/
theorem components_disjoint (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q r : (parsedHierarchy Y hY).Node) (hq : q.1 = 0) (hr : r.1 = 0)
    (hne : component Y hY q ≠ component Y hY r) :
    Disjoint (interior (component Y hY q)) (interior (component Y hY r)) := by
  sorry

/-- Y1, V4 5.7, Step 1: every ground component contains a translated solid cone.
The bounded number of facet hyperplanes and strict expansion apply to anisotropic
σ as well; convexity of the prototypes or components is not assumed. -/
theorem component_contains_cone (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : q.1 = 0) :
    ContainsSolidCone (component Y hY q) := by
  sorry

/-- Y1, V4 5.7, Step 2: a positive power of any symmetry fixes a ground component.
Compact recurrence of its orthogonal part produces intersecting solid cones;
translations of the cone apices do not affect the large-distance intersection. -/
theorem power_fixes_component (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Iso d) (hg : Y.IsSymmetry g) (q : (parsedHierarchy Y hY).Node)
    (hq : q.1 = 0) :
    ∃ k : ℕ, 1 ≤ k ∧ (g ^ k) '' component Y hY q = component Y hY q := by
  sorry

/-- Y1, V4 5.7, Step 3: a positive power of any symmetry preserves an actual
bounded full-dimensional hierarchy node. Common ancestry is obtained from the
component argument; no finite-order hypothesis is inserted here. -/
theorem power_fixes_node (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Iso d) (hg : Y.IsSymmetry g) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ (n : ℕ) (N : FramedNode S),
      N ∈ (parsedHierarchy Y hY).nodes n ∧ (g ^ k) '' N.carrier n = N.carrier n := by
  sorry

/-- Y1/Sym1, V4 5.6, 5.7: every placed node is a full-dimensional polyhedron.
Invertible linear powers of σ and arbitrary isometric frames preserve these facts. -/
theorem node_polyhedron_full (n : ℕ) (N : FramedNode S) :
    Polyhedron (N.carrier n) ∧ (interior (N.carrier n)).Nonempty := by
  sorry

/-- Y1/Sym1, V4 5.6: the full setwise stabilizer of a node is finite. -/
theorem node_stabilizer_finite (n : ℕ) (N : FramedNode S) :
    {g : Iso d | g '' N.carrier n = N.carrier n}.Finite :=
  polyhedron_symmetries_finite _ (node_polyhedron_full n N).1
    (node_polyhedron_full n N).2

/-- Y1/Sym1, V4 5.6, 5.7, Step 3: any isometry preserving a node has finite order.
This is the group-theoretic consequence of its finite setwise stabilizer. -/
theorem finite_order_of_fixes_node (n : ℕ) (N : FramedNode S) (g : Iso d)
    (hg : g '' N.carrier n = N.carrier n) : IsOfFinOrder g := by
  sorry

/-- Y1, V4 5.7, Steps 1--3: every symmetry is periodic, before the group finiteness
argument. A positive power preserves a node and lies in its finite stabilizer. -/
theorem periodic (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Iso d) (hg : Y.IsSymmetry g) : IsOfFinOrder g := by
  obtain ⟨k, hk, n, N, _, hfix⟩ := power_fixes_node Y hY g hg
  have hp := finite_order_of_fixes_node n N (g ^ k) hfix
  rcases isOfFinOrder_pow.mp hp with h | h
  · exact h
  · omega

/-- Y1, V4 5.7, Step 4(i): the tile-and-marking symmetry group is countable.
The stronger local statement is discreteness: the labelled frame marker in one
tile isolates the identity. This countability consequence is used in Step 4(iii). -/
theorem symmetry_countable (Y : MarkedTiling (systemM S P C)) :
    Countable Y.symmetryGroup := by
  sorry

/-- Y1, V4 5.7, Step 4(ii): every finitely generated subgroup is finite. -/
def IsLocallyFiniteGroup (G : Subgroup (Iso d)) : Prop :=
  ∀ F : Finset (Iso d), (F : Set (Iso d)) ⊆ G →
    (Subgroup.closure (F : Set (Iso d)) : Set (Iso d)).Finite

/-- Y1, V4 5.7, Step 4(ii), Schur: a periodic Euclidean isometry group is locally
finite. Its faithful affine matrix representation has dimension d+1; no
orientation, bounded-orbit or finite-generation hypothesis on the whole group is used. -/
theorem schur_locally_finite (G : Subgroup (Iso d))
    (hperiodic : ∀ g : G, IsOfFinOrder (g.val : Iso d)) : IsLocallyFiniteGroup G := by
  sorry

/-- Y1, V4 5.7, Step 4(iii): a countable locally finite Euclidean isometry group
has a common fixed point. Finite subgroup barycentres give nested nonempty affine
fixed spaces, which stabilize in finite dimension. -/
theorem locally_finite_fixed_point (G : Subgroup (Iso d)) [Countable G]
    (hlocal : IsLocallyFiniteGroup G) :
    ∃ c : E d, ∀ g : G, g.val c = c := by
  sorry

/-- Y1, V4 5.7, Step 4(iii): all symmetries of a proper output fix one point.
The point is obtained from the periodic-group and countability arguments, not
assumed as an additional constraint on the tiling. -/
theorem common_fixed_point (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    ∃ c : E d, ∀ g : Iso d, Y.IsSymmetry g → g c = c := by
  letI := symmetry_countable Y
  obtain ⟨c, hc⟩ := locally_finite_fixed_point Y.symmetryGroup
    (schur_locally_finite Y.symmetryGroup (fun g => periodic Y hY g.val g.property))
  exact ⟨c, fun g hg => hc ⟨g, hg⟩⟩

/-- Y1, V4 5.7, Step 4(i),(iv): the symmetry stabilizer of any fixed point is finite.
The marked tile frame isolates the identity; the point stabilizer in the full
Euclidean group is compact. This holds even without properness. -/
theorem point_stabilizer_finite (Y : MarkedTiling (systemM S P C)) (c : E d) :
    {g : Iso d | Y.IsSymmetry g ∧ g c = c}.Finite := by
  sorry

end Symmetry

/-- Y1, V4 5.7: the full Euclidean symmetry group of every proper marked output
is finite, including reflections. Symmetries preserve both physical tiles and
markings. This conclusion uses the C1 system alone and no fitting construction. -/
theorem symmetry_finite (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    Y.symmetries.Finite := by
  obtain ⟨c, hc⟩ := Symmetry.common_fixed_point Y hY
  exact (Symmetry.point_stabilizer_finite Y c).subset (fun g hg => ⟨hg, hc g hg⟩)

/-- Y1, V4 5.7: finiteness of the symmetry group implies finite order of each
symmetry. This is also available for arbitrary enforcement data in Main.lean. -/
theorem symmetry_finite_order (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Iso d) (hg : Y.IsSymmetry g) : IsOfFinOrder g := by
  letI : Fintype Y.symmetryGroup := (symmetry_finite Y hY).fintype
  exact Y.symmetryGroup.subtype.isOfFinOrder
    (isOfFinOrder_of_finite (⟨g, hg⟩ : Y.symmetryGroup))

end Enforce
