import Tilings.Basic
import Tilings.Control.Certificate

/-!
# The repaired grouping construction (statements only)

Skeleton for the chapter `grouping.tex` of the blueprint: mesh constants
(`def:mesh`), the anchored inside/outside groupings
(`lem:regular-grouping`, `lem:outside-grouping`), disjoint skeletal spokes
(`lem:annular-spokes`), quantitative sector localization
(`lem:quantitative-sector`), the fingerprint criterion (`lem:fingerprint`) and
wide routing after a power (`lem:routing`).

The existence of the macrocertificate (`lem:certificate-exists`) is stated at
the end, against `Tilings.Geometry.MacroCertificate` from
`Tilings/Control/Certificate.lean` (which imports only `Tilings.Basic`).

All theorems are `sorry`.  The two classical polygonal-topology helpers
`polygonalJordanBoundary` and `plAnnulusRouting` are stated separately; they
must be *proved* (or obtained from a proved polygonal topology API), never
assumed.

Planar notation: `Binf r` is the closed sup-norm ball `[-r,r]^2`,
`square c h` the closed axis-parallel square with centre `c` and half side `h`;
Minkowski sums `Q + Binf r` are the square buffers of the blueprint.
-/

open Set Pointwise

noncomputable section

namespace Tilings

namespace Geometry

variable {P : Protoset}

/-! ## Planar notation -/

/-- The point with coordinates `(x, y)`. -/
def mkPt (x y : ℝ) : Pt := !₂[x, y]

/-- The closed sup-norm ball `B∞(r) = [-r, r]²`. -/
def Binf (r : ℝ) : Set Pt := {x | |x 0| ≤ r ∧ |x 1| ≤ r}

/-- The closed axis-parallel square with centre `c` and half side `h`. -/
def square (c : Pt) (h : ℝ) : Set Pt := {x | |x 0 - c 0| ≤ h ∧ |x 1 - c 1| ≤ h}

/-! ## Mesh constants (`def:mesh`) -/

/-- Mesh constants of a finite protoset (`def:mesh`): every form has diameter
at most `D`, area at least `a`, every listed side has length at least `γ`,
and every form has at most `K0` listed sides.  Only finiteness of `P` is used
to obtain them; neither FLC nor the crown-cover lemma is involved. -/
structure MeshConstants (P : Protoset) where
  D : ℝ
  a : ℝ
  γ : ℝ
  K0 : ℕ
  D_pos : 0 < D
  a_pos : 0 < a
  γ_pos : 0 < γ
  diam_le : ∀ p : P.Form, Metric.diam (P.disk p).carrier ≤ D
  area_ge : ∀ p : P.Form, ENNReal.ofReal a ≤ MeasureTheory.volume (P.disk p).carrier
  side_ge : ∀ (p : P.Form) (i : Fin (P.disk p).n),
    γ ≤ dist ((P.disk p).vertex i) ((P.disk p).vertex (finRotate _ i))
  sides_le : ∀ p : P.Form, (P.disk p).n ≤ K0

private lemma mesh_finRotate_ne_self {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    finRotate n i ≠ i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have h1 : (1 : Fin (m + 1)) = 0 := by
    have := congrArg (fun x => x - i) h
    simpa using this
  have : NeZero (m + 1) := ⟨by omega⟩
  rw [Fin.one_eq_zero_iff] at h1
  omega

/-- Mesh constants exist for every finite protoset. -/
theorem MeshConstants.nonempty (P : Protoset) : Nonempty (MeshConstants P) := by
  classical
  by_cases hForm : Nonempty P.Form
  · obtain ⟨p0⟩ := hForm
    let diameters := Finset.univ.image (fun p : P.Form => Metric.diam (P.disk p).carrier)
    have diameters_nonempty : diameters.Nonempty :=
      ⟨Metric.diam (P.disk p0).carrier, Finset.mem_image_of_mem _ (Finset.mem_univ p0)⟩
    let D := max 1 (diameters.max' diameters_nonempty)
    have D_pos : 0 < D := lt_max_iff.mpr (Or.inl zero_lt_one)
    have diam_le : ∀ p : P.Form, Metric.diam (P.disk p).carrier ≤ D := by
      intro p
      apply le_max_of_le_right
      exact Finset.le_max' diameters _ (Finset.mem_image_of_mem _ (Finset.mem_univ p))
    let areas := Finset.univ.image
      (fun p : P.Form => (MeasureTheory.volume (P.disk p).carrier).toReal)
    have areas_nonempty : areas.Nonempty :=
      ⟨(MeasureTheory.volume (P.disk p0).carrier).toReal,
        Finset.mem_image_of_mem _ (Finset.mem_univ p0)⟩
    let a := areas.min' areas_nonempty
    have a_pos : 0 < a := by
      have ha_mem : a ∈ areas := Finset.min'_mem areas areas_nonempty
      rcases Finset.mem_image.mp ha_mem with ⟨p, -, hp⟩
      rw [← hp]
      apply ENNReal.toReal_pos
      · exact ((isOpen_interior.measure_pos MeasureTheory.volume (P.disk p).interior_nonempty).trans_le
          (MeasureTheory.measure_mono interior_subset)).ne'
      · exact (P.disk p).compact.measure_lt_top.ne
    have area_ge : ∀ p : P.Form,
        ENNReal.ofReal a ≤ MeasureTheory.volume (P.disk p).carrier := by
      intro p
      calc
        ENNReal.ofReal a ≤ ENNReal.ofReal (MeasureTheory.volume (P.disk p).carrier).toReal :=
          ENNReal.ofReal_le_ofReal
            (Finset.min'_le areas _ (Finset.mem_image_of_mem _ (Finset.mem_univ p)))
        _ = MeasureTheory.volume (P.disk p).carrier :=
          ENNReal.ofReal_toReal (P.disk p).compact.measure_lt_top.ne
    let sideLengths (p : P.Form) := Finset.univ.image
      (fun i : Fin (P.disk p).n =>
        dist ((P.disk p).vertex i) ((P.disk p).vertex (finRotate _ i)))
    have sideLengths_nonempty (p : P.Form) : (sideLengths p).Nonempty := by
      let i : Fin (P.disk p).n := ⟨0, by have := (P.disk p).three_le; omega⟩
      exact ⟨dist ((P.disk p).vertex i) ((P.disk p).vertex (finRotate _ i)),
        Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
    let shortest (p : P.Form) := (sideLengths p).min' (sideLengths_nonempty p)
    let shortestLengths := Finset.univ.image shortest
    have shortestLengths_nonempty : shortestLengths.Nonempty :=
      ⟨shortest p0, Finset.mem_image_of_mem _ (Finset.mem_univ p0)⟩
    let γ := shortestLengths.min' shortestLengths_nonempty
    have γ_pos : 0 < γ := by
      have hγ_mem : γ ∈ shortestLengths :=
        Finset.min'_mem shortestLengths shortestLengths_nonempty
      rcases Finset.mem_image.mp hγ_mem with ⟨p, -, hp⟩
      rw [← hp]
      have hp_mem : shortest p ∈ sideLengths p :=
        Finset.min'_mem (sideLengths p) (sideLengths_nonempty p)
      rcases Finset.mem_image.mp hp_mem with ⟨i, -, hi⟩
      rw [← hi]
      rw [dist_pos]
      intro h
      have hi : i = finRotate (P.disk p).n i := (P.disk p).vertex_injective h
      exact mesh_finRotate_ne_self (by have := (P.disk p).three_le; omega) i hi.symm
    have side_ge : ∀ (p : P.Form) (i : Fin (P.disk p).n),
        γ ≤ dist ((P.disk p).vertex i) ((P.disk p).vertex (finRotate _ i)) := by
      intro p i
      exact (Finset.min'_le shortestLengths (shortest p)
        (Finset.mem_image_of_mem _ (Finset.mem_univ p))).trans
          (Finset.min'_le (sideLengths p) _
            (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
    let sideCounts := Finset.univ.image (fun p : P.Form => (P.disk p).n)
    have sideCounts_nonempty : sideCounts.Nonempty :=
      ⟨(P.disk p0).n, Finset.mem_image_of_mem _ (Finset.mem_univ p0)⟩
    let K0 := sideCounts.max' sideCounts_nonempty
    have sides_le : ∀ p : P.Form, (P.disk p).n ≤ K0 := by
      intro p
      exact Finset.le_max' sideCounts _ (Finset.mem_image_of_mem _ (Finset.mem_univ p))
    exact ⟨⟨D, a, γ, K0, D_pos, a_pos, γ_pos, diam_le, area_ge, side_ge, sides_le⟩⟩
  · refine ⟨⟨1, 1, 1, 0, zero_lt_one, zero_lt_one, zero_lt_one, ?_, ?_, ?_, ?_⟩⟩
    · intro p
      exact (hForm ⟨p⟩).elim
    · intro p
      exact (hForm ⟨p⟩).elim
    · intro p
      exact (hForm ⟨p⟩).elim
    · intro p
      exact (hForm ⟨p⟩).elim

/-! ## The finite cellulation view of a patch (`def:mesh`) -/

/-- The original skeleton: the union of all listed sides of tiles of `S`. -/
def skeleton (S : Set (PlacedTile P)) : Set Pt :=
  ⋃ A ∈ S, ⋃ i : Fin (P.disk A.form).n, A.side i

/-- The edges of the cellulation: the listed sides of tiles of `S`. -/
def edges (S : Set (PlacedTile P)) : Set (Set Pt) :=
  {e | ∃ A ∈ S, ∃ i : Fin (P.disk A.form).n, A.side i = e}

/-- The vertices of the cellulation: the listed vertices of tiles of `S`. -/
def vertices (S : Set (PlacedTile P)) : Set Pt := {v | Substitution.IsVertexOf S v}

/-- `e` is one of the listed sides of the placed tile `A`. -/
def HasEdge (A : PlacedTile P) (e : Set Pt) : Prop :=
  ∃ i : Fin (P.disk A.form).n, A.side i = e

/-- Two distinct faces share a complete listed side. -/
def SharesSide (A B : PlacedTile P) : Prop :=
  A ≠ B ∧ ∃ e, HasEdge A e ∧ HasEdge B e

/-- The face-dual graph of `S` (faces adjacent across complete sides) is
connected. -/
def DualConnected (S : Set (PlacedTile P)) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S,
    Relation.ReflTransGen (fun X Y => X ∈ S ∧ Y ∈ S ∧ SharesSide X Y) A B

/-- A group of faces of the cellulation `S`: a finite set of complete
original faces whose union is a polygonal disk, whose listed boundary sides
are complete original sides, which retains every original vertex on its
boundary, and whose face-dual graph is connected.  Being a polygonal disk is
a *field* that must be established through `polygonalJordanBoundary`; it is
never declared for a filled union without proof. -/
structure FaceGroup (S : Set (PlacedTile P)) where
  faces : Set (PlacedTile P)
  faces_sub : faces ⊆ S
  finite : faces.Finite
  disk : PolygonalDisk
  carrier_eq : disk.carrier = support faces
  side_whole : ∀ i : Fin disk.n, ∃ A ∈ faces, HasEdge A (disk.side i)
  vertex_retained : ∀ v, Substitution.IsVertexOf S v → v ∈ frontier disk.carrier → v ∈ disk.vertexSet
  dualConnected : DualConnected faces

namespace FaceGroup

variable {S : Set (PlacedTile P)}

/-- The closed region of a group. -/
def carrier (L : FaceGroup S) : Set Pt := L.disk.carrier

/-- Inside anchoring: every listed boundary side of `L` adjoins on its inside
a face of `L` whose interior meets the interior of `Q`. -/
def InsideAnchored (L : FaceGroup S) (Q : Set Pt) : Prop :=
  ∀ i : Fin L.disk.n, ∃ F ∈ L.faces,
    HasEdge F (L.disk.side i) ∧ (interior F.carrier ∩ interior Q).Nonempty

/-- Outside anchoring: every listed boundary side of `L` adjoins on its
outside a face of `S`, not in `L`, whose interior meets the open exterior of
`K`. -/
def OutsideAnchored (L : FaceGroup S) (K : Set Pt) : Prop :=
  ∀ i : Fin L.disk.n, ∃ F ∈ S, F ∉ L.faces ∧
    HasEdge F (L.disk.side i) ∧ (interior F.carrier ∩ Kᶜ).Nonempty

end FaceGroup

/-! ## Classical polygonal topology helpers -/

section JordanHelpers

open Filter Topology MeasureTheory

/-! ### Helpers for `polygonalJordanBoundary`

Planar cross products, local half-disk structure of polygonal disks, the partner and vertex
lemmas for side-to-side cellulations, a winding function for closed polygons, and the
assembly of the boundary cycle. -/

/-- cross product of planar vectors -/
private def jcr (u v : Pt) : ℝ := u 0 * v 1 - u 1 * v 0

/-- rotation by a right angle -/
private def jrot (u : Pt) : Pt := !₂[-(u 1), u 0]

@[simp] private lemma jrot_apply0 (u : Pt) : jrot u 0 = -(u 1) := by simp [jrot]
@[simp] private lemma jrot_apply1 (u : Pt) : jrot u 1 = u 0 := by simp [jrot]

private lemma jcr_add_right (u v w : Pt) : jcr u (v + w) = jcr u v + jcr u w := by
  simp [jcr]; ring

private lemma jcr_sub_right (u v w : Pt) : jcr u (v - w) = jcr u v - jcr u w := by
  simp [jcr]; ring

private lemma jcr_smul_right (u v : Pt) (c : ℝ) : jcr u (c • v) = c * jcr u v := by
  simp [jcr]; ring

private lemma jcr_smul_left (u v : Pt) (c : ℝ) : jcr (c • u) v = c * jcr u v := by
  simp [jcr]; ring

private lemma jcr_self (u : Pt) : jcr u u = 0 := by simp [jcr]; ring

private lemma jcr_anti (u v : Pt) : jcr v u = - jcr u v := by simp [jcr]; ring

private lemma norm_sq_pt (u : Pt) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]; simp [Fin.sum_univ_two]

private lemma jcr_jrot (u : Pt) : jcr u (jrot u) = ‖u‖ ^ 2 := by
  rw [norm_sq_pt]; simp [jcr]; ring

private lemma norm_jrot (u : Pt) : ‖jrot u‖ = ‖u‖ := by
  have h1 := norm_sq_pt (jrot u)
  have h2 := norm_sq_pt u
  simp at h1
  have : ‖jrot u‖ ^ 2 = ‖u‖ ^ 2 := by rw [h1, h2]; ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 this

private lemma pt_ext {u v : Pt} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i; fin_cases i <;> simp [h0, h1]

private lemma pos_of_ne_zero_pt {u : Pt} (hu : u ≠ 0) : 0 < u 0 ^ 2 + u 1 ^ 2 := by
  rw [← norm_sq_pt]; positivity

/-- vectors with zero cross product with a nonzero vector are multiples of it -/
private lemma exists_smul_of_jcr_eq_zero {u v : Pt} (hu : u ≠ 0) (h : jcr u v = 0) :
    ∃ t : ℝ, v = t • u := by
  have hp := pos_of_ne_zero_pt hu
  refine ⟨(u 0 * v 0 + u 1 * v 1) / (u 0 ^ 2 + u 1 ^ 2), ?_⟩
  unfold jcr at h
  apply pt_ext <;> simp <;> field_simp
  · linear_combination (-(u 1)) * h
  · linear_combination (u 0) * h

/-- two vectors with nonzero cross product: solve a linear system -/
private lemma exists_jcr_jcr {u w : Pt} (h : jcr u w ≠ 0) (α β : ℝ) :
    ∃ v : Pt, jcr u v = α ∧ jcr w v = β := by
  refine ⟨!₂[(α * w 0 - β * u 0) / jcr u w, (α * w 1 - β * u 1) / jcr u w], ?_, ?_⟩
  · simp only [jcr] at h ⊢; simp
    rw [show u 0 * ((α * w 1 - β * u 1) / (u 0 * w 1 - u 1 * w 0)) -
        u 1 * ((α * w 0 - β * u 0) / (u 0 * w 1 - u 1 * w 0)) =
        α * (u 0 * w 1 - u 1 * w 0) * (u 0 * w 1 - u 1 * w 0)⁻¹ by ring,
      mul_assoc, mul_inv_cancel₀ h, mul_one]
  · simp only [jcr] at h ⊢; simp
    rw [show w 0 * ((α * w 1 - β * u 1) / (u 0 * w 1 - u 1 * w 0)) -
        w 1 * ((α * w 0 - β * u 0) / (u 0 * w 1 - u 1 * w 0)) =
        β * (u 0 * w 1 - u 1 * w 0) * (u 0 * w 1 - u 1 * w 0)⁻¹ by ring,
      mul_assoc, mul_inv_cancel₀ h, mul_one]

/-! ### segments -/

private lemma mem_segment_iff' {a b x : Pt} :
    x ∈ segment ℝ a b ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = a + t • (b - a) := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨t, h0, h1, rfl⟩
  · rintro ⟨t, h0, h1, rfl⟩; exact ⟨t, ⟨h0, h1⟩, rfl⟩

private lemma mem_openSegment_iff' {a b x : Pt} :
    x ∈ openSegment ℝ a b ↔ ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = a + t • (b - a) := by
  rw [openSegment_eq_image']
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨t, h0, h1, rfl⟩
  · rintro ⟨t, h0, h1, rfl⟩; exact ⟨t, ⟨h0, h1⟩, rfl⟩

private lemma smul_cancel_pt {u : Pt} (hu : u ≠ 0) {s t : ℝ} (h : s • u = t • u) : s = t := by
  have := smul_left_injective ℝ hu h
  exact this

private lemma seg_endpoints {a b c d : Pt} (hab : a ≠ b) (h : segment ℝ a b = segment ℝ c d) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  have hc : c ∈ segment ℝ a b := h ▸ left_mem_segment ℝ c d
  have hd : d ∈ segment ℝ a b := h ▸ right_mem_segment ℝ c d
  have ha : a ∈ segment ℝ c d := h ▸ left_mem_segment ℝ a b
  have hb : b ∈ segment ℝ c d := h ▸ right_mem_segment ℝ a b
  rw [mem_segment_iff'] at hc hd ha hb
  obtain ⟨s, hs0, hs1, rfl⟩ := hc
  obtain ⟨t, ht0, ht1, rfl⟩ := hd
  obtain ⟨α, ha0, ha1, hα⟩ := ha
  obtain ⟨β, hb0, hb1, hβ⟩ := hb
  have hu : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have k1 : a + s • (b - a) + α • (a + t • (b - a) - (a + s • (b - a))) =
      a + (s + α * (t - s)) • (b - a) := by module
  have k2 : a + s • (b - a) + β • (a + t • (b - a) - (a + s • (b - a))) =
      a + (s + β * (t - s)) • (b - a) := by module
  rw [k1] at hα
  rw [k2] at hβ
  have e1 : (0 : ℝ) • (b - a) = (s + α * (t - s)) • (b - a) := by
    rw [zero_smul]; exact (add_eq_left.1 hα.symm).symm
  have e2 : (1 : ℝ) • (b - a) = (s + β * (t - s)) • (b - a) := by
    rw [one_smul]
    have : a + (b - a) = a + (s + β * (t - s)) • (b - a) := by rw [← hβ]; abel
    exact add_left_cancel this
  have f1 := smul_cancel_pt hu e1
  have f2 := smul_cancel_pt hu e2
  have key : (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    have h3 : s * (1 - α) = 0 := by nlinarith [mul_nonneg hs0 (sub_nonneg.2 ha1), mul_nonneg ha0 ht0]
    have h4 : α * t = 0 := by nlinarith [mul_nonneg hs0 (sub_nonneg.2 ha1), mul_nonneg ha0 ht0]
    rcases mul_eq_zero.1 h3 with h3 | h3
    · subst h3
      have : β * t = 1 := by linarith
      left; refine ⟨rfl, ?_⟩; nlinarith
    · have hα1 : α = 1 := by linarith
      subst hα1
      have ht : t = 0 := by linarith
      subst ht
      right; refine ⟨?_, rfl⟩; nlinarith
  rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left; constructor <;> simp
  · right; constructor <;> simp

private def pdTranslate (B : PolygonalDisk) (v : Pt) : PolygonalDisk where
  carrier := v +ᵥ B.carrier
  n := B.n
  three_le := B.three_le
  vertex := fun i => v +ᵥ B.vertex i
  vertex_injective := fun i j h => B.vertex_injective ((vadd_left_cancel_iff v).1 h)
  compact := by
    rw [← Set.image_vadd]; exact B.compact.image (continuous_const_vadd v)
  interior_nonempty := by rw [interior_vadd]; exact B.interior_nonempty.vadd_set
  regular_closed := by rw [interior_vadd, closure_vadd, B.regular_closed]
  interior_pathConnected := by
    rw [interior_vadd]
    have := B.interior_pathConnected.image (continuous_const_vadd v)
    simpa [← Set.image_vadd] using this
  frontier_eq := by
    rw [frontier, interior_vadd, closure_vadd, ← Set.vadd_set_sdiff, ← frontier, B.frontier_eq,
      Set.vadd_set_iUnion]
    simp only [vadd_segment]
  simple := by
    intro i j hij
    have h := Set.vadd_set_mono (a := v) (B.simple i j hij)
    rw [Set.vadd_set_inter, Set.vadd_set_inter] at h
    simpa [vadd_segment, Set.vadd_set_insert, Set.vadd_set_singleton] using h

private lemma isCompact_segment_pt (a b : Pt) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

private lemma finRotate_ne_self {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have h1 : (1 : Fin (m + 1)) = 0 := by
    have := congrArg (fun x => x - i) h
    simpa using this
  have : NeZero (m + 1) := ⟨by omega⟩
  rw [Fin.one_eq_zero_iff] at h1
  omega

variable (B : PolygonalDisk)

private lemma pd_vertex_ne_next (i : Fin B.n) : B.vertex i ≠ B.vertex (finRotate B.n i) := by
  intro h
  exact finRotate_ne_self (by have := B.three_le; omega) i (B.vertex_injective h).symm

private lemma pd_isClosed_carrier : IsClosed B.carrier := B.compact.isClosed

private lemma pd_segment_subset_frontier (i : Fin B.n) :
    segment ℝ (B.vertex i) (B.vertex (finRotate B.n i)) ⊆ frontier B.carrier := by
  rw [B.frontier_eq]; exact subset_iUnion (fun j => segment ℝ (B.vertex j) (B.vertex (finRotate B.n j))) i

private lemma pd_frontier_subset_carrier : frontier B.carrier ⊆ B.carrier := by
  have := frontier_subset_closure (s := B.carrier)
  rwa [(pd_isClosed_carrier B).closure_eq] at this

private lemma pd_segment_subset_carrier (i : Fin B.n) :
    segment ℝ (B.vertex i) (B.vertex (finRotate B.n i)) ⊆ B.carrier :=
  (pd_segment_subset_frontier B i).trans (pd_frontier_subset_carrier B)

private lemma pd_eq_of_openSegment_inter_segment {i j : Fin B.n} {q : Pt}
    (hq : q ∈ openSegment ℝ (B.vertex i) (B.vertex (finRotate B.n i)))
    (hq' : q ∈ segment ℝ (B.vertex j) (B.vertex (finRotate B.n j))) : j = i := by
  by_contra hji
  have h := B.simple i j (Ne.symm hji) ⟨openSegment_subset_segment ℝ _ _ hq, hq'⟩
  have hab := pd_vertex_ne_next B i
  rcases h.1 with h1 | h1
  · rw [h1] at hq; exact hab ((left_mem_openSegment_iff).1 hq)
  · rw [Set.mem_singleton_iff] at h1
    rw [h1] at hq; exact hab ((right_mem_openSegment_iff).1 hq)

private lemma pd_vertex_not_mem_openSegment (k i : Fin B.n) :
    B.vertex k ∉ openSegment ℝ (B.vertex i) (B.vertex (finRotate B.n i)) := by
  intro h
  have hk := pd_eq_of_openSegment_inter_segment B h (left_mem_segment ℝ _ _)
  subst hk
  exact pd_vertex_ne_next B k ((left_mem_openSegment_iff).1 h)

/-- local half-disk structure at a relative interior point of a side -/
private lemma pd_halfdisk (i : Fin B.n) {q : Pt}
    (hq : q ∈ openSegment ℝ (B.vertex i) (B.vertex (finRotate B.n i))) :
    ∃ r > 0, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ Metric.ball q r,
      (x ∈ segment ℝ (B.vertex i) (B.vertex (finRotate B.n i)) ↔
          jcr (B.vertex (finRotate B.n i) - B.vertex i) (x - B.vertex i) = 0) ∧
      (x ∈ B.carrier ↔ 0 ≤ σ * jcr (B.vertex (finRotate B.n i) - B.vertex i) (x - B.vertex i)) ∧
      (x ∈ interior B.carrier ↔
          0 < σ * jcr (B.vertex (finRotate B.n i) - B.vertex i) (x - B.vertex i)) := by
  set a := B.vertex i with ha_def
  set b := B.vertex (finRotate B.n i) with hb_def
  have hab : a ≠ b := pd_vertex_ne_next B i
  set d := b - a with hd_def
  have hd : d ≠ 0 := sub_ne_zero.2 hab.symm
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd
  obtain ⟨s, hs0, hs1, hqs⟩ := mem_openSegment_iff'.1 hq
  set K := ⋃ j ∈ ({i}ᶜ : Set (Fin B.n)), segment ℝ (B.vertex j) (B.vertex (finRotate B.n j))
    with hK_def
  have hKc : IsClosed K :=
    Set.Finite.isClosed_biUnion (Set.toFinite _) (fun j _ => (isCompact_segment_pt _ _).isClosed)
  have hqK : q ∉ K := by
    intro h
    simp only [hK_def, Set.mem_iUnion] at h
    obtain ⟨j, hj, hqj⟩ := h
    exact hj (pd_eq_of_openSegment_inter_segment B hq hqj)
  obtain ⟨r1, hr1, hr1K⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl q hqK
  have hm : 0 < min s (1 - s) := lt_min hs0 (by linarith)
  set r := min r1 (min s (1 - s) * ‖d‖) with hr_def
  have hr : 0 < r := lt_min hr1 (mul_pos hm hdn)
  have hrr1 : r ≤ r1 := min_le_left _ _
  have hrd : r ≤ min s (1 - s) * ‖d‖ := min_le_right _ _
  -- the cross product function
  set c : Pt → ℝ := fun x => jcr d (x - a) with hc_def
  have hcq : c q = 0 := by
    simp only [hc_def, hqs, add_sub_cancel_left, ← hd_def, jcr_smul_right, jcr_self, mul_zero]
  -- side characterisation
  have hside : ∀ x ∈ Metric.ball q r, (x ∈ segment ℝ a b ↔ c x = 0) := by
    intro x hx
    constructor
    · intro hxs
      obtain ⟨t, -, -, rfl⟩ := mem_segment_iff'.1 hxs
      simp [hc_def, ← hd_def, jcr_smul_right, jcr_self]
    · intro hcx
      obtain ⟨t, ht⟩ := exists_smul_of_jcr_eq_zero hd hcx
      have hx' : x = a + t • d := by rw [← ht]; abel
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have : x - q = (t - s) • d := by rw [hx', hqs]; module
      rw [this, norm_smul, Real.norm_eq_abs] at hx
      have h2 : |t - s| < min s (1 - s) := by
        have := lt_of_lt_of_le hx hrd
        exact (mul_lt_mul_iff_of_pos_right hdn).1 this
      have h3 := lt_of_lt_of_le h2 (min_le_left _ _)
      have h4 := lt_of_lt_of_le h2 (min_le_right _ _)
      rw [abs_lt] at h3 h4
      exact mem_segment_iff'.2 ⟨t, by linarith, by linarith, hx'⟩
  have hfront : ∀ x ∈ Metric.ball q r, (x ∈ frontier B.carrier ↔ x ∈ segment ℝ a b) := by
    intro x hx
    constructor
    · intro hxf
      rw [B.frontier_eq, Set.mem_iUnion] at hxf
      obtain ⟨j, hj⟩ := hxf
      by_cases hji : j = i
      · subst hji; exact hj
      · exfalso
        have : x ∈ K := by
          simp only [hK_def, Set.mem_iUnion]
          exact ⟨j, hji, hj⟩
        exact hr1K (Metric.ball_subset_ball hrr1 hx) this
    · intro hxs; exact pd_segment_subset_frontier B i hxs
  -- half balls
  set H : ℝ → Set Pt := fun τ => {x | x ∈ Metric.ball q r ∧ 0 < τ * c x} with hH_def
  have hHconv : ∀ τ, Convex ℝ (H τ) := by
    intro τ x hx y hy α β hα hβ hαβ
    refine ⟨(convex_ball q r) hx.1 hy.1 hα hβ hαβ, ?_⟩
    have : c (α • x + β • y) = α * c x + β * c y := by
      simp only [hc_def]
      have e : α • x + β • y - a = α • (x - a) + β • (y - a) := by
        rw [show β = 1 - α by linarith]; module
      rw [e, jcr_add_right, jcr_smul_right, jcr_smul_right]
    rw [this]
    have h1 := hx.2
    have h2 := hy.2
    rcases eq_or_lt_of_le hα with h | h
    · subst h; simp at hαβ; subst hαβ; simpa using h2
    · nlinarith [mul_pos h h1, mul_nonneg hβ h2.le]
  have hHsplit : ∀ τ, H τ ⊆ interior B.carrier ∨ H τ ⊆ (B.carrier)ᶜ := by
    intro τ
    refine (hHconv τ).isPreconnected.subset_or_subset isOpen_interior
      (pd_isClosed_carrier B).isOpen_compl ?_ ?_
    · rw [Set.disjoint_iff]; intro x ⟨h1, h2⟩; exact h2 (interior_subset h1)
    · intro x hx
      by_cases hxc : x ∈ B.carrier
      · left
        by_contra hxi
        have hxf : x ∈ frontier B.carrier := by
          rw [← self_diff_frontier] at hxi
          by_contra hh; exact hxi ⟨hxc, hh⟩
        have := (hside x hx.1).1 ((hfront x hx.1).1 hxf)
        have h2 := hx.2
        rw [this, mul_zero] at h2; exact lt_irrefl _ h2
      · right; exact hxc
  -- approximation of points on the line by points of the half balls
  have hcJ : ∀ (y : Pt) (δ : ℝ), c (y + δ • jrot d) = c y + δ * ‖d‖ ^ 2 := by
    intro y δ
    simp only [hc_def]
    rw [show y + δ • jrot d - a = (y - a) + δ • jrot d by abel, jcr_add_right, jcr_smul_right,
      jcr_jrot]
  have happrox : ∀ x ∈ Metric.ball q r, c x = 0 → ∀ τ, (τ = 1 ∨ τ = -1) →
      ∀ ε > 0, ∃ y ∈ H τ, dist x y < ε := by
    intro x hx hcx τ hτ ε hε
    have hxq : 0 < r - dist x q := by rw [Metric.mem_ball] at hx; linarith
    set δ := min ε (r - dist x q) / (2 * ‖d‖) with hδ
    have hδpos : 0 < δ := div_pos (lt_min hε hxq) (by positivity)
    set y := x + (τ * δ) • jrot d with hy_def
    have hτabs : |τ| = 1 := by rcases hτ with rfl | rfl <;> norm_num
    have hτ2 : τ * τ = 1 := by rcases hτ with rfl | rfl <;> norm_num
    have hdist : dist x y = δ * ‖d‖ := by
      rw [dist_eq_norm, show x - y = -((τ * δ) • jrot d) by rw [hy_def]; abel, norm_neg,
        norm_smul, norm_jrot, Real.norm_eq_abs, abs_mul, hτabs, abs_of_pos hδpos, one_mul]
    have hδd : δ * ‖d‖ = min ε (r - dist x q) / 2 := by
      rw [hδ]; field_simp
    refine ⟨y, ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball]
      calc dist y q ≤ dist y x + dist x q := dist_triangle _ _ _
        _ < r := by
          rw [dist_comm, hdist, hδd]
          have := min_le_right ε (r - dist x q)
          linarith
    · rw [hy_def, hcJ, hcx]
      have : τ * (0 + τ * δ * ‖d‖ ^ 2) = (τ * τ) * (δ * ‖d‖ ^ 2) := by ring
      rw [this, hτ2, one_mul]; positivity
    · rw [hdist, hδd]
      have := min_le_left ε (r - dist x q)
      linarith
  have hqint : q ∉ interior B.carrier := by
    have := pd_segment_subset_frontier B i (openSegment_subset_segment ℝ _ _ hq)
    exact fun h => this.2 h
  have hqc : q ∈ B.carrier := pd_segment_subset_carrier B i (openSegment_subset_segment ℝ _ _ hq)
  have hnotboth : ¬ (H 1 ⊆ interior B.carrier ∧ H (-1) ⊆ interior B.carrier) := by
    rintro ⟨h1, h2⟩
    apply hqint
    rw [mem_interior_iff_mem_nhds]
    apply Filter.mem_of_superset (Metric.ball_mem_nhds q hr)
    intro x hx
    rcases lt_trichotomy (c x) 0 with hlt | heq | hgt
    · exact interior_subset (h2 ⟨hx, by linarith⟩)
    · rw [← (pd_isClosed_carrier B).closure_eq, Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨y, hy, hxy⟩ := happrox x hx heq 1 (Or.inl rfl) ε hε
      exact ⟨y, interior_subset (h1 hy), hxy⟩
    · exact interior_subset (h1 ⟨hx, by linarith⟩)
  have hnotnone : ¬ (H 1 ⊆ B.carrierᶜ ∧ H (-1) ⊆ B.carrierᶜ) := by
    rintro ⟨h1, h2⟩
    have hq' := hqc
    rw [← B.regular_closed, Metric.mem_closure_iff] at hq'
    obtain ⟨y, hyi, hqy⟩ := hq' r hr
    have hyb : y ∈ Metric.ball q r := by rw [Metric.mem_ball, dist_comm]; exact hqy
    obtain ⟨ε, hε, hεi⟩ := Metric.isOpen_iff.1 isOpen_interior y hyi
    rcases lt_trichotomy (c y) 0 with hlt | heq | hgt
    · exact h2 ⟨hyb, by linarith⟩ (interior_subset hyi)
    · obtain ⟨z, hz, hyz⟩ := happrox y hyb heq 1 (Or.inl rfl) ε hε
      exact h1 hz (interior_subset (hεi (by rw [Metric.mem_ball, dist_comm]; exact hyz)))
    · exact h1 ⟨hyb, by linarith⟩ (interior_subset hyi)
  have key : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ H σ ⊆ interior B.carrier ∧ H (-σ) ⊆ B.carrierᶜ := by
    rcases hHsplit 1 with h1 | h1 <;> rcases hHsplit (-1) with h2 | h2
    · exact absurd ⟨h1, h2⟩ hnotboth
    · exact ⟨1, Or.inl rfl, h1, h2⟩
    · exact ⟨-1, Or.inr rfl, h2, by simpa using h1⟩
    · exact absurd ⟨h1, h2⟩ hnotnone
  obtain ⟨σ, hσ, hint, hext⟩ := key
  refine ⟨r, hr, σ, hσ, fun x hx => ⟨hside x hx, ?_, ?_⟩⟩
  · have hcx : c x = jcr d (x - a) := rfl
    rw [← hcx]
    constructor
    · intro hxc
      by_contra hneg
      push_neg at hneg
      exact hext ⟨hx, by linarith⟩ hxc
    · intro h
      rcases eq_or_lt_of_le h with h0 | hpos
      · have : c x = 0 := by rcases hσ with rfl | rfl <;> linarith
        exact pd_frontier_subset_carrier B ((hfront x hx).2 ((hside x hx).2 this))
      · exact interior_subset (hint ⟨hx, hpos⟩)
  · have hcx : c x = jcr d (x - a) := rfl
    rw [← hcx]
    constructor
    · intro hxi
      by_contra hneg
      push_neg at hneg
      rcases eq_or_lt_of_le hneg with h0 | hneg'
      · have : c x = 0 := by rcases hσ with rfl | rfl <;> linarith
        exact ((hfront x hx).2 ((hside x hx).2 this)).2 hxi
      · exact hext ⟨hx, by linarith⟩ (interior_subset hxi)
    · intro hpos; exact hint ⟨hx, hpos⟩

/-- the polygonal disk of a placed tile -/
private def tileDisk (A : PlacedTile P) : PolygonalDisk := pdTranslate (P.disk A.form) A.anchor

private lemma tile_side_eq (A : PlacedTile P) (i : Fin (P.disk A.form).n) :
    A.side i = segment ℝ (A.vertex i) (A.vertex (finRotate _ i)) := by
  simp [PlacedTile.side, PolygonalDisk.side, PlacedTile.vertex, vadd_segment]

private lemma tile_isClosed (A : PlacedTile P) : IsClosed A.carrier := pd_isClosed_carrier (tileDisk A)

private lemma tile_side_subset (A : PlacedTile P) (i : Fin (P.disk A.form).n) :
    A.side i ⊆ A.carrier := by
  rw [tile_side_eq]; exact pd_segment_subset_carrier (tileDisk A) i

private lemma tile_side_subset_frontier (A : PlacedTile P) (i : Fin (P.disk A.form).n) :
    A.side i ⊆ frontier A.carrier := by
  rw [tile_side_eq]; exact pd_segment_subset_frontier (tileDisk A) i

private lemma tile_frontier_eq (A : PlacedTile P) :
    frontier A.carrier = ⋃ i, A.side i := by
  simp_rw [tile_side_eq]; exact (tileDisk A).frontier_eq

private lemma tile_regular (A : PlacedTile P) : closure (interior A.carrier) = A.carrier :=
  (tileDisk A).regular_closed

private lemma tile_vertex_ne_next (A : PlacedTile P) (i : Fin (P.disk A.form).n) :
    A.vertex i ≠ A.vertex (finRotate _ i) := pd_vertex_ne_next (tileDisk A) i

private lemma tile_vertex_not_mem_openSegment (A : PlacedTile P) (k i : Fin (P.disk A.form).n) :
    A.vertex k ∉ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)) :=
  pd_vertex_not_mem_openSegment (tileDisk A) k i

private lemma tile_eq_of_openSegment_inter_segment (A : PlacedTile P) {i j : Fin (P.disk A.form).n}
    {q : Pt} (hq : q ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)))
    (hq' : q ∈ A.side j) : j = i := by
  rw [tile_side_eq] at hq'
  exact pd_eq_of_openSegment_inter_segment (tileDisk A) hq hq'

private lemma tile_halfdisk (A : PlacedTile P) (i : Fin (P.disk A.form).n) {q : Pt}
    (hq : q ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i))) :
    ∃ r > 0, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ Metric.ball q r,
      (x ∈ A.side i ↔ jcr (A.vertex (finRotate _ i) - A.vertex i) (x - A.vertex i) = 0) ∧
      (x ∈ A.carrier ↔ 0 ≤ σ * jcr (A.vertex (finRotate _ i) - A.vertex i) (x - A.vertex i)) ∧
      (x ∈ interior A.carrier ↔
          0 < σ * jcr (A.vertex (finRotate _ i) - A.vertex i) (x - A.vertex i)) := by
  rw [tile_side_eq]; exact pd_halfdisk (tileDisk A) i hq

/-- moving off a line in a prescribed direction -/
private lemma exists_near_off_line (a : Pt) {d : Pt} (hd : d ≠ 0) (x : Pt) {τ : ℝ}
    (hτ : τ = 1 ∨ τ = -1) {ε : ℝ} (hε : 0 < ε) :
    ∃ y, dist x y < ε ∧ τ * jcr d (x - a) < τ * jcr d (y - a) := by
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd
  set δ := ε / (2 * ‖d‖) with hδ
  have hδpos : 0 < δ := div_pos hε (by positivity)
  have hτabs : |τ| = 1 := by rcases hτ with rfl | rfl <;> norm_num
  have hτ2 : τ * τ = 1 := by rcases hτ with rfl | rfl <;> norm_num
  refine ⟨x + (τ * δ) • jrot d, ?_, ?_⟩
  · rw [dist_eq_norm, show x - (x + (τ * δ) • jrot d) = -((τ * δ) • jrot d) by abel, norm_neg,
      norm_smul, norm_jrot, Real.norm_eq_abs, abs_mul, hτabs, abs_of_pos hδpos, one_mul, hδ]
    field_simp
    linarith
  · rw [show x + (τ * δ) • jrot d - a = (x - a) + (τ * δ) • jrot d by abel, jcr_add_right,
      jcr_smul_right, jcr_jrot]
    have : τ * (jcr d (x - a) + τ * δ * ‖d‖ ^ 2) = τ * jcr d (x - a) + (τ * τ) * δ * ‖d‖ ^ 2 := by
      ring
    rw [this, hτ2]
    have : 0 < 1 * δ * ‖d‖ ^ 2 := by positivity
    linarith

private lemma interiors_disjoint {S : Set (PlacedTile P)} (hdisj : DisjointInteriors S) {A B : PlacedTile P}
    (hA : A ∈ S) (hB : B ∈ S) (hne : A ≠ B) {x : Pt} (hxA : x ∈ interior A.carrier)
    (hxB : x ∈ interior B.carrier) : False := by
  have := hdisj hA hB hne
  exact Set.disjoint_left.1 this hxA hxB

/-- **Partner lemma.**  A tile containing a relative interior point of a side of another tile,
not as a vertex, has that whole side as one of its sides. -/
private lemma tile_partner {S : Set (PlacedTile P)} (hdisj : DisjointInteriors S) (hsts : SideToSideSet S)
    {A A' : PlacedTile P} (hA : A ∈ S) (hA' : A' ∈ S) (hne : A ≠ A') (i : Fin (P.disk A.form).n)
    {q : Pt} (hq : q ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)))
    (hqA' : q ∈ A'.carrier) (hqv : q ∉ A'.vertexSet) : ∃ j, A'.side j = A.side i := by
  obtain ⟨r, hr, σ, hσ, hch⟩ := tile_halfdisk A i hq
  set a := A.vertex i
  set b := A.vertex (finRotate _ i)
  have hd : b - a ≠ 0 := sub_ne_zero.2 (tile_vertex_ne_next A i).symm
  have hqside : q ∈ A.side i := by
    rw [tile_side_eq]; exact openSegment_subset_segment ℝ _ _ hq
  have hcq : jcr (b - a) (q - a) = 0 := ((hch q (Metric.mem_ball_self hr)).1).1 hqside
  -- q is not interior to A'
  have hqnint : q ∉ interior A'.carrier := by
    intro hqi
    obtain ⟨ε, hε, hεi⟩ := Metric.isOpen_iff.1 isOpen_interior q hqi
    obtain ⟨y, hy, hyc⟩ := exists_near_off_line a hd q hσ (lt_min hε hr)
    rw [hcq, mul_zero] at hyc
    have hyb : y ∈ Metric.ball q r := by
      rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hy (min_le_right _ _)
    have hyA : y ∈ interior A.carrier := ((hch y hyb).2.2).2 hyc
    have hyA' : y ∈ interior A'.carrier := hεi (by
      rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hy (min_le_left _ _))
    exact interiors_disjoint hdisj hA hA' hne hyA hyA'
  have hqf : q ∈ frontier A'.carrier := by
    rw [← (tile_isClosed A').closure_eq] at hqA'
    exact ⟨hqA', hqnint⟩
  rw [tile_frontier_eq, Set.mem_iUnion] at hqf
  obtain ⟨j, hj⟩ := hqf
  refine ⟨j, ?_⟩
  set a' := A'.vertex j
  set b' := A'.vertex (finRotate _ j)
  have hq' : q ∈ openSegment ℝ a' b' := by
    rw [tile_side_eq] at hj
    refine mem_openSegment_of_ne_left_right ?_ ?_ hj
    · intro h; exact hqv ⟨j, h⟩
    · intro h; exact hqv ⟨_, h⟩
  obtain ⟨r', hr', σ', hσ', hch'⟩ := tile_halfdisk A' j hq'
  have hd' : b' - a' ≠ 0 := sub_ne_zero.2 (tile_vertex_ne_next A' j).symm
  have hcq' : jcr (b' - a') (q - a') = 0 := ((hch' q (Metric.mem_ball_self hr')).1).1 hj
  -- the two sides are parallel
  have hpar : jcr (b - a) (b' - a') = 0 := by
    by_contra hne0
    obtain ⟨v, hv1, hv2⟩ := exists_jcr_jcr hne0 σ σ'
    set ρ := min r r' with hρ
    have hρpos : 0 < ρ := lt_min hr hr'
    set t := ρ / (2 * (‖v‖ + 1)) with ht
    have htpos : 0 < t := div_pos hρpos (by positivity)
    have htv : t * ‖v‖ < ρ := by
      rw [ht]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg v]
    set x := q + t • v
    have hxq : dist x q < ρ := by
      simp only [x, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos htpos]
      exact htv
    have hxb : x ∈ Metric.ball q r := lt_of_lt_of_le hxq (min_le_left _ _)
    have hxb' : x ∈ Metric.ball q r' := lt_of_lt_of_le hxq (min_le_right _ _)
    have e1 : jcr (b - a) (x - a) = t * σ := by
      simp only [x]
      rw [show q + t • v - a = (q - a) + t • v by abel, jcr_add_right, jcr_smul_right, hcq, hv1]
      ring
    have e2 : jcr (b' - a') (x - a') = t * σ' := by
      simp only [x]
      rw [show q + t • v - a' = (q - a') + t • v by abel, jcr_add_right, jcr_smul_right, hcq', hv2]
      ring
    have hxA : x ∈ interior A.carrier := by
      rw [((hch x hxb).2.2), e1]
      rcases hσ with h | h <;> rw [h] <;> nlinarith
    have hxA' : x ∈ interior A'.carrier := by
      rw [((hch' x hxb').2.2), e2]
      rcases hσ' with h | h <;> rw [h] <;> nlinarith
    exact interiors_disjoint hdisj hA hA' hne hxA hxA'
  -- overlap of positive length
  apply (hsts A hA A' hA' i j _).symm
  set ρ := min r r' with hρ
  have hρpos : 0 < ρ := lt_min hr hr'
  have hdn : 0 < ‖b - a‖ := norm_pos_iff.2 hd
  set t := ρ / (2 * ‖b - a‖) with ht
  have htpos : 0 < t := div_pos hρpos (by positivity)
  have htd : t * ‖b - a‖ < ρ := by
    rw [ht]; field_simp; linarith
  have hmem : ∀ τ : ℝ, (τ = t ∨ τ = -t) → q + τ • (b - a) ∈ A.side i ∩ A'.side j := by
    intro τ hτ
    have hτn : |τ| = t := by rcases hτ with rfl | rfl <;> simp [abs_of_pos htpos]
    have hxq : dist (q + τ • (b - a)) q < ρ := by
      simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hτn]
      exact htd
    have hxb : q + τ • (b - a) ∈ Metric.ball q r := lt_of_lt_of_le hxq (min_le_left _ _)
    have hxb' : q + τ • (b - a) ∈ Metric.ball q r' := lt_of_lt_of_le hxq (min_le_right _ _)
    refine ⟨((hch _ hxb).1).2 ?_, ((hch' _ hxb').1).2 ?_⟩
    · rw [show q + τ • (b - a) - a = (q - a) + τ • (b - a) by abel, jcr_add_right, jcr_smul_right,
        hcq, jcr_self]; ring
    · rw [show q + τ • (b - a) - a' = (q - a') + τ • (b - a) by abel, jcr_add_right,
        jcr_smul_right, hcq', jcr_anti, hpar]; ring
  refine ⟨q + (-t) • (b - a), q + t • (b - a), ?_, ?_⟩
  · intro h
    have h2 : (-t) • (b - a) = t • (b - a) := add_left_cancel h
    have := smul_cancel_pt hd h2
    linarith
  · have hc : Convex ℝ (A.side i ∩ A'.side j) := by
      rw [tile_side_eq, tile_side_eq]; exact (convex_segment _ _).inter (convex_segment _ _)
    exact hc.segment_subset (hmem _ (Or.inr rfl)) (hmem _ (Or.inl rfl))

/-- tiles with disjoint interiors are locally finite -/
private lemma tiles_locally_finite {S : Set (PlacedTile P)} (hdisj : DisjointInteriors S) (x : Pt)
    (R : ℝ) : {A ∈ S | (A.carrier ∩ Metric.ball x R).Nonempty}.Finite := by
  classical
  have hb : ∀ p : P.Form, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ (P.disk p).carrier, ‖y‖ ≤ C := by
    intro p
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (P.disk p).compact.isBounded
    exact ⟨max C 0, le_max_right _ _, fun y hy => (hC y hy).trans (le_max_left _ _)⟩
  choose C hC0 hC using hb
  set D := ∑ p, C p with hD
  have hCD : ∀ p, C p ≤ D := fun p =>
    Finset.single_le_sum (f := C) (fun p _ => hC0 p) (Finset.mem_univ p)
  set T := {A ∈ S | (A.carrier ∩ Metric.ball x R).Nonempty} with hT
  have hsub : ∀ A ∈ T, A.carrier ⊆ Metric.ball x (R + 2 * D + 1) := by
    rintro A ⟨-, y, hyA, hyB⟩ z hz
    obtain ⟨y0, hy0, rfl⟩ := Set.mem_vadd_set.1 hyA
    obtain ⟨z0, hz0, rfl⟩ := Set.mem_vadd_set.1 hz
    have h1 := (hC _ y0 hy0).trans (hCD _)
    have h2 := (hC _ z0 hz0).trans (hCD _)
    rw [Metric.mem_ball] at hyB ⊢
    calc dist (A.anchor +ᵥ z0) x ≤ dist (A.anchor +ᵥ z0) (A.anchor +ᵥ y0) + dist (A.anchor +ᵥ y0) x :=
          dist_triangle _ _ _
      _ < R + 2 * D + 1 := by
        have : dist (A.anchor +ᵥ z0) (A.anchor +ᵥ y0) ≤ 2 * D := by
          rw [vadd_eq_add, vadd_eq_add, dist_add_left, dist_eq_norm]
          calc ‖z0 - y0‖ ≤ ‖z0‖ + ‖y0‖ := norm_sub_le _ _
            _ ≤ 2 * D := by linarith
        linarith
  have hTU : T = ⋃ p : P.Form, {A ∈ T | A.form = p} := by
    ext A; simp
  rw [hTU]
  refine Set.finite_iUnion (fun p => ?_)
  by_contra hinf
  set m := volume (interior (P.disk p).carrier) with hm
  have hmpos : 0 < m := isOpen_interior.measure_pos volume (P.disk p).interior_nonempty
  set V := volume (Metric.ball x (R + 2 * D + 1)) with hV
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hmpos.ne' hVtop
  obtain ⟨t, hts, htc⟩ := (Set.not_finite.1 hinf).exists_subset_card_eq n
  have htS : (↑t : Set (PlacedTile P)) ⊆ S := fun A hA => (hts hA).1.1
  have hdisj' : (↑t : Set (PlacedTile P)).PairwiseDisjoint (fun A => interior A.carrier) :=
    hdisj.subset htS
  have hmeas := measure_biUnion_finset (μ := volume) hdisj' (fun A _ => isOpen_interior.measurableSet)
  have hvolA : ∀ A ∈ t, volume (interior A.carrier) = m := by
    intro A hA
    have hform : A.form = p := (hts hA).2
    rw [PlacedTile.carrier, interior_vadd, measure_vadd, hm, hform]
  rw [Finset.sum_congr rfl hvolA, Finset.sum_const, htc, nsmul_eq_mul] at hmeas
  have hle : volume (⋃ A ∈ t, interior A.carrier) ≤ V := by
    apply measure_mono
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨A, hA, hzA⟩ := hz
    exact hsub A (hts hA).1 (interior_subset hzA)
  rw [hmeas] at hle
  exact absurd hn (not_lt.2 hle)

/-- **Vertex lemma.**  In a side-to-side cellulation, no vertex lies in the relative interior
of a side, at points interior to the covered region. -/
private lemma vertex_not_mem_open_side {S : Set (PlacedTile P)} (hdisj : DisjointInteriors S)
    (hsts : SideToSideSet S) {A C : PlacedTile P} (hA : A ∈ S) (hC : C ∈ S)
    (i : Fin (P.disk A.form).n) {v : Pt}
    (hv : v ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)))
    (hvC : v ∈ C.vertexSet) (hvS : v ∈ interior (support S)) : False := by
  classical
  obtain ⟨r, hr, σ, hσ, hch⟩ := tile_halfdisk A i hv
  set a := A.vertex i with ha
  set b := A.vertex (finRotate _ i) with hb
  have hd : b - a ≠ 0 := sub_ne_zero.2 (tile_vertex_ne_next A i).symm
  have hdn : 0 < ‖b - a‖ := norm_pos_iff.2 hd
  obtain ⟨s, hs0, hs1, hvs⟩ := mem_openSegment_iff'.1 hv
  have hcv : jcr (b - a) (v - a) = 0 := by
    rw [hvs, add_sub_cancel_left, jcr_smul_right, jcr_self, mul_zero]
  obtain ⟨ρ, hρ, hρS⟩ := Metric.isOpen_iff.1 isOpen_interior v hvS
  set T := {D ∈ S | (D.carrier ∩ Metric.ball v r).Nonempty} with hT
  have hTf : T.Finite := tiles_locally_finite hdisj v r
  set Vf := ⋃ D ∈ T, D.vertexSet with hVf
  have hVff : Vf.Finite := hTf.biUnion (fun D _ => Set.finite_range _)
  set ρ0 := min r ρ with hρ0
  have hρ0pos : 0 < ρ0 := lt_min hr hρ
  set t0 := min ((1 - s) / 2) (ρ0 / (2 * ‖b - a‖)) with ht0
  have ht0pos : 0 < t0 := lt_min (by linarith) (div_pos hρ0pos (by positivity))
  set f : ℕ → Pt := fun k => v + (t0 / ((k : ℝ) + 2)) • (b - a) with hf
  have hfinj : Function.Injective f := by
    intro k l h
    have h1 := smul_cancel_pt hd (add_left_cancel h)
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hl : (0 : ℝ) < (l : ℝ) + 2 := by positivity
    rw [div_eq_div_iff hk.ne' hl.ne'] at h1
    have : (k : ℝ) = l := by
      have := mul_left_cancel₀ ht0pos.ne' (show t0 * ((l : ℝ) + 2) = t0 * ((k : ℝ) + 2) by linarith)
      linarith
    exact_mod_cast this
  obtain ⟨q, ⟨k, rfl⟩, hqV⟩ := (Set.infinite_range_of_injective hfinj).exists_notMem_finite hVff
  set tk := t0 / ((k : ℝ) + 2) with htk
  have htk0 : 0 < tk := div_pos ht0pos (by positivity)
  have htk1 : tk ≤ t0 / 2 := by
    rw [htk]; apply div_le_div_of_nonneg_left ht0pos.le (by norm_num)
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have ht0a : t0 ≤ (1 - s) / 2 := min_le_left _ _
  have ht0b : t0 ≤ ρ0 / (2 * ‖b - a‖) := min_le_right _ _
  have hq_open : f k ∈ openSegment ℝ a b := by
    refine mem_openSegment_iff'.2 ⟨s + tk, by linarith, by linarith, ?_⟩
    simp only [hf]; rw [hvs]; module
  have hqv : dist (f k) v ≤ ρ0 / 4 := by
    simp only [hf, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    rw [← htk, abs_of_pos htk0]
    have : tk * ‖b - a‖ ≤ ρ0 / (2 * ‖b - a‖) / 2 * ‖b - a‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); linarith
    calc tk * ‖b - a‖ ≤ ρ0 / (2 * ‖b - a‖) / 2 * ‖b - a‖ := this
      _ = ρ0 / 4 := by field_simp; ring
  have hcq : jcr (b - a) (f k - a) = 0 := by
    have hq_seg : f k ∈ A.side i := by
      rw [tile_side_eq]; exact openSegment_subset_segment ℝ _ _ hq_open
    have hqb : f k ∈ Metric.ball v r := by
      rw [Metric.mem_ball]; have := min_le_left r ρ; linarith
    exact ((hch _ hqb).1).1 hq_seg
  -- a tile other than `A` contains `f k`
  set K' := ⋃ D ∈ T \ {A}, D.carrier with hK'
  have hK'c : IsClosed K' := (hTf.diff).isClosed_biUnion (fun D _ => tile_isClosed D)
  have hσn : -σ = 1 ∨ -σ = -1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hqK' : f k ∈ K' := by
    rw [← hK'c.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨y, hy, hyc⟩ := exists_near_off_line a hd (f k) hσn (lt_min hε (half_pos hρ0pos))
    rw [hcq, mul_zero] at hyc
    have hyv : dist y v < ρ0 := by
      calc dist y v ≤ dist y (f k) + dist (f k) v := dist_triangle _ _ _
        _ < ρ0 / 2 + ρ0 / 4 + ρ0 / 4 := by
          rw [dist_comm]; have := lt_of_lt_of_le hy (min_le_right _ _); linarith
        _ = ρ0 := by ring
    have hyS : y ∈ support S :=
      interior_subset (hρS (lt_of_lt_of_le hyv (min_le_right _ _)))
    have hyb : y ∈ Metric.ball v r := lt_of_lt_of_le hyv (min_le_left _ _)
    obtain ⟨D, hD, hyD⟩ : ∃ D ∈ S, y ∈ D.carrier := by
      simpa [support] using hyS
    have hyA : y ∉ A.carrier := by
      rw [(hch y hyb).2.1]; push_neg; linarith
    refine ⟨y, ?_, lt_of_lt_of_le hy (min_le_left _ _)⟩
    simp only [hK', Set.mem_iUnion]
    refine ⟨D, ⟨⟨hD, y, hyD, hyb⟩, ?_⟩, hyD⟩
    rintro rfl; exact hyA hyD
  simp only [hK', Set.mem_iUnion] at hqK'
  obtain ⟨D, ⟨hDT, hDA⟩, hqD⟩ := hqK'
  have hDS : D ∈ S := hDT.1
  have hAD : A ≠ D := fun h => hDA (h ▸ rfl)
  have hqDv : f k ∉ D.vertexSet := fun h => hqV (Set.mem_biUnion hDT h)
  obtain ⟨j, hj⟩ := tile_partner hdisj hsts hA hDS hAD i hq_open hqD hqDv
  rw [tile_side_eq, tile_side_eq] at hj
  have hends := seg_endpoints (tile_vertex_ne_next A i) hj.symm
  have hvD : v ∈ openSegment ℝ (D.vertex j) (D.vertex (finRotate _ j)) := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hv
    · rw [h1, h2, openSegment_symm]; exact hv
  obtain ⟨rD, hrD, σD, hσD, hchD⟩ := tile_halfdisk D j hvD
  have hrel : ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ ∀ x,
      jcr (D.vertex (finRotate _ j) - D.vertex j) (x - D.vertex j) = e * jcr (b - a) (x - a) := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨1, Or.inl rfl, fun x => by rw [h1, h2, one_mul]⟩
    · refine ⟨-1, Or.inr rfl, fun x => ?_⟩
      rw [h1, h2]; simp only [jcr]; simp; ring
  obtain ⟨e, he, hrelx⟩ := hrel
  have hσ2 : σD * e = 1 ∨ σD * e = -1 := by
    rcases hσD with h | h <;> rcases he with h' | h' <;> rw [h, h'] <;> norm_num
  have hintD : ∀ x ∈ Metric.ball v rD,
      (x ∈ interior D.carrier ↔ 0 < (σD * e) * jcr (b - a) (x - a)) := by
    intro x hx; rw [(hchD x hx).2.2, hrelx, mul_assoc]
  have hσ2' : σD * e = -σ := by
    by_contra hne
    have heq : σD * e = σ := by
      rcases hσ with h | h <;> rcases hσ2 with h' | h' <;> rw [h'] at hne ⊢ <;> rw [h] at hne ⊢ <;>
        (try norm_num at hne)
    obtain ⟨y, hy, hyc⟩ := exists_near_off_line a hd v hσ (lt_min hr hrD)
    rw [hcv, mul_zero] at hyc
    have hyb : y ∈ Metric.ball v r := by
      rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hy (min_le_left _ _)
    have hyb' : y ∈ Metric.ball v rD := by
      rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hy (min_le_right _ _)
    have hyA : y ∈ interior A.carrier := ((hch y hyb).2.2).2 hyc
    have hyD : y ∈ interior D.carrier := (hintD y hyb').2 (by rw [heq]; exact hyc)
    exact interiors_disjoint hdisj hA hDS hAD hyA hyD
  obtain ⟨k', hk'⟩ := hvC
  have hCA : C ≠ A := by
    rintro rfl; exact tile_vertex_not_mem_openSegment C k' i (hk' ▸ hv)
  have hCD : C ≠ D := by
    rintro rfl; exact tile_vertex_not_mem_openSegment C k' j (hk' ▸ hvD)
  have hvCc : v ∈ C.carrier := by
    rw [← hk']; apply tile_side_subset C k'
    rw [tile_side_eq]; exact left_mem_segment ℝ _ _
  rw [← tile_regular C, Metric.mem_closure_iff] at hvCc
  set ρ1 := min r rD with hρ1
  have hρ1pos : 0 < ρ1 := lt_min hr hrD
  obtain ⟨y, hyC, hvy⟩ := hvCc (ρ1 / 2) (half_pos hρ1pos)
  have hz : ∃ z ∈ interior C.carrier, dist v z < ρ1 ∧ jcr (b - a) (z - a) ≠ 0 := by
    by_cases hcy : jcr (b - a) (y - a) = 0
    · obtain ⟨ε1, hε1, hε1C⟩ := Metric.isOpen_iff.1 isOpen_interior y hyC
      obtain ⟨y', hy', hy'c⟩ := exists_near_off_line a hd y hσ (lt_min hε1 (half_pos hρ1pos))
      refine ⟨y', hε1C ?_, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hy' (min_le_left _ _)
      · calc dist v y' ≤ dist v y + dist y y' := dist_triangle _ _ _
          _ < ρ1 / 2 + ρ1 / 2 := add_lt_add hvy (lt_of_lt_of_le hy' (min_le_right _ _))
          _ = ρ1 := by ring
      · intro h0; rw [hcy, h0] at hy'c; simp at hy'c
    · exact ⟨y, hyC, by linarith, hcy⟩
  obtain ⟨z, hzC, hvz, hcz⟩ := hz
  have hzb : z ∈ Metric.ball v r := by
    rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hvz (min_le_left _ _)
  have hzb' : z ∈ Metric.ball v rD := by
    rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hvz (min_le_right _ _)
  rcases lt_or_gt_of_ne (mul_ne_zero (show σ ≠ 0 by rcases hσ with h | h <;> rw [h] <;> norm_num)
    hcz) with hneg | hpos
  · have hzD : z ∈ interior D.carrier := (hintD z hzb').2 (by rw [hσ2']; linarith)
    exact interiors_disjoint hdisj hC hDS hCD hzC hzD
  · have hzA : z ∈ interior A.carrier := ((hch z hzb).2.2).2 hpos
    exact interiors_disjoint hdisj hC hA hCA hzC hzA

/-- planar points as complex numbers -/
private def toC (x : Pt) : ℂ := ⟨x 0, x 1⟩

private lemma toC_sub (x y : Pt) : toC (x - y) = toC x - toC y := by
  apply Complex.ext <;> simp [toC]

private lemma toC_add (x y : Pt) : toC (x + y) = toC x + toC y := by
  apply Complex.ext <;> simp [toC]

private lemma toC_smul (t : ℝ) (x : Pt) : toC (t • x) = (t : ℂ) * toC x := by
  apply Complex.ext <;> simp [toC]

private lemma toC_jrot (x : Pt) : toC (jrot x) = Complex.I * toC x := by
  apply Complex.ext <;> simp [toC]

private lemma toC_injective : Function.Injective toC := by
  intro x y h
  have h0 := congrArg Complex.re h
  have h1 := congrArg Complex.im h
  simp [toC] at h0 h1
  exact pt_ext h0 h1

private lemma continuous_toC : Continuous toC := by
  have : toC = fun x => ((x 0 : ℝ) : ℂ) + ((x 1 : ℝ) : ℂ) * Complex.I := by
    funext x; apply Complex.ext <;> simp [toC]
  rw [this]; fun_prop

/-- the ratio used to measure the angle subtended by a segment -/
private def segRatio (a b p : Pt) : ℂ := (toC b - toC p) / (toC a - toC p)

private lemma segRatio_mem_slitPlane {a b p : Pt} (hp : p ∉ segment ℝ a b) :
    segRatio a b p ∈ Complex.slitPlane := by
  have hap : toC a - toC p ≠ 0 := by
    intro h; apply hp; rw [sub_eq_zero] at h; rw [toC_injective h]; exact left_mem_segment ℝ _ _
  rw [Complex.mem_slitPlane_iff]
  by_contra hcon
  push_neg at hcon
  obtain ⟨hre, him⟩ := hcon
  set z := segRatio a b p with hz
  have hzr : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
  have hB : toC b - toC p = (z.re : ℂ) * (toC a - toC p) := by
    rw [← hzr, hz, segRatio, div_mul_cancel₀ _ hap]
  have hB' : b - p = z.re • (a - p) := by
    apply toC_injective; rw [toC_sub, toC_smul, toC_sub, hB]
  apply hp
  rw [mem_segment_iff']
  have h1 : 0 < 1 - z.re := by linarith
  refine ⟨1 / (1 - z.re), by positivity, ?_, ?_⟩
  · rw [div_le_one h1]; linarith
  · have : b - a = (z.re - 1) • (a - p) := by
      rw [show b - a = (b - p) - (a - p) by abel, hB', sub_smul, one_smul]
    rw [this, smul_smul]
    have : 1 / (1 - z.re) * (z.re - 1) = -1 := by field_simp; ring
    rw [this, neg_one_smul]; abel

private lemma continuousAt_segRatio {a b p : Pt} (hp : p ≠ a) : ContinuousAt (segRatio a b) p := by
  unfold segRatio
  apply ContinuousAt.div
  · exact (continuous_const.sub continuous_toC).continuousAt
  · exact (continuous_const.sub continuous_toC).continuousAt
  · intro h; rw [sub_eq_zero] at h; exact hp (toC_injective h).symm

/-- the closed polygonal curve through the points `c` -/
private def polyCurve {m : ℕ} (c : Fin m → Pt) : Set Pt := ⋃ k, segment ℝ (c k) (c (finRotate m k))

/-- the winding function (times `2π`) of a closed polygon -/
private def wind {m : ℕ} (c : Fin m → Pt) (p : Pt) : ℝ :=
  ∑ k, Complex.arg (segRatio (c k) (c (finRotate m k)) p)

private lemma not_mem_seg_of_not_mem_curve {m : ℕ} {c : Fin m → Pt} {p : Pt} (hp : p ∉ polyCurve c)
    (k : Fin m) : p ∉ segment ℝ (c k) (c (finRotate m k)) := by
  intro h; exact hp (Set.mem_iUnion.2 ⟨k, h⟩)

private lemma continuousAt_arg_segRatio {a b p : Pt} (hp : p ∉ segment ℝ a b) :
    ContinuousAt (fun x => Complex.arg (segRatio a b x)) p := by
  have hpa : p ≠ a := by rintro rfl; exact hp (left_mem_segment ℝ _ _)
  exact (Complex.continuousAt_arg (segRatio_mem_slitPlane hp)).comp (continuousAt_segRatio hpa)

private lemma wind_continuousAt {m : ℕ} {c : Fin m → Pt} {p : Pt} (hp : p ∉ polyCurve c) :
    ContinuousAt (wind c) p := by
  unfold wind
  have : ∀ k ∈ (Finset.univ : Finset (Fin m)),
      ContinuousAt (fun x => Complex.arg (segRatio (c k) (c (finRotate m k)) x)) p :=
    fun k _ => continuousAt_arg_segRatio (not_mem_seg_of_not_mem_curve hp k)
  exact tendsto_finset_sum _ this

private lemma wind_int {m : ℕ} {c : Fin m → Pt} {p : Pt} (hp : p ∉ polyCurve c) :
    ∃ n : ℤ, wind c p = 2 * Real.pi * n := by
  have hne : ∀ k, toC (c k) - toC p ≠ 0 := by
    intro k h; rw [sub_eq_zero] at h
    apply not_mem_seg_of_not_mem_curve hp k
    rw [toC_injective h]; exact left_mem_segment ℝ _ _
  have hz : ∀ k, segRatio (c k) (c (finRotate m k)) p ≠ 0 := fun k =>
    div_ne_zero (hne _) (hne k)
  have hprod : ∏ k, segRatio (c k) (c (finRotate m k)) p = 1 := by
    unfold segRatio
    rw [Finset.prod_div_distrib]
    rw [Equiv.prod_comp (finRotate m) (fun k => toC (c k) - toC p)]
    exact div_self (Finset.prod_ne_zero_iff.2 (fun k _ => hne k))
  have hexp : Complex.exp ((wind c p : ℂ) * Complex.I) = 1 := by
    unfold wind
    rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    have : ∀ k, Complex.exp (((Complex.arg (segRatio (c k) (c (finRotate m k)) p)) : ℂ) *
        Complex.I) = segRatio (c k) (c (finRotate m k)) p /
          (‖segRatio (c k) (c (finRotate m k)) p‖ : ℂ) := by
      intro k
      have h := Complex.norm_mul_exp_arg_mul_I (segRatio (c k) (c (finRotate m k)) p)
      have hn : (‖segRatio (c k) (c (finRotate m k)) p‖ : ℂ) ≠ 0 := by
        exact_mod_cast (norm_ne_zero_iff.2 (hz k))
      rw [eq_div_iff hn, mul_comm]; exact h
    simp_rw [this]
    rw [Finset.prod_div_distrib, hprod, ← Complex.ofReal_prod, ← norm_prod, hprod]
    simp
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hexp
  refine ⟨n, ?_⟩
  have := congrArg Complex.re (congrArg (· * (-Complex.I)) hn)
  simp at this
  linarith

private lemma wind_const_of_preconnected {m : ℕ} {c : Fin m → Pt} {S : Set Pt} (hS : IsPreconnected S)
    (hSc : ∀ x ∈ S, x ∉ polyCurve c) {x y : Pt} (hx : x ∈ S) (hy : y ∈ S) :
    wind c x = wind c y := by
  have hcont : ContinuousOn (wind c) S := fun z hz =>
    (wind_continuousAt (hSc z hz)).continuousWithinAt
  have himg := hS.image (wind c) hcont
  have key : ∀ x y, x ∈ S → y ∈ S → wind c x ≤ wind c y → wind c x = wind c y := by
    intro x y hx hy hle
    by_contra hne
    have hlt := lt_of_le_of_ne hle hne
    obtain ⟨n1, hn1⟩ := wind_int (hSc x hx)
    obtain ⟨n2, hn2⟩ := wind_int (hSc y hy)
    have hpi := Real.pi_pos
    have hn12 : (n1 : ℝ) < n2 := by
      rw [hn1, hn2] at hlt; nlinarith
    have hmem : 2 * Real.pi * ((n1 : ℝ) + 1 / 2) ∈ wind c '' S := by
      apply himg.Icc_subset (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)
      rw [hn1, hn2]
      have : (n1 : ℝ) + 1 ≤ n2 := by exact_mod_cast (show n1 + 1 ≤ n2 by exact_mod_cast hn12)
      constructor <;> nlinarith
    obtain ⟨z, hz, hzw⟩ := hmem
    obtain ⟨n3, hn3⟩ := wind_int (hSc z hz)
    rw [hn3] at hzw
    have : (n3 : ℝ) = n1 + 1 / 2 := by
      have := mul_left_cancel₀ (by positivity : (2 * Real.pi) ≠ 0) hzw
      exact this
    have h2 : ((2 * n3 : ℤ) : ℝ) = ((2 * n1 + 1 : ℤ) : ℝ) := by push_cast; linarith
    have h3 : 2 * n3 = 2 * n1 + 1 := by exact_mod_cast h2
    omega
  rcases le_total (wind c x) (wind c y) with h | h
  · exact key x y hx hy h
  · exact (key y x hy hx h).symm

private lemma segRatio_param {a b : Pt} (hab : a ≠ b) (s τ : ℝ) :
    segRatio a b (a + s • (b - a) + τ • jrot (b - a)) =
      (((1 - s : ℝ) : ℂ) - (τ : ℂ) * Complex.I) / (-((s : ℂ) + (τ : ℂ) * Complex.I)) := by
  unfold segRatio
  set δ := toC b - toC a with hδ
  have hδ0 : δ ≠ 0 := by
    intro h; rw [hδ, sub_eq_zero] at h; exact hab (toC_injective h).symm
  have e1 : toC b - toC (a + s • (b - a) + τ • jrot (b - a)) =
      δ * (((1 - s : ℝ) : ℂ) - (τ : ℂ) * Complex.I) := by
    rw [toC_add, toC_add, toC_smul, toC_smul, toC_jrot, toC_sub, hδ]; push_cast; ring
  have e2 : toC a - toC (a + s • (b - a) + τ • jrot (b - a)) =
      δ * (-((s : ℂ) + (τ : ℂ) * Complex.I)) := by
    rw [toC_add, toC_add, toC_smul, toC_smul, toC_jrot, toC_sub, hδ]; ring
  rw [e1, e2, mul_div_mul_left _ _ hδ0]

private lemma segRatio_param_im {a b : Pt} (hab : a ≠ b) {s : ℝ} (hs : 0 < s) (τ : ℝ) :
    (segRatio a b (a + s • (b - a) + τ • jrot (b - a))).im = τ / (s ^ 2 + τ ^ 2) := by
  rw [segRatio_param hab, Complex.div_im]
  have hN : Complex.normSq (-((s : ℂ) + (τ : ℂ) * Complex.I)) = s ^ 2 + τ ^ 2 := by
    rw [Complex.normSq_neg, Complex.normSq_apply]; simp; ring
  rw [hN]
  have : (0 : ℝ) < s ^ 2 + τ ^ 2 := by positivity
  simp
  field_simp
  ring

private lemma segRatio_param_zero {a b : Pt} (hab : a ≠ b) {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (segRatio a b (a + s • (b - a))).re < 0 ∧ (segRatio a b (a + s • (b - a))).im = 0 := by
  have h := segRatio_param hab s 0
  simp only [zero_smul, add_zero, Complex.ofReal_zero, zero_mul, sub_zero] at h
  rw [h]
  constructor
  · rw [show (((1 - s : ℝ) : ℂ)) / (-((s : ℂ))) = (((-(1 - s) / s : ℝ)) : ℂ) by push_cast; field_simp]
    rw [Complex.ofReal_re]
    apply div_neg_of_neg_of_pos <;> linarith
  · rw [show (((1 - s : ℝ) : ℂ)) / (-((s : ℂ))) = (((-(1 - s) / s : ℝ)) : ℂ) by push_cast; field_simp]
    rw [Complex.ofReal_im]

/-- **Jump of the winding function** across a simple point of the polygon. -/
private lemma wind_jump {m : ℕ} {c : Fin m → Pt} (k0 : Fin m) {q : Pt}
    (hab0 : c k0 ≠ c (finRotate m k0))
    (hq : q ∈ openSegment ℝ (c k0) (c (finRotate m k0)))
    (hother : ∀ k ≠ k0, q ∉ segment ℝ (c k) (c (finRotate m k))) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), wind c (q + t • jrot (c (finRotate m k0) - c k0)) -
        wind c (q + (-t) • jrot (c (finRotate m k0) - c k0)) = 2 * Real.pi := by
  classical
  set a := c k0 with ha
  set b := c (finRotate m k0) with hb
  have hab : a ≠ b := hab0
  set J := jrot (b - a) with hJ
  obtain ⟨s, hs0, hs1, hqs⟩ := mem_openSegment_iff'.1 hq
  set R : Pt → ℝ := fun x => ∑ k ∈ Finset.univ.erase k0,
    Complex.arg (segRatio (c k) (c (finRotate m k)) x) with hR
  set T : Pt → ℝ := fun x => Complex.arg (segRatio a b x) with hT
  have hsplit : ∀ x, wind c x = T x + R x := by
    intro x; unfold wind; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k0)]
  have hRc : ContinuousAt R q := by
    apply tendsto_finset_sum
    intro k hk
    exact continuousAt_arg_segRatio (hother k (Finset.ne_of_mem_erase hk))
  have hγ : ∀ σ : ℝ, Tendsto (fun t : ℝ => q + (σ * t) • J) (𝓝[>] 0) (𝓝 q) := by
    intro σ
    have : Continuous (fun t : ℝ => q + (σ * t) • J) := by fun_prop
    have h := this.tendsto 0
    simp only [mul_zero, zero_smul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hqa : q ≠ a := by
    intro h; rw [h] at hq; exact hab ((left_mem_openSegment_iff).1 hq)
  have hpt : ∀ σ t : ℝ, q + (σ * t) • J = a + s • (b - a) + (σ * t) • jrot (b - a) := by
    intro σ t; rw [hqs]
  have hz := segRatio_param_zero hab hs0 hs1
  rw [← hqs] at hz
  -- limits of the main term
  have hTp : Tendsto (fun t : ℝ => T (q + (1 * t) • J)) (𝓝[>] 0) (𝓝 Real.pi) := by
    have hw := Complex.continuousWithinAt_arg_of_re_neg_of_im_zero hz.1 hz.2
    rw [← Complex.arg_eq_pi_iff.2 hz]
    have h1 : Tendsto (fun t : ℝ => segRatio a b (q + (1 * t) • J)) (𝓝[>] 0)
        (𝓝[{z | 0 ≤ z.im}] (segRatio a b q)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨(continuousAt_segRatio hqa).tendsto.comp (hγ 1), ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hpt, segRatio_param_im hab hs0]
      have : (0 : ℝ) < t := ht
      positivity
    exact hw.tendsto.comp h1
  have hTm : Tendsto (fun t : ℝ => T (q + (-1 * t) • J)) (𝓝[>] 0) (𝓝 (-Real.pi)) := by
    have hw := Complex.tendsto_arg_nhdsWithin_im_neg_of_re_neg_of_im_zero hz.1 hz.2
    have h1 : Tendsto (fun t : ℝ => segRatio a b (q + (-1 * t) • J)) (𝓝[>] 0)
        (𝓝[{z | z.im < 0}] (segRatio a b q)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨(continuousAt_segRatio hqa).tendsto.comp (hγ (-1)), ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hpt, segRatio_param_im hab hs0]
      have : (0 : ℝ) < t := ht
      apply div_neg_of_neg_of_pos (by linarith) (by positivity)
    exact hw.comp h1
  have hdiff : Tendsto (fun t : ℝ => wind c (q + (1 * t) • J) - wind c (q + (-1 * t) • J))
      (𝓝[>] 0) (𝓝 (2 * Real.pi)) := by
    have hR1 := hRc.tendsto.comp (hγ 1)
    have hR2 := hRc.tendsto.comp (hγ (-1))
    have := ((hTp.add hR1).sub (hTm.add hR2))
    simp only [hsplit]
    convert this using 2
    ring
  -- off the curve
  have hoff : ∀ σ : ℝ, σ ≠ 0 → ∀ᶠ t in 𝓝[>] (0:ℝ), q + (σ * t) • J ∉ polyCurve c := by
    intro σ hσ
    set K := ⋃ k ∈ (Finset.univ.erase k0 : Finset (Fin m)), segment ℝ (c k) (c (finRotate m k))
      with hK
    have hKc : IsClosed K := isClosed_biUnion_finset (fun k _ => (isCompact_segment_pt _ _).isClosed)
    have hqK : q ∉ K := by
      simp only [hK, Set.mem_iUnion]
      rintro ⟨k, hk, hqk⟩; exact hother k (Finset.ne_of_mem_erase hk) hqk
    have h1 : ∀ᶠ t in 𝓝[>] (0:ℝ), q + (σ * t) • J ∉ K :=
      (hγ σ).eventually (hKc.isOpen_compl.mem_nhds hqK)
    filter_upwards [h1, self_mem_nhdsWithin] with t ht htpos
    intro hmem
    simp only [polyCurve, Set.mem_iUnion] at hmem
    obtain ⟨k, hk⟩ := hmem
    by_cases hkk : k = k0
    · rw [hkk, mem_segment_iff'] at hk
      obtain ⟨u, -, -, hu⟩ := hk
      have hcr := congrArg (fun x => jcr (b - a) (x - a)) hu
      simp only [hpt] at hcr
      rw [show a + s • (b - a) + (σ * t) • jrot (b - a) - a = s • (b - a) + (σ * t) • jrot (b - a)
        by abel, jcr_add_right, jcr_smul_right, jcr_smul_right, jcr_jrot, jcr_self,
        add_sub_cancel_left, jcr_smul_right, jcr_self] at hcr
      have hd : 0 < ‖b - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hab.symm)
      have htp : (0:ℝ) < t := htpos
      simp at hcr
      rcases hcr with (h | h) | h
      · exact hσ h
      · linarith
      · exact (sub_ne_zero.2 hab.symm) h
    · apply ht
      simp only [hK, Set.mem_iUnion]
      exact ⟨k, Finset.mem_erase.2 ⟨hkk, Finset.mem_univ _⟩, hk⟩
  have hclose : ∀ᶠ t in 𝓝[>] (0:ℝ),
      |(wind c (q + (1 * t) • J) - wind c (q + (-1 * t) • J)) - 2 * Real.pi| < Real.pi := by
    have := (Metric.tendsto_nhds.1 hdiff) Real.pi Real.pi_pos
    filter_upwards [this] with t ht
    rwa [Real.dist_eq] at ht
  filter_upwards [hclose, hoff 1 one_ne_zero, hoff (-1) (by norm_num)] with t h1 h2 h3
  obtain ⟨n1, hn1⟩ := wind_int h2
  obtain ⟨n2, hn2⟩ := wind_int h3
  have e1 : q + t • J = q + (1 * t) • J := by rw [one_mul]
  have e2 : q + (-t) • J = q + (-1 * t) • J := by rw [neg_one_mul]
  rw [e1, e2]
  rw [hn1, hn2] at h1 ⊢
  have hpi := Real.pi_pos
  have h4 : |(2 * Real.pi) * (((n1 - n2 : ℤ) : ℝ) - 1)| < Real.pi := by
    push_cast; convert h1 using 2; ring
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at h4
  have h5 : |((n1 - n2 : ℤ) : ℝ) - 1| < 1 := by
    by_contra hh; push_neg at hh; nlinarith
  have h6 : n1 - n2 = 1 := by
    rw [abs_lt] at h5
    have a1 : ((n1 - n2 : ℤ) : ℝ) < 2 := by linarith
    have a2 : (0 : ℝ) < ((n1 - n2 : ℤ) : ℝ) := by linarith
    have b1 : n1 - n2 < 2 := by exact_mod_cast a1
    have b2 : 0 < n1 - n2 := by exact_mod_cast a2
    omega
  have : ((n1 : ℝ) - n2) = 1 := by exact_mod_cast h6
  linear_combination (2 * Real.pi) * this

/-- the standing hypotheses -/
private structure JSetup (S G : Set (PlacedTile P)) : Prop where
  disj : DisjointInteriors S
  sts : SideToSideSet S
  sub : G ⊆ S
  fin : G.Finite
  cov : support G ⊆ interior (support S)

private lemma mem_support_iff' {G : Set (PlacedTile P)} {x : Pt} :
    x ∈ support G ↔ ∃ A ∈ G, x ∈ A.carrier := by
  simp [support]

private lemma support_isClosed {G : Set (PlacedTile P)} (hfin : G.Finite) : IsClosed (support G) :=
  hfin.isClosed_biUnion (fun A _ => tile_isClosed A)

private lemma carrier_subset_support {G : Set (PlacedTile P)} {A : PlacedTile P} (hA : A ∈ G) :
    A.carrier ⊆ support G := fun _ hx => mem_support_iff'.2 ⟨A, hA, hx⟩

private lemma openSegment_transfer {a b c d p : Pt} (hab : a ≠ b) (h : segment ℝ a b = segment ℝ c d)
    (hp : p ∈ openSegment ℝ a b) : p ∈ openSegment ℝ c d := by
  rcases seg_endpoints hab h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact hp
  · rw [h1, h2, openSegment_symm]; exact hp

private lemma openSeg_mem_side (A : PlacedTile P) (i : Fin (P.disk A.form).n) {q : Pt}
    (hq : q ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i))) : q ∈ A.side i := by
  rw [tile_side_eq]; exact openSegment_subset_segment ℝ _ _ hq

private lemma vertex_mem_side (A : PlacedTile P) (i : Fin (P.disk A.form).n) : A.vertex i ∈ A.side i := by
  rw [tile_side_eq]; exact left_mem_segment ℝ _ _

private lemma JSetup.no_vertex {S G : Set (PlacedTile P)} (H : JSetup S G) {A C : PlacedTile P}
    (hA : A ∈ G) (hC : C ∈ S) (i : Fin (P.disk A.form).n) {v : Pt}
    (hv : v ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i))) (hvC : v ∈ C.vertexSet) :
    False :=
  vertex_not_mem_open_side H.disj H.sts (H.sub hA) hC i hv hvC
    (H.cov (carrier_subset_support hA (tile_side_subset A i (openSeg_mem_side A i hv))))

private lemma JSetup.partner {S G : Set (PlacedTile P)} (H : JSetup S G) {A A' : PlacedTile P}
    (hA : A ∈ G) (hA' : A' ∈ S) (hne : A ≠ A') (i : Fin (P.disk A.form).n) {q : Pt}
    (hq : q ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i))) (hqA' : q ∈ A'.carrier) :
    ∃ j, A'.side j = A.side i :=
  tile_partner H.disj H.sts (H.sub hA) hA' hne i hq hqA' (fun hv => H.no_vertex hA hA' i hq hv)

/-- two distinct tiles sharing a side lie on opposite sides of it -/
private lemma two_sides {S : Set (PlacedTile P)} (hdisj : DisjointInteriors S) {A A' : PlacedTile P}
    (hA : A ∈ S) (hA' : A' ∈ S) (hne : A ≠ A') (i : Fin (P.disk A.form).n)
    (j : Fin (P.disk A'.form).n) (hj : A'.side j = A.side i) {q : Pt}
    (hq : q ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i))) :
    ∃ r > 0, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ Metric.ball q r,
      (0 < σ * jcr (A.vertex (finRotate _ i) - A.vertex i) (x - A.vertex i) →
        x ∈ interior A.carrier) ∧
      (σ * jcr (A.vertex (finRotate _ i) - A.vertex i) (x - A.vertex i) < 0 →
        x ∈ interior A'.carrier) ∧
      (0 ≤ σ * jcr (A.vertex (finRotate _ i) - A.vertex i) (x - A.vertex i) →
        x ∈ A.carrier) := by
  obtain ⟨r, hr, σ, hσ, hch⟩ := tile_halfdisk A i hq
  set a := A.vertex i with ha
  set b := A.vertex (finRotate _ i) with hb
  have hab : a ≠ b := tile_vertex_ne_next A i
  have hd : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  rw [tile_side_eq, tile_side_eq] at hj
  have hends := seg_endpoints hab hj.symm
  have hq' : q ∈ openSegment ℝ (A'.vertex j) (A'.vertex (finRotate _ j)) :=
    openSegment_transfer hab hj.symm hq
  obtain ⟨r', hr', σ', hσ', hch'⟩ := tile_halfdisk A' j hq'
  have hrel : ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ ∀ x,
      jcr (A'.vertex (finRotate _ j) - A'.vertex j) (x - A'.vertex j) = e * jcr (b - a) (x - a) := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨1, Or.inl rfl, fun x => by rw [h1, h2, one_mul]⟩
    · refine ⟨-1, Or.inr rfl, fun x => ?_⟩
      rw [h1, h2]; simp only [jcr]; simp; ring
  obtain ⟨e, he, hrelx⟩ := hrel
  have hσ2 : σ' * e = 1 ∨ σ' * e = -1 := by
    rcases hσ' with h | h <;> rcases he with h' | h' <;> rw [h, h'] <;> norm_num
  have hint' : ∀ x ∈ Metric.ball q r',
      (x ∈ interior A'.carrier ↔ 0 < (σ' * e) * jcr (b - a) (x - a)) := by
    intro x hx; rw [(hch' x hx).2.2, hrelx, mul_assoc]
  have hcq : jcr (b - a) (q - a) = 0 := ((hch q (Metric.mem_ball_self hr)).1).1
    (by rw [tile_side_eq]; exact openSegment_subset_segment ℝ _ _ hq)
  have hσ2' : σ' * e = -σ := by
    by_contra hne'
    have heq : σ' * e = σ := by
      rcases hσ with h | h <;> rcases hσ2 with h' | h' <;> rw [h'] at hne' ⊢ <;> rw [h] at hne' ⊢ <;>
        (try norm_num at hne')
    obtain ⟨y, hy, hyc⟩ := exists_near_off_line a hd q hσ (lt_min hr hr')
    rw [hcq, mul_zero] at hyc
    have hyb : y ∈ Metric.ball q r := by
      rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hy (min_le_left _ _)
    have hyb' : y ∈ Metric.ball q r' := by
      rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hy (min_le_right _ _)
    exact interiors_disjoint hdisj hA hA' hne (((hch y hyb).2.2).2 hyc)
      ((hint' y hyb').2 (by rw [heq]; exact hyc))
  refine ⟨min r r', lt_min hr hr', σ, hσ, fun x hx => ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩⟩
  · exact ((hch x (Metric.ball_subset_ball (min_le_left _ _) hx)).2.2).2 h
  · exact (hint' x (Metric.ball_subset_ball (min_le_right _ _) hx)).2 (by rw [hσ2']; linarith)
  · exact ((hch x (Metric.ball_subset_ball (min_le_left _ _) hx)).2.1).2 h

/-- the boundary edges: sides of faces of `G` not shared with another face of `G` -/
private def bEdges (G : Set (PlacedTile P)) : Set (Set Pt) :=
  {e | ∃ A ∈ G, ∃ i, A.side i = e ∧ ∀ A' ∈ G, A' ≠ A → ¬ HasEdge A' e}

private lemma bEdges_finite {G : Set (PlacedTile P)} (hfin : G.Finite) : (bEdges G).Finite := by
  apply (hfin.biUnion (fun A _ => Set.finite_range A.side)).subset
  rintro e ⟨A, hA, i, rfl, -⟩
  exact Set.mem_biUnion hA ⟨i, rfl⟩

/-- near a relative interior point of a boundary edge: inside on one side, outside on the other -/
private lemma JSetup.bedge_sides {S G : Set (PlacedTile P)} (H : JSetup S G) {A : PlacedTile P}
    (hA : A ∈ G) (i : Fin (P.disk A.form).n)
    (hbe : ∀ A' ∈ G, A' ≠ A → ¬ HasEdge A' (A.side i)) {q : Pt}
    (hq : q ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i))) :
    ∃ r > 0, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ Metric.ball q r,
      (0 < σ * jcr (A.vertex (finRotate _ i) - A.vertex i) (x - A.vertex i) →
        x ∈ interior A.carrier) ∧
      (σ * jcr (A.vertex (finRotate _ i) - A.vertex i) (x - A.vertex i) < 0 →
        x ∉ support G) := by
  classical
  obtain ⟨r, hr, σ, hσ, hch⟩ := tile_halfdisk A i hq
  set K' := ⋃ A' ∈ G \ {A}, A'.carrier with hK'
  have hK'c : IsClosed K' := (H.fin.diff).isClosed_biUnion (fun D _ => tile_isClosed D)
  have hqK' : q ∉ K' := by
    intro h
    simp only [hK', Set.mem_iUnion] at h
    obtain ⟨A', ⟨hA'G, hA'A⟩, hqA'⟩ := h
    have hne : A ≠ A' := fun h => hA'A (h ▸ rfl)
    obtain ⟨j, hj⟩ := H.partner hA (H.sub hA'G) hne i hq hqA'
    exact hbe A' hA'G (Ne.symm hne) ⟨j, hj⟩
  obtain ⟨ρ, hρ, hρK⟩ := Metric.isOpen_iff.1 hK'c.isOpen_compl q hqK'
  refine ⟨min r ρ, lt_min hr hρ, σ, hσ, fun x hx => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact ((hch x (Metric.ball_subset_ball (min_le_left _ _) hx)).2.2).2 h
  · intro hxG
    obtain ⟨A', hA'G, hxA'⟩ := mem_support_iff'.1 hxG
    by_cases hAA : A' = A
    · subst hAA
      have := ((hch x (Metric.ball_subset_ball (min_le_left _ _) hx)).2.1).1 hxA'
      linarith
    · apply hρK (Metric.ball_subset_ball (min_le_right _ _) hx)
      simp only [hK', Set.mem_iUnion]
      exact ⟨A', ⟨hA'G, hAA⟩, hxA'⟩

private lemma JSetup.partnered_open_in_U {S G : Set (PlacedTile P)} (H : JSetup S G) {A A' : PlacedTile P}
    (hA : A ∈ G) (hA' : A' ∈ G) (hne : A' ≠ A) (i : Fin (P.disk A.form).n)
    (j : Fin (P.disk A'.form).n) (hj : A'.side j = A.side i) {q : Pt}
    (hq : q ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i))) :
    q ∈ interior (support G) := by
  obtain ⟨r, hr, σ, hσ, hch⟩ := two_sides H.disj (H.sub hA) (H.sub hA') (Ne.symm hne) i j hj hq
  rw [mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset (Metric.ball_mem_nhds q hr)
  intro x hx
  rcases le_or_gt 0 (σ * jcr (A.vertex (finRotate _ i) - A.vertex i) (x - A.vertex i)) with h | h
  · exact carrier_subset_support hA ((hch x hx).2.2 h)
  · exact carrier_subset_support hA' (interior_subset ((hch x hx).2.1 h))

private lemma mem_frontier_iff_of_closed {s : Set Pt} (hs : IsClosed s) {x : Pt} :
    x ∈ frontier s ↔ x ∈ s ∧ x ∉ interior s := by
  rw [frontier, hs.closure_eq]; rfl

private lemma JSetup.bEdge_subset_frontier {S G : Set (PlacedTile P)} (H : JSetup S G) {e : Set Pt}
    (he : e ∈ bEdges G) : e ⊆ frontier (support G) := by
  obtain ⟨A, hA, i, rfl, hbe⟩ := he
  have hopen : openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)) ⊆ frontier (support G) := by
    intro q hq
    rw [mem_frontier_iff_of_closed (support_isClosed H.fin)]
    refine ⟨carrier_subset_support hA (tile_side_subset A i (openSeg_mem_side A i hq)), ?_⟩
    intro hqi
    obtain ⟨r, hr, σ, hσ, hch⟩ := H.bedge_sides hA i hbe hq
    obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.1 isOpen_interior q hqi
    have hd : A.vertex (finRotate _ i) - A.vertex i ≠ 0 :=
      sub_ne_zero.2 (tile_vertex_ne_next A i).symm
    have hσn : -σ = 1 ∨ -σ = -1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
    obtain ⟨y, hy, hyc⟩ := exists_near_off_line (A.vertex i) hd q hσn (lt_min hε hr)
    have hcq : jcr (A.vertex (finRotate _ i) - A.vertex i) (q - A.vertex i) = 0 := by
      obtain ⟨s, -, -, hs⟩ := mem_openSegment_iff'.1 hq
      rw [hs, add_sub_cancel_left, jcr_smul_right, jcr_self, mul_zero]
    rw [hcq, mul_zero] at hyc
    have hyb : y ∈ Metric.ball q r := by
      rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hy (min_le_right _ _)
    have hyε : y ∈ Metric.ball q ε := by
      rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hy (min_le_left _ _)
    exact (hch y hyb).2 (by linarith) (interior_subset (hεG hyε))
  rw [tile_side_eq]
  refine (segment_subset_closure_openSegment).trans ?_
  exact (isClosed_frontier.closure_subset_iff).2 hopen

/-- punctured balls cannot be split by two disjoint open sets -/
private lemma punctured_ball_split {z : Pt} {r : ℝ} {O1 O2 : Set Pt} (h1 : IsOpen O1) (h2 : IsOpen O2)
    (hd : Disjoint O1 O2) (hsub : ∀ x ∈ Metric.ball z r, x ≠ z → x ∈ O1 ∪ O2) :
    (∀ x ∈ Metric.ball z r, x ≠ z → x ∈ O1) ∨ (∀ x ∈ Metric.ball z r, x ≠ z → x ∈ O2) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨y1, hy1b, hy1z, hy1O⟩, ⟨y2, hy2b, hy2z, hy2O⟩⟩ := hcon
  have hy1 : y1 ∈ O2 := ((hsub y1 hy1b hy1z).resolve_left hy1O)
  have hy2 : y2 ∈ O1 := ((hsub y2 hy2b hy2z).resolve_right hy2O)
  have hdz : z - y1 ≠ 0 := sub_ne_zero.2 (Ne.symm hy1z)
  -- find a point of `O1` in the ball off the line through `y1` and `z`
  have hopen : IsOpen (O1 ∩ Metric.ball z r) := h1.inter Metric.isOpen_ball
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 hopen y2 ⟨hy2, hy2b⟩
  have hy3 : ∃ y3 ∈ O1 ∩ Metric.ball z r, jcr (z - y1) (y3 - y1) ≠ 0 := by
    by_cases hc : jcr (z - y1) (y2 - y1) = 0
    · obtain ⟨y3, hy3, hy3c⟩ := exists_near_off_line y1 hdz y2 (τ := 1) (Or.inl rfl) hε
      refine ⟨y3, hεs (by rw [Metric.mem_ball, dist_comm]; exact hy3), ?_⟩
      rw [hc] at hy3c; intro h0; rw [h0] at hy3c; simp at hy3c
    · exact ⟨y2, ⟨hy2, hy2b⟩, hc⟩
  obtain ⟨y3, ⟨hy3O, hy3b⟩, hy3c⟩ := hy3
  have hseg : segment ℝ y1 y3 ⊆ O1 ∪ O2 := by
    intro x hx
    have hxb : x ∈ Metric.ball z r := (convex_ball z r).segment_subset hy1b hy3b hx
    refine hsub x hxb ?_
    rintro rfl
    obtain ⟨t, -, -, ht⟩ := mem_segment_iff'.1 hx
    apply hy3c
    rw [show x - y1 = t • (y3 - y1) by rw [ht]; abel, jcr_smul_left, jcr_self, mul_zero]
  rcases (convex_segment y1 y3).isPreconnected.subset_or_subset h1 h2 hd hseg with h | h
  · exact Set.disjoint_left.1 hd (h (left_mem_segment ℝ _ _)) hy1
  · exact Set.disjoint_left.1 hd hy3O (h (right_mem_segment ℝ _ _))

/-- the vertices of faces of `G` -/
private def gVerts (G : Set (PlacedTile P)) : Set Pt := ⋃ A ∈ G, A.vertexSet

private lemma gVerts_finite {G : Set (PlacedTile P)} (hfin : G.Finite) : (gVerts G).Finite :=
  hfin.biUnion (fun _ _ => Set.finite_range _)

private lemma JSetup.frontier_nonvertex {S G : Set (PlacedTile P)} (H : JSetup S G) {p : Pt}
    (hp : p ∈ frontier (support G)) (hpv : p ∉ gVerts G) : p ∈ ⋃₀ bEdges G := by
  classical
  rw [mem_frontier_iff_of_closed (support_isClosed H.fin)] at hp
  obtain ⟨hpG, hpU⟩ := hp
  obtain ⟨A, hA, hpA⟩ := mem_support_iff'.1 hpG
  have hpAi : p ∉ interior A.carrier := fun h =>
    hpU (interior_mono (carrier_subset_support hA) h)
  have hpf : p ∈ frontier A.carrier := by
    rw [mem_frontier_iff_of_closed (tile_isClosed A)]; exact ⟨hpA, hpAi⟩
  rw [tile_frontier_eq, Set.mem_iUnion] at hpf
  obtain ⟨i, hpi⟩ := hpf
  have hq : p ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)) := by
    rw [tile_side_eq] at hpi
    refine mem_openSegment_of_ne_left_right ?_ ?_ hpi
    · intro h; exact hpv (Set.mem_biUnion hA ⟨i, h⟩)
    · intro h; exact hpv (Set.mem_biUnion hA ⟨_, h⟩)
  by_cases hbe : ∀ A' ∈ G, A' ≠ A → ¬ HasEdge A' (A.side i)
  · exact ⟨A.side i, ⟨A, hA, i, rfl, hbe⟩, hpi⟩
  · push_neg at hbe
    obtain ⟨A', hA'G, hne, j, hj⟩ := hbe
    exact absurd (H.partnered_open_in_U hA hA'G hne i j hj hq) hpU

private lemma bEdges_union_isClosed {G : Set (PlacedTile P)} (hfin : G.Finite) :
    IsClosed (⋃₀ bEdges G) := by
  rw [Set.sUnion_eq_biUnion]
  apply (bEdges_finite hfin).isClosed_biUnion
  rintro e ⟨A, -, i, rfl, -⟩
  rw [tile_side_eq]; exact (isCompact_segment_pt _ _).isClosed

private lemma JSetup.frontier_subset_bEdges {S G : Set (PlacedTile P)} (H : JSetup S G) :
    frontier (support G) ⊆ ⋃₀ bEdges G := by
  intro p hp
  by_contra hpF
  have hcl := bEdges_union_isClosed H.fin
  obtain ⟨r1, hr1, hr1F⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl p hpF
  have hVf : (gVerts G \ {p}).Finite := (gVerts_finite H.fin).diff
  have hpV : p ∉ gVerts G \ {p} := fun h => h.2 rfl
  obtain ⟨r2, hr2, hr2V⟩ := Metric.isOpen_iff.1 hVf.isClosed.isOpen_compl p hpV
  set r := min r1 r2
  have hr : 0 < r := lt_min hr1 hr2
  have hpfr := hp
  rw [mem_frontier_iff_of_closed (support_isClosed H.fin)] at hpfr
  obtain ⟨hpG, hpU⟩ := hpfr
  have hsub : ∀ x ∈ Metric.ball p r, x ≠ p →
      x ∈ interior (support G) ∪ (support G)ᶜ := by
    intro x hx hxp
    by_contra hxn
    have hxf : x ∈ frontier (support G) := by
      rw [mem_frontier_iff_of_closed (support_isClosed H.fin)]
      constructor
      · by_contra h; exact hxn (Or.inr h)
      · intro h; exact hxn (Or.inl h)
    have hxv : x ∉ gVerts G := fun h =>
      hr2V (Metric.ball_subset_ball (min_le_right _ _) hx) ⟨h, hxp⟩
    exact hr1F (Metric.ball_subset_ball (min_le_left _ _) hx) (H.frontier_nonvertex hxf hxv)
  have hdisj : Disjoint (interior (support G)) (support G)ᶜ :=
    Set.disjoint_left.2 (fun x hx hx' => hx' (interior_subset hx))
  rcases punctured_ball_split isOpen_interior (support_isClosed H.fin).isOpen_compl hdisj hsub
    with h | h
  · apply hpU
    rw [mem_interior_iff_mem_nhds]
    apply Filter.mem_of_superset (Metric.ball_mem_nhds p hr)
    intro x hx
    by_cases hxp : x = p
    · rw [hxp]; exact hpG
    · exact interior_subset (h x hx hxp)
  · obtain ⟨A, hA, hpA⟩ := mem_support_iff'.1 hpG
    rw [← tile_regular A, Metric.mem_closure_iff] at hpA
    obtain ⟨y, hyA, hpy⟩ := hpA r hr
    have hyb : y ∈ Metric.ball p r := by rw [Metric.mem_ball, dist_comm]; exact hpy
    have hyp : y ≠ p := by
      rintro rfl
      exact hpU (interior_mono (carrier_subset_support hA) hyA)
    exact h y hyb hyp (carrier_subset_support hA (interior_subset hyA))

private lemma JSetup.frontier_eq_bEdges {S G : Set (PlacedTile P)} (H : JSetup S G) :
    frontier (support G) = ⋃₀ bEdges G := by
  apply Set.Subset.antisymm H.frontier_subset_bEdges
  rintro x ⟨e, he, hx⟩
  exact H.bEdge_subset_frontier he hx

/-- two sides of faces of `G` meeting at a relative interior point of one coincide -/
private lemma JSetup.side_eq_of_open_mem {S G : Set (PlacedTile P)} (H : JSetup S G) {A1 A2 : PlacedTile P}
    (hA1 : A1 ∈ G) (hA2 : A2 ∈ G) (i1 : Fin (P.disk A1.form).n) (i2 : Fin (P.disk A2.form).n)
    {p : Pt} (hp : p ∈ openSegment ℝ (A1.vertex i1) (A1.vertex (finRotate _ i1)))
    (hp2 : p ∈ A2.side i2) : A1.side i1 = A2.side i2 := by
  by_cases h12 : A1 = A2
  · subst h12
    rw [tile_eq_of_openSegment_inter_segment A1 hp hp2]
  · obtain ⟨j, hj⟩ := H.partner hA1 (H.sub hA2) h12 i1 hp (tile_side_subset A2 i2 hp2)
    have hj' := hj
    rw [tile_side_eq, tile_side_eq] at hj'
    have hpj : p ∈ openSegment ℝ (A2.vertex j) (A2.vertex (finRotate _ j)) :=
      openSegment_transfer (tile_vertex_ne_next A1 i1) hj'.symm hp
    rw [← hj, tile_eq_of_openSegment_inter_segment A2 hpj hp2]

private lemma finRotate_finRotate_ne {m : ℕ} (hm : 3 ≤ m) (k : Fin m) : finRotate m (finRotate m k) ≠ k := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [finRotate_succ_apply, finRotate_succ_apply]
  intro h
  have h2 : (k + 1 + 1).val = k.val := by rw [h]
  rw [Fin.val_add, Fin.val_add, Fin.val_one'] at h2
  have hk := k.isLt
  rcases Nat.lt_or_ge (k.val + 1) (m+1) with h3 | h3
  · rw [Nat.mod_eq_of_lt (show 1 < m + 1 by omega), Nat.mod_eq_of_lt h3] at h2
    rcases Nat.lt_or_ge (k.val + 1 + 1) (m+1) with h4 | h4
    · rw [Nat.mod_eq_of_lt h4] at h2; omega
    · rw [show k.val + 1 + 1 = m + 1 by omega, Nat.mod_self] at h2; omega
  · rw [Nat.mod_eq_of_lt (show 1 < m + 1 by omega), show k.val + 1 = m + 1 by omega,
      Nat.mod_self] at h2
    rw [Nat.mod_eq_of_lt (show 0 + 1 < m + 1 by omega)] at h2; omega

private lemma cyc_seg_inj {m : ℕ} (hm : 3 ≤ m) {c : Fin m → Pt} (hc : Function.Injective c) {k l : Fin m}
    (h : segment ℝ (c k) (c (finRotate m k)) = segment ℝ (c l) (c (finRotate m l))) : k = l := by
  have hne : c k ≠ c (finRotate m k) := fun h' =>
    finRotate_ne_self (by omega) k (hc h').symm
  rcases seg_endpoints hne h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact (hc h1).symm
  · have e1 := hc h1
    have e2 := hc h2
    rw [e1] at e2
    exact absurd e2 (finRotate_finRotate_ne hm k)

private lemma bEdge_sides_ne {G : Set (PlacedTile P)} {x y : Pt} (h : segment ℝ x y ∈ bEdges G) :
    x ≠ y := by
  obtain ⟨A, -, i, hi, -⟩ := h
  rintro rfl
  rw [tile_side_eq, segment_same] at hi
  have h1 : A.vertex i ∈ ({x} : Set Pt) := hi ▸ left_mem_segment ℝ _ _
  have h2 : A.vertex (finRotate _ i) ∈ ({x} : Set Pt) := hi ▸ right_mem_segment ℝ _ _
  rw [Set.mem_singleton_iff] at h1 h2
  exact tile_vertex_ne_next A i (h1.trans h2.symm)

private lemma bEdge_rep {G : Set (PlacedTile P)} {x y : Pt} (h : segment ℝ x y ∈ bEdges G) :
    ∃ A ∈ G, ∃ i, A.side i = segment ℝ x y ∧ (∀ A' ∈ G, A' ≠ A → ¬ HasEdge A' (A.side i)) ∧
      ((A.vertex i = x ∧ A.vertex (finRotate _ i) = y) ∨
        (A.vertex i = y ∧ A.vertex (finRotate _ i) = x)) := by
  obtain ⟨A, hA, i, hi, hbe⟩ := h
  refine ⟨A, hA, i, hi, hi ▸ hbe, ?_⟩
  have hi' := hi
  rw [tile_side_eq] at hi'
  rcases seg_endpoints (tile_vertex_ne_next A i) hi' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨h1.symm, h2.symm⟩
  · right; exact ⟨h2.symm, h1.symm⟩

private lemma bEdge_endpoint_gVerts {G : Set (PlacedTile P)} {x y : Pt} (h : segment ℝ x y ∈ bEdges G) :
    x ∈ gVerts G ∧ y ∈ gVerts G := by
  obtain ⟨A, hA, i, -, -, hends⟩ := bEdge_rep h
  rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨Set.mem_biUnion hA ⟨i, h1⟩, Set.mem_biUnion hA ⟨_, h2⟩⟩
  · exact ⟨Set.mem_biUnion hA ⟨_, h2⟩, Set.mem_biUnion hA ⟨i, h1⟩⟩

private lemma jcr_zero_of_mem_segment {a b x : Pt} (hx : x ∈ segment ℝ a b) : jcr (b - a) (x - a) = 0 := by
  obtain ⟨t, -, -, rfl⟩ := mem_segment_iff'.1 hx
  rw [add_sub_cancel_left, jcr_smul_right, jcr_self, mul_zero]

/-- **Degree two.**  Every boundary vertex lies on a second boundary edge. -/
private lemma JSetup.next_edge {S G : Set (PlacedTile P)} (H : JSetup S G) {x y : Pt}
    (hxy : segment ℝ x y ∈ bEdges G) : ∃ z, segment ℝ y z ∈ bEdges G ∧ z ≠ x := by
  classical
  have hxyne := bEdge_sides_ne hxy
  set e := segment ℝ x y with he
  -- it suffices to find a second boundary edge through `y`
  suffices hsuff : ∃ e' ∈ bEdges G, y ∈ e' ∧ e' ≠ e by
    obtain ⟨e', he', hye', hne'⟩ := hsuff
    obtain ⟨A', hA', j, hj, hbe'⟩ := he'
    have hyv : y ∈ gVerts G := (bEdge_endpoint_gVerts hxy).2
    have hy' := hye'
    rw [← hj, tile_side_eq] at hy'
    have hyend : y = A'.vertex j ∨ y = A'.vertex (finRotate _ j) := by
      by_contra hcon
      push_neg at hcon
      have hyo := mem_openSegment_of_ne_left_right hcon.1.symm hcon.2.symm hy'
      obtain ⟨C, hC, hyC⟩ := Set.mem_iUnion₂.1 hyv
      exact H.no_vertex hA' (H.sub hC) j hyo hyC
    rcases hyend with h1 | h1
    · refine ⟨A'.vertex (finRotate _ j), ?_, ?_⟩
      · rw [h1, ← tile_side_eq, hj]; exact ⟨A', hA', j, hj, hbe'⟩
      · intro hz; apply hne'
        rw [← hj, tile_side_eq, ← h1, hz, he, segment_symm]
    · refine ⟨A'.vertex j, ?_, ?_⟩
      · rw [segment_symm, h1, ← tile_side_eq, hj]; exact ⟨A', hA', j, hj, hbe'⟩
      · intro hz; apply hne'
        rw [← hj, tile_side_eq, ← h1, hz, he]
  by_contra hcon
  push_neg at hcon
  -- the other boundary edges stay away from `y`
  set K := ⋃₀ {e' ∈ bEdges G | y ∉ e'} with hK
  have hKc : IsClosed K := by
    rw [hK, Set.sUnion_eq_biUnion]
    apply ((bEdges_finite H.fin).subset (fun e' he' => he'.1)).isClosed_biUnion
    rintro e' ⟨⟨A, -, i, rfl, -⟩, -⟩
    rw [tile_side_eq]; exact (isCompact_segment_pt _ _).isClosed
  have hyK : y ∉ K := by
    rintro ⟨e', ⟨-, hy'⟩, hye'⟩; exact hy' hye'
  obtain ⟨r1, hr1, hr1K⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl y hyK
  set u := x - y with hu
  have hu0 : u ≠ 0 := sub_ne_zero.2 hxyne
  have hun : 0 < ‖u‖ := norm_pos_iff.2 hu0
  set r := min r1 ‖u‖ with hr
  have hrpos : 0 < r := lt_min hr1 hun
  set B := Metric.ball y r with hB
  -- frontier inside the ball lies on `e`
  have hFB : ∀ w ∈ B, w ∈ frontier (support G) → w ∈ e := by
    intro w hw hwF
    rw [H.frontier_eq_bEdges] at hwF
    obtain ⟨e', he', hwe'⟩ := hwF
    by_cases hye' : y ∈ e'
    · rw [← hcon e' he' hye']; exact hwe'
    · exact absurd ⟨e', ⟨he', hye'⟩, hwe'⟩ (hr1K (Metric.ball_subset_ball (min_le_left _ _) hw))
  -- the ball minus `e` is star convex
  set κ := r / (2 * ‖u‖) with hκ
  have hκpos : 0 < κ := div_pos hrpos (by positivity)
  set c0 := y - κ • u with hc0
  have hc0B : c0 ∈ B \ e := by
    constructor
    · rw [hB, Metric.mem_ball, hc0, dist_eq_norm, show y - κ • u - y = -(κ • u) by abel, norm_neg,
        norm_smul, Real.norm_eq_abs, abs_of_pos hκpos, hκ]
      field_simp; linarith
    · intro hc
      rw [he, segment_symm, mem_segment_iff'] at hc
      obtain ⟨s, hs0, -, hs⟩ := hc
      rw [hc0] at hs
      have : (-κ) • u = s • u := by
        have := congrArg (fun w => w - y) hs
        simp only [add_sub_cancel_left] at this
        rw [← hu] at this
        rw [neg_smul, ← this]; abel
      have := smul_cancel_pt hu0 this
      linarith
  have hstar : StarConvex ℝ c0 (B \ e) := by
    intro w hw a b ha hb hab
    refine ⟨(convex_ball y r) hc0B.1 hw.1 ha hb hab, ?_⟩
    intro hmem
    apply hw.2
    rw [he, segment_symm, mem_segment_iff'] at hmem ⊢
    obtain ⟨s, hs0, hs1, hs⟩ := hmem
    rcases eq_or_lt_of_le hb with hb0 | hbpos
    · subst hb0
      have ha1 : a = 1 := by linarith
      subst ha1
      rw [one_smul, zero_smul, add_zero, hc0] at hs
      have : (-κ) • u = s • u := by
        have := congrArg (fun w => w - y) hs
        simp only [add_sub_cancel_left] at this
        rw [← hu] at this
        rw [neg_smul, ← this]; abel
      have := smul_cancel_pt hu0 this
      linarith
    · set μ := (s + a * κ) / b with hμ
      have hw' : w = y + μ • u := by
        have h1 : b • w = y + s • u - a • c0 := by rw [← hs]; abel
        have h2 : y + s • u - a • c0 = b • (y + μ • u) := by
          rw [hc0, hμ, smul_add, smul_smul, mul_div_cancel₀ _ hbpos.ne',
            show a = 1 - b by linarith]
          module
        rw [h2] at h1
        exact smul_right_injective _ hbpos.ne' h1
      have hμ0 : 0 ≤ μ := div_nonneg (by positivity) hb
      have hμ1 : μ ≤ 1 := by
        have hwB := hw.1
        rw [hB, Metric.mem_ball, hw', dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg hμ0] at hwB
        have : μ * ‖u‖ < ‖u‖ := lt_of_lt_of_le hwB (min_le_right _ _)
        have := (mul_lt_iff_lt_one_left hun).1 this
        linarith
      exact ⟨μ, hμ0, hμ1, hw'⟩
  have hpre : IsPreconnected (B \ e) := (hstar.isPathConnected hc0B).isConnected.isPreconnected
  -- the ball minus `e` avoids the frontier
  have hsub : B \ e ⊆ interior (support G) ∪ (support G)ᶜ := by
    intro w hw
    by_contra hn
    apply hw.2
    apply hFB w hw.1
    rw [mem_frontier_iff_of_closed (support_isClosed H.fin)]
    constructor
    · by_contra h; exact hn (Or.inr h)
    · intro h; exact hn (Or.inl h)
  have hdisjUV : Disjoint (interior (support G)) (support G)ᶜ :=
    Set.disjoint_left.2 (fun w hw hw' => hw' (interior_subset hw))
  -- points on both sides near `e` close to `y`
  obtain ⟨A, hA, i, hAi, hbe, hends⟩ := bEdge_rep hxy
  set t := min (1 / 2) (r / (4 * ‖u‖)) with ht
  have htpos : 0 < t := lt_min (by norm_num) (div_pos hrpos (by positivity))
  set q := y + t • u with hq
  have hqo : q ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)) := by
    have : q ∈ openSegment ℝ y x := by
      rw [mem_openSegment_iff']
      exact ⟨t, htpos, lt_of_le_of_lt (min_le_left _ _) (by norm_num), rfl⟩
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, openSegment_symm]; exact this
    · rw [h1, h2]; exact this
  have hqy : dist q y ≤ r / 4 := by
    rw [hq, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    calc t * ‖u‖ ≤ r / (4 * ‖u‖) * ‖u‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) hun.le
      _ = r / 4 := by field_simp
  obtain ⟨rq, hrq, σ, hσ, hch⟩ := H.bedge_sides hA i hbe hqo
  have hd : A.vertex (finRotate _ i) - A.vertex i ≠ 0 :=
    sub_ne_zero.2 (tile_vertex_ne_next A i).symm
  have hcq : jcr (A.vertex (finRotate _ i) - A.vertex i) (q - A.vertex i) = 0 :=
    jcr_zero_of_mem_segment (openSegment_subset_segment ℝ _ _ hqo)
  have hσn : -σ = 1 ∨ -σ = -1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hρ : 0 < min rq (r / 4) := lt_min hrq (by linarith)
  obtain ⟨z1, hz1, hz1c⟩ := exists_near_off_line (A.vertex i) hd q hσ hρ
  obtain ⟨z2, hz2, hz2c⟩ := exists_near_off_line (A.vertex i) hd q hσn hρ
  rw [hcq, mul_zero] at hz1c hz2c
  have hz1q : z1 ∈ Metric.ball q rq := by
    rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hz1 (min_le_left _ _)
  have hz2q : z2 ∈ Metric.ball q rq := by
    rw [Metric.mem_ball, dist_comm]; exact lt_of_lt_of_le hz2 (min_le_left _ _)
  have hinB : ∀ z, dist q z < min rq (r / 4) → z ∈ B := by
    intro z hz
    rw [hB, Metric.mem_ball]
    calc dist z y ≤ dist z q + dist q y := dist_triangle _ _ _
      _ < r / 4 + r / 4 := by
        rw [dist_comm z q]; exact add_lt_add_of_lt_of_le (lt_of_lt_of_le hz (min_le_right _ _)) hqy
      _ < r := by linarith
  have hnote : ∀ z, jcr (A.vertex (finRotate _ i) - A.vertex i) (z - A.vertex i) ≠ 0 → z ∉ e := by
    intro z hz hze
    rw [he, ← hAi, tile_side_eq] at hze
    exact hz (jcr_zero_of_mem_segment hze)
  have hz1e : z1 ∉ e := hnote z1 (by intro h0; rw [h0, mul_zero] at hz1c; exact lt_irrefl _ hz1c)
  have hz2e : z2 ∉ e := hnote z2 (by intro h0; rw [h0, mul_zero] at hz2c; exact lt_irrefl _ hz2c)
  have hz1U : z1 ∈ interior (support G) :=
    interior_mono (carrier_subset_support hA) ((hch z1 hz1q).1 hz1c)
  have hz2V : z2 ∈ (support G)ᶜ := (hch z2 hz2q).2 (by linarith)
  rcases hpre.subset_or_subset isOpen_interior (support_isClosed H.fin).isOpen_compl hdisjUV hsub
    with h | h
  · exact Set.disjoint_left.1 hdisjUV (h ⟨hinB z2 hz2, hz2e⟩) hz2V
  · exact Set.disjoint_left.1 hdisjUV hz1U (h ⟨hinB z1 hz1, hz1e⟩)

private lemma finRotate_val' {m : ℕ} (k : Fin m) :
    (finRotate m k).val = if k.val + 1 = m then 0 else k.val + 1 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := k.isLt; omega⟩
  rw [coe_finRotate]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (by rw [h1]; simp) h2
  · exact absurd (Fin.ext (by simp; omega)) h1
  · rfl

/-- a finite graph in which every edge can be continued contains a cycle -/
private lemma exists_cycle_of_next {E : Pt → Pt → Prop} {Vf : Set Pt} (hVf : Vf.Finite)
    (hne : ∀ x y, E x y → x ≠ y) (hnext : ∀ x y, E x y → ∃ z, E y z ∧ z ≠ x)
    (hV : ∀ x y, E x y → x ∈ Vf) {x0 y0 : Pt} (h0 : E x0 y0) :
    ∃ m, 3 ≤ m ∧ ∃ c : Fin m → Pt, Function.Injective c ∧ ∀ k, E (c k) (c (finRotate m k)) := by
  classical
  let nx : Pt → Pt → Pt := fun x y => if h : E x y then Classical.choose (hnext x y h) else y
  let st : ℕ → Pt × Pt := fun n => Nat.rec (x0, y0) (fun _ p => (p.2, nx p.1 p.2)) n
  have hstS : ∀ n, st (n + 1) = ((st n).2, nx (st n).1 (st n).2) := fun n => rfl
  have hinv : ∀ n, E (st n).1 (st n).2 := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      rw [hstS]
      simp only [nx, dif_pos ih]
      exact (Classical.choose_spec (hnext _ _ ih)).1
  let v : ℕ → Pt := fun n => (st n).1
  have hvE : ∀ n, E (v n) (v (n + 1)) := fun n => by
    simp only [v, hstS]; exact hinv n
  have hv2 : ∀ n, v (n + 2) ≠ v n := by
    intro n
    simp only [v, hstS]
    simp only [nx, dif_pos (hinv n)]
    exact (Classical.choose_spec (hnext _ _ (hinv n))).2
  have hv1 : ∀ n, v n ≠ v (n + 1) := fun n => hne _ _ (hvE n)
  have hvV : ∀ n, v n ∈ Vf := fun n => hV _ _ (hvE n)
  have : Finite Vf := hVf.to_subtype
  obtain ⟨a, b, hab, habv⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (⟨v n, hvV n⟩ : Vf))
  have hex : ∃ j, ∃ i < j, v i = v j := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨b, a, h, congrArg Subtype.val habv⟩
    · exact ⟨a, b, h, (congrArg Subtype.val habv).symm⟩
  obtain ⟨j, ⟨i, hij, hvij⟩, hmin⟩ : ∃ j, (∃ i < j, v i = v j) ∧ ∀ j' < j, ∀ i' < j', v i' ≠ v j' :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j' hj' i' hi' h => Nat.find_min hex hj' ⟨i', hi', h⟩⟩
  have hm3 : 3 ≤ j - i := by
    by_contra h
    push_neg at h
    have : j = i + 1 ∨ j = i + 2 := by omega
    rcases this with h1 | h1
    · exact hv1 i (by rw [hvij, h1])
    · exact hv2 i (by rw [← h1, hvij])
  refine ⟨j - i, hm3, fun k => v (i + k.val), ?_, ?_⟩
  · intro k l hkl
    by_contra hne'
    have hne'' : k.val ≠ l.val := fun h => hne' (Fin.ext h)
    rcases lt_or_gt_of_ne hne'' with h | h
    · exact hmin (i + l.val) (by have := l.isLt; omega) (i + k.val) (by omega) hkl
    · exact hmin (i + k.val) (by have := k.isLt; omega) (i + l.val) (by omega) hkl.symm
  · intro k
    have key : v (i + (finRotate (j - i) k).val) = v (i + k.val + 1) := by
      rw [finRotate_val']
      split_ifs with h
      · rw [add_zero, hvij, show i + k.val + 1 = j by omega]
      · rfl
    show E (v (i + k.val)) (v (i + (finRotate (j - i) k).val))
    rw [key]; exact hvE _

private lemma JSetup.exists_bcycle {S G : Set (PlacedTile P)} (H : JSetup S G) (hne : (bEdges G).Nonempty) :
    ∃ m, 3 ≤ m ∧ ∃ c : Fin m → Pt, Function.Injective c ∧
      ∀ k, segment ℝ (c k) (c (finRotate m k)) ∈ bEdges G := by
  obtain ⟨e, A, hA, i, hAi, hbe⟩ := hne
  have h0 : segment ℝ (A.vertex i) (A.vertex (finRotate _ i)) ∈ bEdges G := by
    rw [← tile_side_eq]; exact ⟨A, hA, i, rfl, hAi ▸ hbe⟩
  exact exists_cycle_of_next (gVerts_finite H.fin) (fun x y h => bEdge_sides_ne h)
    (fun x y h => H.next_edge h) (fun x y h => (bEdge_endpoint_gVerts h).1) h0

/-- both sides of a boundary edge: one is inside, the other outside -/
private lemma JSetup.bedge_UV {S G : Set (PlacedTile P)} (H : JSetup S G) {A : PlacedTile P}
    (hA : A ∈ G) (i : Fin (P.disk A.form).n)
    (hbe : ∀ A' ∈ G, A' ≠ A → ¬ HasEdge A' (A.side i)) {q : Pt}
    (hq : q ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i))) {J : Pt}
    (hJ : jcr (A.vertex (finRotate _ i) - A.vertex i) J ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      (q + t • J ∈ interior (support G) ∧ q + (-t) • J ∈ (support G)ᶜ) ∨
      (q + t • J ∈ (support G)ᶜ ∧ q + (-t) • J ∈ interior (support G)) := by
  obtain ⟨r, hr, σ, hσ, hch⟩ := H.bedge_sides hA i hbe hq
  have hcq : jcr (A.vertex (finRotate _ i) - A.vertex i) (q - A.vertex i) = 0 :=
    jcr_zero_of_mem_segment (openSegment_subset_segment ℝ _ _ hq)
  set κ := jcr (A.vertex (finRotate _ i) - A.vertex i) J with hκ
  have hval : ∀ τ : ℝ, jcr (A.vertex (finRotate _ i) - A.vertex i) (q + τ • J - A.vertex i) =
      τ * κ := by
    intro τ
    rw [show q + τ • J - A.vertex i = (q - A.vertex i) + τ • J by abel, jcr_add_right, hcq,
      jcr_smul_right, zero_add]
  have hball : ∀ τ : ℝ, |τ| * ‖J‖ < r → q + τ • J ∈ Metric.ball q r := by
    intro τ hτ
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    exact hτ
  refine ⟨r / (‖J‖ + 1), div_pos hr (by positivity), fun t ht htδ => ?_⟩
  have htJ : t * ‖J‖ < r := by
    rw [lt_div_iff₀ (by positivity)] at htδ
    nlinarith [norm_nonneg J]
  have hb1 : q + t • J ∈ Metric.ball q r := hball t (by rw [abs_of_pos ht]; exact htJ)
  have hb2 : q + (-t) • J ∈ Metric.ball q r := hball (-t) (by rw [abs_neg, abs_of_pos ht]; exact htJ)
  have hσκ : σ * κ ≠ 0 := mul_ne_zero (by rcases hσ with h | h <;> rw [h] <;> norm_num) hJ
  rcases lt_or_gt_of_ne hσκ with h | h
  · right
    constructor
    · exact (hch _ hb1).2 (by rw [hval]; nlinarith)
    · exact interior_mono (carrier_subset_support hA) ((hch _ hb2).1 (by rw [hval]; nlinarith))
  · left
    constructor
    · exact interior_mono (carrier_subset_support hA) ((hch _ hb1).1 (by rw [hval]; nlinarith))
    · exact (hch _ hb2).2 (by rw [hval]; nlinarith)

private lemma jcr_jrot_ne {u : Pt} (hu : u ≠ 0) : jcr u (jrot u) ≠ 0 := by
  rw [jcr_jrot]; exact pow_ne_zero 2 (norm_ne_zero_iff.2 hu)

/-- **Single cycle.**  Every boundary edge is an edge of the boundary cycle. -/
private lemma JSetup.bEdges_in_cycle {S G : Set (PlacedTile P)} (H : JSetup S G)
    (hint : IsConnected (interior (support G))) (hcompl : IsConnected (support G)ᶜ)
    {m : ℕ} (hm : 3 ≤ m) {c : Fin m → Pt} (hc : Function.Injective c)
    (hE : ∀ k, segment ℝ (c k) (c (finRotate m k)) ∈ bEdges G) :
    ∀ e ∈ bEdges G, ∃ k, e = segment ℝ (c k) (c (finRotate m k)) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨e0, he0, he0c⟩ := hcon
  have hcurveF : polyCurve c ⊆ frontier (support G) := by
    intro x hx
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
    exact H.bEdge_subset_frontier (hE k) hk
  have hUc : ∀ x ∈ interior (support G), x ∉ polyCurve c := fun x hx hxc =>
    (hcurveF hxc).2 hx
  have hVc : ∀ x ∈ (support G)ᶜ, x ∉ polyCurve c := by
    intro x hx hxc
    have := hcurveF hxc
    rw [mem_frontier_iff_of_closed (support_isClosed H.fin)] at this
    exact hx this.1
  have wU := fun x y (hx : x ∈ interior (support G)) (hy : y ∈ interior (support G)) =>
    wind_const_of_preconnected hint.isPreconnected hUc hx hy
  have wV := fun x y (hx : x ∈ (support G)ᶜ) (hy : y ∈ (support G)ᶜ) =>
    wind_const_of_preconnected hcompl.isPreconnected hVc hx hy
  -- the winding function separates inside from outside
  have key1 : ∃ xU ∈ interior (support G), ∃ xV ∈ (support G)ᶜ, wind c xU ≠ wind c xV := by
    set k0 : Fin m := ⟨0, by omega⟩
    obtain ⟨A, hA, i, hAi, hbe, hends⟩ := bEdge_rep (hE k0)
    have hab0 : c k0 ≠ c (finRotate m k0) := bEdge_sides_ne (hE k0)
    set q := c k0 + (1 / 2 : ℝ) • (c (finRotate m k0) - c k0) with hq
    have hqo : q ∈ openSegment ℝ (c k0) (c (finRotate m k0)) :=
      mem_openSegment_iff'.2 ⟨1 / 2, by norm_num, by norm_num, rfl⟩
    have hqA : q ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)) := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact hqo
      · rw [h1, h2, openSegment_symm]; exact hqo
    have hother : ∀ k ≠ k0, q ∉ segment ℝ (c k) (c (finRotate m k)) := by
      intro k hk hqk
      obtain ⟨A2, hA2, i2, hA2i, -, -⟩ := bEdge_rep (hE k)
      have := H.side_eq_of_open_mem hA hA2 i i2 hqA (by rw [hA2i]; exact hqk)
      rw [hAi, hA2i] at this
      exact hk (cyc_seg_inj hm hc this).symm
    have hjump := wind_jump k0 hab0 hqo hother
    set J := jrot (c (finRotate m k0) - c k0) with hJ
    have hu0 : c (finRotate m k0) - c k0 ≠ 0 := sub_ne_zero.2 hab0.symm
    have hκ : jcr (A.vertex (finRotate _ i) - A.vertex i) J ≠ 0 := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact jcr_jrot_ne hu0
      · rw [h1, h2, show c k0 - c (finRotate m k0) = (-1 : ℝ) • (c (finRotate m k0) - c k0) by
          rw [neg_one_smul, neg_sub], jcr_smul_left]
        exact mul_ne_zero (by norm_num) (jcr_jrot_ne hu0)
    obtain ⟨δ, hδ, hUV⟩ := H.bedge_UV hA i hbe hqA hκ
    obtain ⟨t, ht1, ht2⟩ := (hjump.and (Ioo_mem_nhdsGT hδ)).exists
    rcases hUV t ht2.1 ht2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨_, h1, _, h2, fun h => ?_⟩
      rw [h, sub_self] at ht1
      exact Real.pi_pos.ne' (by linarith)
    · refine ⟨_, h2, _, h1, fun h => ?_⟩
      rw [h, sub_self] at ht1
      exact Real.pi_pos.ne' (by linarith)
  obtain ⟨xU, hxU, xV, hxV, hwne⟩ := key1
  -- an edge outside the cycle forces equality
  obtain ⟨A0, hA0, i0, rfl, hbe0⟩ := he0
  set a0 := A0.vertex i0 with ha0
  set b0 := A0.vertex (finRotate _ i0) with hb0
  have hab0 : a0 ≠ b0 := tile_vertex_ne_next A0 i0
  set q0 := a0 + (1 / 2 : ℝ) • (b0 - a0) with hq0
  have hq0o : q0 ∈ openSegment ℝ a0 b0 := mem_openSegment_iff'.2 ⟨1 / 2, by norm_num, by norm_num, rfl⟩
  have hq0c : q0 ∉ polyCurve c := by
    intro h
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h
    obtain ⟨A2, hA2, i2, hA2i, -, -⟩ := bEdge_rep (hE k)
    have := H.side_eq_of_open_mem hA0 hA2 i0 i2 hq0o (by rw [hA2i]; exact hk)
    rw [hA2i] at this
    exact he0c k this
  have hcont := wind_continuousAt hq0c
  set ε := |wind c xU - wind c xV| / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; exact half_pos (abs_pos.2 (sub_ne_zero.2 hwne))
  obtain ⟨δ0, hδ0, hδ0w⟩ := Metric.continuousAt_iff.1 hcont ε hεpos
  have hu0 : b0 - a0 ≠ 0 := sub_ne_zero.2 hab0.symm
  obtain ⟨δ1, hδ1, hUV⟩ := H.bedge_UV hA0 i0 hbe0 hq0o (J := jrot (b0 - a0)) (jcr_jrot_ne hu0)
  set J0 := jrot (b0 - a0) with hJ0
  set t := min δ1 (δ0 / (‖J0‖ + 1)) / 2 with ht
  have htpos : 0 < t := half_pos (lt_min hδ1 (div_pos hδ0 (by positivity)))
  have htδ1 : t < δ1 := by
    have := min_le_left δ1 (δ0 / (‖J0‖ + 1)); rw [ht]; linarith
  have htJ : t * ‖J0‖ < δ0 := by
    have h1 : t < δ0 / (‖J0‖ + 1) := by
      have := min_le_right δ1 (δ0 / (‖J0‖ + 1))
      have : min δ1 (δ0 / (‖J0‖ + 1)) > 0 := lt_min hδ1 (div_pos hδ0 (by positivity))
      rw [ht]; linarith
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith [norm_nonneg J0]
  have hd : ∀ τ : ℝ, |τ| = t → dist (q0 + τ • J0) q0 < δ0 := by
    intro τ hτ
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hτ]; exact htJ
  have hw1 := hδ0w (hd t (abs_of_pos htpos))
  have hw2 := hδ0w (hd (-t) (by rw [abs_neg, abs_of_pos htpos]))
  rw [Real.dist_eq] at hw1 hw2
  have hfinal : |wind c xU - wind c xV| < 2 * ε := by
    rcases hUV t htpos htδ1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [wU _ _ hxU h1, wV _ _ hxV h2]
      calc |wind c (q0 + t • J0) - wind c (q0 + (-t) • J0)|
          ≤ |wind c (q0 + t • J0) - wind c q0| + |wind c q0 - wind c (q0 + (-t) • J0)| :=
            abs_sub_le _ _ _
        _ = |wind c (q0 + t • J0) - wind c q0| + |wind c (q0 + (-t) • J0) - wind c q0| := by
            rw [abs_sub_comm (wind c q0)]
        _ < ε + ε := add_lt_add hw1 hw2
        _ = 2 * ε := by ring
    · rw [wU _ _ hxU h2, wV _ _ hxV h1]
      calc |wind c (q0 + (-t) • J0) - wind c (q0 + t • J0)|
          ≤ |wind c (q0 + (-t) • J0) - wind c q0| + |wind c q0 - wind c (q0 + t • J0)| :=
            abs_sub_le _ _ _
        _ = |wind c (q0 + (-t) • J0) - wind c q0| + |wind c (q0 + t • J0) - wind c q0| := by
            rw [abs_sub_comm (wind c q0)]
        _ < ε + ε := add_lt_add hw2 hw1
        _ = 2 * ε := by ring
  rw [hε] at hfinal
  linarith

private lemma exists_ne_near (x : Pt) {r : ℝ} (hr : 0 < r) : ∃ y ∈ Metric.ball x r, y ≠ x := by
  have hd : (!₂[1, 0] : Pt) ≠ 0 := by
    intro h; have := congrArg (fun z : Pt => z 0) h; simp at this
  obtain ⟨y, hy, hyc⟩ := exists_near_off_line x hd x (τ := 1) (Or.inl rfl) hr
  refine ⟨y, by rw [Metric.mem_ball, dist_comm]; exact hy, ?_⟩
  rintro rfl; exact lt_irrefl _ hyc

private lemma isOpen_punctured_nbhd {W O : Set Pt} (hW : IsOpen W) (hO : IsOpen O) :
    IsOpen {x | x ∈ W ∧ ∃ r > 0, ∀ y ∈ Metric.ball x r, y ≠ x → y ∈ O} := by
  rw [Metric.isOpen_iff]
  rintro x ⟨hxW, r, hr, hball⟩
  obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 hW x hxW
  refine ⟨min r ρ, lt_min hr hρ, fun y hy => ⟨hρW (Metric.ball_subset_ball (min_le_right _ _) hy), ?_⟩⟩
  by_cases hyx : y = x
  · rw [hyx]; exact ⟨r, hr, hball⟩
  · have hyO : y ∈ O := hball y (Metric.ball_subset_ball (min_le_left _ _) hy) hyx
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO y hyO
    exact ⟨ε, hε, fun z hz _ => hεO hz⟩

/-- a connected open set cannot be split by two disjoint open sets up to finitely many points -/
private lemma open_minus_finite_split {W O1 O2 Z : Set Pt} (hW : IsOpen W) (hWc : IsPreconnected W)
    (h1 : IsOpen O1) (h2 : IsOpen O2) (hd : Disjoint O1 O2) (hZ : Z.Finite)
    (hsub : W ⊆ O1 ∪ O2 ∪ Z) (hn1 : (W ∩ O1).Nonempty) (hn2 : (W ∩ O2).Nonempty) : False := by
  set O1' := {x | x ∈ W ∧ ∃ r > 0, ∀ y ∈ Metric.ball x r, y ≠ x → y ∈ O1} with hO1'
  set O2' := {x | x ∈ W ∧ ∃ r > 0, ∀ y ∈ Metric.ball x r, y ≠ x → y ∈ O2} with hO2'
  have ho1 : IsOpen O1' := isOpen_punctured_nbhd hW h1
  have ho2 : IsOpen O2' := isOpen_punctured_nbhd hW h2
  have hd' : Disjoint O1' O2' := by
    rw [Set.disjoint_left]
    rintro x ⟨-, r1, hr1, hb1⟩ ⟨-, r2, hr2, hb2⟩
    obtain ⟨y, hy, hyx⟩ := exists_ne_near x (lt_min hr1 hr2)
    exact Set.disjoint_left.1 hd (hb1 y (Metric.ball_subset_ball (min_le_left _ _) hy) hyx)
      (hb2 y (Metric.ball_subset_ball (min_le_right _ _) hy) hyx)
  have hcov : W ⊆ O1' ∪ O2' := by
    intro x hxW
    obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 hW x hxW
    by_cases hx1 : x ∈ O1
    · obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 h1 x hx1
      exact Or.inl ⟨hxW, ε, hε, fun y hy _ => hεO hy⟩
    by_cases hx2 : x ∈ O2
    · obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 h2 x hx2
      exact Or.inr ⟨hxW, ε, hε, fun y hy _ => hεO hy⟩
    have hZx : (Z \ {x}).Finite := hZ.diff
    have hxZ : x ∉ Z \ {x} := fun h => h.2 rfl
    obtain ⟨r2, hr2, hr2Z⟩ := Metric.isOpen_iff.1 hZx.isClosed.isOpen_compl x hxZ
    have hpb : ∀ y ∈ Metric.ball x (min ρ r2), y ≠ x → y ∈ O1 ∪ O2 := by
      intro y hy hyx
      have hyW := hρW (Metric.ball_subset_ball (min_le_left _ _) hy)
      rcases hsub hyW with h | h
      · exact h
      · exact absurd ⟨h, hyx⟩ (hr2Z (Metric.ball_subset_ball (min_le_right _ _) hy))
    rcases punctured_ball_split h1 h2 hd hpb with h | h
    · exact Or.inl ⟨hxW, min ρ r2, lt_min hρ hr2, h⟩
    · exact Or.inr ⟨hxW, min ρ r2, lt_min hρ hr2, h⟩
  rcases hWc.subset_or_subset ho1 ho2 hd' hcov with h | h
  · obtain ⟨x, hxW, hxO⟩ := hn2
    obtain ⟨-, r, hr, hball⟩ := h hxW
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 h2 x hxO
    obtain ⟨y, hy, hyx⟩ := exists_ne_near x (lt_min hr hε)
    exact Set.disjoint_left.1 hd (hball y (Metric.ball_subset_ball (min_le_left _ _) hy) hyx)
      (hεO (Metric.ball_subset_ball (min_le_right _ _) hy))
  · obtain ⟨x, hxW, hxO⟩ := hn1
    obtain ⟨-, r, hr, hball⟩ := h hxW
    obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 h1 x hxO
    obtain ⟨y, hy, hyx⟩ := exists_ne_near x (lt_min hr hε)
    exact Set.disjoint_left.1 hd (hεO (Metric.ball_subset_ball (min_le_right _ _) hy))
      (hball y (Metric.ball_subset_ball (min_le_left _ _) hy) hyx)

private lemma interior_not_mem_other {S : Set (PlacedTile P)} (hdisj : DisjointInteriors S)
    {X Y : PlacedTile P} (hX : X ∈ S) (hY : Y ∈ S) (hXY : X ≠ Y) {x : Pt}
    (hx : x ∈ interior X.carrier) : x ∉ Y.carrier := by
  intro hxY
  rw [← tile_regular Y, Metric.mem_closure_iff] at hxY
  obtain ⟨ε, hε, hεX⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  obtain ⟨y, hyY, hxy⟩ := hxY ε hε
  exact interiors_disjoint hdisj hX hY hXY (hεX (by rw [Metric.mem_ball, dist_comm]; exact hxy)) hyY

/-- **Dual connectedness.** -/
private lemma JSetup.dualConnected {S G : Set (PlacedTile P)} (H : JSetup S G)
    (hint : IsConnected (interior (support G))) : DualConnected G := by
  classical
  intro A0 hA0 B hB
  set R := fun X Y : PlacedTile P => X ∈ G ∧ Y ∈ G ∧ SharesSide X Y with hR
  set C := {X ∈ G | Relation.ReflTransGen R A0 X} with hC
  by_contra hB'
  set D := G \ C with hD
  have hBD : B ∈ D := ⟨hB, fun h => hB' h.2⟩
  have hA0C : A0 ∈ C := ⟨hA0, Relation.ReflTransGen.refl⟩
  have hCD : ∀ X ∈ C, ∀ Y ∈ D, ∀ p ∈ X.carrier, p ∈ Y.carrier → p ∈ gVerts G := by
    intro X hX Y hY p hpX hpY
    by_contra hpv
    have hXY : X ≠ Y := by rintro rfl; exact hY.2 hX
    have hpXi : p ∉ interior X.carrier := fun h =>
      interior_not_mem_other H.disj (H.sub hX.1) (H.sub hY.1) hXY h hpY
    have hpf : p ∈ frontier X.carrier := by
      rw [mem_frontier_iff_of_closed (tile_isClosed X)]; exact ⟨hpX, hpXi⟩
    rw [tile_frontier_eq, Set.mem_iUnion] at hpf
    obtain ⟨i, hpi⟩ := hpf
    have hpo : p ∈ openSegment ℝ (X.vertex i) (X.vertex (finRotate _ i)) := by
      rw [tile_side_eq] at hpi
      refine mem_openSegment_of_ne_left_right ?_ ?_ hpi
      · intro h; exact hpv (Set.mem_biUnion hX.1 ⟨i, h⟩)
      · intro h; exact hpv (Set.mem_biUnion hX.1 ⟨_, h⟩)
    obtain ⟨j, hj⟩ := H.partner hX.1 (H.sub hY.1) hXY i hpo hpY
    apply hY.2
    have hS : SharesSide X Y := by
      unfold SharesSide; exact ⟨hXY, X.side i, ⟨i, rfl⟩, ⟨j, hj⟩⟩
    have hRXY : R X Y := by simp only [hR]; exact ⟨hX.1, hY.1, hS⟩
    exact ⟨hY.1, Relation.ReflTransGen.tail hX.2 hRXY⟩
  have hCfin : C.Finite := H.fin.subset (fun X hX => hX.1)
  have hDfin : D.Finite := H.fin.subset (fun X hX => hX.1)
  apply open_minus_finite_split (W := interior (support G))
    (O1 := interior (support G) \ support D) (O2 := interior (support G) \ support C)
    (Z := gVerts G) isOpen_interior hint.isPreconnected
    (isOpen_interior.sdiff (support_isClosed hDfin)) (isOpen_interior.sdiff (support_isClosed hCfin))
  · rw [Set.disjoint_left]
    rintro x ⟨hxU, hxD⟩ ⟨-, hxC⟩
    obtain ⟨X, hX, hxX⟩ := mem_support_iff'.1 (interior_subset hxU)
    by_cases hXC : X ∈ C
    · exact hxC (carrier_subset_support hXC hxX)
    · exact hxD (carrier_subset_support (show X ∈ D from ⟨hX, hXC⟩) hxX)
  · exact gVerts_finite H.fin
  · intro x hxU
    by_cases hxD : x ∈ support D
    · by_cases hxC : x ∈ support C
      · obtain ⟨X, hX, hxX⟩ := mem_support_iff'.1 hxC
        obtain ⟨Y, hY, hxY⟩ := mem_support_iff'.1 hxD
        exact Or.inr (hCD X hX Y hY x hxX hxY)
      · exact Or.inl (Or.inr ⟨hxU, hxC⟩)
    · exact Or.inl (Or.inl ⟨hxU, hxD⟩)
  · obtain ⟨x, hx⟩ := (tileDisk A0).interior_nonempty
    refine ⟨x, interior_mono (carrier_subset_support hA0) hx, interior_mono
      (carrier_subset_support hA0) hx, ?_⟩
    intro hxD
    obtain ⟨Y, hY, hxY⟩ := mem_support_iff'.1 hxD
    have hne : A0 ≠ Y := by rintro rfl; exact hY.2 hA0C
    exact interior_not_mem_other H.disj (H.sub hA0) (H.sub hY.1) hne hx hxY
  · obtain ⟨x, hx⟩ := (tileDisk B).interior_nonempty
    refine ⟨x, interior_mono (carrier_subset_support hB) hx, interior_mono
      (carrier_subset_support hB) hx, ?_⟩
    intro hxC
    obtain ⟨Y, hY, hxY⟩ := mem_support_iff'.1 hxC
    have hne : B ≠ Y := by rintro rfl; exact hBD.2 hY
    exact interior_not_mem_other H.disj (H.sub hB) (H.sub hY.1) hne hx hxY

private lemma cycle_inter_endpoints {S G : Set (PlacedTile P)} (H : JSetup S G) {m : ℕ} (hm : 3 ≤ m)
    {c : Fin m → Pt} (hc : Function.Injective c)
    (hE : ∀ k, segment ℝ (c k) (c (finRotate m k)) ∈ bEdges G) {k l : Fin m} (hkl : k ≠ l)
    {x : Pt} (hxk : x ∈ segment ℝ (c k) (c (finRotate m k)))
    (hxl : x ∈ segment ℝ (c l) (c (finRotate m l))) :
    x ∈ ({c k, c (finRotate m k)} : Set Pt) := by
  by_contra hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
  have hxo := mem_openSegment_of_ne_left_right (Ne.symm hx.1) (Ne.symm hx.2) hxk
  obtain ⟨A, hA, i, hAi, -, hends⟩ := bEdge_rep (hE k)
  have hxA : x ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)) := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hxo
    · rw [h1, h2, openSegment_symm]; exact hxo
  obtain ⟨A2, hA2, i2, hA2i, -, -⟩ := bEdge_rep (hE l)
  have := H.side_eq_of_open_mem hA hA2 i i2 hxA (by rw [hA2i]; exact hxl)
  rw [hAi, hA2i] at this
  exact hkl (cyc_seg_inj hm hc this)

private theorem polygonalJordanBoundary_aux (S : Set (PlacedTile P)) (hdisj : DisjointInteriors S)
    (hsts : SideToSideSet S) (G : Set (PlacedTile P)) (hG : G ⊆ S) (hfin : G.Finite)
    (hne : G.Nonempty) (hcov : support G ⊆ interior (support S))
    (hint : IsConnected (interior (support G))) (hcompl : IsConnected (support G)ᶜ) :
    ∃ L : FaceGroup S, L.faces = G := by
  have H : JSetup S G := ⟨hdisj, hsts, hG, hfin, hcov⟩
  obtain ⟨A1, hA1⟩ := hne
  have hbne : (bEdges G).Nonempty := by
    have hfne : (frontier (support G)).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty] at hemp
      rcases isClopen_iff.1 hemp with h | h
      · obtain ⟨x, hx⟩ := (tileDisk A1).interior_nonempty
        have : x ∈ support G := carrier_subset_support hA1 (interior_subset hx)
        rw [h] at this; exact this
      · obtain ⟨x, hx⟩ := hcompl.nonempty
        exact hx (h ▸ Set.mem_univ x)
    obtain ⟨x, hx⟩ := hfne
    obtain ⟨e, he, -⟩ := H.frontier_subset_bEdges hx
    exact ⟨e, he⟩
  obtain ⟨m, hm, c, hc, hE⟩ := H.exists_bcycle hbne
  have hall := H.bEdges_in_cycle hint hcompl hm hc hE
  have hfr : frontier (support G) = ⋃ k, segment ℝ (c k) (c (finRotate m k)) := by
    rw [H.frontier_eq_bEdges]
    ext x
    constructor
    · rintro ⟨e, he, hx⟩
      obtain ⟨k, rfl⟩ := hall e he
      exact Set.mem_iUnion.2 ⟨k, hx⟩
    · intro hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hx
      exact ⟨_, hE k, hk⟩
  let D : PolygonalDisk :=
    { carrier := support G
      n := m
      three_le := hm
      vertex := c
      vertex_injective := hc
      compact := hfin.isCompact_biUnion (fun A _ => (tileDisk A).compact)
      interior_nonempty := by
        obtain ⟨x, hx⟩ := (tileDisk A1).interior_nonempty
        exact ⟨x, interior_mono (carrier_subset_support hA1) hx⟩
      regular_closed := by
        apply Set.Subset.antisymm (closure_minimal interior_subset (support_isClosed hfin))
        intro x hx
        obtain ⟨A, hA, hxA⟩ := mem_support_iff'.1 hx
        rw [← tile_regular A] at hxA
        exact closure_mono (interior_mono (carrier_subset_support hA)) hxA
      interior_pathConnected := (isOpen_interior.isConnected_iff_isPathConnected).1 hint
      frontier_eq := hfr
      simple := by
        intro i j hij x hx
        exact ⟨cycle_inter_endpoints H hm hc hE hij hx.1 hx.2,
          cycle_inter_endpoints H hm hc hE (Ne.symm hij) hx.2 hx.1⟩ }
  refine ⟨{ faces := G
            faces_sub := hG
            finite := hfin
            disk := D
            carrier_eq := rfl
            side_whole := ?_
            vertex_retained := ?_
            dualConnected := H.dualConnected hint }, rfl⟩
  · intro k
    obtain ⟨A, hA, i, hAi, -⟩ := hE k
    exact ⟨A, hA, i, hAi⟩
  · rintro v ⟨C, hC, hvC⟩ hvF
    change v ∈ frontier (support G) at hvF
    rw [hfr] at hvF
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hvF
    by_contra hvn
    have h1 : v ≠ c k := fun h => hvn ⟨k, h.symm⟩
    have h2 : v ≠ c (finRotate m k) := fun h => hvn ⟨_, h.symm⟩
    have hvo := mem_openSegment_of_ne_left_right (Ne.symm h1) (Ne.symm h2) hk
    obtain ⟨A, hA, i, -, -, hends⟩ := bEdge_rep (hE k)
    have hvA : v ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)) := by
      rcases hends with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; exact hvo
      · rw [e1, e2, openSegment_symm]; exact hvo
    exact H.no_vertex hA hC i hvA hvC

end JordanHelpers

/-- **Polygonal Jordan boundary** (classical helper; must be proved, never
assumed).  In a side-to-side cellulation `S`, a finite nonempty union of
complete faces lying in the interior of the covered region, with connected
interior and connected open complement, has a single simple polygonal
boundary consisting of complete original sides; i.e. it is a `FaceGroup`. -/
theorem polygonalJordanBoundary (S : Set (PlacedTile P)) (hdisj : DisjointInteriors S)
    (hsts : SideToSideSet S) (G : Set (PlacedTile P)) (hG : G ⊆ S) (hfin : G.Finite)
    (hne : G.Nonempty) (hcov : support G ⊆ interior (support S))
    (hint : IsConnected (interior (support G))) (hcompl : IsConnected (support G)ᶜ) :
    ∃ L : FaceGroup S, L.faces = G :=
  polygonalJordanBoundary_aux S hdisj hsts G hG hfin hne hcov hint hcompl

/-- A polygonal arc given by its list of `n + 2` breakpoints. -/
structure PolyArc where
  n : ℕ
  pt : Fin (n + 2) → Pt

namespace PolyArc

variable (α : PolyArc)

/-- The `i`-th segment of the arc. -/
def seg (i : Fin (α.n + 1)) : Set Pt := segment ℝ (α.pt i.castSucc) (α.pt i.succ)

/-- The carrier of the arc. -/
def carrier : Set Pt := ⋃ i, α.seg i

/-- Initial point. -/
def start : Pt := α.pt 0

/-- Final point. -/
def stop : Pt := α.pt (Fin.last (α.n + 1))

/-- The arc is simple: distinct breakpoints, and two segments meet only in
shared breakpoints. -/
def IsSimple : Prop :=
  Function.Injective α.pt ∧
    ∀ i j : Fin (α.n + 1), i ≠ j →
      α.seg i ∩ α.seg j ⊆
        ({α.pt i.castSucc, α.pt i.succ} : Set Pt) ∩ {α.pt j.castSucc, α.pt j.succ}

/-- The arc runs in the original skeleton of `S`: each of its segments is a
complete listed side of a tile of `S`. -/
def IsSkeletal (S : Set (PlacedTile P)) : Prop :=
  ∀ i, ∃ A ∈ S, HasEdge A (α.seg i)

end PolyArc

/-- `γ` is a period-one parametrization of the simple closed curve `K`. -/
def IsLoopParam (K : Set Pt) (γ : ℝ → Pt) : Prop :=
  Continuous γ ∧ Function.Periodic γ 1 ∧ InjOn γ (Ico 0 1) ∧ γ '' Ico 0 1 = K

/-- The points `x 0, …, x (k-1)` appear in this cyclic order along the loop
`γ` (in its direction of traversal). -/
def PointsInOrder (γ : ℝ → Pt) {k : ℕ} (x : Fin k → Pt) : Prop :=
  ∃ t : Fin k → ℝ, StrictMono t ∧ (∀ i j, t j < t i + 1) ∧ ∀ i, γ (t i) = x i

/-- Two period-one loops are freely homotopic inside `U`. -/
def LoopsHomotopicIn (U : Set Pt) (γ₀ γ₁ : ℝ → Pt) : Prop :=
  ∃ F : ℝ × ℝ → Pt, Continuous F ∧ (∀ s t, F (s, t + 1) = F (s, t)) ∧
    (∀ t, F (0, t) = γ₀ t) ∧ (∀ t, F (1, t) = γ₁ t) ∧
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t, F (s, t) ∈ U

/-- Matching cyclic order on the two boundary curves of an annulus `U`: the
outer points `x` and the inner points `y` appear in the same cyclic order for
compatible (freely homotopic in `U`) orientations of the two curves. -/
def MatchingCyclicOrder (U Kout Kin : Set Pt) {k : ℕ} (x y : Fin k → Pt) : Prop :=
  ∃ γo γi : ℝ → Pt, IsLoopParam Kout γo ∧ IsLoopParam Kin γi ∧
    LoopsHomotopicIn U γo γi ∧ PointsInOrder γo x ∧ PointsInOrder γi y

/-- Step 1 of the blueprint proof of `plAnnulusRouting`: Topological routing.
In an annulus, points in matching cyclic order can be joined by pairwise disjoint simple
continuous arcs. -/
private lemma plAnnulusRouting_step1_topological (A C : PolygonalDisk)
    (hC : C.carrier ⊆ interior A.carrier) {k : ℕ} (x y : Fin k → Pt)
    (hx : ∀ i, x i ∈ frontier A.carrier) (hy : ∀ i, y i ∈ frontier C.carrier)
    (hxi : Function.Injective x) (hyi : Function.Injective y)
    (horder : MatchingCyclicOrder (A.carrier \ interior C.carrier) (frontier A.carrier)
      (frontier C.carrier) x y) :
    ∃ γ : Fin k → ℝ → Pt,
      (∀ i, Continuous (γ i)) ∧
      (∀ i, γ i 0 = x i) ∧
      (∀ i, γ i 1 = y i) ∧
      (∀ i, ∀ t ∈ Set.Ioo (0:ℝ) 1, γ i t ∈ interior A.carrier \ C.carrier) ∧
      (∀ i, Function.Injective (Set.restrict (Set.Icc (0:ℝ) 1) (γ i))) ∧
      (∀ i j, i ≠ j → Disjoint (γ i '' Set.Icc (0:ℝ) 1) (γ j '' Set.Icc (0:ℝ) 1)) := by
  sorry

/-- Step 1 of the blueprint proof of `plAnnulusRouting_step2_plApprox`: Separation of arcs.
For a finite family of disjoint continuous paths, there exist disjoint open neighborhoods around each. -/
private lemma plAnnulusRouting_step2_plApprox_step1_separation {k : ℕ}
    (γ : Fin k → ℝ → Tilings.Pt)
    (hcont : ∀ i, Continuous (γ i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (γ i '' Set.Icc (0:ℝ) 1) (γ j '' Set.Icc (0:ℝ) 1)) :
    ∃ U : Fin k → Set Tilings.Pt, (∀ i, IsOpen (U i)) ∧
      (∀ i, γ i '' Set.Icc (0:ℝ) 1 ⊆ U i) ∧
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) := sorry

/-- Step 2 of the blueprint proof of `plAnnulusRouting_step2_plApprox`: Single arc approximation.
A single continuous arc disjoint from C can be PL-approximated within its neighborhood. -/
private lemma plAnnulusRouting_step2_plApprox_step2_single (A C : Tilings.PolygonalDisk)
    (hC : C.carrier ⊆ interior A.carrier) (x y : Tilings.Pt)
    (γ : ℝ → Tilings.Pt)
    (hcont : Continuous γ)
    (hend_x : γ 0 = x)
    (hend_y : γ 1 = y)
    (hin : ∀ t ∈ Set.Ioo (0:ℝ) 1, γ t ∈ interior A.carrier \ C.carrier)
    (hsimp : Function.Injective (Set.restrict (Set.Icc (0:ℝ) 1) γ))
    (U : Set Tilings.Pt) (hU_open : IsOpen U) (hU_supset : γ '' Set.Icc (0:ℝ) 1 ⊆ U) :
    ∃ α : Tilings.Geometry.PolyArc,
      α.IsSimple ∧ α.start = x ∧ α.stop = y ∧
      α.carrier ⊆ A.carrier \ interior C.carrier ∧
      α.carrier \ {x, y} ⊆ interior A.carrier \ C.carrier ∧
      α.carrier ⊆ U := sorry

/-- Step 2 of the blueprint proof of `plAnnulusRouting`: PL approximation.
Any family of pairwise disjoint, simple continuous arcs in a polygonal domain
connecting boundary points can be approximated by pairwise disjoint simple polygonal arcs. -/
private lemma plAnnulusRouting_step2_plApprox (A C : PolygonalDisk)
    (hC : C.carrier ⊆ interior A.carrier) {k : ℕ} (x y : Fin k → Pt)
    (γ : Fin k → ℝ → Pt)
    (hcont : ∀ i, Continuous (γ i))
    (hend_x : ∀ i, γ i 0 = x i)
    (hend_y : ∀ i, γ i 1 = y i)
    (hin : ∀ i, ∀ t ∈ Set.Ioo (0:ℝ) 1, γ i t ∈ interior A.carrier \ C.carrier)
    (hsimp : ∀ i, Function.Injective (Set.restrict (Set.Icc (0:ℝ) 1) (γ i)))
    (hdisj : ∀ i j, i ≠ j → Disjoint (γ i '' Set.Icc (0:ℝ) 1) (γ j '' Set.Icc (0:ℝ) 1)) :
    ∃ α : Fin k → PolyArc, ∀ i,
      (α i).IsSimple ∧ (α i).start = x i ∧ (α i).stop = y i ∧
      (α i).carrier ⊆ A.carrier \ interior C.carrier ∧
      (α i).carrier \ {x i, y i} ⊆ interior A.carrier \ C.carrier ∧
      ∀ j, j ≠ i → Disjoint (α i).carrier (α j).carrier := by
  obtain ⟨U, hU_open, hU_supset, hU_disj⟩ :=
    plAnnulusRouting_step2_plApprox_step1_separation γ hcont hdisj
  have h_ex : ∀ i, ∃ α : PolyArc,
      (α).IsSimple ∧ (α).start = x i ∧ (α).stop = y i ∧
      (α).carrier ⊆ A.carrier \ interior C.carrier ∧
      (α).carrier \ {x i, y i} ⊆ interior A.carrier \ C.carrier ∧
      (α).carrier ⊆ U i := by
    intro i
    exact plAnnulusRouting_step2_plApprox_step2_single A C hC (x i) (y i) (γ i)
      (hcont i) (hend_x i) (hend_y i) (hin i) (hsimp i) (U i) (hU_open i) (hU_supset i)
  choose α hα using h_ex
  use α
  intro i
  obtain ⟨hsimp_i, hstart_i, hstop_i, hcarr_i, hcarr_int_i, hU_i⟩ := hα i
  refine ⟨hsimp_i, hstart_i, hstop_i, hcarr_i, hcarr_int_i, ?_⟩
  intro j hneq
  have hU_disj_ij := hU_disj i j hneq.symm
  exact hU_disj_ij.mono hU_i (hα j).2.2.2.2.2

/-- **PL annulus routing** (classical helper; must be proved, never assumed).
In the polygonal annulus `A \ int C`, distinct outer points and distinct inner
points in matching cyclic order are joined by pairwise disjoint simple
polygonal arcs meeting the boundary only at their endpoints. -/
theorem plAnnulusRouting (A C : PolygonalDisk) (hC : C.carrier ⊆ interior A.carrier)
    {k : ℕ} (x y : Fin k → Pt) (hx : ∀ i, x i ∈ frontier A.carrier)
    (hy : ∀ i, y i ∈ frontier C.carrier) (hxi : Function.Injective x)
    (hyi : Function.Injective y)
    (horder : MatchingCyclicOrder (A.carrier \ interior C.carrier) (frontier A.carrier)
      (frontier C.carrier) x y) :
    ∃ α : Fin k → PolyArc, ∀ i,
      (α i).IsSimple ∧ (α i).start = x i ∧ (α i).stop = y i ∧
      (α i).carrier ⊆ A.carrier \ interior C.carrier ∧
      (α i).carrier \ {x i, y i} ⊆ interior A.carrier \ C.carrier ∧
      ∀ j, j ≠ i → Disjoint (α i).carrier (α j).carrier := by
  obtain ⟨γ, hcont, hend_x, hend_y, hin, hsimp, hdisj⟩ :=
    plAnnulusRouting_step1_topological A C hC x y hx hy hxi hyi horder
  exact plAnnulusRouting_step2_plApprox A C hC x y γ hcont hend_x hend_y hin hsimp hdisj

/-! ## Inside- and outside-anchored groupings -/

/-! ### Helpers for `regularGrouping` -/

private lemma rg_coord_sub_le (x y : Pt) (i : Fin 2) : |x i - y i| ≤ dist x y := by
  have := PiLp.norm_apply_le (x - y) i
  rw [Real.norm_eq_abs, PiLp.sub_apply] at this
  rwa [dist_eq_norm]

private lemma rg_mkPt0 (x y : ℝ) : mkPt x y 0 = x := by simp [mkPt]

private lemma rg_mkPt1 (x y : ℝ) : mkPt x y 1 = y := by simp [mkPt]

private lemma rg_square_mono {c : Pt} {h h' : ℝ} (hh : h ≤ h') : square c h ⊆ square c h' :=
  fun _ hx => ⟨hx.1.trans hh, hx.2.trans hh⟩

private lemma rg_binf_mono {r s : ℝ} (h : r ≤ s) : Binf r ⊆ Binf s :=
  fun _ hx => ⟨hx.1.trans h, hx.2.trans h⟩

private lemma rg_clamp {a h r : ℝ} (hh : 0 ≤ h) (hr : 0 ≤ r) (ha : |a| ≤ h + r) :
    |max (-h) (min h a)| ≤ h ∧ |a - max (-h) (min h a)| ≤ r := by
  rw [abs_le] at ha
  rw [abs_le, abs_le]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [min_def, max_def] <;> split_ifs <;> linarith

private lemma rg_square_add {c : Pt} {h r : ℝ} (hh : 0 ≤ h) (hr : 0 ≤ r) :
    square c (h + r) ⊆ square c h + Binf r := by
  intro x hx
  obtain ⟨h0, h0'⟩ := rg_clamp hh hr hx.1
  obtain ⟨h1, h1'⟩ := rg_clamp hh hr hx.2
  refine Set.mem_add.2 ⟨mkPt (c 0 + max (-h) (min h (x 0 - c 0))) (c 1 + max (-h) (min h (x 1 - c 1))),
    ?_, x - mkPt (c 0 + max (-h) (min h (x 0 - c 0))) (c 1 + max (-h) (min h (x 1 - c 1))), ?_, by abel⟩
  · refine ⟨?_, ?_⟩ <;> simp only [rg_mkPt0, rg_mkPt1, add_sub_cancel_left] <;> assumption
  · refine ⟨?_, ?_⟩ <;> simp only [PiLp.sub_apply, rg_mkPt0, rg_mkPt1]
    · rw [show x 0 - (c 0 + max (-h) (min h (x 0 - c 0))) = (x 0 - c 0) - max (-h) (min h (x 0 - c 0)) by ring]
      exact h0'
    · rw [show x 1 - (c 1 + max (-h) (min h (x 1 - c 1))) = (x 1 - c 1) - max (-h) (min h (x 1 - c 1)) by ring]
      exact h1'

private lemma rg_ball_subset_square (c : Pt) (h : ℝ) : Metric.ball c h ⊆ square c h := by
  intro x hx
  rw [Metric.mem_ball] at hx
  exact ⟨(rg_coord_sub_le x c 0).trans hx.le, (rg_coord_sub_le x c 1).trans hx.le⟩

private lemma rg_center_mem_interior {c : Pt} {h : ℝ} (hh : 0 < h) : c ∈ interior (square c h) :=
  interior_mono (rg_ball_subset_square c h) (by rw [Metric.isOpen_ball.interior_eq]; exact Metric.mem_ball_self hh)

private lemma rg_square_convex (c : Pt) (h : ℝ) : Convex ℝ (square c h) := by
  intro x hx y hy a b ha hb hab
  have key : ∀ i : Fin 2, |x i - c i| ≤ h → |y i - c i| ≤ h → |(a • x + b • y) i - c i| ≤ h := by
    intro i hxi hyi
    have e : (a • x + b • y) i - c i = a * (x i - c i) + b * (y i - c i) := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      linear_combination (c i) * hab
    rw [e]
    calc |a * (x i - c i) + b * (y i - c i)| ≤ |a * (x i - c i)| + |b * (y i - c i)| := abs_add_le _ _
      _ = a * |x i - c i| + b * |y i - c i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * h + b * h := by gcongr
      _ = h := by linear_combination h * hab
  exact ⟨key 0 hx.1 hy.1, key 1 hx.2 hy.2⟩

private lemma rg_square_closed (c : Pt) (h : ℝ) : IsClosed (square c h) := by
  have h0 : Continuous fun x : Pt => x 0 := PiLp.continuous_apply 2 _ 0
  have h1 : Continuous fun x : Pt => x 1 := PiLp.continuous_apply 2 _ 1
  exact (isClosed_le ((h0.sub continuous_const).abs) continuous_const).inter
    (isClosed_le ((h1.sub continuous_const).abs) continuous_const)

private lemma rg_square_subset_closure_interior {c : Pt} {h : ℝ} (hh : 0 < h) :
    square c h ⊆ closure (interior (square c h)) := by
  rw [(rg_square_convex c h).closure_interior_eq_closure_of_nonempty_interior
    ⟨c, rg_center_mem_interior hh⟩, (rg_square_closed c h).closure_eq]

private lemma rg_seg_coord {a b z : Pt} (hz : z ∈ segment ℝ a b) {i : Fin 2} (hab : a i = b i) :
    z i = a i := by
  obtain ⟨t, -, -, rfl⟩ := mem_segment_iff'.1 hz
  simp [hab]

private lemma rg_far_mem {O : Set Pt} {c : Pt} {R : ℝ} (hR : 0 ≤ R) (hO : (square c R)ᶜ ⊆ O) {x : Pt}
    (hx : x ∉ square c R) : x ∈ connectedComponentIn O (mkPt (c 0 + (R + 1)) (c 1 + (R + 1))) := by
  set p := mkPt (c 0 + (R + 1)) (c 1 + (R + 1)) with hp
  suffices hT : ∃ T : Set Pt, IsPreconnected T ∧ x ∈ T ∧ p ∈ T ∧ T ⊆ (square c R)ᶜ by
    obtain ⟨T, hT, hxT, hpT, hTs⟩ := hT
    have h1 := hT.subset_connectedComponentIn hxT (hTs.trans hO) hpT
    rw [← connectedComponentIn_eq h1]
    exact mem_connectedComponentIn (hO hx)
  have hR1 : R < |R + 1| := by rw [abs_of_pos (by linarith)]; linarith
  simp only [square, Set.mem_setOf_eq, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · set x' := mkPt (x 0) (c 1 + (R + 1))
    refine ⟨segment ℝ x x' ∪ segment ℝ x' p, (convex_segment _ _).isPreconnected.union x'
      (right_mem_segment ℝ _ _) (left_mem_segment ℝ _ _) (convex_segment _ _).isPreconnected,
      Or.inl (left_mem_segment ℝ _ _), Or.inr (right_mem_segment ℝ _ _), ?_⟩
    rintro z (hz | hz) hzs
    · have := rg_seg_coord hz (i := 0) (by simp [x', rg_mkPt0])
      exact absurd hzs.1 (by rw [this]; exact not_le.2 hx)
    · have := rg_seg_coord hz (i := 1) (by simp [x', p, rg_mkPt1])
      exact absurd hzs.2 (by rw [this]; simp only [x', rg_mkPt1, add_sub_cancel_left]; exact not_le.2 hR1)
  · set x' := mkPt (c 0 + (R + 1)) (x 1)
    refine ⟨segment ℝ x x' ∪ segment ℝ x' p, (convex_segment _ _).isPreconnected.union x'
      (right_mem_segment ℝ _ _) (left_mem_segment ℝ _ _) (convex_segment _ _).isPreconnected,
      Or.inl (left_mem_segment ℝ _ _), Or.inr (right_mem_segment ℝ _ _), ?_⟩
    rintro z (hz | hz) hzs
    · have := rg_seg_coord hz (i := 1) (by simp [x', rg_mkPt1])
      exact absurd hzs.2 (by rw [this]; exact not_le.2 hx)
    · have := rg_seg_coord hz (i := 0) (by simp [x', p, rg_mkPt0])
      exact absurd hzs.1 (by rw [this]; simp only [x', rg_mkPt0, add_sub_cancel_left]; exact not_le.2 hR1)

private lemma rg_tile_coord (M : MeshConstants P) (A : PlacedTile P) {x y : Pt} (hx : x ∈ A.carrier)
    (hy : y ∈ A.carrier) (i : Fin 2) : |x i - y i| ≤ M.D := by
  refine (rg_coord_sub_le x y i).trans ((Metric.dist_le_diam_of_mem (tileDisk A).compact.isBounded hx hy).trans ?_)
  have : Metric.diam A.carrier = Metric.diam (P.disk A.form).carrier := by
    rw [PlacedTile.carrier]; exact diam_vadd _ _
  show Metric.diam A.carrier ≤ M.D
  rw [this]; exact M.diam_le _

private lemma rg_halfplane_convex (σ : ℝ) (d a : Pt) : Convex ℝ {x : Pt | σ * jcr d (x - a) < 0} := by
  intro x hx y hy s t hs ht hst
  obtain rfl : t = 1 - s := by linarith
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have e : σ * jcr d (s • x + (1 - s) • y - a) = s * (σ * jcr d (x - a)) + (1 - s) * (σ * jcr d (y - a)) := by
    simp only [jcr, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e]
  rcases hs.lt_or_eq with hs' | hs'
  · nlinarith
  · subst hs'; simp only [zero_mul, zero_add, sub_zero, one_mul]; exact hy

/-- `JSetup.bedge_sides`, also recording the closed half-disk inside the face -/
private lemma rg_bedge_sides {S G : Set (PlacedTile P)} (H : JSetup S G) {A : PlacedTile P}
    (hA : A ∈ G) (i : Fin (P.disk A.form).n)
    (hbe : ∀ A' ∈ G, A' ≠ A → ¬ HasEdge A' (A.side i)) {q : Pt}
    (hq : q ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i))) :
    ∃ r > 0, ∃ σ : ℝ, ∀ x ∈ Metric.ball q r,
      (σ * jcr (A.vertex (finRotate _ i) - A.vertex i) (x - A.vertex i) < 0 → x ∉ support G) ∧
      (0 ≤ σ * jcr (A.vertex (finRotate _ i) - A.vertex i) (x - A.vertex i) → x ∈ A.carrier) := by
  classical
  obtain ⟨r, hr, σ, -, hch⟩ := tile_halfdisk A i hq
  set K' := ⋃ A' ∈ G \ {A}, A'.carrier with hK'
  have hK'c : IsClosed K' := (H.fin.diff).isClosed_biUnion (fun D _ => tile_isClosed D)
  have hqK' : q ∉ K' := by
    intro h
    simp only [hK', Set.mem_iUnion] at h
    obtain ⟨A', ⟨hA'G, hA'A⟩, hqA'⟩ := h
    have hne : A ≠ A' := fun h => hA'A (h ▸ rfl)
    obtain ⟨j, hj⟩ := H.partner hA (H.sub hA'G) hne i hq hqA'
    exact hbe A' hA'G (Ne.symm hne) ⟨j, hj⟩
  obtain ⟨ρ, hρ, hρK⟩ := Metric.isOpen_iff.1 hK'c.isOpen_compl q hqK'
  refine ⟨min r ρ, lt_min hr hρ, σ, fun x hx => ⟨fun h => ?_, fun h => ?_⟩⟩
  · intro hxG
    obtain ⟨A', hA'G, hxA'⟩ := mem_support_iff'.1 hxG
    by_cases hAA : A' = A
    · subst hAA
      have := ((hch x (Metric.ball_subset_ball (min_le_left _ _) hx)).2.1).1 hxA'
      linarith
    · apply hρK (Metric.ball_subset_ball (min_le_right _ _) hx)
      simp only [hK', Set.mem_iUnion]
      exact ⟨A', ⟨hA'G, hAA⟩, hxA'⟩
  · exact ((hch x (Metric.ball_subset_ball (min_le_left _ _) hx)).2.1).2 h

/-- `lem:regular-grouping`: a finite STS patch of mesh `D` covering `Ω`, and a
square `Q` with `Q + B∞(3D) ⊂ int Ω`.  There is a group `L` of complete faces,
a polygonal disk with connected face-dual graph, with
`Q ⊂ L ⊂ Q + B∞(D)`, inside-anchored at `Q`. -/
theorem regularGrouping (M : MeshConstants P) (S : Patch P) (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h) (hQ : square c h + Binf (3 * M.D) ⊆ interior Ω.carrier) :
    ∃ L : FaceGroup S.tiles, square c h ⊆ L.carrier ∧ L.carrier ⊆ square c h + Binf M.D ∧
      L.InsideAnchored (square c h) := by
  classical
  have hD := M.D_pos
  have hdisj := S.disjoint
  set Q := square c h with hQdef
  set R := h + M.D with hRdef
  set Q' := square c R with hQ'def
  set U₀ : Set (PlacedTile P) := {A ∈ S.tiles | (interior A.carrier ∩ interior Q).Nonempty} with hU₀
  set U := support U₀ with hUdef
  set O := Uᶜ with hOdef
  set p := mkPt (c 0 + (R + 1)) (c 1 + (R + 1)) with hpdef
  set W := connectedComponentIn O p with hWdef
  set G : Set (PlacedTile P) := {A ∈ S.tiles | ¬ interior A.carrier ⊆ W} with hGdef
  have hU₀S : U₀ ⊆ S.tiles := fun A hA => hA.1
  have hU₀fin : U₀.Finite := S.finite.subset hU₀S
  have hUc : IsClosed U := support_isClosed hU₀fin
  have hOo : IsOpen O := hUc.isOpen_compl
  -- the faces meeting the open square stay in the buffer `Q'`
  have hUQ' : U ⊆ Q' := by
    intro x hx
    obtain ⟨A, hA, hxA⟩ := mem_support_iff'.1 hx
    obtain ⟨w, hwA, hwQ⟩ := hA.2
    have hwQ' : w ∈ Q := interior_subset hwQ
    have h0 := rg_tile_coord M A hxA (interior_subset hwA) 0
    have h1 := rg_tile_coord M A hxA (interior_subset hwA) 1
    refine ⟨?_, ?_⟩
    · calc |x 0 - c 0| = |(x 0 - w 0) + (w 0 - c 0)| := by ring_nf
        _ ≤ |x 0 - w 0| + |w 0 - c 0| := abs_add_le _ _
        _ ≤ R := by linarith [hwQ'.1]
    · calc |x 1 - c 1| = |(x 1 - w 1) + (w 1 - c 1)| := by ring_nf
        _ ≤ |x 1 - w 1| + |w 1 - c 1| := abs_add_le _ _
        _ ≤ R := by linarith [hwQ'.2]
  have hQ'B : Q' ⊆ Q + Binf M.D := rg_square_add hh.le hD.le
  have hQ'Ω : Q' ⊆ interior (support S.tiles) := by
    rw [hcov]
    exact hQ'B.trans ((Set.add_subset_add_left (rg_binf_mono (by linarith))).trans hQ)
  have hQQ' : Q ⊆ Q' := rg_square_mono (by linarith)
  have hfar : ∀ x, x ∉ Q' → x ∈ W := fun x hx =>
    rg_far_mem (by linarith) (fun y hy hyU => hy (hUQ' hyU)) hx
  have hWc : Wᶜ ⊆ Q' := fun x hx => by_contra fun h' => hx (hfar x h')
  have hpO : p ∈ O := by
    intro hpU
    have := (hUQ' hpU).2
    rw [hpdef, rg_mkPt1, add_sub_cancel_left, abs_of_pos (by linarith)] at this
    linarith
  have hWO : W ⊆ O := connectedComponentIn_subset _ _
  have hWo : IsOpen W := hOo.connectedComponentIn
  have hUW : U ⊆ Wᶜ := fun x hx hxW => hWO hxW hx
  -- frontiers of complementary components lie in `U`
  have hfrU : ∀ y, frontier (connectedComponentIn O y) ⊆ U := by
    intro y z hz
    by_contra hzU
    have hzo : IsOpen (connectedComponentIn O z) := hOo.connectedComponentIn
    have hzz : z ∈ connectedComponentIn O z := mem_connectedComponentIn hzU
    obtain ⟨x, hx1, hx2⟩ := mem_closure_iff.1 (frontier_subset_closure hz) _ hzo hzz
    have : z ∈ connectedComponentIn O y := by
      rw [connectedComponentIn_eq hx2, ← connectedComponentIn_eq hx1]; exact hzz
    exact hz.2 (by rw [hOo.connectedComponentIn.interior_eq]; exact this)
  have hdisjW : ∀ y ∈ O, y ∉ W → Disjoint (connectedComponentIn O y) W := by
    intro y hyO hyW
    rw [Set.disjoint_left]
    intro w hw1 hw2
    apply hyW
    rw [hWdef, connectedComponentIn_eq hw2, ← connectedComponentIn_eq hw1]
    exact mem_connectedComponentIn hyO
  -- the closed square is covered by the selected faces
  have hQU : Q ⊆ U := by
    have hint : interior Q ⊆ U := by
      intro y hy
      obtain ⟨A, hA, hyA⟩ :=
        mem_support_iff'.1 (interior_subset (hQ'Ω (hQQ' (interior_subset hy))))
      have hyA' : y ∈ closure (interior A.carrier) := by rw [tile_regular]; exact hyA
      obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hyA' _ isOpen_interior hy
      exact carrier_subset_support (show A ∈ U₀ from ⟨hA, w, hw2, hw1⟩) hyA
    exact (rg_square_subset_closure_interior hh).trans (closure_minimal hint hUc)
  have hcQ : c ∈ interior Q := rg_center_mem_interior hh
  have hU₀ne : U₀.Nonempty := by
    obtain ⟨A, hA, -⟩ := mem_support_iff'.1 (hQU (interior_subset hcQ))
    exact ⟨A, hA⟩
  have H0 : JSetup S.tiles U₀ := ⟨hdisj, hsts, hU₀S, hU₀fin, hUQ'.trans hQ'Ω⟩
  have hU₀G : U₀ ⊆ G := by
    intro A hA
    refine ⟨hA.1, fun hsub => ?_⟩
    obtain ⟨a, ha⟩ := (tileDisk A).interior_nonempty
    exact hUW (carrier_subset_support hA (interior_subset ha)) (hsub ha)
  -- the filled region is the complement of the outer component
  have hGW : support G = Wᶜ := by
    ext x
    constructor
    · intro hx hxW
      obtain ⟨A, hA, hxA⟩ := mem_support_iff'.1 hx
      apply hA.2
      have hxA' : x ∈ closure (interior A.carrier) := by rw [tile_regular]; exact hxA
      obtain ⟨w, hwW, hwA⟩ := mem_closure_iff.1 hxA' W hWo hxW
      by_cases hAU : A ∈ U₀
      · exact absurd (carrier_subset_support hAU (interior_subset hwA)) (hWO hwW)
      · have hAO : interior A.carrier ⊆ O := by
          intro v hv hvU
          obtain ⟨B, hB, hvB⟩ := mem_support_iff'.1 hvU
          exact interior_not_mem_other hdisj hA.1 hB.1 (fun h' => hAU (h' ▸ hB)) hv hvB
        have := (tileDisk A).interior_pathConnected.isConnected.isPreconnected.subset_connectedComponentIn
          hwA hAO
        rw [← connectedComponentIn_eq hwW] at this
        exact this
    · intro hx
      by_cases hxc : x ∈ closure W
      · have hxf : x ∈ frontier W := ⟨hxc, by rw [hWo.interior_eq]; exact hx⟩
        obtain ⟨B, hB, hxB⟩ := mem_support_iff'.1 (hfrU p hxf)
        exact carrier_subset_support (hU₀G hB) hxB
      · obtain ⟨A, hA, hxA⟩ := mem_support_iff'.1 (interior_subset (hQ'Ω (hWc hx)))
        by_cases hAG : interior A.carrier ⊆ W
        · exact absurd (by rw [← tile_regular A] at hxA; exact closure_mono hAG hxA) hxc
        · exact carrier_subset_support (show A ∈ G from ⟨hA, hAG⟩) hxA
  have hGS : G ⊆ S.tiles := fun A hA => hA.1
  have hGfin : G.Finite := S.finite.subset hGS
  have hGne : G.Nonempty := hU₀ne.mono hU₀G
  have hGcov : support G ⊆ interior (support S.tiles) := by rw [hGW]; exact hWc.trans hQ'Ω
  have HG : JSetup S.tiles G := ⟨hdisj, hsts, hGS, hGfin, hGcov⟩
  -- every bounded complementary component has a frontier point interior to the filled region
  have hLstar : ∀ y ∈ O, y ∉ W → ∃ z ∈ frontier (connectedComponentIn O y), z ∈ interior Wᶜ := by
    intro y hyO hyW
    set C' := connectedComponentIn O y with hC'
    have hC'o : IsOpen C' := hOo.connectedComponentIn
    have hyC' : y ∈ C' := mem_connectedComponentIn hyO
    have hC'W : Disjoint C' W := hdisjW y hyO hyW
    have hC'Wc : closure C' ⊆ Wᶜ :=
      closure_minimal (fun x hx hxW => Set.disjoint_left.1 hC'W hx hxW) hWo.isClosed_compl
    obtain ⟨z, hz, hzv⟩ : ∃ z ∈ frontier C', z ∉ gVerts S.tiles := by
      by_contra hcon
      push_neg at hcon
      have hpW : p ∈ W := mem_connectedComponentIn hpO
      have hpC : p ∉ closure C' := fun h' => Set.disjoint_left.1 (hC'W.symm.closure_right hWo) hpW h'
      apply open_minus_finite_split (W := Set.univ) (O1 := C') (O2 := (closure C')ᶜ) (Z := frontier C')
        isOpen_univ isPreconnected_univ hC'o isClosed_closure.isOpen_compl
        (Set.disjoint_left.2 fun x hx hx' => hx' (subset_closure hx))
        ((gVerts_finite S.finite).subset hcon)
      · intro x _
        by_cases h1 : x ∈ C'
        · exact Or.inl (Or.inl h1)
        by_cases h2 : x ∈ closure C'
        · exact Or.inr ⟨h2, by rw [hC'o.interior_eq]; exact h1⟩
        · exact Or.inl (Or.inr h2)
      · exact ⟨y, trivial, hyC'⟩
      · exact ⟨p, trivial, hpC⟩
    have hzU : z ∈ U := hfrU y hz
    obtain ⟨B, hB, hzB⟩ := mem_support_iff'.1 hzU
    refine ⟨z, hz, ?_⟩
    by_cases hzi : z ∈ interior B.carrier
    · exact interior_mono ((carrier_subset_support hB).trans hUW) hzi
    have hzf : z ∈ frontier B.carrier := by
      rw [mem_frontier_iff_of_closed (tile_isClosed B)]; exact ⟨hzB, hzi⟩
    rw [tile_frontier_eq, Set.mem_iUnion] at hzf
    obtain ⟨i, hzi'⟩ := hzf
    have hzo : z ∈ openSegment ℝ (B.vertex i) (B.vertex (finRotate _ i)) := by
      rw [tile_side_eq] at hzi'
      refine mem_openSegment_of_ne_left_right ?_ ?_ hzi'
      · intro h'; exact hzv (Set.mem_biUnion hB.1 ⟨i, h'⟩)
      · intro h'; exact hzv (Set.mem_biUnion hB.1 ⟨_, h'⟩)
    by_cases hbe : ∀ A' ∈ U₀, A' ≠ B → ¬ HasEdge A' (B.side i)
    · obtain ⟨r, hr, σ, hch⟩ := rg_bedge_sides H0 hB i hbe hzo
      set d := B.vertex (finRotate _ i) - B.vertex i with hd
      set a := B.vertex i with ha
      set Hm := Metric.ball z r ∩ {x : Pt | σ * jcr d (x - a) < 0} with hHm
      obtain ⟨w, hwC, hwz⟩ := Metric.mem_closure_iff.1 (frontier_subset_closure hz) r hr
      have hwb : w ∈ Metric.ball z r := by rw [Metric.mem_ball, dist_comm]; exact hwz
      have hwH : w ∈ Hm := by
        refine ⟨hwb, ?_⟩
        by_contra hneg
        replace hneg : 0 ≤ σ * jcr d (w - a) := not_lt.1 hneg
        exact (connectedComponentIn_subset O y hwC) (carrier_subset_support hB ((hch w hwb).2 hneg))
      have hHmO : Hm ⊆ O := fun x hx => (hch x hx.1).1 hx.2
      have hHmC : Hm ⊆ C' := by
        have := ((convex_ball z r).inter (rg_halfplane_convex σ d a)).isPreconnected.subset_connectedComponentIn
          hwH hHmO
        rwa [← connectedComponentIn_eq hwC] at this
      rw [mem_interior_iff_mem_nhds]
      refine Filter.mem_of_superset (Metric.ball_mem_nhds z hr) (fun x hx => ?_)
      rcases le_or_gt 0 (σ * jcr d (x - a)) with h0 | h0
      · exact hUW (carrier_subset_support hB ((hch x hx).2 h0))
      · exact hC'Wc (subset_closure (hHmC ⟨hx, h0⟩))
    · push_neg at hbe
      obtain ⟨A', hA', hne, j, hj⟩ := hbe
      exact interior_mono hUW (H0.partnered_open_in_U hB hA' hne i j hj hzo)
  -- the interior of the filled region is connected
  have hint : IsConnected (interior (support G)) := by
    rw [hGW]
    set V := interior Wᶜ with hV
    have hVo : IsOpen V := isOpen_interior
    obtain ⟨A0, hA0⟩ := hU₀ne
    set X₀ := ⋃ A : U₀, (interior Q ∪ interior A.1.carrier) with hX₀
    have hX₀c : IsPreconnected X₀ := by
      apply isPreconnected_iUnion
      · exact ⟨c, Set.mem_iInter.2 fun A => Or.inl hcQ⟩
      · intro A
        obtain ⟨w, hw1, hw2⟩ := A.2.2
        exact IsPreconnected.union' ⟨w, hw2, hw1⟩ (rg_square_convex c h).interior.isPreconnected
          (tileDisk A.1).interior_pathConnected.isConnected.isPreconnected
    have hX₀V : X₀ ⊆ V := by
      intro x hx
      obtain ⟨A, hxA⟩ := Set.mem_iUnion.1 hx
      rcases hxA with hx | hx
      · exact interior_mono (hQU.trans hUW) hx
      · exact interior_mono ((carrier_subset_support A.2).trans hUW) hx
    have hcX : c ∈ X₀ := Set.mem_iUnion.2 ⟨⟨A0, hA0⟩, Or.inl hcQ⟩
    set K := connectedComponentIn V c with hK
    have hX₀K : X₀ ⊆ K := hX₀c.subset_connectedComponentIn hcX hX₀V
    have hUcl : U ⊆ closure X₀ := by
      intro y hy
      obtain ⟨B, hB, hyB⟩ := mem_support_iff'.1 hy
      rw [← tile_regular] at hyB
      exact closure_mono (s := interior B.carrier) (t := X₀)
        (fun x hx => Set.mem_iUnion.2 ⟨(⟨B, hB⟩ : U₀), Or.inr hx⟩) hyB
    have hC1 : ∀ y ∈ V, y ∈ U → y ∈ K := by
      intro y hyV hyU
      obtain ⟨x, hx1, hx2⟩ :=
        mem_closure_iff.1 (hUcl hyU) _ hVo.connectedComponentIn (mem_connectedComponentIn hyV)
      rw [hK, connectedComponentIn_eq (hX₀K hx2), ← connectedComponentIn_eq hx1]
      exact mem_connectedComponentIn hyV
    have hVK : V ⊆ K := by
      intro y hyV
      by_cases hyU : y ∈ U
      · exact hC1 y hyV hyU
      have hyW : y ∉ W := interior_subset hyV
      obtain ⟨z, hz, hzV⟩ := hLstar y hyU hyW
      have hzK := hC1 z hzV (hfrU y hz)
      obtain ⟨x, hx1, hx2⟩ := mem_closure_iff.1 (frontier_subset_closure hz) _ hVo.connectedComponentIn
        (mem_connectedComponentIn hzV)
      have hC'V : connectedComponentIn O y ⊆ V :=
        interior_maximal (fun w hw hwW => Set.disjoint_left.1 (hdisjW y hyU hyW) hw hwW)
          hOo.connectedComponentIn
      have hxy : x ∈ connectedComponentIn V y :=
        isPreconnected_connectedComponentIn.subset_connectedComponentIn (mem_connectedComponentIn hyU) hC'V hx2
      rw [hK, connectedComponentIn_eq hzK, connectedComponentIn_eq hx1, ← connectedComponentIn_eq hxy]
      exact mem_connectedComponentIn hyV
    have hKV : K = V := Set.Subset.antisymm (connectedComponentIn_subset _ _) hVK
    rw [← hKV]
    exact isConnected_connectedComponentIn_iff.2 (hX₀V hcX)
  have hcompl : IsConnected (support G)ᶜ := by
    rw [hGW, compl_compl]; exact isConnected_connectedComponentIn_iff.2 hpO
  obtain ⟨L, hL⟩ := polygonalJordanBoundary S.tiles hdisj hsts G hGS hGfin hGne hGcov hint hcompl
  have hLc : L.carrier = Wᶜ := by rw [FaceGroup.carrier, L.carrier_eq, hL, hGW]
  refine ⟨L, ?_, ?_, ?_⟩
  · rw [hLc]; exact hQU.trans hUW
  · rw [hLc]; exact hWc.trans hQ'B
  · intro i
    obtain ⟨A, hA, j, hAj⟩ := L.side_whole i
    rw [hL] at hA
    obtain ⟨q, hq⟩ : (openSegment ℝ (A.vertex j) (A.vertex (finRotate _ j))).Nonempty :=
      ⟨_, mem_openSegment_iff'.2 ⟨1 / 2, by norm_num, by norm_num, rfl⟩⟩
    have hqs : q ∈ L.disk.side i := hAj ▸ openSeg_mem_side A j hq
    have hqf : q ∈ frontier L.disk.carrier := by
      rw [L.disk.frontier_eq]; exact Set.mem_iUnion.2 ⟨i, hqs⟩
    have hqU : q ∈ U := by
      have e : L.disk.carrier = Wᶜ := hLc
      rw [e, frontier_compl] at hqf
      exact hfrU p hqf
    obtain ⟨B, hB, hqB⟩ := mem_support_iff'.1 hqU
    by_cases hAB : A = B
    · subst hAB
      exact ⟨A, by rw [hL]; exact hA, ⟨j, hAj⟩, hB.2⟩
    · obtain ⟨k, hk⟩ := HG.partner hA hB.1 hAB j hq hqB
      exact ⟨B, by rw [hL]; exact hU₀G hB, ⟨k, hk.trans hAj⟩, hB.2⟩

/-- Step 1 of the blueprint proof of `outsideAnchoredGrouping_step1_E`: `K_1^c \subseteq \operatorname{int} E`. -/
private lemma outsideAnchoredGrouping_step1_E_step1_supset (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier) :
    (square c h + Binf (3 * M.D))ᶜ ⊆
      interior (Ω.carrierᶜ ∪ ⋃ F ∈ S.tiles, ⋃ _ : (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty, F.carrier) := sorry

/-- Step 2 of the blueprint proof of `outsideAnchoredGrouping_step1_E`: every selected face belongs to `E`. -/
private lemma outsideAnchoredGrouping_step1_E_step2_faces (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier) :
    ∀ F ∈ S.tiles, (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty →
      F.carrier ⊆ Ω.carrierᶜ ∪ ⋃ F' ∈ S.tiles, ⋃ _ : (interior F'.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty, F'.carrier := by
  intro F hF hF_nonempty x hx
  have _ := hcov; have _ := hsts; have _ := hh; have _ := hQ; have _ := M; have _ := Ω
  apply Set.mem_union_right
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨F, hF, hF_nonempty, hx⟩

/-- Step 3 of the blueprint proof of `outsideAnchoredGrouping_step1_E`: `\operatorname{int} E` is connected. -/
private lemma outsideAnchoredGrouping_step1_E_step3_conn (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier) :
    IsConnected (interior (Ω.carrierᶜ ∪ ⋃ F ∈ S.tiles, ⋃ _ : (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty, F.carrier)) := sorry

/-- Step 1 of the blueprint proof of `outsideAnchoredGrouping`: defining `E`. -/
private lemma outsideAnchoredGrouping_step1_E (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier) :
    ∃ E : Set Pt, (IsConnected (interior E) ∧
      (square c h + Binf (3 * M.D))ᶜ ⊆ interior E ∧
      ∀ F ∈ S.tiles, (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty →
      F.carrier ⊆ E) ∧
      E = Ω.carrierᶜ ∪ ⋃ F ∈ S.tiles, ⋃ _ : (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty, F.carrier := by
  use Ω.carrierᶜ ∪ ⋃ F ∈ S.tiles, ⋃ _ : (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty, F.carrier
  refine ⟨⟨?_, ?_, ?_⟩, rfl⟩
  · exact outsideAnchoredGrouping_step1_E_step3_conn M S Ω hcov hsts c h hh hQ
  · exact outsideAnchoredGrouping_step1_E_step1_supset M S Ω hcov hsts c h hh hQ
  · exact outsideAnchoredGrouping_step1_E_step2_faces M S Ω hcov hsts c h hh hQ

/-- Step 1 of the blueprint proof of `outsideAnchoredGrouping_step2_H`: lower inclusion. -/
private lemma outsideAnchoredGrouping_step2_H_step1_lower (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier)
    (E : Set Pt) (hE_conn : IsConnected (interior E))
    (hE_supset : (square c h + Binf (3 * M.D))ᶜ ⊆ interior E)
    (hE_faces : ∀ F ∈ S.tiles, (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty →
      F.carrier ⊆ E)
    (hE_def : E = Ω.carrierᶜ ∪ ⋃ F ∈ S.tiles, ⋃ _ : (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty, F.carrier) :
    square c h + Binf (2 * M.D) ⊆ closure (connectedComponentIn (Eᶜ) c) := sorry

/-- Step 2 of the blueprint proof of `outsideAnchoredGrouping_step2_H`: upper inclusion. -/
private lemma outsideAnchoredGrouping_step2_H_step2_upper (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier)
    (E : Set Pt) (hE_conn : IsConnected (interior E))
    (hE_supset : (square c h + Binf (3 * M.D))ᶜ ⊆ interior E)
    (hE_faces : ∀ F ∈ S.tiles, (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty →
      F.carrier ⊆ E)
    (hE_def : E = Ω.carrierᶜ ∪ ⋃ F ∈ S.tiles, ⋃ _ : (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty, F.carrier) :
    closure (connectedComponentIn (Eᶜ) c) ⊆ square c h + Binf (3 * M.D) := by
  have _ := hcov
  have _ := hsts
  have _ := hQ
  have _ := hE_conn
  have _ := hE_faces
  have _ := hE_def
  have hcc : connectedComponentIn (Eᶜ) c ⊆ square c h + Binf (3 * M.D) := by
    intro x hx
    by_contra hxQ
    exact absurd (interior_subset (hE_supset hxQ)) (connectedComponentIn_subset _ _ hx)
  have hDnn : (0 : ℝ) ≤ 3 * M.D := by linarith [M.D_pos]
  have hsum : square c h + Binf (3 * M.D) ⊆ square c (h + 3 * M.D) := by
    rintro x ⟨u, hu, v, hv, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [PiLp.add_apply]
      calc
        |u 0 + v 0 - c 0| = |(u 0 - c 0) + v 0| := by congr 1; ring_nf
        _ ≤ |u 0 - c 0| + |v 0| := abs_add_le _ _
        _ ≤ h + 3 * M.D := add_le_add hu.1 hv.1
    · simp only [PiLp.add_apply]
      calc
        |u 1 + v 1 - c 1| = |(u 1 - c 1) + v 1| := by congr 1; ring_nf
        _ ≤ |u 1 - c 1| + |v 1| := abs_add_le _ _
        _ ≤ h + 3 * M.D := add_le_add hu.2 hv.2
  have hclosed : IsClosed (square c h + Binf (3 * M.D)) := by
    have heq : square c h + Binf (3 * M.D) = square c (h + 3 * M.D) :=
      Set.Subset.antisymm hsum (rg_square_add hh.le hDnn)
    rw [heq]
    exact rg_square_closed c (h + 3 * M.D)
  calc closure (connectedComponentIn (Eᶜ) c)
      ⊆ closure (square c h + Binf (3 * M.D)) := closure_mono hcc
    _ = square c h + Binf (3 * M.D) := hclosed.closure_eq

/-- Step 3 of the blueprint proof of `outsideAnchoredGrouping_step2_H`: interior connected. -/
private lemma outsideAnchoredGrouping_step2_H_step3_conn_int (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier)
    (E : Set Pt) (hE_conn : IsConnected (interior E))
    (hE_supset : (square c h + Binf (3 * M.D))ᶜ ⊆ interior E)
    (hE_faces : ∀ F ∈ S.tiles, (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty →
      F.carrier ⊆ E)
    (hE_def : E = Ω.carrierᶜ ∪ ⋃ F ∈ S.tiles, ⋃ _ : (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty, F.carrier) :
    IsConnected (interior (closure (connectedComponentIn (Eᶜ) c))) := sorry

/-- Near a nonvertex point of an edge of a selected face, the two local half-planes
lie respectively in that face and outside all selected faces.  Unlike `JSetup.bedge_sides`,
this local version only requires the point in question to be interior to the patch. -/
private lemma outsideAnchoredGrouping_local_bedge_sides {S G : Set (PlacedTile P)}
    (hdisj : DisjointInteriors S) (hsts : SideToSideSet S) (hsub : G ⊆ S)
    (hfin : G.Finite) {A : PlacedTile P} (hA : A ∈ G)
    (i : Fin (P.disk A.form).n)
    (hbe : ∀ A' ∈ G, A' ≠ A → ¬ HasEdge A' (A.side i)) {q : Pt}
    (hq : q ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)))
    (hqS : q ∈ interior (support S)) :
    ∃ r > 0, ∃ σ : ℝ, ∀ x ∈ Metric.ball q r,
      (σ * jcr (A.vertex (finRotate _ i) - A.vertex i) (x - A.vertex i) < 0 →
        x ∉ support G) ∧
      (0 ≤ σ * jcr (A.vertex (finRotate _ i) - A.vertex i) (x - A.vertex i) →
        x ∈ A.carrier) := by
  classical
  obtain ⟨r, hr, σ, -, hch⟩ := tile_halfdisk A i hq
  set K' := ⋃ A' ∈ G \ {A}, A'.carrier with hK'
  have hK'c : IsClosed K' := (hfin.diff).isClosed_biUnion (fun D _ => tile_isClosed D)
  have hqK' : q ∉ K' := by
    intro hqK'
    simp only [hK', Set.mem_iUnion] at hqK'
    obtain ⟨A', ⟨hA'G, hA'A⟩, hqA'⟩ := hqK'
    have hne : A ≠ A' := fun h => hA'A (h ▸ rfl)
    obtain ⟨j, hj⟩ := tile_partner hdisj hsts (hsub hA) (hsub hA'G) hne i hq hqA' (fun hv =>
      vertex_not_mem_open_side hdisj hsts (hsub hA) (hsub hA'G) i hq hv hqS)
    exact hbe A' hA'G hne.symm ⟨j, hj⟩
  obtain ⟨ρ, hρ, hρK⟩ := Metric.isOpen_iff.1 hK'c.isOpen_compl q hqK'
  refine ⟨min r ρ, lt_min hr hρ, σ, fun x hx => ⟨fun hneg => ?_, fun hnonneg => ?_⟩⟩
  · intro hxG
    obtain ⟨A', hA'G, hxA'⟩ := mem_support_iff'.1 hxG
    by_cases hAA : A' = A
    · subst hAA
      have hxside := ((hch x (Metric.ball_subset_ball (min_le_left _ _) hx)).2.1).1 hxA'
      linarith
    · apply hρK (Metric.ball_subset_ball (min_le_right _ _) hx)
      simp only [hK', Set.mem_iUnion]
      exact ⟨A', ⟨hA'G, hAA⟩, hxA'⟩
  · exact ((hch x (Metric.ball_subset_ball (min_le_left _ _) hx)).2.1).2 hnonneg

/-- Step 4 of the blueprint proof of `outsideAnchoredGrouping_step2_H`: complement connected. -/
private lemma outsideAnchoredGrouping_step2_H_step4_conn_comp (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier)
    (E : Set Pt) (hE_conn : IsConnected (interior E))
    (hE_supset : (square c h + Binf (3 * M.D))ᶜ ⊆ interior E)
    (hE_faces : ∀ F ∈ S.tiles, (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty →
      F.carrier ⊆ E)
    (hE_def : E = Ω.carrierᶜ ∪ ⋃ F ∈ S.tiles, ⋃ _ : (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty, F.carrier) :
    IsConnected (closure (connectedComponentIn (Eᶜ) c))ᶜ := by
  classical
  set K := square c h + Binf (3 * M.D) with hKdef
  set G : Set (PlacedTile P) :=
    {F ∈ S.tiles | (interior F.carrier ∩ Kᶜ).Nonempty} with hGdef
  have hGS : G ⊆ S.tiles := fun F hF => hF.1
  have hGfin : G.Finite := S.finite.subset hGS
  have hEsupport : E = Ω.carrierᶜ ∪ support G := by
    rw [hE_def]
    congr 1
    ext x
    simp only [hGdef, hKdef, mem_support_iff', Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨F, hFS, hF, hxF⟩
      exact ⟨F, ⟨hFS, hF⟩, hxF⟩
    · rintro ⟨F, ⟨hFS, hF⟩, hxF⟩
      exact ⟨F, hFS, hF, hxF⟩
  have hKclosed : IsClosed K := by
    have hDnn : (0 : ℝ) ≤ 3 * M.D := by linarith [M.D_pos]
    have hsum : K ⊆ square c (h + 3 * M.D) := by
      rintro x ⟨u, hu, v, hv, rfl⟩
      refine ⟨?_, ?_⟩
      · simp only [PiLp.add_apply]
        calc
          |u 0 + v 0 - c 0| = |(u 0 - c 0) + v 0| := by congr 1; ring_nf
          _ ≤ |u 0 - c 0| + |v 0| := abs_add_le _ _
          _ ≤ h + 3 * M.D := add_le_add hu.1 hv.1
      · simp only [PiLp.add_apply]
        calc
          |u 1 + v 1 - c 1| = |(u 1 - c 1) + v 1| := by congr 1; ring_nf
          _ ≤ |u 1 - c 1| + |v 1| := abs_add_le _ _
          _ ≤ h + 3 * M.D := add_le_add hu.2 hv.2
    have heq : K = square c (h + 3 * M.D) :=
      Set.Subset.antisymm hsum (by rw [hKdef]; exact rg_square_add hh.le hDnn)
    rw [heq]
    exact rg_square_closed c (h + 3 * M.D)
  have hKΩ : K ⊆ interior Ω.carrier := by
    rw [hKdef]
    exact (Set.add_subset_add_left (rg_binf_mono (by linarith [M.D_pos]))).trans hQ
  set O := Eᶜ with hOdef
  have hOK : O ⊆ K := by
    intro x hxO
    by_contra hxK
    exact hxO (interior_subset (hE_supset (by rwa [hKdef])))
  have hOeq : O = interior Ω.carrier ∩ (support G)ᶜ := by
    ext x
    constructor
    · intro hxO
      have hxK := hOK hxO
      have hxΩ := hKΩ hxK
      rw [hOdef, hEsupport] at hxO
      exact ⟨hxΩ, fun hxG => hxO (Or.inr hxG)⟩
    · rintro ⟨hxΩ, hxG⟩
      rw [hOdef, hEsupport]
      exact fun hxE => hxE.elim (fun hxΩc => hxΩc (interior_subset hxΩ)) hxG
  have hOo : IsOpen O := by
    rw [hOeq]
    exact isOpen_interior.inter (support_isClosed hGfin).isOpen_compl
  set W := connectedComponentIn O c with hWdef
  have hcK : c ∈ K := by
    rw [hKdef]
    refine Set.mem_add.2 ⟨c, ?_, 0, ?_, by simp⟩
    · simp only [square, Set.mem_setOf_eq, sub_self, abs_zero]
      exact ⟨hh.le, hh.le⟩
    · simp only [Binf, Set.mem_setOf_eq, PiLp.zero_apply, abs_zero]
      exact ⟨by linarith [M.D_pos], by linarith [M.D_pos]⟩
  have hcO : c ∈ O := by
    rw [hOeq]
    refine ⟨hKΩ hcK, ?_⟩
    intro hcG
    obtain ⟨F, hFG, hcF⟩ := mem_support_iff'.1 hcG
    obtain ⟨w, hwF, hwK⟩ := hFG.2
    apply hwK
    rw [hKdef]
    refine Set.mem_add.2 ⟨c, ?_, w - c, ?_, by abel⟩
    · simp only [square, Set.mem_setOf_eq, sub_self, abs_zero]
      exact ⟨hh.le, hh.le⟩
    · refine ⟨?_, ?_⟩
      · exact (rg_tile_coord M F (interior_subset hwF) hcF 0).trans (by linarith [M.D_pos])
      · exact (rg_tile_coord M F (interior_subset hwF) hcF 1).trans (by linarith [M.D_pos])
  have hWne : W.Nonempty := by
    exact ⟨c, hWdef ▸ mem_connectedComponentIn hcO⟩
  have hWO : W ⊆ O := by rw [hWdef]; exact connectedComponentIn_subset O c
  have hWo : IsOpen W := by rw [hWdef]; exact hOo.connectedComponentIn
  set V := interior Wᶜ with hVdef
  have htarget : (closure W)ᶜ = V := by rw [hVdef, interior_compl]
  rw [hWdef, htarget]
  set P0 := interior E with hP0def
  have hP0Wc : P0 ⊆ Wᶜ := by
    intro x hxP hxW
    exact (connectedComponentIn_subset O c (hWdef ▸ hxW)) (interior_subset hxP)
  have hP0V : P0 ⊆ V := by
    rw [hVdef]
    exact interior_maximal hP0Wc isOpen_interior
  have hEclP0 : E ⊆ closure P0 := by
    intro x hxE
    rw [hEsupport] at hxE
    rcases hxE with hxΩ | hxG
    · have hxK : x ∉ K := fun hx => hxΩ (interior_subset (hKΩ hx))
      exact subset_closure (hE_supset (by rwa [hKdef] at hxK))
    · obtain ⟨F, hFG, hxF⟩ := mem_support_iff'.1 hxG
      have hFE : F.carrier ⊆ E := hE_faces F hFG.1 hFG.2
      have hxcl : x ∈ closure (interior F.carrier) := by rw [tile_regular]; exact hxF
      exact closure_mono (by simpa [hP0def] using interior_mono hFE) hxcl
  have hfrE : ∀ y, frontier (connectedComponentIn O y) ⊆ E := by
    intro y z hz
    by_contra hzE
    have hzo : IsOpen (connectedComponentIn O z) := hOo.connectedComponentIn
    have hzz : z ∈ connectedComponentIn O z := mem_connectedComponentIn hzE
    obtain ⟨x, hx1, hx2⟩ := mem_closure_iff.1 (frontier_subset_closure hz) _ hzo hzz
    have hzCy : z ∈ connectedComponentIn O y := by
      rw [connectedComponentIn_eq hx2, ← connectedComponentIn_eq hx1]
      exact hzz
    exact hz.2 (by rw [hOo.connectedComponentIn.interior_eq]; exact hzCy)
  have hdisjW : ∀ y ∈ O, y ∉ W → Disjoint (connectedComponentIn O y) W := by
    intro y hyO hyW
    rw [Set.disjoint_left]
    intro w hw1 hw2
    apply hyW
    rw [hWdef, connectedComponentIn_eq hw2, ← connectedComponentIn_eq hw1]
    exact mem_connectedComponentIn hyO
  have hLstar : ∀ y ∈ O, y ∉ W →
      ∃ z ∈ frontier (connectedComponentIn O y), z ∈ V := by
    intro y hyO hyW
    set C' := connectedComponentIn O y with hC'def
    have hC'o : IsOpen C' := by rw [hC'def]; exact hOo.connectedComponentIn
    have hyC' : y ∈ C' := by rw [hC'def]; exact mem_connectedComponentIn hyO
    have hC'W : Disjoint C' W := by rw [hC'def]; exact hdisjW y hyO hyW
    have hC'Wc : closure C' ⊆ Wᶜ :=
      closure_minimal (fun x hx hxW => Set.disjoint_left.1 hC'W hx hxW) hWo.isClosed_compl
    have hC'K : closure C' ⊆ K := by
      apply closure_minimal
      · rw [hC'def]
        exact (connectedComponentIn_subset O y).trans hOK
      · exact hKclosed
    obtain ⟨w0, hw0W⟩ := hWne
    have hw0C' : w0 ∉ closure C' := fun hw0 => Set.disjoint_left.1 (hC'W.symm.closure_right hWo) hw0W hw0
    obtain ⟨z, hz, hzv⟩ : ∃ z ∈ frontier C', z ∉ gVerts S.tiles := by
      by_contra hcon
      push_neg at hcon
      apply open_minus_finite_split (W := Set.univ) (O1 := C') (O2 := (closure C')ᶜ)
        (Z := frontier C') isOpen_univ isPreconnected_univ hC'o isClosed_closure.isOpen_compl
        (Set.disjoint_left.2 fun x hx hx' => hx' (subset_closure hx))
        ((gVerts_finite S.finite).subset hcon)
      · intro x _
        by_cases h1 : x ∈ C'
        · exact Or.inl (Or.inl h1)
        by_cases h2 : x ∈ closure C'
        · exact Or.inr ⟨h2, by rw [hC'o.interior_eq]; exact h1⟩
        · exact Or.inl (Or.inr h2)
      · exact ⟨y, trivial, hyC'⟩
      · exact ⟨w0, trivial, hw0C'⟩
    have hzE : z ∈ E := by
      rw [hC'def] at hz
      exact hfrE y hz
    have hzK : z ∈ K := hC'K (frontier_subset_closure hz)
    have hzΩ : z ∈ interior (support S.tiles) := by rw [hcov]; exact hKΩ hzK
    have hzG : z ∈ support G := by
      rw [hEsupport] at hzE
      exact hzE.resolve_left (fun hzΩc => hzΩc (interior_subset (hKΩ hzK)))
    obtain ⟨B, hBG, hzB⟩ := mem_support_iff'.1 hzG
    by_cases hzi : z ∈ interior B.carrier
    · exact ⟨z, hz, hP0V (by simpa [hP0def] using interior_mono (hE_faces B hBG.1 hBG.2) hzi)⟩
    have hzf : z ∈ frontier B.carrier := by
      rw [mem_frontier_iff_of_closed (tile_isClosed B)]
      exact ⟨hzB, hzi⟩
    rw [tile_frontier_eq, Set.mem_iUnion] at hzf
    obtain ⟨i, hzi'⟩ := hzf
    have hzo : z ∈ openSegment ℝ (B.vertex i) (B.vertex (finRotate _ i)) := by
      rw [tile_side_eq] at hzi'
      refine mem_openSegment_of_ne_left_right ?_ ?_ hzi'
      · intro hz'
        exact hzv (Set.mem_biUnion hBG.1 ⟨i, hz'⟩)
      · intro hz'
        exact hzv (Set.mem_biUnion hBG.1 ⟨_, hz'⟩)
    by_cases hbe : ∀ A' ∈ G, A' ≠ B → ¬ HasEdge A' (B.side i)
    · obtain ⟨r, hr, σ, hch⟩ := outsideAnchoredGrouping_local_bedge_sides S.disjoint hsts hGS hGfin
        hBG i hbe hzo hzΩ
      obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 isOpen_interior z hzΩ
      set r0 := min r ρ with hr0def
      set d := B.vertex (finRotate _ i) - B.vertex i with hddef
      set a := B.vertex i with hadef
      set Hm := Metric.ball z r0 ∩ {x : Pt | σ * jcr d (x - a) < 0} with hHmdef
      obtain ⟨w, hwC, hwz⟩ := Metric.mem_closure_iff.1 (frontier_subset_closure hz) r0 (lt_min hr hρ)
      have hwb : w ∈ Metric.ball z r0 := by rw [Metric.mem_ball, dist_comm]; exact hwz
      have hwH : w ∈ Hm := by
        refine ⟨hwb, ?_⟩
        by_contra hneg
        replace hneg : 0 ≤ σ * jcr d (w - a) := not_lt.1 hneg
        have hwB := (hch w (Metric.ball_subset_ball (hr0def ▸ min_le_left r ρ) hwb)).2 (by simpa [hddef, hadef] using hneg)
        exact (connectedComponentIn_subset O y (hC'def ▸ hwC)) (hE_faces B hBG.1 hBG.2 hwB)
      have hHmO : Hm ⊆ O := by
        intro x hx
        rw [hOeq]
        refine ⟨?_, ?_⟩
        · rw [← hcov]
          exact hρΩ (Metric.ball_subset_ball (hr0def ▸ min_le_right r ρ) hx.1)
        exact (hch x (Metric.ball_subset_ball (hr0def ▸ min_le_left r ρ) hx.1)).1
          (by simpa [hddef, hadef] using hx.2)
      have hHmC : Hm ⊆ C' := by
        have hpre := ((convex_ball z r0).inter (rg_halfplane_convex σ d a)).isPreconnected
          |>.subset_connectedComponentIn hwH hHmO
        rw [hC'def] at hwC
        rw [hHmdef, hC'def, connectedComponentIn_eq hwC]
        exact hpre
      refine ⟨z, hz, ?_⟩
      rw [hVdef, mem_interior_iff_mem_nhds]
      refine Filter.mem_of_superset (Metric.ball_mem_nhds z (lt_min hr hρ)) (fun x hx => ?_)
      rcases le_or_gt 0 (σ * jcr d (x - a)) with hnonneg | hneg
      · intro hxW
        have hxB := (hch x (Metric.ball_subset_ball (hr0def ▸ min_le_left r ρ) hx)).2
          (by simpa [hddef, hadef] using hnonneg)
        exact (hWO hxW) (hE_faces B hBG.1 hBG.2 hxB)
      · exact hC'Wc (subset_closure (hHmC ⟨hx, hneg⟩))
    · push_neg at hbe
      obtain ⟨A', hA'G, hne, j, hj⟩ := hbe
      have hzGi : z ∈ interior (support G) := by
        obtain ⟨r, hr, σ, -, hside⟩ :=
          two_sides S.disjoint (hGS hBG) (hGS hA'G) hne.symm i j hj hzo
        rw [mem_interior_iff_mem_nhds]
        refine Filter.mem_of_superset (Metric.ball_mem_nhds z hr) (fun x hx => ?_)
        rcases le_or_gt 0 (σ * jcr (B.vertex (finRotate _ i) - B.vertex i) (x - B.vertex i)) with h | h
        · exact carrier_subset_support hBG ((hside x hx).2.2 h)
        · exact carrier_subset_support hA'G (interior_subset ((hside x hx).2.1 h))
      refine ⟨z, hz, hP0V ?_⟩
      exact interior_mono (by rw [hEsupport]; exact Set.subset_union_right) hzGi
  obtain ⟨x0, hx0⟩ := hE_conn.nonempty
  have hx0V : x0 ∈ V := hP0V hx0
  set C0 := connectedComponentIn V x0 with hC0def
  have hP0C0 : P0 ⊆ C0 := by
    rw [hC0def]
    exact hE_conn.isPreconnected.subset_connectedComponentIn hx0 hP0V
  have hC0V : C0 ⊆ V := by rw [hC0def]; exact connectedComponentIn_subset V x0
  have hC1 : ∀ y ∈ V, y ∈ E → y ∈ C0 := by
    intro y hyV hyE
    obtain ⟨x, hx1, hx2⟩ := mem_closure_iff.1 (hEclP0 hyE) _
      isOpen_interior.connectedComponentIn (mem_connectedComponentIn hyV)
    rw [hC0def, connectedComponentIn_eq (hP0C0 hx2), ← connectedComponentIn_eq hx1]
    exact mem_connectedComponentIn hyV
  have hVC0 : V ⊆ C0 := by
    intro y hyV
    by_cases hyE : y ∈ E
    · exact hC1 y hyV hyE
    · have hyO : y ∈ O := by simpa [hOdef] using hyE
      have hyW : y ∉ W := interior_subset hyV
      obtain ⟨z, hz, hzV⟩ := hLstar y hyO hyW
      have hzC0 := hC1 z hzV (hfrE y hz)
      obtain ⟨x, hx1, hx2⟩ := mem_closure_iff.1 (frontier_subset_closure hz) _
        isOpen_interior.connectedComponentIn (mem_connectedComponentIn hzV)
      have hCyV : connectedComponentIn O y ⊆ V := by
        rw [hVdef]
        exact interior_maximal (fun w hw hwW => Set.disjoint_left.1 (hdisjW y hyO hyW) hw hwW)
          hOo.connectedComponentIn
      have hxy : x ∈ connectedComponentIn V y :=
        isPreconnected_connectedComponentIn.subset_connectedComponentIn
          (mem_connectedComponentIn hyO) hCyV hx2
      rw [hC0def, connectedComponentIn_eq hzC0, connectedComponentIn_eq hx1,
        ← connectedComponentIn_eq hxy]
      exact mem_connectedComponentIn hyV
  have hC0eq : C0 = V := Set.Subset.antisymm hC0V hVC0
  rw [← hC0eq, hC0def]
  exact isConnected_connectedComponentIn_iff.2 hx0V

/-- Step 2 of the blueprint proof of `outsideAnchoredGrouping`: defining `H_carrier`. -/
private lemma outsideAnchoredGrouping_step2_H (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier)
    (E : Set Pt) (hE_conn : IsConnected (interior E))
    (hE_supset : (square c h + Binf (3 * M.D))ᶜ ⊆ interior E)
    (hE_faces : ∀ F ∈ S.tiles, (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty →
      F.carrier ⊆ E)
    (hE_def : E = Ω.carrierᶜ ∪ ⋃ F ∈ S.tiles, ⋃ _ : (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty, F.carrier) :
    ∃ H_carrier : Set Pt, square c h + Binf (2 * M.D) ⊆ H_carrier ∧
      H_carrier ⊆ square c h + Binf (3 * M.D) ∧
      H_carrier = closure (connectedComponentIn (Eᶜ) c) ∧
      IsConnected (interior H_carrier) ∧ IsConnected (H_carrierᶜ) := by
  use closure (connectedComponentIn (Eᶜ) c)
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · exact outsideAnchoredGrouping_step2_H_step1_lower M S Ω hcov hsts c h hh hQ E hE_conn hE_supset
      hE_faces hE_def
  · exact outsideAnchoredGrouping_step2_H_step2_upper M S Ω hcov hsts c h hh hQ E hE_conn hE_supset
      hE_faces hE_def
  · exact outsideAnchoredGrouping_step2_H_step3_conn_int M S Ω hcov hsts c h hh hQ E hE_conn
      hE_supset hE_faces hE_def
  · exact outsideAnchoredGrouping_step2_H_step4_conn_comp M S Ω hcov hsts c h hh hQ E hE_conn
      hE_supset hE_faces hE_def

/-! The remaining step is the cellulation identification of the component closure. -/

/-- Step 1 of the blueprint proof of `outsideAnchoredGrouping_step3_FaceGroup`: the closure
of the component selected by `H_carrier` is the support of a finite nonempty set of complete
faces of the patch, and this support lies in the interior of the covered polygonal disk. -/
private lemma outsideAnchoredGrouping_step3_FaceGroup_step1_component_faces
    (M : MeshConstants P) (S : Patch P) (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier)
    (E : Set Pt) (hE_conn : IsConnected (interior E))
    (hE_supset : (square c h + Binf (3 * M.D))ᶜ ⊆ interior E)
    (hE_faces : ∀ F ∈ S.tiles,
      (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty →
      F.carrier ⊆ E)
    (hE_def : E = Ω.carrierᶜ ∪ ⋃ F ∈ S.tiles,
      ⋃ _ : (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty, F.carrier)
    (H_carrier : Set Pt) (hH_sub : H_carrier ⊆ square c h + Binf (3 * M.D))
    (hH_def : H_carrier = closure (connectedComponentIn (Eᶜ) c)) :
    ∃ G : Set (PlacedTile P), G ⊆ S.tiles ∧ G.Finite ∧ G.Nonempty ∧
      support G = H_carrier ∧ support G ⊆ interior Ω.carrier := sorry

private lemma outsideAnchoredGrouping_step3_FaceGroup (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier)
    (E : Set Pt) (hE_conn : IsConnected (interior E))
    (hE_supset : (square c h + Binf (3 * M.D))ᶜ ⊆ interior E)
    (hE_faces : ∀ F ∈ S.tiles, (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty →
      F.carrier ⊆ E)
    (hE_def : E = Ω.carrierᶜ ∪ ⋃ F ∈ S.tiles, ⋃ _ : (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty, F.carrier)
    (H_carrier : Set Pt) (hH_sub : H_carrier ⊆ square c h + Binf (3 * M.D))
    (hH_def : H_carrier = closure (connectedComponentIn (Eᶜ) c)) :
    ∃ H : FaceGroup S.tiles, H.carrier = H_carrier := by
  have s2 := outsideAnchoredGrouping_step2_H M S Ω hcov hsts c h hh hQ E hE_conn
    hE_supset hE_faces hE_def
  rcases s2 with ⟨H', -, -, hH'_def, hH'_conn_int, hH'_conn_comp⟩
  have hH_conn_int : IsConnected (interior H_carrier) := by
    rw [hH_def, ← hH'_def]
    exact hH'_conn_int
  have hH_conn_comp : IsConnected H_carrierᶜ := by
    rw [hH_def, ← hH'_def]
    exact hH'_conn_comp
  obtain ⟨G, hG_sub, hG_fin, hG_ne, hG_eq, hG_cov⟩ :=
    outsideAnchoredGrouping_step3_FaceGroup_step1_component_faces M S Ω hcov hsts c h hh hQ E
      hE_conn hE_supset hE_faces hE_def H_carrier hH_sub hH_def
  have hG_cov' : support G ⊆ interior (support S.tiles) := by
    rw [hcov]
    exact hG_cov
  have hG_conn_int : IsConnected (interior (support G)) := by
    rw [hG_eq]
    exact hH_conn_int
  have hG_conn_comp : IsConnected (support G)ᶜ := by
    rw [hG_eq]
    exact hH_conn_comp
  obtain ⟨H, hH_faces⟩ := polygonalJordanBoundary S.tiles S.disjoint hsts G hG_sub hG_fin hG_ne
    hG_cov' hG_conn_int hG_conn_comp
  refine ⟨H, ?_⟩
  rw [FaceGroup.carrier, H.carrier_eq, hH_faces, hG_eq]

private lemma JSetup.boundary_partner {S G : Set (PlacedTile P)} (J : JSetup S G)
    (hS_fin : S.Finite) {A : PlacedTile P} (hA : A ∈ G)
    (i : Fin (P.disk A.form).n) {q : Pt}
    (hq : q ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)))
    (hq_frontier : q ∈ frontier (support G)) :
    ∃ F ∈ S, F ∉ G ∧ ∃ j, F.side j = A.side i := by
  have hboundary : ∀ A' ∈ G, A' ≠ A → ¬ HasEdge A' (A.side i) := by
    intro A' hA' hA'A ⟨j, hj⟩
    exact hq_frontier.2 (J.partnered_open_in_U hA hA' hA'A i j hj hq)
  obtain ⟨r, hr, σ, hσ, hside⟩ := J.bedge_sides hA i hboundary hq
  have hq_support : q ∈ interior (support S) :=
    J.cov (carrier_subset_support hA (tile_side_subset A i (openSeg_mem_side A i hq)))
  obtain ⟨ρ, hρ, hρ_support⟩ := Metric.isOpen_iff.1 isOpen_interior q hq_support
  have hclosed : IsClosed (support (S \ G)) :=
    support_isClosed (show (S \ G).Finite from hS_fin.diff)
  have hq_closure : q ∈ closure (support (S \ G)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hd : A.vertex (finRotate _ i) - A.vertex i ≠ 0 :=
      sub_ne_zero.2 (tile_vertex_ne_next A i).symm
    have hnegσ : -σ = 1 ∨ -σ = -1 := by
      rcases hσ with hσ | hσ <;> rw [hσ] <;> norm_num
    obtain ⟨y, hy, hycross⟩ :=
      exists_near_off_line (A.vertex i) hd q hnegσ (lt_min hε (lt_min hr hρ))
    have hqcross : jcr (A.vertex (finRotate _ i) - A.vertex i) (q - A.vertex i) = 0 :=
      jcr_zero_of_mem_segment (openSegment_subset_segment ℝ _ _ hq)
    have hyball_r : y ∈ Metric.ball q r := by
      rw [Metric.mem_ball, dist_comm]
      exact lt_of_lt_of_le hy (min_le_right _ _ |>.trans (min_le_left _ _))
    have hyball_ρ : y ∈ Metric.ball q ρ := by
      rw [Metric.mem_ball, dist_comm]
      exact lt_of_lt_of_le hy (min_le_right _ _ |>.trans (min_le_right _ _))
    have hy_not : y ∉ support G := (hside y hyball_r).2 (by rw [hqcross, mul_zero] at hycross; linarith)
    obtain ⟨F, hFS, hyF⟩ := mem_support_iff'.1 (interior_subset (hρ_support hyball_ρ))
    have hFG : F ∉ G := fun h => hy_not (carrier_subset_support h hyF)
    refine ⟨y, carrier_subset_support (show F ∈ S \ G from ⟨hFS, hFG⟩) hyF, ?_⟩
    exact lt_of_lt_of_le hy (min_le_left _ _)
  have hq_diff : q ∈ support (S \ G) := by
    rw [← hclosed.closure_eq]
    exact hq_closure
  obtain ⟨F, ⟨hFS, hFG⟩, hqF⟩ := mem_support_iff'.1 hq_diff
  have hAF : A ≠ F := fun h => hFG (h ▸ hA)
  have hq_not_vertex : q ∉ F.vertexSet := fun h => J.no_vertex hA hFS i hq h
  obtain ⟨j, hj⟩ := tile_partner J.disj J.sts (J.sub hA) hFS hAF i hq hqF hq_not_vertex
  exact ⟨F, hFS, hFG, j, hj⟩

private lemma side_partner_unique {S : Set (PlacedTile P)} (hdisj : DisjointInteriors S)
    {A B C : PlacedTile P} (hA : A ∈ S) (hB : B ∈ S) (hC : C ∈ S)
    (hAB : A ≠ B) (hAC : A ≠ C) (i : Fin (P.disk A.form).n)
    (j : Fin (P.disk B.form).n) (k : Fin (P.disk C.form).n)
    (hj : B.side j = A.side i) (hk : C.side k = A.side i) : B = C := by
  by_contra hBC
  let q := A.vertex i + (1 / 2 : ℝ) • (A.vertex (finRotate _ i) - A.vertex i)
  have hq : q ∈ openSegment ℝ (A.vertex i) (A.vertex (finRotate _ i)) :=
    mem_openSegment_iff'.2 ⟨1 / 2, by norm_num, by norm_num, rfl⟩
  obtain ⟨r, hr, σ, hσ, hsB⟩ := two_sides hdisj hA hB hAB i j hj hq
  obtain ⟨r', hr', σ', hσ', hsC⟩ := two_sides hdisj hA hC hAC i k hk hq
  let d := A.vertex (finRotate _ i) - A.vertex i
  have hd : d ≠ 0 := sub_ne_zero.2 (tile_vertex_ne_next A i).symm
  have hqcross : jcr d (q - A.vertex i) = 0 := by
    dsimp [q, d]
    rw [add_sub_cancel_left, jcr_smul_right, jcr_self, mul_zero]
  have hσσ' : σ' = σ := by
    by_contra hne
    have heq : σ' = -σ := by
      rcases hσ with rfl | rfl
      · rcases hσ' with rfl | rfl
        · exact (hne rfl).elim
        · norm_num
      · rcases hσ' with rfl | rfl
        · norm_num
        · exact (hne rfl).elim
    obtain ⟨y, hy, hycross⟩ := exists_near_off_line (A.vertex i) hd q hσ (lt_min hr hr')
    have hyr : y ∈ Metric.ball q r := by
      rw [Metric.mem_ball, dist_comm]
      exact lt_of_lt_of_le hy (min_le_left _ _)
    have hyr' : y ∈ Metric.ball q r' := by
      rw [Metric.mem_ball, dist_comm]
      exact lt_of_lt_of_le hy (min_le_right _ _)
    have hpos : 0 < σ * jcr d (y - A.vertex i) := by
      rw [hqcross, mul_zero] at hycross
      exact hycross
    exact interiors_disjoint hdisj hA hC hAC ((hsB y hyr).1 hpos)
      ((hsC y hyr').2.1 (by rw [heq]; linarith))
  have hnegσ : -σ = 1 ∨ -σ = -1 := by
    rcases hσ with hσ | hσ <;> rw [hσ] <;> norm_num
  obtain ⟨y, hy, hycross⟩ := exists_near_off_line (A.vertex i) hd q hnegσ (lt_min hr hr')
  have hyr : y ∈ Metric.ball q r := by
    rw [Metric.mem_ball, dist_comm]
    exact lt_of_lt_of_le hy (min_le_left _ _)
  have hyr' : y ∈ Metric.ball q r' := by
    rw [Metric.mem_ball, dist_comm]
    exact lt_of_lt_of_le hy (min_le_right _ _)
  have hneg : σ * jcr d (y - A.vertex i) < 0 := by
    rw [hqcross, mul_zero] at hycross
    linarith
  exact interiors_disjoint hdisj hB hC hBC ((hsB y hyr).2.1 hneg)
    ((hsC y hyr').2.1 (by rw [hσσ']; exact hneg))

private lemma outsideAnchoredGrouping_step4_anchor (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier)
    (E : Set Pt)
    (hE_faces : ∀ F ∈ S.tiles, (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty →
      F.carrier ⊆ E)
    (hE_def : E = Ω.carrierᶜ ∪ ⋃ F ∈ S.tiles, ⋃ _ : (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty, F.carrier)
    (H : FaceGroup S.tiles) (hH_sub : H.carrier ⊆ square c h + Binf (3 * M.D))
    (hH_def : H.carrier = closure (connectedComponentIn (Eᶜ) c))
    (hH_conn_int : IsConnected (interior H.carrier))
    (hH_conn_comp : IsConnected (H.carrierᶜ)) :
    H.OutsideAnchored (square c h + Binf (3 * M.D)) := by
  classical
  have hD_pos : 0 < M.D := by
    by_cases hall : 0 < h ∧ IsConnected (interior H.carrier) ∧ IsConnected (H.carrierᶜ)
    · exact M.D_pos
    · exact (hall ⟨hh, hH_conn_int, hH_conn_comp⟩).elim
  have hbuffer : square c h + Binf (3 * M.D) ⊆
      square c h + Binf (10 * M.D) :=
    Set.add_subset_add_left (rg_binf_mono (by nlinarith [hD_pos]))
  have hfaces_cov : support H.faces ⊆ interior (support S.tiles) := by
    rw [← H.carrier_eq, hcov]
    exact hH_sub.trans (hbuffer.trans hQ)
  let J : JSetup S.tiles H.faces :=
    ⟨S.disjoint, hsts, H.faces_sub, H.finite, hfaces_cov⟩
  intro i
  obtain ⟨A, hAH, j, hAj⟩ := H.side_whole i
  let q := A.vertex j + (1 / 2 : ℝ) • (A.vertex (finRotate _ j) - A.vertex j)
  have hq : q ∈ openSegment ℝ (A.vertex j) (A.vertex (finRotate _ j)) := by
    exact mem_openSegment_iff'.2 ⟨1 / 2, by norm_num, by norm_num, rfl⟩
  have hq_side : q ∈ H.disk.side i := by
    rw [← hAj]
    exact openSeg_mem_side A j hq
  have hq_frontier_disk : q ∈ frontier H.disk.carrier := by
    rw [H.disk.frontier_eq]
    exact Set.mem_iUnion.2 ⟨i, hq_side⟩
  have hq_frontier : q ∈ frontier (support H.faces) := by
    rw [← H.carrier_eq]
    exact hq_frontier_disk
  obtain ⟨F, hFS, hFH, k, hk⟩ := J.boundary_partner S.finite hAH j hq hq_frontier
  refine ⟨F, hFS, hFH, ⟨k, hk.trans hAj⟩, ?_⟩
  by_contra hF_not_selected
  have hAF : A ≠ F := fun h => hFH (h ▸ hAH)
  have hA_not_selected :
      ¬ (interior A.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty := by
    intro hA_selected
    have hAE : A.carrier ⊆ E := hE_faces A (H.faces_sub hAH) hA_selected
    obtain ⟨z, hzA⟩ := (tileDisk A).interior_nonempty
    have hAH_carrier : A.carrier ⊆ H.carrier := by
      intro x hx
      change x ∈ H.disk.carrier
      rw [H.carrier_eq]
      exact carrier_subset_support hAH hx
    have hzH : z ∈ interior H.carrier := interior_mono hAH_carrier hzA
    have hz_closure : z ∈ closure (connectedComponentIn (Eᶜ) c) := by
      rw [← hH_def]
      exact interior_subset hzH
    obtain ⟨x, hxA, hx_component⟩ :=
      mem_closure_iff.1 hz_closure (interior A.carrier) isOpen_interior hzA
    exact (connectedComponentIn_subset (Eᶜ) c hx_component) (hAE (interior_subset hxA))
  let T : Set (PlacedTile P) :=
    {D | D ∈ S.tiles ∧ (interior D.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty}
  have hT_fin : T.Finite := S.finite.subset (fun D hD => hD.1)
  have hT_closed : IsClosed (support T) := support_isClosed hT_fin
  have hq_not_selected_support : q ∉ support T := by
    intro hqT
    obtain ⟨D, ⟨hDS, hD_selected⟩, hqD⟩ := mem_support_iff'.1 hqT
    by_cases hDA : D = A
    · exact hA_not_selected (hDA ▸ hD_selected)
    have hqD_not_vertex : q ∉ D.vertexSet := fun hv => J.no_vertex hAH hDS j hq hv
    obtain ⟨l, hl⟩ := tile_partner S.disjoint hsts (H.faces_sub hAH) hDS (Ne.symm hDA) j hq hqD hqD_not_vertex
    have hFD : F = D :=
      side_partner_unique S.disjoint (H.faces_sub hAH) hFS hDS hAF (Ne.symm hDA) j k l hk hl
    exact hF_not_selected (hFD ▸ hD_selected)
  have hqH : q ∈ H.carrier := by
    change q ∈ H.disk.carrier
    exact pd_frontier_subset_carrier H.disk hq_frontier_disk
  have hqOmega : q ∈ interior Ω.carrier := hQ (hbuffer (hH_sub hqH))
  obtain ⟨rΩ, hrΩ, hrΩ_sub⟩ := Metric.isOpen_iff.1 isOpen_interior q hqOmega
  obtain ⟨rT, hrT, hrT_sub⟩ := Metric.isOpen_iff.1 hT_closed.isOpen_compl q hq_not_selected_support
  let r := min rΩ rT
  have hr : 0 < r := lt_min hrΩ hrT
  have hball_Ec : Metric.ball q r ⊆ Eᶜ := by
    intro x hx hxE
    rw [hE_def] at hxE
    rcases hxE with hxΩ | hx_selected
    · exact hxΩ (interior_subset (hrΩ_sub (Metric.ball_subset_ball (min_le_left _ _) hx)))
    · simp only [Set.mem_iUnion] at hx_selected
      obtain ⟨D, hDS, hD_selected, hxD⟩ := hx_selected
      exact (hrT_sub (Metric.ball_subset_ball (min_le_right _ _) hx))
        (carrier_subset_support (show D ∈ T from ⟨hDS, hD_selected⟩) hxD)
  have hq_component_closure : q ∈ closure (connectedComponentIn (Eᶜ) c) := by
    rw [← hH_def]
    exact hqH
  obtain ⟨x, hx_ball, hx_component⟩ :=
    mem_closure_iff.1 hq_component_closure (Metric.ball q r) Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hqF : q ∈ F.carrier := tile_side_subset F k (by rw [hk]; exact openSeg_mem_side A j hq)
  have hqF_closure : q ∈ closure (interior F.carrier) := by
    rw [tile_regular]
    exact hqF
  obtain ⟨y, hy_ball, hyF⟩ :=
    mem_closure_iff.1 hqF_closure (Metric.ball q r) Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hball_component : Metric.ball q r ⊆ connectedComponentIn (Eᶜ) x :=
    (convex_ball q r).isPreconnected.subset_connectedComponentIn hx_ball hball_Ec
  have hy_component : y ∈ connectedComponentIn (Eᶜ) c := by
    rw [connectedComponentIn_eq hx_component]
    exact hball_component hy_ball
  have hyH : y ∈ H.carrier := by
    rw [hH_def]
    exact subset_closure hy_component
  change y ∈ H.disk.carrier at hyH
  rw [H.carrier_eq] at hyH
  obtain ⟨D, hDH, hyD⟩ := mem_support_iff'.1 hyH
  exact interior_not_mem_other S.disjoint hFS (H.faces_sub hDH)
    (fun h => hFH (h ▸ hDH)) hyF hyD

/-- `lem:outside-grouping`: with `Q₁ + B∞(10D) ⊂ int Ω` and `K₁ = Q₁ + B∞(3D)`
there is a group `H` with `Q₁ + B∞(2D) ⊂ H ⊂ K₁`, outside-anchored at `K₁`,
whose open complement is connected. -/
theorem outsideAnchoredGrouping (M : MeshConstants P) (S : Patch P) (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier) :
    ∃ H : FaceGroup S.tiles, square c h + Binf (2 * M.D) ⊆ H.carrier ∧
      H.carrier ⊆ square c h + Binf (3 * M.D) ∧
      H.OutsideAnchored (square c h + Binf (3 * M.D)) ∧ IsConnected (H.carrier)ᶜ := by
  have s1 := outsideAnchoredGrouping_step1_E M S Ω hcov hsts c h hh hQ
  rcases s1 with ⟨E, ⟨hE_conn, hE_supset, hE_faces⟩, hE_def⟩
  have s2 := outsideAnchoredGrouping_step2_H M S Ω hcov hsts c h hh hQ E hE_conn
    hE_supset hE_faces hE_def
  rcases s2 with ⟨H_carrier, hH_supset, hH_subset, hH_def, hH_conn_int, hH_conn_comp⟩
  have s3 := outsideAnchoredGrouping_step3_FaceGroup M S Ω hcov hsts c h hh hQ E hE_conn
    hE_supset hE_faces hE_def H_carrier hH_subset hH_def
  rcases s3 with ⟨H, hH_eq⟩
  use H
  rw [hH_eq]
  refine ⟨hH_supset, hH_subset, ?_, hH_conn_comp⟩
  rw [← hH_eq] at hH_subset hH_def hH_conn_int hH_conn_comp
  exact outsideAnchoredGrouping_step4_anchor M S Ω hcov hsts c h hh hQ E hE_faces hE_def H
    hH_subset hH_def hH_conn_int hH_conn_comp

/-! ## Spokes and annular groups -/

/-- A system of `4N` skeletal spokes in the annulus `H \ int L` and the `4N`
annular groups obtained by cutting along them (`lem:annular-spokes`).  The
`j`-th group lies between spokes `j` and `j + 1` (cyclically). -/
structure SpokeSystem (S : Set (PlacedTile P)) (L H : FaceGroup S) (N : ℕ) where
  spoke : Fin (4 * N) → PolyArc
  simple : ∀ j, (spoke j).IsSimple
  skeletal : ∀ j, (spoke j).IsSkeletal S
  in_annulus : ∀ j, (spoke j).carrier ⊆ H.carrier \ interior L.carrier
  meets_L : ∀ j, (spoke j).carrier ∩ frontier L.carrier = {(spoke j).start}
  meets_H : ∀ j, (spoke j).carrier ∩ frontier H.carrier = {(spoke j).stop}
  disjoint : ∀ i j, i ≠ j → Disjoint (spoke i).carrier (spoke j).carrier
  order : MatchingCyclicOrder (H.carrier \ interior L.carrier) (frontier H.carrier)
    (frontier L.carrier) (fun j => (spoke j).stop) (fun j => (spoke j).start)
  piece : Fin (4 * N) → FaceGroup S
  piece_partition : ∀ A ∈ S, (A ∈ H.faces ∧ A ∉ L.faces) ↔ ∃! j, A ∈ (piece j).faces
  /-- every piece is made of faces of `H` that are not faces of `L` (with `piece_partition`:
  the pieces partition the faces of `H \ L`, and no piece contains any other face) -/
  piece_sub : ∀ j, (piece j).faces ⊆ H.faces \ L.faces
  piece_between : ∀ j,
    (spoke j).carrier ⊆ (piece j).carrier ∧
      (spoke (finRotate (4 * N) j)).carrier ⊆ (piece j).carrier
  contact_connected : ∀ j, IsConnected ((piece j).carrier ∩ L.carrier)
  contact_nondegenerate : ∀ j, ((piece j).carrier ∩ L.carrier).Nontrivial

/-- The full annular grouping around the centre `c`: `Q₀ = square c (NR/2)`,
`Q₁ = square c (NR/2 + R)`, `K₁ = Q₁ + B∞(3D)`, the inside-anchored group `L`,
the outside-anchored group `H`, and a spoke system between them. -/
structure AnnularGrouping (M : MeshConstants P) (S : Set (PlacedTile P)) (c : Pt) (N : ℕ)
    (R : ℝ) where
  L : FaceGroup S
  H : FaceGroup S
  L_lower : square c ((N : ℝ) * R / 2) ⊆ L.carrier
  L_upper : L.carrier ⊆ square c ((N : ℝ) * R / 2) + Binf M.D
  L_anchor : L.InsideAnchored (square c ((N : ℝ) * R / 2))
  H_lower : square c ((N : ℝ) * R / 2 + R) + Binf (2 * M.D) ⊆ H.carrier
  H_upper : H.carrier ⊆ square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D)
  H_anchor : H.OutsideAnchored (square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D))
  spokes : SpokeSystem S L H N

/-! ### Helpers for `existsAnnularSpokes` -/

/-- The point at arclength parameter `t` on the boundary of the square `[-A, A]²`, starting at
the corner `(A, -A)` and running counterclockwise (a private copy of `squarePerimeterPoint`,
which is declared after `existsAnnularSpokes`; the two definitions are definitionally equal). -/
private def existsAnnularSpokes_pos (A t : ℝ) : Pt :=
  if t ≤ 2 * A then mkPt A (-A + t)
  else if t ≤ 4 * A then mkPt (A - (t - 2 * A)) A
  else if t ≤ 6 * A then mkPt (-A) (A - (t - 4 * A))
  else mkPt (-A + (t - 6 * A)) (-A)

/-- The `j`-th extended radial segment: the part of the ray from the centre `c` through the
`j`-th length-`R` position `v_j` of `∂Q₀` (`Q₀ = square c (NR/2)`, `v_j` at arclength `jR`)
between infinity norms `NR/2 - 3D` and `NR/2 + R + 6D` from `c`, i.e. the radial segment from
`∂Q₀` to `∂K₁` (`K₁ = square c (NR/2 + R + 3D)`) extended by `3D` past both squares. -/
private def existsAnnularSpokes_ray (c : Pt) (N : ℕ) (R D : ℝ) (j : ℕ) : Set Pt :=
  segment ℝ
    (c + (((N : ℝ) * R / 2 - 3 * D) / ((N : ℝ) * R / 2)) •
      existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R))
    (c + (((N : ℝ) * R / 2 + R + 6 * D) / ((N : ℝ) * R / 2)) •
      existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R))

/-- `existsAnnularSpokes_skelEdgeIn S Z u w`: the segment `[u, w]` is a complete listed side of
a tile of `S` (an edge of the original skeleton) and lies in `Z`.  Walks in the skeleton are
chains of this relation (`Relation.ReflTransGen`). -/
private def existsAnnularSpokes_skelEdgeIn (S : Set (PlacedTile P)) (Z : Set Pt) (u w : Pt) :
    Prop :=
  (∃ A ∈ S, HasEdge A (segment ℝ u w)) ∧ segment ℝ u w ⊆ Z

/-- Step 1 of the blueprint proof of `existsAnnularSpokes`: "Take concentric squares `Q₀, Q₁`
... with the margin required above."  Square buffers are nested with room to spare:
`square c a + B∞(r) ⊂ int (square c b + B∞(s))` whenever `a + r < b + s` (`b, s ≥ 0`).  In
particular `L ⊂ Q₀ + B∞(D)` lies in the interior of `H ⊃ Q₁ + B∞(2D)`, and
`H ⊂ Q₁ + B∞(3D)` lies in `int (Q₁ + B∞(10D)) ⊂ int Ω`. -/
private lemma existsAnnularSpokes_step1_nest (c : Pt) {a r b s : ℝ} (h : a + r < b + s)
    (hb : 0 ≤ b) (hs : 0 ≤ s) : square c a + Binf r ⊆ interior (square c b + Binf s) := by
  have hsum : square c a + Binf r ⊆ square c (a + r) := by
    rintro x ⟨u, hu, v, hv, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [PiLp.add_apply]
      calc
        |u 0 + v 0 - c 0| = |(u 0 - c 0) + v 0| := by
          congr 1
          ring_nf
        _ ≤ |u 0 - c 0| + |v 0| := abs_add_le _ _
        _ ≤ a + r := add_le_add hu.1 hv.1
    · simp only [PiLp.add_apply]
      calc
        |u 1 + v 1 - c 1| = |(u 1 - c 1) + v 1| := by
          congr 1
          ring_nf
        _ ≤ |u 1 - c 1| + |v 1| := abs_add_le _ _
        _ ≤ a + r := add_le_add hu.2 hv.2
  have hinner : square c (a + r) ⊆ interior (square c (b + s)) := by
    intro x hx
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    refine ⟨(b + s - (a + r)) / 2, by linarith, ?_⟩
    intro y hy
    rw [Metric.mem_ball] at hy
    have hy0 : |y 0 - x 0| ≤ dist y x := rg_coord_sub_le y x 0
    have hy1 : |y 1 - x 1| ≤ dist y x := rg_coord_sub_le y x 1
    refine ⟨?_, ?_⟩
    · calc
        |y 0 - c 0| = |(y 0 - x 0) + (x 0 - c 0)| := by
          congr 1
          ring_nf
        _ ≤ |y 0 - x 0| + |x 0 - c 0| := abs_add_le _ _
        _ ≤ dist y x + (a + r) := add_le_add hy0 hx.1
        _ ≤ b + s := (by linarith)
    · calc
        |y 1 - c 1| = |(y 1 - x 1) + (x 1 - c 1)| := by
          congr 1
          ring_nf
        _ ≤ |y 1 - x 1| + |x 1 - c 1| := abs_add_le _ _
        _ ≤ dist y x + (a + r) := add_le_add hy1 hx.2
        _ ≤ b + s := (by linarith)
  exact hsum.trans (hinner.trans (interior_mono (rg_square_add hb hs)))

/-- Technical bound for `existsAnnularSpokes_step2_tubes`: a boundary position
`existsAnnularSpokes_pos A t` (for `t` in the arclength range `[0, 8A]` of one full lap) has
coordinate vector of Euclidean norm at most `A√2`. -/
private lemma existsAnnularSpokes_step2_tubes_normLe {A t : ℝ} (h0 : 0 ≤ t) (h8 : t ≤ 8 * A) :
    (existsAnnularSpokes_pos A t 0) ^ 2 + (existsAnnularSpokes_pos A t 1) ^ 2 ≤ 2 * A ^ 2 := by
  unfold existsAnnularSpokes_pos
  split_ifs <;> simp [mkPt] <;> nlinarith

/-- Technical bound for `existsAnnularSpokes_step2_tubes`: a boundary position
`existsAnnularSpokes_pos A t` has coordinate vector of Euclidean norm at least `A` (one of its
two coordinates is exactly `±A`). -/
private lemma existsAnnularSpokes_step2_tubes_normGe (A t : ℝ) :
    A ^ 2 ≤ (existsAnnularSpokes_pos A t 0) ^ 2 + (existsAnnularSpokes_pos A t 1) ^ 2 := by
  unfold existsAnnularSpokes_pos
  split_ifs <;> simp [mkPt] <;>
    nlinarith [sq_nonneg (t - A), sq_nonneg (3 * A - t), sq_nonneg (5 * A - t),
      sq_nonneg (t - 7 * A)]

/-- Technical parametrization for `existsAnnularSpokes_step2_tubes`: every point of the `k`-th
extended radial segment is `c + μ • v_k` for some `μ` in the segment's ideal range of homothety
factors, `v_k` the `k`-th boundary position of `∂Q₀`. -/
private lemma existsAnnularSpokes_step2_tubes_rayMem {c : Pt} {N : ℕ} {R D : ℝ} (hR : 0 ≤ R)
    (hD : 0 ≤ D) (hA : 0 < (N : ℝ) * R / 2) {k : ℕ} {p : Pt}
    (hp : p ∈ existsAnnularSpokes_ray c N R D k) :
    ∃ μ : ℝ, ((N : ℝ) * R / 2 - 3 * D) / ((N : ℝ) * R / 2) ≤ μ ∧
      μ ≤ ((N : ℝ) * R / 2 + R + 6 * D) / ((N : ℝ) * R / 2) ∧
      p = c + μ • existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((k : ℝ) * R) := by
  unfold existsAnnularSpokes_ray at hp
  set A := (N : ℝ) * R / 2 with hAeq
  obtain ⟨t, ht0, ht1, hpe⟩ := mem_segment_iff'.1 hp
  have hk21 : (A - 3 * D) / A ≤ (A + R + 6 * D) / A := by
    rw [div_le_div_iff_of_pos_right hA]
    nlinarith
  refine ⟨(A - 3 * D) / A + t * ((A + R + 6 * D) / A - (A - 3 * D) / A), by nlinarith,
    by nlinarith, ?_⟩
  rw [hpe]
  module

/-- Lagrange's identity bound for `existsAnnularSpokes_step2_tubes`: the cross product `jcr u v`
is bounded by the product of the two Euclidean norms. -/
private lemma existsAnnularSpokes_step2_tubes_jcrSq (u v : Pt) :
    jcr u v ^ 2 ≤ (u 0 ^ 2 + u 1 ^ 2) * (v 0 ^ 2 + v 1 ^ 2) := by
  simp only [jcr]
  nlinarith [sq_nonneg (u 0 * v 0 + u 1 * v 1)]

/-- Elementary real-analysis fact for `existsAnnularSpokes_step2_tubes`: comparing squares of
nonnegative reals compares the reals. -/
private lemma existsAnnularSpokes_step2_tubes_sqLt {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 < b ^ 2) : a < b := by
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_self_le_mul_self hb hcon]

private lemma existsAnnularSpokes_step2_tubes_pos_cases {N : ℕ} {R : ℝ} (hR : 0 < R)
    {k : ℕ} (hk : k < 4 * N) :
    k ≤ N ∧ existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((k : ℝ) * R) =
        mkPt ((N : ℝ) * R / 2) (-((N : ℝ) * R / 2) + (k : ℝ) * R) ∨
    N < k ∧ k ≤ 2 * N ∧ existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((k : ℝ) * R) =
        mkPt (3 * ((N : ℝ) * R / 2) - (k : ℝ) * R) ((N : ℝ) * R / 2) ∨
    2 * N < k ∧ k ≤ 3 * N ∧ existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((k : ℝ) * R) =
        mkPt (-((N : ℝ) * R / 2)) (5 * ((N : ℝ) * R / 2) - (k : ℝ) * R) ∨
    3 * N < k ∧ existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((k : ℝ) * R) =
        mkPt ((k : ℝ) * R - 7 * ((N : ℝ) * R / 2)) (-((N : ℝ) * R / 2)) := by
  have hR0 : 0 ≤ R := hR.le
  have hA : 0 < (N : ℝ) * R / 2 := by
    have hN : 0 < N := by omega
    positivity
  have hkn : k ≤ N ∨ N < k ∧ k ≤ 2 * N ∨ 2 * N < k ∧ k ≤ 3 * N ∨ 3 * N < k := by
    omega
  rcases hkn with hkn | hkn | hkn | hkn
  · left
    refine ⟨hkn, ?_⟩
    unfold existsAnnularSpokes_pos
    have ht : (k : ℝ) * R ≤ 2 * ((N : ℝ) * R / 2) := by
      rw [div_eq_mul_inv]
      have hk' : (k : ℝ) ≤ N := by exact_mod_cast hkn
      nlinarith
    simp only [if_pos ht]
  · right; left
    refine ⟨hkn.1, hkn.2, ?_⟩
    unfold existsAnnularSpokes_pos
    have ht0 : ¬ ((k : ℝ) * R ≤ 2 * ((N : ℝ) * R / 2)) := by
      intro ht
      have hk' : (k : ℝ) ≤ N := by
        nlinarith
      have hkn' : (N : ℝ) < k := by exact_mod_cast hkn.1
      nlinarith
    have ht1 : (k : ℝ) * R ≤ 4 * ((N : ℝ) * R / 2) := by
      have hk' : (k : ℝ) ≤ 2 * N := by exact_mod_cast hkn.2
      nlinarith
    simp only [if_neg ht0, if_pos ht1]
    congr 1
    all_goals ring
  · right; right; left
    refine ⟨hkn.1, hkn.2, ?_⟩
    unfold existsAnnularSpokes_pos
    have ht0 : ¬ ((k : ℝ) * R ≤ 2 * ((N : ℝ) * R / 2)) := by
      intro ht
      have hk' : (k : ℝ) ≤ N := by nlinarith
      have hkn' : (2 * (N : ℝ)) < k := by exact_mod_cast hkn.1
      nlinarith
    have ht1 : ¬ ((k : ℝ) * R ≤ 4 * ((N : ℝ) * R / 2)) := by
      intro ht
      have hk' : (k : ℝ) ≤ 2 * N := by nlinarith
      have hkn' : (2 * (N : ℝ)) < k := by exact_mod_cast hkn.1
      nlinarith
    have ht2 : (k : ℝ) * R ≤ 6 * ((N : ℝ) * R / 2) := by
      have hk' : (k : ℝ) ≤ 3 * N := by exact_mod_cast hkn.2
      nlinarith
    simp only [if_neg ht0, if_neg ht1, if_pos ht2]
    congr 1
    all_goals ring
  · right; right; right
    refine ⟨hkn, ?_⟩
    unfold existsAnnularSpokes_pos
    have ht0 : ¬ ((k : ℝ) * R ≤ 2 * ((N : ℝ) * R / 2)) := by
      intro ht
      have hk' : (k : ℝ) ≤ N := by nlinarith
      have hkn' : (3 * (N : ℝ)) < k := by exact_mod_cast hkn
      nlinarith
    have ht1 : ¬ ((k : ℝ) * R ≤ 4 * ((N : ℝ) * R / 2)) := by
      intro ht
      have hk' : (k : ℝ) ≤ 2 * N := by nlinarith
      have hkn' : (3 * (N : ℝ)) < k := by exact_mod_cast hkn
      nlinarith
    have ht2 : ¬ ((k : ℝ) * R ≤ 6 * ((N : ℝ) * R / 2)) := by
      intro ht
      have hk' : (k : ℝ) ≤ 3 * N := by nlinarith
      have hkn' : (3 * (N : ℝ)) < k := by exact_mod_cast hkn
      nlinarith
    simp only [if_neg ht0, if_neg ht1, if_neg ht2]
    congr 1
    all_goals ring

/-! Each of the following is one pair of sides in the square-perimeter calculation. -/

/-- Step 1a of the blueprint proof: two marks on the first straight side. -/
private lemma existsAnnularSpokes_step2_tubes_step1_baseSep_s0s0 {N : ℕ} {R : ℝ}
    (hN : 2 ≤ N) (hR : 0 < R) {i j : ℕ} (hi : i < 4 * N) (hj : j < 4 * N)
    (hij : i < j) (hi0 : i ≤ N) (hj0 : j ≤ N) :
    existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R) =
        - existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R) ∨
      (N : ℝ) * R / 2 * R ≤
        |jcr (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R))
          (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R))| := by
  sorry

/-- Step 1b of the blueprint proof: two marks on the second straight side. -/
private lemma existsAnnularSpokes_step2_tubes_step1_baseSep_s1s1 {N : ℕ} {R : ℝ}
    (hN : 2 ≤ N) (hR : 0 < R) {i j : ℕ} (hi : i < 4 * N) (hj : j < 4 * N)
    (hij : i < j) (hi1 : N < i ∧ i ≤ 2 * N) (hj1 : N < j ∧ j ≤ 2 * N) :
    existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R) =
        - existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R) ∨
      (N : ℝ) * R / 2 * R ≤
        |jcr (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R))
          (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R))| := by
  sorry

/-- Step 1c of the blueprint proof: two marks on the third straight side. -/
private lemma existsAnnularSpokes_step2_tubes_step1_baseSep_s2s2 {N : ℕ} {R : ℝ}
    (hN : 2 ≤ N) (hR : 0 < R) {i j : ℕ} (hi : i < 4 * N) (hj : j < 4 * N)
    (hij : i < j) (hi2 : 2 * N < i ∧ i ≤ 3 * N) (hj2 : 2 * N < j ∧ j ≤ 3 * N) :
    existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R) =
        - existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R) ∨
      (N : ℝ) * R / 2 * R ≤
        |jcr (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R))
          (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R))| := by
  sorry

/-- Step 1d of the blueprint proof: two marks on the fourth straight side. -/
private lemma existsAnnularSpokes_step2_tubes_step1_baseSep_s3s3 {N : ℕ} {R : ℝ}
    (hN : 2 ≤ N) (hR : 0 < R) {i j : ℕ} (hi : i < 4 * N) (hj : j < 4 * N)
    (hij : i < j) (hi3 : 3 * N < i) (hj3 : 3 * N < j) :
    existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R) =
        - existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R) ∨
      (N : ℝ) * R / 2 * R ≤
        |jcr (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R))
          (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R))| := by
  sorry

/-- Step 1e of the blueprint proof: marks on the first two adjacent sides. -/
private lemma existsAnnularSpokes_step2_tubes_step1_baseSep_s0s1 {N : ℕ} {R : ℝ}
    (hN : 2 ≤ N) (hR : 0 < R) {i j : ℕ} (hi : i < 4 * N) (hj : j < 4 * N)
    (hij : i < j) (hi0 : i ≤ N) (hj1 : N < j ∧ j ≤ 2 * N) :
    existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R) =
        - existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R) ∨
      (N : ℝ) * R / 2 * R ≤
        |jcr (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R))
          (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R))| := by
  sorry

/-- Step 1f of the blueprint proof: marks on the second and third adjacent sides. -/
private lemma existsAnnularSpokes_step2_tubes_step1_baseSep_s1s2 {N : ℕ} {R : ℝ}
    (hN : 2 ≤ N) (hR : 0 < R) {i j : ℕ} (hi : i < 4 * N) (hj : j < 4 * N)
    (hij : i < j) (hi1 : N < i ∧ i ≤ 2 * N) (hj2 : 2 * N < j ∧ j ≤ 3 * N) :
    existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R) =
        - existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R) ∨
      (N : ℝ) * R / 2 * R ≤
        |jcr (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R))
          (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R))| := by
  sorry

/-- Step 1g of the blueprint proof: marks on the third and fourth adjacent sides. -/
private lemma existsAnnularSpokes_step2_tubes_step1_baseSep_s2s3 {N : ℕ} {R : ℝ}
    (hN : 2 ≤ N) (hR : 0 < R) {i j : ℕ} (hi : i < 4 * N) (hj : j < 4 * N)
    (hij : i < j) (hi2 : 2 * N < i ∧ i ≤ 3 * N) (hj3 : 3 * N < j) :
    existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R) =
        - existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R) ∨
      (N : ℝ) * R / 2 * R ≤
        |jcr (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R))
          (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R))| := by
  sorry

/-- Step 1h of the blueprint proof: marks on the fourth and first adjacent sides cyclically. -/
private lemma existsAnnularSpokes_step2_tubes_step1_baseSep_s0s3 {N : ℕ} {R : ℝ}
    (hN : 2 ≤ N) (hR : 0 < R) {i j : ℕ} (hi : i < 4 * N) (hj : j < 4 * N)
    (hij : i < j) (hi0 : i ≤ N) (hj3 : 3 * N < j) :
    existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R) =
        - existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R) ∨
      (N : ℝ) * R / 2 * R ≤
        |jcr (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R))
          (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R))| := by
  sorry

/-- Step 1i of the blueprint proof: marks on the first and third opposite sides. -/
private lemma existsAnnularSpokes_step2_tubes_step1_baseSep_s0s2 {N : ℕ} {R : ℝ}
    (hN : 2 ≤ N) (hR : 0 < R) {i j : ℕ} (hi : i < 4 * N) (hj : j < 4 * N)
    (hij : i < j) (hi0 : i ≤ N) (hj2 : 2 * N < j ∧ j ≤ 3 * N) :
    existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R) =
        - existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R) ∨
      (N : ℝ) * R / 2 * R ≤
        |jcr (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R))
          (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R))| := by
  sorry

/-- Step 1j of the blueprint proof: marks on the second and fourth opposite sides. -/
private lemma existsAnnularSpokes_step2_tubes_step1_baseSep_s1s3 {N : ℕ} {R : ℝ}
    (hN : 2 ≤ N) (hR : 0 < R) {i j : ℕ} (hi : i < 4 * N) (hj : j < 4 * N)
    (hij : i < j) (hi1 : N < i ∧ i ≤ 2 * N) (hj3 : 3 * N < j) :
    existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R) =
        - existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R) ∨
      (N : ℝ) * R / 2 * R ≤
        |jcr (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R))
          (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R))| := by
  sorry

/-- Step 1 of the blueprint proof of `existsAnnularSpokes_step2_tubes`: "In the square annulus,
successive radial segments have separation at least a universal positive multiple of `R`.  This
follows by considering a straight side and the two sides adjacent to a corner."  For `N ≥ 2` and
distinct `i, j < 4N`, the two boundary positions `v_i, v_j` of `∂Q₀` (`existsAnnularSpokes_pos`
at arclength `iR` resp. `jR`) are either antipodal (`v_j = -v_i`, which happens exactly when `i`
and `j` differ by `2N`) or their cross product has magnitude at least `(NR/2) * R`. -/
private lemma existsAnnularSpokes_step2_tubes_step1_baseSep {N : ℕ} {R : ℝ} (hN : 2 ≤ N)
    (hR : 0 < R) {i j : ℕ} (hi : i < 4 * N) (hj : j < 4 * N) (hij : i ≠ j) :
    existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R) =
      - existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R) ∨
      (N : ℝ) * R / 2 * R ≤
      |jcr (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((i : ℝ) * R))
        (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R))| := by
  have hordered : ∀ {a b : ℕ}, a < b → a < 4 * N → b < 4 * N →
      existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((b : ℝ) * R) =
          - existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((a : ℝ) * R) ∨
        (N : ℝ) * R / 2 * R ≤
          |jcr (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((a : ℝ) * R))
            (existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((b : ℝ) * R))| := by
    intro a b hab ha4 hb4
    have ha := existsAnnularSpokes_step2_tubes_pos_cases hR ha4
    have hb := existsAnnularSpokes_step2_tubes_pos_cases hR hb4
    rcases ha with ⟨ha0, _⟩ | ⟨ha1, ha1', _⟩ | ⟨ha2, ha2', _⟩ | ⟨ha3, _⟩
    · rcases hb with ⟨hb0, _⟩ | ⟨hb1, hb1', _⟩ | ⟨hb2, hb2', _⟩ | ⟨hb3, _⟩
      · exact existsAnnularSpokes_step2_tubes_step1_baseSep_s0s0 hN hR (by omega) (by omega)
          hab ha0 hb0
      · exact existsAnnularSpokes_step2_tubes_step1_baseSep_s0s1 hN hR (by omega) (by omega)
          hab ha0 ⟨hb1, hb1'⟩
      · exact existsAnnularSpokes_step2_tubes_step1_baseSep_s0s2 hN hR (by omega) (by omega)
          hab ha0 ⟨hb2, hb2'⟩
      · exact existsAnnularSpokes_step2_tubes_step1_baseSep_s0s3 hN hR (by omega) (by omega)
          hab ha0 hb3
    · rcases hb with ⟨hb0, _⟩ | ⟨hb1, hb1', _⟩ | ⟨hb2, hb2', _⟩ | ⟨hb3, _⟩
      · omega
      · exact existsAnnularSpokes_step2_tubes_step1_baseSep_s1s1 hN hR (by omega) (by omega)
          hab ⟨ha1, ha1'⟩ ⟨hb1, hb1'⟩
      · exact existsAnnularSpokes_step2_tubes_step1_baseSep_s1s2 hN hR (by omega) (by omega)
          hab ⟨ha1, ha1'⟩ ⟨hb2, hb2'⟩
      · exact existsAnnularSpokes_step2_tubes_step1_baseSep_s1s3 hN hR (by omega) (by omega)
          hab ⟨ha1, ha1'⟩ hb3
    · rcases hb with ⟨hb0, _⟩ | ⟨hb1, hb1', _⟩ | ⟨hb2, hb2', _⟩ | ⟨hb3, _⟩
      · omega
      · omega
      · exact existsAnnularSpokes_step2_tubes_step1_baseSep_s2s2 hN hR (by omega) (by omega)
          hab ⟨ha2, ha2'⟩ ⟨hb2, hb2'⟩
      · exact existsAnnularSpokes_step2_tubes_step1_baseSep_s2s3 hN hR (by omega) (by omega)
          hab ⟨ha2, ha2'⟩ hb3
    · rcases hb with ⟨hb0, _⟩ | ⟨hb1, hb1', _⟩ | ⟨hb2, hb2', _⟩ | ⟨hb3, _⟩
      · omega
      · omega
      · omega
      · exact existsAnnularSpokes_step2_tubes_step1_baseSep_s3s3 hN hR (by omega) (by omega)
          hab ha3 hb3
  rcases lt_or_gt_of_ne hij with hij' | hji
  · exact hordered hij' hi hj
  · have h := hordered hji hj hi
    rcases h with hanti | hcross
    · left
      rw [hanti]
      simp
    · right
      rw [jcr_anti, abs_neg] at hcross
      exact hcross

/-- Step 2 of the blueprint proof of `existsAnnularSpokes_step2_tubes`: "Extending each segment a
bounded number of mesh diameters past the two cycles preserves disjoint tubes when `R/D` is
sufficiently large."  For `N ≥ 2` and `R ≥ 100 D`, any point of the `i`-th extended radial
segment and any point of the `j`-th extended radial segment, for distinct `i j`, are at distance
more than `2D`. -/
private lemma existsAnnularSpokes_step2_tubes_step2_separation (c : Pt) {N : ℕ} {R D : ℝ}
    (hD : 0 < D) (hN : 2 ≤ N) (hR : 100 * D ≤ R) {i j : Fin (4 * N)} (hij : i ≠ j)
    {p q : Pt} (hp : p ∈ existsAnnularSpokes_ray c N R D i)
    (hq : q ∈ existsAnnularSpokes_ray c N R D j) :
    2 * D < dist p q := by
  have hR0 : 0 < R := by linarith
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  have hAR : R ≤ (N : ℝ) * R / 2 := by nlinarith
  obtain ⟨μp, hμp1, hμp2, hpeq⟩ := existsAnnularSpokes_step2_tubes_rayMem hR0.le hD.le hA hp
  obtain ⟨μq, hμq1, hμq2, hqeq⟩ := existsAnnularSpokes_step2_tubes_rayMem hR0.le hD.le hA hq
  set A := (N : ℝ) * R / 2 with hAeq
  clear_value A
  have hμp0 : (97 : ℝ) / 100 ≤ μp := by
    have h1 : (97 : ℝ) / 100 ≤ (A - 3 * D) / A := by rw [le_div_iff₀ hA]; nlinarith
    linarith [h1.trans hμp1]
  have hμq0 : (97 : ℝ) / 100 ≤ μq := by
    have h1 : (97 : ℝ) / 100 ≤ (A - 3 * D) / A := by rw [le_div_iff₀ hA]; nlinarith
    linarith [h1.trans hμq1]
  set vi := existsAnnularSpokes_pos A (((i : ℕ) : ℝ) * R) with hvi
  set vj := existsAnnularSpokes_pos A (((j : ℕ) : ℝ) * R) with hvj
  clear_value vi vj
  have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  have hpq0 : p 0 - q 0 = μp * vi 0 - μq * vj 0 := by
    rw [hpeq, hqeq]; simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hpq1 : p 1 - q 1 = μp * vi 1 - μq * vj 1 := by
    rw [hpeq, hqeq]; simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hdsq : dist p q ^ 2 = (μp * vi 0 - μq * vj 0) ^ 2 + (μp * vi 1 - μq * vj 1) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs,
      hpq0, hpq1]
  rcases existsAnnularSpokes_step2_tubes_step1_baseSep hN hR0 i.isLt j.isLt hij' with hanti | hcross
  · have hanti' : vj = -vi := by rw [hvj, hvi, hAeq]; exact hanti
    have hviq : dist p q ^ 2 = (μp + μq) ^ 2 * (vi 0 ^ 2 + vi 1 ^ 2) := by
      rw [hdsq, hanti']; simp only [PiLp.neg_apply]; ring
    have hvinorm := existsAnnularSpokes_step2_tubes_normGe A (((i : ℕ) : ℝ) * R)
    rw [← hvi] at hvinorm
    have hsum : (194 : ℝ) / 100 ≤ μp + μq := by linarith
    have hprod : ((194 : ℝ) / 100) ^ 2 * A ^ 2 ≤ (μp + μq) ^ 2 * (vi 0 ^ 2 + vi 1 ^ 2) :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) hsum 2) hvinorm (sq_nonneg A) (sq_nonneg (μp + μq))
    have hA2 : R ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hR0.le hAR 2
    have hD2 : D ^ 2 ≤ (R / 100) ^ 2 := pow_le_pow_left₀ hD.le (by linarith) 2
    have hfinal : (2 * D) ^ 2 < dist p q ^ 2 := by
      rw [hviq]
      nlinarith only [hprod, hA2, hD2, mul_pos hR0 hR0]
    exact existsAnnularSpokes_step2_tubes_sqLt (by linarith) dist_nonneg hfinal
  · set d : Pt := μp • vi - μq • vj with hddef
    clear_value d
    have hjcrd : jcr vi d = -μq * jcr vi vj := by
      rw [hddef, jcr_sub_right, jcr_smul_right, jcr_smul_right, jcr_self]; ring
    have hcross' : A * R ≤ |jcr vi vj| := by rw [hvi, hvj, hAeq]; exact hcross
    have he1 : μq * (A * R) ≤ μq * |jcr vi vj| :=
      mul_le_mul_of_nonneg_left hcross' (by linarith : (0 : ℝ) ≤ μq)
    have he2 : (97 : ℝ) / 100 * (A * R) ≤ μq * (A * R) :=
      mul_le_mul_of_nonneg_right hμq0 (by positivity : (0 : ℝ) ≤ A * R)
    have h1 : (97 : ℝ) / 100 * (A * R) ≤ |jcr vi d| := by
      rw [hjcrd, abs_mul, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ μq)]
      linarith [he1, he2]
    have hX2 : ((97 : ℝ) / 100 * (A * R)) ^ 2 ≤ jcr vi d ^ 2 := by
      have hle := pow_le_pow_left₀ (by positivity) h1 2
      rwa [sq_abs] at hle
    have h3 := existsAnnularSpokes_step2_tubes_jcrSq vi d
    have hit0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) * R := by positivity
    have hib : (i : ℕ) + 1 ≤ 4 * N := i.isLt
    have hib' : (((i : ℕ) : ℝ)) + 1 ≤ 4 * (N : ℝ) := by exact_mod_cast hib
    have hRA8 : ((i : ℕ) : ℝ) * R ≤ (4 * (N : ℝ)) * R :=
      mul_le_mul_of_nonneg_right (by linarith : ((i : ℕ) : ℝ) ≤ 4 * (N : ℝ)) hR0.le
    have hit8 : ((i : ℕ) : ℝ) * R ≤ 8 * A := by rw [hAeq]; linarith only [hRA8]
    have h4 := existsAnnularSpokes_step2_tubes_normLe hit0 hit8
    rw [← hvi] at h4
    have hd0 : d 0 = μp * vi 0 - μq * vj 0 := by
      rw [hddef]; simp [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    have hd1 : d 1 = μp * vi 1 - μq * vj 1 := by
      rw [hddef]; simp [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    have h5 : ((97 : ℝ) / 100 * (A * R)) ^ 2 ≤ 2 * A ^ 2 * (d 0 ^ 2 + d 1 ^ 2) :=
      hX2.trans (h3.trans (by nlinarith only [h4, sq_nonneg (d 0), sq_nonneg (d 1)]))
    have hA2 : R ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ hR0.le hAR 2
    have hD2 : D ^ 2 ≤ (R / 100) ^ 2 := pow_le_pow_left₀ hD.le (by linarith) 2
    have hfinal : (2 * D) ^ 2 < dist p q ^ 2 := by
      rw [hdsq, ← hd0, ← hd1]
      nlinarith only [h5, hA2, hD2, hA, mul_pos hR0 hR0]
    exact existsAnnularSpokes_step2_tubes_sqLt (by linarith) dist_nonneg hfinal

private lemma existsAnnularSpokes_step2_tubes (c : Pt) {N : ℕ} {R D : ℝ} (hD : 0 < D)
    (hN : 2 ≤ N) (hR : 100 * D ≤ R) {i j : Fin (4 * N)} (hij : i ≠ j) :
    Disjoint (Metric.cthickening D (existsAnnularSpokes_ray c N R D i))
      (Metric.cthickening D (existsAnnularSpokes_ray c N R D j)) := by
  have hci : IsCompact (existsAnnularSpokes_ray c N R D i) := isCompact_segment_pt _ _
  have hcj : IsCompact (existsAnnularSpokes_ray c N R D j) := isCompact_segment_pt _ _
  rw [hci.cthickening_eq_biUnion_closedBall hD.le, hcj.cthickening_eq_biUnion_closedBall hD.le,
    Set.disjoint_iUnion₂_left]
  intro p hp
  rw [Set.disjoint_iUnion₂_right]
  intro q hq
  exact Metric.closedBall_disjoint_closedBall (by
    have := existsAnnularSpokes_step2_tubes_step2_separation c hD hN hR hij hp hq
    linarith)

/-- Step 1 of the blueprint proof of `existsAnnularSpokes_step3_spoke`: "Follow the finite
sequence of original faces crossed by one extended segment.  Consecutive faces share a side or
vertex, and every face boundary is a connected polygonal cycle.  Their boundary graphs form a
connected finite graph, all of whose edges lie within `D` of the segment.  It meets both `∂L`
and `∂H`."  Concretely: there is a walk along original edges, each within `D` of the `j`-th
extended radial segment and inside `int Ω`, from a vertex in `int L` (a vertex of a face
containing the inner end of the segment, at infinity norm `NR/2 - 3D`; that face lies in
`int Q₀`) to a vertex outside `H` (a vertex of a face containing the outer end, at infinity
norm `NR/2 + R + 6D`; that face lies outside `K₁ ⊃ H`). -/
private lemma existsAnnularSpokes_step3_spoke_step1_walk (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk) (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) {N : ℕ} {R : ℝ} (hN : 2 ≤ N) (hR : 100 * M.D ≤ R)
    (hΩ : square c ((N : ℝ) * R / 2 + R) + Binf (10 * M.D) ⊆ interior Ω.carrier)
    (L H : FaceGroup S.tiles) (hL : square c ((N : ℝ) * R / 2) ⊆ L.carrier)
    (hH : H.carrier ⊆ square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D)) (j : Fin (4 * N)) :
    ∃ u w, u ∈ interior L.carrier ∧ w ∉ H.carrier ∧
      Relation.ReflTransGen (existsAnnularSpokes_skelEdgeIn S.tiles
        (Metric.cthickening M.D (existsAnnularSpokes_ray c N R M.D j) ∩ interior Ω.carrier))
        u w := by
  sorry

/-- Step 2 of the blueprint proof of `existsAnnularSpokes_step3_spoke`: "take the part from its
last point on `∂L` to its first subsequent point on `∂H`.  The part lies in the annulus and has
no other point on either cycle.  Planarity of the skeleton ensures that an edge cannot cross a
cycle without meeting it at a vertex."  A skeletal walk with edges in `Z ⊆ int (support S)`
from a point of `int L` to a point outside `H` contains a sub-walk from a vertex `u'` of `∂L`
to a vertex `w'` of `∂H` all of whose edges lie in `Z` and, apart from `u'` and `w'`, in
`int H \ L`. -/
private lemma existsAnnularSpokes_step3_spoke_step2_cut (S : Patch P)
    (hsts : SideToSideSet S.tiles) (L H : FaceGroup S.tiles)
    (hLH : L.carrier ⊆ interior H.carrier) {Z : Set Pt} (hZ : Z ⊆ interior (support S.tiles))
    {u w : Pt} (hu : u ∈ interior L.carrier) (hw : w ∉ H.carrier)
    (hwalk : Relation.ReflTransGen (existsAnnularSpokes_skelEdgeIn S.tiles Z) u w) :
    ∃ u' w', u' ∈ frontier L.carrier ∧ w' ∈ frontier H.carrier ∧
      Relation.ReflTransGen (existsAnnularSpokes_skelEdgeIn S.tiles
        (Z ∩ (interior H.carrier \ L.carrier ∪ {u', w'}))) u' w' := by
  sorry

/-- Step 3 of the blueprint proof of `existsAnnularSpokes_step3_spoke`: "Select a graph path,
erase loops".  A skeletal walk between two distinct points, with edges in
`Z ⊆ int (support S)`, yields a simple skeletal polygonal arc with the same endpoints inside `Z`
(by the side-to-side property, two distinct original edges inside the covered region meet at
most in a common endpoint). -/
private lemma existsAnnularSpokes_step3_spoke_step3_erase (S : Patch P)
    (hsts : SideToSideSet S.tiles) {Z : Set Pt} (hZ : Z ⊆ interior (support S.tiles))
    {u w : Pt} (huw : u ≠ w)
    (hwalk : Relation.ReflTransGen (existsAnnularSpokes_skelEdgeIn S.tiles Z) u w) :
    ∃ α : PolyArc, α.IsSimple ∧ α.IsSkeletal S.tiles ∧ α.start = u ∧ α.stop = w ∧
      α.carrier ⊆ Z := by
  sorry

/-- Step 3 of the blueprint proof of `existsAnnularSpokes`: "Follow the finite sequence of
original faces crossed by one extended segment ... Select a graph path, erase loops, and take
the part from its last point on `∂L` to its first subsequent point on `∂H`.  The part lies in
the annulus and has no other point on either cycle."  For each of the `4N` extended radial
segments there is a simple skeletal arc in `H \ int L`, meeting `∂L` only at its start and `∂H`
only at its stop, within `D` of the segment. -/
private lemma existsAnnularSpokes_step3_spoke (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk) (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) {N : ℕ} {R : ℝ} (hN : 2 ≤ N) (hR : 100 * M.D ≤ R)
    (hΩ : square c ((N : ℝ) * R / 2 + R) + Binf (10 * M.D) ⊆ interior Ω.carrier)
    (L H : FaceGroup S.tiles) (hL : square c ((N : ℝ) * R / 2) ⊆ L.carrier)
    (hLu : L.carrier ⊆ square c ((N : ℝ) * R / 2) + Binf M.D)
    (hHl : square c ((N : ℝ) * R / 2 + R) + Binf (2 * M.D) ⊆ H.carrier)
    (hHu : H.carrier ⊆ square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D)) (j : Fin (4 * N)) :
    ∃ α : PolyArc, α.IsSimple ∧ α.IsSkeletal S.tiles ∧
      α.carrier ⊆ H.carrier \ interior L.carrier ∧
      α.carrier ∩ frontier L.carrier = {α.start} ∧ α.carrier ∩ frontier H.carrier = {α.stop} ∧
      α.carrier ⊆ Metric.cthickening M.D (existsAnnularSpokes_ray c N R M.D j) := by
  have hD := M.D_pos
  have hR0 : 0 < R := by linarith
  have hb : 0 ≤ (N : ℝ) * R / 2 + R :=
    add_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg N) hR0.le) zero_le_two) hR0.le
  have hnest : square c ((N : ℝ) * R / 2) + Binf M.D ⊆
      interior (square c ((N : ℝ) * R / 2 + R) + Binf (2 * M.D)) :=
    existsAnnularSpokes_step1_nest c (by linarith) hb (by linarith)
  have hLH : L.carrier ⊆ interior H.carrier := hLu.trans (hnest.trans (interior_mono hHl))
  obtain ⟨u, w, hu, hw, hwalk⟩ :=
    existsAnnularSpokes_step3_spoke_step1_walk M S Ω hcov hsts c hN hR hΩ L H hL hHu j
  have hZ : Metric.cthickening M.D (existsAnnularSpokes_ray c N R M.D j) ∩ interior Ω.carrier ⊆
      interior (support S.tiles) := by
    rw [hcov]
    exact Set.inter_subset_right
  obtain ⟨u', w', hu', hw', hwalk'⟩ :=
    existsAnnularSpokes_step3_spoke_step2_cut S hsts L H hLH hZ hu hw hwalk
  have hfL : frontier L.carrier ⊆ L.carrier := L.disk.compact.isClosed.frontier_subset
  have hfH : frontier H.carrier ⊆ H.carrier := H.disk.compact.isClosed.frontier_subset
  have hu'H : u' ∈ interior H.carrier := hLH (hfL hu')
  have hne : u' ≠ w' := fun h => hw'.2 (h ▸ hu'H)
  obtain ⟨α, hsimp, hskel, hst, hsp, hsub⟩ :=
    existsAnnularSpokes_step3_spoke_step3_erase S hsts (Set.inter_subset_left.trans hZ) hne
      hwalk'
  have hstart : α.start ∈ α.carrier := Set.mem_iUnion.2 ⟨0, left_mem_segment ℝ _ _⟩
  have hstop : α.stop ∈ α.carrier := Set.mem_iUnion.2 ⟨Fin.last _, right_mem_segment ℝ _ _⟩
  have hmem : ∀ x ∈ α.carrier, (x ∈ interior H.carrier ∧ x ∉ L.carrier) ∨ x = u' ∨ x = w' :=
    fun x hx => (hsub hx).2
  refine ⟨α, hsimp, hskel, ?_, ?_, ?_, fun x hx => (hsub hx).1.1⟩
  · intro x hx
    rcases hmem x hx with ⟨h1, h2⟩ | rfl | rfl
    · exact ⟨interior_subset h1, fun h => h2 (interior_subset h)⟩
    · exact ⟨interior_subset hu'H, hu'.2⟩
    · exact ⟨hfH hw', fun h => hw'.2 (hLH (interior_subset h))⟩
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hxf⟩
      rcases hmem x hx with ⟨-, h2⟩ | rfl | rfl
      · exact absurd (hfL hxf) h2
      · exact hst.symm
      · exact absurd (hLH (hfL hxf)) hw'.2
    · rintro rfl
      exact ⟨hstart, by rw [hst]; exact hu'⟩
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hxf⟩
      rcases hmem x hx with ⟨h1, -⟩ | rfl | rfl
      · exact absurd h1 hxf.2
      · exact absurd hu'H hxf.2
      · exact hsp.symm
    · rintro rfl
      exact ⟨hstop, by rw [hsp]; exact hw'⟩

/-- Step 1 of the blueprint proof of `existsAnnularSpokes_step4_sort`: parametrize the polygonal
boundary of the outer disk by a continuous period-one loop, injective on one
period. -/
private def polygonBoundaryIndex (B : PolygonalDisk) (t : ℝ) : Fin B.n :=
  ⟨⌊(B.n : ℝ) * t⌋₊ % B.n, Nat.mod_lt _ (by have := B.three_le; omega)⟩

private def polygonBoundaryBase (B : PolygonalDisk) (t : ℝ) : Pt :=
  AffineMap.lineMap (B.vertex (polygonBoundaryIndex B t))
    (B.vertex (finRotate B.n (polygonBoundaryIndex B t)))
    ((B.n : ℝ) * t - ⌊(B.n : ℝ) * t⌋₊)

private lemma polygonBoundaryIndex_on_halfOpen (B : PolygonalDisk) (i : Fin B.n) {t : ℝ}
    (hlo : (i : ℝ) / B.n ≤ t) (hhi : t < ((i : ℕ) + 1 : ℝ) / B.n) :
    polygonBoundaryIndex B t = i := by
  have hnN : 0 < B.n := by have := B.three_le; omega
  have hn : (0 : ℝ) < B.n := by exact_mod_cast hnN
  have ht0 : 0 ≤ (B.n : ℝ) * t := by
    have : 0 ≤ t := le_trans (div_nonneg (by positivity) hn.le) hlo
    positivity
  have hfloor : ⌊(B.n : ℝ) * t⌋₊ = i := by
    rw [Nat.floor_eq_iff ht0]
    simpa [mul_comm] using And.intro ((div_le_iff₀ hn).1 hlo) ((lt_div_iff₀ hn).1 hhi)
  apply Fin.ext
  simp [polygonBoundaryIndex, hfloor, Nat.mod_eq_of_lt i.isLt]

private lemma polygonBoundaryIndex_at_right (B : PolygonalDisk) (i : Fin B.n) :
    polygonBoundaryIndex B (((i : ℕ) + 1 : ℝ) / B.n) = finRotate B.n i := by
  have hnN : 0 < B.n := by have := B.three_le; omega
  have hn : (B.n : ℝ) ≠ 0 := by exact_mod_cast hnN.ne'
  apply Fin.ext
  simp only [polygonBoundaryIndex]
  rw [mul_div_cancel₀ _ hn]
  have hfloor : ⌊((i : ℕ) : ℝ) + 1⌋₊ = i.val + 1 := by
    rw [Nat.floor_eq_iff (by positivity)]
    norm_num
  rw [hfloor, finRotate_val']
  by_cases hlast : i.val + 1 = B.n
  · rw [if_pos hlast, hlast, Nat.mod_self]
  · rw [if_neg hlast, Nat.mod_eq_of_lt (by omega)]

private lemma polygonBoundaryBase_on_edge (B : PolygonalDisk) (i : Fin B.n) {t : ℝ}
    (ht : t ∈ Icc ((i : ℝ) / B.n) (((i : ℕ) + 1 : ℝ) / B.n)) :
    polygonBoundaryBase B t = AffineMap.lineMap (B.vertex i)
      (B.vertex (finRotate B.n i)) ((B.n : ℝ) * t - i) := by
  rcases lt_or_eq_of_le ht.2 with hhi | rfl
  · have hidx := polygonBoundaryIndex_on_halfOpen B i ht.1 hhi
    have hnN : 0 < B.n := by have := B.three_le; omega
    have hn : (0 : ℝ) < B.n := by exact_mod_cast hnN
    have ht0 : 0 ≤ (B.n : ℝ) * t := by
      have : 0 ≤ t := le_trans (div_nonneg (by positivity) hn.le) ht.1
      positivity
    have hfloor : ⌊(B.n : ℝ) * t⌋₊ = i := by
      rw [Nat.floor_eq_iff ht0]
      simpa [mul_comm] using And.intro ((div_le_iff₀ hn).1 ht.1) ((lt_div_iff₀ hn).1 hhi)
    simp [polygonBoundaryBase, hidx, hfloor]
  · have hnN : 0 < B.n := by have := B.three_le; omega
    have hn : (B.n : ℝ) ≠ 0 := by exact_mod_cast hnN.ne'
    have hmul : (B.n : ℝ) * (((i : ℕ) + 1 : ℝ) / B.n) = (i : ℕ) + 1 :=
      mul_div_cancel₀ _ hn
    rw [polygonBoundaryBase, polygonBoundaryIndex_at_right]
    rw [hmul]
    have hfloor : ⌊((i : ℕ) : ℝ) + 1⌋₊ = i.val + 1 := by
      rw [Nat.floor_eq_iff (by positivity)]
      norm_num
    rw [hfloor]
    simp

private lemma polygonBoundaryBase_continuousOn (B : PolygonalDisk) :
    ContinuousOn (polygonBoundaryBase B) (Icc 0 1) := by
  let C : Fin B.n → Set ℝ := fun i =>
    Icc ((i : ℝ) / B.n) (((i : ℕ) + 1 : ℝ) / B.n)
  have hcover : Icc (0 : ℝ) 1 = ⋃ i, C i := by
    apply Set.Subset.antisymm
    · intro t ht
      have hnN : 0 < B.n := by have := B.three_le; omega
      have hn : (0 : ℝ) < B.n := by exact_mod_cast hnN
      by_cases ht1 : t = 1
      · subst t
        let i : Fin B.n := ⟨B.n - 1, by omega⟩
        refine Set.mem_iUnion.2 ⟨i, ?_⟩
        change ((B.n - 1 : ℕ) : ℝ) / B.n ≤ 1 ∧
          1 ≤ (((B.n - 1 : ℕ) : ℝ) + 1) / B.n
        constructor
        · rw [div_le_one hn]
          exact_mod_cast Nat.sub_le B.n 1
        · rw [le_div_iff₀ hn]
          norm_num
          exact_mod_cast (Nat.sub_add_cancel hnN).ge
      have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
      have hnt0 : 0 ≤ (B.n : ℝ) * t := mul_nonneg hn.le ht.1
      have hfl := Nat.floor_le hnt0
      have hlt := Nat.lt_floor_add_one ((B.n : ℝ) * t)
      have hfloor_lt : ⌊(B.n : ℝ) * t⌋₊ < B.n := by
        rw [Nat.floor_lt hnt0]
        simpa using mul_lt_mul_of_pos_left htlt hn
      let i : Fin B.n := ⟨⌊(B.n : ℝ) * t⌋₊, hfloor_lt⟩
      refine Set.mem_iUnion.2 ⟨i, ?_⟩
      change (i : ℝ) / B.n ≤ t ∧ t ≤ ((i : ℕ) + 1 : ℝ) / B.n
      constructor
      · exact (div_le_iff₀ hn).2 (by simpa [i, mul_comm] using hfl)
      · exact (le_div_iff₀ hn).2 (by simpa [i, mul_comm, add_comm] using hlt.le)
    · rw [Set.iUnion_subset_iff]
      intro i t ht
      change 0 ≤ t ∧ t ≤ 1
      have hnN : 0 < B.n := by have := B.three_le; omega
      have hn : (0 : ℝ) < B.n := by exact_mod_cast hnN
      constructor
      · exact (div_nonneg (by positivity) hn.le).trans ht.1
      · calc
          t ≤ ((i : ℕ) + 1 : ℝ) / B.n := ht.2
          _ ≤ 1 := by rw [div_le_one hn]; exact_mod_cast i.isLt
  rw [hcover]
  refine (locallyFinite_of_finite C).continuousOn_iUnion (fun i => ?_) (fun i => ?_)
  · exact isClosed_Icc
  · apply ContinuousOn.congr
      (AffineMap.lineMap_continuous.comp
        (continuous_const.mul continuous_id |>.sub continuous_const)).continuousOn
    intro t ht
    exact polygonBoundaryBase_on_edge B i ht

set_option maxHeartbeats 800000 in
private lemma existsAnnularSpokes_step4_sort_step1_boundary_param (B : PolygonalDisk) :
    ∃ γ : ℝ → Pt, IsLoopParam (frontier B.carrier) γ := by
  let γ : ℝ → Pt := polygonBoundaryBase B ∘ Int.fract
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · apply (polygonBoundaryBase_continuousOn B).comp_fract''
    have hnN : 0 < B.n := by have := B.three_le; omega
    simp [polygonBoundaryBase, polygonBoundaryIndex]
  · intro t
    simp [γ, Function.comp_def, Int.fract_add_one]
  · intro s hs t ht hst
    have hγ (u : ℝ) (hu : u ∈ Ico (0 : ℝ) 1) : γ u = polygonBoundaryBase B u := by
      simp [γ, Function.comp_def, Int.fract_eq_self.2 hu]
    rw [hγ s hs, hγ t ht] at hst
    let i := polygonBoundaryIndex B s
    let j := polygonBoundaryIndex B t
    have hnN : 0 < B.n := by have := B.three_le; omega
    have hn : (0 : ℝ) < B.n := by exact_mod_cast hnN
    have hs0 : 0 ≤ (B.n : ℝ) * s := mul_nonneg hn.le hs.1
    have ht0 : 0 ≤ (B.n : ℝ) * t := mul_nonneg hn.le ht.1
    have hsi : ⌊(B.n : ℝ) * s⌋₊ < B.n := by
      rw [Nat.floor_lt hs0]
      simpa using (mul_lt_mul_of_pos_left hs.2 hn)
    have htj : ⌊(B.n : ℝ) * t⌋₊ < B.n := by
      rw [Nat.floor_lt ht0]
      simpa using (mul_lt_mul_of_pos_left ht.2 hn)
    have hi : i.val = ⌊(B.n : ℝ) * s⌋₊ := by
      simp [i, polygonBoundaryIndex, Nat.mod_eq_of_lt hsi]
    have hj : j.val = ⌊(B.n : ℝ) * t⌋₊ := by
      simp [j, polygonBoundaryIndex, Nat.mod_eq_of_lt htj]
    have hus : (B.n : ℝ) * s - i.val ∈ Ico (0 : ℝ) 1 := by
      rw [hi]
      exact ⟨sub_nonneg.2 (Nat.floor_le hs0), by
        have := Nat.lt_floor_add_one ((B.n : ℝ) * s)
        linarith⟩
    have hut : (B.n : ℝ) * t - j.val ∈ Ico (0 : ℝ) 1 := by
      rw [hj]
      exact ⟨sub_nonneg.2 (Nat.floor_le ht0), by
        have := Nat.lt_floor_add_one ((B.n : ℝ) * t)
        linarith⟩
    have hBs : polygonBoundaryBase B s = AffineMap.lineMap (B.vertex i)
        (B.vertex (finRotate B.n i)) ((B.n : ℝ) * s - i.val) := by
      simp [polygonBoundaryBase, i, hi]
    have hBt : polygonBoundaryBase B t = AffineMap.lineMap (B.vertex j)
        (B.vertex (finRotate B.n j)) ((B.n : ℝ) * t - j.val) := by
      simp [polygonBoundaryBase, j, hj]
    rw [hBs, hBt] at hst
    by_cases hij : i = j
    · rw [hij] at hst
      have hne : B.vertex j ≠ B.vertex (finRotate B.n j) := pd_vertex_ne_next B j
      have hu := AffineMap.lineMap_injective ℝ hne hst
      nlinarith
    · have hsseg : AffineMap.lineMap (B.vertex i) (B.vertex (finRotate B.n i))
          ((B.n : ℝ) * s - i.val) ∈ segment ℝ (B.vertex i) (B.vertex (finRotate B.n i)) := by
        rw [segment_eq_image_lineMap]
        exact ⟨_, ⟨hus.1, hus.2.le⟩, rfl⟩
      have htseg : AffineMap.lineMap (B.vertex j) (B.vertex (finRotate B.n j))
          ((B.n : ℝ) * t - j.val) ∈ segment ℝ (B.vertex j) (B.vertex (finRotate B.n j)) := by
        rw [segment_eq_image_lineMap]
        exact ⟨_, ⟨hut.1, hut.2.le⟩, rfl⟩
      have hends := B.simple i j hij ⟨hsseg, hst ▸ htseg⟩
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hends
      have hne_i : B.vertex i ≠ B.vertex (finRotate B.n i) := pd_vertex_ne_next B i
      have hne_j : B.vertex j ≠ B.vertex (finRotate B.n j) := pd_vertex_ne_next B j
      have hleft_i : AffineMap.lineMap (B.vertex i) (B.vertex (finRotate B.n i))
          ((B.n : ℝ) * s - i.val) = B.vertex i := by
        rcases hends.1 with h | h
        · exact h
        · rw [AffineMap.lineMap_eq_right_iff] at h
          exact False.elim ((ne_of_lt hus.2) (h.resolve_left hne_i))
      have hleft_j : AffineMap.lineMap (B.vertex j) (B.vertex (finRotate B.n j))
          ((B.n : ℝ) * t - j.val) = B.vertex j := by
        rcases hends.2 with h | h
        · exact hst.symm.trans h
        · have h' := hst.symm.trans h
          rw [AffineMap.lineMap_eq_right_iff] at h'
          exact False.elim ((ne_of_lt hut.2) (h'.resolve_left hne_j))
      exact (hij (B.vertex_injective (hleft_i.symm.trans (hst.trans hleft_j)))).elim
  · rw [B.frontier_eq]
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have hfract : Int.fract t = t := Int.fract_eq_self.2 ht
      change polygonBoundaryBase B (Int.fract t) ∈ _
      rw [hfract]
      let i := polygonBoundaryIndex B t
      have hnN : 0 < B.n := by have := B.three_le; omega
      have hn : (0 : ℝ) < B.n := by exact_mod_cast hnN
      have ht0 : 0 ≤ (B.n : ℝ) * t := mul_nonneg hn.le ht.1
      have hfi : ⌊(B.n : ℝ) * t⌋₊ < B.n := by
        rw [Nat.floor_lt ht0]
        simpa using mul_lt_mul_of_pos_left ht.2 hn
      have hi : i.val = ⌊(B.n : ℝ) * t⌋₊ := by
        simp [i, polygonBoundaryIndex, Nat.mod_eq_of_lt hfi]
      apply Set.mem_iUnion.2
      refine ⟨i, ?_⟩
      have hbase : polygonBoundaryBase B t = AffineMap.lineMap (B.vertex i)
          (B.vertex (finRotate B.n i)) ((B.n : ℝ) * t - i.val) := by
        simp [polygonBoundaryBase, i, hi]
      rw [hbase, segment_eq_image_lineMap]
      refine ⟨(B.n : ℝ) * t - i.val, ?_, rfl⟩
      rw [hi]
      refine ⟨sub_nonneg.2 (Nat.floor_le ht0), ?_⟩
      have := Nat.lt_floor_add_one ((B.n : ℝ) * t)
      linarith
    · rw [Set.mem_iUnion]
      rintro ⟨i, hx⟩
      rw [segment_eq_image_lineMap] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      by_cases hu1 : u = 1
      · let j := finRotate B.n i
        refine ⟨(j : ℝ) / B.n, ?_, ?_⟩
        · have hnN : 0 < B.n := by have := B.three_le; omega
          have hn : (0 : ℝ) < B.n := by exact_mod_cast hnN
          exact ⟨div_nonneg (by positivity) hn.le, (div_lt_one hn).2 (by exact_mod_cast j.isLt)⟩
        · have hjmem : (j : ℝ) / B.n ∈
              Icc ((j : ℝ) / B.n) (((j : ℕ) + 1 : ℝ) / B.n) := by
            constructor
            · rfl
            · have hnN : 0 < B.n := by have := B.three_le; omega
              exact div_le_div_of_nonneg_right (by norm_num) (by exact_mod_cast hnN.le)
          have hnN : 0 < B.n := by have := B.three_le; omega
          have hn : (0 : ℝ) < B.n := by exact_mod_cast hnN
          simp only [γ, Function.comp_apply]
          rw [Int.fract_eq_self.2 ⟨(div_nonneg (by positivity) hn.le).trans hjmem.1,
            (div_lt_one hn).2 (by exact_mod_cast j.isLt)⟩]
          rw [polygonBoundaryBase_on_edge B j hjmem, hu1]
          rw [mul_div_cancel₀ _ hn.ne']
          simp [j]
      · let t := ((i : ℝ) + u) / B.n
        have hnN : 0 < B.n := by have := B.three_le; omega
        have hn : (0 : ℝ) < B.n := by exact_mod_cast hnN
        have htmem : t ∈ Icc ((i : ℝ) / B.n) (((i : ℕ) + 1 : ℝ) / B.n) := by
          dsimp [t]
          constructor <;> rw [div_le_div_iff_of_pos_right hn]
          · linarith [hu.1]
          · norm_num at hu1 ⊢
            linarith [hu.2]
        have htIco : t ∈ Ico (0 : ℝ) 1 := by
          refine ⟨(div_nonneg (by positivity) hn.le).trans htmem.1, ?_⟩
          rw [div_lt_one hn]
          have hi : ((i : ℕ) : ℝ) + 1 ≤ B.n := by exact_mod_cast i.isLt
          have hu' : u < 1 := lt_of_le_of_ne hu.2 hu1
          linarith
        refine ⟨t, htIco, ?_⟩
        simp only [γ, Function.comp_apply]
        rw [Int.fract_eq_self.2 htIco, polygonBoundaryBase_on_edge B i htmem]
        congr 1
        dsimp [t]
        rw [mul_div_cancel₀ _ hn.ne']
        ring

/-- Step 2 of the blueprint proof of `existsAnnularSpokes_step4_sort`: choose a cyclic starting
point and re-index finitely many distinct points in the image of a simple loop
in traversal order. -/
private lemma existsAnnularSpokes_step4_sort_step2_reindex (γ : ℝ → Pt) {k : ℕ}
    (x : Fin k → Pt) {K : Set Pt} (hγ : IsLoopParam K γ)
    (hx : ∀ i, x i ∈ γ '' Ico (0 : ℝ) 1) (hxi : Function.Injective x) :
    ∃ σ : Equiv.Perm (Fin k), PointsInOrder γ (x ∘ σ) := by
  have _ := hγ
  have Ht : ∀ i, ∃ t ∈ Ico (0:ℝ) 1, γ t = x i := by
    intro i
    rcases hx i with ⟨t, ht, H⟩
    exact ⟨t, ht, H⟩
  choose t ht hEq using Ht
  have HtInj : Function.Injective t := by
    intro i j hij
    have H : x i = x j := by
      rw [← hEq i, ← hEq j, hij]
    exact hxi H
  let s := Finset.image t Finset.univ
  have hcard : s.card = k := by
    rw [Finset.card_image_of_injective Finset.univ HtInj, Finset.card_univ, Fintype.card_fin]
  let e := Finset.orderIsoOfFin s hcard
  let t_equiv : Fin k ≃ s := Equiv.ofBijective (fun i => ⟨t i, by simp [s]⟩) (by
    constructor
    · intro i j hij
      apply HtInj
      exact Subtype.ext_iff.mp hij
    · intro ⟨y, hy⟩
      simp [s] at hy
      rcases hy with ⟨i, hi⟩
      use i
      ext
      exact hi
  )
  let σ := e.toEquiv.trans t_equiv.symm
  use σ
  dsimp [PointsInOrder]
  use (t ∘ σ)
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have h1 : e i < e j := e.strictMono hij
    have h2 : (e i).val < (e j).val := h1
    have h3 : t (σ i) = (e i).val := by
      dsimp [σ]
      have h4 := t_equiv.apply_symm_apply (e i)
      exact congrArg Subtype.val h4
    have h5 : t (σ j) = (e j).val := by
      dsimp [σ]
      have h6 := t_equiv.apply_symm_apply (e j)
      exact congrArg Subtype.val h6
    dsimp
    rw [h3, h5]
    exact h2
  · intro i j
    have h_tj : (t ∘ σ) j < 1 := (ht (σ j)).2
    have h_ti : 0 ≤ (t ∘ σ) i := (ht (σ i)).1
    linarith
  · intro i
    dsimp
    rw [hEq]

/-- Step 4 of the blueprint proof of `existsAnnularSpokes`: the stops of the spokes are distinct
points of the polygonal cycle `∂H`, so after a re-indexing they appear in cyclic order along a
parametrization of that cycle.  (Blueprint: "The index `j` of the `j`th cut disk is matched with
the ideal sector `T_j` only in the next lemma"; here any cyclic labelling will do.) -/
private lemma existsAnnularSpokes_step4_sort (B : PolygonalDisk) {k : ℕ} (x : Fin k → Pt)
    (hx : ∀ i, x i ∈ frontier B.carrier) (hxi : Function.Injective x) :
    ∃ γ : ℝ → Pt, ∃ σ : Equiv.Perm (Fin k), IsLoopParam (frontier B.carrier) γ ∧
      PointsInOrder γ (x ∘ σ) := by
  obtain ⟨γ, hγ⟩ := existsAnnularSpokes_step4_sort_step1_boundary_param B
  have himage : ∀ i, x i ∈ γ '' Ico (0 : ℝ) 1 := by
    intro i
    rw [hγ.2.2.2]
    exact hx i
  obtain ⟨σ, hσ⟩ := existsAnnularSpokes_step4_sort_step2_reindex γ x
    hγ himage hxi
  exact ⟨γ, σ, hγ, hσ⟩

/-- Step 5 of the blueprint proof of `existsAnnularSpokes_step5_crosscuts`: the disjointness
of the crosscuts forces both endpoint maps to be injective. -/
private lemma existsAnnularSpokes_step5_crosscuts_step1_endpoints (A C : PolygonalDisk)
    {k : ℕ} (α : Fin k → PolyArc)
    (hC : ∀ j, (α j).carrier ∩ frontier C.carrier = {(α j).start})
    (hA : ∀ j, (α j).carrier ∩ frontier A.carrier = {(α j).stop})
    (hdisj : ∀ i j, i ≠ j → Disjoint (α i).carrier (α j).carrier) :
    Function.Injective (fun j => (α j).start) ∧
      Function.Injective (fun j => (α j).stop) := by
  have hstart : ∀ j, (α j).start ∈ (α j).carrier ∩ frontier C.carrier := by
    intro j
    rw [hC j]
    exact Set.mem_singleton _
  have hstop : ∀ j, (α j).stop ∈ (α j).carrier ∩ frontier A.carrier := by
    intro j
    rw [hA j]
    exact Set.mem_singleton _
  constructor
  · intro i j hij
    change (α i).start = (α j).start at hij
    by_contra hne
    exact Set.disjoint_left.1 (hdisj i j hne) (hstart i).1 (by
      rw [hij]
      exact (hstart j).1)
  · intro i j hij
    change (α i).stop = (α j).stop at hij
    by_contra hne
    exact Set.disjoint_left.1 (hdisj i j hne) (hstop i).1 (by
      rw [hij]
      exact (hstop j).1)

/-- Step 5 of the blueprint proof of `existsAnnularSpokes_step5_crosscuts`: choose the inner
boundary parametrization with the orientation freely homotopic to the given outer one. -/
private lemma existsAnnularSpokes_step5_crosscuts_step2_boundary_homotopy (A C : PolygonalDisk)
    (hCA : C.carrier ⊆ interior A.carrier) {γo : ℝ → Pt}
    (hγo : IsLoopParam (frontier A.carrier) γo) :
    ∃ γi : ℝ → Pt, IsLoopParam (frontier C.carrier) γi ∧
      LoopsHomotopicIn (A.carrier \ interior C.carrier) γo γi := by
  sorry

/-- Step 1 of the blueprint proof of `existsAnnularSpokes_step5_crosscuts_step3_order_transfer`:
cyclic order is preserved for 3 crosscuts. -/
private lemma existsAnnularSpokes_step5_crosscuts_step3_order_transfer_step1_k3
    (A C : PolygonalDisk)
    (hCA : C.carrier ⊆ interior A.carrier) (α : Fin 3 → PolyArc)
    (hin : ∀ j, (α j).carrier ⊆ A.carrier \ interior C.carrier)
    (hC : ∀ j, (α j).carrier ∩ frontier C.carrier = {(α j).start})
    (hA : ∀ j, (α j).carrier ∩ frontier A.carrier = {(α j).stop})
    (hdisj : ∀ i j, i ≠ j → Disjoint (α i).carrier (α j).carrier)
    (hstart : Function.Injective (fun j => (α j).start))
    (hstop : Function.Injective (fun j => (α j).stop))
    {γo γi : ℝ → Pt} (hγo : IsLoopParam (frontier A.carrier) γo)
    (hγi : IsLoopParam (frontier C.carrier) γi)
    (hhom : LoopsHomotopicIn (A.carrier \ interior C.carrier) γo γi)
    (hord : PointsInOrder γo fun j => (α j).stop) :
    PointsInOrder γi fun j => (α j).start := by
  sorry

/-- Step 2 of the blueprint proof of `existsAnnularSpokes_step5_crosscuts_step3_order_transfer`:
cyclic order is preserved if it is preserved for any 3 points. -/
private lemma existsAnnularSpokes_step5_crosscuts_step3_order_transfer_step2_reduction
    {k : ℕ} (x : Fin k → Pt) (γ : ℝ → Pt) {K : Set Pt} (hγ : IsLoopParam K γ) (hx_in : ∀ i, x i ∈ K)
    (hx_inj : Function.Injective x)
    (h3 : ∀ f : Fin 3 ↪ Fin k, StrictMono f → PointsInOrder γ (x ∘ f)) :
    PointsInOrder γ x := by
  sorry

/-- Step 3 of the blueprint proof of `existsAnnularSpokes_step5_crosscuts_step3_order_transfer`:
cyclic order is trivially preserved for `k < 3` points. -/
private lemma existsAnnularSpokes_step5_crosscuts_step3_order_transfer_step3_small_k
    {k : ℕ} (hk : k < 3) (x : Fin k → Pt) (γ : ℝ → Pt) {K : Set Pt} (hγ : IsLoopParam K γ)
    (hx_in : ∀ i, x i ∈ K) (hx_inj : Function.Injective x) :
    PointsInOrder γ x := by
  sorry

/-- Step 4 of the blueprint proof of `existsAnnularSpokes_step5_crosscuts_step3_order_transfer`:
a subset of points in cyclic order is in cyclic order. -/
private lemma existsAnnularSpokes_step5_crosscuts_step3_order_transfer_step4_sub_order
    {k : ℕ} (x : Fin k → Pt) (γ : ℝ → Pt) (hord : PointsInOrder γ x)
    {m : ℕ} (f : Fin m ↪ Fin k) (hf : StrictMono f) :
    PointsInOrder γ (x ∘ f) := by
  sorry

/-- Step 5 of the blueprint proof of `existsAnnularSpokes_step5_crosscuts`: disjoint crosscuts
in an annulus transfer the cyclic order of their outer endpoints to their inner endpoints. -/
private lemma existsAnnularSpokes_step5_crosscuts_step3_order_transfer (A C : PolygonalDisk)
    (hCA : C.carrier ⊆ interior A.carrier) {k : ℕ} (α : Fin k → PolyArc)
    (hin : ∀ j, (α j).carrier ⊆ A.carrier \ interior C.carrier)
    (hC : ∀ j, (α j).carrier ∩ frontier C.carrier = {(α j).start})
    (hA : ∀ j, (α j).carrier ∩ frontier A.carrier = {(α j).stop})
    (hdisj : ∀ i j, i ≠ j → Disjoint (α i).carrier (α j).carrier)
    (hstart : Function.Injective (fun j => (α j).start))
    (hstop : Function.Injective (fun j => (α j).stop))
    {γo γi : ℝ → Pt} (hγo : IsLoopParam (frontier A.carrier) γo)
    (hγi : IsLoopParam (frontier C.carrier) γi)
    (hhom : LoopsHomotopicIn (A.carrier \ interior C.carrier) γo γi)
    (hord : PointsInOrder γo fun j => (α j).stop) :
    PointsInOrder γi fun j => (α j).start := by
  by_cases hk : k < 3
  · apply existsAnnularSpokes_step5_crosscuts_step3_order_transfer_step3_small_k hk _ _ hγi
    · intro i
      have h : (α i).start ∈ (α i).carrier ∩ frontier C.carrier := by
        rw [hC i]
        exact Set.mem_singleton _
      exact h.2
    · exact hstart
  · apply existsAnnularSpokes_step5_crosscuts_step3_order_transfer_step2_reduction _ _ hγi
    · intro i
      have h : (α i).start ∈ (α i).carrier ∩ frontier C.carrier := by
        rw [hC i]
        exact Set.mem_singleton _
      exact h.2
    · exact hstart
    · intro f hf
      have hord_sub := existsAnnularSpokes_step5_crosscuts_step3_order_transfer_step4_sub_order
        _ _ hord f hf
      let α' : Fin 3 → PolyArc := α ∘ f
      have hin' : ∀ j, (α' j).carrier ⊆ A.carrier \ interior C.carrier := fun j => hin (f j)
      have hC' : ∀ j, (α' j).carrier ∩ frontier C.carrier = {(α' j).start} := fun j => hC (f j)
      have hA' : ∀ j, (α' j).carrier ∩ frontier A.carrier = {(α' j).stop} := fun j => hA (f j)
      have hdisj' : ∀ i j, i ≠ j → Disjoint (α' i).carrier (α' j).carrier := by
        intro i j hij
        exact hdisj (f i) (f j) (f.injective.ne hij)
      have hstart' : Function.Injective (fun j => (α' j).start) := hstart.comp f.injective
      have hstop' : Function.Injective (fun j => (α' j).stop) := hstop.comp f.injective
      exact existsAnnularSpokes_step5_crosscuts_step3_order_transfer_step1_k3 A C hCA α' hin'
        hC' hA' hdisj' hstart' hstop' hγo hγi hhom hord_sub

/-- Step 5 of the blueprint proof of `existsAnnularSpokes`: "The separated tubes give disjoint
arcs and distinct endpoints.  Disjoint arcs joining the two boundary components of an annulus
have compatible cyclic endpoint order."  In the polygonal annulus `A \ int C`, if pairwise
disjoint polygonal arcs, each meeting `∂C` only at its start and `∂A` only at its stop, have
their stops in cyclic order along a parametrization `γo` of `∂A`, then their starts are in the
same cyclic order along a parametrization of `∂C` freely homotopic to `γo` in the annulus. -/
private lemma existsAnnularSpokes_step5_crosscuts (A C : PolygonalDisk)
    (hCA : C.carrier ⊆ interior A.carrier) {k : ℕ} (α : Fin k → PolyArc)
    (hin : ∀ j, (α j).carrier ⊆ A.carrier \ interior C.carrier)
    (hC : ∀ j, (α j).carrier ∩ frontier C.carrier = {(α j).start})
    (hA : ∀ j, (α j).carrier ∩ frontier A.carrier = {(α j).stop})
    (hdisj : ∀ i j, i ≠ j → Disjoint (α i).carrier (α j).carrier) {γo : ℝ → Pt}
    (hγo : IsLoopParam (frontier A.carrier) γo)
    (hord : PointsInOrder γo fun j => (α j).stop) :
    MatchingCyclicOrder (A.carrier \ interior C.carrier) (frontier A.carrier)
      (frontier C.carrier) (fun j => (α j).stop) (fun j => (α j).start) := by
  obtain ⟨γi, hγi, hhom⟩ :=
    existsAnnularSpokes_step5_crosscuts_step2_boundary_homotopy A C hCA hγo
  obtain ⟨hstart, hstop⟩ :=
    existsAnnularSpokes_step5_crosscuts_step1_endpoints A C α hC hA hdisj
  have hinner := existsAnnularSpokes_step5_crosscuts_step3_order_transfer A C hCA α hin hC hA
    hdisj hstart hstop hγo hγi hhom hord
  exact ⟨γo, γi, hγo, hγi, hhom, hord, hinner⟩

/-- Step 1 of the blueprint proof of `existsAnnularSpokes_step6_cut`: "Cutting a polygonal
annulus along such `4N` arcs gives `4N` disks, one between each successive pair; this is a
direct polygonal Jordan argument, or the elementary polygonal annulus theorem ... Their inner
boundary arcs have distinct endpoints and positive length."  Planar form: removing `k ≥ 2`
pairwise disjoint simple polygonal cross-cuts of the annulus `A \ int C`, in matching cyclic
order, from the open annulus `int A \ C` leaves `k` connected open regions; the `j`-th has the
cross-cuts `j` and `j + 1` in its closure, its closure has connected complement, and its
closure meets `C` in a connected set with more than one point. -/
private lemma existsAnnularSpokes_step6_cut_step1_regions (A C : PolygonalDisk)
    (hCA : C.carrier ⊆ interior A.carrier) {k : ℕ} (hk : 2 ≤ k) (α : Fin k → PolyArc)
    (hsimple : ∀ j, (α j).IsSimple)
    (hin : ∀ j, (α j).carrier ⊆ A.carrier \ interior C.carrier)
    (hC : ∀ j, (α j).carrier ∩ frontier C.carrier = {(α j).start})
    (hA : ∀ j, (α j).carrier ∩ frontier A.carrier = {(α j).stop})
    (hdisj : ∀ i j, i ≠ j → Disjoint (α i).carrier (α j).carrier)
    (horder : MatchingCyclicOrder (A.carrier \ interior C.carrier) (frontier A.carrier)
      (frontier C.carrier) (fun j => (α j).stop) (fun j => (α j).start)) :
    ∃ W : Fin k → Set Pt, (∀ j, IsOpen (W j)) ∧ (∀ j, IsConnected (W j)) ∧
      (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
      ⋃ j, W j = interior A.carrier \ (C.carrier ∪ ⋃ j, (α j).carrier) ∧
      (∀ j, (α j).carrier ⊆ closure (W j) ∧ (α (finRotate k j)).carrier ⊆ closure (W j)) ∧
      (∀ j, IsConnected (closure (W j))ᶜ) ∧
      (∀ j, IsConnected (closure (W j) ∩ C.carrier) ∧
        (closure (W j) ∩ C.carrier).Nontrivial) := by
  sorry

/-- Step 2a of the blueprint proof of `existsAnnularSpokes_step6_cut_step2_faces`: Uniqueness from topological connectedness. -/
private lemma existsAnnularSpokes_step6_cut_step2_faces_unique
    {C : Set Pt} {k : ℕ} (W : Fin k → Set Pt)
    (hCne : C.Nonempty) (hCconn : IsPreconnected C)
    (hWo : ∀ j, IsOpen (W j))
    (hWd : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hCsub : C ⊆ ⋃ j, W j) : ∃! j, C ⊆ W j := by
  have : ∃ j, (C ∩ W j).Nonempty := by
    by_contra h
    push_neg at h
    have hCemp : C = ∅ := by
      calc C = C ∩ ⋃ j, W j := by rw [inter_eq_left.mpr hCsub]
           _ = ⋃ j, C ∩ W j := inter_iUnion _ _
           _ = ⋃ j, (∅ : Set Pt) := by
             congr 1; funext j; exact h j
           _ = ∅ := iUnion_empty
    exact hCne.ne_empty hCemp
  rcases this with ⟨j, hj⟩
  use j
  constructor
  · have hj2 : C ⊆ W j ∪ ⋃ (i : Fin k) (_ : i ≠ j), W i := by
      intro x hx
      have hxu := hCsub hx
      simp only [mem_iUnion] at hxu ⊢
      rcases hxu with ⟨i, hi⟩
      by_cases hij : i = j
      · exact Or.inl (hij ▸ hi)
      · right
        simp only [mem_iUnion, exists_prop]
        exact ⟨i, hij, hi⟩
    have hd : Disjoint (W j) (⋃ (i : Fin k) (_ : i ≠ j), W i) := by
      simp only [disjoint_iUnion_right]
      intro i hij
      exact hWd j i hij.symm
    have hWo_union : IsOpen (⋃ (i : Fin k) (_ : i ≠ j), W i) := by
      apply isOpen_biUnion
      intro i _
      exact hWo i
    exact hCconn.subset_left_of_subset_union (hWo j) hWo_union hd hj2 hj
  · intro i hi
    by_contra hij
    have hd := hWd i j hij
    have hx : hj.some ∈ W i ∩ W j := ⟨hi hj.some_mem.1, hj.some_mem.2⟩
    have hd_emp : W i ∩ W j = ∅ := disjoint_iff_inter_eq_empty.mp hd
    rw [hd_emp] at hx
    exact hx

/-- Step 2b of the blueprint proof of `existsAnnularSpokes_step6_cut_step2_faces`: Connectedness of interior of tile. -/
private lemma existsAnnularSpokes_step6_cut_step2_faces_conn (A : PlacedTile P) :
    IsPreconnected (interior A.carrier) := by sorry

/-- Step 2c of the blueprint proof of `existsAnnularSpokes_step6_cut_step2_faces`: Nonemptiness of interior of tile. -/
private lemma existsAnnularSpokes_step6_cut_step2_faces_ne (A : PlacedTile P) :
    (interior A.carrier).Nonempty := by sorry

/-- Step 2d of the blueprint proof of `existsAnnularSpokes_step6_cut_step2_faces`: Sub-H. -/
private lemma existsAnnularSpokes_step6_cut_step2_faces_sub_H {S : Set (PlacedTile P)} (L H : FaceGroup S) {A : PlacedTile P}
    (hA : A ∈ H.faces) : interior A.carrier ⊆ interior H.carrier := by sorry

/-- Step 2e of the blueprint proof of `existsAnnularSpokes_step6_cut_step2_faces`: Avoid. -/
private lemma existsAnnularSpokes_step6_cut_step2_faces_sub_avoid (S : Patch P) (L H : FaceGroup S.tiles)
    {k : ℕ} (α : Fin k → PolyArc)
    (hskel : ∀ j, (α j).IsSkeletal S.tiles)
    {A : PlacedTile P} (hA : A ∈ H.faces) (hAL : A ∉ L.faces) :
    Disjoint (interior A.carrier)
      (L.carrier ∪ ⋃ j, (α j).carrier) := by sorry

/-- Step 2 of the blueprint proof of `existsAnnularSpokes_step6_cut`: "All cuts use original
edges, so the disks are unions of whole original faces."  The interior of a face of `H` that is
not a face of `L` avoids `L` and the skeletal cuts, so it lies in exactly one of the regions of
the cut annulus. -/
private lemma existsAnnularSpokes_step6_cut_step2_faces (S : Patch P) (L H : FaceGroup S.tiles)
    {k : ℕ} (α : Fin k → PolyArc) (hskel : ∀ j, (α j).IsSkeletal S.tiles)
    (W : Fin k → Set Pt) (hWo : ∀ j, IsOpen (W j))
    (hWd : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hWU : ⋃ j, W j = interior H.carrier \ (L.carrier ∪ ⋃ j, (α j).carrier))
    {A : PlacedTile P} (hA : A ∈ H.faces) (hAL : A ∉ L.faces) :
    ∃! j, interior A.carrier ⊆ W j := by
  have hint_conn := existsAnnularSpokes_step6_cut_step2_faces_conn A
  have hint_ne := existsAnnularSpokes_step6_cut_step2_faces_ne A
  have hsub_H := existsAnnularSpokes_step6_cut_step2_faces_sub_H L H hA
  have havoid := existsAnnularSpokes_step6_cut_step2_faces_sub_avoid S L H α hskel hA hAL
  have hsub : interior A.carrier ⊆ ⋃ j, W j := by
    rw [hWU, subset_diff]
    exact ⟨hsub_H, havoid⟩
  exact existsAnnularSpokes_step6_cut_step2_faces_unique W hint_ne hint_conn hWo hWd hsub

/-- Step 3 of the blueprint proof of `existsAnnularSpokes_step6_cut`: "the disks are unions of
whole original faces" -- the closure of each region of the cut annulus is the union of the
faces of `H`, not in `L`, whose interiors it contains. -/
private lemma existsAnnularSpokes_step6_cut_step3_closure (S : Patch P)
    (L H : FaceGroup S.tiles) {k : ℕ} (α : Fin k → PolyArc)
    (hskel : ∀ j, (α j).IsSkeletal S.tiles) (W : Fin k → Set Pt) (hWo : ∀ j, IsOpen (W j))
    (hWd : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hWU : ⋃ j, W j = interior H.carrier \ (L.carrier ∪ ⋃ j, (α j).carrier)) (j : Fin k) :
    closure (W j) = support {A | A ∈ H.faces ∧ A ∉ L.faces ∧ interior A.carrier ⊆ W j} := by
  sorry

/-- Step 6 of the blueprint proof of `existsAnnularSpokes`: "Cutting a polygonal annulus along
such `4N` arcs gives `4N` disks, one between each successive pair ... All cuts use original
edges, so the disks are unions of whole original faces.  Their inner boundary arcs have distinct
endpoints and positive length.  Their face-dual graphs are connected by the generic-path
argument used in Lemma `lem:regular-grouping`."  Given `4N` spokes with all the spoke
properties, the pieces exist (each a `FaceGroup`, through `polygonalJordanBoundary`). -/
private lemma existsAnnularSpokes_step6_cut (S : Patch P) (hsts : SideToSideSet S.tiles)
    (L H : FaceGroup S.tiles) (hLH : L.carrier ⊆ interior H.carrier)
    (hHS : H.carrier ⊆ interior (support S.tiles)) {N : ℕ} (hN : 1 ≤ N)
    (α : Fin (4 * N) → PolyArc) (hsimple : ∀ j, (α j).IsSimple)
    (hskel : ∀ j, (α j).IsSkeletal S.tiles)
    (hin : ∀ j, (α j).carrier ⊆ H.carrier \ interior L.carrier)
    (hmL : ∀ j, (α j).carrier ∩ frontier L.carrier = {(α j).start})
    (hmH : ∀ j, (α j).carrier ∩ frontier H.carrier = {(α j).stop})
    (hdisj : ∀ i j, i ≠ j → Disjoint (α i).carrier (α j).carrier)
    (horder : MatchingCyclicOrder (H.carrier \ interior L.carrier) (frontier H.carrier)
      (frontier L.carrier) (fun j => (α j).stop) (fun j => (α j).start)) :
    ∃ T : SpokeSystem S.tiles L H N, T.spoke = α := by
  classical
  obtain ⟨W, hWo, hWc, hWd, hWU, hWb, hWco, hWct⟩ :=
    existsAnnularSpokes_step6_cut_step1_regions H.disk L.disk hLH (by omega) α hsimple hin hmL
      hmH hdisj horder
  set G : Fin (4 * N) → Set (PlacedTile P) :=
    fun j => {A | A ∈ H.faces ∧ A ∉ L.faces ∧ interior A.carrier ⊆ W j}
  have hcl : ∀ j, closure (W j) = support (G j) := fun j =>
    existsAnnularSpokes_step6_cut_step3_closure S L H α hskel W hWo hWd hWU j
  have hGS : ∀ j, G j ⊆ S.tiles := fun j _ hA => H.faces_sub hA.1
  have hex : ∀ j, ∃ F : FaceGroup S.tiles, F.faces = G j := by
    intro j
    refine polygonalJordanBoundary S.tiles S.disjoint hsts (G j) (hGS j)
      (S.finite.subset (hGS j)) ?_ ?_ ?_ ?_
    · obtain ⟨x, hx⟩ := (hWc j).nonempty
      have hx' : x ∈ support (G j) := by
        rw [← hcl j]
        exact subset_closure hx
      obtain ⟨A, hA, -⟩ := mem_support_iff'.1 hx'
      exact ⟨A, hA⟩
    · intro x hx
      obtain ⟨A, hA, hxA⟩ := mem_support_iff'.1 hx
      apply hHS
      show x ∈ H.disk.carrier
      rw [H.carrier_eq]
      exact mem_support_iff'.2 ⟨A, hA.1, hxA⟩
    · rw [← hcl j]
      exact (hWc j).subset_closure (interior_maximal subset_closure (hWo j)) interior_subset
    · rw [← hcl j]
      exact hWco j
  choose F hF using hex
  have hcar : ∀ j, (F j).carrier = closure (W j) := by
    intro j
    show (F j).disk.carrier = _
    rw [(F j).carrier_eq, hF j, hcl j]
  refine ⟨
    { spoke := α
      simple := hsimple
      skeletal := hskel
      in_annulus := hin
      meets_L := hmL
      meets_H := hmH
      disjoint := hdisj
      order := horder
      piece := F
      piece_partition := ?_
      piece_sub := ?_
      piece_between := ?_
      contact_connected := ?_
      contact_nondegenerate := ?_ }, rfl⟩
  · intro A _
    simp only [hF]
    constructor
    · rintro ⟨hAH, hAL⟩
      obtain ⟨j, hj, huniq⟩ :=
        existsAnnularSpokes_step6_cut_step2_faces S L H α hskel W hWo hWd hWU hAH hAL
      exact ⟨j, ⟨hAH, hAL, hj⟩, fun i hi => huniq i hi.2.2⟩
    · rintro ⟨j, hj, -⟩
      exact ⟨hj.1, hj.2.1⟩
  · intro j A hA
    rw [hF j] at hA
    exact ⟨hA.1, hA.2.1⟩
  · intro j
    rw [hcar j]
    exact hWb j
  · intro j
    rw [hcar j]
    exact (hWct j).1
  · intro j
    rw [hcar j]
    exact (hWct j).2

/-- `lem:annular-spokes`: for `N ≥ 2` and `R` large compared with `D`, any
inside-anchored `L` and outside-anchored `H` as above admit `4N` disjoint
simple skeletal spokes in matching cyclic order, cutting the annulus into `4N`
polygonal disks of complete faces with connected duals, each sharing one
connected nondegenerate arc with `∂L`. -/
theorem existsAnnularSpokes (M : MeshConstants P) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (S : Patch P) (Ω : PolygonalDisk), support S.tiles = Ω.carrier →
        SideToSideSet S.tiles → ∀ (c : Pt) (N : ℕ) (R : ℝ), 2 ≤ N → C₀ * M.D ≤ R →
        square c ((N : ℝ) * R / 2 + R) + Binf (10 * M.D) ⊆ interior Ω.carrier →
        ∀ L H : FaceGroup S.tiles,
          square c ((N : ℝ) * R / 2) ⊆ L.carrier →
          L.carrier ⊆ square c ((N : ℝ) * R / 2) + Binf M.D →
          L.InsideAnchored (square c ((N : ℝ) * R / 2)) →
          square c ((N : ℝ) * R / 2 + R) + Binf (2 * M.D) ⊆ H.carrier →
          H.carrier ⊆ square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D) →
          H.OutsideAnchored (square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D)) →
          Nonempty (SpokeSystem S.tiles L H N) := by
  have hD := M.D_pos
  refine ⟨100, by norm_num, ?_⟩
  intro S Ω hcov hsts c N R hN hR hΩ L H hL hLu _ hHl hHu _
  have hR0 : 0 < R := by linarith
  have hb : 0 ≤ (N : ℝ) * R / 2 + R :=
    add_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg N) hR0.le) zero_le_two) hR0.le
  have hnest1 : square c ((N : ℝ) * R / 2) + Binf M.D ⊆
      interior (square c ((N : ℝ) * R / 2 + R) + Binf (2 * M.D)) :=
    existsAnnularSpokes_step1_nest c (by linarith) hb (by linarith)
  have hnest2 : square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D) ⊆
      interior (square c ((N : ℝ) * R / 2 + R) + Binf (10 * M.D)) :=
    existsAnnularSpokes_step1_nest c (by linarith) hb (by linarith)
  have hLH : L.carrier ⊆ interior H.carrier := hLu.trans (hnest1.trans (interior_mono hHl))
  have hHS : H.carrier ⊆ interior (support S.tiles) := by
    rw [hcov]
    exact hHu.trans (hnest2.trans ((interior_mono hΩ).trans interior_interior.subset))
  choose α hα using fun j : Fin (4 * N) =>
    existsAnnularSpokes_step3_spoke M S Ω hcov hsts c hN hR hΩ L H hL hLu hHl hHu j
  have hdisj : ∀ i j, i ≠ j → Disjoint (α i).carrier (α j).carrier := fun _ _ hij =>
    (existsAnnularSpokes_step2_tubes c hD hN hR hij).mono (hα _).2.2.2.2.2 (hα _).2.2.2.2.2
  have hstop : ∀ j, (α j).stop ∈ (α j).carrier ∩ frontier H.carrier := fun j => by
    rw [(hα j).2.2.2.2.1]
    exact Set.mem_singleton _
  have hinj : Function.Injective fun j => (α j).stop := by
    intro i j hij
    have hij' : (α i).stop = (α j).stop := hij
    by_contra hne
    refine Set.disjoint_left.1 (hdisj i j hne) (hstop i).1 ?_
    rw [hij']
    exact (hstop j).1
  obtain ⟨γo, σ, hγo, hord⟩ :=
    existsAnnularSpokes_step4_sort H.disk (fun j => (α j).stop) (fun j => (hstop j).2) hinj
  have horder := existsAnnularSpokes_step5_crosscuts H.disk L.disk hLH (fun j => α (σ j))
    (fun j => (hα (σ j)).2.2.1) (fun j => (hα (σ j)).2.2.2.1) (fun j => (hα (σ j)).2.2.2.2.1)
    (fun i j hij => hdisj _ _ (σ.injective.ne hij)) hγo hord
  obtain ⟨T, -⟩ := existsAnnularSpokes_step6_cut S hsts L H hLH hHS (by omega)
    (fun j => α (σ j)) (fun j => (hα (σ j)).1) (fun j => (hα (σ j)).2.1)
    (fun j => (hα (σ j)).2.2.1) (fun j => (hα (σ j)).2.2.2.1) (fun j => (hα (σ j)).2.2.2.2.1)
    (fun i j hij => hdisj _ _ (σ.injective.ne hij)) horder
  exact ⟨T⟩

/-! ## Quantitative sector localization (`lem:quantitative-sector`) -/

/-- The point at arclength parameter `t ∈ [0, 8A)` on the boundary of the
square `[-A, A]²`, starting at the corner `(A, -A)` and running
counterclockwise. -/
def squarePerimeterPoint (A t : ℝ) : Pt :=
  if t ≤ 2 * A then mkPt A (-A + t)
  else if t ≤ 4 * A then mkPt (A - (t - 2 * A)) A
  else if t ≤ 6 * A then mkPt (-A) (A - (t - 4 * A))
  else mkPt (-A + (t - 6 * A)) (-A)

/-- The ideal radial trapezoid `T_j` between the radial segments through the
successive length-`R` positions `v_j, v_{j+1}` of `∂Q₀` (half side
`A = NR/2`), between `∂Q₀` and `∂K₁` (half side `h = A + R + 3D`). -/
def idealTrapezoid (c : Pt) (N : ℕ) (R D : ℝ) (j : ℕ) : Set Pt :=
  {x | ∃ t ∈ Icc ((j : ℝ) * R) (((j : ℝ) + 1) * R),
    ∃ μ ∈ Icc (1 : ℝ) (((N : ℝ) * R / 2 + R + 3 * D) / ((N : ℝ) * R / 2)),
      x = c + μ • squarePerimeterPoint ((N : ℝ) * R / 2) t}

/-- Private outer edges of the `j`-th annular group: its listed sides on `∂H`
whose outside neighbouring original face meets no other annular group. -/
def privateOuterEdges {M : MeshConstants P} {S : Set (PlacedTile P)} {c : Pt} {N : ℕ}
    {R : ℝ} (G : AnnularGrouping M S c N R) (j : Fin (4 * N)) : Set (Set Pt) :=
  {e | (∃ A ∈ (G.spokes.piece j).faces, HasEdge A e) ∧ e ⊆ frontier G.H.carrier ∧
    ∃ F ∈ S, F ∉ G.H.faces ∧ HasEdge F e ∧
      ∀ t, t ≠ j → Disjoint F.carrier (G.spokes.piece t).carrier}

/-! ### Helpers for `quantitativeAnnularGrouping` -/

/-- hat function -/
private def qoHat (n k : ℕ) (s : ℝ) : ℝ := max 0 (1 - |(n : ℝ) * s - k|)

private lemma qoHat_cont (n k : ℕ) : Continuous (qoHat n k) := by
  unfold qoHat; fun_prop

private lemma qoHat_zero {n k : ℕ} {s : ℝ} (h : 1 ≤ |(n : ℝ) * s - k|) : qoHat n k s = 0 := by
  unfold qoHat; rw [max_eq_left]; linarith

private def qoIdx (B : PolygonalDisk) (k : ℕ) : Fin B.n :=
  ⟨k % B.n, Nat.mod_lt _ (by have := B.three_le; omega)⟩

/-- piecewise-linear parametrization of the boundary on `[0,1]` -/
private def qoG (B : PolygonalDisk) (s : ℝ) : Pt :=
  ∑ k ∈ Finset.range (B.n + 1), qoHat B.n k s • B.vertex (qoIdx B k)

private lemma qoG_cont (B : PolygonalDisk) : Continuous (qoG B) := by
  unfold qoG
  exact continuous_finset_sum _ fun k _ => (qoHat_cont _ _).smul continuous_const

private lemma qoG_piece (B : PolygonalDisk) {k : ℕ} (hk : k < B.n) {s : ℝ}
    (hs1 : (k : ℝ) ≤ B.n * s) (hs2 : B.n * s ≤ k + 1) :
    qoG B s = B.vertex (qoIdx B k) + ((B.n : ℝ) * s - k) • (B.vertex (qoIdx B (k + 1)) - B.vertex (qoIdx B k)) := by
  unfold qoG
  rw [Finset.sum_eq_add_of_mem k (k + 1) (by simp; omega) (by simp; omega) (by omega)]
  · have h1 : qoHat B.n k s = 1 - (B.n * s - k) := by
      unfold qoHat; rw [abs_of_nonneg (by linarith)]; rw [max_eq_right (by linarith)]
    have h2 : qoHat B.n (k + 1) s = B.n * s - k := by
      unfold qoHat; push_cast; rw [abs_of_nonpos (by linarith)]; rw [max_eq_right (by linarith)]; ring
    rw [h1, h2]; module
  · intro j _ hj
    rw [qoHat_zero, zero_smul]
    rcases Nat.lt_or_gt_of_ne hj.1 with h | h
    · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
    · have : (k : ℝ) + 2 ≤ j := by
        have : k + 2 ≤ j := by omega
        exact_mod_cast this
      rw [abs_of_nonpos (by linarith)]; linarith

private lemma qoIdx_succ (B : PolygonalDisk) (k : ℕ) (hk : k < B.n) :
    qoIdx B (k + 1) = finRotate B.n (qoIdx B k) := by
  apply Fin.ext
  rw [finRotate_val']
  simp only [qoIdx, Nat.mod_eq_of_lt hk]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (by omega)]

private lemma qoIdx_val (B : PolygonalDisk) (i : Fin B.n) : qoIdx B i.val = i := by
  apply Fin.ext; simp [qoIdx, Nat.mod_eq_of_lt i.isLt]

private lemma qoG_zero (B : PolygonalDisk) : qoG B 0 = B.vertex (qoIdx B 0) := by
  have hn : 0 < B.n := by have := B.three_le; omega
  rw [qoG_piece B hn (by simp) (by simp)]; simp

private lemma qoG_one (B : PolygonalDisk) : qoG B 1 = B.vertex (qoIdx B 0) := by
  have hn : 0 < B.n := by have := B.three_le; omega
  rw [qoG_piece B (k := B.n - 1) (by omega) (by rw [Nat.cast_sub (by omega)]; simp)
    (by rw [Nat.cast_sub (by omega)]; simp)]
  have : B.n - 1 + 1 = B.n := by omega
  rw [this, Nat.cast_sub (by omega)]
  have e : qoIdx B B.n = qoIdx B 0 := by apply Fin.ext; simp [qoIdx]
  rw [e]; simp

/-- the boundary loop -/
private def qoLoop (B : PolygonalDisk) (t : ℝ) : Pt := qoG B (Int.fract t)

/-- every `s ∈ [0,1)` lies in a piece -/
private lemma qo_piece_of (B : PolygonalDisk) {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    ∃ k < B.n, (k : ℝ) ≤ B.n * s ∧ B.n * s < k + 1 := by
  have hn : (0 : ℝ) < B.n := by have := B.three_le; exact_mod_cast (show 0 < B.n by omega)
  refine ⟨⌊(B.n : ℝ) * s⌋₊, ?_, Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩
  have : (B.n : ℝ) * s < B.n := by nlinarith
  exact (Nat.floor_lt (by positivity)).2 this

private lemma qoG_mem_side (B : PolygonalDisk) {k : ℕ} (hk : k < B.n) {s : ℝ}
    (hs1 : (k : ℝ) ≤ B.n * s) (hs2 : B.n * s ≤ k + 1) :
    qoG B s ∈ B.side (qoIdx B k) := by
  rw [qoG_piece B hk hs1 hs2, PolygonalDisk.side, ← qoIdx_succ B k hk]
  rw [segment_eq_image']
  exact ⟨_, ⟨by linarith, by linarith⟩, rfl⟩

private lemma qoLoop_isLoopParam (B : PolygonalDisk) : IsLoopParam (frontier B.carrier) (qoLoop B) := by
  have hn : (0 : ℝ) < B.n := by have := B.three_le; exact_mod_cast (show 0 < B.n by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := ContinuousOn.comp_fract (s := id) (f := fun (_ : ℝ) u => qoG B u)
      ((qoG_cont B).comp continuous_snd).continuousOn continuous_id (fun _ => by simp only; rw [qoG_zero, qoG_one])
    exact this
  · intro t; simp [qoLoop]
  · intro s hs s' hs' heq
    simp only [qoLoop, Int.fract_eq_self.2 hs, Int.fract_eq_self.2 hs'] at heq
    obtain ⟨k, hk, hk1, hk2⟩ := qo_piece_of B hs.1 hs.2
    obtain ⟨k', hk', hk1', hk2'⟩ := qo_piece_of B hs'.1 hs'.2
    rw [qoG_piece B hk hk1 hk2.le, qoG_piece B hk' hk1' hk2'.le] at heq
    rw [qoIdx_succ B k hk, qoIdx_succ B k' hk'] at heq
    have hne := pd_vertex_ne_next B
    by_cases hkk : k = k'
    · subst hkk
      have h3 := sub_eq_zero.2 heq
      rw [show B.vertex (qoIdx B k) + ((B.n : ℝ) * s - k) • (B.vertex (finRotate B.n (qoIdx B k)) - B.vertex (qoIdx B k)) -
        (B.vertex (qoIdx B k) + ((B.n : ℝ) * s' - k) • (B.vertex (finRotate B.n (qoIdx B k)) - B.vertex (qoIdx B k)))
        = ((B.n : ℝ) * (s - s')) • (B.vertex (finRotate B.n (qoIdx B k)) - B.vertex (qoIdx B k)) by module] at h3
      rcases smul_eq_zero.1 h3 with h4 | h4
      · rcases mul_eq_zero.1 h4 with h5 | h5
        · linarith
        · linarith
      · exact absurd (sub_eq_zero.1 h4).symm (hne _)
    · exfalso
      set x := B.vertex (qoIdx B k) + ((B.n : ℝ) * s - k) • (B.vertex (finRotate B.n (qoIdx B k)) - B.vertex (qoIdx B k))
      have hik : qoIdx B k ≠ qoIdx B k' := by
        intro h; apply hkk
        have := congrArg Fin.val h; simpa [qoIdx, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk'] using this
      have hx1 : x ∈ segment ℝ (B.vertex (qoIdx B k)) (B.vertex (finRotate B.n (qoIdx B k))) := by
        rw [segment_eq_image']; exact ⟨_, ⟨by linarith, by linarith⟩, rfl⟩
      have hx2 : x ∈ segment ℝ (B.vertex (qoIdx B k')) (B.vertex (finRotate B.n (qoIdx B k'))) := by
        rw [heq, segment_eq_image']; exact ⟨_, ⟨by linarith, by linarith⟩, rfl⟩
      have hs := B.simple _ _ hik ⟨hx1, hx2⟩
      -- x is not the second endpoint of its own side
      have key : ∀ (j : Fin B.n) (τ : ℝ), τ < 1 →
          B.vertex j + τ • (B.vertex (finRotate B.n j) - B.vertex j) ≠ B.vertex (finRotate B.n j) := by
        intro j τ hτ h
        have : (1 - τ) • (B.vertex (finRotate B.n j) - B.vertex j) = 0 := by
          rw [show (1 - τ) • (B.vertex (finRotate B.n j) - B.vertex j) = B.vertex (finRotate B.n j) -
            (B.vertex j + τ • (B.vertex (finRotate B.n j) - B.vertex j)) by module, h, sub_self]
        rcases smul_eq_zero.1 this with h1 | h1
        · linarith
        · exact hne j (sub_eq_zero.1 h1).symm
      have hxa : x = B.vertex (qoIdx B k) := by
        rcases hs.1 with h | h
        · exact h
        · exact absurd h (key _ _ (by linarith))
      have hxb : x = B.vertex (qoIdx B k') := by
        rcases hs.2 with h | h
        · exact h
        · rw [heq] at h; exact absurd h (key _ _ (by linarith))
      exact hik (B.vertex_injective (hxa.symm.trans hxb))
  · rw [B.frontier_eq]
    ext x
    simp only [mem_image, mem_iUnion]
    constructor
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨k, hk, hk1, hk2⟩ := qo_piece_of B hs.1 hs.2
      refine ⟨qoIdx B k, ?_⟩
      simp only [qoLoop, Int.fract_eq_self.2 hs]
      exact qoG_mem_side B hk hk1 hk2.le
    · rintro ⟨i, hi⟩
      rw [segment_eq_image'] at hi
      obtain ⟨τ, hτ, rfl⟩ := hi
      have hiv : (i.val : ℝ) + 1 ≤ B.n := by exact_mod_cast i.isLt
      rcases hτ.2.lt_or_eq with hτ1 | hτ1
      · refine ⟨(i.val + τ) / B.n, ⟨by have := hτ.1; positivity, ?_⟩, ?_⟩
        · rw [div_lt_one hn]; linarith
        · simp only [qoLoop]
          rw [Int.fract_eq_self.2 ⟨by have := hτ.1; positivity, by rw [div_lt_one hn]; linarith⟩]
          rw [qoG_piece B i.isLt (by field_simp; linarith [hτ.1]) (by field_simp; linarith), qoIdx_succ B _ i.isLt,
            qoIdx_val]
          congr 2; field_simp; ring
      · subst hτ1
        set j := finRotate B.n i
        refine ⟨j.val / B.n, ⟨by positivity, by rw [div_lt_one hn]; exact_mod_cast j.isLt⟩, ?_⟩
        simp only [qoLoop]
        rw [Int.fract_eq_self.2 ⟨by positivity, by rw [div_lt_one hn]; exact_mod_cast j.isLt⟩]
        rw [qoG_piece B j.isLt (by field_simp; rfl) (by field_simp; linarith), qoIdx_val]
        have : (B.n : ℝ) * (j.val / B.n) - j.val = 0 := by field_simp; ring
        rw [this, zero_smul, add_zero]
        module

private lemma qo_loop_fract {K : Set Pt} {γ : ℝ → Pt} (hγ : IsLoopParam K γ) (x : ℝ) :
    γ (Int.fract x) = γ x := by
  have := hγ.2.1.sub_int_mul_eq (x := x) ⌊x⌋
  rw [mul_one] at this; rw [Int.fract]; exact this

private lemma qo_loop_eq_iff {K : Set Pt} {γ : ℝ → Pt} (hγ : IsLoopParam K γ) (x y : ℝ) :
    γ x = γ y ↔ Int.fract x = Int.fract y := by
  constructor
  · intro h
    rw [← qo_loop_fract hγ x, ← qo_loop_fract hγ y] at h
    exact hγ.2.2.1 ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩ ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩ h
  · intro h; rw [← qo_loop_fract hγ x, ← qo_loop_fract hγ y, h]

private lemma qo_loop_mem {K : Set Pt} {γ : ℝ → Pt} (hγ : IsLoopParam K γ) (x : ℝ) : γ x ∈ K := by
  rw [← qo_loop_fract hγ x, ← hγ.2.2.2]
  exact ⟨_, ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩, rfl⟩

private lemma qo_loop_of_eq {K : Set Pt} {γ γ' : ℝ → Pt} (hγ : IsLoopParam K γ) (hc : Continuous γ')
    (hp : Function.Periodic γ' 1) (h : ∀ x y, γ' x = γ' y → ∃ z : ℤ, x - y = z)
    (hsurj : ∀ x, ∃ y, γ' y = γ x) (hmem : ∀ x, ∃ y, γ y = γ' x) : IsLoopParam K γ' := by
  have frac' : ∀ x, γ' (Int.fract x) = γ' x := by
    intro x
    have := hp.sub_int_mul_eq (x := x) ⌊x⌋
    rw [mul_one] at this; rw [Int.fract]; exact this
  refine ⟨hc, hp, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨z, hz⟩ := h x y hxy
    have h1 : (z : ℝ) < 1 := by rw [← hz]; linarith [hx.2, hy.1]
    have h2 : (-1 : ℝ) < z := by rw [← hz]; linarith [hx.1, hy.2]
    have : z = 0 := by
      have h3 : z < 1 := by exact_mod_cast h1
      have h4 : -1 < z := by exact_mod_cast h2
      omega
    rw [this, Int.cast_zero, sub_eq_zero] at hz; exact hz
  · ext z
    constructor
    · rintro ⟨x, -, rfl⟩
      obtain ⟨y, hy⟩ := hmem x
      rw [← hy]; exact qo_loop_mem hγ y
    · intro hz
      rw [← hγ.2.2.2] at hz
      obtain ⟨x, -, rfl⟩ := hz
      obtain ⟨y, hy⟩ := hsurj x
      exact ⟨Int.fract y, ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩, by rw [frac', hy]⟩

private lemma qo_loop_shift {K : Set Pt} {γ : ℝ → Pt} (hγ : IsLoopParam K γ) (s : ℝ) :
    IsLoopParam K (fun t => γ (t + s)) :=
  qo_loop_of_eq hγ (hγ.1.comp (continuous_add_right s))
    (fun t => by show γ (t + 1 + s) = γ (t + s); rw [add_right_comm, hγ.2.1])
    (fun x y hxy => by
      obtain ⟨z, hz⟩ := Int.fract_eq_fract.1 ((qo_loop_eq_iff hγ _ _).1 hxy)
      exact ⟨z, by rw [← hz]; ring⟩) (fun x => ⟨x - s, by simp⟩) (fun x => ⟨x + s, rfl⟩)

private lemma qo_loop_neg {K : Set Pt} {γ : ℝ → Pt} (hγ : IsLoopParam K γ) :
    IsLoopParam K (fun t => γ (-t)) := by
  refine qo_loop_of_eq hγ (hγ.1.comp continuous_neg) (fun t => ?_) (fun x y hxy => ?_)
    (fun x => ⟨-x, by simp⟩) (fun x => ⟨-x, rfl⟩)
  · show γ (-(t + 1)) = γ (-t)
    rw [show -(t + 1) = -t - 1 by ring]
    exact hγ.2.1.sub_eq _
  · obtain ⟨z, hz⟩ := Int.fract_eq_fract.1 ((qo_loop_eq_iff hγ _ _).1 hxy)
    exact ⟨-z, by push_cast; rw [← hz]; ring⟩

/-- the combinatorial core: positions in `[0,1)` satisfying the per-`b` dichotomy are ordered -/
private lemma qo_comb {k : ℕ} (hk : 4 ≤ k) (t : Fin k → ℝ)
    (hcase : ∀ b : Fin k, 3 ≤ b.val →
      ((∀ i : Fin k, 2 ≤ i.val → i.val < b.val → t i < t b) ∧
          (∀ i : Fin k, (b.val < i.val ∨ i.val = 0) → t b < t i)) ∨
      ((∀ i : Fin k, 2 ≤ i.val → i.val < b.val → t b < t i) ∧
          (∀ i : Fin k, (b.val < i.val ∨ i.val = 0) → t i < t b))) :
    ((∀ i j : Fin k, 2 ≤ i.val → i.val < j.val → t i < t j) ∧ (∀ i : Fin k, 2 ≤ i.val → t i < t ⟨0, by omega⟩)) ∨
    ((∀ i j : Fin k, 2 ≤ i.val → i.val < j.val → t j < t i) ∧ (∀ i : Fin k, 2 ≤ i.val → t ⟨0, by omega⟩ < t i)) := by
  set b3 : Fin k := ⟨3, by omega⟩
  set bl : Fin k := ⟨k - 1, by omega⟩
  set z : Fin k := ⟨0, by omega⟩
  -- all cases agree with the case at `3`
  have agree1 : ∀ b : Fin k, 3 ≤ b.val →
      ((∀ i : Fin k, 2 ≤ i.val → i.val < b.val → t i < t b) ∧
          (∀ i : Fin k, (b.val < i.val ∨ i.val = 0) → t b < t i)) →
      ∀ b' : Fin k, 3 ≤ b'.val → ((∀ i : Fin k, 2 ≤ i.val → i.val < b'.val → t i < t b') ∧
          (∀ i : Fin k, (b'.val < i.val ∨ i.val = 0) → t b' < t i)) := by
    intro b hb hI b' hb'
    rcases hcase b' hb' with h | h
    · exact h
    · exfalso
      rcases lt_trichotomy b.val b'.val with hl | he | hl
      · have := hI.2 b' (Or.inl hl); have := h.1 b (by omega) hl; linarith
      · have hbb : b = b' := Fin.ext he
        subst hbb
        have := hI.2 z (Or.inr rfl); have := h.2 z (Or.inr rfl); linarith
      · have := hI.1 b' (by omega) hl; have := h.2 b (Or.inl hl); linarith
  have agree2 : ∀ b : Fin k, 3 ≤ b.val →
      ((∀ i : Fin k, 2 ≤ i.val → i.val < b.val → t b < t i) ∧
          (∀ i : Fin k, (b.val < i.val ∨ i.val = 0) → t i < t b)) →
      ∀ b' : Fin k, 3 ≤ b'.val → ((∀ i : Fin k, 2 ≤ i.val → i.val < b'.val → t b' < t i) ∧
          (∀ i : Fin k, (b'.val < i.val ∨ i.val = 0) → t i < t b')) := by
    intro b hb hI b' hb'
    rcases hcase b' hb' with h | h
    · exfalso
      rcases lt_trichotomy b.val b'.val with hl | he | hl
      · have := hI.2 b' (Or.inl hl); have := h.1 b (by omega) hl; linarith
      · have hbb : b = b' := Fin.ext he
        subst hbb
        have := hI.2 z (Or.inr rfl); have := h.2 z (Or.inr rfl); linarith
      · have := hI.1 b' (by omega) hl; have := h.2 b (Or.inl hl); linarith
    · exact h
  rcases hcase b3 (le_refl 3) with h3 | h3
  · left
    have hall := agree1 b3 (le_refl _) h3
    refine ⟨fun i j hi hij => ?_, fun i hi => ?_⟩
    · exact (hall j (by omega)).1 i hi hij
    · by_cases hi3 : 3 ≤ i.val
      · exact (hall i hi3).2 z (Or.inr rfl)
      · have := (hall b3 le_rfl).1 i hi (by simp [b3]; omega)
        have := (hall b3 le_rfl).2 z (Or.inr rfl)
        linarith
  · right
    have hall := agree2 b3 (le_refl _) h3
    refine ⟨fun i j hi hij => ?_, fun i hi => ?_⟩
    · exact (hall j (by omega)).1 i hi hij
    · by_cases hi3 : 3 ≤ i.val
      · exact (hall i hi3).2 z (Or.inr rfl)
      · have := (hall b3 le_rfl).1 i hi (by simp [b3]; omega)
        have := (hall b3 le_rfl).2 z (Or.inr rfl)
        linarith

/-- from ordered positions to `PointsInOrder` -/
private lemma qo_pointsInOrder {K : Set Pt} {γ : ℝ → Pt} (hγ : IsLoopParam K γ) {k : ℕ} (hk : 4 ≤ k)
    (w : Fin k → Pt) (t : Fin k → ℝ) (ht : ∀ i, t i ∈ Ico (0 : ℝ) 1) (htw : ∀ i, γ (t i) = w i)
    (h1max : ∀ i : Fin k, i.val ≠ 1 → t i < t ⟨1, by omega⟩)
    (hcase : ∀ b : Fin k, 3 ≤ b.val →
      ((∀ i : Fin k, 2 ≤ i.val → i.val < b.val → t i < t b) ∧
          (∀ i : Fin k, (b.val < i.val ∨ i.val = 0) → t b < t i)) ∨
      ((∀ i : Fin k, 2 ≤ i.val → i.val < b.val → t b < t i) ∧
          (∀ i : Fin k, (b.val < i.val ∨ i.val = 0) → t i < t b))) :
    ∃ γo : ℝ → Pt, IsLoopParam K γo ∧ PointsInOrder γo w := by
  set z : Fin k := ⟨0, by omega⟩
  set o : Fin k := ⟨1, by omega⟩
  have hz1 : t z < t o := h1max z (by simp [z])
  rcases qo_comb hk t hcase with ⟨hinc, h0⟩ | ⟨hdec, h0⟩
  · refine ⟨γ, hγ, fun i => if i.val < 2 then t i - 1 else t i, ?_, ?_, ?_⟩
    · intro i j hij
      have hij' : i.val < j.val := hij
      simp only
      split_ifs with hi hj hj
      · have hi0 : i = z := Fin.ext (by simp [z]; omega)
        have hj1 : j = o := Fin.ext (by simp [o]; omega)
        rw [hi0, hj1]; linarith
      · linarith [(ht i).2, (ht j).1]
      · omega
      · exact hinc i j (by omega) hij'
    · intro i j
      have hmin : ∀ l : Fin k, t z - 1 ≤ (if l.val < 2 then t l - 1 else t l) := by
        intro l
        split_ifs with hl
        · by_cases hl0 : l.val = 0
          · rw [show l = z from Fin.ext (by simp [z, hl0])]
          · rw [show l = o from Fin.ext (by simp [o]; omega)]; linarith
        · linarith [(ht l).1, (ht z).2]
      have hmax : ∀ l : Fin k, (if l.val < 2 then t l - 1 else t l) < t z := by
        intro l
        split_ifs with hl
        · linarith [(ht l).2, (ht z).1]
        · exact h0 l (by omega)
      linarith [hmin i, hmax j]
    · intro i
      simp only
      split_ifs
      · rw [show t i - 1 = t i + (-1 : ℤ) * 1 by push_cast; ring, hγ.2.1.int_mul, htw]
      · exact htw i
  · refine ⟨fun x => γ (-x), qo_loop_neg hγ, fun i => if i.val = 0 then -t i - 1 else -t i, ?_, ?_, ?_⟩
    · intro i j hij
      have hij' : i.val < j.val := hij
      simp only
      split_ifs with hi hj hj
      · omega
      · by_cases hj1 : j.val = 1
        · rw [show i = z from Fin.ext (by simp [z, hi]), show j = o from Fin.ext (by simp [o, hj1])]
          linarith [(ht o).2, (ht z).1]
        · rw [show i = z from Fin.ext (by simp [z, hi])]
          linarith [h0 j (by omega), (ht j).2, (ht z).1]
      · omega
      · by_cases hi1 : i.val = 1
        · have := h1max j (by omega)
          rw [show i = o from Fin.ext (by simp [o, hi1])]; linarith
        · have := hdec i j (by omega) hij'; linarith
    · intro i j
      have hmin : ∀ l : Fin k, -t z - 1 ≤ (if l.val = 0 then -t l - 1 else -t l) := by
        intro l
        split_ifs with hl
        · rw [show l = z from Fin.ext (by simp [z, hl])]
        · linarith [(ht l).2, (ht z).1]
      have hmax : ∀ l : Fin k, (if l.val = 0 then -t l - 1 else -t l) < -t z := by
        intro l
        split_ifs with hl
        · rw [show l = z from Fin.ext (by simp [z, hl])]; linarith
        · by_cases hl1 : l.val = 1
          · have := (ht o).2; rw [show l = o from Fin.ext (by simp [o, hl1])]
            have := h0 ⟨2, by omega⟩ (le_refl _)
            have := h1max ⟨2, by omega⟩ (by simp)
            linarith
          · have := h0 l (by omega); linarith
      linarith [hmin i, hmax j]
    · intro i
      simp only
      split_ifs
      · rw [show -(-t i - 1) = t i + (1 : ℤ) * 1 by push_cast; ring, hγ.2.1.int_mul, htw]
      · rw [neg_neg]; exact htw i

/-- the open polygonal chain through a list of points -/
private def qoChain : List Pt → Set Pt
  | a :: b :: l => segment ℝ a b ∪ qoChain (b :: l)
  | _ => ∅

/-- the closed polygon through a list of points, as a vertex function -/
private def qoV (l : List Pt) : Fin l.length → Pt := fun k => l[k.val]

private lemma qoChain_seg : ∀ (m : List Pt) (i : ℕ) (h : i + 1 < m.length),
    segment ℝ (m[i]'(by omega)) (m[i + 1]) ⊆ qoChain m
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: l, 0, _ => by simp [qoChain]
  | a :: b :: l, i + 1, h => by
    simp only [qoChain, List.getElem_cons_succ]
    exact (qoChain_seg (b :: l) i (by simp at h ⊢; omega)).trans subset_union_right

private lemma qoChain_append : ∀ (l₁ : List Pt) (a b : Pt) (l₂ : List Pt),
    qoChain (l₁ ++ a :: b :: l₂) = qoChain (l₁ ++ [a]) ∪ segment ℝ a b ∪ qoChain (b :: l₂)
  | [], a, b, l₂ => by simp [qoChain]
  | [x], a, b, l₂ => by simp [qoChain, union_assoc]
  | x :: y :: l₁, a, b, l₂ => by
    have := qoChain_append (y :: l₁) a b l₂
    simp only [List.cons_append] at this ⊢
    simp only [qoChain, this, union_assoc]

private lemma qoChain_single (a : Pt) : qoChain [a] = ∅ := rfl

private lemma qoChain_pair (a b : Pt) : qoChain [a, b] = segment ℝ a b := by simp [qoChain]

private lemma qoChain_subset_of_seg : ∀ (m : List Pt) (U : Set Pt),
    (∀ i (h : i + 1 < m.length), segment ℝ (m[i]'(by omega)) (m[i + 1]) ⊆ U) → qoChain m ⊆ U
  | [], _, _ => by simp [qoChain]
  | [_], _, _ => by simp [qoChain]
  | a :: b :: l, U, h => by
    simp only [qoChain, union_subset_iff]
    refine ⟨h 0 (by simp), qoChain_subset_of_seg (b :: l) U fun i hi => ?_⟩
    have := h (i + 1) (by simp at hi ⊢; omega)
    simpa using this

private lemma qoV_rot_lt (l : List Pt) (k : Fin l.length) (h : k.val + 1 < l.length) :
    qoV l (finRotate _ k) = l[k.val + 1] := by
  have : finRotate l.length k = ⟨k.val + 1, h⟩ := Fin.ext (by rw [finRotate_val']; simp; omega)
  rw [this]; rfl

private lemma qoV_rot_last (l : List Pt) (k : Fin l.length) (h : k.val + 1 = l.length) :
    qoV l (finRotate _ k) = l[0]'(by omega) := by
  have : finRotate l.length k = ⟨0, by omega⟩ := Fin.ext (by rw [finRotate_val']; simp; omega)
  rw [this]; rfl

private lemma qo_getLastD_eq (a : Pt) (l : List Pt) : (a :: l)[l.length]'(by simp) = l.getLastD a := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp only [List.length_cons, List.getElem_cons_succ, List.getLastD_cons]; exact ih b

private lemma qo_polyCurve_subset (a : Pt) (l : List Pt) :
    polyCurve (qoV (a :: l)) ⊆ qoChain (a :: l) ∪ segment ℝ (l.getLastD a) a := by
  intro x hx
  obtain ⟨k, hk⟩ := mem_iUnion.1 hx
  by_cases h : k.val + 1 = (a :: l).length
  · right
    rw [qoV_rot_last _ k h] at hk
    have hk' : k.val = l.length := by simp at h; omega
    have e1 : qoV (a :: l) k = l.getLastD a := by
      rcases k with ⟨kv, hkv⟩
      simp only at hk'
      subst hk'
      exact qo_getLastD_eq a l
    rw [e1] at hk
    simpa using hk
  · left
    rw [qoV_rot_lt _ k (by omega)] at hk
    exact qoChain_seg (a :: l) k.val (by omega) hk

private lemma qo_getElem_midL (l₁ : List Pt) (a b : Pt) (l₂ : List Pt) (i : ℕ) (hi : i < l₁.length + 1) :
    (l₁ ++ a :: b :: l₂)[i]'(by simp; omega) = (l₁ ++ [a])[i]'(by simp; omega) := by
  rw [List.getElem_append, List.getElem_append]
  split_ifs with h
  · rfl
  · have : i - l₁.length = 0 := by omega
    simp [this]

private lemma qo_getElem_midR (l₁ : List Pt) (a b : Pt) (l₂ : List Pt) (i : ℕ) (hi : l₁.length + 1 ≤ i)
    (hi2 : i < l₁.length + l₂.length + 2) :
    (l₁ ++ a :: b :: l₂)[i]'(by simp; omega) = (b :: l₂)[i - l₁.length - 1]'(by simp; omega) := by
  rw [List.getElem_append_right (by omega)]
  obtain ⟨j, hj⟩ : ∃ j, i - l₁.length = j + 1 := ⟨i - l₁.length - 1, by omega⟩
  simp only [hj, List.getElem_cons_succ, Nat.add_sub_cancel]

/-- the jump of the winding function across an edge of a list polygon -/
private lemma qo_wind_jump (l₁ : List Pt) (a b : Pt) (l₂ : List Pt) {q : Pt} (hab : a ≠ b)
    (hq : q ∈ openSegment ℝ a b) (h1 : q ∉ qoChain (l₁ ++ [a])) (h2 : q ∉ qoChain (b :: l₂))
    (h3 : q ∉ segment ℝ (l₂.getLastD b) (l₁.headD a)) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), wind (qoV (l₁ ++ a :: b :: l₂)) (q + t • jrot (b - a)) -
      wind (qoV (l₁ ++ a :: b :: l₂)) (q + (-t) • jrot (b - a)) = 2 * Real.pi := by
  have hlen : (l₁ ++ a :: b :: l₂).length = l₁.length + l₂.length + 2 := by simp; omega
  have hk0 : qoV (l₁ ++ a :: b :: l₂) ⟨l₁.length, by omega⟩ = a := by simp [qoV]
  have hk1' : qoV (l₁ ++ a :: b :: l₂) (finRotate _ ⟨l₁.length, by omega⟩) = b := by
    rw [qoV_rot_lt _ _ (by simp only [List.length_append, List.length_cons]; omega)]
    rw [qo_getElem_midR _ _ _ _ _ (le_refl _) (by omega)]
    simp
  have := wind_jump (c := qoV (l₁ ++ a :: b :: l₂)) ⟨l₁.length, by omega⟩ (by rw [hk0, hk1']; exact hab)
    (by rw [hk0, hk1']; exact hq) ?_
  · rw [hk0, hk1'] at this; exact this
  intro k hk hqk
  have hkne : k.val ≠ l₁.length := fun h => hk (Fin.ext h)
  rcases k with ⟨kv, hkl⟩
  simp only at hkne
  by_cases hlast : kv + 1 = (l₁ ++ a :: b :: l₂).length
  · rw [qoV_rot_last _ _ hlast] at hqk
    apply h3
    have e1 : qoV (l₁ ++ a :: b :: l₂) ⟨kv, hkl⟩ = l₂.getLastD b := by
      have hkv : kv = l₁.length + 1 + l₂.length := by omega
      subst hkv
      simp only [qoV]
      rw [qo_getElem_midR _ _ _ _ _ (by omega) (by omega)]
      have : l₁.length + 1 + l₂.length - l₁.length - 1 = l₂.length := by omega
      simp only [this]
      exact qo_getLastD_eq b l₂
    have e2 : (l₁ ++ a :: b :: l₂)[0]'(by omega) = l₁.headD a := by
      cases l₁ <;> simp
    rw [e1, e2] at hqk; exact hqk
  · rw [qoV_rot_lt _ _ (by simp only; omega)] at hqk
    simp only [qoV] at hqk
    rcases Nat.lt_or_gt_of_ne hkne with hlt | hgt
    · apply h1
      refine qoChain_seg (l₁ ++ [a]) kv (by simp; omega) ?_
      rw [qo_getElem_midL _ _ _ _ _ (by omega), qo_getElem_midL _ _ _ _ _ (by omega)] at hqk
      exact hqk
    · apply h2
      refine qoChain_seg (b :: l₂) (kv - l₁.length - 1) (by simp; omega) ?_
      rw [qo_getElem_midR _ _ _ _ _ (by omega) (by omega), qo_getElem_midR _ _ _ _ _ (by omega) (by omega)] at hqk
      have : kv + 1 - l₁.length - 1 = kv - l₁.length - 1 + 1 := by omega
      simp only [this] at hqk
      exact hqk

private lemma qoChain_snoc : ∀ (a : Pt) (m : List Pt) (z : Pt),
    qoChain (a :: m ++ [z]) = qoChain (a :: m) ∪ segment ℝ (m.getLastD a) z
  | a, [], z => by simp [qoChain]
  | a, b :: m, z => by
    have := qoChain_snoc b m z
    simp only [List.cons_append] at this ⊢
    simp only [qoChain, this, List.getLastD_cons, union_assoc]

/-- polygonal paths in open connected sets -/
private lemma qo_polyPath {U : Set Pt} (hU : IsOpen U) (hc : IsPreconnected U) {x y : Pt}
    (hx : x ∈ U) (hy : y ∈ U) : ∃ m : List Pt, qoChain (x :: m ++ [y]) ⊆ U := by
  set V := {z : Pt | ∃ m : List Pt, qoChain (x :: m ++ [z]) ⊆ U} with hV
  have ext : ∀ z ∈ V, ∀ z', segment ℝ z z' ⊆ U → z' ∈ V := by
    rintro z ⟨m, hm⟩ z' hzz
    refine ⟨m ++ [z], ?_⟩
    rw [show x :: (m ++ [z]) ++ [z'] = x :: (m ++ [z]) ++ [z'] from rfl, qoChain_snoc]
    refine union_subset (by simpa using hm) ?_
    have : (m ++ [z]).getLastD x = z := by simp [List.getLastD_eq_getLast?]
    rw [this]; exact hzz
  have hball : ∀ z ∈ U, ∃ r > 0, Metric.ball z r ⊆ U := fun z hz => Metric.isOpen_iff.1 hU z hz
  have hsegball : ∀ (z : Pt) (r : ℝ) (z' : Pt), z' ∈ Metric.ball z r → segment ℝ z z' ⊆ Metric.ball z r :=
    fun z r z' hz' => (convex_ball z r).segment_subset (Metric.mem_ball_self (by
      have := Metric.mem_ball.1 hz'; have := dist_nonneg (x := z') (y := z); linarith)) hz'
  have hu : IsOpen {z | z ∈ U ∧ z ∈ V} := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzU, hzV⟩
    obtain ⟨r, hr, hrU⟩ := hball z hzU
    exact ⟨r, hr, fun z' hz' => ⟨hrU hz', ext z hzV z' ((hsegball z r z' hz').trans hrU)⟩⟩
  have hv : IsOpen {z | z ∈ U ∧ z ∉ V} := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzU, hzV⟩
    obtain ⟨r, hr, hrU⟩ := hball z hzU
    refine ⟨r, hr, fun z' hz' => ⟨hrU hz', fun hz'V => hzV (ext z' hz'V z ?_)⟩⟩
    rw [segment_symm]; exact (hsegball z r z' hz').trans hrU
  have hxV : x ∈ V := ⟨[], by simp [qoChain, hx]⟩
  have := hc.subset_left_of_subset_union hu hv
    (by rw [Set.disjoint_left]; rintro z ⟨-, h1⟩ ⟨-, h2⟩; exact h2 h1)
    (fun z hz => by by_cases h : z ∈ V; exacts [Or.inl ⟨hz, h⟩, Or.inr ⟨hz, h⟩]) ⟨x, hx, hx, hxV⟩
  exact (this hy).2

private lemma qo_pos_L2 {ρ u u' M : ℝ} 
    (h0 : |existsAnnularSpokes_pos ρ u 0 - existsAnnularSpokes_pos ρ u' 0| ≤ M)
    (h1 : |existsAnnularSpokes_pos ρ u 1 - existsAnnularSpokes_pos ρ u' 1| ≤ M) :
    |u - u'| ≤ 2 * M ∨ 8 * ρ - |u - u'| ≤ 2 * M := by
  unfold existsAnnularSpokes_pos at h0 h1
  rw [abs_le] at h0 h1
  obtain ⟨h0a, h0b⟩ := h0
  obtain ⟨h1a, h1b⟩ := h1
  rcases le_total u u' with h | h
  · rw [abs_of_nonpos (by linarith)]
    split_ifs at h0a h0b h1a h1b <;> simp only [rg_mkPt0, rg_mkPt1] at h0a h0b h1a h1b <;>
      first | (left; linarith) | (right; linarith) |
        (rcases le_total (u - u') (4 * ρ) with h' | h' <;> rcases le_total (u' - u) (4 * ρ) with h'' | h'' <;>
          first | (left; linarith) | (right; linarith))
  · rw [abs_of_nonneg (by linarith)]
    split_ifs at h0a h0b h1a h1b <;> simp only [rg_mkPt0, rg_mkPt1] at h0a h0b h1a h1b <;>
      first | (left; linarith) | (right; linarith) |
        (rcases le_total (u - u') (4 * ρ) with h' | h' <;> rcases le_total (u' - u) (4 * ρ) with h'' | h'' <;>
          first | (left; linarith) | (right; linarith))

/-- the four outward axis directions -/
private def qoD : Fin 4 → Pt
  | 0 => mkPt 1 0
  | 1 => mkPt 0 1
  | 2 => mkPt (-1) 0
  | 3 => mkPt 0 (-1)

/-- the coordinate along the `k`-th direction -/
private def qoCo (k : Fin 4) (x : Pt) : ℝ := x 0 * qoD k 0 + x 1 * qoD k 1

private lemma qoD_jrot (k : Fin 4) : jrot (qoD k) = qoD (k + 1) := by
  fin_cases k <;> apply pt_ext <;> simp [qoD, mkPt]

private lemma qoD_add_two (k : Fin 4) : qoD (k + 2) = - qoD k := by
  fin_cases k <;> apply pt_ext <;> simp [qoD, mkPt]

private lemma qoCo_add (k : Fin 4) (x y : Pt) : qoCo k (x + y) = qoCo k x + qoCo k y := by
  simp [qoCo]; ring

private lemma qoCo_sub (k : Fin 4) (x y : Pt) : qoCo k (x - y) = qoCo k x - qoCo k y := by
  simp [qoCo]; ring

private lemma qoCo_smul (k : Fin 4) (a : ℝ) (x : Pt) : qoCo k (a • x) = a * qoCo k x := by
  simp [qoCo]; ring

private lemma qoCo_self (k : Fin 4) : qoCo k (qoD k) = 1 := by
  fin_cases k <;> simp [qoCo, qoD, mkPt]

private lemma qoCo_next (k : Fin 4) : qoCo k (qoD (k + 1)) = 0 := by
  fin_cases k <;> simp [qoCo, qoD, mkPt]

private lemma qoCo_next' (k : Fin 4) : qoCo (k + 1) (qoD k) = 0 := by
  fin_cases k <;> simp [qoCo, qoD, mkPt]

private lemma qoCo_add_two (k : Fin 4) (x : Pt) : qoCo (k + 2) x = - qoCo k x := by
  fin_cases k <;> simp [qoCo, qoD, mkPt]

private lemma qo_decomp (k : Fin 4) (x : Pt) : x = qoCo k x • qoD k + qoCo (k + 1) x • qoD (k + 1) := by
  fin_cases k <;> apply pt_ext <;> simp [qoCo, qoD, mkPt]

private lemma qo_abs_coord_le (k : Fin 4) (x : Pt) (r : ℝ) (h0 : |x 0| ≤ r) (h1 : |x 1| ≤ r) :
    |qoCo k x| ≤ r := by
  fin_cases k <;> simp [qoCo, qoD, mkPt] <;> assumption

private lemma qo_square_iff (c x : Pt) (r : ℝ) : x ∈ square c r ↔ ∀ k : Fin 4, qoCo k (x - c) ≤ r := by
  constructor
  · intro hx k
    exact (le_abs_self _).trans (qo_abs_coord_le k (x - c) r (by simpa using hx.1) (by simpa using hx.2))
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    simp [qoCo, qoD, mkPt] at h0 h1 h2 h3
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

/-- the boundary point on side `k` -/
private lemma qo_pos_side (k : Fin 4) {ρ τ : ℝ} (hρ : 0 < ρ) (h1 : -ρ ≤ τ) (h2 : τ ≤ ρ) :
    existsAnnularSpokes_pos ρ (2 * ρ * (k : ℕ) + ρ + τ) = ρ • qoD k + τ • qoD (k + 1) := by
  fin_cases k <;> unfold existsAnnularSpokes_pos <;> norm_num <;>
    split_ifs <;> apply pt_ext <;> simp [qoD, mkPt] <;> first | (exfalso; linarith) | linarith

/-- on one side, the perimeter map is affine -/
private lemma qo_pos_side' (k : Fin 4) {ρ s : ℝ} (hρ : 0 < ρ) (h1 : 2 * ρ * (k : ℕ) ≤ s)
    (h2 : s ≤ 2 * ρ * (k : ℕ) + 2 * ρ) :
    existsAnnularSpokes_pos ρ s = ρ • qoD k + (s - 2 * ρ * (k : ℕ) - ρ) • qoD (k + 1) := by
  rw [← qo_pos_side k hρ (by linarith) (by linarith)]; congr 1; ring

private lemma qo_pos_seg (k : Fin 4) {ρ s s' : ℝ} (hρ : 0 < ρ) (h1 : 2 * ρ * (k : ℕ) ≤ s) (hss : s ≤ s')
    (h2 : s' ≤ 2 * ρ * (k : ℕ) + 2 * ρ) :
    segment ℝ (existsAnnularSpokes_pos ρ s) (existsAnnularSpokes_pos ρ s') ⊆
      existsAnnularSpokes_pos ρ '' Icc s s' := by
  intro x hx
  rw [segment_eq_image'] at hx
  obtain ⟨θ, hθ, rfl⟩ := hx
  refine ⟨s + θ * (s' - s), ⟨by nlinarith [hθ.1], by nlinarith [hθ.2]⟩, ?_⟩
  rw [qo_pos_side' k hρ h1 (by linarith), qo_pos_side' k hρ (by linarith) h2,
    qo_pos_side' k hρ (by nlinarith [hθ.1]) (by nlinarith [hθ.2])]
  module

private lemma qo_pos_sub (k : Fin 4) {ρ s s' : ℝ} (hρ : 0 < ρ) (h1 : 2 * ρ * (k : ℕ) ≤ s) (h1' : 2 * ρ * (k : ℕ) ≤ s')
    (h2 : s ≤ 2 * ρ * (k : ℕ) + 2 * ρ) (h2' : s' ≤ 2 * ρ * (k : ℕ) + 2 * ρ) :
    existsAnnularSpokes_pos ρ s' - existsAnnularSpokes_pos ρ s = (s' - s) • qoD (k + 1) := by
  rw [qo_pos_side' k hρ h1 h2, qo_pos_side' k hρ h1' h2']
  module

private lemma qo_pos_scale {A ρ t : ℝ} (hA : 0 < A) (hρ : 0 < ρ) :
    (ρ / A) • existsAnnularSpokes_pos A t = existsAnnularSpokes_pos ρ (ρ / A * t) := by
  have key : ∀ c : ℝ, (t ≤ c * A ↔ ρ / A * t ≤ c * ρ) := by
    intro c
    rw [show c * ρ = ρ / A * (c * A) by field_simp]
    exact (mul_le_mul_iff_of_pos_left (div_pos hρ hA)).symm
  unfold existsAnnularSpokes_pos
  simp only [key 2, key 4, key 6]
  split_ifs <;> apply pt_ext <;> simp [mkPt] <;> field_simp

private lemma qo_pos_bound {A t : ℝ} (hA : 0 < A) (h0 : 0 ≤ t) (h8 : t ≤ 8 * A) :
    |existsAnnularSpokes_pos A t 0| ≤ A ∧ |existsAnnularSpokes_pos A t 1| ≤ A ∧
      (|existsAnnularSpokes_pos A t 0| = A ∨ |existsAnnularSpokes_pos A t 1| = A) := by
  unfold existsAnnularSpokes_pos
  split_ifs <;> simp only [rg_mkPt0, rg_mkPt1] <;>
    refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩, ?_⟩ <;>
    first | (left; rw [abs_of_pos (by linarith)]) | (left; rw [abs_of_neg (by linarith)]; ring) |
      (right; rw [abs_of_pos (by linarith)]) | (right; rw [abs_of_neg (by linarith)]; ring)

private lemma qoChain_append_sub : ∀ (l₁ l₂ : List Pt) (d : Pt),
    qoChain (l₁ ++ l₂) ⊆ qoChain l₁ ∪ segment ℝ (l₁.getLastD d) (l₂.headD d) ∪ qoChain l₂
  | [], l₂, d => fun x hx => Or.inr hx
  | [a], [], d => by simp [qoChain]
  | [a], b :: l₂, d => by
    intro x hx
    simp only [List.cons_append, List.nil_append, qoChain] at hx
    rcases hx with hx | hx
    · exact Or.inl (Or.inr (by simpa using hx))
    · exact Or.inr hx
  | a :: b :: l₁, l₂, d => by
    intro x hx
    simp only [List.cons_append, qoChain] at hx
    rcases hx with hx | hx
    · exact Or.inl (Or.inl (Or.inl hx))
    · have := qoChain_append_sub (b :: l₁) l₂ d (by simpa using hx)
      simp only [List.getLastD_cons] at this ⊢
      rcases this with (h | h) | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

private lemma qoChain_reverse : ∀ (l : List Pt), qoChain l.reverse = qoChain l
  | [] => rfl
  | [a] => rfl
  | a :: b :: l => by
    have ih := qoChain_reverse (b :: l)
    rw [List.reverse_cons, List.reverse_cons]
    have := qoChain_append l.reverse b a []
    simp only [List.append_assoc, List.cons_append, List.nil_append] at this ⊢
    rw [this, show l.reverse ++ [b] = (b :: l).reverse by simp, ih]
    simp [qoChain, segment_symm, union_comm]

/-- points of the big square boundary -/
private def qoPc (c : Pt) (ρ u : ℝ) : Pt := c + existsAnnularSpokes_pos ρ u

/-- two parameters on a common side -/
private def qoGood (ρ x y : ℝ) : Prop :=
  x = y ∨ ∃ k : Fin 4, 2 * ρ * (k : ℕ) ≤ x ∧ x ≤ y ∧ y ≤ 2 * ρ * (k : ℕ) + 2 * ρ

private def qoSG (ρ : ℝ) : ℝ → List ℝ → Prop
  | _, [] => True
  | x, y :: l => x ≤ y ∧ qoGood ρ x y ∧ qoSG ρ y l

private lemma qo_pos_inj {ρ u u' : ℝ} (hu : 0 ≤ u) (hu8 : u < 8 * ρ) (hu' : 0 ≤ u') (hu8' : u' < 8 * ρ)
    (h : existsAnnularSpokes_pos ρ u = existsAnnularSpokes_pos ρ u') : u = u' := by
  have := qo_pos_L2 (ρ := ρ) (u := u) (u' := u') (M := 0) (by rw [h]; simp) (by rw [h]; simp)
  rcases this with h1 | h1
  · have := abs_nonneg (u - u')
    have h2 : |u - u'| = 0 := by linarith
    linarith [abs_eq_zero.1 h2]
  · exfalso
    have : |u - u'| < 8 * ρ := abs_lt.2 ⟨by linarith, by linarith⟩
    linarith

private lemma qoPc_inj {c : Pt} {ρ u u' : ℝ} (hu : 0 ≤ u) (hu8 : u < 8 * ρ) (hu' : 0 ≤ u') (hu8' : u' < 8 * ρ)
    (h : qoPc c ρ u = qoPc c ρ u') : u = u' :=
  qo_pos_inj hu hu8 hu' hu8' (add_left_cancel h)

private lemma qo_seg_good {c : Pt} {ρ x y : ℝ} (hρ : 0 < ρ) (hxy : x ≤ y) (h : qoGood ρ x y) :
    segment ℝ (qoPc c ρ x) (qoPc c ρ y) ⊆ qoPc c ρ '' Icc x y := by
  rcases h with rfl | ⟨k, h1, -, h2⟩
  · simp only [segment_same, singleton_subset_iff]; exact ⟨x, ⟨le_rfl, le_rfl⟩, rfl⟩
  · intro z hz
    simp only [qoPc] at hz
    rw [← vadd_eq_add, ← vadd_eq_add, ← vadd_segment] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    obtain ⟨u, hu, hu'⟩ := qo_pos_seg k hρ h1 hxy h2 hz'
    exact ⟨u, hu, by simp [qoPc, hu']⟩

private lemma qoSG_le_last {ρ : ℝ} : ∀ (y : ℝ) (L : List ℝ), qoSG ρ y L → y ≤ L.getLastD y
  | y, [], _ => by simp
  | y, z :: L, h => by simp only [List.getLastD_cons]; exact h.1.trans (qoSG_le_last z L h.2.2)

private lemma qo_arc_chain {c : Pt} {ρ : ℝ} (hρ : 0 < ρ) : ∀ (x0 : ℝ) (L : List ℝ), qoSG ρ x0 L →
    qoChain ((x0 :: L).map (qoPc c ρ)) ⊆ qoPc c ρ '' Icc x0 (L.getLastD x0)
  | x0, [], _ => by simp [qoChain]
  | x0, y :: L, ⟨hxy, hg, hL⟩ => by
    have ih := qo_arc_chain (c := c) hρ y L hL
    have hyl : y ≤ L.getLastD y := qoSG_le_last y L hL
    simp only [List.map_cons, qoChain, List.getLastD_cons] at ih ⊢
    refine union_subset ((qo_seg_good hρ hxy hg).trans (image_mono (Icc_subset_Icc le_rfl hyl)))
      (ih.trans (image_mono (Icc_subset_Icc hxy le_rfl)))

private lemma qo_arc_split {c : Pt} {ρ : ℝ} (hρ : 0 < ρ) : ∀ (x0 : ℝ) (L : List ℝ), qoSG ρ x0 L → 0 ≤ x0 →
    L.getLastD x0 < 8 * ρ → ∀ v, x0 < v → v < L.getLastD x0 → v ∉ L →
    ∃ (l₁ l₂ : List Pt) (s s' : ℝ) (k : Fin 4), (x0 :: L).map (qoPc c ρ) = l₁ ++ qoPc c ρ s :: qoPc c ρ s' :: l₂ ∧
      s < v ∧ v < s' ∧ 2 * ρ * (k : ℕ) ≤ s ∧ s' ≤ 2 * ρ * (k : ℕ) + 2 * ρ ∧
      qoPc c ρ v ∉ qoChain (l₁ ++ [qoPc c ρ s]) ∧ qoPc c ρ v ∉ qoChain (qoPc c ρ s' :: l₂)
  | x0, [], _, _, _, v, h1, h2, _ => by simp at h2; linarith
  | x0, y :: L, ⟨hxy, hg, hL⟩, h0, h8, v, h1, h2, hv => by
    have hyl : y ≤ L.getLastD y := qoSG_le_last y L hL
    simp only [List.getLastD_cons] at h8 h2
    have hvy : v ≠ y := fun h => hv (h ▸ List.mem_cons_self)
    rcases lt_or_gt_of_ne hvy with hlt | hgt
    · rcases hg with heq | ⟨k, hk1, -, hk2⟩
      · exact absurd heq (by linarith)
      refine ⟨[], L.map (qoPc c ρ), x0, y, k, by simp, h1, hlt, hk1, hk2, by simp [qoChain], ?_⟩
      intro hmem
      have := qo_arc_chain (c := c) hρ y L hL
      simp only [List.map_cons] at this
      obtain ⟨u, hu, hu'⟩ := this hmem
      have := qoPc_inj (by linarith [hu.1]) (by linarith [hu.2]) (by linarith) (by linarith) hu'
      linarith [hu.1]
    · obtain ⟨l₁, l₂, s, s', k, heq, hs, hs', hk1, hk2, hn1, hn2⟩ :=
        qo_arc_split hρ y L hL (by linarith) h8 v hgt h2 (fun h => hv (List.mem_cons_of_mem _ h))
      refine ⟨qoPc c ρ x0 :: l₁, l₂, s, s', k, by simp only [List.map_cons] at heq ⊢; rw [heq]; rfl,
        hs, hs', hk1, hk2, ?_, hn2⟩
      intro hmem
      have hmap : (y :: L).map (qoPc c ρ) = l₁ ++ qoPc c ρ s :: qoPc c ρ s' :: l₂ := heq
      have hl1 : (l₁ ++ [qoPc c ρ s]).headD (qoPc c ρ x0) = qoPc c ρ y := by
        cases l₁ with
        | nil => simp only [List.map_cons, List.nil_append, List.cons.injEq] at hmap; simp [hmap.1]
        | cons a l => simp only [List.map_cons, List.cons_append, List.cons.injEq] at hmap; simp [hmap.1]
      have : qoChain (qoPc c ρ x0 :: (l₁ ++ [qoPc c ρ s])) ⊆
          segment ℝ (qoPc c ρ x0) (qoPc c ρ y) ∪ qoChain (l₁ ++ [qoPc c ρ s]) := by
        have := qoChain_append_sub [qoPc c ρ x0] (l₁ ++ [qoPc c ρ s]) (qoPc c ρ x0)
        simp only [List.singleton_append, qoChain_single, empty_union, hl1] at this
        exact this
      rcases this (by simpa using hmem) with h | h
      · obtain ⟨u, hu, hu'⟩ := qo_seg_good hρ hxy hg h
        have := qoPc_inj (by linarith [hu.1]) (by linarith [hu.2]) (by linarith) (by linarith) hu'
        linarith [hu.2]
      · exact hn1 h

private lemma qo_int_disj {S : Patch P} (H : FaceGroup S.tiles) {F : PlacedTile P} (hF : F ∈ S.tiles)
    (hFH : F ∉ H.faces) : Disjoint (interior F.carrier) H.carrier := by
  rw [Set.disjoint_left]
  intro x hxF hxH
  change x ∈ H.disk.carrier at hxH
  rw [H.carrier_eq] at hxH
  simp only [support, mem_iUnion] at hxH
  obtain ⟨A, hA, hxA⟩ := hxH
  rw [← tile_regular A] at hxA
  obtain ⟨y, hyF, hyA⟩ := mem_closure_iff_nhds.1 hxA _ (isOpen_interior.mem_nhds hxF)
  have hne : F ≠ A := fun h => hFH (h ▸ hA)
  exact Set.disjoint_left.1 (S.disjoint hF (H.faces_sub hA) hne) hyF hyA

private lemma qo_tile_sq (M : MeshConstants P) (F : PlacedTile P) {x y : Pt} (hx : x ∈ F.carrier)
    (hy : y ∈ F.carrier) : y ∈ square x M.D :=
  ⟨by rw [abs_sub_comm]; exact rg_tile_coord M F hx hy 0, by rw [abs_sub_comm]; exact rg_tile_coord M F hx hy 1⟩

private lemma qo_sq_trans {x y z : Pt} {r s : ℝ} (h1 : y ∈ square x r) (h2 : z ∈ square y s) : z ∈ square x (r + s) := by
  refine ⟨?_, ?_⟩
  · have := abs_sub_le (z 0) (y 0) (x 0); linarith [h1.1, h2.1]
  · have := abs_sub_le (z 1) (y 1) (x 1); linarith [h1.2, h2.2]

private lemma qo_sq_symm {x y : Pt} {r : ℝ} (h : y ∈ square x r) : x ∈ square y r :=
  ⟨by rw [abs_sub_comm]; exact h.1, by rw [abs_sub_comm]; exact h.2⟩

private lemma qo_sq_of_dist {x y : Pt} {r : ℝ} (h : dist x y ≤ r) : y ∈ square x r :=
  ⟨by rw [abs_sub_comm]; exact (rg_coord_sub_le x y 0).trans h, by rw [abs_sub_comm]; exact (rg_coord_sub_le x y 1).trans h⟩

private lemma qo_sum_sub_square (c : Pt) (a r : ℝ) : square c a + Binf r ⊆ square c (a + r) := by
  intro x hx
  obtain ⟨s, hs, b, hb, rfl⟩ := Set.mem_add.1 hx
  refine ⟨?_, ?_⟩
  · simp only [PiLp.add_apply]
    have := abs_add_le (s 0 - c 0) (b 0)
    rw [show s 0 + b 0 - c 0 = s 0 - c 0 + b 0 by ring]; linarith [hs.1, hb.1]
  · simp only [PiLp.add_apply]
    have := abs_add_le (s 1 - c 1) (b 1)
    rw [show s 1 + b 1 - c 1 = s 1 - c 1 + b 1 by ring]; linarith [hs.2, hb.2]

/-- the band containing `∂H` -/
private lemma qo_band {S : Patch P} (H : FaceGroup S.tiles) {c : Pt} {a d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hHl : square c a + Binf (2 * d) ⊆ H.carrier) (hHu : H.carrier ⊆ square c a + Binf (3 * d))
    {x : Pt} (hx : x ∈ frontier H.carrier) :
    x ∈ square c (a + 3 * d) ∧ (a + 2 * d ≤ |x 0 - c 0| ∨ a + 2 * d ≤ |x 1 - c 1|) := by
  have hcl : IsClosed H.carrier := H.disk.compact.isClosed
  have hxH : x ∈ H.carrier := hcl.frontier_subset hx
  refine ⟨qo_sum_sub_square c a (3 * d) (hHu hxH), ?_⟩
  by_contra hcon
  push_neg at hcon
  have hopen : IsOpen {y : Pt | |y 0 - c 0| < a + 2 * d ∧ |y 1 - c 1| < a + 2 * d} := by
    have h0 : Continuous fun y : Pt => y 0 := PiLp.continuous_apply 2 _ 0
    have h1 : Continuous fun y : Pt => y 1 := PiLp.continuous_apply 2 _ 1
    exact (isOpen_lt ((h0.sub continuous_const).abs) continuous_const).inter
      (isOpen_lt ((h1.sub continuous_const).abs) continuous_const)
  have hsub : {y : Pt | |y 0 - c 0| < a + 2 * d ∧ |y 1 - c 1| < a + 2 * d} ⊆ H.carrier := by
    intro y hy
    exact hHl (rg_square_add ha (by linarith) ⟨hy.1.le, hy.2.le⟩)
  have : x ∈ interior H.carrier := interior_maximal hsub hopen hcon
  exact hx.2 this

/-- an outside-anchored face at a boundary point -/
private lemma qo_outer_face {S : Patch P} (H : FaceGroup S.tiles) {K : Set Pt} (hHa : H.OutsideAnchored K)
    {x : Pt} (hx : x ∈ frontier H.carrier) :
    ∃ m : Fin H.disk.n, x ∈ H.disk.side m ∧ ∃ F ∈ S.tiles, F ∉ H.faces ∧ HasEdge F (H.disk.side m) ∧
      x ∈ F.carrier ∧ (interior F.carrier ∩ Kᶜ).Nonempty := by
  change x ∈ frontier H.disk.carrier at hx
  rw [H.disk.frontier_eq] at hx
  obtain ⟨m, hm⟩ := mem_iUnion.1 hx
  obtain ⟨F, hF, hFH, hE, hne⟩ := hHa m
  refine ⟨m, hm, F, hF, hFH, hE, ?_, hne⟩
  obtain ⟨i, hi⟩ := hE
  exact tile_side_subset F i (hi ▸ hm)

/-- a point outside a square is beyond one of its four sides -/
private lemma qo_exists_dir {c z : Pt} {r : ℝ} (hz : z ∉ square c r) : ∃ k : Fin 4, r < qoCo k (z - c) := by
  rw [qo_square_iff] at hz
  push_neg at hz
  exact hz

private lemma qo_coords_lt (k : Fin 4) (v : Pt) {r : ℝ} (h1 : |qoCo k v| < r) (h2 : |qoCo (k + 1) v| < r) :
    |v 0| < r ∧ |v 1| < r := by
  fin_cases k <;> simp [qoCo, qoD, mkPt] at h1 h2 ⊢ <;> first | exact ⟨h1, h2⟩ | exact ⟨h2, h1⟩

private lemma qoCo_abs_le_of_sq {c x : Pt} {r : ℝ} (hx : x ∈ square c r) (k : Fin 4) : |qoCo k (x - c)| ≤ r :=
  qo_abs_coord_le k (x - c) r (by simpa using hx.1) (by simpa using hx.2)

/-- the escape point of `z` in direction `k` onto the boundary of `square c ρ` -/
private def qoEsc (c : Pt) (ρ : ℝ) (k : Fin 4) (z : Pt) : Pt := z + (ρ - qoCo k (z - c)) • qoD k

/-- its perimeter parameter -/
private def qoU (c : Pt) (ρ : ℝ) (k : Fin 4) (z : Pt) : ℝ := 2 * ρ * (k : ℕ) + ρ + qoCo (k + 1) (z - c)

private lemma qo_esc_eq {c z : Pt} {ρ : ℝ} (hρ : 0 < ρ) (k : Fin 4) (h : |qoCo (k + 1) (z - c)| ≤ ρ) :
    qoEsc c ρ k z = qoPc c ρ (qoU c ρ k z) := by
  rw [abs_le] at h
  unfold qoEsc qoPc qoU
  rw [qo_pos_side k hρ h.1 h.2]
  have := qo_decomp k (z - c)
  rw [show z = c + (z - c) by abel, this]
  have e1 : qoCo k (c + (qoCo k (z - c) • qoD k + qoCo (k + 1) (z - c) • qoD (k + 1)) - c) = qoCo k (z - c) := by
    rw [show c + (qoCo k (z - c) • qoD k + qoCo (k + 1) (z - c) • qoD (k + 1)) - c =
      qoCo k (z - c) • qoD k + qoCo (k + 1) (z - c) • qoD (k + 1) by abel, qoCo_add, qoCo_smul, qoCo_smul,
      qoCo_self, qoCo_next]; ring
  have e2 : qoCo (k + 1) (c + (qoCo k (z - c) • qoD k + qoCo (k + 1) (z - c) • qoD (k + 1)) - c) =
      qoCo (k + 1) (z - c) := by
    rw [show c + (qoCo k (z - c) • qoD k + qoCo (k + 1) (z - c) • qoD (k + 1)) - c =
      qoCo k (z - c) • qoD k + qoCo (k + 1) (z - c) • qoD (k + 1) by abel, qoCo_add, qoCo_smul, qoCo_smul,
      qoCo_self, qoCo_next']; ring
  rw [e1, e2]
  module

private lemma qoCo_ray (k : Fin 4) (c z : Pt) (s : ℝ) : qoCo k (z + s • qoD k - c) = qoCo k (z - c) + s := by
  rw [show z + s • qoD k - c = (z - c) + s • qoD k by abel, qoCo_add, qoCo_smul, qoCo_self]; ring

private lemma qoCo_ray' (k : Fin 4) (c z : Pt) (s : ℝ) : qoCo (k + 1) (z + s • qoD k - c) = qoCo (k + 1) (z - c) := by
  rw [show z + s • qoD k - c = (z - c) + s • qoD k by abel, qoCo_add, qoCo_smul, qoCo_next']; ring

private lemma qo_pos_mem_bd {c : Pt} {ρ u : ℝ} (hρ : 0 < ρ) (h0 : 0 ≤ u) (h8 : u ≤ 8 * ρ) :
    |qoPc c ρ u 0 - c 0| = ρ ∨ |qoPc c ρ u 1 - c 1| = ρ := by
  have := (qo_pos_bound hρ h0 h8).2.2
  simpa [qoPc] using this

private lemma qo_pos_mem_sq {c : Pt} {ρ u : ℝ} (hρ : 0 < ρ) (h0 : 0 ≤ u) (h8 : u ≤ 8 * ρ) :
    qoPc c ρ u ∈ square c ρ := by
  have := qo_pos_bound hρ h0 h8
  exact ⟨by simpa [qoPc] using this.1, by simpa [qoPc] using this.2.1⟩

private lemma qoChain_join : ∀ (l₁ : List Pt) (x : Pt) (l₂ : List Pt),
    qoChain (l₁ ++ x :: l₂) = qoChain (l₁ ++ [x]) ∪ qoChain (x :: l₂)
  | [], x, l₂ => by simp [qoChain]
  | [a], x, l₂ => by simp [qoChain]
  | a :: b :: l₁, x, l₂ => by
    have := qoChain_join (b :: l₁) x l₂
    simp only [List.cons_append] at this ⊢
    simp only [qoChain, this, union_assoc]

private lemma qo_sq_far {c : Pt} {ρ a b r1 r2 : ℝ} {x : Pt} (h1 : x ∈ square (qoPc c ρ a) r1)
    (h2 : x ∈ square (qoPc c ρ b) r2) : |a - b| ≤ 2 * (r1 + r2) ∨ 8 * ρ - |a - b| ≤ 2 * (r1 + r2) := by
  have h := qo_sq_trans h2 (qo_sq_symm h1)
  have := qo_pos_L2 (ρ := ρ) (u := a) (u' := b) (M := r1 + r2) ?_ ?_
  · exact this
  · have := h.1; simp only [qoPc, PiLp.add_apply] at this
    rw [show c 0 + existsAnnularSpokes_pos ρ a 0 - (c 0 + existsAnnularSpokes_pos ρ b 0) =
      existsAnnularSpokes_pos ρ a 0 - existsAnnularSpokes_pos ρ b 0 by ring] at this
    linarith
  · have := h.2; simp only [qoPc, PiLp.add_apply] at this
    rw [show c 1 + existsAnnularSpokes_pos ρ a 1 - (c 1 + existsAnnularSpokes_pos ρ b 1) =
      existsAnnularSpokes_pos ρ a 1 - existsAnnularSpokes_pos ρ b 1 by ring] at this
    linarith

private lemma qoPc_not_mem_sq {c : Pt} {ρ h u : ℝ} (hρ : 0 < ρ) (hh : h < ρ) (h0 : 0 ≤ u) (h8 : u ≤ 8 * ρ) :
    qoPc c ρ u ∉ square c h := by
  intro hm
  rcases qo_pos_mem_bd (c := c) hρ h0 h8 with h' | h' <;> [linarith [hm.1]; linarith [hm.2]]

/-- clamped corner parameters of the arc -/
private def qoCl (ρ ua ub : ℝ) (j : ℕ) : ℝ := max ua (min (2 * ρ * j) ub)

private lemma qoCl_good {ρ ua ub : ℝ} (hρ : 0 < ρ) (j : ℕ) (hj : j < 4) :
    qoGood ρ (qoCl ρ ua ub j) (qoCl ρ ua ub (j + 1)) := by
  unfold qoCl qoGood
  push_cast
  by_cases h1 : ub < 2 * ρ * j
  · left
    rw [min_eq_right h1.le, min_eq_right (by nlinarith [h1] : ub ≤ 2 * ρ * ((j : ℝ) + 1))]
  by_cases h2 : 2 * ρ * ((j : ℝ) + 1) < ua
  · left
    have e1 := min_le_left (2 * ρ * ((j : ℝ) + 1)) ub
    have e2 := min_le_left (2 * ρ * (j : ℝ)) ub
    rw [max_eq_left (by nlinarith), max_eq_left (by nlinarith)]
  push_neg at h1 h2
  right
  refine ⟨⟨j, hj⟩, ?_, ?_, ?_⟩
  · exact le_max_of_le_right (le_min le_rfl h1)
  · exact max_le_max le_rfl (min_le_min (by nlinarith) le_rfl)
  · exact max_le (by linarith) (min_le_left _ _ |>.trans (by linarith))

private lemma qoCl_mono {ρ ua ub : ℝ} (hρ : 0 < ρ) (j : ℕ) : qoCl ρ ua ub j ≤ qoCl ρ ua ub (j + 1) := by
  unfold qoCl; push_cast
  exact max_le_max le_rfl (min_le_min (by nlinarith) le_rfl)

private lemma qoCl_zero {ρ ua ub : ℝ} (h0 : 0 ≤ ua) : qoCl ρ ua ub 0 = ua := by
  unfold qoCl; simp only [CharP.cast_eq_zero, mul_zero]
  exact max_eq_left ((min_le_left _ _).trans h0)

private lemma qoCl_four {ρ ua ub : ℝ} (hab : ua ≤ ub) (h8 : ub ≤ 8 * ρ) : qoCl ρ ua ub 4 = ub := by
  unfold qoCl; push_cast
  rw [min_eq_right (by linarith), max_eq_right hab]

private lemma qoCl_mem {ρ ua ub : ℝ} (j : ℕ) (hab : ua ≤ ub) :
    qoCl ρ ua ub j = ua ∨ qoCl ρ ua ub j = ub ∨ qoCl ρ ua ub j = 2 * ρ * j := by
  unfold qoCl
  rcases le_total (2 * ρ * j) ub with h | h
  · rw [min_eq_left h]
    rcases le_total ua (2 * ρ * j) with h' | h'
    · right; right; exact max_eq_right h'
    · left; exact max_eq_left h'
  · rw [min_eq_right h, max_eq_right hab]; right; left; rfl

private def qoArcL (ρ ua ub : ℝ) : List ℝ := [qoCl ρ ua ub 1, qoCl ρ ua ub 2, qoCl ρ ua ub 3, qoCl ρ ua ub 4]

private lemma qoArc_SG {ρ ua ub : ℝ} (hρ : 0 < ρ) : qoSG ρ (qoCl ρ ua ub 0) (qoArcL ρ ua ub) := by
  simp only [qoArcL, qoSG]
  exact ⟨qoCl_mono hρ 0, qoCl_good hρ 0 (by norm_num), qoCl_mono hρ 1, qoCl_good hρ 1 (by norm_num),
    qoCl_mono hρ 2, qoCl_good hρ 2 (by norm_num), qoCl_mono hρ 3, qoCl_good hρ 3 (by norm_num), trivial⟩

private lemma qo_getLastD_app : ∀ (l : List Pt) (x : Pt) (m : List Pt) (d : Pt), (l ++ x :: m).getLastD d = m.getLastD x
  | [], x, m, d => by rw [List.nil_append, List.getLastD_cons]
  | a :: l, x, m, d => by
    rw [List.cons_append, List.getLastD_cons]; exact qo_getLastD_app l x m a

private lemma qo_head_split : ∀ (x : Pt) (L l₁ : List Pt) (y : Pt) (rest : List Pt), x :: L = l₁ ++ y :: rest →
    ∃ m, l₁ ++ [y] = x :: m
  | x, L, [], y, rest, h => ⟨[], by simp at h ⊢; exact h.1.symm⟩
  | x, L, a :: l₁, y, rest, h => ⟨l₁ ++ [y], by simp at h ⊢; exact h.1.symm⟩

private lemma qo_last_split : ∀ (l₁ : List Pt) (y : Pt) (l₂ L : List Pt) (x : Pt), l₁ ++ y :: l₂ = L ++ [x] →
    ∃ m, y :: l₂ = m ++ [x]
  | [], y, l₂, L, x, h => ⟨L, by simpa using h⟩
  | a :: l₁, y, l₂, [], x, h => by simp at h
  | a :: l₁, y, l₂, b :: L, x, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    exact qo_last_split l₁ y l₂ L x h.2

private lemma qo_no_corner {ρ : ℝ} (hρ : 0 < ρ) (k j : ℕ) (h1 : 2 * ρ * k < 2 * ρ * j) (h2 : 2 * ρ * j < 2 * ρ * k + 2 * ρ) :
    False := by
  have a : (k : ℝ) < j := lt_of_mul_lt_mul_left h1 (by positivity)
  have b : (j : ℝ) < k + 1 := lt_of_mul_lt_mul_left (by linarith : 2 * ρ * (j : ℝ) < 2 * ρ * (k + 1)) (by positivity)
  have a' : k < j := by exact_mod_cast a
  have b' : j < k + 1 := by exact_mod_cast b
  omega

private lemma qo_same_side {ρ u : ℝ} (hρ : 0 < ρ) (k k' : Fin 4) (h1 : 2 * ρ * (k : ℕ) < u) (h2 : u < 2 * ρ * (k : ℕ) + 2 * ρ)
    (h1' : 2 * ρ * (k' : ℕ) ≤ u) (h2' : u ≤ 2 * ρ * (k' : ℕ) + 2 * ρ) : k' = k := by
  have a : ((k' : ℕ) : ℝ) < (k : ℕ) + 1 :=
    lt_of_mul_lt_mul_left (by linarith : 2 * ρ * ((k' : ℕ) : ℝ) < 2 * ρ * ((k : ℕ) + 1)) (by positivity)
  have b : ((k : ℕ) : ℝ) < (k' : ℕ) + 1 :=
    lt_of_mul_lt_mul_left (by linarith : 2 * ρ * ((k : ℕ) : ℝ) < 2 * ρ * ((k' : ℕ) + 1)) (by positivity)
  have a' : (k' : ℕ) < (k : ℕ) + 1 := by exact_mod_cast a
  have b' : (k : ℕ) < (k' : ℕ) + 1 := by exact_mod_cast b
  exact Fin.ext (by omega)

private lemma qo_jrot_smul (a : ℝ) (v : Pt) : jrot (a • v) = a • jrot v := by
  apply pt_ext <;> simp [jrot_apply0, jrot_apply1]

/-- the separating polygon -/
private def qoLam (c : Pt) (ρ ua ub : ℝ) (pa : Pt) (la lb : List Pt) (pb : Pt) (lm : List Pt) : List Pt :=
  pa :: (la ++ ((qoCl ρ ua ub 0 :: qoArcL ρ ua ub).map (qoPc c ρ) ++ (lb ++ pb :: lm)))

private lemma qoLam_curve {c : Pt} {ρ ua ub : ℝ} (hρ : 0 < ρ) (hua : 0 ≤ ua) (hab : ua < ub) (hub : ub < 8 * ρ)
    (pa : Pt) (la lb : List Pt) (pb : Pt) (lm : List Pt) :
    polyCurve (qoV (qoLam c ρ ua ub pa la lb pb lm)) ⊆ qoChain (pa :: la ++ [qoPc c ρ ua]) ∪
      qoPc c ρ '' Icc ua ub ∪ qoChain (qoPc c ρ ub :: lb ++ [pb]) ∪ qoChain (pb :: lm ++ [pa]) := by
  have h0 := qoCl_zero (ρ := ρ) (ub := ub) hua
  have h4 := qoCl_four (ρ := ρ) hab.le hub.le
  have harc := qo_arc_chain (c := c) hρ _ _ (qoArc_SG (ua := ua) (ub := ub) hρ)
  simp only [qoArcL, List.getLastD_cons, List.getLastD_nil, h0, h4] at harc
  have hM := qoChain_snoc pb lm pa
  intro x hx
  have := qo_polyCurve_subset _ _ hx
  unfold qoLam at this
  rw [show la ++ ((qoCl ρ ua ub 0 :: qoArcL ρ ua ub).map (qoPc c ρ) ++ (lb ++ pb :: lm)) =
      la ++ qoPc c ρ ua :: ([qoPc c ρ (qoCl ρ ua ub 1), qoPc c ρ (qoCl ρ ua ub 2), qoPc c ρ (qoCl ρ ua ub 3)] ++
        qoPc c ρ ub :: (lb ++ pb :: lm)) by simp [qoArcL, h0, h4]] at this
  rw [qo_getLastD_app, qo_getLastD_app, qo_getLastD_app, ← List.cons_append] at this
  set a1 := qoPc c ρ ua
  set bU := qoPc c ρ ub
  set mid := [qoPc c ρ (qoCl ρ ua ub 1), qoPc c ρ (qoCl ρ ua ub 2), qoPc c ρ (qoCl ρ ua ub 3)]
  have E1 := qoChain_join (pa :: la) a1 (mid ++ bU :: (lb ++ pb :: lm))
  have E2 : qoChain (a1 :: (mid ++ bU :: (lb ++ pb :: lm))) = qoChain (a1 :: mid ++ [bU]) ∪
      qoChain (bU :: (lb ++ pb :: lm)) := qoChain_join (a1 :: mid) bU (lb ++ pb :: lm)
  have E3 : qoChain (bU :: (lb ++ pb :: lm)) = qoChain (bU :: lb ++ [pb]) ∪ qoChain (pb :: lm) :=
    qoChain_join (bU :: lb) pb lm
  rw [E1, E2, E3] at this
  have harc' : qoChain (a1 :: mid ++ [bU]) ⊆ qoPc c ρ '' Icc ua ub := by
    refine subset_trans ?_ harc; simp [a1, bU, mid]
  rw [hM]
  rcases this with ((h | h | h | h) | h)
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr (harc' h)))
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

private lemma qoD_ne (k : Fin 4) : qoD k ≠ 0 := by
  intro h; have := qoCo_self k; rw [h] at this; simp [qoCo] at this

private lemma qoLam_jump {c : Pt} {ρ ua ub : ℝ} (hρ : 0 < ρ) (hua : 0 ≤ ua) (hab : ua < ub) (hub : ub < 8 * ρ)
    (pa : Pt) (la lb : List Pt) (pb : Pt) (lm : List Pt) (k : Fin 4) {u : ℝ} (hu1 : 2 * ρ * (k : ℕ) < u)
    (hu2 : u < 2 * ρ * (k : ℕ) + 2 * ρ) (hu : u ∈ Ioo ua ub)
    (hA : qoPc c ρ u ∉ qoChain (pa :: la ++ [qoPc c ρ ua])) (hB : qoPc c ρ u ∉ qoChain (qoPc c ρ ub :: lb ++ [pb]))
    (hM : qoPc c ρ u ∉ qoChain (pb :: lm ++ [pa])) :
    ∃ δ > 0, ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      wind (qoV (qoLam c ρ ua ub pa la lb pb lm)) (qoPc c ρ u + (-(t * δ)) • qoD k) -
        wind (qoV (qoLam c ρ ua ub pa la lb pb lm)) (qoPc c ρ u + (t * δ) • qoD k) = 2 * Real.pi := by
  have h0 := qoCl_zero (ρ := ρ) (ub := ub) hua
  have h4 := qoCl_four (ρ := ρ) hab.le hub.le
  set P := qoPc c ρ with hP
  have hlast : (qoArcL ρ ua ub).getLastD (qoCl ρ ua ub 0) = ub := by simp [qoArcL, h4]
  have hnot : u ∉ qoArcL ρ ua ub := by
    intro hmem
    have key : ∀ j : ℕ, u ≠ qoCl ρ ua ub j := by
      intro j hj
      rcases qoCl_mem (ρ := ρ) j hab.le with h | h | h
      · rw [h] at hj; exact absurd hj (ne_of_gt hu.1)
      · rw [h] at hj; exact absurd hj (ne_of_lt hu.2)
      · rw [h] at hj; exact qo_no_corner hρ (k : ℕ) j (by linarith) (by linarith)
    simp only [qoArcL, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h <;> exact key _ h
  obtain ⟨l₁, l₂, s, s', k', heq, hsu, hus', hk1, hk2, hn1, hn2⟩ := qo_arc_split (c := c) hρ _ _ (qoArc_SG hρ)
    (by rw [h0]; exact hua) (by rw [hlast]; exact hub) u (by rw [h0]; exact hu.1) (by rw [hlast]; exact hu.2) hnot
  have hk' : k' = k := qo_same_side hρ k k' hu1 hu2 (by linarith) (by linarith)
  rw [hk'] at hk1 hk2
  rw [← hP] at heq hn1 hn2
  have hΛ : qoLam c ρ ua ub pa la lb pb lm = (pa :: la ++ l₁) ++ P s :: P s' :: (l₂ ++ (lb ++ pb :: lm)) := by
    unfold qoLam; rw [heq]; simp
  have heq' : P (qoCl ρ ua ub 0) :: (qoArcL ρ ua ub).map P = l₁ ++ P s :: P s' :: l₂ := by
    rw [← heq]; rfl
  obtain ⟨m, hm⟩ := qo_head_split _ _ l₁ (P s) (P s' :: l₂) heq'
  have heq2 : (l₁ ++ [P s]) ++ P s' :: l₂ = [P ua, P (qoCl ρ ua ub 1), P (qoCl ρ ua ub 2), P (qoCl ρ ua ub 3)] ++
      [P ub] := by
    rw [List.append_assoc, List.singleton_append, ← heq']; simp [qoArcL, h0, h4]
  obtain ⟨m', hm'⟩ := qo_last_split _ _ _ _ _ heq2
  have hsub : P s' - P s = (s' - s) • qoD (k + 1) := by
    simp only [hP, qoPc]
    rw [show c + existsAnnularSpokes_pos ρ s' - (c + existsAnnularSpokes_pos ρ s) =
      existsAnnularSpokes_pos ρ s' - existsAnnularSpokes_pos ρ s by abel]
    exact qo_pos_sub k hρ hk1 (by linarith) (by linarith) hk2
  have hsubu : P u - P s = (u - s) • qoD (k + 1) := by
    simp only [hP, qoPc]
    rw [show c + existsAnnularSpokes_pos ρ u - (c + existsAnnularSpokes_pos ρ s) =
      existsAnnularSpokes_pos ρ u - existsAnnularSpokes_pos ρ s by abel]
    exact qo_pos_sub k hρ hk1 (by linarith) (by linarith) (by linarith)
  have hab' : P s ≠ P s' := by
    intro h
    have : (s' - s) • qoD (k + 1) = 0 := by rw [← hsub, h, sub_self]
    rcases smul_eq_zero.1 this with h' | h'
    · linarith
    · exact qoD_ne _ h'
  have hq : P u ∈ openSegment ℝ (P s) (P s') := by
    rw [openSegment_eq_image']
    refine ⟨(u - s) / (s' - s), ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩, ?_⟩
    simp only
    rw [hsub, smul_smul, div_mul_cancel₀ _ (by linarith : s' - s ≠ 0), ← hsubu]; abel
  have h1 : P u ∉ qoChain ((pa :: la ++ l₁) ++ [P s]) := by
    rw [List.append_assoc, hm, qoChain_join, ← hm]
    rintro (h | h)
    · exact hA (by rw [h0] at h; exact h)
    · exact hn1 h
  have h2 : P u ∉ qoChain (P s' :: (l₂ ++ (lb ++ pb :: lm))) := by
    rw [show P s' :: (l₂ ++ (lb ++ pb :: lm)) = m' ++ P ub :: (lb ++ pb :: lm) by
      rw [← List.cons_append, hm']; simp, qoChain_join,
      show qoChain (P ub :: (lb ++ pb :: lm)) = qoChain (P ub :: lb ++ [pb]) ∪ qoChain (pb :: lm) from
        qoChain_join (P ub :: lb) pb lm, ← hm']
    rintro (h | h | h)
    · exact hn2 h
    · exact hB h
    · exact hM (by rw [qoChain_snoc]; exact Or.inl h)
  have h3 : P u ∉ segment ℝ ((l₂ ++ (lb ++ pb :: lm)).getLastD (P s')) ((pa :: la ++ l₁).headD (P s)) := by
    rw [← List.append_assoc, qo_getLastD_app]
    intro h
    exact hM (by rw [qoChain_snoc]; exact Or.inr (by simpa using h))
  refine ⟨s' - s, by linarith, ?_⟩
  have J := qo_wind_jump _ _ _ _ hab' hq h1 h2 h3
  rw [← hΛ, hsub, qo_jrot_smul, qoD_jrot, show k + 1 + 1 = k + 2 by rw [add_assoc]; rfl, qoD_add_two] at J
  refine J.mono fun t ht => ?_
  rw [← ht, show t • (s' - s) • -qoD k = -(t * (s' - s)) • qoD k by module,
    show -t • (s' - s) • -qoD k = (t * (s' - s)) • qoD k by module]

private lemma qo_core {c : Pt} {ρ h r e : ℝ} (hρ : 0 < ρ) (hh : h < ρ) (he : 0 ≤ e) {Hc : Set Pt} (hHs : Hc ⊆ square c h)
    {pa pb : Pt} (hpa : pa ∈ Hc) (hpb : pb ∈ Hc) {ua ub : ℝ} (hua : 0 ≤ ua) (hab : ua < ub) (hub : ub < 8 * ρ)
    (la lb lm : List Pt)
    (hA : qoChain (pa :: la ++ [qoPc c ρ ua]) ⊆ insert pa ((square c ρ ∩ square (qoPc c ρ ua) r) \ Hc))
    (hB : qoChain (qoPc c ρ ub :: lb ++ [pb]) ⊆ insert pb ((square c ρ ∩ square (qoPc c ρ ub) r) \ Hc))
    (hM : qoChain (pb :: lm ++ [pa]) ⊆ insert pa (insert pb (interior Hc))) :
    ∃ W : ℝ,
      (∀ x ∈ Hc, x ∉ interior Hc → x ≠ pa → x ≠ pb → x ∉ polyCurve (qoV (qoLam c ρ ua ub pa la lb pb lm))) ∧
      (∀ x ∉ Hc, |x 0 - c 0| < ρ → |x 1 - c 1| < ρ → x ∉ square (qoPc c ρ ua) r → x ∉ square (qoPc c ρ ub) r →
        x ∉ polyCurve (qoV (qoLam c ρ ua ub pa la lb pb lm))) ∧
      ∀ (z : Pt) (k : Fin 4), h < qoCo k (z - c) → qoCo k (z - c) < ρ → |qoCo (k + 1) (z - c)| < ρ →
        z ∈ square (qoPc c ρ (qoU c ρ k z)) e →
        2 * (e + r) < |qoU c ρ k z - ua| → 2 * (e + r) < 8 * ρ - |qoU c ρ k z - ua| →
        2 * (e + r) < |qoU c ρ k z - ub| → 2 * (e + r) < 8 * ρ - |qoU c ρ k z - ub| →
        (qoU c ρ k z ∉ Icc ua ub → wind (qoV (qoLam c ρ ua ub pa la lb pb lm)) z = W) ∧
        (qoU c ρ k z ∈ Ioo ua ub → wind (qoV (qoLam c ρ ua ub pa la lb pb lm)) z ≠ W) := by
  set V := qoV (qoLam c ρ ua ub pa la lb pb lm) with hV
  have hcur := qoLam_curve (c := c) hρ hua hab hub pa la lb pb lm
  rw [← hV] at hcur
  have hh0 : 0 ≤ h := (abs_nonneg _).trans (hHs hpa).1
  have hHρ : Hc ⊆ square c ρ := fun x hx => ⟨(hHs hx).1.trans hh.le, (hHs hx).2.trans hh.le⟩
  have harcB : ∀ v ∈ Icc ua ub, qoPc c ρ v ∉ square c h := fun v hv =>
    qoPc_not_mem_sq hρ hh (by linarith [hv.1]) (by linarith [hv.2])
  have hsq : polyCurve V ⊆ square c ρ := by
    intro x hx
    rcases hcur hx with ((h1 | h1) | h1) | h1
    · rcases hA h1 with rfl | h2
      · exact hHρ hpa
      · exact h2.1.1
    · obtain ⟨v, hv, rfl⟩ := h1; exact qo_pos_mem_sq hρ (by linarith [hv.1]) (by linarith [hv.2])
    · rcases hB h1 with rfl | h2
      · exact hHρ hpb
      · exact h2.1.1
    · rcases hM h1 with rfl | rfl | h2
      · exact hHρ hpa
      · exact hHρ hpb
      · exact hHρ (interior_subset h2)
  have hgen : ∀ x ∉ Hc, |x 0 - c 0| < ρ → |x 1 - c 1| < ρ → x ∉ square (qoPc c ρ ua) r →
      x ∉ square (qoPc c ρ ub) r → x ∉ polyCurve V := by
    intro x hx h0 h1 hxa hxb hxc
    rcases hcur hxc with ((h2 | h2) | h2) | h2
    · rcases hA h2 with rfl | h3
      · exact hx hpa
      · exact hxa h3.1.2
    · obtain ⟨v, hv, rfl⟩ := h2
      rcases qo_pos_mem_bd (c := c) (u := v) hρ (by linarith [hv.1]) (by linarith [hv.2]) with h3 | h3 <;> linarith
    · rcases hB h2 with rfl | h3
      · exact hx hpb
      · exact hxb h3.1.2
    · rcases hM h2 with rfl | rfl | h3
      · exact hx hpa
      · exact hx hpb
      · exact hx (interior_subset h3)
  set far := mkPt (c 0 + (ρ + 1)) (c 1 + (ρ + 1)) with hfar_def
  have hfar : ∀ y ∉ square c ρ, wind V y = wind V far := by
    intro y hy
    have hO : (square c ρ)ᶜ ⊆ (polyCurve V)ᶜ := compl_subset_compl.2 hsq
    have hy' := rg_far_mem hρ.le hO hy
    have hfO : far ∈ (polyCurve V)ᶜ := by
      apply hO
      intro hm
      have := hm.1
      rw [hfar_def, rg_mkPt0, show c 0 + (ρ + 1) - c 0 = ρ + 1 by ring, abs_of_pos (by linarith)] at this
      linarith
    exact wind_const_of_preconnected isPreconnected_connectedComponentIn
      (fun x hx => connectedComponentIn_subset _ _ hx) hy' (mem_connectedComponentIn hfO)
  refine ⟨wind V far, ?_, hgen, ?_⟩
  · intro x hx hxi hxa hxb hxc
    rcases hcur hxc with ((h1 | h1) | h1) | h1
    · rcases hA h1 with h2 | h2
      · exact hxa h2
      · exact h2.2 hx
    · obtain ⟨v, hv, rfl⟩ := h1; exact harcB v hv (hHs hx)
    · rcases hB h1 with h2 | h2
      · exact hxb h2
      · exact h2.2 hx
    · rcases hM h1 with h2 | h2 | h2
      · exact hxa h2
      · exact hxb h2
      · exact hxi h2
  intro z k hk1 hk2 hk3 hz f1 f2 f3 f4
  set u := qoU c ρ k z with hu_def
  set s0 := ρ - qoCo k (z - c) with hs0_def
  have hs0 : 0 < s0 := by linarith
  set ray : ℝ → Pt := fun t => z + t • qoD k with hray
  have hq : qoPc c ρ u = ray s0 := (qo_esc_eq hρ k hk3.le).symm
  have hk3' := abs_lt.1 hk3
  have hk4 : ((k : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : (k : ℕ) ≤ 3)
  have hu1 : 2 * ρ * (k : ℕ) < u := by rw [hu_def, qoU]; linarith
  have hu2 : u < 2 * ρ * (k : ℕ) + 2 * ρ := by rw [hu_def, qoU]; linarith
  have hu8 : u < 8 * ρ := by nlinarith
  have hu0 : 0 < u := by nlinarith [(by positivity : (0 : ℝ) ≤ (k : ℕ))]
  have hPu : qoPc c ρ u ∈ square (qoPc c ρ u) e := by simp [square, he]
  have hseg : ∀ t ∈ Icc 0 s0, ray t ∈ square (qoPc c ρ u) e := by
    intro t ht
    have := (rg_square_convex (qoPc c ρ u) e).add_smul_sub_mem hz hPu
      ⟨div_nonneg ht.1 hs0.le, (div_le_one hs0).2 ht.2⟩
    rw [hq] at this ⊢
    convert this using 1
    simp only [hray]
    rw [show z + s0 • qoD k - z = s0 • qoD k by abel, smul_smul, div_mul_cancel₀ _ hs0.ne']
  have hfA : ∀ x ∈ square (qoPc c ρ u) e, x ∉ square (qoPc c ρ ua) r := fun x h1 h2 => by
    rcases qo_sq_far h1 h2 with h3 | h3 <;> linarith
  have hfB : ∀ x ∈ square (qoPc c ρ u) e, x ∉ square (qoPc c ρ ub) r := fun x h1 h2 => by
    rcases qo_sq_far h1 h2 with h3 | h3 <;> linarith
  have hin : ∀ t, 0 ≤ t → t < s0 → ray t ∉ polyCurve V := by
    intro t ht0 ht1
    have hc1 : qoCo k (ray t - c) = qoCo k (z - c) + t := qoCo_ray k c z t
    have hc2 : qoCo (k + 1) (ray t - c) = qoCo (k + 1) (z - c) := qoCo_ray' k c z t
    have hlt := qo_coords_lt k (ray t - c) (r := ρ) (abs_lt.2 ⟨by linarith, by linarith⟩) (by rw [hc2]; exact hk3)
    simp only [PiLp.sub_apply] at hlt
    refine hgen _ ?_ hlt.1 hlt.2 (hfA _ (hseg t ⟨ht0, ht1.le⟩)) (hfB _ (hseg t ⟨ht0, ht1.le⟩))
    intro hm
    have := (qo_square_iff c _ h).1 (hHs hm) k
    linarith
  have hout : ∀ t, s0 < t → ray t ∉ square c ρ := by
    intro t ht hm
    have := (qo_square_iff c _ ρ).1 hm k
    rw [qoCo_ray] at this
    linarith
  have hsw : ∀ t1, 0 ≤ t1 → (∀ t ∈ Icc 0 t1, ray t ∉ polyCurve V) → wind V z = wind V (ray t1) := by
    intro t1 ht1 hav
    have hcont : Continuous ray := continuous_const.add (continuous_id.smul continuous_const)
    have h0 : ray 0 = z := by simp [hray]
    rw [← h0]
    exact wind_const_of_preconnected (isPreconnected_Icc.image ray hcont.continuousOn)
      (by rintro _ ⟨t, ht, rfl⟩; exact hav t ht) ⟨0, ⟨le_rfl, ht1⟩, rfl⟩ ⟨t1, ⟨ht1, le_rfl⟩, rfl⟩
  have hqHc : qoPc c ρ u ∉ Hc := fun hm => qoPc_not_mem_sq hρ hh hu0.le hu8.le (hHs hm)
  have hqA : qoPc c ρ u ∉ qoChain (pa :: la ++ [qoPc c ρ ua]) := by
    intro h1
    rcases hA h1 with h2 | h2
    · exact hqHc (h2 ▸ hpa)
    · exact hfA _ hPu h2.1.2
  have hqB : qoPc c ρ u ∉ qoChain (qoPc c ρ ub :: lb ++ [pb]) := by
    intro h1
    rcases hB h1 with h2 | h2
    · exact hqHc (h2 ▸ hpb)
    · exact hfB _ hPu h2.1.2
  have hqM : qoPc c ρ u ∉ qoChain (pb :: lm ++ [pa]) := by
    intro h1
    rcases hM h1 with h2 | h2 | h2
    · exact hqHc (h2 ▸ hpa)
    · exact hqHc (h2 ▸ hpb)
    · exact hqHc (interior_subset h2)
  constructor
  · intro hnot
    have hqnot : qoPc c ρ u ∉ polyCurve V := by
      intro h1
      rcases hcur h1 with ((h2 | h2) | h2) | h2
      · exact hqA h2
      · obtain ⟨v, hv, hv'⟩ := h2
        have hs1 : qoPc c ρ u ∈ square (qoPc c ρ v) 0 := by rw [← hv']; simp [square]
        have hs2 : qoPc c ρ u ∈ square (qoPc c ρ u) 0 := by simp [square]
        have hlt : |v - u| < 8 * ρ := abs_lt.2 ⟨by linarith [hv.1], by linarith [hv.2]⟩
        rcases qo_sq_far hs1 hs2 with h3 | h3
        · have : v = u := by
            have := abs_nonneg (v - u)
            have h4 : |v - u| = 0 := by linarith
            linarith [abs_eq_zero.1 h4]
          exact hnot (this ▸ hv)
        · linarith
      · exact hqB h2
      · exact hqM h2
    rw [hsw (s0 + 1) (by linarith) ?_]
    · exact hfar _ (hout _ (by linarith))
    intro t ht
    rcases lt_trichotomy t s0 with h1 | h1 | h1
    · exact hin t ht.1 h1
    · rw [h1, ← hq]; exact hqnot
    · exact fun hm => hout t h1 (hsq hm)
  · intro hIoo
    obtain ⟨δ, hδ, J⟩ := qoLam_jump (c := c) hρ hua hab hub pa la lb pb lm k hu1 hu2 hIoo hqA hqB hqM
    have ev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t * δ < s0 := by
      have : Filter.Tendsto (fun t : ℝ => t * δ) (nhds 0) (nhds 0) := by
        have := ((continuous_id.mul continuous_const).tendsto (0 : ℝ) : Filter.Tendsto (fun t : ℝ => t * δ) _ _)
        simpa using this
      exact (this.mono_left nhdsWithin_le_nhds) (Iio_mem_nhds hs0)
    obtain ⟨t, ht1, ht2, ht3⟩ := (J.and (ev.and self_mem_nhdsWithin)).exists
    have ht3' : 0 < t := ht3
    have e1 : qoPc c ρ u + (-(t * δ)) • qoD k = ray (s0 - t * δ) := by
      rw [hq]; simp only [hray]; rw [sub_eq_add_neg, add_smul, add_assoc]
    have e2 : qoPc c ρ u + (t * δ) • qoD k = ray (s0 + t * δ) := by
      rw [hq]; simp only [hray]; rw [add_smul, add_assoc]
    have htd := mul_pos ht3' hδ
    rw [e1, e2, hfar (ray (s0 + t * δ)) (hout _ (by linarith))] at ht1
    rw [hsw (s0 - t * δ) (by linarith) (fun t' ht' => hin t' ht'.1 (by linarith [ht'.2]))]
    intro heq
    rw [heq, sub_self] at ht1
    linarith [Real.pi_pos]

private lemma qo_halfdisk_pick {U : Set Pt} {p a d : Pt} (hd : d ≠ 0) {r : ℝ} (hr : 0 < r) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hp : jcr d (p - a) = 0) (hU : ∀ x ∈ Metric.ball p r, x ∈ U ↔ 0 < σ * jcr d (x - a)) :
    ∃ y ∈ U, segment ℝ p y ⊆ insert p U := by
  obtain ⟨y, hy, hlt⟩ := exists_near_off_line a hd p hσ hr
  rw [hp, mul_zero] at hlt
  have key : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → p + θ • (y - p) ∈ U := by
    intro θ h0 h1
    have hb : p + θ • (y - p) ∈ Metric.ball p r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos h0, ← dist_eq_norm, dist_comm]
      calc θ * dist p y ≤ 1 * dist p y := by gcongr
        _ < r := by linarith
    have e : jcr d (p + θ • (y - p) - a) = jcr d (p - a) + θ * (jcr d (y - a) - jcr d (p - a)) := by
      simp only [jcr, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hU _ hb, e, hp]
    nlinarith
  refine ⟨y, by simpa using key 1 one_pos le_rfl, ?_⟩
  intro x hx
  rw [segment_eq_image'] at hx
  obtain ⟨θ, hθ, rfl⟩ := hx
  rcases eq_or_lt_of_le hθ.1 with h | h
  · left; rw [← h]; simp
  · right; exact key θ h hθ.2

private lemma qo_open_pick_H (B : PolygonalDisk) (m : Fin B.n) {p : Pt}
    (hp : p ∈ openSegment ℝ (B.vertex m) (B.vertex (finRotate B.n m))) :
    ∃ y ∈ interior B.carrier, segment ℝ p y ⊆ insert p (interior B.carrier) := by
  obtain ⟨r, hr, σ, hσ, hball⟩ := pd_halfdisk B m hp
  have hd : B.vertex (finRotate B.n m) - B.vertex m ≠ 0 := sub_ne_zero.2 (pd_vertex_ne_next B m).symm
  have hpl := ((hball p (Metric.mem_ball_self hr)).1).1 (openSegment_subset_segment _ _ _ hp)
  exact qo_halfdisk_pick hd hr hσ hpl fun x hx => (hball x hx).2.2

private lemma qo_open_pick_F (F : PlacedTile P) {a b p : Pt} (hab : a ≠ b) (hE : HasEdge F (segment ℝ a b))
    (hp : p ∈ openSegment ℝ a b) :
    ∃ y ∈ interior F.carrier, segment ℝ p y ⊆ insert p (interior F.carrier) := by
  obtain ⟨i, hi⟩ := hE
  rw [tile_side_eq] at hi
  have hp' : p ∈ openSegment ℝ (F.vertex i) (F.vertex (finRotate _ i)) := by
    rcases seg_endpoints hab hi.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hp
    · rw [h1, h2, openSegment_symm]; exact hp
  obtain ⟨r, hr, σ, hσ, hball⟩ := tile_halfdisk F i hp'
  have hd : F.vertex (finRotate _ i) - F.vertex i ≠ 0 := sub_ne_zero.2 (tile_vertex_ne_next F i).symm
  have hpl := ((hball p (Metric.mem_ball_self hr)).1).1
    (by rw [tile_side_eq]; exact openSegment_subset_segment _ _ _ hp')
  exact qo_halfdisk_pick hd hr hσ hpl fun x hx => (hball x hx).2.2

private lemma qo_ray_sq (z : Pt) (s : ℝ) (k : Fin 4) : z ∈ square (z + s • qoD k) |s| := by
  fin_cases k <;> simp [square, qoD, mkPt]

private lemma qo_sq_mono {x y : Pt} {r r' : ℝ} (h : y ∈ square x r) (hr : r ≤ r') : y ∈ square x r' :=
  ⟨h.1.trans hr, h.2.trans hr⟩

/-- escape data at a boundary point of `H` -/
private lemma qo_escape {M : MeshConstants P} {S : Patch P} (H : FaceGroup S.tiles) {c : Pt} {a : ℝ} (ha : 0 ≤ a)
    (hHl : square c a + Binf (2 * M.D) ⊆ H.carrier) (hHu : H.carrier ⊆ square c a + Binf (3 * M.D))
    (hHa : H.OutsideAnchored (square c a + Binf (3 * M.D))) {x : Pt} (hx : x ∈ frontier H.carrier)
    (m : Fin H.disk.n) (hxm : x ∈ H.disk.side m) :
    ∃ F ∈ S.tiles, F ∉ H.faces ∧ HasEdge F (H.disk.side m) ∧ x ∈ F.carrier ∧ ∃ z ∈ interior F.carrier, ∃ k : Fin 4,
      a + 3 * M.D < qoCo k (z - c) ∧ qoCo k (z - c) < a + 5 * M.D ∧ |qoCo (k + 1) (z - c)| < a + 5 * M.D ∧
      z ∈ square x M.D ∧ z ∈ square (qoPc c (a + 5 * M.D) (qoU c (a + 5 * M.D) k z)) (2 * M.D) := by
  have hD := M.D_pos
  obtain ⟨F, hF, hFH, hE, hne⟩ := hHa m
  have hxF : x ∈ F.carrier := by
    obtain ⟨i, hi⟩ := hE; exact tile_side_subset F i (hi ▸ hxm)
  refine ⟨F, hF, hFH, hE, hxF, ?_⟩
  obtain ⟨z, hzF, hzK⟩ := hne
  have hzs : z ∉ square c (a + 3 * M.D) := fun h => hzK (rg_square_add ha (by linarith) h)
  obtain ⟨k, hk⟩ := qo_exists_dir hzs
  have hzx : z ∈ square x M.D := qo_tile_sq M F hxF (interior_subset hzF)
  have hxc : x ∈ square c (a + 3 * M.D) := (qo_band H ha hD.le hHl hHu hx).1
  have hzc : z ∈ square c (a + 3 * M.D + M.D) := qo_sq_trans hxc hzx
  have hb : ∀ j, |qoCo j (z - c)| ≤ a + 3 * M.D + M.D := qoCo_abs_le_of_sq hzc
  have hb1 := hb (k + 1)
  have hbk := (abs_le.1 (hb k)).2
  refine ⟨z, hzF, k, hk, by linarith, by linarith, hzx, ?_⟩
  rw [← qo_esc_eq (by linarith) k (by linarith)]
  unfold qoEsc
  refine qo_sq_mono (qo_ray_sq z _ k) ?_
  rw [abs_of_pos (by linarith)]; linarith

/-- the outer gadget at a cut point -/
private lemma qo_gadget {M : MeshConstants P} {S : Patch P} (H : FaceGroup S.tiles) {c : Pt} {a : ℝ} (ha : 0 ≤ a)
    (hHl : square c a + Binf (2 * M.D) ⊆ H.carrier) (hHu : H.carrier ⊆ square c a + Binf (3 * M.D))
    (hHa : H.OutsideAnchored (square c a + Binf (3 * M.D))) {p : Pt} (m : Fin H.disk.n)
    (hp : p ∈ openSegment ℝ (H.disk.vertex m) (H.disk.vertex (finRotate _ m))) :
    ∃ (la : List Pt) (z : Pt) (k : Fin 4), |qoCo (k + 1) (z - c)| < a + 5 * M.D ∧ z ∈ square p M.D ∧
      z ∈ square (qoPc c (a + 5 * M.D) (qoU c (a + 5 * M.D) k z)) (2 * M.D) ∧
      qoChain (p :: la ++ [qoPc c (a + 5 * M.D) (qoU c (a + 5 * M.D) k z)]) ⊆
        insert p ((square c (a + 5 * M.D) ∩ square (qoPc c (a + 5 * M.D) (qoU c (a + 5 * M.D) k z)) (3 * M.D)) \
          H.carrier) := by
  have hD := M.D_pos
  have hpm : p ∈ H.disk.side m := openSegment_subset_segment _ _ _ hp
  have hpf : p ∈ frontier H.carrier := by
    change p ∈ frontier H.disk.carrier
    rw [H.disk.frontier_eq]; exact mem_iUnion.2 ⟨m, hpm⟩
  obtain ⟨F, hF, hFH, hE, hpF, z, hzF, k, hk1, hk2, hk3, hzp, hzu⟩ := qo_escape H ha hHl hHu hHa hpf m hpm
  obtain ⟨y, hyF, hyseg⟩ := qo_open_pick_F F (pd_vertex_ne_next H.disk m) hE hp
  obtain ⟨Q, hQ⟩ := qo_polyPath isOpen_interior (tileDisk F).interior_pathConnected.isConnected.isPreconnected hyF hzF
  refine ⟨y :: Q ++ [z], z, k, hk3, hzp, hzu, ?_⟩
  set ρ := a + 5 * M.D with hρ_def
  set U := qoPc c ρ (qoU c ρ k z) with hU_def
  have hpc : p ∈ square c (a + 3 * M.D) := (qo_band H ha hD.le hHl hHu hpf).1
  have hHs : H.carrier ⊆ square c (a + 3 * M.D) := hHu.trans (qo_sum_sub_square c a _)
  have hintF : interior F.carrier ⊆ (square c ρ ∩ square U (3 * M.D)) \ H.carrier := by
    intro x hx
    have hxF := interior_subset hx
    refine ⟨⟨qo_sq_mono (qo_sq_trans hpc (qo_tile_sq M F hpF hxF)) (by linarith), ?_⟩,
      fun h => Set.disjoint_left.1 (qo_int_disj H hF hFH) hx h⟩
    have := qo_sq_trans hzu (qo_tile_sq M F (interior_subset hzF) hxF)
    exact qo_sq_mono this (by linarith)
  have hk4 : ((k : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : (k : ℕ) ≤ 3)
  have hk0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := by positivity
  have hk3' := abs_lt.1 hk3
  have hUeq : U = z + (ρ - qoCo k (z - c)) • qoD k := (qo_esc_eq (by linarith) k hk3.le).symm
  have hUc : U ∈ square c ρ := qo_pos_mem_sq (by linarith) (by unfold qoU; nlinarith) (by unfold qoU; nlinarith)
  have hzc : z ∈ square c ρ := (hintF hzF).1.1
  have hray : segment ℝ z U ⊆ (square c ρ ∩ square U (3 * M.D)) \ H.carrier := by
    intro w hw
    refine ⟨⟨(rg_square_convex c ρ).segment_subset hzc hUc hw,
      (rg_square_convex U _).segment_subset (qo_sq_mono hzu (by linarith)) (by simp [square]; linarith) hw⟩, ?_⟩
    intro hwH
    rw [segment_eq_image'] at hw
    obtain ⟨θ, hθ, rfl⟩ := hw
    have h1 := (qo_square_iff c _ _).1 (hHs hwH) k
    beta_reduce at h1
    rw [hUeq, show z + θ • (z + (ρ - qoCo k (z - c)) • qoD k - z) = z + (θ * (ρ - qoCo k (z - c))) • qoD k by
      rw [add_sub_cancel_left, smul_smul], qoCo_ray] at h1
    nlinarith [hθ.1]
  have hch : qoChain (p :: (y :: Q ++ [z]) ++ [U]) = segment ℝ p y ∪ (qoChain (y :: Q ++ [z]) ∪ segment ℝ z U) := by
    have := qoChain_snoc y (Q ++ [z]) U
    rw [List.getLastD_concat] at this
    have e : qoChain (y :: ((Q ++ [z]) ++ [U])) = qoChain (y :: Q ++ [z]) ∪ segment ℝ z U := this
    show segment ℝ p y ∪ qoChain (y :: ((Q ++ [z]) ++ [U])) = _
    rw [e]
  rw [hch]
  refine union_subset (hyseg.trans (insert_subset_insert (hintF))) (union_subset ?_ ?_)
  · exact hQ.trans (hintF.trans (subset_insert _ _))
  · exact hray.trans (subset_insert _ _)

private lemma qo_sep {M : MeshConstants P} {S : Patch P} (H : FaceGroup S.tiles) {c : Pt} {a : ℝ} (ha : 0 ≤ a)
    (hHl : square c a + Binf (2 * M.D) ⊆ H.carrier) (hHu : H.carrier ⊆ square c a + Binf (3 * M.D))
    (hHa : H.OutsideAnchored (square c a + Binf (3 * M.D))) {pa pb : Pt} (ma mb : Fin H.disk.n)
    (hpa : pa ∈ openSegment ℝ (H.disk.vertex ma) (H.disk.vertex (finRotate _ ma)))
    (hpb : pb ∈ openSegment ℝ (H.disk.vertex mb) (H.disk.vertex (finRotate _ mb))) :
    ∃ ua ub : ℝ, qoPc c (a + 5 * M.D) ua ∈ square pa (3 * M.D) ∧ qoPc c (a + 5 * M.D) ub ∈ square pb (3 * M.D) ∧
      0 < ua ∧ ua < 8 * (a + 5 * M.D) ∧ 0 < ub ∧ ub < 8 * (a + 5 * M.D) ∧
      (ua < ub → ∃ (f : Pt → ℝ) (W : ℝ),
        (∀ T ⊆ frontier H.carrier, IsPreconnected T → pa ∉ T → pb ∉ T → ∀ x ∈ T, ∀ y ∈ T, f x = f y) ∧
        ∀ x ∈ frontier H.carrier, x ≠ pa → x ≠ pb → ∀ F ∈ S.tiles, F ∉ H.faces → x ∈ F.carrier →
          ∀ z ∈ interior F.carrier, ∀ k : Fin 4, a + 3 * M.D < qoCo k (z - c) → qoCo k (z - c) < a + 5 * M.D →
          |qoCo (k + 1) (z - c)| < a + 5 * M.D → z ∈ square x M.D →
          z ∈ square (qoPc c (a + 5 * M.D) (qoU c (a + 5 * M.D) k z)) (2 * M.D) →
          12 * M.D < |qoU c (a + 5 * M.D) k z - ua| →
          12 * M.D < 8 * (a + 5 * M.D) - |qoU c (a + 5 * M.D) k z - ua| →
          12 * M.D < |qoU c (a + 5 * M.D) k z - ub| →
          12 * M.D < 8 * (a + 5 * M.D) - |qoU c (a + 5 * M.D) k z - ub| →
          (qoU c (a + 5 * M.D) k z ∉ Icc ua ub → f x = W) ∧ (qoU c (a + 5 * M.D) k z ∈ Ioo ua ub → f x ≠ W)) := by
  have hD := M.D_pos
  set ρ := a + 5 * M.D with hρ_def
  have hρ : 0 < ρ := by linarith
  have bnd : ∀ (k : Fin 4) (z : Pt), |qoCo (k + 1) (z - c)| < ρ → 0 < qoU c ρ k z ∧ qoU c ρ k z < 8 * ρ := by
    intro k z hk
    have hk4 : ((k : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : (k : ℕ) ≤ 3)
    have hk0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := by positivity
    have := abs_lt.1 hk
    unfold qoU; constructor <;> nlinarith
  obtain ⟨la, za, ka, hka, hzpa, hzua, hcha⟩ := qo_gadget H ha hHl hHu hHa ma hpa
  obtain ⟨lb0, zb, kb, hkb, hzpb, hzub, hchb⟩ := qo_gadget H ha hHl hHu hHa mb hpb
  refine ⟨qoU c ρ ka za, qoU c ρ kb zb, qo_sq_mono (qo_sq_trans hzpa (qo_sq_symm hzua)) (by linarith),
    qo_sq_mono (qo_sq_trans hzpb (qo_sq_symm hzub)) (by linarith), (bnd ka za hka).1, (bnd ka za hka).2,
    (bnd kb zb hkb).1, (bnd kb zb hkb).2, fun hab => ?_⟩
  set ua := qoU c ρ ka za
  set ub := qoU c ρ kb zb
  have hHs : H.carrier ⊆ square c (a + 3 * M.D) := hHu.trans (qo_sum_sub_square c a _)
  have hcl : IsClosed H.carrier := H.disk.compact.isClosed
  have hfr : ∀ {x}, x ∈ openSegment ℝ (H.disk.vertex ma) (H.disk.vertex (finRotate _ ma)) ∨
      x ∈ openSegment ℝ (H.disk.vertex mb) (H.disk.vertex (finRotate _ mb)) → x ∈ H.carrier := by
    intro x hx
    apply hcl.frontier_subset
    change x ∈ frontier H.disk.carrier
    rw [H.disk.frontier_eq]
    rcases hx with hx | hx
    · exact mem_iUnion.2 ⟨ma, openSegment_subset_segment _ _ _ hx⟩
    · exact mem_iUnion.2 ⟨mb, openSegment_subset_segment _ _ _ hx⟩
  obtain ⟨ya, hya, hsega⟩ := qo_open_pick_H H.disk ma hpa
  obtain ⟨yb, hyb, hsegb⟩ := qo_open_pick_H H.disk mb hpb
  obtain ⟨Pm, hPm⟩ := qo_polyPath isOpen_interior H.disk.interior_pathConnected.isConnected.isPreconnected hyb hya
  have hM : qoChain (pb :: (yb :: Pm ++ [ya]) ++ [pa]) ⊆ insert pa (insert pb (interior H.carrier)) := by
    have := qoChain_snoc yb (Pm ++ [ya]) pa
    rw [List.getLastD_concat] at this
    have e : qoChain (yb :: ((Pm ++ [ya]) ++ [pa])) = qoChain (yb :: Pm ++ [ya]) ∪ segment ℝ ya pa := this
    show segment ℝ pb yb ∪ qoChain (yb :: ((Pm ++ [ya]) ++ [pa])) ⊆ _
    rw [e]
    refine union_subset ?_ (union_subset ?_ ?_)
    · exact hsegb.trans (insert_subset_insert (subset_insert _ _)) |>.trans (insert_comm _ _ _).subset
    · exact hPm.trans ((subset_insert _ _).trans (subset_insert _ _))
    · rw [segment_symm]; exact hsega.trans (insert_subset_insert (subset_insert _ _))
  have hB : qoChain (qoPc c ρ ub :: lb0.reverse ++ [pb]) ⊆
      insert pb ((square c ρ ∩ square (qoPc c ρ ub) (3 * M.D)) \ H.carrier) := by
    rw [show qoPc c ρ ub :: lb0.reverse ++ [pb] = (pb :: lb0 ++ [qoPc c ρ ub]).reverse by simp, qoChain_reverse]
    exact hchb
  obtain ⟨W, hfront, hgen, hz⟩ := qo_core (c := c) (ρ := ρ) (h := a + 3 * M.D) (r := 3 * M.D) (e := 3 * M.D)
    hρ (by linarith) (by linarith) hHs (hfr (Or.inl hpa)) (hfr (Or.inr hpb)) (bnd ka za hka).1.le hab
    (bnd kb zb hkb).2 la lb0.reverse (yb :: Pm ++ [ya]) hcha hB hM
  refine ⟨wind (qoV (qoLam c ρ ua ub pa la lb0.reverse pb (yb :: Pm ++ [ya]))), W, ?_, ?_⟩
  · intro T hTs hT hpaT hpbT x hx y hy
    refine wind_const_of_preconnected hT (fun x hx => ?_) hx hy
    exact hfront x (hcl.frontier_subset (hTs hx)) (hTs hx).2 (fun h => hpaT (h ▸ hx)) (fun h => hpbT (h ▸ hx))
  · intro x hx hxa hxb F hF hFH hxF z hzF k hk1 hk2 hk3 hzx hzu f1 f2 f3 f4
    have hxc : x ∈ square c (a + 3 * M.D) := hHs (hcl.frontier_subset hx)
    have hpre : IsPreconnected (insert x (interior F.carrier)) := by
      refine (tileDisk F).interior_pathConnected.isConnected.isPreconnected.subset_closure
        (subset_insert _ _) ?_
      rw [show interior (tileDisk F).carrier = interior F.carrier from rfl, tile_regular]
      exact insert_subset hxF interior_subset
    have hwz : wind (qoV (qoLam c ρ ua ub pa la lb0.reverse pb (yb :: Pm ++ [ya]))) x =
        wind (qoV (qoLam c ρ ua ub pa la lb0.reverse pb (yb :: Pm ++ [ya]))) z := by
      refine wind_const_of_preconnected hpre ?_ (mem_insert _ _) (mem_insert_of_mem _ hzF)
      intro y hy
      rcases hy with rfl | hy
      · exact hfront y (hcl.frontier_subset hx) hx.2 hxa hxb
      · have hyF := interior_subset hy
        have hyc : y ∈ square c (a + 3 * M.D + M.D) := qo_sq_trans hxc (qo_tile_sq M F hxF hyF)
        have hyu := qo_sq_trans hzu (qo_tile_sq M F (interior_subset hzF) hyF)
        refine hgen y (fun h => Set.disjoint_left.1 (qo_int_disj H hF hFH) hy h)
          (lt_of_le_of_lt hyc.1 (by linarith)) (lt_of_le_of_lt hyc.2 (by linarith)) ?_ ?_
        · intro h; rcases qo_sq_far hyu h with h' | h' <;> linarith
        · intro h; rcases qo_sq_far hyu h with h' | h' <;> linarith
    rw [hwz]
    exact hz z k hk1 hk2 hk3 (qo_sq_mono hzu (by linarith)) (by linarith) (by linarith) (by linarith) (by linarith)

private lemma qo_near_ideal {c : Pt} {N : ℕ} {R D a : ℝ} (hA : 0 < (N : ℝ) * R / 2) (hD : 0 < D)
    (haA : a = (N : ℝ) * R / 2 + R) (hR : 0 ≤ R) (h3 : 3 * D ≤ (N : ℝ) * R / 2)
    {x : Pt} (hx1 : x ∈ square c (a + 3 * D)) (hx2 : a + 2 * D ≤ |x 0 - c 0| ∨ a + 2 * D ≤ |x 1 - c 1|)
    (j : ℕ) (hj : (j : ℝ) * R ≤ 8 * ((N : ℝ) * R / 2)) {D' : ℝ} (hD' : 0 ≤ D')
    (hxr : x ∈ Metric.cthickening D' (existsAnnularSpokes_ray c N R D j)) :
    x ∈ square (qoPc c (a + 5 * D) ((a + 5 * D) / ((N : ℝ) * R / 2) * ((j : ℝ) * R))) (3 * D + 2 * D') := by
  set A := (N : ℝ) * R / 2 with hAdef
  set ρ := a + 5 * D with hρdef
  have hρ : 0 < ρ := by rw [hρdef, haA]; linarith
  have hcpt : IsCompact (existsAnnularSpokes_ray c N R D j) := by
    unfold existsAnnularSpokes_ray; rw [← convexHull_pair]; exact (Set.toFinite _).isCompact_convexHull
  obtain ⟨r, hr, hxr'⟩ := hcpt.exists_infEDist_eq_edist ⟨_, left_mem_segment ℝ _ _⟩ x
  have hdist : dist x r ≤ D' := by
    rw [← edist_le_ofReal hD', ← hxr']; exact Metric.mem_cthickening_iff.1 hxr
  obtain ⟨μ, hμ0, -, hμ⟩ := existsAnnularSpokes_step2_tubes_rayMem hR hD.le hA hr
  have hμ0' : 0 ≤ μ := le_trans (div_nonneg (by linarith) hA.le) hμ0
  set v := existsAnnularSpokes_pos A ((j : ℝ) * R) with hv
  have hvb := qo_pos_bound hA (by positivity) hj
  rw [← hv] at hvb
  have hT : qoPc c ρ (ρ / A * ((j : ℝ) * R)) = c + (ρ / A) • v := by
    unfold qoPc; rw [← qo_pos_scale hA hρ]
  have hxr2 := qo_sq_of_dist (dist_comm x r ▸ hdist)
  have hr0 : r 0 = c 0 + μ * v 0 := by rw [hμ]; simp
  have hr1 : r 1 = c 1 + μ * v 1 := by rw [hμ]; simp
  have hxa := hxr2.1; have hxb := hxr2.2
  rw [hr0] at hxa; rw [hr1] at hxb
  have hc0 := hx1.1; have hc1 := hx1.2
  have hav0 : |μ * v 0| = μ * |v 0| := by rw [abs_mul, abs_of_nonneg hμ0']
  have hav1 : |μ * v 1| = μ * |v 1| := by rw [abs_mul, abs_of_nonneg hμ0']
  have up : μ * A ≤ ρ - 2 * D + D' := by
    rcases hvb.2.2 with h | h
    · have := abs_sub_abs_le_abs_sub (μ * v 0) (x 0 - c 0)
      rw [show μ * v 0 - (x 0 - c 0) = -(x 0 - (c 0 + μ * v 0)) by ring, abs_neg, hav0, h] at this
      linarith
    · have := abs_sub_abs_le_abs_sub (μ * v 1) (x 1 - c 1)
      rw [show μ * v 1 - (x 1 - c 1) = -(x 1 - (c 1 + μ * v 1)) by ring, abs_neg, hav1, h] at this
      linarith
  have lo : ρ - 3 * D - D' ≤ μ * A := by
    rcases hx2 with h | h
    · have := abs_sub_abs_le_abs_sub (x 0 - c 0) (μ * v 0)
      rw [show x 0 - c 0 - μ * v 0 = x 0 - (c 0 + μ * v 0) by ring, hav0] at this
      nlinarith [hvb.1]
    · have := abs_sub_abs_le_abs_sub (x 1 - c 1) (μ * v 1)
      rw [show x 1 - c 1 - μ * v 1 = x 1 - (c 1 + μ * v 1) by ring, hav1] at this
      nlinarith [hvb.2.1]
  have key : ∀ t : ℝ, |t| ≤ A → |(μ - ρ / A) * t| ≤ 3 * D + D' := by
    intro t ht
    rw [abs_mul]
    have e : |μ - ρ / A| * A = |μ * A - ρ| := by
      rw [← abs_of_pos hA, ← abs_mul, abs_of_pos hA]; congr 1; field_simp
    have : |μ * A - ρ| ≤ 3 * D + D' := abs_le.2 ⟨by linarith, by linarith⟩
    calc |μ - ρ / A| * |t| ≤ |μ - ρ / A| * A := by gcongr
      _ ≤ 3 * D + D' := by linarith
  rw [hT]
  refine ⟨?_, ?_⟩
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have := key (v 0) hvb.1
    rw [show x 0 - (c 0 + ρ / A * v 0) = (x 0 - (c 0 + μ * v 0)) + (μ - ρ / A) * v 0 by ring]
    linarith [abs_add_le (x 0 - (c 0 + μ * v 0)) ((μ - ρ / A) * v 0)]
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have := key (v 1) hvb.2.1
    rw [show x 1 - (c 1 + ρ / A * v 1) = (x 1 - (c 1 + μ * v 1)) + (μ - ρ / A) * v 1 by ring]
    linarith [abs_add_le (x 1 - (c 1 + μ * v 1)) ((μ - ρ / A) * v 1)]

private lemma qo_cut_pick (B : PolygonalDisk) {γ : ℝ → Pt} (hγ : IsLoopParam (frontier B.carrier) γ) (t δ : ℝ)
    (hδ : 0 < δ) : ∃ s ∈ Ioo t (t + δ), ∃ m, γ s ∈ openSegment ℝ (B.vertex m) (B.vertex (finRotate _ m)) := by
  by_contra hcon
  push_neg at hcon
  set δ' := min δ 1
  have hδ' : 0 < δ' := lt_min hδ one_pos
  have hmaps : MapsTo γ (Ioo t (t + δ')) (range B.vertex) := by
    intro s hs
    have hs' : s ∈ Ioo t (t + δ) := ⟨hs.1, by linarith [hs.2, min_le_left δ 1]⟩
    have hm := qo_loop_mem hγ s
    rw [B.frontier_eq] at hm
    obtain ⟨m, hm⟩ := mem_iUnion.1 hm
    by_contra hv
    exact hcon s hs' m (mem_openSegment_of_ne_left_right (fun h => hv ⟨m, h⟩) (fun h => hv ⟨_, h⟩) hm)
  obtain ⟨x, hx, y, hy, hxy, he⟩ := (Ioo_infinite (by linarith : t < t + δ')).exists_ne_map_eq_of_mapsTo hmaps
    (finite_range _)
  rw [qo_loop_eq_iff hγ, Int.fract_eq_fract] at he
  obtain ⟨z, hz⟩ := he
  have h1 : (z : ℝ) < 1 := by
    have := min_le_right δ 1; linarith [hx.1, hx.2, hy.1, hy.2]
  have h2 : (-1 : ℝ) < z := by
    have := min_le_right δ 1; linarith [hx.1, hx.2, hy.1, hy.2]
  have : z = 0 := by
    have a1 : z < 1 := by exact_mod_cast h1
    have a2 : -1 < z := by exact_mod_cast h2
    omega
  rw [this, Int.cast_zero, sub_eq_zero] at hz
  exact hxy hz

/-- the winding dichotomy forces one of the two cyclic configurations -/
private lemma qo_case_of_wind {Fr : Set Pt} {γ : ℝ → Pt} (hγ : IsLoopParam Fr γ) {k : ℕ} (t : Fin k → ℝ)
    (ht : ∀ i, t i ∈ Ico (0 : ℝ) 1) (hpos : ∀ i : Fin k, i.val ≠ 1 → 0 < t i) (b : Fin k) (hb : 3 ≤ b.val)
    {s : ℝ} (hbs : t b < s) (hs1 : s < 1) (hsep : ∀ i, i ≠ b → t i ≠ s ∧ (t i < s ↔ t i < t b))
    (f : Pt → ℝ) (W : ℝ)
    (hf : ∀ T ⊆ Fr, IsPreconnected T → γ 0 ∉ T → γ s ∉ T → ∀ x ∈ T, ∀ y ∈ T, f x = f y)
    (h1 : ∀ i : Fin k, 2 ≤ i.val → i.val < b.val → f (γ (t i)) ≠ W)
    (h2 : ∀ i : Fin k, (b.val < i.val ∨ i.val = 0) → f (γ (t i)) = W) :
    ((∀ i : Fin k, 2 ≤ i.val → i.val < b.val → t i < t b) ∧
        (∀ i : Fin k, (b.val < i.val ∨ i.val = 0) → t b < t i)) ∨
      ((∀ i : Fin k, 2 ≤ i.val → i.val < b.val → t b < t i) ∧
        (∀ i : Fin k, (b.val < i.val ∨ i.val = 0) → t i < t b)) := by
  have hs0 : 0 < s := lt_of_le_of_lt (ht b).1 hbs
  have hsub : ∀ {I : Set ℝ}, I ⊆ Ico 0 1 → γ '' I ⊆ Fr := by
    intro I hI; rw [← hγ.2.2.2]; exact image_mono hI
  have hnot : ∀ {I : Set ℝ} {x : ℝ}, I ⊆ Ico 0 1 → x ∈ Ico (0 : ℝ) 1 → x ∉ I → γ x ∉ γ '' I := by
    rintro I x hI hx hxI ⟨y, hy, hyx⟩
    exact hxI (hγ.2.2.1 (hI hy) hx hyx ▸ hy)
  have h01 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, one_pos⟩
  have hs01 : s ∈ Ico (0 : ℝ) 1 := ⟨hs0.le, hs1⟩
  have I1 : Ioo 0 s ⊆ Ico (0 : ℝ) 1 := fun x hx => ⟨hx.1.le, hx.2.trans hs1⟩
  have I2 : Ioo s 1 ⊆ Ico (0 : ℝ) 1 := fun x hx => ⟨hs0.le.trans hx.1.le, hx.2⟩
  have c1 := hf _ (hsub I1) (isPreconnected_Ioo.image _ hγ.1.continuousOn)
    (hnot I1 h01 (fun h => lt_irrefl _ h.1)) (hnot I1 hs01 (fun h => lt_irrefl _ h.2))
  have c2 := hf _ (hsub I2) (isPreconnected_Ioo.image _ hγ.1.continuousOn)
    (hnot I2 h01 (fun h => by linarith [h.1])) (hnot I2 hs01 (fun h => lt_irrefl _ h.1))
  -- same side implies same value
  have same : ∀ i j : Fin k, i.val ≠ 1 → j.val ≠ 1 → i ≠ b → j ≠ b → (t i < s ↔ t j < s) →
      f (γ (t i)) = f (γ (t j)) := by
    intro i j hi hj hib hjb hiff
    rcases lt_or_gt_of_ne (hsep i hib).1 with hi' | hi'
    · exact c1 _ ⟨t i, ⟨hpos i hi, hi'⟩, rfl⟩ _ ⟨t j, ⟨hpos j hj, hiff.1 hi'⟩, rfl⟩
    · have hj' : s < t j := lt_of_le_of_ne (not_lt.1 fun h => absurd (hiff.2 h) (not_lt.2 hi'.le))
        (hsep j hjb).1.symm
      exact c2 _ ⟨t i, ⟨hi', (ht i).2⟩, rfl⟩ _ ⟨t j, ⟨hj', (ht j).2⟩, rfl⟩
  have hk : 4 ≤ k := by have := b.isLt; omega
  set i0 : Fin k := ⟨0, by omega⟩
  set i2 : Fin k := ⟨2, by omega⟩
  have hi0b : i0 ≠ b := fun h => by have := congrArg Fin.val h; simp [i0] at this; omega
  have hi2b : i2 ≠ b := fun h => by have := congrArg Fin.val h; simp [i2] at this; omega
  have hW0 : f (γ (t i0)) = W := h2 i0 (Or.inr rfl)
  have hW2 : f (γ (t i2)) ≠ W := h1 i2 le_rfl (by simp [i2]; omega)
  have ne1 : ∀ i : Fin k, 2 ≤ i.val → i.val ≠ 1 := fun i h => by omega
  have ne1' : ∀ i : Fin k, (b.val < i.val ∨ i.val = 0) → i.val ≠ 1 := fun i h => by omega
  have neb : ∀ i : Fin k, i.val < b.val → i ≠ b := fun i h e => by rw [e] at h; omega
  have neb' : ∀ i : Fin k, (b.val < i.val ∨ i.val = 0) → i ≠ b := fun i h e => by rw [e] at h; omega
  -- t i vs t b comparisons through s
  have tb_ne : ∀ i, i ≠ b → t i ≠ t b := by
    intro i hib e
    have := (hsep i hib).2
    rw [e] at this
    exact lt_irrefl _ (this.1 hbs)
  have lt_iff : ∀ i, i ≠ b → (t i < t b ↔ t i < s) := fun i hib => (hsep i hib).2.symm
  have gt_iff : ∀ i, i ≠ b → (t b < t i ↔ ¬ t i < s) := by
    intro i hib
    rw [← lt_iff i hib]
    exact ⟨fun h => not_lt.2 h.le, fun h => lt_of_le_of_ne (not_lt.1 h) (tb_ne i hib).symm⟩
  have h02 : ¬ ((t i0 < s) ↔ (t i2 < s)) := by
    intro hiff
    exact hW2 ((same i2 i0 (by simp [i2]) (by simp [i0]) hi2b hi0b hiff.symm).trans hW0)
  by_cases hA : t i0 < s
  · right
    have h2s : ¬ t i2 < s := fun h => h02 ⟨fun _ => h, fun _ => hA⟩
    refine ⟨fun i hi hib => ?_, fun i hi => ?_⟩
    · rw [gt_iff i (neb i hib)]
      intro his
      exact h1 i hi hib ((same i i0 (ne1 i hi) (by simp [i0]) (neb i hib) hi0b ⟨fun _ => hA, fun _ => his⟩).trans hW0)
    · rw [lt_iff i (neb' i hi)]
      by_contra his
      exact hW2 ((same i2 i (by simp [i2]) (ne1' i hi) hi2b (neb' i hi)
        ⟨fun h => absurd h h2s, fun h => absurd h his⟩).trans (h2 i hi))
  · left
    have h2s : t i2 < s := by by_contra h; exact h02 ⟨fun h' => absurd h' hA, fun h' => absurd h' h⟩
    refine ⟨fun i hi hib => ?_, fun i hi => ?_⟩
    · rw [lt_iff i (neb i hib)]
      by_contra his
      exact h1 i hi hib ((same i i0 (ne1 i hi) (by simp [i0]) (neb i hib) hi0b
        ⟨fun h => absurd h his, fun h => absurd h hA⟩).trans hW0)
    · rw [gt_iff i (neb' i hi)]
      intro his
      exact hW2 ((same i2 i (by simp [i2]) (ne1' i hi) hi2b (neb' i hi) ⟨fun _ => his, fun _ => h2s⟩).trans
        (h2 i hi))

private lemma qo_cut_near (B : PolygonalDisk) {γ : ℝ → Pt} (hγ : IsLoopParam (frontier B.carrier) γ) (t : ℝ) {D δ0 : ℝ}
    (hD : 0 < D) (hδ0 : 0 < δ0) : ∃ s ∈ Ioo t (t + δ0), dist (γ s) (γ t) < D ∧
      ∃ m, γ s ∈ openSegment ℝ (B.vertex m) (B.vertex (finRotate _ m)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.continuous_iff.1 hγ.1 t D hD
  obtain ⟨s, hs, hm⟩ := qo_cut_pick B hγ t (min δ0 ε) (lt_min hδ0 hε)
  refine ⟨s, ⟨hs.1, hs.2.trans_le (by linarith [min_le_left δ0 ε])⟩, hball s ?_, hm⟩
  rw [Real.dist_eq, abs_of_pos (by linarith [hs.1])]
  linarith [hs.2, min_le_right δ0 ε]

private lemma qo_fin_pos {n : ℕ} (f : Fin n → ℝ) (Q : Fin n → Prop) (h : ∀ i, Q i → 0 < f i) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ i, Q i → δ ≤ f i := by
  classical
  by_cases hne : (Finset.univ.filter Q).Nonempty
  · obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image _ f hne
    refine ⟨min (f i0) 1, lt_min (h i0 (Finset.mem_filter.1 hi0).2) one_pos, min_le_right _ _,
      fun i hi => (min_le_left _ _).trans (hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩))⟩
  · refine ⟨1, one_pos, le_rfl, fun i hi => absurd ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩ hne⟩

private lemma qo_close_norm {ρ L M u ι : ℝ} (hu0 : 0 < u) (hu8 : u < 8 * ρ) (hi1 : L ≤ ι) (hi2 : ι ≤ 8 * ρ - L)
    (hL : M < L) (h : |u - ι| ≤ M ∨ 8 * ρ - |u - ι| ≤ M) : |u - ι| ≤ M := by
  rcases h with h | h
  · exact h
  · exfalso
    rcases le_total 0 (u - ι) with h' | h'
    · rw [abs_of_nonneg h'] at h; linarith
    · rw [abs_of_nonpos h'] at h; linarith

private lemma qo_fract_eq {x : ℝ} {z : ℤ} (h1 : (z : ℝ) ≤ x) (h2 : x < z + 1) : Int.fract x = x - z := by
  rw [Int.fract, Int.floor_eq_iff.2 ⟨h1, h2⟩]

private lemma qo_mulL {L : ℝ} (hL : 0 ≤ L) {i j : ℕ} (h : i + 1 ≤ j) : (i : ℝ) * L + L ≤ j * L := by
  have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
  nlinarith

private lemma qo_far_pos {M ρ d : ℝ} (hM : 0 ≤ M) (h1 : M < d) (h2 : d < 8 * ρ - M) : M < |d| ∧ M < 8 * ρ - |d| := by
  rw [abs_of_pos (by linarith)]; exact ⟨h1, by linarith⟩

private lemma qo_far_neg {M ρ d : ℝ} (hM : 0 ≤ M) (h1 : M < -d) (h2 : -d < 8 * ρ - M) : M < |d| ∧ M < 8 * ρ - |d| := by
  rw [abs_of_neg (by linarith)]; exact ⟨h1, by linarith⟩

set_option maxHeartbeats 1000000 in
private theorem qo_main {M : MeshConstants P} {S : Patch P}
    (c : Pt) {N : ℕ} {R : ℝ} (hN : 2 ≤ N) (hR : 1000 * M.D ≤ R) (H : FaceGroup S.tiles)
    (hHl : square c ((N : ℝ) * R / 2 + R) + Binf (2 * M.D) ⊆ H.carrier)
    (hHu : H.carrier ⊆ square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D))
    (hHa : H.OutsideAnchored (square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D)))
    (w : Fin (4 * N) → Pt) (hw : ∀ j, w j ∈ frontier H.carrier)
    (hwr : ∀ j : Fin (4 * N), w j ∈ Metric.cthickening M.D (existsAnnularSpokes_ray c N R M.D j)) :
    ∃ γo : ℝ → Pt, IsLoopParam (frontier H.carrier) γo ∧ PointsInOrder γo w := by
  have hD := M.D_pos
  set D := M.D with hDdef
  set A := (N : ℝ) * R / 2 with hAdef
  set a := A + R with hadef
  set ρ := a + 5 * D with hρdef
  set L := ρ / A * R with hLdef
  have hR0 : 0 < R := by linarith
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hAR : R ≤ A := by rw [hAdef]; nlinarith
  have hApos : 0 < A := by linarith
  have ha : 0 ≤ a := by linarith
  have hρA : A ≤ ρ := by linarith
  have hLR : R ≤ L := by
    rw [hLdef]
    have : 1 ≤ ρ / A := (one_le_div hApos).2 hρA
    nlinarith
  have hK8 : ((4 * N : ℕ) : ℝ) * L = 8 * ρ := by
    rw [hLdef]; push_cast; field_simp; rw [hAdef]; ring
  have hι : ∀ j : ℕ, (a + 5 * D) / A * ((j : ℝ) * R) = j * L := by intro j; rw [hLdef]; ring
  have hjL : ∀ j : Fin (4 * N), (j : ℝ) * L + L ≤ 8 * ρ := fun j => hK8 ▸ qo_mulL (by linarith) j.isLt
  have hband : ∀ x ∈ frontier H.carrier, x ∈ square c (a + 3 * D) ∧
      (a + 2 * D ≤ |x 0 - c 0| ∨ a + 2 * D ≤ |x 1 - c 1|) := fun x hx => qo_band H ha hD.le hHl hHu hx
  have hnear : ∀ j : Fin (4 * N), w j ∈ square (qoPc c ρ ((j : ℕ) * L)) (5 * D) := by
    intro j
    have hj : ((j : ℕ) : ℝ) * R ≤ 8 * A := by
      have : ((j : ℕ) : ℝ) ≤ 4 * N := by exact_mod_cast (by omega : (j : ℕ) ≤ 4 * N)
      rw [hAdef]; nlinarith
    have := qo_near_ideal hApos hD rfl hR0.le (by linarith) (hband _ (hw j)).1 (hband _ (hw j)).2 j hj hD.le (hwr j)
    rw [hι] at this
    convert this using 2; ring
  -- escape data at the given points
  have hesc : ∀ j : Fin (4 * N), ∃ F ∈ S.tiles, F ∉ H.faces ∧ w j ∈ F.carrier ∧ ∃ z ∈ interior F.carrier,
      ∃ k : Fin 4, a + 3 * D < qoCo k (z - c) ∧ qoCo k (z - c) < ρ ∧ |qoCo (k + 1) (z - c)| < ρ ∧
        z ∈ square (w j) D ∧ z ∈ square (qoPc c ρ (qoU c ρ k z)) (2 * D) := by
    intro j
    have hm := hw j
    change w j ∈ frontier H.disk.carrier at hm
    rw [H.disk.frontier_eq] at hm
    obtain ⟨m, hm⟩ := mem_iUnion.1 hm
    obtain ⟨F, hF, hFH, -, hwF, hrest⟩ := qo_escape H ha hHl hHu hHa (hw j) m hm
    exact ⟨F, hF, hFH, hwF, hrest⟩
  choose F hF hFH hwF z hz k hk1 hk2 hk3 hzw hzu using hesc
  set u : Fin (4 * N) → ℝ := fun j => qoU c ρ (k j) (z j) with hudef
  have hu08 : ∀ j, 0 < u j ∧ u j < 8 * ρ := by
    intro j
    have hk4 : ((k j : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : (k j : ℕ) ≤ 3)
    have hk0 : (0 : ℝ) ≤ ((k j : ℕ) : ℝ) := by positivity
    have := abs_lt.1 (hk3 j)
    simp only [hudef, qoU]; constructor <;> nlinarith
  have hclose : ∀ j : Fin (4 * N), |u j - (j : ℕ) * L| ≤ 16 * D ∨ 8 * ρ - |u j - (j : ℕ) * L| ≤ 16 * D := by
    intro j
    have h1 : qoPc c ρ (u j) ∈ square (qoPc c ρ ((j : ℕ) * L)) (5 * D + D + 2 * D) :=
      qo_sq_trans (qo_sq_trans (hnear j) (hzw j)) (qo_sq_symm (hzu j))
    have h0 : qoPc c ρ (u j) ∈ square (qoPc c ρ (u j)) 0 := by simp [square]
    have := qo_sq_far h0 h1
    rcases this with h | h
    · left; linarith
    · right; linarith
  have hu1 : ∀ j : Fin (4 * N), 1 ≤ (j : ℕ) → |u j - (j : ℕ) * L| ≤ 16 * D := by
    intro j hj
    have : (1 : ℝ) ≤ (j : ℕ) := by exact_mod_cast hj
    exact qo_close_norm (ρ := ρ) (L := L) (M := 16 * D) (u := u j) (ι := (j : ℕ) * L) (hu08 j).1 (hu08 j).2
      (by nlinarith) (by linarith [hjL j]) (by linarith) (hclose j)
  have hK4 : 4 ≤ 4 * N := by omega
  set o : Fin (4 * N) := ⟨1, by omega⟩ with ho
  set i0 : Fin (4 * N) := ⟨0, by omega⟩ with hi0
  have hu0 : u i0 ≤ 16 * D ∨ 8 * ρ - 16 * D ≤ u i0 := by
    have := hclose i0
    have e : ((i0 : ℕ) : ℝ) * L = 0 := by simp [hi0]
    rw [e, sub_zero, abs_of_pos (hu08 i0).1] at this
    rcases this with h | h
    · left; exact h
    · right; linarith
  -- distinctness
  have hwinj : ∀ i j : Fin (4 * N), w i = w j → i = j := by
    intro i j hij
    by_contra hne
    have h1 := hnear i
    rw [hij] at h1
    have := qo_sq_far h1 (hnear j)
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have e1 := qo_mulL (L := L) (by linarith) hlt
      have e2 := hjL j
      rw [abs_of_nonpos (by linarith)] at this
      rcases this with h | h <;> nlinarith
    · have e1 := qo_mulL (L := L) (by linarith) hlt
      have e2 := hjL i
      rw [abs_of_nonneg (by linarith)] at this
      rcases this with h | h <;> nlinarith
  -- the loop and the parameters of the points
  have hγ : IsLoopParam (frontier H.carrier) (qoLoop H.disk) := qoLoop_isLoopParam H.disk
  set γ := qoLoop H.disk with hγdef
  have ht0e : ∀ j, ∃ t ∈ Ico (0 : ℝ) 1, γ t = w j := by
    intro j; have := hw j; rw [← hγ.2.2.2] at this; exact this
  choose t0 ht0 hγt0 using ht0e
  have hfr0 : ∀ i j, i ≠ j → 0 < Int.fract (t0 i - t0 j) := by
    intro i j hij
    refine lt_of_le_of_ne (Int.fract_nonneg _) (fun h => hij (hwinj i j ?_))
    rw [← hγt0, ← hγt0, qo_loop_eq_iff hγ, Int.fract_eq_fract]
    refine ⟨⌊t0 i - t0 j⌋, ?_⟩
    have := Int.floor_add_fract (t0 i - t0 j)
    rw [← h] at this; linarith
  obtain ⟨δ₁, hδ₁, hδ₁1, hδ₁f⟩ := qo_fin_pos (fun i => Int.fract (t0 i - t0 o)) (· ≠ o) (fun i hi => hfr0 i o hi)
  obtain ⟨s₁, hs₁, hds₁, ma, hpa⟩ := qo_cut_near H.disk hγ (t0 o) hD hδ₁
  have hγ₁ : IsLoopParam (frontier H.carrier) (fun t => γ (t + s₁)) := qo_loop_shift hγ s₁
  set γ₁ : ℝ → Pt := fun t => γ (t + s₁) with hγ₁def
  set t₁ : Fin (4 * N) → ℝ := fun i => Int.fract (t0 i - s₁) with ht₁def
  have ht₁ : ∀ i, t₁ i ∈ Ico (0 : ℝ) 1 := fun i => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hγt₁ : ∀ i, γ₁ (t₁ i) = w i := by
    intro i
    rw [ht₁def]; simp only []
    rw [qo_loop_fract hγ₁, hγ₁def]; simp only [sub_add_cancel]; exact hγt0 i
  set e₁ := s₁ - t0 o with he₁
  have he₁0 : 0 < e₁ := by linarith [hs₁.1]
  have he₁1 : e₁ < δ₁ := by linarith [hs₁.2]
  have ht₁o : t₁ o = 1 - e₁ := by
    simp only [ht₁def]
    rw [show t0 o - s₁ = -e₁ by ring, qo_fract_eq (z := -1) (by push_cast; linarith) (by push_cast; linarith)]
    push_cast; ring
  have ht₁i : ∀ i, i ≠ o → t₁ i = Int.fract (t0 i - t0 o) - e₁ := by
    intro i hi
    have hf := hδ₁f i hi
    have hf1 := Int.fract_lt_one (t0 i - t0 o)
    simp only [ht₁def]
    rw [show t0 i - s₁ = ⌊t0 i - t0 o⌋ + (Int.fract (t0 i - t0 o) - e₁) by
      rw [he₁]; have := Int.floor_add_fract (t0 i - t0 o); linarith]
    rw [qo_fract_eq (z := ⌊t0 i - t0 o⌋) (by linarith) (by linarith)]
    ring
  have h1max : ∀ i : Fin (4 * N), i.val ≠ 1 → t₁ i < t₁ o := by
    intro i hi
    have hio : i ≠ o := fun h => hi (by rw [h])
    rw [ht₁i i hio, ht₁o]; linarith [Int.fract_lt_one (t0 i - t0 o)]
  have hpos : ∀ i : Fin (4 * N), i.val ≠ 1 → 0 < t₁ i := by
    intro i hi
    have hio : i ≠ o := fun h => hi (by rw [h])
    rw [ht₁i i hio]; linarith [hδ₁f i hio]
  have ht₁inj : ∀ i j, t₁ i = t₁ j → i = j := by
    intro i j h; apply hwinj; rw [← hγt₁, ← hγt₁, h]
  have hpa' : γ₁ 0 ∈ openSegment ℝ (H.disk.vertex ma) (H.disk.vertex (finRotate _ ma)) := by
    simp only [hγ₁def, zero_add]; exact hpa
  have hdpa : dist (γ₁ 0) (w o) < D := by
    simp only [hγ₁def, zero_add]; rw [← hγt0 o]; exact hds₁
  have hoL : ((o : ℕ) : ℝ) * L = L := by simp [ho]
  have hL1000 : 1000 * D ≤ L := by linarith
  have h8L : 8 * L ≤ 8 * ρ := by
    rw [← hK8]; push_cast; nlinarith
  have hcase : ∀ b : Fin (4 * N), 3 ≤ b.val →
      ((∀ i : Fin (4 * N), 2 ≤ i.val → i.val < b.val → t₁ i < t₁ b) ∧
          (∀ i : Fin (4 * N), (b.val < i.val ∨ i.val = 0) → t₁ b < t₁ i)) ∨
      ((∀ i : Fin (4 * N), 2 ≤ i.val → i.val < b.val → t₁ b < t₁ i) ∧
          (∀ i : Fin (4 * N), (b.val < i.val ∨ i.val = 0) → t₁ i < t₁ b)) := by
    intro b hb3
    obtain ⟨δb, hδb, -, hδbf⟩ := qo_fin_pos (fun i => t₁ i - t₁ b) (fun i => t₁ b < t₁ i)
      (fun i hi => sub_pos.2 hi)
    have hbo' : t₁ b < t₁ o := h1max b (by omega)
    have hδbo := hδbf o hbo'
    obtain ⟨sb, hsb, hdsb, mb, hpb⟩ := qo_cut_near H.disk hγ₁ (t₁ b) hD hδb
    have hs1 : sb < 1 := by simp only at hδbo; linarith [hsb.2, (ht₁ o).2]
    have hsep : ∀ i, i ≠ b → t₁ i ≠ sb ∧ (t₁ i < sb ↔ t₁ i < t₁ b) := by
      intro i hib
      rcases lt_trichotomy (t₁ i) (t₁ b) with h | h | h
      · exact ⟨by linarith [hsb.1], ⟨fun _ => h, fun _ => by linarith [hsb.1]⟩⟩
      · exact absurd (ht₁inj i b h) hib
      · have := hδbf i h
        simp only at this
        exact ⟨by linarith [hsb.2], ⟨fun h' => by linarith [hsb.2], fun h' => by linarith⟩⟩
    obtain ⟨ua, ub, hua, hub, hua0, hua8, hub0, hub8, hsep'⟩ := qo_sep H ha hHl hHu hHa ma mb hpa' hpb
    have hdpb : dist (γ₁ sb) (w b) < D := by rw [← hγt₁ b]; exact hdsb
    have h0a : qoPc c ρ ua ∈ square (qoPc c ρ ua) 0 := by simp [square]
    have h0b : qoPc c ρ ub ∈ square (qoPc c ρ ub) 0 := by simp [square]
    have hua' : |ua - L| ≤ 18 * D := by
      have h1 : qoPc c ρ ua ∈ square (qoPc c ρ ((o : ℕ) * L)) (5 * D + D + 3 * D) :=
        qo_sq_trans (qo_sq_trans (hnear o) (qo_sq_of_dist (by rw [dist_comm]; exact hdpa.le))) hua
      rw [hoL] at h1
      have := qo_sq_far h0a h1
      refine qo_close_norm (ρ := ρ) (L := L) hua0 hua8 le_rfl ?_ (by linarith) (by
        rcases this with h | h
        · left; linarith
        · right; linarith)
      linarith
    have hb1 : (1 : ℝ) * L + L ≤ (b : ℕ) * L := by
      have := qo_mulL (L := L) (by linarith) (show 1 + 1 ≤ (b : ℕ) by omega); simpa using this
    have hub' : |ub - (b : ℕ) * L| ≤ 18 * D := by
      have h1 : qoPc c ρ ub ∈ square (qoPc c ρ ((b : ℕ) * L)) (5 * D + D + 3 * D) :=
        qo_sq_trans (qo_sq_trans (hnear b) (qo_sq_of_dist (by rw [dist_comm]; exact hdpb.le))) hub
      have := qo_sq_far h0b h1
      exact qo_close_norm (ρ := ρ) (L := L) hub0 hub8 (by linarith) (by linarith [hjL b]) (by linarith) (by
        rcases this with h | h
        · left; linarith
        · right; linarith)
    have hb2 : (2 : ℝ) * L + L ≤ (b : ℕ) * L := by
      have := qo_mulL (L := L) (by linarith) (show 2 + 1 ≤ (b : ℕ) by omega); simpa using this
    have hua2 := abs_le.1 hua'
    have hub2 := abs_le.1 hub'
    have hab : ua < ub := by linarith
    obtain ⟨f, W, hf, hval⟩ := hsep' hab
    have hne_a : ∀ i : Fin (4 * N), i.val ≠ 1 → w i ≠ γ₁ 0 := by
      intro i hi h
      rw [← hγt₁ i] at h
      have := hγ₁.2.2.1 (ht₁ i) ⟨le_rfl, one_pos⟩ h
      exact absurd this (hpos i hi).ne'
    have hne_b : ∀ i : Fin (4 * N), i ≠ b → w i ≠ γ₁ sb := by
      intro i hi h
      rw [← hγt₁ i] at h
      exact (hsep i hi).1 (hγ₁.2.2.1 (ht₁ i) ⟨hsb.1.le.trans' (ht₁ b).1, hs1⟩ h)
    have hD0 : (0 : ℝ) ≤ 12 * D := by linarith
    refine qo_case_of_wind hγ₁ t₁ ht₁ hpos b hb3 hsb.1 hs1 hsep f W hf ?_ ?_
    · intro i hi2 hib
      have hib' : i ≠ b := fun h => by rw [h] at hib; omega
      have hi := abs_le.1 (hu1 i (by omega))
      have e1 := qo_mulL (L := L) (by linarith) (show 1 + 1 ≤ (i : ℕ) by omega)
      have e2 := qo_mulL (L := L) (by linarith) (show (i : ℕ) + 1 ≤ (b : ℕ) by omega)
      have e3 := hjL b
      simp only [Nat.cast_one] at e1
      have fa := qo_far_pos (ρ := ρ) (d := u i - ua) hD0 (by linarith) (by linarith)
      have fb := qo_far_neg (ρ := ρ) (d := u i - ub) hD0 (by linarith) (by linarith)
      rw [hγt₁ i]
      exact (hval (w i) (hw i) (hne_a i (by omega)) (hne_b i hib') (F i) (hF i) (hFH i) (hwF i) (z i) (hz i) (k i)
        (hk1 i) (hk2 i) (hk3 i) (hzw i) (hzu i) fa.1 fa.2 fb.1 fb.2).2 ⟨by linarith, by linarith⟩
    · intro i hi
      have hib' : i ≠ b := fun h => by rw [h] at hi; omega
      rw [hγt₁ i]
      rcases hi with hi | hi
      · have hu := abs_le.1 (hu1 i (by omega))
        have e2 := qo_mulL (L := L) (by linarith) (show (b : ℕ) + 1 ≤ (i : ℕ) by omega)
        have e3 := hjL i
        have fa := qo_far_pos (ρ := ρ) (d := u i - ua) hD0 (by linarith) (by linarith)
        have fb := qo_far_pos (ρ := ρ) (d := u i - ub) hD0 (by linarith) (by linarith)
        exact (hval (w i) (hw i) (hne_a i (by omega)) (hne_b i hib') (F i) (hF i) (hFH i) (hwF i) (z i) (hz i)
          (k i) (hk1 i) (hk2 i) (hk3 i) (hzw i) (hzu i) fa.1 fa.2 fb.1 fb.2).1 (fun h => by linarith [h.2])
      · have hii : i = i0 := Fin.ext hi
        have e3 := hjL b
        have hb8 := hu08 i
        rw [hii] at hb8 ⊢
        rcases hu0 with h | h
        · have fa := qo_far_neg (ρ := ρ) (d := u i0 - ua) hD0 (by linarith) (by linarith)
          have fb := qo_far_neg (ρ := ρ) (d := u i0 - ub) hD0 (by linarith) (by linarith)
          exact (hval (w i0) (hw i0) (hne_a i0 (by simp [hi0])) (hne_b i0 (hii ▸ hib')) (F i0) (hF i0) (hFH i0)
            (hwF i0) (z i0) (hz i0) (k i0) (hk1 i0) (hk2 i0) (hk3 i0) (hzw i0) (hzu i0) fa.1 fa.2 fb.1 fb.2).1
            (fun h' => by linarith [h'.1])
        · have fa := qo_far_pos (ρ := ρ) (d := u i0 - ua) hD0 (by linarith) (by linarith)
          have fb := qo_far_pos (ρ := ρ) (d := u i0 - ub) hD0 (by linarith) (by linarith)
          exact (hval (w i0) (hw i0) (hne_a i0 (by simp [hi0])) (hne_b i0 (hii ▸ hib')) (F i0) (hF i0) (hFH i0)
            (hwF i0) (z i0) (hz i0) (k i0) (hk1 i0) (hk2 i0) (hk3 i0) (hzw i0) (hzu i0) fa.1 fa.2 fb.1 fb.2).1
            (fun h' => by linarith [h'.2])
  exact qo_pointsInOrder hγ₁ hK4 w t₁ ht₁ hγt₁ h1max hcase

/-- Step 1 of the blueprint proof of `quantitativeAnnularGrouping`: the outer spoke endpoints lie
along `∂H` in the order of the ideal positions.  Blueprint: "The outer endpoint `w_j` satisfies
`h - D ≤ ‖w_j‖∞ ≤ h`, giving similarly `|w_j - λ v_j| < 4D` ... Use the outside-anchored face at
`w_j` to reach `q_j ∉ K₁` ... The endpoint boxes are separated by at least `R - 10D`", and
(`lem:annular-spokes`) "each wall crosses `∂L` exactly once, and pigeonhole over the ideal
wedges fixes the correspondence".  Points of `∂H`, the `j`-th within `D` of the `j`-th extended
radial segment, appear in the index order along a parametrization of `∂H` (outside anchoring
excludes long backtracking of `∂H` inside its band of width `D`). -/
private lemma quantitativeAnnularGrouping_step1_outerOrder {M : MeshConstants P} {S : Patch P}
    (c : Pt) {N : ℕ} {R : ℝ} (hN : 2 ≤ N) (hR : 1000 * M.D ≤ R) (H : FaceGroup S.tiles)
    (hHl : square c ((N : ℝ) * R / 2 + R) + Binf (2 * M.D) ⊆ H.carrier)
    (hHu : H.carrier ⊆ square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D))
    (hHa : H.OutsideAnchored (square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D)))
    (w : Fin (4 * N) → Pt) (hw : ∀ j, w j ∈ frontier H.carrier)
    (hwr : ∀ j : Fin (4 * N), w j ∈ Metric.cthickening M.D (existsAnnularSpokes_ray c N R M.D j)) :
    ∃ γo : ℝ → Pt, IsLoopParam (frontier H.carrier) γo ∧ PointsInOrder γo w := by
  exact qo_main c hN hR H hHl hHu hHa w hw hwr

/-- Step 2 of the blueprint proof of `quantitativeAnnularGrouping`: an annular group lies in
`H \ int L`, hence ("for a point `x ∈ int K₁ \ Q₀`") between `∂Q₀` and `∂K₁`: in the square of
half side `NR/2 + R + 3D` and outside the open square of half side `NR/2`. -/
private lemma quantitativeAnnularGrouping_step2_band {M : MeshConstants P} {S : Patch P}
    {c : Pt} {N : ℕ} {R : ℝ} (G : AnnularGrouping M S.tiles c N R) (j : Fin (4 * N)) {x : Pt}
    (hx : x ∈ (G.spokes.piece j).carrier) :
    x ∈ square c ((N : ℝ) * R / 2 + R + 3 * M.D) ∧ x ∉ interior (square c ((N : ℝ) * R / 2)) := by
  have hxfaces : x ∈ support (G.spokes.piece j).faces := by
    rw [← (G.spokes.piece j).carrier_eq]
    exact hx
  obtain ⟨A, hA, hxA⟩ := mem_support_iff'.1 hxfaces
  have hAH : A ∈ G.H.faces := (G.spokes.piece_sub j hA).1
  have hxH : x ∈ G.H.carrier := by
    change x ∈ G.H.disk.carrier
    rw [G.H.carrier_eq]
    exact mem_support_iff'.2 ⟨A, hAH, hxA⟩
  constructor
  · rcases G.H_upper hxH with ⟨u, hu, v, hv, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [PiLp.add_apply]
      calc
        |u 0 + v 0 - c 0| = |(u 0 - c 0) + v 0| := by ring_nf
        _ ≤ |u 0 - c 0| + |v 0| := abs_add_le _ _
        _ ≤ (N : ℝ) * R / 2 + R + 3 * M.D := by
          linarith [hu.1, hv.1]
    · simp only [PiLp.add_apply]
      calc
        |u 1 + v 1 - c 1| = |(u 1 - c 1) + v 1| := by ring_nf
        _ ≤ |u 1 - c 1| + |v 1| := abs_add_le _ _
        _ ≤ (N : ℝ) * R / 2 + R + 3 * M.D := by
          linarith [hu.2, hv.2]
  · intro hxQ
    have hxLint : x ∈ interior G.L.carrier := interior_mono G.L_lower hxQ
    obtain ⟨ε, hε, hεL⟩ := Metric.isOpen_iff.1 isOpen_interior x hxLint
    have hxAcl : x ∈ closure (interior A.carrier) := by
      rw [tile_regular]
      exact hxA
    obtain ⟨y, hyball, hyA⟩ := mem_closure_iff.1 hxAcl (Metric.ball x ε)
      Metric.isOpen_ball (Metric.mem_ball_self hε)
    have hyL : y ∈ G.L.carrier := interior_subset (hεL hyball)
    have hyLfaces : y ∈ support G.L.faces := by
      rw [← G.L.carrier_eq]
      exact hyL
    obtain ⟨B, hB, hyB⟩ := mem_support_iff'.1 hyLfaces
    by_cases hBA : B = A
    · exact (G.spokes.piece_sub j hA).2 (hBA ▸ hB)
    · exact interior_not_mem_other S.disjoint
        ((G.spokes.piece j).faces_sub hA) (G.L.faces_sub hB)
        (fun h : A = B => hBA h.symm) hyA hyB

/-- periodic perimeter point -/
private def sw3P (A t : ℝ) : Pt := squarePerimeterPoint A (8 * A * Int.fract (t / (8 * A)))

private lemma sw3_V0 (A t : ℝ) : squarePerimeterPoint A t 0 =
    if t ≤ 2 * A then A else if t ≤ 4 * A then A - (t - 2 * A) else if t ≤ 6 * A then -A
    else -A + (t - 6 * A) := by
  unfold squarePerimeterPoint; split_ifs <;> simp [mkPt]

private lemma sw3_V1 (A t : ℝ) : squarePerimeterPoint A t 1 =
    if t ≤ 2 * A then -A + t else if t ≤ 4 * A then A else if t ≤ 6 * A then A - (t - 4 * A)
    else -A := by
  unfold squarePerimeterPoint; split_ifs <;> simp [mkPt]

private lemma sw3P_eq {A t : ℝ} (hA : 0 < A) (h0 : 0 ≤ t) (h1 : t < 8 * A) :
    sw3P A t = squarePerimeterPoint A t := by
  unfold sw3P
  have h8 : 0 < 8 * A := by linarith
  have : Int.fract (t / (8 * A)) = t / (8 * A) := by
    rw [Int.fract_eq_self]; constructor
    · positivity
    · rw [div_lt_one h8]; exact h1
  rw [this]; congr 1; field_simp

private lemma sw3P_add_int {A : ℝ} (t : ℝ) (k : ℤ) : sw3P A (t + k * (8 * A)) = sw3P A t := by
  unfold sw3P
  rcases eq_or_ne A 0 with rfl | hA
  · simp
  have h8 : (8 * A) ≠ 0 := by positivity
  rw [show (t + k * (8 * A)) / (8 * A) = t / (8 * A) + k by field_simp, Int.fract_add_intCast]

private lemma sw3P_periodic {A : ℝ} (t : ℝ) : sw3P A (t + 8 * A) = sw3P A t := by
  have := sw3P_add_int (A := A) t 1
  simpa using this

private lemma sw3P_reduce {A : ℝ} (hA : 0 < A) (t : ℝ) :
    ∃ u, 0 ≤ u ∧ u < 8 * A ∧ ∃ k : ℤ, t = u + k * (8 * A) := by
  have h8 : 0 < 8 * A := by linarith
  refine ⟨8 * A * Int.fract (t / (8 * A)), by have := Int.fract_nonneg (t / (8 * A)); positivity,
    ?_, ⌊t / (8 * A)⌋, ?_⟩
  · have := Int.fract_lt_one (t / (8 * A)); nlinarith
  · rw [Int.fract]; field_simp; ring

private lemma sw3P_coord0 {A t : ℝ} (hA : 0 < A) (h0 : 0 ≤ t) (h1 : t < 8 * A) :
    sw3P A t 0 = if t ≤ 2 * A then A else if t ≤ 4 * A then A - (t - 2 * A) else if t ≤ 6 * A then -A
      else -A + (t - 6 * A) := by
  rw [sw3P_eq hA h0 h1, sw3_V0]

private lemma sw3P_coord1 {A t : ℝ} (hA : 0 < A) (h0 : 0 ≤ t) (h1 : t < 8 * A) :
    sw3P A t 1 = if t ≤ 2 * A then -A + t else if t ≤ 4 * A then A else if t ≤ 6 * A then A - (t - 4 * A)
      else -A := by
  rw [sw3P_eq hA h0 h1, sw3_V1]

private lemma sw3_pt_ext {u v : Pt} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := pt_ext h0 h1

private lemma sw3P_rot {A : ℝ} (hA : 0 < A) (t : ℝ) : sw3P A (t + 2 * A) = jrot (sw3P A t) := by
  obtain ⟨u, hu0, hu1, k, rfl⟩ := sw3P_reduce hA t
  rw [show u + k * (8 * A) + 2 * A = (u + 2 * A) + k * (8 * A) by ring, sw3P_add_int,
    sw3P_add_int]
  have hj0 : ∀ v : Pt, jrot v 0 = -(v 1) := fun v => by simp [jrot]
  have hj1 : ∀ v : Pt, jrot v 1 = v 0 := fun v => by simp [jrot]
  by_cases hu : u + 2 * A < 8 * A
  · apply sw3_pt_ext
    · rw [hj0, sw3P_coord0 hA (by linarith) hu, sw3P_coord1 hA hu0 hu1]
      split_ifs <;> linarith
    · rw [hj1, sw3P_coord1 hA (by linarith) hu, sw3P_coord0 hA hu0 hu1]
      split_ifs <;> linarith
  · push_neg at hu
    have := sw3P_add_int (A := A) (u + 2 * A - 8 * A) 1
    rw [show u + 2 * A - 8 * A + ((1 : ℤ) : ℝ) * (8 * A) = u + 2 * A by push_cast; ring] at this
    rw [this]
    apply sw3_pt_ext
    · rw [hj0, sw3P_coord0 hA (by linarith) (by linarith), sw3P_coord1 hA hu0 hu1]
      split_ifs <;> linarith
    · rw [hj1, sw3P_coord1 hA (by linarith) (by linarith), sw3P_coord0 hA hu0 hu1]
      split_ifs <;> linarith

private lemma sw3_jcr_jrot (u v : Pt) : jcr (jrot u) (jrot v) = jcr u v := by
  simp [jcr, jrot]; ring

private lemma sw3P_jcr_base {A u d : ℝ} (hA : 0 < A) (hu0 : 0 ≤ u) (hu1 : u < 2 * A) (hd0 : 0 ≤ d)
    (hd1 : d ≤ 4 * A) : A / 2 * min d (4 * A - d) ≤ jcr (sw3P A u) (sw3P A (u + d)) := by
  have h1 : u + d < 8 * A := by linarith
  unfold jcr
  rw [sw3P_coord0 hA hu0 (by linarith), sw3P_coord1 hA hu0 (by linarith),
    sw3P_coord0 hA (by linarith) h1, sw3P_coord1 hA (by linarith) h1]
  rcases le_total d (2 * A) with hd | hd
  · rw [min_eq_left (by linarith)]
    split_ifs <;> nlinarith [sq_nonneg ((u + d - 2 * A) - (2 * A - u)),
      mul_nonneg hd0 (by linarith : (0:ℝ) ≤ 2 * A - d)]
  · rw [min_eq_right (by linarith)]
    split_ifs <;> nlinarith [sq_nonneg ((u + d - 2 * A) - (2 * A - u)),
      mul_nonneg (by linarith : (0:ℝ) ≤ 4 * A - d) (by linarith : (0:ℝ) ≤ d - 2 * A)]

private lemma sw3P_jcr {A : ℝ} (hA : 0 < A) (s : ℝ) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 4 * A) :
    A / 2 * min d (4 * A - d) ≤ jcr (sw3P A s) (sw3P A (s + d)) := by
  obtain ⟨u, hu0, hu1, k, rfl⟩ := sw3P_reduce hA s
  rw [show u + k * (8 * A) + d = (u + d) + k * (8 * A) by ring, sw3P_add_int, sw3P_add_int]
  have step : ∀ v : ℝ, A / 2 * min d (4 * A - d) ≤ jcr (sw3P A v) (sw3P A (v + d)) →
      A / 2 * min d (4 * A - d) ≤ jcr (sw3P A (v + 2 * A)) (sw3P A (v + 2 * A + d)) := by
    intro v hv
    rw [show v + 2 * A + d = (v + d) + 2 * A by ring, sw3P_rot hA, sw3P_rot hA, sw3_jcr_jrot]
    exact hv
  by_cases h2 : u < 2 * A
  · exact sw3P_jcr_base hA hu0 h2 hd0 hd1
  by_cases h4 : u < 4 * A
  · have := step (u - 2 * A) (sw3P_jcr_base hA (by linarith) (by linarith) hd0 hd1)
    simpa using this
  by_cases h6 : u < 6 * A
  · have := step _ (step (u - 4 * A) (sw3P_jcr_base hA (by linarith) (by linarith) hd0 hd1))
    rw [show u - 4 * A + 2 * A + 2 * A = u by ring] at this; exact this
  · have := step _ (step _ (step (u - 6 * A) (sw3P_jcr_base hA (by linarith) (by linarith) hd0 hd1)))
    rw [show u - 6 * A + 2 * A + 2 * A + 2 * A = u by ring] at this; exact this

private lemma sw3P_bounds {A : ℝ} (hA : 0 < A) (t : ℝ) :
    |sw3P A t 0| ≤ A ∧ |sw3P A t 1| ≤ A ∧ (|sw3P A t 0| = A ∨ |sw3P A t 1| = A) := by
  obtain ⟨u, hu0, hu1, k, rfl⟩ := sw3P_reduce hA t
  rw [sw3P_add_int, sw3P_coord0 hA hu0 hu1, sw3P_coord1 hA hu0 hu1]
  split_ifs
  · refine ⟨by rw [abs_of_pos hA], abs_le.2 ⟨by linarith, by linarith⟩, Or.inl (abs_of_pos hA)⟩
  · refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, by rw [abs_of_pos hA], Or.inr (abs_of_pos hA)⟩
  · refine ⟨by rw [abs_neg, abs_of_pos hA], abs_le.2 ⟨by linarith, by linarith⟩,
      Or.inl (by rw [abs_neg, abs_of_pos hA])⟩
  · refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, by rw [abs_neg, abs_of_pos hA],
      Or.inr (by rw [abs_neg, abs_of_pos hA])⟩

private lemma sw3P_normsq {A : ℝ} (hA : 0 < A) (t : ℝ) :
    A ^ 2 ≤ sw3P A t 0 ^ 2 + sw3P A t 1 ^ 2 ∧ sw3P A t 0 ^ 2 + sw3P A t 1 ^ 2 ≤ 2 * A ^ 2 := by
  obtain ⟨h0, h1, h2⟩ := sw3P_bounds hA t
  have a0 := sq_abs (sw3P A t 0)
  have a1 := sq_abs (sw3P A t 1)
  have b0 : |sw3P A t 0| ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h0 2
  have b1 : |sw3P A t 1| ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  constructor
  · rcases h2 with h | h
    · rw [← a0, h]; nlinarith [sq_nonneg (sw3P A t 1)]
    · rw [← a1, h]; nlinarith [sq_nonneg (sw3P A t 0)]
  · rw [← a0, ← a1]; linarith

private lemma sw3P_norm_le {A : ℝ} (hA : 0 < A) (t : ℝ) : ‖sw3P A t‖ ≤ 2 * A := by
  have h := (sw3P_normsq hA t).2
  have hn : ‖sw3P A t‖ ^ 2 = sw3P A t 0 ^ 2 + sw3P A t 1 ^ 2 := norm_sq_pt _
  nlinarith [norm_nonneg (sw3P A t)]

private lemma sw3P_norm_ge {A : ℝ} (hA : 0 < A) (t : ℝ) : A ≤ ‖sw3P A t‖ := by
  have h := (sw3P_normsq hA t).1
  have hn : ‖sw3P A t‖ ^ 2 = sw3P A t 0 ^ 2 + sw3P A t 1 ^ 2 := norm_sq_pt _
  nlinarith [norm_nonneg (sw3P A t)]

/-- inner product via rotation -/
private lemma sw3P_inner {A : ℝ} (hA : 0 < A) (s : ℝ) {d : ℝ} (hd0 : 2 * A ≤ d) (hd1 : d ≤ 6 * A) :
    sw3P A s 0 * sw3P A (s + d) 0 + sw3P A s 1 * sw3P A (s + d) 1 ≤
      -(A / 2 * min (d - 2 * A) (6 * A - d)) := by
  have h := sw3P_jcr hA (s + 2 * A) (d := d - 2 * A) (by linarith) (by linarith)
  rw [show s + 2 * A + (d - 2 * A) = s + d by ring, sw3P_rot hA,
    show 4 * A - (d - 2 * A) = 6 * A - d by ring] at h
  simp only [jcr, jrot] at h
  simp at h
  linarith

/-- sup-norm -/
private def sw3N (u : Pt) : ℝ := max |u 0| |u 1|

private lemma sw3N_smul (σ : ℝ) (u : Pt) : sw3N (σ • u) = |σ| * sw3N u := by
  simp [sw3N, abs_mul, mul_max_of_nonneg _ _ (abs_nonneg σ)]

private lemma sw3N_add_le (u v : Pt) : sw3N (u + v) ≤ sw3N u + sw3N v := by
  simp only [sw3N, PiLp.add_apply]
  refine max_le ((abs_add_le _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _)))
    ((abs_add_le _ _).trans (add_le_add (le_max_right _ _) (le_max_right _ _)))

private lemma sw3N_le_norm (u : Pt) : sw3N u ≤ ‖u‖ := by
  have h0 := PiLp.norm_apply_le u 0
  have h1 := PiLp.norm_apply_le u 1
  rw [Real.norm_eq_abs] at h0 h1
  exact max_le h0 h1

private lemma sw3N_sub_le (u v : Pt) : sw3N u - sw3N v ≤ sw3N (u - v) := by
  have := sw3N_add_le (u - v) v
  simp at this; linarith

private lemma sw3N_sw3P {A : ℝ} (hA : 0 < A) (t : ℝ) : sw3N (sw3P A t) = A := by
  obtain ⟨h0, h1, h2⟩ := sw3P_bounds hA t
  unfold sw3N
  rcases h2 with h | h
  · rw [h]; exact max_eq_left h1
  · rw [h]; exact max_eq_right h0

private lemma sw3N_nonneg (u : Pt) : 0 ≤ sw3N u := le_max_of_le_left (abs_nonneg _)

private lemma sw3_mem_square_iff {c x : Pt} {h : ℝ} : x ∈ square c h ↔ sw3N (x - c) ≤ h := by
  simp [square, sw3N]

/-- surjectivity of the perimeter parametrization -/
private lemma sw3P_surj {A : ℝ} (hA : 0 < A) (u : Pt) (hu : sw3N u = A) :
    ∃ τ, 0 ≤ τ ∧ τ < 8 * A ∧ sw3P A τ = u := by
  have h0 : |u 0| ≤ A := hu ▸ le_max_left _ _
  have h1 : |u 1| ≤ A := hu ▸ le_max_right _ _
  have h2 : |u 0| = A ∨ |u 1| = A := by
    unfold sw3N at hu
    rcases le_total |u 0| |u 1| with h | h
    · rw [max_eq_right h] at hu; exact Or.inr hu
    · rw [max_eq_left h] at hu; exact Or.inl hu
  rw [abs_le] at h0 h1
  by_cases ha : u 0 = A ∧ u 1 < A
  · refine ⟨u 1 + A, by linarith, by linarith, ?_⟩
    apply sw3_pt_ext
    · rw [sw3P_coord0 hA (by linarith) (by linarith)]; split_ifs <;> linarith
    · rw [sw3P_coord1 hA (by linarith) (by linarith)]; split_ifs <;> linarith
  by_cases hb : u 1 = A ∧ -A < u 0
  · refine ⟨3 * A - u 0, by linarith, by linarith, ?_⟩
    apply sw3_pt_ext
    · rw [sw3P_coord0 hA (by linarith) (by linarith)]; split_ifs <;> linarith
    · rw [sw3P_coord1 hA (by linarith) (by linarith)]; split_ifs <;> linarith
  by_cases hc : u 0 = -A ∧ -A < u 1
  · refine ⟨5 * A - u 1, by linarith, by linarith, ?_⟩
    apply sw3_pt_ext
    · rw [sw3P_coord0 hA (by linarith) (by linarith)]; split_ifs <;> linarith
    · rw [sw3P_coord1 hA (by linarith) (by linarith)]; split_ifs <;> linarith
  have hd : u 1 = -A ∧ u 0 < A := by
    rcases h2 with h | h
    · rcases abs_eq hA.le |>.1 h with h' | h'
      · refine ⟨?_, ?_⟩
        · by_contra hne; exact ha ⟨h', lt_of_le_of_ne h1.2 (by
            intro h''; exact hb ⟨h'', by linarith⟩)⟩
        · exfalso; by_cases hh : u 1 = A
          · exact hb ⟨hh, by linarith⟩
          · exact ha ⟨h', lt_of_le_of_ne h1.2 hh⟩
      · refine ⟨?_, by linarith⟩
        by_contra hne
        exact hc ⟨h', lt_of_le_of_ne h1.1 (fun h'' => hne h''.symm)⟩
    · rcases abs_eq hA.le |>.1 h with h' | h'
      · exfalso
        by_cases hh : u 0 = -A
        · exact hc ⟨hh, by linarith⟩
        · exact hb ⟨h', lt_of_le_of_ne h0.1 (fun h'' => hh h''.symm)⟩
      · refine ⟨h', lt_of_le_of_ne h0.2 ?_⟩
        intro hh; exact ha ⟨hh, by linarith⟩
  refine ⟨7 * A + u 0, by linarith, by linarith, ?_⟩
  apply sw3_pt_ext
  · rw [sw3P_coord0 hA (by linarith) (by linarith)]; split_ifs <;> linarith
  · rw [sw3P_coord1 hA (by linarith) (by linarith)]; split_ifs <;> linarith

private lemma sw3_dist_eq (x c : Pt) (l : ℝ) (V : Pt) : dist x (c + l • V) = ‖x - c - l • V‖ := by
  rw [dist_eq_norm]; congr 1; abel

/-- the shadow lemma -/
private lemma sw3_shadow {A R D : ℝ} (hA : 0 < A) (hD : 0 < D) (hAD : 12 * D ≤ A) (hR : 0 ≤ R)
    {V : Pt} (hV : sw3N V = A) {c x y : Pt} {l' σ' σ : ℝ}
    (hx1 : A ≤ sw3N (x - c)) (hx2 : sw3N (x - c) ≤ A + R + 3 * D)
    (hfar : ∀ l, (A - 3 * D) / A ≤ l → l ≤ (A + R + 6 * D) / A → 3 * D < dist x (c + l • V))
    (hl1 : (A - 3 * D) / A ≤ l') (hl2 : l' ≤ (A + R + 6 * D) / A)
    (hy : dist y (c + l' • V) ≤ 2 * D)
    (hσ' : 1 ≤ σ') (hσ : 1 ≤ σ) (hyy : σ = 1 ∨ A + R + 3 * D - 4 * D ≤ sw3N (y - c))
    (heq : c + σ' • (x - c) = c + σ • (y - c)) : False := by
  set ρ := σ / σ' with hρ
  have hσ'0 : 0 < σ' := by linarith
  have hρ0 : 0 < ρ := div_pos (by linarith) hσ'0
  have hxc : x - c = ρ • (y - c) := by
    have h1 : σ' • (x - c) = σ • (y - c) := add_left_cancel heq
    have : x - c = σ'⁻¹ • (σ • (y - c)) := by rw [← h1, smul_smul, inv_mul_cancel₀ hσ'0.ne', one_smul]
    rw [this, smul_smul]; congr 1; rw [hρ]; field_simp
  set e := y - (c + l' • V) with he
  have hye : y - c = l' • V + e := by rw [he]; abel
  have hen : ‖e‖ ≤ 2 * D := by rw [he, ← dist_eq_norm]; exact hy
  have hxe : x - c = (ρ * l') • V + ρ • e := by rw [hxc, hye, smul_add, smul_smul]
  have hdist : dist x (c + (ρ * l') • V) = ρ * ‖e‖ := by
    rw [sw3_dist_eq, show x - c - (ρ * l') • V = ρ • e by rw [hxe]; abel, norm_smul,
      Real.norm_eq_abs, abs_of_pos hρ0]
  have hl1pos : 0 < (A - 3 * D) / A := div_pos (by linarith) hA
  have hl'0 : 0 < l' := lt_of_lt_of_le hl1pos hl1
  have hNe : sw3N (ρ • e) ≤ ρ * ‖e‖ := by
    rw [sw3N_smul, abs_of_pos hρ0]; exact mul_le_mul_of_nonneg_left (sw3N_le_norm e) hρ0.le
  have hNV : sw3N ((ρ * l') • V) = ρ * l' * A := by
    rw [sw3N_smul, hV, abs_of_pos (mul_pos hρ0 hl'0)]
  have hup : sw3N (x - c) ≤ ρ * l' * A + ρ * ‖e‖ := by
    rw [hxe]; exact (sw3N_add_le _ _).trans (by rw [hNV]; linarith)
  have hlow : ρ * l' * A - ρ * ‖e‖ ≤ sw3N (x - c) := by
    have := sw3N_sub_le ((ρ * l') • V) (-(ρ • e))
    rw [sub_neg_eq_add, ← hxe, hNV, show -(ρ • e) = (-ρ) • e by rw [neg_smul], sw3N_smul,
      abs_neg, abs_of_pos hρ0] at this
    have h2 : ρ * sw3N e ≤ ρ * ‖e‖ := mul_le_mul_of_nonneg_left (sw3N_le_norm e) hρ0.le
    linarith
  rcases le_or_gt ρ 1 with hρ1 | hρ1
  · have hb : ρ * ‖e‖ ≤ 2 * D := by nlinarith [norm_nonneg e]
    have := hfar (ρ * l') ?_ ?_
    · rw [hdist] at this; linarith
    · rw [div_le_iff₀ hA]; linarith
    · nlinarith [mul_le_mul_of_nonneg_right hρ1 hl'0.le]
  · have hσ1 : σ ≠ 1 := by
      intro h; rw [hρ, h] at hρ1; rw [lt_div_iff₀ hσ'0] at hρ1; linarith
    have hyc := hyy.resolve_left hσ1
    have hNx : sw3N (x - c) = ρ * sw3N (y - c) := by rw [hxc, sw3N_smul, abs_of_pos hρ0]
    have h1 : ρ * (A + R + 3 * D - 4 * D) ≤ A + R + 3 * D := by
      have := mul_le_mul_of_nonneg_left hyc hρ0.le
      linarith
    have hρ15 : ρ ≤ 3 / 2 := by
      by_contra hc; push_neg at hc
      have : 3 / 2 * (A + R + 3 * D - 4 * D) < ρ * (A + R + 3 * D - 4 * D) :=
        mul_lt_mul_of_pos_right hc (by linarith)
      linarith
    have hb : ρ * ‖e‖ ≤ 3 * D := by
      have := mul_le_mul hρ15 hen (norm_nonneg e) (by norm_num)
      linarith
    have := hfar (ρ * l') ?_ ?_
    · rw [hdist] at this; linarith
    · nlinarith [mul_le_mul_of_nonneg_right hρ1.le hl'0.le]
    · rw [le_div_iff₀ hA]; linarith

private lemma sw3_jcr_le (u v : Pt) : |jcr u v| ≤ ‖u‖ * ‖v‖ := by
  have h := existsAnnularSpokes_step2_tubes_jcrSq u v
  rw [← norm_sq_pt, ← norm_sq_pt] at h
  have : jcr u v ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by rw [mul_pow]; exact h
  exact abs_le_of_sq_le_sq' this (by positivity) |> fun h => abs_le.2 h

private lemma sw3_inner_le (u v : Pt) : |u 0 * v 0 + u 1 * v 1| ≤ ‖u‖ * ‖v‖ := by
  have h := abs_real_inner_le_norm u v
  have he : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
  rwa [he] at h

private lemma sw3P_int_shift {A R : ℝ} {N : ℕ} (h8 : 8 * A = 4 * N * R) (a q : ℤ) :
    sw3P A (((a + 4 * N * q : ℤ) : ℝ) * R) = sw3P A (a * R) := by
  have := sw3P_add_int (A := A) (a * R) q
  rw [← this]; congr 1; push_cast; rw [h8]; ring

private lemma sw3P_jcr_int {A R : ℝ} {N : ℕ} (hA : 0 < A) (hR : 0 < R) (h8 : 8 * A = 4 * N * R)
    {a b : ℤ} (h1 : 1 ≤ b - a) (h2 : b - a ≤ 2 * N - 1) :
    A * R / 2 ≤ jcr (sw3P A (a * R)) (sw3P A (b * R)) := by
  have h1' : (1 : ℝ) ≤ (b : ℝ) - a := by exact_mod_cast h1
  have h2' : (b : ℝ) - a ≤ 2 * N - 1 := by exact_mod_cast h2
  have hd0 : R ≤ ((b : ℝ) - a) * R := by nlinarith
  have hd1 : ((b : ℝ) - a) * R ≤ 4 * A - R := by nlinarith
  have := sw3P_jcr hA (a * R) (d := ((b : ℝ) - a) * R) (by linarith) (by linarith)
  rw [show (a : ℝ) * R + ((b : ℝ) - a) * R = b * R by ring] at this
  have hm : R ≤ min (((b : ℝ) - a) * R) (4 * A - ((b : ℝ) - a) * R) := le_min hd0 (by linarith)
  nlinarith

private lemma sw3P_sep {A R : ℝ} {N : ℕ} (hA : 0 < A) (hR : 0 < R) (hRA : R ≤ A) (h8 : 8 * A = 4 * N * R)
    (hN : 1 ≤ N) {a t : ℤ} (hdiv : ¬ ((4 * N : ℤ) ∣ t - a)) (c : Pt) {l l' : ℝ}
    (hl : 1 / 2 ≤ l) (hl' : 1 / 2 ≤ l') :
    R / 8 ≤ dist (c + l' • sw3P A (t * R)) (c + l • sw3P A (a * R)) := by
  set r := (t - a) % (4 * N : ℤ) with hr
  have h4N : (0 : ℤ) < 4 * N := by positivity
  have hr0 : 0 ≤ r := Int.emod_nonneg _ h4N.ne'
  have hr1 : r < 4 * N := Int.emod_lt_of_pos _ h4N
  have hrne : r ≠ 0 := by
    intro h; exact hdiv (Int.dvd_of_emod_eq_zero h)
  have hr0' : 1 ≤ r := by omega
  have ht : t = a + r + 4 * N * ((t - a) / (4 * N)) := by
    have := Int.emod_add_mul_ediv (t - a) (4 * N); rw [← hr] at this; linarith
  have hVt : sw3P A (t * R) = sw3P A (a * R + r * R) := by
    rw [ht, sw3P_int_shift h8]; push_cast; ring_nf
  set Va := sw3P A (a * R)
  set Vt := sw3P A (t * R)
  have hdist : dist (c + l' • Vt) (c + l • Va) = ‖l' • Vt - l • Va‖ := by
    rw [dist_eq_norm]; congr 1; abel
  rw [hdist]
  have hVa2 : ‖Va‖ ≤ 2 * A := sw3P_norm_le hA _
  have hVa1 : A ≤ ‖Va‖ := sw3P_norm_ge hA _
  have hr0R : (1 : ℝ) ≤ r := by exact_mod_cast hr0'
  have hr1R : (r : ℝ) ≤ 4 * N - 1 := by
    have : r ≤ 4 * N - 1 := by omega
    exact_mod_cast this
  have hd0 : R ≤ (r : ℝ) * R := by nlinarith
  have hd1 : (r : ℝ) * R ≤ 8 * A - R := by nlinarith
  set w := l' • Vt - l • Va with hw
  have hwn := norm_nonneg w
  -- jcr route
  have jcr_route : A * R / 2 ≤ |jcr Va Vt| → R / 8 ≤ ‖w‖ := by
    intro hj
    have h1 : jcr Va w = l' * jcr Va Vt := by
      rw [hw, jcr_sub_right, jcr_smul_right, jcr_smul_right, jcr_self]; ring
    have h2 := sw3_jcr_le Va w
    rw [h1, abs_mul, abs_of_pos (by linarith : (0:ℝ) < l')] at h2
    have h3 : l' * (A * R / 2) ≤ ‖Va‖ * ‖w‖ := le_trans (mul_le_mul_of_nonneg_left hj (by linarith)) h2
    have h4 : ‖Va‖ * ‖w‖ ≤ 2 * A * ‖w‖ := mul_le_mul_of_nonneg_right hVa2 hwn
    have h5 : 1 / 2 * (A * R / 2) ≤ l' * (A * R / 2) := mul_le_mul_of_nonneg_right hl' (by positivity)
    by_contra hcon; push_neg at hcon
    have : 2 * A * ‖w‖ < 2 * A * (R / 8) := mul_lt_mul_of_pos_left hcon (by positivity)
    linarith
  rcases le_total ((r : ℝ) * R) (3 * A) with hc | hc
  · apply jcr_route
    have := sw3P_jcr hA (a * R) (d := (r : ℝ) * R) (by linarith) (by linarith)
    rw [← hVt] at this
    have hm : R ≤ min ((r : ℝ) * R) (4 * A - (r : ℝ) * R) := le_min hd0 (by linarith)
    have h2 := mul_le_mul_of_nonneg_left hm (by positivity : (0:ℝ) ≤ A / 2)
    have h3 : 0 ≤ A * R := by positivity
    rw [abs_of_nonneg (by linarith)]; linarith
  rcases le_total ((r : ℝ) * R) (5 * A) with hc' | hc'
  · have hin := sw3P_inner hA (a * R) (d := (r : ℝ) * R) (by linarith) (by linarith)
    rw [← hVt] at hin
    have hm : A ≤ min ((r : ℝ) * R - 2 * A) (6 * A - (r : ℝ) * R) := le_min (by linarith) (by linarith)
    have hin' : Va 0 * Vt 0 + Va 1 * Vt 1 ≤ -(A ^ 2 / 2) := by
      have := mul_le_mul_of_nonneg_left hm (by positivity : (0:ℝ) ≤ A / 2)
      nlinarith
    have hVsq : ‖Va‖ ^ 2 = Va 0 ^ 2 + Va 1 ^ 2 := norm_sq_pt _
    have hip : Va 0 * w 0 + Va 1 * w 1 = l' * (Va 0 * Vt 0 + Va 1 * Vt 1) - l * ‖Va‖ ^ 2 := by
      rw [hVsq, hw]; simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
    have hcs := sw3_inner_le Va w
    have hA2 : A ^ 2 ≤ ‖Va‖ ^ 2 := pow_le_pow_left₀ hA.le hVa1 2
    have e1 : l' * (Va 0 * Vt 0 + Va 1 * Vt 1) ≤ l' * (-(A ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left hin' (by linarith)
    have e2 : l' * (-(A ^ 2 / 2)) ≤ 1 / 2 * (-(A ^ 2 / 2)) :=
      mul_le_mul_of_nonpos_right hl' (by have := sq_nonneg A; linarith)
    have e3 : 1 / 2 * A ^ 2 ≤ l * ‖Va‖ ^ 2 := mul_le_mul hl hA2 (by positivity) (by linarith)
    have hval : Va 0 * w 0 + Va 1 * w 1 ≤ -(3 * A ^ 2 / 4) := by rw [hip]; linarith
    have hipabs : 3 * A ^ 2 / 4 ≤ |Va 0 * w 0 + Va 1 * w 1| := by
      rw [abs_of_nonpos (by have := sq_nonneg A; linarith)]; linarith
    have h4 : ‖Va‖ * ‖w‖ ≤ 2 * A * ‖w‖ := mul_le_mul_of_nonneg_right hVa2 hwn
    by_contra hcon; push_neg at hcon
    have : 2 * A * ‖w‖ < 2 * A * (R / 8) := mul_lt_mul_of_pos_left hcon (by positivity)
    have hAR : A * R ≤ A ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_left hRA hA.le
    have := pow_pos hA 2
    linarith
  · apply jcr_route
    have hVa' : Va = sw3P A (t * R + (8 * A - (r : ℝ) * R)) := by
      have hq : (t : ℝ) = a + r + 4 * N * (((t - a) / (4 * N) : ℤ) : ℝ) := by
        exact_mod_cast ht
      change sw3P A (a * R) = _
      rw [← sw3P_int_shift h8 a ((t - a) / (4 * N) + 1)]; congr 1; push_cast; rw [hq]
      linear_combination (-1 : ℝ) * h8
    have := sw3P_jcr hA (t * R) (d := 8 * A - (r : ℝ) * R) (by linarith) (by linarith)
    rw [← hVa'] at this
    have hm : R ≤ min (8 * A - (r : ℝ) * R) (4 * A - (8 * A - (r : ℝ) * R)) :=
      le_min (by linarith) (by linarith)
    rw [jcr_anti] at this
    have h2 := mul_le_mul_of_nonneg_left hm (by positivity : (0:ℝ) ≤ A / 2)
    have h3 : 0 ≤ A * R := by positivity
    rw [abs_of_nonpos (by linarith)]; linarith

private lemma sw3_arg_div_of_re_pos {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Complex.arg (w / z) = Complex.arg w - Complex.arg z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have h1 : |Complex.arg z| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hz)
  have h2 : |Complex.arg w| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hw)
  rw [abs_lt] at h1 h2
  have hzpi : Complex.arg z ≠ Real.pi := by linarith
  rw [div_eq_mul_inv, Complex.arg_mul hw0 (inv_ne_zero hz0), Complex.arg_inv, if_neg hzpi]
  · ring
  · rw [Complex.arg_inv, if_neg hzpi]; constructor <;> linarith

private lemma sw3_wind_zero_of_re {m : ℕ} {c : Fin m → Pt} {p : Pt} (ω : ℂ)
    (h : ∀ k, 0 < (ω * (toC (c k) - toC p)).re) : wind c p = 0 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [wind]
  have hω : ω ≠ 0 := by
    intro h0
    have := h ⟨0, hm⟩; simp [h0] at this
  unfold wind
  have key : ∀ k, Complex.arg (segRatio (c k) (c (finRotate m k)) p) =
      Complex.arg (ω * (toC (c (finRotate m k)) - toC p)) - Complex.arg (ω * (toC (c k) - toC p)) := by
    intro k
    rw [← sw3_arg_div_of_re_pos (h k) (h _)]
    congr 1
    unfold segRatio
    rw [mul_div_mul_left _ _ hω]
  simp_rw [key]
  rw [Finset.sum_sub_distrib, Equiv.sum_comp (finRotate m)
    (fun k => Complex.arg (ω * (toC (c k) - toC p)))]
  ring

private lemma sw3_wind_zero_coord {m : ℕ} {c : Fin m → Pt} {p : Pt} (i : Fin 2) (σ : ℝ)
    (h : ∀ k, 0 < σ * (c k - p) i) : wind c p = 0 := by
  fin_cases i
  · apply sw3_wind_zero_of_re (σ : ℂ)
    intro k
    have := h k
    simp only [Fin.zero_eta, PiLp.sub_apply] at this
    simp [toC, Complex.mul_re]; linarith
  · apply sw3_wind_zero_of_re (-(σ : ℂ) * Complex.I)
    intro k
    have := h k
    simp only [Fin.mk_one, PiLp.sub_apply] at this
    simp [toC, Complex.mul_re]; linarith

open Filter Topology in
private lemma sw3_wind_cross {m : ℕ} {c : Fin m → Pt} (k0 : Fin m) {q d : Pt}
    (hab0 : c k0 ≠ c (finRotate m k0))
    (hq : q ∈ openSegment ℝ (c k0) (c (finRotate m k0)))
    (hother : ∀ k ≠ k0, q ∉ segment ℝ (c k) (c (finRotate m k)))
    (hd : jcr (c (finRotate m k0) - c k0) d ≠ 0) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 → |wind c (q + ε • d) - wind c (q - ε • d)| = 2 * Real.pi := by
  set a := c k0 with ha
  set b := c (finRotate m k0) with hb
  set v := b - a with hv
  -- step 1
  have hclosed : IsClosed (⋃ k ∈ (Finset.univ.erase k0 : Finset (Fin m)),
      segment ℝ (c k) (c (finRotate m k))) :=
    isClosed_biUnion_finset (fun k _ => (isCompact_segment_pt _ _).isClosed)
  have hqnot : q ∉ ⋃ k ∈ (Finset.univ.erase k0 : Finset (Fin m)),
      segment ℝ (c k) (c (finRotate m k)) := by
    simp only [mem_iUnion, not_exists]
    intro k hk; exact hother k (Finset.ne_of_mem_erase hk)
  obtain ⟨r, hr0, hrball⟩ := Metric.isOpen_iff.1 hclosed.isOpen_compl q hqnot
  have hstep1 : ∀ z ∈ Metric.ball q r, z ∈ polyCurve c → jcr v (z - a) = 0 := by
    intro z hz hzc
    obtain ⟨k, hk⟩ := mem_iUnion.1 hzc
    by_cases hkk : k = k0
    · subst hkk; exact jcr_zero_of_mem_segment hk
    · exfalso; apply hrball hz
      exact mem_biUnion (Finset.mem_erase.2 ⟨hkk, Finset.mem_univ _⟩) hk
  have hqline : jcr v (q - a) = 0 := jcr_zero_of_mem_segment (openSegment_subset_segment _ _ _ hq)
  -- step 2
  have hstep2 : ∀ s : ℝ, ∀ z ∈ Metric.ball q r, ∀ z' ∈ Metric.ball q r, 0 < s * jcr v (z - a) →
      0 < s * jcr v (z' - a) → wind c z = wind c z' := by
    intro s z hz z' hz' h1 h2
    apply wind_const_of_preconnected (convex_segment z z').isPreconnected _
      (left_mem_segment ℝ z z') (right_mem_segment ℝ z z')
    intro y hy hyc
    have hyb : y ∈ Metric.ball q r := (convex_ball q r).segment_subset hz hz' hy
    have h0 := hstep1 y hyb hyc
    obtain ⟨θ, hθ0, hθ1, rfl⟩ := mem_segment_iff'.1 hy
    have : jcr v (z + θ • (z' - z) - a) = (1 - θ) * jcr v (z - a) + θ * jcr v (z' - a) := by
      rw [show z + θ • (z' - z) - a = (1 - θ) • (z - a) + θ • (z' - a) by
        simp only [sub_smul, one_smul, smul_sub]; abel]
      rw [jcr_add_right, jcr_smul_right, jcr_smul_right]
    rw [this] at h0
    have : 0 < s * ((1 - θ) * jcr v (z - a) + θ * jcr v (z' - a)) := by
      rcases eq_or_lt_of_le hθ1 with h | h
      · subst h; simpa using h2
      · have e : s * ((1 - θ) * jcr v (z - a) + θ * jcr v (z' - a)) =
            (1 - θ) * (s * jcr v (z - a)) + θ * (s * jcr v (z' - a)) := by ring
        rw [e]; have := mul_pos (by linarith : (0:ℝ) < 1 - θ) h1
        nlinarith [mul_nonneg hθ0 h2.le]
    rw [h0, mul_zero] at this; exact lt_irrefl _ this
  -- step 3
  have hjump := wind_jump k0 hab0 hq hother
  set n := jrot v with hn
  have hvne : v ≠ 0 := by rw [hv]; exact sub_ne_zero.2 (Ne.symm hab0)
  have hvpos : 0 < ‖v‖ ^ 2 := by have := norm_pos_iff.2 hvne; positivity
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t * (‖n‖ + 1) < r := by
    have : Tendsto (fun t : ℝ => t * (‖n‖ + 1)) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun t : ℝ => t * (‖n‖ + 1)) (𝓝 0) (𝓝 (0 * (‖n‖ + 1))) :=
        tendsto_id.mul tendsto_const_nhds
      rw [zero_mul] at h; exact h.mono_left nhdsWithin_le_nhds
    exact this.eventually (gt_mem_nhds hr0)
  obtain ⟨t, ⟨htj, hts⟩, htpos⟩ :=
    ((hjump.and hsmall).and self_mem_nhdsWithin).exists
  have htpos' : (0:ℝ) < t := htpos
  have hball_t : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → q + (σ * t) • n ∈ Metric.ball q r := by
    intro σ hσ
    rw [Metric.mem_ball, dist_eq_norm, show q + (σ * t) • n - q = (σ * t) • n by abel, norm_smul,
      Real.norm_eq_abs, abs_mul]
    rcases hσ with rfl | rfl <;> simp [abs_of_pos htpos'] <;> nlinarith [norm_nonneg n]
  have hjcr_t : ∀ σ : ℝ, jcr v (q + (σ * t) • n - a) = σ * t * ‖v‖ ^ 2 := by
    intro σ
    rw [show q + (σ * t) • n - a = (q - a) + (σ * t) • n by abel, jcr_add_right, jcr_smul_right,
      hqline, hn, jcr_jrot]; ring
  refine ⟨r / (‖d‖ + 1), by positivity, ?_⟩
  intro ε hε0 hε1
  have hball_e : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → q + (σ * ε) • d ∈ Metric.ball q r := by
    intro σ hσ
    rw [Metric.mem_ball, dist_eq_norm, show q + (σ * ε) • d - q = (σ * ε) • d by abel, norm_smul,
      Real.norm_eq_abs, abs_mul]
    rw [lt_div_iff₀ (by positivity)] at hε1
    rcases hσ with rfl | rfl <;> simp [abs_of_pos hε0] <;> nlinarith [norm_nonneg d]
  have hjcr_e : ∀ σ : ℝ, jcr v (q + (σ * ε) • d - a) = σ * ε * jcr v d := by
    intro σ
    rw [show q + (σ * ε) • d - a = (q - a) + (σ * ε) • d by abel, jcr_add_right, jcr_smul_right,
      hqline]; ring
  have e1 : q + ε • d = q + ((1:ℝ) * ε) • d := by rw [one_mul]
  have e2 : q - ε • d = q + ((-1:ℝ) * ε) • d := by rw [neg_one_mul, neg_smul, sub_eq_add_neg]
  have f1 : q + t • n = q + ((1:ℝ) * t) • n := by rw [one_mul]
  have f2 : q + (-t) • n = q + ((-1:ℝ) * t) • n := by rw [neg_one_mul]
  rw [f1, f2] at htj
  rw [e1, e2]
  have hvt := mul_pos htpos' hvpos
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · have hεj := mul_pos hε0 (neg_pos.2 hneg)
    have w1 := hstep2 (-1) _ (hball_e 1 (Or.inl rfl)) _ (hball_t (-1) (Or.inr rfl))
      (by rw [hjcr_e]; linarith) (by rw [hjcr_t]; linarith)
    have w2 := hstep2 1 _ (hball_e (-1) (Or.inr rfl)) _ (hball_t 1 (Or.inl rfl))
      (by rw [hjcr_e]; linarith) (by rw [hjcr_t]; linarith)
    rw [w1, w2, show wind c (q + ((-1:ℝ) * t) • n) - wind c (q + ((1:ℝ) * t) • n) =
      -(wind c (q + ((1:ℝ) * t) • n) - wind c (q + ((-1:ℝ) * t) • n)) by ring, htj, abs_neg,
      abs_of_pos (by positivity)]
  · have hεj := mul_pos hε0 hpos
    have w1 := hstep2 1 _ (hball_e 1 (Or.inl rfl)) _ (hball_t 1 (Or.inl rfl))
      (by rw [hjcr_e]; linarith) (by rw [hjcr_t]; linarith)
    have w2 := hstep2 (-1) _ (hball_e (-1) (Or.inr rfl)) _ (hball_t (-1) (Or.inr rfl))
      (by rw [hjcr_e]; linarith) (by rw [hjcr_t]; linarith)
    rw [w1, w2, htj, abs_of_pos (by positivity)]

/-- polygonal path in an open preconnected set -/
private lemma sw3_poly_path {U : Set Pt} (hUo : IsOpen U) (hUc : IsPreconnected U) {x y : Pt}
    (hx : x ∈ U) (hy : y ∈ U) :
    ∃ l : List Pt, l.head? = some x ∧ l.getLast? = some y ∧
      l.IsChain (fun a b => segment ℝ a b ⊆ U) := by
  set S := {z | ∃ l : List Pt, l.head? = some x ∧ l.getLast? = some z ∧
      l.IsChain (fun a b => segment ℝ a b ⊆ U)} with hS
  have ext : ∀ z ∈ S, ∀ w, segment ℝ z w ⊆ U → w ∈ S := by
    rintro z ⟨l, hl1, hl2, hl3⟩ w hzw
    refine ⟨l ++ [w], ?_, by simp, ?_⟩
    · cases l with
      | nil => simp at hl1
      | cons a l => simpa using hl1
    · refine hl3.append (List.isChain_singleton w) ?_
      intro a ha b hb
      rw [hl2] at ha; simp at ha hb; subst ha; subst hb; exact hzw
  have hSo : IsOpen (S ∩ U) := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzS, hzU⟩
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUo z hzU
    refine ⟨r, hr, fun w hw => ⟨ext z hzS w ?_, hrU hw⟩⟩
    exact (convex_ball z r).segment_subset (Metric.mem_ball_self hr) hw |>.trans hrU
  have hVo : IsOpen (U \ S) := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzU, hzS⟩
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUo z hzU
    refine ⟨r, hr, fun w hw => ⟨hrU hw, fun hwS => hzS (ext w hwS z ?_)⟩⟩
    exact (convex_ball z r).segment_subset hw (Metric.mem_ball_self hr) |>.trans hrU
  have hxS : x ∈ S := ⟨[x], rfl, rfl, List.isChain_singleton x⟩
  have hsub := hUc.subset_left_of_subset_union hSo hVo
    (Set.disjoint_left.2 fun z hz hz' => hz'.2 hz.1)
    (fun z hz => by by_cases h : z ∈ S; exacts [Or.inl ⟨h, hz⟩, Or.inr ⟨hz, h⟩])
    ⟨x, hx, hxS, hx⟩
  exact (hsub hy).1

/-- the closed polygon through the points of a list -/
private def sw3poly (l : List Pt) : Fin l.length → Pt := fun k => l.get k

private lemma sw3_poly_seg_sub {l : List Pt} {T : Set Pt}
    (hchain : l.IsChain (fun a b => segment ℝ a b ⊆ T))
    (k : Fin l.length) (hk : k.val + 1 < l.length) :
    segment ℝ (sw3poly l k) (sw3poly l (finRotate _ k)) ⊆ T := by
  have hf : (finRotate _ k).val = k.val + 1 := by rw [finRotate_val', if_neg (by omega)]
  have e2 : sw3poly l (finRotate _ k) = l[k.val + 1] := by
    simp only [sw3poly, List.get_eq_getElem, hf]
  rw [e2]; exact hchain.getElem k.val hk

private lemma sw3_poly_last {l : List Pt} (hl : 0 < l.length) :
    sw3poly l ⟨l.length - 1, by omega⟩ = l[l.length - 1] ∧
      sw3poly l (finRotate _ ⟨l.length - 1, by omega⟩) = l[0] := by
  refine ⟨rfl, ?_⟩
  have hf : (finRotate _ (⟨l.length - 1, by omega⟩ : Fin l.length)).val = 0 := by
    rw [finRotate_val', if_pos (by simp; omega)]
  simp only [sw3poly, List.get_eq_getElem, hf]

private lemma sw3_poly_other {l : List Pt} {T : Set Pt} (hl : 0 < l.length)
    (hchain : l.IsChain (fun a b => segment ℝ a b ⊆ T))
    (k : Fin l.length) (hk : k ≠ ⟨l.length - 1, by omega⟩) :
    segment ℝ (sw3poly l k) (sw3poly l (finRotate _ k)) ⊆ T := by
  apply sw3_poly_seg_sub hchain k
  have : k.val ≠ l.length - 1 := fun h => hk (Fin.ext h)
  omega

private lemma sw3_wind_far {m : ℕ} (cc : Fin m → Pt) {c y : Pt} (hy : y ≠ c) :
    ∃ σ0 : ℝ, 1 ≤ σ0 ∧ ∀ σ, σ0 ≤ σ → wind cc (c + σ • (y - c)) = 0 := by
  set u := y - c with hu
  have hu0 : u ≠ 0 := sub_ne_zero.2 hy
  have hν : 0 < sw3N u := by
    by_contra h; push_neg at h
    have h0 : |u 0| ≤ 0 := (le_max_left _ _).trans h
    have h1 : |u 1| ≤ 0 := (le_max_right _ _).trans h
    exact hu0 (pt_ext (by simpa using h0) (by simpa using h1))
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, |u i| = sw3N u := by
    unfold sw3N
    rcases le_total |u 0| |u 1| with h | h
    · exact ⟨1, (max_eq_right h).symm⟩
    · exact ⟨0, (max_eq_left h).symm⟩
  set s : ℝ := if 0 < u i then 1 else -1 with hs
  have hsu : s * u i = sw3N u := by
    rw [← hi, hs]; split_ifs with h
    · rw [one_mul, abs_of_pos h]
    · push_neg at h; rw [abs_of_nonpos h]; ring
  have hsabs : |s| = 1 := by rw [hs]; split_ifs <;> simp
  set M := ∑ k, sw3N (cc k - c) with hM
  have hMk : ∀ k, sw3N (cc k - c) ≤ M := fun k =>
    Finset.single_le_sum (f := fun k => sw3N (cc k - c)) (fun k _ => sw3N_nonneg _)
      (Finset.mem_univ k)
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun k _ => sw3N_nonneg _)
  refine ⟨1 + M / sw3N u, by have := div_nonneg hM0 hν.le; linarith, ?_⟩
  intro σ hσ
  apply sw3_wind_zero_coord i (-s)
  intro k
  have hσν : sw3N u + M ≤ σ * sw3N u := by
    have := mul_le_mul_of_nonneg_right hσ hν.le
    rw [add_mul, div_mul_cancel₀ _ hν.ne', one_mul] at this; exact this
  have hck : |(cc k - c) i| ≤ sw3N (cc k - c) := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have e : -s * (cc k - (c + σ • u)) i = σ * (s * u i) - s * (cc k - c) i := by
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e, hsu]
  have : s * (cc k - c) i ≤ |(cc k - c) i| := by
    calc s * (cc k - c) i ≤ |s * (cc k - c) i| := le_abs_self _
      _ = |(cc k - c) i| := by rw [abs_mul, hsabs, one_mul]
  linarith [hMk k]

private lemma sw3_wind_ray_zero {m : ℕ} (cc : Fin m → Pt) {c y : Pt} (hy : y ≠ c) {σ1 : ℝ}
    (havoid : ∀ σ : ℝ, σ1 ≤ σ → c + σ • (y - c) ∉ polyCurve cc) :
    wind cc (c + σ1 • (y - c)) = 0 := by
  obtain ⟨σ0, hσ0, hfar⟩ := sw3_wind_far cc hy
  set f : ℝ → Pt := fun σ => c + σ • (y - c)
  have hf : Continuous f := by fun_prop
  have hS : IsPreconnected (f '' Ici σ1) := (isPreconnected_Ici).image f hf.continuousOn
  have := wind_const_of_preconnected hS (by rintro _ ⟨σ, hσ, rfl⟩; exact havoid σ hσ)
    (mem_image_of_mem f (self_mem_Ici)) (mem_image_of_mem f (show max σ0 σ1 ∈ Ici σ1 from le_max_right σ0 σ1))
  rw [this]; exact hfar _ (le_max_left _ _)

private lemma sw3_wind_ray_cross {m : ℕ} (cc : Fin m → Pt) (k0 : Fin m) {c y : Pt} (hy : y ≠ c) {σs : ℝ}
    (hσs : 1 < σs) (hab0 : cc k0 ≠ cc (finRotate m k0))
    (hq : c + σs • (y - c) ∈ openSegment ℝ (cc k0) (cc (finRotate m k0)))
    (hother : ∀ k ≠ k0, ∀ σ : ℝ, 1 ≤ σ → c + σ • (y - c) ∉ segment ℝ (cc k) (cc (finRotate m k)))
    (hk0 : ∀ σ : ℝ, 1 ≤ σ → σ ≠ σs → c + σ • (y - c) ∉ segment ℝ (cc k0) (cc (finRotate m k0)))
    (hd : jcr (cc (finRotate m k0) - cc k0) (y - c) ≠ 0) : wind cc y ≠ 0 := by
  set u := y - c with hu
  set q := c + σs • u with hqdef
  have hother' : ∀ k ≠ k0, q ∉ segment ℝ (cc k) (cc (finRotate m k)) :=
    fun k hk => hother k hk σs hσs.le
  obtain ⟨ε0, hε0, hcross⟩ := sw3_wind_cross k0 hab0 hq hother' hd
  set ε := min (ε0 / 2) ((σs - 1) / 2) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  have hεlt : ε < ε0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεs : ε ≤ (σs - 1) / 2 := min_le_right _ _
  have havoid : ∀ σ : ℝ, 1 ≤ σ → σ ≠ σs → c + σ • u ∉ polyCurve cc := by
    intro σ hσ hne hc
    obtain ⟨k, hk⟩ := mem_iUnion.1 hc
    by_cases hkk : k = k0
    · subst hkk; exact hk0 σ hσ hne hk
    · exact hother k hkk σ hσ hk
  have e1 : q + ε • u = c + (σs + ε) • u := by rw [hqdef, add_smul]; abel
  have e2 : q - ε • u = c + (σs - ε) • u := by rw [hqdef, sub_smul]; abel
  have hz : wind cc (q + ε • u) = 0 := by
    rw [e1]
    exact sw3_wind_ray_zero cc hy (fun σ hσ => havoid σ (by linarith) (by linarith))
  have hw : wind cc (q - ε • u) = wind cc y := by
    rw [e2]
    set f : ℝ → Pt := fun σ => c + σ • u
    have hf : Continuous f := by fun_prop
    have hS : IsPreconnected (f '' Icc 1 (σs - ε)) := (isPreconnected_Icc).image f hf.continuousOn
    have := wind_const_of_preconnected hS
      (by rintro _ ⟨σ, hσ, rfl⟩; exact havoid σ hσ.1 (by linarith [hσ.2]))
      (mem_image_of_mem f (show σs - ε ∈ Icc 1 (σs - ε) from ⟨by linarith, le_rfl⟩))
      (mem_image_of_mem f (show (1:ℝ) ∈ Icc 1 (σs - ε) from ⟨le_rfl, by linarith⟩))
    rw [this]; simp [f, hu]
  have := hcross ε hεpos hεlt
  rw [hz, hw, zero_sub, abs_neg] at this
  intro h0; rw [h0, abs_zero] at this
  have := Real.pi_pos; linarith

private lemma sw3_tile_unique {S : Set (PlacedTile P)} (hdisj : DisjointInteriors S) {A C : PlacedTile P}
    (hA : A ∈ S) (hC : C ∈ S) {z : Pt} (hzA : z ∈ interior A.carrier) (hzC : z ∈ C.carrier) :
    C = A := by
  by_contra hne
  have hz : z ∈ closure (interior C.carrier) := by rw [tile_regular]; exact hzC
  obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hz _ isOpen_interior hzA
  exact interiors_disjoint hdisj hA hC (Ne.symm hne) hw1 hw2

private lemma sw3_polyCurve_closed {m : ℕ} (cc : Fin m → Pt) : IsClosed (polyCurve cc) :=
  isClosed_iUnion_of_finite (fun _ => (isCompact_segment_pt _ _).isClosed)

/-- winding number is constant along the face chain of a dual-connected group avoiding the
curve -/
private lemma sw3_wind_chain {S : Set (PlacedTile P)} (hdisj : DisjointInteriors S)
    {G : Set (PlacedTile P)} (hG : G ⊆ S) (hconn : DualConnected G) {m : ℕ} (cc : Fin m → Pt)
    (hcurve : ∀ z ∈ polyCurve cc, z ∉ interior (support G) ∨ ∃ C ∈ S, C ∉ G ∧ z ∈ C.carrier)
    {A B : PlacedTile P} (hA : A ∈ G) (hB : B ∈ G) {x y : Pt} (hx : x ∈ interior A.carrier)
    (hy : y ∈ interior B.carrier) : wind cc x = wind cc y := by
  -- interiors avoid the curve
  have hint : ∀ A ∈ G, ∀ z ∈ interior A.carrier, z ∉ polyCurve cc := by
    intro A hA z hz hzc
    rcases hcurve z hzc with h | ⟨C, hC, hCG, hzC⟩
    · exact h (interior_mono (carrier_subset_support hA) hz)
    · exact hCG (sw3_tile_unique hdisj (hG hA) hC hz hzC ▸ hA)
  -- constant on each interior
  have hconst : ∀ A ∈ G, ∀ z ∈ interior A.carrier, ∀ z' ∈ interior A.carrier,
      wind cc z = wind cc z' := by
    intro A hA z hz z' hz'
    exact wind_const_of_preconnected (tileDisk A).interior_pathConnected.isConnected.isPreconnected
      (hint A hA) hz hz'
  -- across a shared side
  have hstep : ∀ X ∈ G, ∀ Y ∈ G, SharesSide X Y → ∀ z ∈ interior X.carrier,
      ∀ z' ∈ interior Y.carrier, wind cc z = wind cc z' := by
    intro X hX Y hY ⟨hne, e, ⟨i, hi⟩, ⟨i', hi'⟩⟩ z hz z' hz'
    set q := midpoint ℝ (X.vertex i) (X.vertex (finRotate _ i)) with hq
    have hqo : q ∈ openSegment ℝ (X.vertex i) (X.vertex (finRotate _ i)) :=
      mem_openSegment_of_ne_left_right (by
        intro h; exact tile_vertex_ne_next X i (by
          rw [hq, eq_comm, midpoint_eq_left_iff] at h; exact h)) (by
        intro h; exact tile_vertex_ne_next X i (by
          rw [hq, eq_comm, midpoint_eq_right_iff] at h; exact h))
        (by rw [hq]; exact midpoint_mem_segment _ _)
    obtain ⟨r, hr, σ, hσ, hball⟩ := two_sides hdisj (hG hX) (hG hY) hne i i' (hi'.trans hi.symm) hqo
    set a := X.vertex i
    set v := X.vertex (finRotate _ i) - a with hv
    have hvne : v ≠ 0 := sub_ne_zero.2 (tile_vertex_ne_next X i).symm
    -- every tile containing q is X or Y
    have hXY : ∀ C ∈ S, q ∈ C.carrier → C = X ∨ C = Y := by
      intro C hC hqC
      have hqcl : q ∈ closure (interior C.carrier) := by rw [tile_regular]; exact hqC
      obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hqcl _ Metric.isOpen_ball (Metric.mem_ball_self hr)
      obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 (isOpen_interior.inter Metric.isOpen_ball) w ⟨hw2, hw1⟩
      obtain ⟨w', hw'1, hw'2⟩ := exists_near_off_line a hvne w (τ := σ) hσ hρ
      have hw'in := hρsub (by rw [Metric.mem_ball, dist_comm]; exact hw'1)
      rcases lt_trichotomy (σ * jcr v (w - a)) 0 with h | h | h
      · -- w itself is on the negative side
        right; exact sw3_tile_unique hdisj (hG hY) hC ((hball w hw1).2.1 h) (interior_subset hw2)
      · left
        rw [h] at hw'2
        exact sw3_tile_unique hdisj (hG hX) hC ((hball w' hw'in.2).1 hw'2) (interior_subset hw'in.1)
      · left; exact sw3_tile_unique hdisj (hG hX) hC ((hball w hw1).1 h) (interior_subset hw2)
    have hqint : q ∈ interior (support G) := by
      rw [mem_interior]
      refine ⟨Metric.ball q r, ?_, Metric.isOpen_ball, Metric.mem_ball_self hr⟩
      intro w hw
      rcases le_or_gt 0 (σ * jcr v (w - a)) with h | h
      · exact carrier_subset_support hX ((hball w hw).2.2 h)
      · exact carrier_subset_support hY (interior_subset ((hball w hw).2.1 h))
    have hqnc : q ∉ polyCurve cc := by
      intro hqc
      rcases hcurve q hqc with h | ⟨C, hC, hCG, hqC⟩
      · exact h hqint
      · rcases hXY C hC hqC with rfl | rfl <;> contradiction
    obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.1 (sw3_polyCurve_closed cc).isOpen_compl q hqnc
    have hball_const : ∀ w ∈ Metric.ball q r', ∀ w' ∈ Metric.ball q r', wind cc w = wind cc w' :=
      fun w hw w' hw' => wind_const_of_preconnected (convex_ball q r').isPreconnected
        (fun u hu => hr'sub hu) hw hw'
    have hqX : q ∈ closure (interior X.carrier) := by
      rw [tile_regular]; exact (tile_side_subset X i) (by
        rw [tile_side_eq]; exact openSegment_subset_segment _ _ _ hqo)
    have hqY : q ∈ closure (interior Y.carrier) := by
      rw [tile_regular]; exact (tile_side_subset Y i') (by
        rw [hi', ← hi, tile_side_eq]; exact openSegment_subset_segment _ _ _ hqo)
    obtain ⟨w1, hw1b, hw1X⟩ := mem_closure_iff.1 hqX _ Metric.isOpen_ball (Metric.mem_ball_self hr')
    obtain ⟨w2, hw2b, hw2Y⟩ := mem_closure_iff.1 hqY _ Metric.isOpen_ball (Metric.mem_ball_self hr')
    rw [hconst X hX z hz w1 hw1X, hball_const w1 hw1b w2 hw2b, hconst Y hY w2 hw2Y z' hz']
  -- induction along the chain
  have key : ∀ B, Relation.ReflTransGen (fun X Y => X ∈ G ∧ Y ∈ G ∧ SharesSide X Y) A B →
      B ∈ G → ∀ y ∈ interior B.carrier, wind cc x = wind cc y := by
    intro B hrel
    induction hrel with
    | refl => intro _ y hy; exact hconst A hA x hx y hy
    | tail _ hYZ ih =>
      intro hZ y hy
      obtain ⟨hY, -, hsh⟩ := hYZ
      obtain ⟨w, hw⟩ := (tileDisk _).interior_nonempty
      rw [ih hY w hw]
      exact hstep _ hY _ hZ hsh w hw y hy
  exact key B (hconn A hA B hB) hB y hy

private lemma sw3_cramer {Va Vb : Pt} (hJ : jcr Va Vb ≠ 0) (u : Pt) :
    u = (jcr u Vb / jcr Va Vb) • Va + (jcr Va u / jcr Va Vb) • Vb := by
  apply pt_ext
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    simp only [jcr] at hJ ⊢; ring
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp
    simp only [jcr] at hJ ⊢; ring

/-- a point of the closing segment, seen from `c` -/
private lemma sw3_closing_jcr {c Va Vb z : Pt} {Λa Λb : ℝ}
    (hz : z ∈ segment ℝ (c + Λa • Va) (c + Λb • Vb)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ jcr Va (z - c) = θ * Λb * jcr Va Vb ∧
      jcr (z - c) Vb = (1 - θ) * Λa * jcr Va Vb := by
  obtain ⟨θ, h0, h1, rfl⟩ := mem_segment_iff'.1 hz
  refine ⟨θ, h0, h1, ?_, ?_⟩ <;>
  · simp only [jcr, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

private lemma sw3_core_zero {Γ : List Pt} {T : Set Pt} (hΓ : 0 < Γ.length) {c Va Vb s : Pt}
    {Λa Λb : ℝ} (hΛa : 0 < Λa) (hΛb : 0 < Λb) (hJ : 0 < jcr Va Vb)
    (hlast : Γ[Γ.length - 1] = c + Λa • Va) (hfirst : Γ[0] = c + Λb • Vb)
    (hchain : Γ.IsChain (fun a b => segment ℝ a b ⊆ T))
    (hs : s ≠ c) (hT : ∀ σ : ℝ, 1 ≤ σ → c + σ • (s - c) ∉ T)
    (hcone : jcr Va (s - c) < 0 ∨ jcr (s - c) Vb < 0) : wind (sw3poly Γ) s = 0 := by
  have h := sw3_wind_ray_zero (sw3poly Γ) hs (σ1 := 1) ?_
  · simpa using h
  intro σ hσ hz
  obtain ⟨k, hk⟩ := mem_iUnion.1 hz
  by_cases hkk : k = ⟨Γ.length - 1, by omega⟩
  · subst hkk
    obtain ⟨e1, e2⟩ := sw3_poly_last hΓ
    rw [e1, e2, hlast, hfirst] at hk
    obtain ⟨θ, h0, h1, ha, hb⟩ := sw3_closing_jcr hk
    simp only [add_sub_cancel_left, jcr_smul_right, jcr_smul_left] at ha hb
    rcases hcone with h | h
    · have : σ * jcr Va (s - c) < 0 := mul_neg_of_pos_of_neg (by linarith) h
      have : 0 ≤ θ * Λb * jcr Va Vb := by positivity
      linarith
    · have : σ * jcr (s - c) Vb < 0 := mul_neg_of_pos_of_neg (by linarith) h
      have : 0 ≤ (1 - θ) * Λa * jcr Va Vb := mul_nonneg (mul_nonneg (by linarith) hΛa.le) hJ.le
      linarith
  · exact hT σ hσ (sw3_poly_other hΓ hchain k hkk hk)

private lemma sw3_core_cross {Γ : List Pt} {T : Set Pt} (hΓ : 0 < Γ.length) {c Va Vb x : Pt}
    {Λa Λb : ℝ} (hΛa : 0 < Λa) (hΛb : 0 < Λb) (hJ : 0 < jcr Va Vb)
    (hlast : Γ[Γ.length - 1] = c + Λa • Va) (hfirst : Γ[0] = c + Λb • Vb)
    (hchain : Γ.IsChain (fun a b => segment ℝ a b ⊆ T))
    (hx : x ≠ c) (hT : ∀ σ : ℝ, 1 ≤ σ → c + σ • (x - c) ∉ T)
    (hα : 0 < jcr (x - c) Vb) (hβ : 0 < jcr Va (x - c))
    (hbiga : 2 * jcr (x - c) Vb < Λa * jcr Va Vb) (hbigb : 2 * jcr Va (x - c) < Λb * jcr Va Vb) :
    wind (sw3poly Γ) x ≠ 0 := by
  obtain ⟨J, hJdef⟩ : ∃ J, J = jcr Va Vb := ⟨_, rfl⟩
  rw [← hJdef] at hJ hbiga hbigb
  obtain ⟨a1, b1, hxc, hjxb, hjax⟩ : ∃ a1 b1 : ℝ, x - c = a1 • Va + b1 • Vb ∧
      jcr (x - c) Vb = a1 * J ∧ jcr Va (x - c) = b1 * J := by
    refine ⟨jcr (x - c) Vb / J, jcr Va (x - c) / J, ?_, by field_simp, by field_simp⟩
    rw [hJdef]; exact sw3_cramer (hJdef ▸ hJ.ne') (x - c)
  rw [hjxb] at hα hbiga; rw [hjax] at hβ hbigb
  have ha1p : 0 < a1 := pos_of_mul_pos_left hα hJ.le
  have hb1p : 0 < b1 := pos_of_mul_pos_left hβ hJ.le
  have ha1s : a1 / Λa < 1 / 2 := by
    rw [div_lt_iff₀ hΛa]; nlinarith
  have hb1s : b1 / Λb < 1 / 2 := by
    rw [div_lt_iff₀ hΛb]; nlinarith
  obtain ⟨ss, hss⟩ : ∃ ss, ss = a1 / Λa + b1 / Λb := ⟨_, rfl⟩
  have hss0 : 0 < ss := by rw [hss]; positivity
  obtain ⟨σs, hσs⟩ : ∃ σs, σs = 1 / ss := ⟨_, rfl⟩
  have hσs1 : 1 < σs := by rw [hσs, lt_div_iff₀ hss0]; linarith
  have hsum : σs * ss = 1 := by rw [hσs]; field_simp
  set k0 : Fin Γ.length := ⟨Γ.length - 1, by omega⟩
  obtain ⟨e1, e2⟩ := sw3_poly_last hΓ
  -- uniqueness of the crossing parameter
  have huniq : ∀ σ : ℝ, 1 ≤ σ → c + σ • (x - c) ∈ segment ℝ (c + Λa • Va) (c + Λb • Vb) →
      σ = σs := by
    intro σ hσ hz
    obtain ⟨θ, h0, h1, ha, hb⟩ := sw3_closing_jcr hz
    simp only [add_sub_cancel_left, jcr_smul_right, jcr_smul_left] at ha hb
    rw [hjax, ← hJdef] at ha; rw [hjxb, ← hJdef] at hb
    have ha' : σ * b1 = θ * Λb := mul_right_cancel₀ hJ.ne' (show σ * b1 * J = θ * Λb * J by linarith)
    have hb' : σ * a1 = (1 - θ) * Λa := mul_right_cancel₀ hJ.ne' (show σ * a1 * J = (1 - θ) * Λa * J by linarith)
    have : σ * ss = 1 := by
      rw [hss, mul_add, mul_div_assoc', mul_div_assoc', hb', ha']
      field_simp; ring
    have := mul_right_cancel₀ hss0.ne' (this.trans hsum.symm)
    exact this
  have hab0 : c + Λa • Va ≠ c + Λb • Vb := by
    intro h
    have := congrArg (fun z => jcr Va (z - c)) h
    simp only [add_sub_cancel_left, jcr_smul_right, jcr_self, mul_zero, ← hJdef] at this
    have : 0 < Λb * J := mul_pos hΛb hJ
    linarith
  apply sw3_wind_ray_cross (sw3poly Γ) k0 hx hσs1
  · rw [e1, e2, hlast, hfirst]; exact hab0
  · rw [e1, e2, hlast, hfirst]
    rw [mem_openSegment_iff']
    have h1 : σs * b1 / Λb * Λb = σs * b1 := by field_simp
    have h2 : Λa * (1 - σs * b1 / Λb) = σs * a1 := by
      rw [hss] at hsum; field_simp at hsum ⊢; linarith
    have hlt : σs * b1 / Λb < 1 := by
      have : 0 < σs * a1 := by positivity
      by_contra hc; push_neg at hc
      have : Λa * (1 - σs * b1 / Λb) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hΛa.le (by linarith)
      linarith
    refine ⟨σs * b1 / Λb, by positivity, hlt, ?_⟩
    rw [hxc]
    apply pt_ext <;>
    · simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      linear_combination (-(Va _)) * h2 - (Vb _) * h1
  · intro k hk σ hσ hz
    exact hT σ hσ (sw3_poly_other hΓ hchain k hk hz)
  · intro σ hσ hne hz
    rw [e1, e2, hlast, hfirst] at hz
    exact hne (huniq σ hσ hz)
  · rw [e1, e2, hlast, hfirst]
    have : jcr (c + Λb • Vb - (c + Λa • Va)) (x - c) = -(Λb * a1 + Λa * b1) * J := by
      rw [hxc, hJdef]; simp only [jcr, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
        smul_eq_mul]; ring
    rw [this]
    have : 0 < (Λb * a1 + Λa * b1) * J := by positivity
    linarith

private lemma sw3_tile_dist_le (M : MeshConstants P) (F : PlacedTile P) {z z' : Pt} (hz : z ∈ F.carrier)
    (hz' : z' ∈ F.carrier) : dist z z' ≤ M.D := by
  obtain ⟨u, hu, rfl⟩ := Set.mem_vadd_set.1 hz
  obtain ⟨u', hu', rfl⟩ := Set.mem_vadd_set.1 hz'
  rw [dist_vadd_cancel_left]
  exact (Metric.dist_le_diam_of_mem (P.disk F.form).compact.isBounded hu hu').trans
    (M.diam_le F.form)

private lemma sw3_square_add_sub (c : Pt) (a r : ℝ) : square c a + Binf r ⊆ square c (a + r) := by
  intro z hz
  obtain ⟨s, hs, b, hb, rfl⟩ := Set.mem_add.1 hz
  refine ⟨?_, ?_⟩
  · simp only [PiLp.add_apply]
    calc |s 0 + b 0 - c 0| = |(s 0 - c 0) + b 0| := by ring_nf
      _ ≤ |s 0 - c 0| + |b 0| := abs_add_le _ _
      _ ≤ a + r := add_le_add hs.1 hb.1
  · simp only [PiLp.add_apply]
    calc |s 1 + b 1 - c 1| = |(s 1 - c 1) + b 1| := by ring_nf
      _ ≤ |s 1 - c 1| + |b 1| := abs_add_le _ _
      _ ≤ a + r := add_le_add hs.2 hb.2

private lemma sw3_interior_square {c z : Pt} {a : ℝ} (hz : z ∈ interior (square c a)) :
    sw3N (z - c) < a := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
  have key : ∀ i : Fin 2, |z i - c i| < a := by
    intro i
    set s : ℝ := if 0 ≤ z i - c i then 1 else -1 with hs
    have hsabs : s * (z i - c i) = |z i - c i| := by
      rw [hs]; split_ifs with h
      · rw [one_mul, abs_of_nonneg h]
      · push_neg at h; rw [abs_of_neg h]; ring
    have hs2 : |s| = 1 := by rw [hs]; split_ifs <;> simp
    set e : Pt := (s * (ε / 2)) • (EuclideanSpace.single i (1 : ℝ)) with he
    have hen : ‖e‖ = ε / 2 := by
      rw [he, norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs, abs_mul,
        hs2, one_mul, abs_of_pos (by positivity)]
    have hmem : z + e ∈ square c a := interior_subset (hball (by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hen]; linarith))
    have hi : |(z + e) i - c i| ≤ a := by
      fin_cases i
      · exact hmem.1
      · exact hmem.2
    have hei : e i = s * (ε / 2) := by simp [he]
    rw [PiLp.add_apply, hei] at hi
    have : |z i + s * (ε / 2) - c i| = |z i - c i| + ε / 2 := by
      rw [show z i + s * (ε / 2) - c i = s * (s * (z i - c i) + ε / 2) by
        have : s * s = 1 := by rw [hs]; split_ifs <;> norm_num
        linear_combination (-(z i - c i)) * this]
      rw [abs_mul, hs2, one_mul, hsabs, abs_of_nonneg (by positivity)]
    linarith
  exact max_lt (key 0) (key 1)

private lemma sw3_mem_interior_square {c z : Pt} {a : ℝ} (hz : sw3N (z - c) < a) :
    z ∈ interior (square c a) := by
  have hopen : IsOpen {w : Pt | |w 0 - c 0| < a ∧ |w 1 - c 1| < a} := by
    have h0 : Continuous fun w : Pt => w 0 := PiLp.continuous_apply 2 _ 0
    have h1 : Continuous fun w : Pt => w 1 := PiLp.continuous_apply 2 _ 1
    exact (isOpen_lt ((h0.sub continuous_const).abs) continuous_const).inter
      (isOpen_lt ((h1.sub continuous_const).abs) continuous_const)
  refine interior_maximal (show {w : Pt | |w 0 - c 0| < a ∧ |w 1 - c 1| < a} ⊆ square c a from
    fun w hw => ⟨hw.1.le, hw.2.le⟩) hopen ?_
  exact ⟨lt_of_le_of_lt (le_max_left _ _) hz, lt_of_le_of_lt (le_max_right _ _) hz⟩

/-- entering a tile through one of its sides -/
private lemma sw3_tile_entry (F : PlacedTile P) (i : Fin (P.disk F.form).n) {u p : Pt}
    (hu : u ∈ F.side i) (hp : p ∈ interior F.carrier) :
    ∃ l : List Pt, l.head? = some u ∧ l.getLast? = some p ∧
      l.IsChain (fun x y => segment ℝ x y ⊆ {z | z ∈ F.side i ∨ z ∈ interior F.carrier}) := by
  set a := F.vertex i
  set b := F.vertex (finRotate _ i)
  have hab : a ≠ b := tile_vertex_ne_next F i
  set m := midpoint ℝ a b with hm
  have hmo : m ∈ openSegment ℝ a b :=
    mem_openSegment_of_ne_left_right (by
        intro h; exact hab (by rw [hm, eq_comm, midpoint_eq_left_iff] at h; exact h)) (by
        intro h; exact hab (by rw [hm, eq_comm, midpoint_eq_right_iff] at h; exact h))
      (by rw [hm]; exact midpoint_mem_segment _ _)
  obtain ⟨r, hr, σ, hσ, hch⟩ := tile_halfdisk F i hmo
  have hd : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  obtain ⟨y, hy, hyc⟩ := exists_near_off_line a hd m hσ hr
  have hmline : jcr (b - a) (m - a) = 0 := jcr_zero_of_mem_segment (openSegment_subset_segment _ _ _ hmo)
  rw [hmline, mul_zero] at hyc
  have hyb : y ∈ Metric.ball m r := by rw [Metric.mem_ball, dist_comm]; exact hy
  have hyint : y ∈ interior F.carrier := ((hch y hyb).2.2).2 hyc
  have hside : F.side i = segment ℝ a b := tile_side_eq F i
  -- the segment from `m` to `y`
  have hmy : segment ℝ m y ⊆ {z | z ∈ F.side i ∨ z ∈ interior F.carrier} := by
    intro z hz
    obtain ⟨θ, hθ0, hθ1, rfl⟩ := mem_segment_iff'.1 hz
    rcases eq_or_lt_of_le hθ0 with h | h
    · left; subst h; rw [zero_smul, add_zero, hside]; exact openSegment_subset_segment _ _ _ hmo
    · right
      have hzb : m + θ • (y - m) ∈ Metric.ball m r :=
        (convex_ball m r).segment_subset (Metric.mem_ball_self hr) hyb (mem_segment_iff'.2 ⟨θ, hθ0, hθ1, rfl⟩)
      apply ((hch _ hzb).2.2).2
      have : jcr (b - a) (m + θ • (y - m) - a) = θ * jcr (b - a) (y - a) := by
        rw [show m + θ • (y - m) - a = (m - a) + θ • ((y - a) - (m - a)) by module, jcr_add_right,
          jcr_smul_right, hmline, jcr_sub_right, hmline]; ring
      rw [this]
      have := mul_pos h hyc
      linarith [show σ * (θ * jcr (b - a) (y - a)) = θ * (σ * jcr (b - a) (y - a)) by ring]
  -- the segment from `u` to `m` lies in the side
  have hum : segment ℝ u m ⊆ F.side i := by
    rw [hside] at hu ⊢
    exact (convex_segment a b).segment_subset hu (openSegment_subset_segment _ _ _ hmo)
  -- polygonal path inside the interior
  obtain ⟨l, hl1, hl2, hl3⟩ := sw3_poly_path isOpen_interior
    (tileDisk F).interior_pathConnected.isConnected.isPreconnected hyint hp
  refine ⟨u :: m :: l, rfl, ?_, ?_⟩
  · cases l with
    | nil => simp at hl1
    | cons a' l' => simpa using hl2
  · rw [List.isChain_cons_cons]
    refine ⟨fun z hz => Or.inl (hum hz), ?_⟩
    cases l with
    | nil => simp at hl1
    | cons a' l' =>
      simp only [List.head?_cons, Option.some.injEq] at hl1
      subst hl1
      rw [List.isChain_cons_cons]
      exact ⟨hmy, hl3.imp (fun x y h => h.trans (fun z hz => Or.inr hz))⟩

private lemma sw3_chain_join {R : Pt → Pt → Prop} {l1 l2 : List Pt} {x y z : Pt}
    (h1 : l1.head? = some x) (h1' : l1.getLast? = some y) (h2 : l2.head? = some y)
    (h2' : l2.getLast? = some z) (c1 : l1.IsChain R) (c2 : l2.IsChain R) (hy : R y y) :
    (l1 ++ l2).head? = some x ∧ (l1 ++ l2).getLast? = some z ∧ (l1 ++ l2).IsChain R := by
  refine ⟨by rw [List.head?_append, h1]; rfl, by rw [List.getLast?_append, h2']; rfl, ?_⟩
  refine c1.append c2 ?_
  intro a ha b hb
  rw [h1'] at ha; rw [h2] at hb
  simp only [Option.mem_def, Option.some.injEq] at ha hb
  subst ha; subst hb; exact hy

private lemma sw3_ray_near {c : Pt} {N : ℕ} {R D : ℝ} (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hA : 0 < (N : ℝ) * R / 2) {k : ℕ} {z : Pt} {δ : ℝ} (hδ : 0 ≤ δ)
    (hz : z ∈ Metric.cthickening δ (existsAnnularSpokes_ray c N R D k)) :
    ∃ l, ((N : ℝ) * R / 2 - 3 * D) / ((N : ℝ) * R / 2) ≤ l ∧
      l ≤ ((N : ℝ) * R / 2 + R + 6 * D) / ((N : ℝ) * R / 2) ∧
      dist z (c + l • squarePerimeterPoint ((N : ℝ) * R / 2) ((k : ℝ) * R)) ≤ δ := by
  have hz' := hz
  unfold existsAnnularSpokes_ray at hz'
  rw [(isCompact_segment_pt _ _).cthickening_eq_biUnion_closedBall hδ] at hz'
  simp only [mem_iUnion, Metric.mem_closedBall] at hz'
  obtain ⟨p, hp, hzp⟩ := hz'
  obtain ⟨l, hl1, hl2, rfl⟩ := existsAnnularSpokes_step2_tubes_rayMem (k := k) hR hD hA hp
  exact ⟨l, hl1, hl2, hzp⟩

/-- the shadow of a radial direction -/
private def sw3Shadow (c V : Pt) (A R D : ℝ) (z : Pt) : Prop :=
  ∃ y : Pt, ∃ σ l : ℝ, (A - 3 * D) / A ≤ l ∧ l ≤ (A + R + 6 * D) / A ∧ dist y (c + l • V) ≤ 2 * D ∧
    1 ≤ σ ∧ (σ = 1 ∨ A + R + 3 * D - 4 * D ≤ sw3N (y - c)) ∧ z = c + σ • (y - c)

private lemma sw3Shadow_self {c V z : Pt} {A R D l : ℝ} (hl1 : (A - 3 * D) / A ≤ l)
    (hl2 : l ≤ (A + R + 6 * D) / A) (hz : dist z (c + l • V) ≤ 2 * D) : sw3Shadow c V A R D z :=
  ⟨z, 1, l, hl1, hl2, hz, le_rfl, Or.inl rfl, by simp⟩

private lemma sw3_spoke_list (α : PolyArc) :
    (List.ofFn α.pt).head? = some α.start ∧ (List.ofFn α.pt).getLast? = some α.stop ∧
      (List.ofFn α.pt).IsChain (fun x y => segment ℝ x y ⊆ α.carrier) := by
  refine ⟨by simp [List.ofFn_succ, PolyArc.start], ?_, ?_⟩
  · rw [List.getLast?_eq_getElem?, List.getElem?_ofFn]
    simp [PolyArc.stop, Fin.last]
  · rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn]
    intro z hz
    refine mem_iUnion.2 ⟨⟨i, by omega⟩, ?_⟩
    simpa [PolyArc.seg] using hz

private lemma sw3_inner_part {S : Set (PlacedTile P)} (L : FaceGroup S) {Q : Set Pt}
    (hanc : L.InsideAnchored Q) {u : Pt} (hu : u ∈ frontier L.carrier) :
    ∃ F ∈ L.faces, u ∈ F.carrier ∧ ∃ p0, p0 ∈ interior Q ∧ ∃ l : List Pt, l.head? = some p0 ∧
      l.getLast? = some u ∧ l.IsChain (fun x y => segment ℝ x y ⊆ F.carrier) := by
  unfold FaceGroup.carrier at hu
  rw [L.disk.frontier_eq] at hu
  obtain ⟨k, hk⟩ := mem_iUnion.1 hu
  obtain ⟨F, hF, ⟨i, hi⟩, p0, hp1, hp2⟩ := hanc k
  have hui : u ∈ F.side i := by rw [hi]; exact hk
  obtain ⟨l, h1, h2, h3⟩ := sw3_tile_entry F i hui hp1
  refine ⟨F, hF, tile_side_subset F i hui, p0, hp2, l.reverse, by rw [List.head?_reverse, h2], by rw [List.getLast?_reverse, h1], ?_⟩
  rw [List.isChain_reverse]
  refine h3.imp (fun x y h => ?_)
  rw [segment_symm]
  intro z hz
  rcases h hz with h' | h'
  · exact tile_side_subset F i h'
  · exact interior_subset h'

private lemma sw3_outer_part {S : Set (PlacedTile P)} (H : FaceGroup S) {K : Set Pt}
    (hanc : H.OutsideAnchored K) {w : Pt} (hw : w ∈ frontier H.carrier) :
    ∃ F ∈ S, F ∉ H.faces ∧ w ∈ F.carrier ∧ ∃ q, q ∉ K ∧ q ∈ F.carrier ∧ ∃ l : List Pt, l.head? = some w ∧
      l.getLast? = some q ∧ l.IsChain (fun x y => segment ℝ x y ⊆ F.carrier) := by
  unfold FaceGroup.carrier at hw
  rw [H.disk.frontier_eq] at hw
  obtain ⟨k, hk⟩ := mem_iUnion.1 hw
  obtain ⟨F, hFS, hFH, ⟨i, hi⟩, q, hq1, hq2⟩ := hanc k
  have hwi : w ∈ F.side i := by rw [hi]; exact hk
  obtain ⟨l, h1, h2, h3⟩ := sw3_tile_entry F i hwi hq1
  refine ⟨F, hFS, hFH, tile_side_subset F i hwi, q, hq2, interior_subset hq1, l, h1, h2, h3.imp (fun x y h => ?_)⟩
  intro z hz
  rcases h hz with h' | h'
  · exact tile_side_subset F i h'
  · exact interior_subset h'

private lemma sw3_radial_part {c V q : Pt} {A R D lq Λ0 : ℝ} (hA : 0 < A) (hD : 0 ≤ D) (hDA : D ≤ A)
    (hR : 0 ≤ R) (hl1 : (A - 3 * D) / A ≤ lq) (hl2 : lq ≤ (A + R + 6 * D) / A) (hlq : 0 < lq)
    (hq : dist q (c + lq • V) ≤ 2 * D) (hqh : A + R + 3 * D < sw3N (q - c)) :
    ∃ Λ, Λ0 ≤ Λ ∧ ∃ l : List Pt, l.head? = some q ∧ l.getLast? = some (c + Λ • V) ∧
      l.IsChain (fun x y => segment ℝ x y ⊆ {z | A + R + 3 * D < sw3N (z - c) ∧ sw3Shadow c V A R D z}) := by
  set Λ' := max 2 (Λ0 / lq) with hΛ'
  have hΛ'2 : 2 ≤ Λ' := le_max_left _ _
  have hΛ'3 : Λ0 / lq ≤ Λ' := le_max_right _ _
  refine ⟨Λ' * lq, by rwa [div_le_iff₀ hlq] at hΛ'3, [q, c + Λ' • (q - c), c + (Λ' * lq) • V], rfl, rfl, ?_⟩
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
  constructor
  · intro z hz
    obtain ⟨θ, h0, h1, rfl⟩ := mem_segment_iff'.1 hz
    have e : q + θ • (c + Λ' • (q - c) - q) = c + (1 + θ * (Λ' - 1)) • (q - c) := by module
    have hσ : 1 ≤ 1 + θ * (Λ' - 1) := by nlinarith
    rw [e]
    refine ⟨?_, q, 1 + θ * (Λ' - 1), lq, hl1, hl2, hq, hσ, Or.inr (by linarith), rfl⟩
    rw [add_sub_cancel_left, sw3N_smul, abs_of_pos (by linarith)]
    nlinarith [sw3N_nonneg (q - c)]
  · intro z hz
    obtain ⟨θ, h0, h1, rfl⟩ := mem_segment_iff'.1 hz
    set y := q + θ • (c + lq • V - q) with hy
    have e : c + Λ' • (q - c) + θ • (c + (Λ' * lq) • V - (c + Λ' • (q - c))) = c + Λ' • (y - c) := by
      rw [hy]; module
    have hyd : dist y (c + lq • V) ≤ 2 * D := by
      have : y - (c + lq • V) = (1 - θ) • (q - (c + lq • V)) := by rw [hy]; module
      rw [dist_eq_norm, this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), ← dist_eq_norm]
      nlinarith [dist_nonneg (x := q) (y := c + lq • V)]
    have hyq : sw3N (y - q) ≤ 2 * D := by
      have : y - q = θ • (c + lq • V - q) := by rw [hy]; abel
      refine (sw3N_le_norm _).trans ?_
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0, ← dist_eq_norm, dist_comm]
      nlinarith [dist_nonneg (x := q) (y := c + lq • V)]
    have hyc : sw3N (q - c) - 2 * D ≤ sw3N (y - c) := by
      have := sw3N_sub_le (q - c) (q - y)
      have h2 : sw3N (q - y) = sw3N (y - q) := by
        rw [show q - y = (-1 : ℝ) • (y - q) by module, sw3N_smul]; simp
      rw [show q - c - (q - y) = y - c by abel] at this
      linarith
    rw [e]
    refine ⟨?_, y, Λ', lq, hl1, hl2, hyd, by linarith, Or.inr (by linarith), rfl⟩
    rw [add_sub_cancel_left, sw3N_smul, abs_of_pos (by linarith)]
    nlinarith

private lemma sw3_wall {M : MeshConstants P} {S : Patch P} {c : Pt} {N : ℕ} {R : ℝ} (hN : 2 ≤ N)
    (hR : 1000 * M.D ≤ R) (G : AnnularGrouping M S.tiles c N R)
    (hspk : ∀ j, (G.spokes.spoke j).carrier ⊆
      Metric.cthickening M.D (existsAnnularSpokes_ray c N R M.D j))
    (i : Fin (4 * N)) (Bad : Pt → Prop) (hL : ∀ F ∈ G.L.faces, ∀ z ∈ F.carrier, Bad z)
    (hSp : ∀ z ∈ (G.spokes.spoke i).carrier, Bad z)
    (hF : ∀ F ∈ S.tiles, F ∉ G.H.faces → ∀ z ∈ F.carrier, Bad z)
    (hH : ∀ z, (N : ℝ) * R / 2 + R + 3 * M.D < sw3N (z - c) → Bad z) (Λ0 : ℝ) :
    ∃ p0 : Pt, ∃ Λ : ℝ, ∃ l : List Pt, Λ0 ≤ Λ ∧ p0 ∈ interior (square c ((N : ℝ) * R / 2)) ∧
      l.head? = some p0 ∧
      l.getLast? = some (c + Λ • squarePerimeterPoint ((N : ℝ) * R / 2) (((i : ℕ) : ℝ) * R)) ∧
      l.IsChain (fun x y => segment ℝ x y ⊆ {z | Bad z ∧ (z ∈ interior (square c ((N : ℝ) * R / 2)) ∨
        sw3Shadow c (squarePerimeterPoint ((N : ℝ) * R / 2) (((i : ℕ) : ℝ) * R)) ((N : ℝ) * R / 2) R M.D z)}) := by
  set A := (N : ℝ) * R / 2 with hAdef
  set D := M.D with hDdef
  set V := squarePerimeterPoint A (((i : ℕ) : ℝ) * R) with hV
  set T := {z | Bad z ∧ (z ∈ interior (square c A) ∨ sw3Shadow c V A R D z)} with hT
  have hD : 0 < D := M.D_pos
  have hR0 : 0 < R := by linarith
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < A := by rw [hAdef]; positivity
  have hAR : R ≤ A := by rw [hAdef]; nlinarith
  set α := G.spokes.spoke i with hα
  have hu : α.start ∈ α.carrier ∩ frontier G.L.carrier := by
    rw [G.spokes.meets_L i]; rfl
  have hw : α.stop ∈ α.carrier ∩ frontier G.H.carrier := by
    rw [G.spokes.meets_H i]; rfl
  obtain ⟨F, hF1, huF, p0, hp0, l1, h11, h12, h13⟩ := sw3_inner_part G.L G.L_anchor hu.2
  obtain ⟨h21, h22, h23⟩ := sw3_spoke_list α
  obtain ⟨F', hF'S, hF'H, hwF, q, hqK, hqF, l3, h31, h32, h33⟩ := sw3_outer_part G.H G.H_anchor hw.2
  obtain ⟨lu, hlu1, hlu2, hlu⟩ := sw3_ray_near hR0.le hD.le hA (le_of_lt hD) (hspk i hu.1)
  obtain ⟨lw, hlw1, hlw2, hlw⟩ := sw3_ray_near hR0.le hD.le hA (le_of_lt hD) (hspk i hw.1)
  have hq3 : A + R + 3 * D < sw3N (q - c) := by
    by_contra hc
    push_neg at hc
    apply hqK
    refine rg_square_add (by linarith) (by linarith) ?_
    rw [sw3_mem_square_iff]; exact hc
  have hqw : dist q (c + lw • V) ≤ 2 * D := by
    have := sw3_tile_dist_le M F' hqF hwF
    linarith [dist_triangle q α.stop (c + lw • V)]
  have hlw0 : 0 < lw := lt_of_lt_of_le (div_pos (by linarith) hA) hlw1
  obtain ⟨Λ, hΛ, l4, h41, h42, h43⟩ := sw3_radial_part (Λ0 := Λ0) hA hD.le (by linarith) hR0.le hlw1 hlw2
    hlw0 hqw hq3
  have hT1 : ∀ z ∈ F.carrier, z ∈ T := by
    intro z hz
    refine ⟨hL F hF1 z hz, Or.inr (sw3Shadow_self hlu1 hlu2 ?_)⟩
    have := sw3_tile_dist_le M F hz huF
    linarith [dist_triangle z α.start (c + lu • V)]
  have hT2 : ∀ z ∈ α.carrier, z ∈ T := by
    intro z hz
    obtain ⟨l, hl1, hl2, hl⟩ := sw3_ray_near hR0.le hD.le hA (le_of_lt hD) (hspk i hz)
    exact ⟨hSp z hz, Or.inr (sw3Shadow_self hl1 hl2 (by linarith))⟩
  have hT3 : ∀ z ∈ F'.carrier, z ∈ T := by
    intro z hz
    refine ⟨hF F' hF'S hF'H z hz, Or.inr (sw3Shadow_self hlw1 hlw2 ?_)⟩
    have := sw3_tile_dist_le M F' hz hwF
    linarith [dist_triangle z α.stop (c + lw • V)]
  have hT4 : ∀ z ∈ {z | A + R + 3 * D < sw3N (z - c) ∧ sw3Shadow c V A R D z}, z ∈ T :=
    fun z hz => ⟨hH z hz.1, Or.inr hz.2⟩
  have hseg : ∀ y ∈ T, segment ℝ y y ⊆ T := fun y hy => by rw [segment_same]; simpa using hy
  obtain ⟨j1, j2, j3⟩ := sw3_chain_join h11 h12 h21 h22 (h13.imp (fun x y h => h.trans hT1))
    (h23.imp (fun x y h => h.trans hT2)) (hseg _ (hT2 _ hu.1))
  obtain ⟨k1, k2, k3⟩ := sw3_chain_join j1 j2 h31 h32 j3 (h33.imp (fun x y h => h.trans hT3))
    (hseg _ (hT2 _ hw.1))
  obtain ⟨m1, m2, m3⟩ := sw3_chain_join k1 k2 h41 h42 k3 (h43.imp (fun x y h => h.trans hT4))
    (hseg _ (hT3 _ hqF))
  exact ⟨p0, Λ, _, hΛ, hp0, m1, m2, m3⟩

private lemma sw3_piece_ne {S : Set (PlacedTile P)} {L H : FaceGroup S} {N : ℕ} (sp : SpokeSystem S L H N)
    {m j : Fin (4 * N)} (hmj : m ≠ j) {C : PlacedTile P} (hCm : C ∈ (sp.piece m).faces) :
    C ∉ (sp.piece j).faces := by
  intro hCj
  have hCS : C ∈ S := (sp.piece m).faces_sub hCm
  have h1 := sp.piece_sub m hCm
  obtain ⟨k, -, hk⟩ := (sp.piece_partition C hCS).1 ⟨h1.1, h1.2⟩
  exact hmj ((hk m hCm).trans (hk j hCj).symm)

private lemma sw3_spoke_bad {S : Set (PlacedTile P)} {L H : FaceGroup S} {N : ℕ} (hN : 2 ≤ N)
    (sp : SpokeSystem S L H N) (i j : Fin (4 * N)) {z : Pt} (hz : z ∈ (sp.spoke i).carrier) :
    ∃ C ∈ S, C ∉ (sp.piece j).faces ∧ z ∈ C.carrier := by
  set i' := (finRotate (4 * N)).symm i with hi'
  have hrot : finRotate (4 * N) i' = i := by rw [hi']; simp
  have hne : i ≠ i' := by
    intro h
    exact mesh_finRotate_ne_self (by omega) i' (hrot.trans h)
  have hzi : z ∈ (sp.piece i).carrier := (sp.piece_between i).1 hz
  have hzi' : z ∈ (sp.piece i').carrier := (sp.piece_between i').2 (by rw [hrot]; exact hz)
  obtain ⟨m, hm, hzm⟩ : ∃ m, m ≠ j ∧ z ∈ (sp.piece m).carrier := by
    by_cases h : i = j
    · exact ⟨i', fun h' => hne (h.trans h'.symm), hzi'⟩
    · exact ⟨i, h, hzi⟩
  unfold FaceGroup.carrier at hzm
  rw [(sp.piece m).carrier_eq, mem_support_iff'] at hzm
  obtain ⟨C, hC, hzC⟩ := hzm
  exact ⟨C, (sp.piece m).faces_sub hC, sw3_piece_ne sp hm hC, hzC⟩

private lemma sw3_closing_far {c Va Vb z : Pt} {A Λa Λb Λ0 : ℝ} (hA : 0 < A) (hΛ0 : 0 ≤ Λ0)
    (ha : Λ0 ≤ Λa) (hb : Λ0 ≤ Λb) (hVa : sw3N Va = A) (hVb : sw3N Vb = A)
    (hin : 0 ≤ Va 0 * Vb 0 + Va 1 * Vb 1) (hz : z ∈ segment ℝ (c + Λa • Va) (c + Λb • Vb)) :
    Λ0 * A / 2 ≤ sw3N (z - c) := by
  obtain ⟨θ, h0, h1, rfl⟩ := mem_segment_iff'.1 hz
  have e0 : (c + Λa • Va + θ • (c + Λb • Vb - (c + Λa • Va)) - c) 0 = (1 - θ) * Λa * Va 0 + θ * Λb * Vb 0 := by
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have e1 : (c + Λa • Va + θ • (c + Λb • Vb - (c + Λa • Va)) - c) 1 = (1 - θ) * Λa * Va 1 + θ * Λb * Vb 1 := by
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  set w := c + Λa • Va + θ • (c + Λb • Vb - (c + Λa • Va)) - c
  have hna : A ^ 2 ≤ Va 0 ^ 2 + Va 1 ^ 2 := by
    rw [← hVa]; unfold sw3N
    rcases le_total |Va 0| |Va 1| with h | h
    · rw [max_eq_right h, sq_abs]; nlinarith
    · rw [max_eq_left h, sq_abs]; nlinarith
  have hnb : A ^ 2 ≤ Vb 0 ^ 2 + Vb 1 ^ 2 := by
    rw [← hVb]; unfold sw3N
    rcases le_total |Vb 0| |Vb 1| with h | h
    · rw [max_eq_right h, sq_abs]; nlinarith
    · rw [max_eq_left h, sq_abs]; nlinarith
  have hw2 : w 0 ^ 2 + w 1 ^ 2 ≤ 2 * sw3N w ^ 2 := by
    unfold sw3N
    have := le_max_left |w 0| |w 1|
    have := le_max_right |w 0| |w 1|
    have h0' : w 0 ^ 2 ≤ max |w 0| |w 1| ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (by assumption) 2
    have h1' : w 1 ^ 2 ≤ max |w 0| |w 1| ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (by assumption) 2
    linarith
  have hΛa : 0 ≤ Λa := by linarith
  have hΛb : 0 ≤ Λb := by linarith
  have key : (Λ0 * A) ^ 2 / 2 ≤ w 0 ^ 2 + w 1 ^ 2 := by
    rw [e0, e1]
    have ha2 : ((1 - θ) * Λ0) ^ 2 * A ^ 2 ≤ ((1 - θ) * Λa) ^ 2 * (Va 0 ^ 2 + Va 1 ^ 2) := by
      apply mul_le_mul _ hna (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by nlinarith) (by nlinarith) 2
    have hb2 : (θ * Λ0) ^ 2 * A ^ 2 ≤ (θ * Λb) ^ 2 * (Vb 0 ^ 2 + Vb 1 ^ 2) := by
      apply mul_le_mul _ hnb (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by nlinarith) (by nlinarith) 2
    have hc : 0 ≤ ((1 - θ) * Λa) * (θ * Λb) * (Va 0 * Vb 0 + Va 1 * Vb 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hΛa) (mul_nonneg h0 hΛb)) hin
    have hθ : 1 / 2 ≤ (1 - θ) ^ 2 + θ ^ 2 := by
      have := sq_nonneg (2 * θ - 1)
      linarith [show (2 * θ - 1) ^ 2 = 2 * ((1 - θ) ^ 2 + θ ^ 2) - 1 by ring]
    have h3 : (Λ0 * A) ^ 2 / 2 ≤ ((1 - θ) ^ 2 + θ ^ 2) * (Λ0 * A) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hθ (sq_nonneg (Λ0 * A))
      linarith
    have hid : ((1 - θ) * Λa * Va 0 + θ * Λb * Vb 0) ^ 2 + ((1 - θ) * Λa * Va 1 + θ * Λb * Vb 1) ^ 2 =
        ((1 - θ) * Λa) ^ 2 * (Va 0 ^ 2 + Va 1 ^ 2) + (θ * Λb) ^ 2 * (Vb 0 ^ 2 + Vb 1 ^ 2) +
          2 * (((1 - θ) * Λa) * (θ * Λb) * (Va 0 * Vb 0 + Va 1 * Vb 1)) := by ring
    have h4 : ((1 - θ) ^ 2 + θ ^ 2) * (Λ0 * A) ^ 2 =
        ((1 - θ) * Λ0) ^ 2 * A ^ 2 + (θ * Λ0) ^ 2 * A ^ 2 := by ring
    rw [hid]
    linarith
  have hs : (Λ0 * A / 2) ^ 2 ≤ sw3N w ^ 2 := by
    have : (Λ0 * A / 2) ^ 2 = (Λ0 * A) ^ 2 / 2 / 2 := by ring
    linarith
  by_contra hc
  push_neg at hc
  have : sw3N w ^ 2 < (Λ0 * A / 2) ^ 2 := pow_lt_pow_left₀ hc (sw3N_nonneg w) two_ne_zero
  linarith

private lemma sw3_list_last {l : List Pt} {v : Pt} (h : l.getLast? = some v) :
    ∃ hl : 0 < l.length, l[l.length - 1] = v := by
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_some_iff] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, h2⟩

private lemma sw3_list_head {l : List Pt} {v : Pt} (h : l.head? = some v) :
    ∃ hl : 0 < l.length, l[0] = v := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_some_iff] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, h2⟩

private lemma sw3_spp_N {N : ℕ} {R : ℝ} (hR : 0 < R) (hN : 1 ≤ N) (k : Fin (4 * N)) :
    sw3N (squarePerimeterPoint ((N : ℝ) * R / 2) (((k : ℕ) : ℝ) * R)) = (N : ℝ) * R / 2 := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  have hk : ((k : ℕ) : ℝ) + 1 ≤ 4 * N := by exact_mod_cast k.isLt
  rw [← sw3P_eq hA (by positivity) (by nlinarith), sw3N_sw3P hA]

private lemma sw3_ray_avoid {c x V : Pt} {A R D : ℝ} (hA : 0 < A) (hD : 0 < D) (hAD : 12 * D ≤ A) (hR : 0 ≤ R)
    (hV : sw3N V = A) (hx1 : A ≤ sw3N (x - c)) (hx2 : sw3N (x - c) ≤ A + R + 3 * D)
    (hfar : ∀ l, (A - 3 * D) / A ≤ l → l ≤ (A + R + 6 * D) / A → 3 * D < dist x (c + l • V))
    {σ : ℝ} (hσ : 1 ≤ σ) :
    c + σ • (x - c) ∉ interior (square c A) ∧ ¬ sw3Shadow c V A R D (c + σ • (x - c)) := by
  constructor
  · intro h
    have := sw3_interior_square h
    rw [add_sub_cancel_left, sw3N_smul, abs_of_pos (by linarith)] at this
    nlinarith
  · rintro ⟨y, σ2, l, hl1, hl2, hy, hσ2, hyy, heq⟩
    exact sw3_shadow hA hD hAD hR hV hx1 hx2 hfar hl1 hl2 hy hσ hσ2 hyy heq

private lemma sw3_contra {M : MeshConstants P} {S : Patch P} {c : Pt} {N : ℕ} {R : ℝ} (hN : 2 ≤ N)
    (hR : 1000 * M.D ≤ R) (G : AnnularGrouping M S.tiles c N R)
    (hspk : ∀ j, (G.spokes.spoke j).carrier ⊆
      Metric.cthickening M.D (existsAnnularSpokes_ray c N R M.D j))
    (j a b : Fin (4 * N))
    (hJ : 0 < jcr (squarePerimeterPoint ((N : ℝ) * R / 2) (((a : ℕ) : ℝ) * R))
      (squarePerimeterPoint ((N : ℝ) * R / 2) (((b : ℕ) : ℝ) * R)))
    (hin : 0 ≤ squarePerimeterPoint ((N : ℝ) * R / 2) (((a : ℕ) : ℝ) * R) 0 *
        squarePerimeterPoint ((N : ℝ) * R / 2) (((b : ℕ) : ℝ) * R) 0 +
      squarePerimeterPoint ((N : ℝ) * R / 2) (((a : ℕ) : ℝ) * R) 1 *
        squarePerimeterPoint ((N : ℝ) * R / 2) (((b : ℕ) : ℝ) * R) 1)
    {x s : Pt} {X Y : PlacedTile P} (hX : X ∈ (G.spokes.piece j).faces)
    (hY : Y ∈ (G.spokes.piece j).faces) (hxX : x ∈ interior X.carrier) (hsY : s ∈ interior Y.carrier)
    (hx1 : (N : ℝ) * R / 2 ≤ sw3N (x - c)) (hx2 : sw3N (x - c) ≤ (N : ℝ) * R / 2 + R + 3 * M.D)
    (hxa : ∀ l, ((N : ℝ) * R / 2 - 3 * M.D) / ((N : ℝ) * R / 2) ≤ l →
      l ≤ ((N : ℝ) * R / 2 + R + 6 * M.D) / ((N : ℝ) * R / 2) →
      3 * M.D < dist x (c + l • squarePerimeterPoint ((N : ℝ) * R / 2) (((a : ℕ) : ℝ) * R)))
    (hxb : ∀ l, ((N : ℝ) * R / 2 - 3 * M.D) / ((N : ℝ) * R / 2) ≤ l →
      l ≤ ((N : ℝ) * R / 2 + R + 6 * M.D) / ((N : ℝ) * R / 2) →
      3 * M.D < dist x (c + l • squarePerimeterPoint ((N : ℝ) * R / 2) (((b : ℕ) : ℝ) * R)))
    (hα : 0 < jcr (x - c) (squarePerimeterPoint ((N : ℝ) * R / 2) (((b : ℕ) : ℝ) * R)))
    (hβ : 0 < jcr (squarePerimeterPoint ((N : ℝ) * R / 2) (((a : ℕ) : ℝ) * R)) (x - c))
    (hs1 : (N : ℝ) * R / 2 ≤ sw3N (s - c)) (hs2 : sw3N (s - c) ≤ (N : ℝ) * R / 2 + R + 3 * M.D)
    (hsa : ∀ l, ((N : ℝ) * R / 2 - 3 * M.D) / ((N : ℝ) * R / 2) ≤ l →
      l ≤ ((N : ℝ) * R / 2 + R + 6 * M.D) / ((N : ℝ) * R / 2) →
      3 * M.D < dist s (c + l • squarePerimeterPoint ((N : ℝ) * R / 2) (((a : ℕ) : ℝ) * R)))
    (hsb : ∀ l, ((N : ℝ) * R / 2 - 3 * M.D) / ((N : ℝ) * R / 2) ≤ l →
      l ≤ ((N : ℝ) * R / 2 + R + 6 * M.D) / ((N : ℝ) * R / 2) →
      3 * M.D < dist s (c + l • squarePerimeterPoint ((N : ℝ) * R / 2) (((b : ℕ) : ℝ) * R)))
    (hcone : jcr (squarePerimeterPoint ((N : ℝ) * R / 2) (((a : ℕ) : ℝ) * R)) (s - c) < 0 ∨
      jcr (s - c) (squarePerimeterPoint ((N : ℝ) * R / 2) (((b : ℕ) : ℝ) * R)) < 0) : False := by
  set A := (N : ℝ) * R / 2 with hAdef
  set D := M.D with hDdef
  set Va := squarePerimeterPoint A (((a : ℕ) : ℝ) * R) with hVa
  set Vb := squarePerimeterPoint A (((b : ℕ) : ℝ) * R) with hVb
  set J := jcr Va Vb with hJdef
  have hD : 0 < D := M.D_pos
  have hR0 : 0 < R := by linarith
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < A := by rw [hAdef]; positivity
  have hAR : R ≤ A := by rw [hAdef]; nlinarith
  have hAD : 12 * D ≤ A := by linarith
  have hNa : sw3N Va = A := sw3_spp_N hR0 (by omega) a
  have hNb : sw3N Vb = A := sw3_spp_N hR0 (by omega) b
  set pj := G.spokes.piece j with hpj
  set Bad : Pt → Prop := fun z => z ∉ interior (support pj.faces) ∨
    ∃ C ∈ S.tiles, C ∉ pj.faces ∧ z ∈ C.carrier with hBad
  have hsupp : ∀ z ∈ support pj.faces, sw3N (z - c) ≤ A + R + 3 * D := by
    intro z hz
    obtain ⟨C, hC, hzC⟩ := mem_support_iff'.1 hz
    have hzH : z ∈ G.H.carrier := by
      unfold FaceGroup.carrier; rw [G.H.carrier_eq]
      exact carrier_subset_support (G.spokes.piece_sub j hC).1 hzC
    rw [← sw3_mem_square_iff]
    exact sw3_square_add_sub c _ _ (G.H_upper hzH)
  have hL : ∀ F ∈ G.L.faces, ∀ z ∈ F.carrier, Bad z := fun F hF z hz =>
    Or.inr ⟨F, G.L.faces_sub hF, fun h => (G.spokes.piece_sub j h).2 hF, hz⟩
  have hF : ∀ F ∈ S.tiles, F ∉ G.H.faces → ∀ z ∈ F.carrier, Bad z := fun F hF hFH z hz =>
    Or.inr ⟨F, hF, fun h => hFH (G.spokes.piece_sub j h).1, hz⟩
  have hH : ∀ z, A + R + 3 * D < sw3N (z - c) → Bad z := fun z hz =>
    Or.inl (fun h => by linarith [hsupp z (interior_subset h)])
  set jx := jcr (x - c) Vb
  set jy := jcr Va (x - c)
  set Λ0 := 2 * (A + R + 3 * D) / A + 1 + 2 * (jx + jy) / J with hΛ0
  have hΛ0a : 2 * (A + R + 3 * D) / A * A = 2 * (A + R + 3 * D) := div_mul_cancel₀ _ hA.ne'
  have hΛ0b : 2 * (jx + jy) / J * J = 2 * (jx + jy) := div_mul_cancel₀ _ hJ.ne'
  have hΛ0p : 1 ≤ Λ0 := by
    have : 0 ≤ 2 * (A + R + 3 * D) / A := by positivity
    have : 0 ≤ 2 * (jx + jy) / J := div_nonneg (by linarith) hJ.le
    linarith
  obtain ⟨pa, Λa, la, hΛa, hpa, ha1, ha2, ha3⟩ := sw3_wall hN hR G hspk a Bad hL
    (fun z hz => Or.inr (sw3_spoke_bad hN G.spokes a j hz)) hF hH Λ0
  obtain ⟨pb, Λb, lb, hΛb, hpb, hb1, hb2, hb3⟩ := sw3_wall hN hR G hspk b Bad hL
    (fun z hz => Or.inr (sw3_spoke_bad hN G.spokes b j hz)) hF hH Λ0
  set T : Set Pt := {z | Bad z ∧ ((z ∈ interior (square c A) ∨ sw3Shadow c Va A R D z) ∨
    (z ∈ interior (square c A) ∨ sw3Shadow c Vb A R D z))} with hT
  set Γ := lb.reverse ++ la with hΓ
  have hQL : ∀ z ∈ interior (square c A), Bad z := by
    intro z hz
    have hzL := G.L_lower (interior_subset hz)
    unfold FaceGroup.carrier at hzL; rw [G.L.carrier_eq] at hzL
    obtain ⟨F, hF', hzF⟩ := mem_support_iff'.1 hzL
    exact hL F hF' z hzF
  have hchain : Γ.IsChain (fun x y => segment ℝ x y ⊆ T) := by
    refine List.IsChain.append ?_ (ha3.imp (fun x y h => h.trans (fun z hz => ⟨hz.1, Or.inl hz.2⟩))) ?_
    · rw [List.isChain_reverse]
      refine hb3.imp (fun x y h => ?_)
      rw [segment_symm]
      exact h.trans (fun z hz => ⟨hz.1, Or.inr hz.2⟩)
    · intro x hx y hy
      rw [List.getLast?_reverse, hb1] at hx
      rw [ha1] at hy
      simp only [Option.mem_def, Option.some.injEq] at hx hy
      subst hx; subst hy
      intro z hz
      have hz' : z ∈ interior (square c A) := (rg_square_convex c A).interior.segment_subset hpb hpa hz
      exact ⟨hQL z hz', Or.inl (Or.inl hz')⟩
  have hlast : ∃ hl : 0 < Γ.length, Γ[Γ.length - 1] = c + Λa • Va := by
    apply sw3_list_last
    rw [hΓ, List.getLast?_append, ha2]; rfl
  have hfirst : ∃ hl : 0 < Γ.length, Γ[0] = c + Λb • Vb := by
    apply sw3_list_head
    rw [hΓ, List.head?_append, List.head?_reverse, hb2]; rfl
  obtain ⟨hΓl, hlast⟩ := hlast
  obtain ⟨_, hfirst⟩ := hfirst
  have hΛa0 : 0 < Λa := by linarith
  have hΛb0 : 0 < Λb := by linarith
  have hΛ0J : Λ0 * J = 2 * (A + R + 3 * D) / A * J + J + 2 * (jx + jy) := by
    rw [← hΛ0b, hΛ0]; ring
  have hΛ0A : Λ0 * A = 2 * (A + R + 3 * D) + A + 2 * (jx + jy) / J * A := by
    rw [← hΛ0a, hΛ0]; ring
  have hJaJ : Λ0 * J ≤ Λa * J := mul_le_mul_of_nonneg_right hΛa hJ.le
  have hJbJ : Λ0 * J ≤ Λb * J := mul_le_mul_of_nonneg_right hΛb hJ.le
  have hpos1 : 0 ≤ 2 * (A + R + 3 * D) / A * J := mul_nonneg (by positivity) hJ.le
  have hpos2 : 0 ≤ 2 * (jx + jy) / J * A := mul_nonneg (div_nonneg (by linarith) hJ.le) hA.le
  have hxc : x ≠ c := by
    intro h; rw [h, sub_self] at hx1
    have : sw3N (0 : Pt) = 0 := by simp [sw3N]
    linarith
  have hsc : s ≠ c := by
    intro h; rw [h, sub_self] at hs1
    have : sw3N (0 : Pt) = 0 := by simp [sw3N]
    linarith
  have hTx : ∀ σ : ℝ, 1 ≤ σ → c + σ • (x - c) ∉ T := by
    rintro σ hσ ⟨-, hm⟩
    have h1 := sw3_ray_avoid hA hD hAD hR0.le hNa hx1 hx2 hxa hσ
    have h2 := sw3_ray_avoid hA hD hAD hR0.le hNb hx1 hx2 hxb hσ
    tauto
  have hTs : ∀ σ : ℝ, 1 ≤ σ → c + σ • (s - c) ∉ T := by
    rintro σ hσ ⟨-, hm⟩
    have h1 := sw3_ray_avoid hA hD hAD hR0.le hNa hs1 hs2 hsa hσ
    have h2 := sw3_ray_avoid hA hD hAD hR0.le hNb hs1 hs2 hsb hσ
    tauto
  have hwx := sw3_core_cross hΓl hΛa0 hΛb0 hJ hlast hfirst hchain hxc hTx hα hβ (by linarith) (by linarith)
  have hws := sw3_core_zero hΓl hΛa0 hΛb0 hJ hlast hfirst hchain hsc hTs hcone
  have hcurve : ∀ z ∈ polyCurve (sw3poly Γ), Bad z := by
    intro z hz
    obtain ⟨k, hk⟩ := mem_iUnion.1 hz
    by_cases hkk : k = ⟨Γ.length - 1, by omega⟩
    · subst hkk
      obtain ⟨e1, e2⟩ := sw3_poly_last hΓl
      rw [e1, e2, hlast, hfirst] at hk
      have := sw3_closing_far hA (by linarith) hΛa hΛb hNa hNb hin hk
      exact hH z (by linarith)
    · exact (sw3_poly_other hΓl hchain k hkk hk).1
  have := sw3_wind_chain S.disjoint pj.faces_sub pj.dualConnected (sw3poly Γ) hcurve hX hY hxX hsY
  exact hwx (this.trans hws)

private lemma sw3_spp_eq {A t : ℝ} (hA : 0 < A) (h0 : 0 ≤ t) (h1 : t ≤ 8 * A) :
    squarePerimeterPoint A t = sw3P A t := by
  rcases lt_or_eq_of_le h1 with h | h
  · exact (sw3P_eq hA h0 h).symm
  · subst h
    have := sw3P_periodic (A := A) 0
    rw [zero_add] at this
    rw [this, sw3P_eq hA le_rfl (by linarith)]
    unfold squarePerimeterPoint
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_pos (by linarith)]
    congr 1 <;> ring

private lemma sw3_fin_of_int {N : ℕ} {R : ℝ} (hR : 0 < R) (hN : 1 ≤ N) (m : ℤ) :
    ∃ i : Fin (4 * N), squarePerimeterPoint ((N : ℝ) * R / 2) (((i : ℕ) : ℝ) * R) =
      sw3P ((N : ℝ) * R / 2) ((m : ℝ) * R) := by
  have h4N : (0 : ℤ) < 4 * N := by positivity
  have hr0 : 0 ≤ m % (4 * N : ℤ) := Int.emod_nonneg _ h4N.ne'
  have hr1 : m % (4 * N : ℤ) < 4 * N := Int.emod_lt_of_pos _ h4N
  refine ⟨⟨(m % (4 * N : ℤ)).toNat, by omega⟩, ?_⟩
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  have hcast : (((m % (4 * N : ℤ)).toNat : ℕ) : ℝ) = ((m % (4 * N : ℤ) : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hr0]
  simp only
  rw [hcast]
  have hr1' : ((m % (4 * N : ℤ) : ℤ) : ℝ) + 1 ≤ 4 * N := by exact_mod_cast hr1
  have hr0' : (0 : ℝ) ≤ ((m % (4 * N : ℤ) : ℤ) : ℝ) := by exact_mod_cast hr0
  rw [sw3_spp_eq hA (by positivity) (by nlinarith)]
  have h8 : 8 * ((N : ℝ) * R / 2) = 4 * N * R := by ring
  have e : m % (4 * N : ℤ) = m + 4 * N * (-(m / (4 * N : ℤ))) := by
    rw [Int.emod_def]; ring
  rw [e, sw3P_int_shift h8]

private lemma sw3_jcr_pos {A : ℝ} (hA : 0 < A) (s : ℝ) {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 2 * A) :
    0 < jcr (sw3P A s) (sw3P A (s + d)) := by
  have h := sw3P_jcr hA s hd0.le (by linarith)
  have : 0 < min d (4 * A - d) := lt_min hd0 (by linarith)
  have : 0 < A / 2 * min d (4 * A - d) := by positivity
  linarith

private lemma sw3_inner_nonneg {A : ℝ} (hA : 0 < A) (s : ℝ) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 2 * A) :
    0 ≤ sw3P A s 0 * sw3P A (s + d) 0 + sw3P A s 1 * sw3P A (s + d) 1 := by
  have h := sw3P_jcr hA s (d := d + 2 * A) (by linarith) (by linarith)
  rw [show s + (d + 2 * A) = (s + d) + 2 * A by ring, sw3P_rot hA] at h
  have e : jcr (sw3P A s) (jrot (sw3P A (s + d))) =
      sw3P A s 0 * sw3P A (s + d) 0 + sw3P A s 1 * sw3P A (s + d) 1 := by
    simp [jcr, jrot]
  rw [e] at h
  have : 0 ≤ min (d + 2 * A) (4 * A - (d + 2 * A)) := le_min (by linarith) (by linarith)
  have : 0 ≤ A / 2 * min (d + 2 * A) (4 * A - (d + 2 * A)) := by positivity
  linarith

private lemma sw3_ray_mem {c V : Pt} {lo hi l : ℝ} (hlh : lo < hi) (h1 : lo ≤ l) (h2 : l ≤ hi) :
    c + l • V ∈ segment ℝ (c + lo • V) (c + hi • V) := by
  rw [mem_segment_iff']
  refine ⟨(l - lo) / (hi - lo), div_nonneg (by linarith) (by linarith),
    (div_le_one (by linarith)).2 (by linarith), ?_⟩
  have : (l - lo) / (hi - lo) * (hi - lo) = l - lo := div_mul_cancel₀ _ (by linarith)
  rw [show c + hi • V - (c + lo • V) = (hi - lo) • V by module, smul_smul, this]
  module

private lemma sw3_far_of_not_cthick {c x : Pt} {N : ℕ} {R D δ : ℝ} (hR : 0 < R) (hD : 0 < D) (hN : 1 ≤ N)
    (j : ℕ) (hj : j ≤ 4 * N) (hx : x ∉ Metric.cthickening δ (existsAnnularSpokes_ray c N R D j)) :
    ∀ l, ((N : ℝ) * R / 2 - 3 * D) / ((N : ℝ) * R / 2) ≤ l →
      l ≤ ((N : ℝ) * R / 2 + R + 6 * D) / ((N : ℝ) * R / 2) →
      δ < dist x (c + l • sw3P ((N : ℝ) * R / 2) (((j : ℤ) : ℝ) * R)) := by
  intro l h1 h2
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  have hj' : (j : ℝ) ≤ 4 * N := by exact_mod_cast hj
  by_contra h
  push_neg at h
  apply hx
  refine Metric.mem_cthickening_of_dist_le x _ δ _ ?_ h
  unfold existsAnnularSpokes_ray
  have e : existsAnnularSpokes_pos ((N : ℝ) * R / 2) ((j : ℝ) * R) =
      sw3P ((N : ℝ) * R / 2) (((j : ℤ) : ℝ) * R) := by
    rw [Int.cast_natCast]
    exact sw3_spp_eq hA (by positivity) (by nlinarith)
  rw [e]
  exact sw3_ray_mem (div_lt_div_of_pos_right (by linarith) hA) h1 h2

private lemma sw3_not_dvd {n m : ℤ} (h1 : 1 ≤ m) (h2 : m < n) : ¬ n ∣ m := fun h => by
  have := Int.le_of_dvd (by omega) h; omega

private lemma sw3_near_excl {c x : Pt} {A R D : ℝ} {N : ℕ} (hA : 0 < A) (hR : 0 < R) (hRA : R ≤ A)
    (h8 : 8 * A = 4 * N * R) (hN : 1 ≤ N) (h64 : 64 * D < R) {m m' : ℤ}
    (hdiv : ¬ (4 * N : ℤ) ∣ m - m') {l l' : ℝ} (hl : 1 / 2 ≤ l) (hl' : 1 / 2 ≤ l')
    (h1 : dist x (c + l • sw3P A ((m : ℝ) * R)) ≤ 4 * D)
    (h2 : dist x (c + l' • sw3P A ((m' : ℝ) * R)) ≤ 4 * D) : False := by
  have := sw3P_sep hA hR hRA h8 hN hdiv c hl' hl
  have := dist_triangle_left (c + l • sw3P A ((m : ℝ) * R)) (c + l' • sw3P A ((m' : ℝ) * R)) x
  linarith

private lemma sw3_sep_far {c s : Pt} {A R D : ℝ} {N : ℕ} (hA : 0 < A) (hR : 0 < R) (hRA : R ≤ A)
    (h8 : 8 * A = 4 * N * R) (hN : 1 ≤ N) (h40 : 40 * D < R) {t a : ℤ}
    (hdiv : ¬ (4 * N : ℤ) ∣ t - a) {l' : ℝ} (hl' : 1 / 2 ≤ l')
    (hs : dist s (c + l' • sw3P A ((t : ℝ) * R)) ≤ 2 * D) {l : ℝ} (hl : 1 / 2 ≤ l) :
    3 * D < dist s (c + l • sw3P A ((a : ℝ) * R)) := by
  have := sw3P_sep hA hR hRA h8 hN hdiv c hl hl'
  have := dist_triangle_left (c + l' • sw3P A ((t : ℝ) * R)) (c + l • sw3P A ((a : ℝ) * R)) s
  linarith

private lemma sw3_cone {c s : Pt} {A R D : ℝ} {N : ℕ} (hA : 0 < A) (hR : 0 < R)
    (h8 : 8 * A = 4 * N * R) (hD : 0 ≤ D) (h16 : 32 * D < R) {a b t : ℤ} (hab1 : 1 ≤ b - a)
    (hab2 : b - a ≤ 2) (ht1 : b + 1 ≤ t) (ht2 : t ≤ a + 4 * N - 1) {l' : ℝ} (hl' : 1 / 2 ≤ l')
    (hs : dist s (c + l' • sw3P A ((t : ℝ) * R)) ≤ 2 * D) :
    jcr (sw3P A ((a : ℝ) * R)) (s - c) < 0 ∨ jcr (s - c) (sw3P A ((b : ℝ) * R)) < 0 := by
  set e := s - c - l' • sw3P A ((t : ℝ) * R) with he
  have hen : ‖e‖ ≤ 2 * D := by
    rw [he, show s - c - l' • sw3P A ((t : ℝ) * R) = s - (c + l' • sw3P A ((t : ℝ) * R)) by abel,
      ← dist_eq_norm]; exact hs
  have hsc : s - c = l' • sw3P A ((t : ℝ) * R) + e := by rw [he]; abel
  have hkey : ∀ u v : Pt, A * R / 2 ≤ jcr u v → ‖u‖ ≤ 2 * A →
      l' * jcr u v + jcr u e > 0 := by
    intro u v huv hu
    have h1 : 1 / 2 * (A * R / 2) ≤ l' * jcr u v :=
      mul_le_mul hl' huv (by positivity) (by linarith)
    have h2 := sw3_jcr_le u e
    have h3 : ‖u‖ * ‖e‖ ≤ 2 * A * (2 * D) := mul_le_mul hu hen (norm_nonneg _) (by linarith)
    have h4 : A * (32 * D) < A * R := mul_lt_mul_of_pos_left h16 hA
    have := (abs_le.1 h2).1
    have : 0 ≤ A * D := by positivity
    linarith
  have hkey2 : ∀ u v : Pt, A * R / 2 ≤ jcr v u → ‖u‖ ≤ 2 * A →
      l' * jcr u v + jcr u e < 0 := by
    intro u v huv hu
    have h1 : 1 / 2 * (A * R / 2) ≤ l' * jcr v u :=
      mul_le_mul hl' huv (by positivity) (by linarith)
    have h2 := sw3_jcr_le u e
    have h3 : ‖u‖ * ‖e‖ ≤ 2 * A * (2 * D) := mul_le_mul hu hen (norm_nonneg _) (by linarith)
    have h4 : A * (32 * D) < A * R := mul_lt_mul_of_pos_left h16 hA
    have := (abs_le.1 h2).2
    have : 0 ≤ A * D := by positivity
    rw [jcr_anti v u]
    linarith
  rcases le_or_gt (t - b) (2 * N - 1) with h | h
  · right
    have hj := sw3P_jcr_int hA hR h8 (a := b) (b := t) (by omega) h
    have := hkey _ _ hj (sw3P_norm_le hA _)
    rw [hsc, jcr_anti, jcr_add_right, jcr_smul_right]
    linarith
  · left
    have hj := sw3P_jcr_int hA hR h8 (a := t) (b := a + 4 * N * 1) (by omega) (by omega)
    have e1 := sw3P_int_shift h8 a 1
    rw [e1] at hj
    have := hkey2 _ _ hj (sw3P_norm_le hA _)
    rw [hsc, jcr_add_right, jcr_smul_right]
    exact this

private lemma sw3_pick (n j a b : ℤ) (h : (b + 1 ≤ j ∧ j ≤ a + n - 1) ∨ (b + 1 ≤ j + 1 ∧ j + 1 ≤ a + n - 1) ∨
    (b + 1 ≤ j + n ∧ j + n ≤ a + n - 1) ∨ (b + 1 ≤ j + 1 + n ∧ j + 1 + n ≤ a + n - 1) ∨
    (b + 1 ≤ j - n ∧ j - n ≤ a + n - 1) ∨ (b + 1 ≤ j + 1 - n ∧ j + 1 - n ≤ a + n - 1)) :
    ∃ t q : ℤ, (t = j + n * q ∨ t = j + 1 + n * q) ∧ b + 1 ≤ t ∧ t ≤ a + n - 1 := by
  rcases h with h | h | h | h | h | h
  · exact ⟨_, 0, Or.inl (by ring), h⟩
  · exact ⟨_, 0, Or.inr (by ring), h⟩
  · exact ⟨_, 1, Or.inl (by ring), h⟩
  · exact ⟨_, 1, Or.inr (by ring), h⟩
  · exact ⟨_, -1, Or.inl (by ring), h⟩
  · exact ⟨_, -1, Or.inr (by ring), h⟩

private lemma sw3_perturb {X : PlacedTile P} {x : Pt} (hx : x ∈ X.carrier) {U : Set Pt} (hU : IsOpen U)
    (hxU : x ∈ U) : ∃ z ∈ interior X.carrier, z ∈ U := by
  rw [← tile_regular X] at hx
  obtain ⟨z, hzU, hz⟩ := mem_closure_iff.1 hx U hU hxU
  exact ⟨z, hz, hzU⟩

private lemma sw3_face_band {M : MeshConstants P} {S : Patch P} {c : Pt} {N : ℕ} {R : ℝ}
    (G : AnnularGrouping M S.tiles c N R) (j : Fin (4 * N)) {X : PlacedTile P}
    (hX : X ∈ (G.spokes.piece j).faces) {z : Pt} (hz : z ∈ X.carrier) :
    sw3N (z - c) ≤ (N : ℝ) * R / 2 + R + 3 * M.D ∧
      (z ∈ interior X.carrier → (N : ℝ) * R / 2 ≤ sw3N (z - c)) := by
  constructor
  · have hzH : z ∈ G.H.carrier := by
      unfold FaceGroup.carrier; rw [G.H.carrier_eq]
      exact carrier_subset_support (G.spokes.piece_sub j hX).1 hz
    rw [← sw3_mem_square_iff]
    exact sw3_square_add_sub c _ _ (G.H_upper hzH)
  · intro hzi
    by_contra h
    push_neg at h
    have hzL := G.L_lower (sw3_mem_square_iff.2 h.le)
    unfold FaceGroup.carrier at hzL; rw [G.L.carrier_eq] at hzL
    obtain ⟨C, hC, hzC⟩ := mem_support_iff'.1 hzL
    have hXS := (G.spokes.piece j).faces_sub hX
    have := sw3_tile_unique S.disjoint hXS (G.L.faces_sub hC) hzi hzC
    subst this
    exact (G.spokes.piece_sub j hX).2 hC

private lemma sw3_point_band {M : MeshConstants P} {S : Patch P} {c : Pt} {N : ℕ} {R : ℝ}
    (G : AnnularGrouping M S.tiles c N R) (j : Fin (4 * N)) {X : PlacedTile P}
    (hX : X ∈ (G.spokes.piece j).faces) {x : Pt} (hx : x ∈ X.carrier) :
    (N : ℝ) * R / 2 ≤ sw3N (x - c) := by
  by_contra h
  push_neg at h
  obtain ⟨z, hz, hzU⟩ := sw3_perturb hx isOpen_interior (sw3_mem_interior_square h)
  have h1 := (sw3_face_band G j hX (interior_subset hz)).2 hz
  have h2 := sw3_interior_square hzU
  linarith

private lemma sw3_cont_jcr1 (c V : Pt) : Continuous fun z : Pt => jcr (z - c) V := by
  have h0 : Continuous fun w : Pt => w 0 := PiLp.continuous_apply 2 _ 0
  have h1 : Continuous fun w : Pt => w 1 := PiLp.continuous_apply 2 _ 1
  unfold jcr
  simp only [PiLp.sub_apply]
  fun_prop

private lemma sw3_cont_jcr2 (c V : Pt) : Continuous fun z : Pt => jcr V (z - c) := by
  have h0 : Continuous fun w : Pt => w 0 := PiLp.continuous_apply 2 _ 0
  have h1 : Continuous fun w : Pt => w 1 := PiLp.continuous_apply 2 _ 1
  unfold jcr
  simp only [PiLp.sub_apply]
  fun_prop

private lemma sw3_s_exists {M : MeshConstants P} {S : Patch P} {c : Pt} {N : ℕ} {R : ℝ}
    (hR0 : 0 < R) (hN : 1 ≤ N) (G : AnnularGrouping M S.tiles c N R)
    (hspk : ∀ j, (G.spokes.spoke j).carrier ⊆
      Metric.cthickening M.D (existsAnnularSpokes_ray c N R M.D j))
    (j t : Fin (4 * N)) (ht : (G.spokes.spoke t).carrier ⊆ (G.spokes.piece j).carrier) :
    ∃ Y ∈ (G.spokes.piece j).faces, ∃ s ∈ interior Y.carrier, ∃ l : ℝ,
      ((N : ℝ) * R / 2 - 3 * M.D) / ((N : ℝ) * R / 2) ≤ l ∧
      l ≤ ((N : ℝ) * R / 2 + R + 6 * M.D) / ((N : ℝ) * R / 2) ∧
      dist s (c + l • squarePerimeterPoint ((N : ℝ) * R / 2) (((t : ℕ) : ℝ) * R)) ≤ 2 * M.D := by
  have hD := M.D_pos
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  have hu : (G.spokes.spoke t).start ∈ (G.spokes.spoke t).carrier ∩ frontier G.L.carrier := by
    rw [G.spokes.meets_L t]; rfl
  obtain ⟨l, hl1, hl2, hl⟩ := sw3_ray_near hR0.le hD.le hA hD.le (hspk t hu.1)
  have hz := ht hu.1
  unfold FaceGroup.carrier at hz; rw [(G.spokes.piece j).carrier_eq] at hz
  obtain ⟨Y, hY, hzY⟩ := mem_support_iff'.1 hz
  obtain ⟨s, hs, hsb⟩ := sw3_perturb hzY Metric.isOpen_ball (Metric.mem_ball_self hD)
  refine ⟨Y, hY, s, hs, l, hl1, hl2, ?_⟩
  have := dist_triangle s (G.spokes.spoke t).start (c + l • squarePerimeterPoint ((N : ℝ) * R / 2) (((t : ℕ) : ℝ) * R))
  rw [Metric.mem_ball] at hsb
  linarith

private lemma sw3_spp_fin {N : ℕ} {R : ℝ} (hR : 0 < R) (hN : 1 ≤ N) (j : Fin (4 * N)) :
    squarePerimeterPoint ((N : ℝ) * R / 2) (((j : ℕ) : ℝ) * R) =
      sw3P ((N : ℝ) * R / 2) ((((j : ℕ) : ℤ) : ℝ) * R) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  have hk : ((j : ℕ) : ℝ) + 1 ≤ 4 * N := by exact_mod_cast j.isLt
  rw [Int.cast_natCast, sw3_spp_eq hA (by positivity) (by nlinarith)]

private lemma sw3_spp_rot {N : ℕ} {R : ℝ} (hR : 0 < R) (hN : 1 ≤ N) (j : Fin (4 * N)) :
    squarePerimeterPoint ((N : ℝ) * R / 2) (((finRotate (4 * N) j : ℕ) : ℝ) * R) =
      sw3P ((N : ℝ) * R / 2) (((((j : ℕ) : ℤ) + 1 : ℤ) : ℝ) * R) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  have h8 : 8 * ((N : ℝ) * R / 2) = 4 * N * R := by ring
  rw [sw3_spp_fin hR hN, finRotate_val']
  split_ifs with h
  · have e : (((j : ℕ) : ℤ) + 1 : ℤ) = 0 + 4 * N * 1 := by omega
    rw [e, sw3P_int_shift h8]; simp
  · push_cast; rfl

private lemma sw3_lo_half {A D : ℝ} (hA : 0 < A) (h : 6 * D ≤ A) : 1 / 2 ≤ (A - 3 * D) / A := by
  rw [le_div_iff₀ hA]; linarith

private lemma sw3_final {M : MeshConstants P} {S : Patch P} {c : Pt} {N : ℕ} {R : ℝ} (hN : 2 ≤ N)
    (hR : 1000 * M.D ≤ R) (G : AnnularGrouping M S.tiles c N R)
    (hspk : ∀ j, (G.spokes.spoke j).carrier ⊆
      Metric.cthickening M.D (existsAnnularSpokes_ray c N R M.D j))
    (j : Fin (4 * N)) {x : Pt} {X : PlacedTile P} (hX : X ∈ (G.spokes.piece j).faces)
    (hxX : x ∈ X.carrier) {a b t q : ℤ} (hab1 : 1 ≤ b - a) (hab2 : b - a ≤ 2) (ht1 : b + 1 ≤ t)
    (ht2 : t ≤ a + 4 * N - 1) (htj : t = ((j : ℕ) : ℤ) + 4 * N * q ∨ t = ((j : ℕ) : ℤ) + 1 + 4 * N * q)
    (hxa : ∀ l, ((N : ℝ) * R / 2 - 3 * M.D) / ((N : ℝ) * R / 2) ≤ l →
      l ≤ ((N : ℝ) * R / 2 + R + 6 * M.D) / ((N : ℝ) * R / 2) →
      4 * M.D < dist x (c + l • sw3P ((N : ℝ) * R / 2) ((a : ℝ) * R)))
    (hxb : ∀ l, ((N : ℝ) * R / 2 - 3 * M.D) / ((N : ℝ) * R / 2) ≤ l →
      l ≤ ((N : ℝ) * R / 2 + R + 6 * M.D) / ((N : ℝ) * R / 2) →
      4 * M.D < dist x (c + l • sw3P ((N : ℝ) * R / 2) ((b : ℝ) * R)))
    (hα : 0 < jcr (x - c) (sw3P ((N : ℝ) * R / 2) ((b : ℝ) * R)))
    (hβ : 0 < jcr (sw3P ((N : ℝ) * R / 2) ((a : ℝ) * R)) (x - c)) : False := by
  set A := (N : ℝ) * R / 2 with hAdef
  set D := M.D with hDdef
  have hD : 0 < D := M.D_pos
  have hR0 : 0 < R := by linarith
  have hN1 : 1 ≤ N := by omega
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < A := by rw [hAdef]; positivity
  have hAR : R ≤ A := by rw [hAdef]; nlinarith
  have h8 : 8 * A = 4 * N * R := by rw [hAdef]; ring
  have hlo := sw3_lo_half hA (show 6 * D ≤ A by linarith)
  set Va := sw3P A ((a : ℝ) * R) with hVa
  set Vb := sw3P A ((b : ℝ) * R) with hVb
  obtain ⟨af, haf⟩ := sw3_fin_of_int hR0 hN1 a
  obtain ⟨bf, hbf⟩ := sw3_fin_of_int hR0 hN1 b
  -- perturbation of `x`
  set U : Set Pt := {z | 0 < jcr (z - c) Vb} ∩ {z | 0 < jcr Va (z - c)} ∩ Metric.ball x (D / 2) with hU
  have hUo : IsOpen U :=
    ((isOpen_lt continuous_const (sw3_cont_jcr1 c Vb)).inter
      (isOpen_lt continuous_const (sw3_cont_jcr2 c Va))).inter Metric.isOpen_ball
  obtain ⟨x', hx'X, ⟨⟨hx'1, hx'2⟩, hx'3⟩⟩ := sw3_perturb hxX hUo ⟨⟨hα, hβ⟩, Metric.mem_ball_self (by linarith)⟩
  rw [Metric.mem_ball] at hx'3
  -- the test spoke
  obtain ⟨tf, htf, htfe⟩ : ∃ tf : Fin (4 * N), (G.spokes.spoke tf).carrier ⊆ (G.spokes.piece j).carrier ∧
      squarePerimeterPoint A (((tf : ℕ) : ℝ) * R) = sw3P A ((t : ℝ) * R) := by
    rcases htj with h | h
    · refine ⟨j, (G.spokes.piece_between j).1, ?_⟩
      rw [sw3_spp_fin hR0 hN1, h, sw3P_int_shift h8]
    · refine ⟨finRotate (4 * N) j, (G.spokes.piece_between j).2, ?_⟩
      rw [sw3_spp_rot hR0 hN1, h, sw3P_int_shift h8]
  obtain ⟨Y, hY, s, hsY, l', hl'1, hl'2, hs⟩ := sw3_s_exists hR0 hN1 G hspk j tf htf
  rw [htfe] at hs
  have hbfa : sw3P A ((b : ℝ) * R) = sw3P A ((a : ℝ) * R + ((b : ℝ) - a) * R) := by ring_nf
  have hba1 : (1 : ℝ) ≤ (b : ℝ) - a := by exact_mod_cast hab1
  have hba2 : (b : ℝ) - a ≤ 2 := by exact_mod_cast hab2
  refine sw3_contra hN hR G hspk j af bf ?_ ?_ hX hY hx'X hsY ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try simp only [haf, hbf]
  · rw [hbfa]; exact sw3_jcr_pos hA _ (by nlinarith) (by nlinarith)
  · rw [hbfa]; exact sw3_inner_nonneg hA _ (by nlinarith) (by nlinarith)
  · exact (sw3_face_band G j hX (interior_subset hx'X)).2 hx'X
  · exact (sw3_face_band G j hX (interior_subset hx'X)).1
  · intro l h1 h2
    have := hxa l h1 h2
    have := dist_triangle x x' (c + l • Va)
    rw [dist_comm] at hx'3
    linarith
  · intro l h1 h2
    have := hxb l h1 h2
    have := dist_triangle x x' (c + l • Vb)
    rw [dist_comm] at hx'3
    linarith
  · exact hx'1
  · exact hx'2
  · exact (sw3_face_band G j hY (interior_subset hsY)).2 hsY
  · exact (sw3_face_band G j hY (interior_subset hsY)).1
  · intro l h1 h2
    exact sw3_sep_far hA hR0 hAR h8 hN1 (by linarith) (sw3_not_dvd (by omega) (by omega))
      (hlo.trans hl'1) hs (hlo.trans h1)
  · intro l h1 h2
    exact sw3_sep_far hA hR0 hAR h8 hN1 (by linarith) (sw3_not_dvd (by omega) (by omega))
      (hlo.trans hl'1) hs (hlo.trans h1)
  · exact sw3_cone hA hR0 h8 hD.le (by linarith) hab1 hab2 ht1 ht2 (hlo.trans hl'1) hs

private lemma sw3_jcr_x1 {A μ τ s : ℝ} (hA : 0 < A) (hμ : 0 < μ) (hd0 : 0 < τ - s) (hd1 : τ - s ≤ 2 * A)
    {c x : Pt} (hx : x = c + μ • sw3P A τ) : 0 < jcr (sw3P A s) (x - c) := by
  rw [hx, add_sub_cancel_left, jcr_smul_right]
  have := sw3_jcr_pos hA s hd0 hd1
  rw [show s + (τ - s) = τ by ring] at this
  positivity

private lemma sw3_jcr_x2 {A μ τ s : ℝ} (hA : 0 < A) (hμ : 0 < μ) (hd0 : 0 < s - τ) (hd1 : s - τ ≤ 2 * A)
    {c x : Pt} (hx : x = c + μ • sw3P A τ) : 0 < jcr (x - c) (sw3P A s) := by
  rw [hx, add_sub_cancel_left, jcr_smul_left]
  have := sw3_jcr_pos hA τ hd0 hd1
  rw [show τ + (s - τ) = s by ring] at this
  positivity

private lemma sw3_main {M : MeshConstants P} {S : Patch P}
    (c : Pt) {N : ℕ} {R : ℝ} (hN : 2 ≤ N) (hR : 1000 * M.D ≤ R)
    (G : AnnularGrouping M S.tiles c N R)
    (hspk : ∀ j, (G.spokes.spoke j).carrier ⊆
      Metric.cthickening M.D (existsAnnularSpokes_ray c N R M.D j))
    (j : Fin (4 * N)) {x : Pt} (hx : x ∈ (G.spokes.piece j).carrier)
    (hxj : x ∉ Metric.cthickening (5 * M.D) (existsAnnularSpokes_ray c N R M.D j))
    (hxj' : x ∉ Metric.cthickening (5 * M.D) (existsAnnularSpokes_ray c N R M.D ((j : ℕ) + 1))) :
    x ∈ idealTrapezoid c N R M.D (j : ℕ) := by
  have hD : 0 < M.D := M.D_pos
  have hR0 : 0 < R := by linarith
  have hN1 : 1 ≤ N := by omega
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  have hAR : R ≤ (N : ℝ) * R / 2 := by nlinarith
  have h8 : 8 * ((N : ℝ) * R / 2) = 4 * N * R := by ring
  have hlo := sw3_lo_half hA (show 6 * M.D ≤ (N : ℝ) * R / 2 by linarith)
  -- the face containing `x`
  have hx' := hx
  unfold FaceGroup.carrier at hx'; rw [(G.spokes.piece j).carrier_eq] at hx'
  obtain ⟨X, hX, hxX⟩ := mem_support_iff'.1 hx'
  have hx1 := sw3_point_band G j hX hxX
  have hx2 := (sw3_face_band G j hX hxX).1
  set A := (N : ℝ) * R / 2 with hAdef
  set D := M.D with hDdef
  set n := sw3N (x - c) with hn
  have hn0 : 0 < n := by linarith
  set μ := n / A with hμ
  have hμ1 : 1 ≤ μ := by rw [hμ, le_div_iff₀ hA]; linarith
  have hμ2 : μ ≤ (A + R + 3 * D) / A := div_le_div_of_nonneg_right hx2 hA.le
  have hμlo : (A - 3 * D) / A ≤ μ := le_trans (by rw [div_le_one hA]; linarith) hμ1
  have hμhi : μ ≤ (A + R + 6 * D) / A := hμ2.trans (div_le_div_of_nonneg_right (by linarith) hA.le)
  set u := (A / n) • (x - c) with hu
  have hun : sw3N u = A := by
    rw [hu, sw3N_smul, abs_of_pos (by positivity), div_mul_cancel₀ _ hn0.ne']
  obtain ⟨τ, hτ0, hτ1, hτu⟩ := sw3P_surj hA u hun
  have hxeq : x = c + μ • sw3P A τ := by
    rw [hτu, hu, smul_smul, hμ, show n / A * (A / n) = 1 by field_simp, one_smul]; abel
  have hjlt : ((j : ℕ) : ℝ) + 1 ≤ 4 * N := by exact_mod_cast j.isLt
  by_cases hτ : ((j : ℕ) : ℝ) * R ≤ τ ∧ τ ≤ (((j : ℕ) : ℝ) + 1) * R
  · refine ⟨τ, hτ, μ, ⟨hμ1, hμ2⟩, ?_⟩
    rw [sw3_spp_eq hA hτ0 hτ1.le]; exact hxeq
  exfalso
  set k := ⌊τ / R⌋ with hk
  have hkτ : (k : ℝ) * R ≤ τ := by
    have := Int.floor_le (τ / R); rwa [le_div_iff₀ hR0] at this
  have hτk : τ < ((k : ℝ) + 1) * R := by
    have := Int.lt_floor_add_one (τ / R); rwa [div_lt_iff₀ hR0] at this
  have hk0 : 0 ≤ k := Int.floor_nonneg.2 (div_nonneg hτ0 hR0.le)
  have hk1 : k < 4 * N := by
    have h1 : (k : ℝ) < 4 * N := by
      by_contra h; push_neg at h
      have : 4 * (N : ℝ) * R ≤ (k : ℝ) * R := mul_le_mul_of_nonneg_right h hR0.le
      linarith
    exact_mod_cast h1
  have hj0 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := by positivity
  have hj1 : ((j : ℕ) : ℤ) < 4 * N := by exact_mod_cast j.isLt
  have hkj : k ≠ ((j : ℕ) : ℤ) := by
    intro h
    apply hτ
    have h' : (k : ℝ) = ((j : ℕ) : ℝ) := by rw [h]; push_cast; rfl
    rw [← h']
    exact ⟨hkτ, hτk.le⟩
  have hfj := sw3_far_of_not_cthick hR0 hD hN1 (j : ℕ) (by omega) hxj
  have hfj1 := sw3_far_of_not_cthick hR0 hD hN1 ((j : ℕ) + 1) (by omega) hxj'
  have ecast : ((((j : ℕ) + 1 : ℕ) : ℤ) : ℝ) = (((((j : ℕ) : ℤ) + 1 : ℤ)) : ℝ) := by push_cast; ring
  rw [ecast] at hfj1
  set Near : ℤ → Prop := fun m => ∃ l, (A - 3 * D) / A ≤ l ∧ l ≤ (A + R + 6 * D) / A ∧
    dist x (c + l • sw3P A ((m : ℝ) * R)) ≤ 4 * D with hNear
  have hfar_of : ∀ m, ¬ Near m → ∀ l, (A - 3 * D) / A ≤ l → l ≤ (A + R + 6 * D) / A →
      4 * D < dist x (c + l • sw3P A ((m : ℝ) * R)) := by
    intro m hm l h1 h2
    by_contra h; push_neg at h
    exact hm ⟨l, h1, h2, h⟩
  have hexcl : ∀ m m', Near m → Near m' → ¬ (4 * N : ℤ) ∣ m - m' → False := by
    rintro m m' ⟨l, h1, -, hl⟩ ⟨l', h1', -, hl'⟩ hdiv
    exact sw3_near_excl hA hR0 hAR h8 hN1 (by linarith) hdiv (hlo.trans h1) (hlo.trans h1') hl hl'
  have hne_j : ∀ m, Near m → ∀ q : ℤ, m ≠ ((j : ℕ) : ℤ) + 4 * N * q := by
    rintro m ⟨l, h1, h2, hl⟩ q hmq
    have := hfj l h1 h2
    rw [hmq, sw3P_int_shift h8] at hl
    linarith
  have hne_j1 : ∀ m, Near m → ∀ q : ℤ, m ≠ (((j : ℕ) : ℤ) + 1) + 4 * N * q := by
    rintro m ⟨l, h1, h2, hl⟩ q hmq
    have := hfj1 l h1 h2
    rw [hmq, sw3P_int_shift h8] at hl
    linarith
  have hon : τ = (k : ℝ) * R → Near k := by
    intro h
    refine ⟨μ, hμlo, hμhi, ?_⟩
    rw [hxeq, ← h, dist_self]; linarith
  have hμ0 : 0 < μ := by linarith
  have h4N : (8 : ℤ) ≤ 4 * N := by omega
  by_cases hNk : Near k
  · -- near the `k`-th ray: the wedge `[k - 1, k + 1]`
    have hk1' := hne_j k hNk 0
    have hk2' := hne_j1 k hNk 0
    have hk3' := hne_j1 k hNk (-1)
    obtain ⟨t, q, htq, ht1, ht2⟩ := sw3_pick (4 * N) ((j : ℕ) : ℤ) (k - 1) (k + 1) (by omega)
    refine sw3_final hN hR G hspk j hX hxX (a := k - 1) (b := k + 1) (by omega) (by omega) ht1 ht2 htq
      (hfar_of _ (fun h => hexcl k (k - 1) hNk h (sw3_not_dvd (by omega) (by omega))))
      (hfar_of _ (fun h => hexcl (k + 1) k h hNk (sw3_not_dvd (by omega) (by omega)))) ?_ ?_
    · exact sw3_jcr_x2 hA hμ0 (by push_cast; linarith) (by push_cast; linarith) hxeq
    · exact sw3_jcr_x1 hA hμ0 (by push_cast; linarith) (by push_cast; linarith) hxeq
  by_cases hNk1 : Near (k + 1)
  · -- near the `(k+1)`-st ray: the wedge `[k, k + 2]`
    have hk1' := hne_j (k + 1) hNk1 0
    have hk2' := hne_j (k + 1) hNk1 1
    have hτk' : τ ≠ (k : ℝ) * R := fun h => hNk (hon h)
    have hτk2 : (k : ℝ) * R < τ := lt_of_le_of_ne hkτ (Ne.symm hτk')
    obtain ⟨t, q, htq, ht1, ht2⟩ := sw3_pick (4 * N) ((j : ℕ) : ℤ) k (k + 2) (by omega)
    refine sw3_final hN hR G hspk j hX hxX (a := k) (b := k + 2) (by omega) (by omega) ht1 ht2 htq
      (hfar_of _ hNk)
      (hfar_of _ (fun h => hexcl (k + 2) (k + 1) h hNk1 (sw3_not_dvd (by omega) (by omega)))) ?_ ?_
    · exact sw3_jcr_x2 hA hμ0 (by push_cast; linarith) (by push_cast; linarith) hxeq
    · exact sw3_jcr_x1 hA hμ0 (by linarith) (by linarith) hxeq
  · -- far from both rays: the wedge `[k, k + 1]`
    have hτk' : τ ≠ (k : ℝ) * R := fun h => hNk (hon h)
    have hτk2 : (k : ℝ) * R < τ := lt_of_le_of_ne hkτ (Ne.symm hτk')
    obtain ⟨t, q, htq, ht1, ht2⟩ := sw3_pick (4 * N) ((j : ℕ) : ℤ) k (k + 1) (by omega)
    refine sw3_final hN hR G hspk j hX hxX (a := k) (b := k + 1) (by omega) (by omega) ht1 ht2 htq
      (hfar_of _ hNk) (hfar_of _ hNk1) ?_ ?_
    · exact sw3_jcr_x2 hA hμ0 (by push_cast; linarith) (by push_cast; linarith) hxeq
    · exact sw3_jcr_x1 hA hμ0 (by linarith) (by linarith) hxeq

/-- Step 3 of the blueprint proof of `quantitativeAnnularGrouping`: localization away from the
tubes.  Blueprint: "Use the inside-anchored face at `u_j` to join it through that face's
interior to `p_j ∈ int Q₀` ... We obtain proper simple walls `W_j` from zero to infinity,
pairwise disjoint except at zero ... For a point `x ∈ int K₁ \ Q₀` outside the two `5D` radial
tubes, truncate `W_j, W_{j+1}` on a sufficiently large circle and close them along that circle
... Winding number is unchanged, so the actual and ideal wedge labels agree away from the
tubes.  This proves localization there."  A point of the `j`-th annular group outside the
`5D`-neighbourhoods of the `j`-th and `(j+1)`-st extended radial segments lies in the ideal
trapezoid `T_j`. -/
private lemma quantitativeAnnularGrouping_step3_wedges {M : MeshConstants P} {S : Patch P}
    (c : Pt) {N : ℕ} {R : ℝ} (hN : 2 ≤ N) (hR : 1000 * M.D ≤ R)
    (G : AnnularGrouping M S.tiles c N R)
    (hspk : ∀ j, (G.spokes.spoke j).carrier ⊆
      Metric.cthickening M.D (existsAnnularSpokes_ray c N R M.D j))
    (j : Fin (4 * N)) {x : Pt} (hx : x ∈ (G.spokes.piece j).carrier)
    (hxj : x ∉ Metric.cthickening (5 * M.D) (existsAnnularSpokes_ray c N R M.D j))
    (hxj' : x ∉ Metric.cthickening (5 * M.D) (existsAnnularSpokes_ray c N R M.D ((j : ℕ) + 1))) :
    x ∈ idealTrapezoid c N R M.D (j : ℕ) := by
  exact sw3_main c hN hR G hspk j hx hxj hxj'

/-- Step 1 of the blueprint proof of
`quantitativeAnnularGrouping_step4_tubes_step1_clip`: extract a point of the
extended radial segment at the thickening radius. -/
private lemma quantitativeAnnularGrouping_step4_tubes_step1_clip_step1_witness
    (c : Pt) {N : ℕ} {R D : ℝ} (hD : 0 < D) {k : ℕ} {x : Pt}
    (hxr : x ∈ Metric.cthickening (5 * D)
      (existsAnnularSpokes_ray c N R D k)) :
    ∃ y ∈ existsAnnularSpokes_ray c N R D k, dist x y ≤ 5 * D := by
  sorry

/-- Step 2 of the blueprint proof of
`quantitativeAnnularGrouping_step4_tubes_step1_clip`: normalize an extended
radial segment and record the square-boundary properties of its direction. -/
private lemma quantitativeAnnularGrouping_step4_tubes_step1_clip_step2_ray_geometry_aux
    (A t : ℝ) (h0 : 0 ≤ t) (h8 : t ≤ 8 * A) :
    let v := squarePerimeterPoint A t;
    |v 0| ≤ A ∧ |v 1| ≤ A ∧ (|v 0| = A ∨ |v 1| = A) := by
  intro v
  have _ := h0; have _ := h8
  have hA : 0 ≤ A := by linarith
  dsimp [v, squarePerimeterPoint]
  split_ifs with h1 h2 h3
  · refine ⟨by simp [mkPt, abs_of_nonneg hA], ?_, by left; simp [mkPt, abs_of_nonneg hA]⟩
    simp [mkPt]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · refine ⟨?_, by simp [mkPt, abs_of_nonneg hA], by right; simp [mkPt, abs_of_nonneg hA]⟩
    simp [mkPt]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · refine ⟨by simp [mkPt, abs_of_nonneg hA], ?_, by left; simp [mkPt, abs_of_nonneg hA]⟩
    simp [mkPt]; exact abs_le.mpr ⟨by linarith, by linarith⟩
  · refine ⟨?_, by simp [mkPt, abs_of_nonneg hA], by right; simp [mkPt, abs_of_nonneg hA]⟩
    simp [mkPt]; exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma existsAnnularSpokes_pos_eq_squarePerimeterPoint (A t : ℝ) :
    existsAnnularSpokes_pos A t = squarePerimeterPoint A t := rfl

private lemma quantitativeAnnularGrouping_step4_tubes_step1_clip_step2_ray_geometry
    (c : Pt) {N : ℕ} {R D : ℝ} (hD : 0 < D) (hN : 2 ≤ N)
    (hR : 1000 * D ≤ R) (k : ℕ) (hk : k ≤ 4 * N) {y : Pt}
    (hy : y ∈ existsAnnularSpokes_ray c N R D k) :
    ∃ v : Pt,
      v = squarePerimeterPoint ((N : ℝ) * R / 2) ((k : ℝ) * R) ∧
      y ∈ segment ℝ
        (c + (((N : ℝ) * R / 2 - 3 * D) / ((N : ℝ) * R / 2)) • v)
        (c + (((N : ℝ) * R / 2 + R + 6 * D) / ((N : ℝ) * R / 2)) • v) ∧
      |v 0| ≤ (N : ℝ) * R / 2 ∧ |v 1| ≤ (N : ℝ) * R / 2 ∧
      (|v 0| = (N : ℝ) * R / 2 ∨ |v 1| = (N : ℝ) * R / 2) := by
  have _ := hD; have _ := hN; have _ := hR
  use squarePerimeterPoint ((N : ℝ) * R / 2) ((k : ℝ) * R)
  have hk0 : 0 ≤ (k : ℝ) * R := mul_nonneg (by positivity) (by linarith)
  have hk8 : (k : ℝ) * R ≤ 8 * ((N : ℝ) * R / 2) := by
    have h1 : (k : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hk
    have h2 : 0 ≤ R := by linarith
    calc
      (k : ℝ) * R ≤ (4 * (N : ℝ)) * R := mul_le_mul_of_nonneg_right h1 h2
      _ = 8 * ((N : ℝ) * R / 2) := by ring
  have hprops := quantitativeAnnularGrouping_step4_tubes_step1_clip_step2_ray_geometry_aux
    ((N : ℝ) * R / 2) ((k : ℝ) * R) hk0 hk8
  refine ⟨rfl, ?_, hprops.1, hprops.2.1, hprops.2.2⟩
  unfold existsAnnularSpokes_ray at hy
  rw [existsAnnularSpokes_pos_eq_squarePerimeterPoint] at hy
  exact hy

/-- Step 3 of the blueprint proof of
`quantitativeAnnularGrouping_step4_tubes_step1_clip`: the standalone square
clipping estimate for a point close to an extended radial segment. -/
private lemma quantitativeAnnularGrouping_step4_tubes_step1_clip_step3_square_clip
    (c : Pt) {A R D : ℝ} (hD : 0 < D) (hA : 0 < A) (hR : 1000 * D ≤ R)
    (v x y : Pt) (hv : |v 0| ≤ A ∧ |v 1| ≤ A)
    (hvb : |v 0| = A ∨ |v 1| = A)
    (hy : y ∈ segment ℝ (c + ((A - 3 * D) / A) • v)
      (c + ((A + R + 6 * D) / A) • v))
    (hx : x ∈ square c (A + R + 3 * D))
    (hx' : x ∉ interior (square c A)) (hxy : dist x y ≤ 5 * D) :
    ∃ μ ∈ Icc (1 : ℝ) ((A + R + 3 * D) / A),
      dist x (c + μ • v) ≤ 13 * D := by
  sorry

/-- Step 1 of the blueprint proof of `quantitativeAnnularGrouping_step4_tubes`: clipping.
Blueprint: "If `x` lies in one of the tubes, clip its nearest radial-line point to the segment
between infinity norms `A` and `h`.  The clipping moves it by at most `5√2 D`.  Its distance to
the corresponding boundary segment of `T_j` is therefore less than `(1+√2)5D < 13D`."  For a
single extended radial segment, through the `k`-th position `v_k` of `∂Q₀` (`k ≤ 4N`): a point
of the square of half side `(N:ℝ)*R/2 + R + 3*D` about `c`, outside the interior of the square
of half side `(N:ℝ)*R/2` about `c`, within `5D` of that extended radial segment, is within `13D`
of some point `c + μ • v_k` with `μ` in the ideal range `[1, h/A]`
(`A = (N:ℝ)*R/2`, `h = A + R + 3*D`). -/
private lemma quantitativeAnnularGrouping_step4_tubes_step1_clip (c : Pt) {N : ℕ} {R D : ℝ}
    (hD : 0 < D) (hN : 2 ≤ N) (hR : 1000 * D ≤ R) (k : ℕ) (hk : k ≤ 4 * N) {x : Pt}
    (hx : x ∈ square c ((N : ℝ) * R / 2 + R + 3 * D))
    (hx' : x ∉ interior (square c ((N : ℝ) * R / 2)))
    (hxr : x ∈ Metric.cthickening (5 * D) (existsAnnularSpokes_ray c N R D k)) :
    ∃ μ ∈ Icc (1 : ℝ) (((N : ℝ) * R / 2 + R + 3 * D) / ((N : ℝ) * R / 2)),
      dist x (c + μ • squarePerimeterPoint ((N : ℝ) * R / 2) ((k : ℝ) * R)) ≤ 13 * D := by
  have hR0 : 0 < R := by nlinarith
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  obtain ⟨y, hy, hxy⟩ :=
    quantitativeAnnularGrouping_step4_tubes_step1_clip_step1_witness c hD hxr
  obtain ⟨v, hv_eq, hy_seg, hv0, hv1, hvb⟩ :=
    quantitativeAnnularGrouping_step4_tubes_step1_clip_step2_ray_geometry c hD hN hR k hk hy
  obtain ⟨μ, hμ, hdist⟩ :=
    quantitativeAnnularGrouping_step4_tubes_step1_clip_step3_square_clip c hD hA hR v x y
      ⟨hv0, hv1⟩ hvb hy_seg hx hx' hxy
  rw [hv_eq] at hdist
  exact ⟨μ, hμ, hdist⟩

/-- Step 4 of the blueprint proof of `quantitativeAnnularGrouping`: localization in the tubes.
Blueprint: "If `x` lies in one of the tubes, clip its nearest radial-line point to the segment
between infinity norms `A` and `h`.  The clipping moves it by at most `5√2 D`.  Its distance to
the corresponding boundary segment of `T_j` is therefore less than `(1+√2)5D < 13D`."  A point
between `∂Q₀` and `∂K₁` within `5D` of the `j`-th or `(j+1)`-st extended radial segment is
within `13D` of `T_j`. -/
private lemma quantitativeAnnularGrouping_step4_tubes (c : Pt) {N : ℕ} {R D : ℝ} (hD : 0 < D)
    (hN : 2 ≤ N) (hR : 1000 * D ≤ R) (j : Fin (4 * N)) {x : Pt}
    (hx : x ∈ square c ((N : ℝ) * R / 2 + R + 3 * D))
    (hx' : x ∉ interior (square c ((N : ℝ) * R / 2)))
    (ht : x ∈ Metric.cthickening (5 * D) (existsAnnularSpokes_ray c N R D j) ∨
      x ∈ Metric.cthickening (5 * D) (existsAnnularSpokes_ray c N R D ((j : ℕ) + 1))) :
    x ∈ Metric.cthickening (13 * D) (idealTrapezoid c N R D (j : ℕ)) := by
  have hR0 : 0 < R := by linarith
  rcases ht with ht | ht
  · obtain ⟨μ, hμ, hdist⟩ := quantitativeAnnularGrouping_step4_tubes_step1_clip c hD hN hR
      (j : ℕ) (by have := j.isLt; omega) hx hx' ht
    refine Metric.mem_cthickening_of_dist_le x
      (c + μ • squarePerimeterPoint ((N : ℝ) * R / 2) (((j : ℕ) : ℝ) * R)) (13 * D) _ ?_ hdist
    exact ⟨((j : ℕ) : ℝ) * R, ⟨le_refl _, by nlinarith⟩, μ, hμ, rfl⟩
  · obtain ⟨μ, hμ, hdist⟩ := quantitativeAnnularGrouping_step4_tubes_step1_clip c hD hN hR
      ((j : ℕ) + 1) (by have := j.isLt; omega) hx hx' ht
    refine Metric.mem_cthickening_of_dist_le x
      (c + μ • squarePerimeterPoint ((N : ℝ) * R / 2) ((((j : ℕ) + 1 : ℕ) : ℝ) * R)) (13 * D) _
      ?_ hdist
    refine ⟨(((j : ℕ) + 1 : ℕ) : ℝ) * R, ⟨by push_cast; nlinarith, by push_cast; nlinarith⟩, μ,
      hμ, rfl⟩

private lemma step5_spp0 {A t : ℝ} (h : t ≤ 2 * A) : squarePerimeterPoint A t = mkPt A (-A + t) := by
  simp [squarePerimeterPoint, h]

private lemma step5_spp1 {A t : ℝ} (h1 : 2 * A ≤ t) (h : t ≤ 4 * A) :
    squarePerimeterPoint A t = mkPt (3 * A - t) A := by
  unfold squarePerimeterPoint; split_ifs with h' <;> (congr 1 <;> linarith)

private lemma step5_spp2 {A t : ℝ} (hA : 0 ≤ A) (h1 : 4 * A ≤ t) (h : t ≤ 6 * A) :
    squarePerimeterPoint A t = mkPt (-A) (5 * A - t) := by
  unfold squarePerimeterPoint; split_ifs with h' h'' <;> (congr 1 <;> linarith)

private lemma step5_spp3 {A t : ℝ} (hA : 0 ≤ A) (h1 : 6 * A ≤ t) :
    squarePerimeterPoint A t = mkPt (t - 7 * A) (-A) := by
  unfold squarePerimeterPoint; split_ifs with h' h'' h''' <;> (congr 1 <;> linarith)

private lemma step5_spp_bound {A t : ℝ} (h0 : 0 ≤ t) (h8 : t ≤ 8 * A) :
    (squarePerimeterPoint A t 0) ^ 2 + (squarePerimeterPoint A t 1) ^ 2 ≤ 2 * A ^ 2 := by
  unfold squarePerimeterPoint; split_ifs <;> simp [mkPt] <;> nlinarith

private lemma step5_far (v w z q : Pt) (μ A R : ℝ) (hA : 0 < A) (hμ : 0 ≤ μ) (hR : 0 ≤ R)
    (hv : v 0 ^ 2 + v 1 ^ 2 ≤ 2 * A ^ 2) (hw : w 0 ^ 2 + w 1 ^ 2 ≤ 2 * A ^ 2)
    (h1 : A * R / 8 ≤ jcr v z) (h2 : A * R / 8 ≤ jcr z w)
    (hq : jcr v q ≤ 0 ∨ jcr q w ≤ 0) :
    R ^ 2 / 128 ≤ (z 0 - μ * q 0) ^ 2 + (z 1 - μ * q 1) ^ 2 := by
  unfold jcr at *
  set d0 := z 0 - μ * q 0
  set d1 := z 1 - μ * q 1
  have key : ∀ a b : ℝ, a ^ 2 + b ^ 2 ≤ 2 * A ^ 2 → A * R / 8 ≤ a * d1 - b * d0 →
      R ^ 2 / 128 ≤ d0 ^ 2 + d1 ^ 2 := by
    intro a b hab hc
    have hl : (a * d1 - b * d0) ^ 2 ≤ (a ^ 2 + b ^ 2) * (d0 ^ 2 + d1 ^ 2) := by
      nlinarith [sq_nonneg (a * d0 + b * d1)]
    have hpos : 0 ≤ A * R / 8 := by positivity
    have h3 : (A * R / 8) ^ 2 ≤ 2 * A ^ 2 * (d0 ^ 2 + d1 ^ 2) := by
      calc (A * R / 8) ^ 2 ≤ (a * d1 - b * d0) ^ 2 := pow_le_pow_left₀ hpos hc 2
        _ ≤ _ := hl
        _ ≤ _ := mul_le_mul_of_nonneg_right hab (by positivity)
    have hA2 : 0 < A ^ 2 := by positivity
    nlinarith
  rcases hq with hq | hq
  · exact key (v 0) (v 1) hv (by simp only [d0, d1]; nlinarith)
  · exact key (-w 0) (-w 1) (by nlinarith) (by simp only [d0, d1]; nlinarith)

/-- Angular separation: a perimeter position outside `[u, u + R]` (all on one side of `∂Q₀`) lies
weakly outside one of the two bounding rays through `u` and `u + R`. -/
private lemma step5_sign (A R u τ : ℝ) (k : ℕ) (hk : k < 4) (hA : 0 < A) (hR : 0 < R)
    (hu1 : 2 * k * A ≤ u) (hu2 : u + R ≤ 2 * (k + 1) * A) (hτ0 : 0 ≤ τ) (hτ8 : τ ≤ 8 * A)
    (hτ : τ ≤ u ∨ u + R ≤ τ) :
    jcr (squarePerimeterPoint A u) (squarePerimeterPoint A τ) ≤ 0 ∨ jcr (squarePerimeterPoint A τ) (squarePerimeterPoint A (u + R)) ≤ 0 := by
  have hA' := hA.le
  have hτc : τ ≤ 2 * A ∨ (2 * A ≤ τ ∧ τ ≤ 4 * A) ∨ (4 * A ≤ τ ∧ τ ≤ 6 * A) ∨ 6 * A ≤ τ := by
    by_cases h1 : τ ≤ 2 * A
    · exact Or.inl h1
    by_cases h2 : τ ≤ 4 * A
    · exact Or.inr (Or.inl ⟨by linarith, h2⟩)
    by_cases h3 : τ ≤ 6 * A
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith, h3⟩))
    exact Or.inr (Or.inr (Or.inr (by linarith)))
  by_contra hne
  rw [not_or, not_le, not_le] at hne
  obtain ⟨hc1, hc2⟩ := hne
  interval_cases k <;> norm_num at hu1 hu2
  · rw [step5_spp0 (t := u) (by linarith)] at hc1
    rw [step5_spp0 (t := u + R) (by linarith)] at hc2
    rcases hτc with h | ⟨h, h'⟩ | ⟨h, h'⟩ | h
    · rw [step5_spp0 h] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith
    · rw [step5_spp1 h h'] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith
    · rw [step5_spp2 hA' h h'] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith
    · rw [step5_spp3 hA' h] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith
  · rw [step5_spp1 (t := u) (by linarith) (by linarith)] at hc1
    rw [step5_spp1 (t := u + R) (by linarith) (by linarith)] at hc2
    rcases hτc with h | ⟨h, h'⟩ | ⟨h, h'⟩ | h
    · rw [step5_spp0 h] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith
    · rw [step5_spp1 h h'] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith
    · rw [step5_spp2 hA' h h'] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith
    · rw [step5_spp3 hA' h] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith
  · rw [step5_spp2 (t := u) hA' (by linarith) (by linarith)] at hc1
    rw [step5_spp2 (t := u + R) hA' (by linarith) (by linarith)] at hc2
    rcases hτc with h | ⟨h, h'⟩ | ⟨h, h'⟩ | h
    · rw [step5_spp0 h] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith
    · rw [step5_spp1 h h'] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith
    · rw [step5_spp2 hA' h h'] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith
    · rw [step5_spp3 hA' h] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith
  · rw [step5_spp3 (t := u) hA' (by linarith)] at hc1
    rw [step5_spp3 (t := u + R) hA' (by linarith)] at hc2
    rcases hτc with h | ⟨h, h'⟩ | ⟨h, h'⟩ | h
    · rw [step5_spp0 h] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith
    · rw [step5_spp1 h h'] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith
    · rw [step5_spp2 hA' h h'] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith
    · rw [step5_spp3 hA' h] at hc1 hc2
      simp [jcr, mkPt] at hc1 hc2
      rcases hτ with hτ | hτ <;> nlinarith

/-- A point strictly inside the cone of `T_j` (by the cross-product margin `AR/8`) is at distance
at least `22D` from every other ideal trapezoid. -/
private lemma step5_farFromOthers {c : Pt} {N : ℕ} {R D : ℝ} (hN : 2 ≤ N) (hD : 0 < D)
    (hR : 1000 * D ≤ R) (j : Fin (4 * N)) (k : ℕ) (hk : k < 4)
    (hu1 : 2 * k * ((N : ℝ) * R / 2) ≤ ((j : ℕ) : ℝ) * R)
    (hu2 : ((j : ℕ) : ℝ) * R + R ≤ 2 * (k + 1) * ((N : ℝ) * R / 2)) (p : Pt)
    (h1 : (N : ℝ) * R / 2 * R / 8 ≤ jcr (squarePerimeterPoint ((N : ℝ) * R / 2) (((j : ℕ) : ℝ) * R)) (p - c))
    (h2 : (N : ℝ) * R / 2 * R / 8 ≤
      jcr (p - c) (squarePerimeterPoint ((N : ℝ) * R / 2) (((j : ℕ) : ℝ) * R + R)))
    (t : Fin (4 * N)) (ht : t ≠ j) (q : Pt) (hq : q ∈ idealTrapezoid c N R D (t : ℕ)) :
    22 * D ≤ dist p q := by
  obtain ⟨τ, ⟨hτ1, hτ2⟩, μ, ⟨hμ1, -⟩, rfl⟩ := hq
  have hRpos : 0 < R := by linarith
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  have htN : ((t : ℕ) : ℝ) + 1 ≤ 4 * N := by
    have := t.isLt; exact_mod_cast (show (t : ℕ) + 1 ≤ 4 * N by omega)
  have hjN : ((j : ℕ) : ℝ) + 1 ≤ 4 * N := by
    have := j.isLt; exact_mod_cast (show (j : ℕ) + 1 ≤ 4 * N by omega)
  have hτ0 : 0 ≤ τ := le_trans (by positivity) hτ1
  have hτ8 : τ ≤ 8 * ((N : ℝ) * R / 2) := by nlinarith
  have hτ : τ ≤ ((j : ℕ) : ℝ) * R ∨ ((j : ℕ) : ℝ) * R + R ≤ τ := by
    have : (t : ℕ) ≠ (j : ℕ) := fun h => ht (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne this with h | h
    · left
      have : ((t : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast h
      nlinarith
    · right
      have : ((j : ℕ) : ℝ) + 1 ≤ (t : ℕ) := by exact_mod_cast h
      nlinarith
  have hsign := step5_sign _ _ _ _ k hk hA hRpos hu1 hu2 hτ0 hτ8 hτ
  have hv := step5_spp_bound (A := (N : ℝ) * R / 2) (t := ((j : ℕ) : ℝ) * R) (by positivity) (by nlinarith)
  have hw := step5_spp_bound (A := (N : ℝ) * R / 2) (t := ((j : ℕ) : ℝ) * R + R) (by positivity)
    (by nlinarith)
  have key := step5_far _ _ (p - c) _ μ _ R hA (by linarith) hRpos.le hv hw h1 h2 hsign
  have hd : dist p (c + μ • squarePerimeterPoint ((N : ℝ) * R / 2) τ) ^ 2 =
      ((p - c) 0 - μ * squarePerimeterPoint ((N : ℝ) * R / 2) τ 0) ^ 2 +
        ((p - c) 1 - μ * squarePerimeterPoint ((N : ℝ) * R / 2) τ 1) ^ 2 := by
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
    simp [Real.dist_eq, sq_abs]
    ring
  have hdn := dist_nonneg (x := p) (y := c + μ • squarePerimeterPoint ((N : ℝ) * R / 2) τ)
  nlinarith

private lemma step5_reduced {A R D y x s : ℝ} (hA : 0 < A) (hD : 0 < D) (hR : 1000 * D ≤ R)
    (hRA : R ≤ A) (hy1 : -A ≤ y) (hy2 : y ≤ A - R) (hx1 : A + R + 2 * D ≤ x)
    (hx2 : x ≤ A + R + 4 * D) (hs1 : y * (A + R + 2 * D) / A + R / 8 + 2 * D ≤ s)
    (hs2 : s ≤ y * (A + R + 2 * D) / A + R / 8 + 2 * D + R / 2) :
    A * R / 8 ≤ A * s - y * x ∧ A * R / 8 ≤ x * (y + R) - s * A ∧ |s| ≤ A + R + 2 * D := by
  have e : y * (A + R + 2 * D) / A * A = y * (A + R + 2 * D) := by field_simp
  have hs1' : y * (A + R + 2 * D) + A * (R / 8 + 2 * D) ≤ A * s := by nlinarith
  have hs2' : A * s ≤ y * (A + R + 2 * D) + A * (R / 8 + 2 * D + R / 2) := by nlinarith
  refine ⟨by nlinarith, by nlinarith, abs_le.2 ⟨?_, ?_⟩⟩
  · nlinarith
  · nlinarith

private lemma step5_square_add_subset {c : Pt} {h r : ℝ} : square c h + Binf r ⊆ square c (h + r) := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  refine ⟨?_, ?_⟩
  · simp only [PiLp.add_apply]
    calc |a 0 + b 0 - c 0| = |(a 0 - c 0) + b 0| := by ring_nf
      _ ≤ |a 0 - c 0| + |b 0| := abs_add_le _ _
      _ ≤ h + r := add_le_add ha.1 hb.1
  · simp only [PiLp.add_apply]
    calc |a 1 + b 1 - c 1| = |(a 1 - c 1) + b 1| := by ring_nf
      _ ≤ |a 1 - c 1| + |b 1| := abs_add_le _ _
      _ ≤ h + r := add_le_add ha.2 hb.2

private lemma step5_tile_dist_le (M : MeshConstants P) (A : PlacedTile P) {x y : Pt}
    (hx : x ∈ A.carrier) (hy : y ∈ A.carrier) : dist x y ≤ M.D := by
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  simp only [vadd_eq_add, dist_add_left]
  exact (Metric.dist_le_diam_of_mem (P.disk A.form).compact.isBounded hx' hy').trans (M.diam_le _)

private lemma step5_frontier_hit {K : Set Pt} {γ : ℝ → Pt} (hγ : Continuous γ) {x0 x1 : ℝ}
    (hx : x0 ≤ x1) (h0 : γ x0 ∈ K) (h1 : γ x1 ∉ K) :
    ∃ x ∈ Icc x0 x1, γ x ∈ frontier K := by
  have hpc : IsPreconnected (γ '' Icc x0 x1) := isPreconnected_Icc.image _ hγ.continuousOn
  obtain ⟨_, ⟨x, hx, rfl⟩, hz1, hz2⟩ := isPreconnected_closed_iff.1 hpc (closure K) (closure Kᶜ)
    isClosed_closure isClosed_closure
    (fun z _ => by
      by_cases hz : z ∈ K
      · exact Or.inl (subset_closure hz)
      · exact Or.inr (subset_closure hz))
    ⟨γ x0, ⟨x0, left_mem_Icc.2 hx, rfl⟩, subset_closure h0⟩
    ⟨γ x1, ⟨x1, right_mem_Icc.2 hx, rfl⟩, subset_closure h1⟩
  refine ⟨x, hx, ?_⟩
  rw [frontier_eq_closure_inter_closure]; exact ⟨hz1, hz2⟩

/-- If a path crosses `∂H` while staying away from `L` and from the other ideal trapezoids, the
crossing point lies on a private outer edge of the `j`-th group. -/
private lemma step5_core {M : MeshConstants P} {S : Patch P} {c : Pt} {N : ℕ} {R : ℝ}
    (G : AnnularGrouping M S.tiles c N R)
    (hloc : ∀ j : Fin (4 * N), (G.spokes.piece j).carrier ⊆
      Metric.cthickening (20 * M.D) (idealTrapezoid c N R M.D (j : ℕ)))
    (j : Fin (4 * N)) (f : Pt → ℝ) (s : ℝ) (γ : ℝ → Pt) (hγ : Continuous γ) {x0 x1 : ℝ}
    (hx : x0 ≤ x1) (h0 : γ x0 ∈ G.H.carrier) (h1 : γ x1 ∉ G.H.carrier)
    (hfs : ∀ x ∈ Icc x0 x1, f (γ x) = s) (hL : ∀ x ∈ Icc x0 x1, γ x ∉ G.L.carrier)
    (hfar : ∀ x ∈ Icc x0 x1, ∀ t : Fin (4 * N), t ≠ j → ∀ q ∈ idealTrapezoid c N R M.D (t : ℕ),
      22 * M.D ≤ dist (γ x) q) :
    ∃ e ∈ privateOuterEdges G j, ∃ p ∈ e, f p = s := by
  obtain ⟨x, hxI, hxf⟩ := step5_frontier_hit hγ hx h0 h1
  have hfr : frontier G.H.carrier = ⋃ i, G.H.disk.side i := G.H.disk.frontier_eq
  have hxf' := hxf
  rw [hfr, mem_iUnion] at hxf'
  obtain ⟨i, hi⟩ := hxf'
  obtain ⟨A, hAH, iA, hA⟩ := G.H.side_whole i
  obtain ⟨F, hFS, hFH, ⟨iF, hF⟩, -⟩ := G.H_anchor i
  have hpA : γ x ∈ A.carrier := tile_side_subset A iA (hA ▸ hi)
  have hpF : γ x ∈ F.carrier := tile_side_subset F iF (hF ▸ hi)
  -- distance bound to the other trapezoids, in extended form
  have hfarE : ∀ t : Fin (4 * N), t ≠ j → ∀ y, dist y (γ x) ≤ M.D →
      y ∉ (G.spokes.piece t).carrier := by
    intro t ht y hy hyt
    have h1 := hloc t hyt
    rw [Metric.mem_cthickening_iff] at h1
    have h2 : ENNReal.ofReal (22 * M.D) ≤ Metric.infEDist (γ x) (idealTrapezoid c N R M.D (t : ℕ)) := by
      rw [Metric.le_infEDist]
      intro q hq
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (hfar x hxI t ht q hq)
    have h3 := Metric.infEDist_le_infEDist_add_edist (x := γ x) (y := y)
      (s := idealTrapezoid c N R M.D (t : ℕ))
    rw [edist_dist, dist_comm] at h3
    have h4 : ENNReal.ofReal (22 * M.D) ≤ ENNReal.ofReal (20 * M.D) + ENNReal.ofReal M.D :=
      h2.trans (h3.trans (add_le_add h1 (ENNReal.ofReal_le_ofReal hy)))
    rw [← ENNReal.ofReal_add (by linarith [M.D_pos]) M.D_pos.le] at h4
    have := (ENNReal.ofReal_le_ofReal_iff (by linarith [M.D_pos])).1 h4
    linarith [M.D_pos]
  have hAj : A ∈ (G.spokes.piece j).faces := by
    have hAL : A ∉ G.L.faces := by
      intro hAL
      apply hL x hxI
      show γ x ∈ G.L.disk.carrier
      rw [G.L.carrier_eq]
      exact carrier_subset_support hAL hpA
    obtain ⟨t, ht, -⟩ := (G.spokes.piece_partition A (G.H.faces_sub hAH)).1 ⟨hAH, hAL⟩
    by_cases htj : t = j
    · exact htj ▸ ht
    · exfalso
      apply hfarE t htj (γ x) (by simp [M.D_pos.le])
      show γ x ∈ (G.spokes.piece t).disk.carrier
      rw [(G.spokes.piece t).carrier_eq]
      exact carrier_subset_support ht hpA
  refine ⟨G.H.disk.side i, ⟨⟨A, hAj, iA, hA⟩, ?_, F, hFS, hFH, ⟨iF, hF⟩, ?_⟩, γ x, hi, hfs x hxI⟩
  · rw [hfr]; exact subset_iUnion (fun i => G.H.disk.side i) i
  · intro t ht
    rw [Set.disjoint_left]
    intro y hyF hyt
    exact hfarE t ht y (step5_tile_dist_le M F hyF hpF) hyt

/-- The side-independent part of step 5: given a coordinate system adapted to the side of `∂K₁`
carrying `T_j`, every value of the side coordinate in the middle interval is hit. -/
private lemma step5_side {M : MeshConstants P} {S : Patch P} {c : Pt} {N : ℕ} {R : ℝ} (hN : 2 ≤ N)
    (hR : 1000 * M.D ≤ R) (G : AnnularGrouping M S.tiles c N R)
    (hloc : ∀ j : Fin (4 * N), (G.spokes.piece j).carrier ⊆
      Metric.cthickening (20 * M.D) (idealTrapezoid c N R M.D (j : ℕ)))
    (j : Fin (4 * N)) (k : ℕ) (hk : k < 4)
    (hu1 : 2 * k * ((N : ℝ) * R / 2) ≤ ((j : ℕ) : ℝ) * R)
    (hu2 : ((j : ℕ) : ℝ) * R + R ≤ 2 * (k + 1) * ((N : ℝ) * R / 2))
    (y : ℝ) (hy1 : -((N : ℝ) * R / 2) ≤ y) (hy2 : y ≤ (N : ℝ) * R / 2 - R)
    (f : Pt → ℝ) (g : ℝ → ℝ) (a : ℝ) (Z : ℝ → ℝ → Pt) (hZc : ∀ s, Continuous (Z s))
    (hfZ : ∀ s x, f (Z s x) = s)
    (hg : ∀ s ∈ Icc a (a + R / 2),
      y * ((N : ℝ) * R / 2 + R + 2 * M.D) / ((N : ℝ) * R / 2) + R / 8 + 2 * M.D ≤ g s ∧
      g s ≤ y * ((N : ℝ) * R / 2 + R + 2 * M.D) / ((N : ℝ) * R / 2) + R / 8 + 2 * M.D + R / 2)
    (hgabs : ∀ s, |g s| = |s|)
    (hZsq : ∀ s x, (|Z s x 0 - c 0| = |x| ∧ |Z s x 1 - c 1| = |s|) ∨
      (|Z s x 0 - c 0| = |s| ∧ |Z s x 1 - c 1| = |x|))
    (hcr1 : ∀ s x, jcr (squarePerimeterPoint ((N : ℝ) * R / 2) (((j : ℕ) : ℝ) * R)) (Z s x - c) =
      (N : ℝ) * R / 2 * g s - y * x)
    (hcr2 : ∀ s x, jcr (Z s x - c) (squarePerimeterPoint ((N : ℝ) * R / 2) (((j : ℕ) : ℝ) * R + R)) =
      x * (y + R) - g s * ((N : ℝ) * R / 2)) :
    ∀ s ∈ Icc a (a + R / 2), ∃ e ∈ privateOuterEdges G j, ∃ p ∈ e, f p = s := by
  intro s hs
  have hD := M.D_pos
  have hRpos : 0 < R := by linarith
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  have hRA : R ≤ (N : ℝ) * R / 2 := by nlinarith
  have red : ∀ x ∈ Icc ((N : ℝ) * R / 2 + R + 2 * M.D) ((N : ℝ) * R / 2 + R + 4 * M.D),
      (N : ℝ) * R / 2 * R / 8 ≤ (N : ℝ) * R / 2 * g s - y * x ∧
      (N : ℝ) * R / 2 * R / 8 ≤ x * (y + R) - g s * ((N : ℝ) * R / 2) ∧
      |g s| ≤ (N : ℝ) * R / 2 + R + 2 * M.D := fun x hx =>
    step5_reduced hA hD hR hRA hy1 hy2 hx.1 hx.2 (hg s hs).1 (hg s hs).2
  have hsabs : |s| ≤ (N : ℝ) * R / 2 + R + 2 * M.D :=
    hgabs s ▸ (red _ ⟨le_rfl, by linarith⟩).2.2
  refine step5_core G hloc j f s (Z s) (hZc s) (x0 := (N : ℝ) * R / 2 + R + 2 * M.D)
    (x1 := (N : ℝ) * R / 2 + R + 4 * M.D) (by linarith) ?_ ?_ (fun x _ => hfZ s x) ?_ ?_
  · apply G.H_lower
    apply rg_square_add (by positivity) (by positivity)
    have hx0 : |(N : ℝ) * R / 2 + R + 2 * M.D| = (N : ℝ) * R / 2 + R + 2 * M.D := abs_of_pos (by positivity)
    rcases hZsq s ((N : ℝ) * R / 2 + R + 2 * M.D) with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact ⟨h0.trans_le hx0.le, h1.trans_le hsabs⟩
    · exact ⟨h0.trans_le hsabs, h1.trans_le hx0.le⟩
  · intro hmem
    have hsq := step5_square_add_subset (G.H_upper hmem)
    have hx1 : |(N : ℝ) * R / 2 + R + 4 * M.D| = (N : ℝ) * R / 2 + R + 4 * M.D := abs_of_pos (by positivity)
    rcases hZsq s ((N : ℝ) * R / 2 + R + 4 * M.D) with ⟨h0, -⟩ | ⟨-, h1⟩
    · have := hsq.1; rw [h0, hx1] at this; linarith
    · have := hsq.2; rw [h1, hx1] at this; linarith
  · intro x hx hmem
    have hsq := step5_square_add_subset (G.L_upper hmem)
    have hxa : |x| = x := abs_of_pos (by linarith [hx.1])
    rcases hZsq s x with ⟨h0, -⟩ | ⟨-, h1⟩
    · have := hsq.1; rw [h0, hxa] at this; linarith [hx.1]
    · have := hsq.2; rw [h1, hxa] at this; linarith [hx.1]
  · intro x hx t ht q hq
    exact step5_farFromOthers hN hD hR j k hk hu1 hu2 (Z s x) (by rw [hcr1]; exact (red x hx).1)
      (by rw [hcr2]; exact (red x hx).2.1) t ht q hq

private lemma step5_mkPt_continuous {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x : ℝ => mkPt (f x) (g x)) := by
  unfold mkPt
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i <;> simpa

private lemma step5_coord_lipschitz (c : Pt) (i : Fin 2) : LipschitzWith 1 (fun p : Pt => p i - c i) :=
  LipschitzWith.of_dist_le_mul fun p q => by
    rw [Real.dist_eq, NNReal.coe_one, one_mul, show p i - c i - (q i - c i) = p i - q i by ring]
    exact rg_coord_sub_le p q i

/-- Step 5 of the blueprint proof of `quantitativeAnnularGrouping`: private outer edges along the
middle half of the outer side of `T_j`.  Blueprint: "Take the middle half `J` of the outer edge
of `T_j`; its length is `λR/2 ≥ R/2`.  Its distance to every other ideal trapezoid is at least
`R/(4√2)` ... The inward normal from each `y ∈ J` meets `∂H` within its first `D` of length ...
That intersection has distance at least `R/(4√2) - 21D > D` from every other `S_t`.  Its
outside original face, of diameter at most `D`, cannot meet another small group.  Thus `e` is
an ordinary marked private edge of `S_j`."  With `f` the coordinate along the side of `∂K₁`
carrying the outer edge of `T_j` (a `1`-Lipschitz function), every value in an interval of
length `R/2` is attained by `f` on some private outer edge of the `j`-th group. -/
private lemma quantitativeAnnularGrouping_step5_privateHit {M : MeshConstants P} {S : Patch P}
    (c : Pt) {N : ℕ} {R : ℝ} (hN : 2 ≤ N) (hR : 1000 * M.D ≤ R)
    (G : AnnularGrouping M S.tiles c N R)
    (hloc : ∀ j : Fin (4 * N), (G.spokes.piece j).carrier ⊆
      Metric.cthickening (20 * M.D) (idealTrapezoid c N R M.D (j : ℕ)))
    (j : Fin (4 * N)) :
    ∃ f : Pt → ℝ, LipschitzWith 1 f ∧ ∃ a : ℝ,
      ∀ s ∈ Icc a (a + R / 2), ∃ e ∈ privateOuterEdges G j, ∃ p ∈ e, f p = s := by
  have hD := M.D_pos
  have hRpos : 0 < R := by linarith
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : 0 < (N : ℝ) * R / 2 := by positivity
  obtain ⟨k, hk, hk1, hk2⟩ : ∃ k, k < 4 ∧ k * N ≤ (j : ℕ) ∧ (j : ℕ) + 1 ≤ (k + 1) * N := by
    refine ⟨(j : ℕ) / N, (Nat.div_lt_iff_lt_mul (by omega)).2 j.isLt, Nat.div_mul_le_self _ _, ?_⟩
    have h1 := Nat.div_add_mod (j : ℕ) N
    have h2 := Nat.mod_lt (j : ℕ) (show N > 0 by omega)
    nlinarith
  have hk1' : (k : ℝ) * N ≤ (j : ℕ) := by exact_mod_cast hk1
  have hk2' : ((j : ℕ) : ℝ) + 1 ≤ ((k : ℝ) + 1) * N := by exact_mod_cast hk2
  have hu1 : 2 * k * ((N : ℝ) * R / 2) ≤ ((j : ℕ) : ℝ) * R := by nlinarith
  have hu2 : ((j : ℕ) : ℝ) * R + R ≤ 2 * (k + 1) * ((N : ℝ) * R / 2) := by nlinarith
  set A := (N : ℝ) * R / 2 with hAdef
  set u := ((j : ℕ) : ℝ) * R with hudef
  interval_cases k <;> norm_num at hu1 hu2
  · refine ⟨fun p => p 1 - c 1, step5_coord_lipschitz c 1,
      ((-A + u) * (A + R + 2 * M.D) / A + R / 8 + 2 * M.D),
      step5_side hN hR G hloc j 0 (by norm_num) (by push_cast; linarith) (by push_cast; linarith) (-A + u)
        (by linarith) (by linarith) _ id _ (fun s x => c + mkPt x s)
        (fun s => continuous_const.add (step5_mkPt_continuous continuous_id continuous_const))
        (fun s x => by simp [mkPt]) (fun s hs => hs) (fun s => rfl)
        (fun s x => Or.inl (by simp [mkPt])) (fun s x => ?_) (fun s x => ?_)⟩
    · rw [step5_spp0 (t := u) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1, id]; ring
    · rw [step5_spp0 (t := u + R) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1, id]; ring
  · refine ⟨fun p => p 0 - c 0, step5_coord_lipschitz c 0,
      (-((u - 3 * A) * (A + R + 2 * M.D) / A + R / 8 + 2 * M.D) - R / 2),
      step5_side hN hR G hloc j 1 (by norm_num) (by push_cast; linarith) (by push_cast; linarith) (u - 3 * A)
        (by linarith) (by linarith) _ (fun s => -s) _ (fun s x => c + mkPt s x)
        (fun s => continuous_const.add (step5_mkPt_continuous continuous_const continuous_id))
        (fun s x => by simp [mkPt]) (fun s hs => by
          rw [hAdef] at hs ⊢; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩) (fun s => abs_neg s)
        (fun s x => Or.inr (by simp [mkPt])) (fun s x => ?_) (fun s x => ?_)⟩
    · rw [step5_spp1 (t := u) (by linarith) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1]; ring
    · rw [step5_spp1 (t := u + R) (by linarith) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1]; ring
  · refine ⟨fun p => p 1 - c 1, step5_coord_lipschitz c 1,
      (-((u - 5 * A) * (A + R + 2 * M.D) / A + R / 8 + 2 * M.D) - R / 2),
      step5_side hN hR G hloc j 2 (by norm_num) (by push_cast; linarith) (by push_cast; linarith) (u - 5 * A)
        (by linarith) (by linarith) _ (fun s => -s) _ (fun s x => c + mkPt (-x) s)
        (fun s => continuous_const.add (step5_mkPt_continuous continuous_neg continuous_const))
        (fun s x => by simp [mkPt]) (fun s hs => by
          rw [hAdef] at hs ⊢; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩) (fun s => abs_neg s)
        (fun s x => Or.inl (by simp [mkPt])) (fun s x => ?_) (fun s x => ?_)⟩
    · rw [step5_spp2 hA.le (t := u) (by linarith) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1]; ring
    · rw [step5_spp2 hA.le (t := u + R) (by linarith) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1]; ring
  · refine ⟨fun p => p 0 - c 0, step5_coord_lipschitz c 0,
      ((u - 7 * A) * (A + R + 2 * M.D) / A + R / 8 + 2 * M.D),
      step5_side hN hR G hloc j 3 (by norm_num) (by push_cast; linarith) (by push_cast; linarith) (u - 7 * A)
        (by linarith) (by linarith) _ id _ (fun s x => c + mkPt s (-x))
        (fun s => continuous_const.add (step5_mkPt_continuous continuous_const continuous_neg))
        (fun s x => by simp [mkPt]) (fun s hs => hs) (fun s => rfl)
        (fun s x => Or.inr (by simp [mkPt])) (fun s x => ?_) (fun s x => ?_)⟩
    · rw [step5_spp3 hA.le (t := u) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1, id]; ring
    · rw [step5_spp3 hA.le (t := u + R) (by linarith)]
      simp only [jcr, add_sub_cancel_left, rg_mkPt0, rg_mkPt1, id]; ring

/-- Step 6 of the blueprint proof of `quantitativeAnnularGrouping`: "each has projected length
at most `D`" -- the private outer edges of a group are finitely many listed sides of its faces,
each of diameter at most `D`. -/
private lemma quantitativeAnnularGrouping_step6_privateFinite {M : MeshConstants P}
    {S : Patch P} {c : Pt} {N : ℕ} {R : ℝ} (G : AnnularGrouping M S.tiles c N R)
    (j : Fin (4 * N)) :
    (privateOuterEdges G j).Finite ∧
      ∀ e ∈ privateOuterEdges G j, ∀ p ∈ e, ∀ q ∈ e, dist p q ≤ M.D := by
  constructor
  · apply (G.spokes.piece j).finite.biUnion (fun A _ => Set.finite_range A.side) |>.subset
    rintro e ⟨⟨A, hA, hAe⟩, -⟩
    rcases hAe with ⟨i, rfl⟩
    exact Set.mem_biUnion hA ⟨i, rfl⟩
  · intro e he p hp q hq
    rcases he.1 with ⟨A, hA, hAe⟩
    rcases hAe with ⟨i, hi⟩
    have hpA : p ∈ A.carrier := by
      apply tile_side_subset A i
      rw [hi]
      exact hp
    have hqA : q ∈ A.carrier := by
      apply tile_side_subset A i
      rw [hi]
      exact hq
    have hdiam : Metric.diam A.carrier ≤ M.D := by
      rw [PlacedTile.carrier, diam_vadd]
      exact M.diam_le A.form
    exact (Metric.dist_le_diam_of_mem (tileDisk A).compact.isBounded hpA hqA).trans hdiam

/-- Step 7 of the blueprint proof of `quantitativeAnnularGrouping`: "The projections of these
private edges cover `J` apart from finitely many points, and each has projected length at most
`D`.  There are consequently at least `|J|/D ≥ R/(2D)` distinct private edge occurrences."
Counting form: if every value in an interval of length `ℓ` is attained by a `1`-Lipschitz
function on one of finitely many sets of diameter at most `D`, there are at least `ℓ / D`
sets. -/
private lemma quantitativeAnnularGrouping_step7_count {D : ℝ} (hD : 0 < D) {E : Set (Set Pt)}
    (hE : E.Finite) (hdiam : ∀ e ∈ E, ∀ p ∈ e, ∀ q ∈ e, dist p q ≤ D) {f : Pt → ℝ}
    (hf : LipschitzWith 1 f) {a ℓ : ℝ}
    (hcov : ∀ s ∈ Icc a (a + ℓ), ∃ e ∈ E, ∃ p ∈ e, f p = s) :
    ℓ / D ≤ E.ncard := by
  rcases le_or_gt ℓ 0 with hl | hl
  · exact (div_nonpos_of_nonpos_of_nonneg hl hD.le).trans (Nat.cast_nonneg _)
  have hsub : Icc a (a + ℓ) ⊆ ⋃ e ∈ hE.toFinset, f '' e := by
    intro s hs
    obtain ⟨e, he, p, hp, rfl⟩ := hcov s hs
    exact mem_biUnion (hE.mem_toFinset.2 he) ⟨p, hp, rfl⟩
  have hdi : ∀ e ∈ hE.toFinset, MeasureTheory.volume (f '' e) ≤ ENNReal.ofReal D := by
    intro e he
    refine (Real.volume_le_diam _).trans (Metric.ediam_le ?_)
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    refine (hf.edist_le_mul p q).trans ?_
    rw [ENNReal.coe_one, one_mul, edist_dist]
    exact ENNReal.ofReal_le_ofReal (hdiam e (hE.mem_toFinset.1 he) p hp q hq)
  have key : ENNReal.ofReal ℓ ≤ ENNReal.ofReal (hE.toFinset.card * D) := by
    calc ENNReal.ofReal ℓ = MeasureTheory.volume (Icc a (a + ℓ)) := by
          rw [Real.volume_Icc]; ring_nf
      _ ≤ MeasureTheory.volume (⋃ e ∈ hE.toFinset, f '' e) := MeasureTheory.measure_mono hsub
      _ ≤ ∑ e ∈ hE.toFinset, MeasureTheory.volume (f '' e) := MeasureTheory.measure_biUnion_finset_le _ _
      _ ≤ ∑ e ∈ hE.toFinset, ENNReal.ofReal D := Finset.sum_le_sum hdi
      _ = ENNReal.ofReal (hE.toFinset.card * D) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  rw [Set.ncard_eq_toFinset_card E hE, div_le_iff₀ hD]
  exact key

private lemma spp_coord_lip (A t s : ℝ) (hA : 0 ≤ A) (i : Fin 2) :
    |squarePerimeterPoint A t i - squarePerimeterPoint A s i| ≤ |t - s| := by
  fin_cases i <;>
  · simp only [squarePerimeterPoint]
    split_ifs <;> simp [mkPt] <;>
      rcases abs_cases (t - s) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1, abs_le] <;> constructor <;> linarith

private lemma spp_coord_bound (A t : ℝ) (hA : 0 ≤ A) (ht0 : 0 ≤ t) (ht : t ≤ 8 * A) (i : Fin 2) :
    |squarePerimeterPoint A t i| ≤ A := by
  fin_cases i <;>
  · simp only [squarePerimeterPoint]
    split_ifs <;> simp [mkPt] <;> rw [abs_le] <;> constructor <;> linarith

private lemma step8_dist_le (c : Pt) {N : ℕ} {R D : ℝ} (hD : 0 < D)
    (hN : 2 ≤ N) (hR : 1000 * D ≤ R) (j : Fin (4 * N)) {x y : Pt}
    (hx : x ∈ idealTrapezoid c N R D (j : ℕ)) (hy : y ∈ idealTrapezoid c N R D (j : ℕ)) :
    dist x y ≤ 2 * (3 * R + 6 * D) := by
  obtain ⟨t, ⟨ht1, ht2⟩, μ, ⟨hμ1, hμ2⟩, rfl⟩ := hx
  obtain ⟨s, ⟨hs1, hs2⟩, ν, ⟨hν1, hν2⟩, rfl⟩ := hy
  set A : ℝ := (N : ℝ) * R / 2 with hAdef
  set l : ℝ := (A + R + 3 * D) / A with hldef
  have hR0 : 0 < R := by linarith
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hAR : R ≤ A := by rw [hAdef]; nlinarith
  have hA0 : 0 < A := by linarith
  have hlA : l * A = A + R + 3 * D := by rw [hldef]; field_simp
  have hj : ((j : ℕ) : ℝ) + 1 ≤ 4 * N := by
    have := j.isLt; exact_mod_cast (show (j : ℕ) + 1 ≤ 4 * N by omega)
  have hj0 : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
  have h8 : ((j : ℝ) + 1) * R ≤ 8 * A := by rw [hAdef]; nlinarith
  have hts : |t - s| ≤ R := by rw [abs_le]; constructor <;> nlinarith
  have hcoord : ∀ i : Fin 2, |(c + μ • squarePerimeterPoint A t) i - (c + ν • squarePerimeterPoint A s) i|
      ≤ 3 * R + 6 * D := by
    intro i
    have e : (c + μ • squarePerimeterPoint A t) i - (c + ν • squarePerimeterPoint A s) i =
        μ * (squarePerimeterPoint A t i - squarePerimeterPoint A s i) + (μ - ν) * squarePerimeterPoint A s i := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e]
    have h1 := spp_coord_lip A t s hA0.le i
    have h2 := spp_coord_bound A s hA0.le (by nlinarith) (by nlinarith) i
    have hμν : |μ - ν| ≤ l - 1 := by rw [abs_le]; constructor <;> linarith
    calc _ ≤ |μ * (squarePerimeterPoint A t i - squarePerimeterPoint A s i)| + |(μ - ν) * squarePerimeterPoint A s i| :=
          abs_add_le _ _
      _ = μ * |squarePerimeterPoint A t i - squarePerimeterPoint A s i| + |μ - ν| * |squarePerimeterPoint A s i| := by
          rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0:ℝ) < μ)]
      _ ≤ l * R + (l - 1) * A := by
          gcongr <;> linarith
      _ ≤ 3 * R + 6 * D := by nlinarith
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  have h0 := hcoord 0
  have h1 := hcoord 1
  rw [Real.sqrt_le_left (by positivity)]
  · rw [Real.dist_eq, Real.dist_eq]
    have := sq_abs ((c + μ • squarePerimeterPoint A t) 0 - (c + ν • squarePerimeterPoint A s) 0)
    have := sq_abs ((c + μ • squarePerimeterPoint A t) 1 - (c + ν • squarePerimeterPoint A s) 1)
    nlinarith [abs_nonneg ((c + μ • squarePerimeterPoint A t) 0 - (c + ν • squarePerimeterPoint A s) 0),
      abs_nonneg ((c + μ • squarePerimeterPoint A t) 1 - (c + ν • squarePerimeterPoint A s) 1)]

/-- Step 8 of the blueprint proof of `quantitativeAnnularGrouping`: "Since `λ ≤ 2 + 3D/R`, each
ideal trapezoid has span at most `5R` along its square side and at most `2R` across it ...
hence diameter less than `6R`.  Localization gives `diam S_j ≤ 7R`."  The closed
`20D`-neighbourhood of an ideal trapezoid is bounded, of diameter at most `7R`. -/
private lemma quantitativeAnnularGrouping_step8_diam (c : Pt) {N : ℕ} {R D : ℝ} (hD : 0 < D)
    (hN : 2 ≤ N) (hR : 1000 * D ≤ R) (j : Fin (4 * N)) :
    Bornology.IsBounded (Metric.cthickening (20 * D) (idealTrapezoid c N R D (j : ℕ))) ∧
      Metric.diam (Metric.cthickening (20 * D) (idealTrapezoid c N R D (j : ℕ))) ≤ 7 * R := by
  have hT : Bornology.IsBounded (idealTrapezoid c N R D (j : ℕ)) :=
    Metric.isBounded_iff.2 ⟨_, fun x hx y hy => step8_dist_le c hD hN hR j hx hy⟩
  refine ⟨hT.cthickening, ?_⟩
  have hd : Metric.diam (idealTrapezoid c N R D (j : ℕ)) ≤ 2 * (3 * R + 6 * D) :=
    Metric.diam_le_of_forall_dist_le (by linarith) fun x hx y hy => step8_dist_le c hD hN hR j hx hy
  have := Metric.diam_cthickening_le (idealTrapezoid c N R D (j : ℕ)) (by linarith : (0:ℝ) ≤ 20 * D)
  linarith

private lemma step9_volume_segment (x y : Pt) : MeasureTheory.volume (segment ℝ x y) = 0 := by
  have hsub : segment ℝ x y ⊆ (affineSpan ℝ ({x, y} : Set Pt) : Set Pt) := by
    rw [segment_eq_image_lineMap]
    rintro _ ⟨t, -, rfl⟩
    exact AffineMap.lineMap_mem_affineSpan_pair t x y
  refine MeasureTheory.measure_mono_null hsub ?_
  refine MeasureTheory.Measure.addHaar_affineSubspace _ _ ?_
  intro htop
  have h1 := (collinear_iff_finrank_le_one (k := ℝ) (s := ({x, y} : Set Pt))).1 (collinear_pair ℝ x y)
  rw [← direction_affineSpan, htop, AffineSubspace.direction_top, finrank_top, finrank_euclideanSpace,
    Fintype.card_fin] at h1
  omega

private lemma step9_volume_frontier (B : PolygonalDisk) : MeasureTheory.volume (frontier B.carrier) = 0 := by
  rw [B.frontier_eq]
  exact MeasureTheory.measure_iUnion_null fun i => step9_volume_segment _ _

private lemma step9_volume_interior (B : PolygonalDisk) :
    MeasureTheory.volume (interior B.carrier) = MeasureTheory.volume B.carrier := by
  refine le_antisymm (MeasureTheory.measure_mono interior_subset) ?_
  calc MeasureTheory.volume B.carrier ≤ MeasureTheory.volume (interior B.carrier ∪ frontier B.carrier) := by
        refine MeasureTheory.measure_mono fun z hz => ?_
        by_cases h : z ∈ interior B.carrier
        · exact Or.inl h
        · exact Or.inr ⟨subset_closure hz, h⟩
    _ ≤ _ := MeasureTheory.measure_union_le _ _
    _ = _ := by rw [step9_volume_frontier, add_zero]

/-- Step 9 of the blueprint proof of `quantitativeAnnularGrouping`: "A square of side `14R`
contains `S_j`, so disjoint constituent interiors of area at least `a` bound their number by
`⌈196R²/a⌉`."  A group of faces whose region has diameter at most `d` has at most `⌈4d²/a⌉`
faces. -/
private lemma quantitativeAnnularGrouping_step9_faces (M : MeshConstants P) {S : Patch P}
    (F : FaceGroup S.tiles) {d : ℝ} (hd : Metric.diam F.carrier ≤ d) :
    F.faces.ncard ≤ ⌈4 * d ^ 2 / M.a⌉₊ := by
  classical
  open MeasureTheory in
  obtain ⟨x, hx⟩ := F.disk.interior_nonempty
  have hxc : x ∈ F.carrier := interior_subset hx
  have hd0 : 0 ≤ d := Metric.diam_nonneg.trans hd
  have hball : F.carrier ⊆ Metric.closedBall x d := fun y hy =>
    Metric.mem_closedBall.2 ((Metric.dist_le_diam_of_mem F.disk.compact.isBounded hy hxc).trans hd)
  set t := F.finite.toFinset with ht
  have hdisj : (↑t : Set (PlacedTile P)).PairwiseDisjoint (fun A => interior A.carrier) := by
    rw [ht, Set.Finite.coe_toFinset]; exact S.disjoint.subset F.faces_sub
  have hmeas := measure_biUnion_finset (μ := volume) hdisj (fun A _ => isOpen_interior.measurableSet)
  have hvolA : ∀ A ∈ t, ENNReal.ofReal M.a ≤ volume (interior A.carrier) := by
    intro A _
    rw [PlacedTile.carrier, interior_vadd, measure_vadd, step9_volume_interior]
    exact M.area_ge A.form
  have hle : volume (⋃ A ∈ t, interior A.carrier) ≤ volume (Metric.closedBall x d) := by
    apply measure_mono
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨A, hA, hzA⟩ := hz
    refine hball ?_
    show z ∈ F.disk.carrier
    rw [F.carrier_eq]
    exact Set.mem_biUnion (by simpa [ht] using hA) (interior_subset hzA)
  rw [hmeas, EuclideanSpace.volume_closedBall_fin_two] at hle
  have hsum : (t.card : ENNReal) * ENNReal.ofReal M.a ≤ ENNReal.ofReal (d ^ 2 * Real.pi) := by
    calc (t.card : ENNReal) * ENNReal.ofReal M.a = ∑ A ∈ t, ENNReal.ofReal M.a := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hvolA
      _ ≤ _ := hle
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hd0]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hsum
  have hcard : F.faces.ncard = t.card := Set.ncard_eq_toFinset_card _ F.finite
  rw [hcard]
  have ha := M.a_pos
  have : (t.card : ℝ) ≤ 4 * d ^ 2 / M.a := by
    rw [le_div_iff₀ ha]
    nlinarith [Real.pi_lt_four, sq_nonneg d]
  exact_mod_cast this.trans (Nat.le_ceil _)

private lemma step10_polygonalDisk_side_injective (B : PolygonalDisk) : Function.Injective B.side := by
  intro i j h
  by_contra hij
  have hab : B.vertex i ≠ B.vertex (finRotate B.n i) := fun he =>
    mesh_finRotate_ne_self (by have := B.three_le; omega) i (B.vertex_injective he).symm
  have hm : midpoint ℝ (B.vertex i) (B.vertex (finRotate B.n i)) ∈ B.side i :=
    midpoint_mem_segment _ _
  have hmj : midpoint ℝ (B.vertex i) (B.vertex (finRotate B.n i)) ∈ B.side j := h ▸ hm
  have := (B.simple i j hij ⟨hm, hmj⟩).1
  rcases this with h1 | h1
  · exact hab ((midpoint_eq_left_iff ℝ).mp h1)
  · exact hab ((midpoint_eq_right_iff ℝ).mp h1)

private lemma step10_placedTile_side_congr {A A' : PlacedTile P} (k : Fin (P.disk A.form).n)
    (k' : Fin (P.disk A'.form).n) (hA : A = A') (hk : (k : ℕ) = k') : A.side k = A'.side k' := by
  subst hA
  rw [Fin.ext hk]

/-- Step 10 of the blueprint proof of `quantitativeAnnularGrouping`: "Retaining all original
vertices proves the stated side bound" -- every listed side of a group is a whole listed side of
one of its faces, and distinct listed sides of a polygonal disk are distinct, so a group has at
most `K₀` listed sides per face. -/
private lemma quantitativeAnnularGrouping_step10_sides (M : MeshConstants P)
    {S : Set (PlacedTile P)} (F : FaceGroup S) : F.disk.n ≤ M.K0 * F.faces.ncard := by
  classical
  choose A hA k hk using F.side_whole
  let g : Fin F.disk.n → PlacedTile P × Fin M.K0 := fun i =>
    (A i, ⟨k i, lt_of_lt_of_le (k i).isLt (M.sides_le _)⟩)
  have hinj : Function.Injective g := by
    intro i j hij
    simp only [g, Prod.mk.injEq, Fin.mk.injEq] at hij
    apply step10_polygonalDisk_side_injective
    rw [← hk i, ← hk j]
    exact step10_placedTile_side_congr _ _ hij.1 hij.2
  have hcard := Finset.card_le_card_of_injOn g (s := Finset.univ)
    (t := F.finite.toFinset ×ˢ (Finset.univ : Finset (Fin M.K0)))
    (fun i _ => by simp [g, hA i]) hinj.injOn
  rw [Finset.card_univ, Fintype.card_fin, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    ← Set.ncard_eq_toFinset_card _ F.finite] at hcard
  linarith [hcard, mul_comm M.K0 F.faces.ncard]

/-- `lem:quantitative-sector`: there are constants `C_sep, C_loc, C_len,
C_err, C`, independent of `N`, of the substitution power and of the patch,
such that for `R ≥ C_sep D` the groupings can be chosen with every annular
group in the `C_loc D`-neighbourhood of its ideal trapezoid, with at least
`⌊R/(C_len D)⌋ - C_err` private outer edges, of diameter at most `C R`, and
with at most `Q(P,R) = K0 ⌈4C²R²/a⌉` listed sides. -/
theorem quantitativeAnnularGrouping (M : MeshConstants P) :
    ∃ Csep Cloc Clen Cerr C : ℝ, 0 < Csep ∧ 0 < Cloc ∧ 0 < Clen ∧ 0 ≤ Cerr ∧ 0 < C ∧
      ∀ (S : Patch P) (Ω : PolygonalDisk), support S.tiles = Ω.carrier →
        SideToSideSet S.tiles → ∀ (c : Pt) (N : ℕ) (R : ℝ), 2 ≤ N → Csep * M.D ≤ R →
        square c ((N : ℝ) * R / 2 + R) + Binf (10 * M.D) ⊆ interior Ω.carrier →
        ∃ G : AnnularGrouping M S.tiles c N R,
          (∀ j : Fin (4 * N), (G.spokes.piece j).carrier ⊆
              Metric.cthickening (Cloc * M.D) (idealTrapezoid c N R M.D (j : ℕ))) ∧
          (∀ j : Fin (4 * N),
              (⌊R / (Clen * M.D)⌋₊ : ℝ) - Cerr ≤ ((privateOuterEdges G j).ncard : ℝ)) ∧
          (∀ j : Fin (4 * N), Metric.diam (G.spokes.piece j).carrier ≤ C * R) ∧
          (∀ j : Fin (4 * N),
              (G.spokes.piece j).disk.n ≤ M.K0 * ⌈4 * C ^ 2 * R ^ 2 / M.a⌉₊) := by
  refine ⟨1000, 20, 2, 0, 7, by norm_num, by norm_num, by norm_num, le_rfl, by norm_num, ?_⟩
  intro S Ω hcov hsts c N R hN hR hΩ
  have hD := M.D_pos
  have hR0 : 0 < R := by linarith
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hA0 : 0 < (N : ℝ) * R / 2 := by nlinarith
  have hb : 0 ≤ (N : ℝ) * R / 2 + R := by linarith
  have hnest0 : square c ((N : ℝ) * R / 2) + Binf (3 * M.D) ⊆
      interior (square c ((N : ℝ) * R / 2 + R) + Binf (10 * M.D)) :=
    existsAnnularSpokes_step1_nest c (by linarith) hb (by linarith)
  have hnest1 : square c ((N : ℝ) * R / 2) + Binf M.D ⊆
      interior (square c ((N : ℝ) * R / 2 + R) + Binf (2 * M.D)) :=
    existsAnnularSpokes_step1_nest c (by linarith) hb (by linarith)
  have hnest2 : square c ((N : ℝ) * R / 2 + R) + Binf (3 * M.D) ⊆
      interior (square c ((N : ℝ) * R / 2 + R) + Binf (10 * M.D)) :=
    existsAnnularSpokes_step1_nest c (by linarith) hb (by linarith)
  have hΩi : interior (square c ((N : ℝ) * R / 2 + R) + Binf (10 * M.D)) ⊆ interior Ω.carrier :=
    (interior_mono hΩ).trans interior_interior.subset
  -- the inside-anchored group `L` and the outside-anchored group `H`
  obtain ⟨L, hL1, hL2, hL3⟩ :=
    regularGrouping M S Ω hcov hsts c ((N : ℝ) * R / 2) hA0 (hnest0.trans hΩi)
  obtain ⟨H, hH1, hH2, hH3, -⟩ :=
    outsideAnchoredGrouping M S Ω hcov hsts c ((N : ℝ) * R / 2 + R) (by linarith) hΩ
  have hLH : L.carrier ⊆ interior H.carrier := hL2.trans (hnest1.trans (interior_mono hH1))
  have hHS : H.carrier ⊆ interior (support S.tiles) := by
    rw [hcov]
    exact hH2.trans (hnest2.trans hΩi)
  -- spokes along the extended radial segments
  have hR100 : 100 * M.D ≤ R := by linarith
  choose α hα using fun j : Fin (4 * N) =>
    existsAnnularSpokes_step3_spoke M S Ω hcov hsts c hN hR100 hΩ L H hL1 hL2 hH1 hH2 j
  have hdisj : ∀ i j, i ≠ j → Disjoint (α i).carrier (α j).carrier := fun _ _ hij =>
    (existsAnnularSpokes_step2_tubes c hD hN hR100 hij).mono (hα _).2.2.2.2.2 (hα _).2.2.2.2.2
  have hstop : ∀ j, (α j).stop ∈ (α j).carrier ∩ frontier H.carrier := fun j => by
    rw [(hα j).2.2.2.2.1]
    exact Set.mem_singleton _
  obtain ⟨γo, hγo, hord⟩ := quantitativeAnnularGrouping_step1_outerOrder c hN hR H hH1 hH2 hH3
    (fun j => (α j).stop) (fun j => (hstop j).2) (fun j => (hα j).2.2.2.2.2 (hstop j).1)
  have horder := existsAnnularSpokes_step5_crosscuts H.disk L.disk hLH α
    (fun j => (hα j).2.2.1) (fun j => (hα j).2.2.2.1) (fun j => (hα j).2.2.2.2.1) hdisj hγo hord
  obtain ⟨T, hT⟩ := existsAnnularSpokes_step6_cut S hsts L H hLH hHS (by omega) α
    (fun j => (hα j).1) (fun j => (hα j).2.1) (fun j => (hα j).2.2.1)
    (fun j => (hα j).2.2.2.1) (fun j => (hα j).2.2.2.2.1) hdisj horder
  let G : AnnularGrouping M S.tiles c N R :=
    { L := L
      H := H
      L_lower := hL1
      L_upper := hL2
      L_anchor := hL3
      H_lower := hH1
      H_upper := hH2
      H_anchor := hH3
      spokes := T }
  have hspk : ∀ j, (G.spokes.spoke j).carrier ⊆
      Metric.cthickening M.D (existsAnnularSpokes_ray c N R M.D j) := by
    intro j
    show (T.spoke j).carrier ⊆ _
    rw [hT]
    exact (hα j).2.2.2.2.2
  -- localization
  have hloc : ∀ j : Fin (4 * N), (G.spokes.piece j).carrier ⊆
      Metric.cthickening (20 * M.D) (idealTrapezoid c N R M.D (j : ℕ)) := by
    intro j x hx
    obtain ⟨hx1, hx2⟩ := quantitativeAnnularGrouping_step2_band G j hx
    by_cases ht : x ∈ Metric.cthickening (5 * M.D) (existsAnnularSpokes_ray c N R M.D j) ∨
        x ∈ Metric.cthickening (5 * M.D) (existsAnnularSpokes_ray c N R M.D ((j : ℕ) + 1))
    · exact Metric.cthickening_mono (by linarith) _
        (quantitativeAnnularGrouping_step4_tubes c hD hN hR j hx1 hx2 ht)
    · exact Metric.self_subset_cthickening _
        (quantitativeAnnularGrouping_step3_wedges c hN hR G hspk j hx (not_or.1 ht).1
          (not_or.1 ht).2)
  -- diameter
  have hdiam : ∀ j : Fin (4 * N), Metric.diam (G.spokes.piece j).carrier ≤ 7 * R := by
    intro j
    obtain ⟨hbd, hd⟩ := quantitativeAnnularGrouping_step8_diam c hD hN hR j
    exact (Metric.diam_mono (hloc j) hbd).trans hd
  refine ⟨G, hloc, ?_, hdiam, ?_⟩
  · -- private outer edges
    intro j
    obtain ⟨f, hf, a, hcovJ⟩ := quantitativeAnnularGrouping_step5_privateHit c hN hR G hloc j
    obtain ⟨hfin, hdi⟩ := quantitativeAnnularGrouping_step6_privateFinite G j
    have hcount := quantitativeAnnularGrouping_step7_count hD hfin hdi hf hcovJ
    have hfl : (⌊R / (2 * M.D)⌋₊ : ℝ) ≤ R / (2 * M.D) :=
      Nat.floor_le (div_nonneg hR0.le (by linarith))
    have heq : R / 2 / M.D = R / (2 * M.D) := by rw [div_div]
    linarith
  · -- side bound
    intro j
    have h1 := quantitativeAnnularGrouping_step10_sides M (G.spokes.piece j)
    have h2 := quantitativeAnnularGrouping_step9_faces M (G.spokes.piece j) (hdiam j)
    have h3 : 4 * (7 * R) ^ 2 / M.a = 4 * 7 ^ 2 * R ^ 2 / M.a := by ring
    rw [h3] at h2
    exact h1.trans (Nat.mul_le_mul_left _ h2)

/-! ## The fingerprint criterion (`lem:fingerprint`) -/

/-- Kinds of types in a macrotemplate. -/
inductive TypeKind where
  | original
  | small
  | central
  deriving DecidableEq

/-- Abstract fingerprint data of a finite family of templates: type tags, the
template of each tag, its kind, the multiset `ordinary t` of neighbouring
type tags across its ordinary inner sides (for a small type: its ordinary
marked inner sides), and the full inner-side adjacency of the template dual
graphs. -/
structure FingerprintData where
  Tag : Type
  [decEq : DecidableEq Tag]
  Tmpl : Type
  template : Tag → Tmpl
  kind : Tag → TypeKind
  ordinary : Tag → Multiset Tag
  adj : Tag → Tag → Prop

attribute [instance] FingerprintData.decEq

namespace FingerprintData

variable (F : FingerprintData)

/-- The multiset of type components of the ordinary identity pairs of `t`:
each ordinary side towards `v` contributes the two components `t` and `v`. -/
def baseFingerprint (t : F.Tag) : Multiset F.Tag :=
  F.ordinary t + Multiset.replicate (Multiset.card (F.ordinary t)) t

/-- Possible fingerprints: an original type has exactly its base fingerprint;
a small type may add at most two further components from its special side. -/
def possibleFingerprints (t : F.Tag) : Set (Multiset F.Tag) :=
  match F.kind t with
  | .original => {F.baseFingerprint t}
  | .small => {f | ∃ X : Multiset F.Tag, Multiset.card X ≤ 2 ∧ f = F.baseFingerprint t + X}
  | .central => ∅

/-- (G6): possible fingerprints of distinct noncentral types are disjoint. -/
def Separates : Prop :=
  ∀ t u, F.kind t ≠ .central → F.kind u ≠ .central → t ≠ u →
    Disjoint (F.possibleFingerprints t) (F.possibleFingerprints u)

end FingerprintData

/-- Step 1 of the blueprint proof of `fingerprintSeparation`: An original and a small type
cannot have equal fingerprints. -/
private lemma fingerprintSeparation_step1_size (F : FingerprintData) (K0 : ℕ)
    (h_orig_le : ∀ u, F.kind u = .original → Multiset.card (F.ordinary u) ≤ K0)
    (h_small_ge : ∀ t, F.kind t = .small → K0 + 2 ≤ Multiset.card (F.ordinary t)) :
    ∀ t u, F.kind t = .original → F.kind u = .small →
    Disjoint (F.possibleFingerprints t) (F.possibleFingerprints u) := by
  intro t u ht hu
  rw [Set.disjoint_left]
  intro f hf1 hf2
  unfold FingerprintData.possibleFingerprints at hf1 hf2
  rw [ht] at hf1
  rw [hu] at hf2
  simp only [Set.mem_singleton_iff] at hf1
  simp only [Set.mem_setOf_eq] at hf2
  rcases hf2 with ⟨X, hX, hf2⟩
  have C1 : Multiset.card f ≤ 2 * K0 := by
    rw [hf1]
    unfold FingerprintData.baseFingerprint
    simp
    linarith [h_orig_le t ht]
  have C2 : 2 * K0 + 4 ≤ Multiset.card f := by
    rw [hf2]
    unfold FingerprintData.baseFingerprint
    simp
    linarith [h_small_ge u hu]
  omega

/-- Step 1 of the blueprint proof of `fingerprintSeparation_step2_templates`: A possible
fingerprint of `t` (noncentral) is its base fingerprint plus some elements, bounded
differently if original or small. -/
private lemma fingerprintSeparation_step2_templates_step1_X (F : FingerprintData) :
    ∀ t f, F.kind t ≠ .central → f ∈ F.possibleFingerprints t →
    ∃ X : Multiset F.Tag, (F.kind t = .small → Multiset.card X ≤ 2) ∧ (F.kind t = .original → X = 0) ∧ f = F.baseFingerprint t + X := by
  intro t f ht_not_central hf
  unfold FingerprintData.possibleFingerprints at hf
  rcases hk : F.kind t with _ | _ | _
  · -- original
    rw [hk] at hf
    simp only [Set.mem_singleton_iff] at hf
    use 0
    refine ⟨?_, ?_, ?_⟩
    · intro h
      contradiction
    · intro _
      rfl
    · rw [hf, add_zero]
  · -- small
    rw [hk] at hf
    simp only [Set.mem_setOf_eq] at hf
    rcases hf with ⟨X, hX_card, hX_eq⟩
    use X
    refine ⟨?_, ?_, ?_⟩
    · intro _
      exact hX_card
    · intro h
      contradiction
    · exact hX_eq
  · -- central
    exact False.elim (ht_not_central hk)

/-- Step 2 of the blueprint proof of `fingerprintSeparation_step2_templates`: The base
fingerprint of `u` contains no elements from the template of `t` if they have different
templates. -/
private lemma fingerprintSeparation_step2_templates_step2_count (F : FingerprintData)
    [DecidableEq F.Tmpl]
    (h_tmpl : ∀ t, ∀ v ∈ F.ordinary t, F.template v = F.template t) :
    ∀ t u, F.template t ≠ F.template u → Multiset.countP (fun v => F.template v = F.template t) (F.baseFingerprint u) = 0 := by
  intro t u htu
  unfold FingerprintData.baseFingerprint
  rw [Multiset.countP_add]
  have h1 : Multiset.countP (fun v => F.template v = F.template t) (F.ordinary u) = 0 := by
    rw [Multiset.countP_eq_zero]
    intro v hv
    have h_v_tmpl := h_tmpl u v hv
    intro h_eq
    apply htu
    rw [← h_eq, h_v_tmpl]
  have h2 : Multiset.countP (fun v => F.template v = F.template t)
      (Multiset.replicate (Multiset.card (F.ordinary u)) u) = 0 := by
    rw [Multiset.countP_eq_zero]
    intro v hv
    have h_eq_u := Multiset.eq_of_mem_replicate hv
    intro h_eq
    apply htu
    rw [← h_eq, h_eq_u]
  rw [h1, h2, add_zero]

/-- Step 3 of the blueprint proof of `fingerprintSeparation_step2_templates`: The base
fingerprint of `t` contains 2 * card (F.ordinary t) elements from its own template. -/
private lemma fingerprintSeparation_step2_templates_step3_count_self (F : FingerprintData)
    [DecidableEq F.Tmpl]
    (h_tmpl : ∀ t, ∀ v ∈ F.ordinary t, F.template v = F.template t) :
    ∀ t, Multiset.countP (fun v => F.template v = F.template t) (F.baseFingerprint t) =
      2 * Multiset.card (F.ordinary t) := by
  intro t
  unfold FingerprintData.baseFingerprint
  rw [Multiset.countP_add]
  have h_ordinary :
      Multiset.countP (fun v => F.template v = F.template t) (F.ordinary t) =
        Multiset.card (F.ordinary t) := by
    apply Multiset.countP_eq_card.mpr
    intro v hv
    exact h_tmpl t v hv
  have h_replicate :
      Multiset.countP (fun v => F.template v = F.template t)
          (Multiset.replicate (Multiset.card (F.ordinary t)) t) =
        Multiset.card (Multiset.replicate (Multiset.card (F.ordinary t)) t) := by
    apply Multiset.countP_eq_card.mpr
    intro v hv
    rw [Multiset.eq_of_mem_replicate hv]
  rw [h_ordinary, h_replicate, Multiset.card_replicate]
  omega

/-- Step 2 of the blueprint proof of `fingerprintSeparation`: Types in different
templates have disjoint possible fingerprints. -/
private lemma fingerprintSeparation_step2_templates (F : FingerprintData)
    (h_tmpl : ∀ t, ∀ v ∈ F.ordinary t, F.template v = F.template t)
    (h_orig_ne : ∀ u, F.kind u = .original → F.ordinary u ≠ 0)
    (h_small_ge : ∀ t, F.kind t = .small → 2 ≤ Multiset.card (F.ordinary t)) :
    ∀ t u, F.kind t ≠ .central → F.kind u ≠ .central → F.template t ≠ F.template u →
    Disjoint (F.possibleFingerprints t) (F.possibleFingerprints u) := by
  intro t u ht hu htu
  rw [Set.disjoint_iff]
  rintro f ⟨hft, hfu⟩
  have hf_t := fingerprintSeparation_step2_templates_step1_X F t f ht hft
  have hf_u := fingerprintSeparation_step2_templates_step1_X F u f hu hfu
  rcases hf_t with ⟨X, hX_cond, hX_zero, hf_t_eq⟩
  rcases hf_u with ⟨Y, hY_cond, hY_zero, hf_u_eq⟩
  
  letI : DecidableEq F.Tmpl := Classical.decEq F.Tmpl

  have hf_count_t : Multiset.countP (fun v => F.template v = F.template t) f =
      2 * Multiset.card (F.ordinary t) +
        Multiset.countP (fun v => F.template v = F.template t) X := by
    rw [hf_t_eq, Multiset.countP_add]
    have h1 := fingerprintSeparation_step2_templates_step3_count_self F h_tmpl t
    rw [h1]

  have hf_count_u : Multiset.countP (fun v => F.template v = F.template t) f = Multiset.countP (fun v => F.template v = F.template t) Y := by
    rw [hf_u_eq, Multiset.countP_add]
    have h1 := fingerprintSeparation_step2_templates_step2_count F h_tmpl t u htu
    rw [h1, zero_add]

  have h_eq : 2 * Multiset.card (F.ordinary t) +
        Multiset.countP (fun v => F.template v = F.template t) X =
      Multiset.countP (fun v => F.template v = F.template t) Y := by
    rw [← hf_count_t, hf_count_u]

  have h_Y_le : Multiset.countP (fun v => F.template v = F.template t) Y ≤ 2 := by
    have h1 : Multiset.countP (fun v => F.template v = F.template t) Y ≤ Multiset.card Y := Multiset.countP_le_card _ _
    rcases hku : F.kind u with _ | _ | _
    · have hY_eq_0 := hY_zero hku
      rw [hY_eq_0, Multiset.countP_zero]
      exact Nat.zero_le 2
    · have hY_le_2 := hY_cond hku
      linarith
    · contradiction

  rcases hkt : F.kind t with _ | _ | _
  · have h_ne : F.ordinary t ≠ 0 := h_orig_ne t hkt
    have h_pos : 1 ≤ Multiset.card (F.ordinary t) := Multiset.card_pos.mpr h_ne
    
    have hf_count_u_u : Multiset.countP (fun v => F.template v = F.template u) f = Multiset.countP (fun v => F.template v = F.template u) X := by
      rw [hf_t_eq, Multiset.countP_add]
      have h1 : Multiset.countP (fun v => F.template v = F.template u) (F.baseFingerprint t) = 0 := by
        apply fingerprintSeparation_step2_templates_step2_count F h_tmpl u t htu.symm
      rw [h1, zero_add]
      
    have hf_count_u_u2 : Multiset.countP (fun v => F.template v = F.template u) f =
        2 * Multiset.card (F.ordinary u) +
          Multiset.countP (fun v => F.template v = F.template u) Y := by
      rw [hf_u_eq, Multiset.countP_add]
      have h1 := fingerprintSeparation_step2_templates_step3_count_self F h_tmpl u
      rw [h1]

    have h_eq2 : Multiset.countP (fun v => F.template v = F.template u) X =
        2 * Multiset.card (F.ordinary u) +
          Multiset.countP (fun v => F.template v = F.template u) Y := by
      rw [← hf_count_u_u, hf_count_u_u2]

    have hX_eq_0 := hX_zero hkt
    rw [hX_eq_0, Multiset.countP_zero] at h_eq2
    
    rcases hku : F.kind u with _ | _ | _
    · have h_ne_u : F.ordinary u ≠ 0 := h_orig_ne u hku
      have h_pos_u : 1 ≤ Multiset.card (F.ordinary u) := Multiset.card_pos.mpr h_ne_u
      have h_non_neg_Y : 0 ≤ Multiset.countP (fun v => F.template v = F.template u) Y := Nat.zero_le _
      linarith
    · have h_ge2_u : 2 ≤ Multiset.card (F.ordinary u) := h_small_ge u hku
      have h_non_neg_Y : 0 ≤ Multiset.countP (fun v => F.template v = F.template u) Y := Nat.zero_le _
      linarith
    · contradiction
    
  · have h_ge2 : 2 ≤ Multiset.card (F.ordinary t) := h_small_ge t hkt
    have h_non_neg : 0 ≤ Multiset.countP (fun v => F.template v = F.template t) X := Nat.zero_le _
    linarith
  · contradiction

/-- Step 3 of the blueprint proof of `fingerprintSeparation`: Two original types
in the same template cannot have equal fingerprints. -/
private lemma fingerprintSeparation_step3_orig (F : FingerprintData)
    (h_symm : ∀ u v, F.kind u = .original → F.kind v = .original →
      (F.ordinary u).count v = (F.ordinary v).count u)
    (h_adj_symm : ∀ u v, F.adj u v → F.adj v u)
    (h_adj_orig : ∀ u w, F.kind u = .original → (F.adj u w ↔ w ∈ F.ordinary u))
    (h_conn : ∀ t w, F.template t = F.template w → Relation.ReflTransGen F.adj t w)
    (h_three : ∀ t, ∃ a b, a ≠ t ∧ b ≠ t ∧ a ≠ b ∧
      F.template a = F.template t ∧ F.template b = F.template t) :
    ∀ u v, F.kind u = .original → F.kind v = .original → u ≠ v → F.template u = F.template v →
    Disjoint (F.possibleFingerprints u) (F.possibleFingerprints v) := sorry

/-- Step 4 of the blueprint proof of `fingerprintSeparation`: Two small types
in the same template cannot have equal fingerprints. -/
private lemma fingerprintSeparation_step4_small (F : FingerprintData)
    (h_private : ∀ t u, F.kind t = .small → F.kind u = .small → t ≠ u →
      F.template t = F.template u →
      3 ≤ Multiset.card ((F.ordinary t).filter
        (fun v => F.kind v = .original ∧ v ∉ F.ordinary u))) :
    ∀ t u, F.kind t = .small → F.kind u = .small → t ≠ u → F.template t = F.template u →
    Disjoint (F.possibleFingerprints t) (F.possibleFingerprints u) := by
  intro t u hkt hku htu htmpl
  rw [Set.disjoint_iff_forall_ne]
  intro f hf g hg heq
  subst heq
  simp only [FingerprintData.possibleFingerprints, hkt, hku, Set.mem_setOf_eq] at hf hg
  rcases hf with ⟨X, hX, rfl⟩
  rcases hg with ⟨Y, hY, heq⟩
  let P := fun v => F.kind v = TypeKind.original ∧ v ∉ F.ordinary u
  have h_P_f : Multiset.card (Multiset.filter P (F.baseFingerprint t + X)) =
               Multiset.card (Multiset.filter P (F.baseFingerprint u + Y)) := by
    rw [heq]
  simp only [Multiset.filter_add, Multiset.card_add] at h_P_f
  have h_P_t : Multiset.filter P (F.baseFingerprint t) = Multiset.filter P (F.ordinary t) := by
    rw [FingerprintData.baseFingerprint, Multiset.filter_add]
    have : Multiset.filter P (Multiset.replicate (Multiset.card (F.ordinary t)) t) = 0 := by
      apply Multiset.filter_eq_nil.mpr
      intro x hx
      simp only [Multiset.mem_replicate] at hx
      rcases hx with ⟨_, rfl⟩
      intro h
      have := h.1
      rw [hkt] at this
      contradiction
    rw [this, add_zero]
  have h_P_u : Multiset.filter P (F.baseFingerprint u) = 0 := by
    rw [FingerprintData.baseFingerprint, Multiset.filter_add]
    have h1 : Multiset.filter P (F.ordinary u) = 0 := by
      apply Multiset.filter_eq_nil.mpr
      intro x hx h
      have := h.2
      contradiction
    have h2 : Multiset.filter P (Multiset.replicate (Multiset.card (F.ordinary u)) u) = 0 := by
      apply Multiset.filter_eq_nil.mpr
      intro x hx
      simp only [Multiset.mem_replicate] at hx
      rcases hx with ⟨_, rfl⟩
      intro h
      have := h.1
      rw [hku] at this
      contradiction
    rw [h1, h2, add_zero]
  rw [h_P_t, h_P_u] at h_P_f
  simp only [Multiset.card_zero, zero_add] at h_P_f
  have h_le_Y : Multiset.card (Multiset.filter P Y) ≤ 2 := by
    have : Multiset.card (Multiset.filter P Y) ≤ Multiset.card Y := Multiset.card_le_card (Multiset.filter_le P Y)
    omega
  have h_ge_X : 3 ≤ Multiset.card (Multiset.filter P (F.ordinary t)) := by
    have := h_private t u hkt hku htu htmpl
    omega
  omega

/-- `lem:fingerprint`: under (G1) (neighbours in the same template, symmetric
original adjacency counts, connected template dual graphs with at least three
children), with original types having nonempty fingerprints of at most `K0`
sides, small types having at least `K0 + 2` ordinary marked sides, and every
small type having at least three ordinary occurrences of original neighbours
which are not ordinary neighbours of any other small type of its template,
the fingerprints separate types (G6). -/
theorem fingerprintSeparation (F : FingerprintData) (K0 : ℕ)
    (h_tmpl : ∀ t, ∀ v ∈ F.ordinary t, F.template v = F.template t)
    (h_symm : ∀ u v, F.kind u = .original → F.kind v = .original →
      (F.ordinary u).count v = (F.ordinary v).count u)
    (h_adj_symm : ∀ u v, F.adj u v → F.adj v u)
    (h_adj_orig : ∀ u w, F.kind u = .original → (F.adj u w ↔ w ∈ F.ordinary u))
    (h_conn : ∀ t w, F.template t = F.template w → Relation.ReflTransGen F.adj t w)
    (h_three : ∀ t, ∃ a b, a ≠ t ∧ b ≠ t ∧ a ≠ b ∧
      F.template a = F.template t ∧ F.template b = F.template t)
    (h_orig_ne : ∀ u, F.kind u = .original → F.ordinary u ≠ 0)
    (h_orig_le : ∀ u, F.kind u = .original → Multiset.card (F.ordinary u) ≤ K0)
    (h_small_ge : ∀ t, F.kind t = .small → K0 + 2 ≤ Multiset.card (F.ordinary t))
    (h_private : ∀ t u, F.kind t = .small → F.kind u = .small → t ≠ u →
      F.template t = F.template u →
      3 ≤ Multiset.card ((F.ordinary t).filter
        (fun v => F.kind v = .original ∧ v ∉ F.ordinary u))) :
    F.Separates := by
  intro t u ht hu htu
  by_cases h_tmpl_eq : F.template t = F.template u
  · rcases hkt : F.kind t with _ | _ | _
    · rcases hku : F.kind u with _ | _ | _
      · exact fingerprintSeparation_step3_orig F h_symm h_adj_symm h_adj_orig h_conn
          h_three t u hkt hku htu h_tmpl_eq
      · exact fingerprintSeparation_step1_size F K0 h_orig_le h_small_ge t u hkt hku
      · contradiction
    · rcases hku : F.kind u with _ | _ | _
      · exact (fingerprintSeparation_step1_size F K0 h_orig_le h_small_ge u t hku hkt).symm
      · exact fingerprintSeparation_step4_small F h_private t u hkt hku htu h_tmpl_eq
      · contradiction
    · contradiction
  · apply fingerprintSeparation_step2_templates F h_tmpl h_orig_ne
    · intro x hx
      exact le_trans (by omega) (h_small_ge x hx)
    · exact ht
    · exact hu
    · exact h_tmpl_eq

/-! ## Grouped families and grouped substitutions -/

/-- A finite grouped family over `P`: grouped forms `P'`, each with a
scattering patch `dissect α` (the map `Δ` of the blueprint) of original tiles
whose support is the grouped carrier.  Each group is STS, has a connected
face-dual graph, has as listed sides complete original sides, and retains
every original vertex on its boundary. -/
structure GroupedFamily (P : Protoset) where
  P' : Protoset
  dissect : P'.Form → Patch P
  support_eq : ∀ α, support (dissect α).tiles = (P'.disk α).carrier
  sts : ∀ α, SideToSideSet (dissect α).tiles
  dualConnected : ∀ α, DualConnected (dissect α).tiles
  side_whole : ∀ α (i : Fin (P'.disk α).n), ∃ A ∈ (dissect α).tiles, HasEdge A ((P'.disk α).side i)
  vertex_retained : ∀ α v, Substitution.IsVertexOf (dissect α).tiles v →
    v ∈ frontier (P'.disk α).carrier → v ∈ (P'.disk α).vertexSet

namespace GroupedFamily

variable (G : GroupedFamily P)

/-- Scattering of a placed grouped tile into its original constituents. -/
def scatterTile (A : PlacedTile G.P') : Set (PlacedTile P) :=
  translateSet A.anchor (G.dissect A.form).tiles

/-- Scattering of a set of placed grouped tiles. -/
def scatter (S : Set (PlacedTile G.P')) : Set (PlacedTile P) := ⋃ A ∈ S, G.scatterTile A

/-- Mixed protoset: grouped forms together with original forms (used for
templates in which only some groups are retained and the others are
scattered). -/
abbrev mixed : Protoset where
  Form := G.P'.Form ⊕ P.Form
  fintype := inferInstance
  decEq := inferInstance
  disk := Sum.elim G.P'.disk P.disk

/-- Scattering of a placed mixed tile. -/
def mixedScatterTile (A : PlacedTile G.mixed) : Set (PlacedTile P) :=
  Sum.elim (fun α => translateSet A.anchor (G.dissect α).tiles)
    (fun p => ({⟨p, A.anchor⟩} : Set (PlacedTile P))) A.form

/-- Scattering of a set of placed mixed tiles. -/
def mixedScatter (S : Set (PlacedTile G.mixed)) : Set (PlacedTile P) :=
  ⋃ A ∈ S, G.mixedScatterTile A

end GroupedFamily

/-- A grouped substitution for `τ^k`: a grouped family with a substitution
`σ` on grouped forms, of expansion `θ^k`, with `Δ σ α = τ^k Δ α`. -/
structure GroupedSubstitution (τ : Substitution P) where
  G : GroupedFamily P
  k : ℕ
  k_pos : 0 < k
  σ : Substitution G.P'
  θ_eq : σ.θ = τ.θ ^ k
  compat : ∀ α, G.scatter (σ.rule α).tiles = τ.decomposeIter k (G.dissect α).tiles

/-! ## Templates and routing data (`lem:routing`) -/

/-- A finite side-to-side template: a patch of children covering a region. -/
structure Template (Q : Protoset) where
  children : Patch Q
  region : Set Pt
  support_eq : support children.tiles = region
  sts : SideToSideSet children.tiles

namespace Template

variable {Q : Protoset} (T : Template Q)

/-- Inner side: a complete side of two distinct children. -/
def IsInner (e : Set Pt) : Prop :=
  ∃ A ∈ T.children.tiles, ∃ B ∈ T.children.tiles, A ≠ B ∧ HasEdge A e ∧ HasEdge B e

/-- Outer side: a side of a child contained in the boundary of the region. -/
def IsOuter (e : Set Pt) : Prop :=
  e ∈ edges T.children.tiles ∧ e ⊆ frontier T.region

end Template

/-- `f` preserves cyclic order on `s` up to a rotation of the target and up
to a global reversal of orientation (polygonal disks carry no orientation in
`Basic.lean`). -/
def CyclicOrderPreservingOn {n m : ℕ} (s : Finset (Fin n)) (f : Fin n → Fin m) : Prop :=
  ∃ r : ℕ, StrictMonoOn (fun a : Fin n => ((f a : ℕ) + r) % m) (s : Set (Fin n)) ∨
    StrictAntiOn (fun a : Fin n => ((f a : ℕ) + r) % m) (s : Set (Fin n))

/-- Routing data (G4) for one template `T` of a parent disk `par` scaled by
`s`, with central child `central` and marked parent sides `marked`.  For a
marked side `a` the paths `i = 0,…,3` run from port `i` to the print
`central.side (printIdx a)`.  Paths are lists of sides; `pathTiles` lists the
crossed children (`k`-th tile contains sides `k` and `k+1`). -/
structure RoutingData {Q : Protoset} (T : Template Q) (par : PolygonalDisk) (s : ℝ)
    (central : PlacedTile Q) (marked : Finset (Fin par.n)) where
  marking : Set (Set Pt)
  port : Fin par.n → Fin 5 → Set Pt
  printIdx : Fin par.n → Fin (Q.disk central.form).n
  pathSides : Fin par.n → Fin 4 → List (Set Pt)
  pathTiles : Fin par.n → Fin 4 → List (PlacedTile Q)
  central_mem : central ∈ T.children.tiles
  port_outer : ∀ a r, T.IsOuter (port a r) ∧ port a r ⊆ s • par.side a
  port_injective : ∀ a, Function.Injective (port a)
  print_inner : ∀ a ∈ marked, T.IsInner (central.side (printIdx a))
  print_injOn : Set.InjOn printIdx (marked : Set (Fin par.n))
  print_cyclic : CyclicOrderPreservingOn marked printIdx
  path_head : ∀ a ∈ marked, ∀ i : Fin 4, (pathSides a i).head? = some (port a i.castSucc)
  path_last : ∀ a ∈ marked, ∀ i : Fin 4,
    (pathSides a i).getLast? = some (central.side (printIdx a))
  path_length : ∀ a ∈ marked, ∀ i : Fin 4, (pathTiles a i).length + 1 = (pathSides a i).length
  path_step : ∀ a ∈ marked, ∀ i : Fin 4, ∀ (k : ℕ) (X : PlacedTile Q) (e e' : Set Pt),
    (pathTiles a i)[k]? = some X → (pathSides a i)[k]? = some e →
    (pathSides a i)[k + 1]? = some e' →
    X ∈ T.children.tiles ∧ HasEdge X e ∧ HasEdge X e'
  path_cross : ∀ a ∈ marked, ∀ i : Fin 4, ∀ (k : ℕ) (X Y : PlacedTile Q),
    (pathTiles a i)[k]? = some X → (pathTiles a i)[k + 1]? = some Y → X ≠ Y
  /-- the side preceding the print is a side of the small child sharing it -/
  path_last_tile : ∀ a ∈ marked, ∀ i : Fin 4, ∀ X, (pathTiles a i).getLast? = some X →
    X ≠ central
  /-- every side of a genuine path other than its initial port is inner -/
  path_inner : ∀ a ∈ marked, ∀ i : Fin 4, ∀ e ∈ (pathSides a i).tail, T.IsInner e
  path_marked : ∀ a ∈ marked, ∀ i : Fin 4, ∀ e ∈ pathSides a i, e ∈ marking
  /-- the only central side on a genuine path is its final print -/
  path_central : ∀ a ∈ marked, ∀ i : Fin 4, ∀ e ∈ (pathSides a i).dropLast, ¬ HasEdge central e
  /-- every nonterminal side occurrence is used at most once -/
  path_nodup : ∀ a ∈ marked, ∀ i : Fin 4, ((pathSides a i).dropLast).Nodup
  path_disjoint : ∀ a ∈ marked, ∀ b ∈ marked, ∀ i j : Fin 4, (a, i) ≠ (b, j) →
    List.Disjoint (pathSides a i).dropLast (pathSides b j).dropLast
  /-- the fifth port and all ports of unmarked sides are singleton paths,
  disjoint from the genuine paths -/
  singleton_disjoint : ∀ (a : Fin par.n) (r : Fin 5), (a ∉ marked ∨ r = 4) →
    ∀ b ∈ marked, ∀ i : Fin 4, port a r ∉ pathSides b i

/-- Input of the wide-routing lemma: a grouped substitution, the central-form
map `c`, the marked sides of each grouped form, and for each power `l` the
retained `σ^l`-templates (central child and its annular small neighbours
retained, all other groups scattered), together with the properties the
grouping construction guarantees: uniform normalized clearance of the central
child, at least four private outer edges of every small neighbour, and an
injective cyclically ordered choice of print slots on distinct small
neighbours. -/
structure RoutingSetup (τ : Substitution P) (M : MeshConstants P) where
  GS : GroupedSubstitution τ
  c : GS.G.P'.Form → GS.G.P'.Form
  markedSides : ∀ α : GS.G.P'.Form, Finset (Fin (GS.G.P'.disk α).n)
  retained : ℕ → GS.G.P'.Form → Template GS.G.mixed
  central : ℕ → GS.G.P'.Form → PlacedTile GS.G.mixed
  region_eq : ∀ l α, (retained l α).region = (τ.θ ^ (GS.k * l)) • (GS.G.P'.disk α).carrier
  scatter_eq : ∀ l α, GS.G.mixedScatter (retained l α).children.tiles =
    τ.decomposeIter (GS.k * l) (GS.G.dissect α).tiles
  central_mem : ∀ l α, central l α ∈ (retained l α).children.tiles
  central_form : ∀ l α, (central l α).form = Sum.inl (c^[l] α)
  others : ∀ l α, ∀ X ∈ (retained l α).children.tiles, X ≠ central l α →
    (∃ p, X.form = Sum.inr p) ∨ SharesSide X (central l α)
  /-- all quantitative clauses concern genuine powers `l ≥ 1` (at `l = 0` the retained
  template is the form itself) -/
  clearance : ∃ ρ : ℝ, 0 < ρ ∧ ∀ l α, 0 < l → ∀ x ∈ (central l α).carrier,
    ρ * τ.θ ^ (GS.k * l) ≤ Metric.infDist x (frontier (retained l α).region)
  /-- The annular grouping of each retained template (`lem:quantitative-sector`,
  review addition of 13 October 2026): the central child scatters to the
  inside-anchored group `L`, the small neighbours scatter to the `4N` annular
  groups (pieces) between `L` and the outside-anchored group `H`, whose
  boundary edges adjoin faces reaching the exterior of `K₁ = Q₁ + B∞(3D)`.
  Without this structure the private faces of a small neighbour could sit in
  cavities closed off by fewer than four sides, and four disjoint paths cannot
  exist (Aristotle, project ccb3975c). -/
  N : GS.G.P'.Form → ℕ
  R : GS.G.P'.Form → ℝ
  centre : ℕ → GS.G.P'.Form → Pt
  N_two : ∀ α, 2 ≤ N α
  /-- `R ≥ 10000 (K₀ + 3) D`: the collars and radial rays of distinct private
  edges are separated by more than `10 D` outside `K₁` (`lem:routing`). -/
  R_large : ∀ α, 10000 * ((M.K0 : ℝ) + 3) * M.D ≤ R α
  annulus : ∀ l α, 0 < l →
    AnnularGrouping M (GS.G.mixedScatter (retained l α).children.tiles) (centre l α) (N α) (R α)
  annulus_inside : ∀ l α (_hl : 0 < l),
    square (centre l α) ((N α : ℝ) * R α / 2 + R α) + Binf (10 * M.D) ⊆
      interior (retained l α).region
  central_scatter : ∀ l α (hl : 0 < l),
    GS.G.mixedScatterTile (central l α) = (annulus l α hl).L.faces
  small_scatter : ∀ l α (hl : 0 < l), ∀ X ∈ (retained l α).children.tiles, X ≠ central l α →
    (∃ β, X.form = Sum.inl β) →
      ∃ j, GS.G.mixedScatterTile X = ((annulus l α hl).spokes.piece j).faces
  piece_child : ∀ l α (hl : 0 < l) (j : Fin (4 * N α)),
    ∃ X ∈ (retained l α).children.tiles, X ≠ central l α ∧
      GS.G.mixedScatterTile X = ((annulus l α hl).spokes.piece j).faces
  /-- Four private outer edges of every annular group in separated windows
  (`lem:routing`: windows at relative parameters `0.30, 0.43, 0.57, 0.70` of
  the outer boundary), pairwise at distance at least `R / 10`. -/
  windows : ∀ l α (hl : 0 < l) (j : Fin (4 * N α)), ∃ e : Fin 4 → Set Pt,
    (∀ i, e i ∈ privateOuterEdges (annulus l α hl) j) ∧
      ∀ i i', i ≠ i' → ∀ x ∈ e i, ∀ y ∈ e i', R α / 10 ≤ dist x y
  print_slots : ∀ l α, 0 < l → ∃ (f : Fin (GS.G.P'.disk α).n → Fin (GS.G.mixed.disk (central l α).form).n)
    (g : Fin (GS.G.P'.disk α).n → PlacedTile GS.G.mixed),
    Set.InjOn f (markedSides α : Set _) ∧ Set.InjOn g (markedSides α : Set _) ∧
    CyclicOrderPreservingOn (markedSides α) f ∧
    ∀ a ∈ markedSides α, g a ∈ (retained l α).children.tiles ∧ g a ≠ central l α ∧
      HasEdge (g a) ((central l α).side (f a))

/-- `lem:routing`: there are arbitrarily large powers `l` with `c^[2l] = c^[l]`
for which every retained `σ^l`-template carries routing data (G4), including
the inner-side clause. -/
theorem existsRoutingAfterPower (τ : Substitution P) (hτ : τ.STS) (M : MeshConstants P)
    (Rs : RoutingSetup τ M) :
    ∀ n₀ : ℕ, ∃ l ≥ n₀, 0 < l ∧ Rs.c^[2 * l] = Rs.c^[l] ∧
      ∀ α, Nonempty (RoutingData (Rs.retained l α) (Rs.GS.G.P'.disk α)
        (τ.θ ^ (Rs.GS.k * l)) (Rs.central l α) (Rs.markedSides α)) := by
  sorry

/-! ## Existence of the macrocertificate (`lem:certificate-exists`) -/

/-- A macrocertificate *represents* the substitution `τ` at the power `m`
(the content of `lem:certificate-exists` beyond (G1)–(G7)): its scattering
`Δ` makes the grouped forms `C.Q` a grouped family of `τ` in which every
original form is available as a singleton group, the grouped substitution
`σ' = C.σ` has expansion `θ^m` and satisfies `Δ σ' α = τ^m Δ α`, and
hereditary listed sides of `τ` make the macrotemplate system hereditary.
Without these clauses the empty certificate satisfies (G1)–(G7) vacuously
(Aristotle, project 1691ce37, 12 October 2026). -/
structure MacroCertificate.Represents (C : MacroCertificate P) (τ : Substitution P) (m : ℕ) :
    Prop where
  m_pos : 0 < m
  θ_eq : C.σ.θ = τ.θ ^ m
  compat : ∀ α, (⋃ A ∈ (C.σ.rule α).tiles, translateSet A.anchor (C.Δ A.form).tiles) =
    τ.decomposeIter m (C.Δ α).tiles
  sts : ∀ α, SideToSideSet (C.Δ α).tiles
  dualConnected : ∀ α, DualConnected (C.Δ α).tiles
  side_whole : ∀ α (i : Fin (C.Q.disk α).n), ∃ A ∈ (C.Δ α).tiles, HasEdge A ((C.Q.disk α).side i)
  vertex_retained : ∀ α v, Substitution.IsVertexOf (C.Δ α).tiles v →
    v ∈ frontier (C.Q.disk α).carrier → v ∈ (C.Q.disk α).vertexSet
  singleton : ∀ p : P.Form, ∃ α, (C.Δ α).tiles = {⟨p, 0⟩}
  /-- Every grouped form is a group of tiles of a supertile (the groups are formed inside the
  STS cellulations `τ^k α`). -/
  inside_supertile : ∀ α, ∃ (n : ℕ) (p : P.Form) (v : Pt),
    translateSet v (C.Δ α).tiles ⊆ τ.supertile n p
  hereditary : τ.HereditarySides → C.Hereditary

/-- The grouped family underlying a representing certificate. -/
def MacroCertificate.Represents.groupedFamily {C : MacroCertificate P} {τ : Substitution P}
    {m : ℕ} (h : C.Represents τ m) : GroupedFamily P where
  P' := C.Q
  dissect := C.Δ
  support_eq := C.scatter_support
  sts := h.sts
  dualConnected := h.dualConnected
  side_whole := h.side_whole
  vertex_retained := h.vertex_retained

/-- The grouped substitution for `τ^m` underlying a representing certificate
(the input of `lem:grouping-lift`). -/
def MacroCertificate.Represents.groupedSubstitution {C : MacroCertificate P} {τ : Substitution P}
    {m : ℕ} (h : C.Represents τ m) : GroupedSubstitution τ where
  G := h.groupedFamily
  k := m
  k_pos := h.m_pos
  σ := C.σ
  θ_eq := h.θ_eq
  compat := h.compat

/-- `lem:certificate-exists`: for every STS polygonal substitution `τ` there
are a macrocertificate `C` with the properties (G1)–(G7) and a power `m > 0`
such that `C` represents `τ` at the power `m`: a finite grouped family
`P'` (the forms `C.Q`) containing every original form as a singleton group,
a scattering map `Δ = C.Δ`, and a grouped substitution `σ' = C.σ` of
expansion `θ^m` with `Δ σ' α = τ^m Δ α` for all `α`. -/
theorem existsMacroCertificate (τ : Substitution P) (h : τ.STS) :
    ∃ (C : MacroCertificate P) (m : ℕ), C.Represents τ m := by
  sorry

end Geometry

end Tilings

end
