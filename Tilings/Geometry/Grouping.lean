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
  sorry

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

/-- Step 1 of the blueprint proof of `outsideAnchoredGrouping`: defining `E`. -/
private lemma outsideAnchoredGrouping_step1_E (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier) :
    ∃ E : Set Pt, IsConnected (interior E) ∧
      (square c h + Binf (3 * M.D))ᶜ ⊆ interior E ∧
      ∀ F ∈ S.tiles, (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty →
      F.carrier ⊆ E := sorry

/-- Step 2 of the blueprint proof of `outsideAnchoredGrouping`: defining `H_carrier`. -/
private lemma outsideAnchoredGrouping_step2_H (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier)
    (E : Set Pt) (hE_conn : IsConnected (interior E))
    (hE_supset : (square c h + Binf (3 * M.D))ᶜ ⊆ interior E)
    (hE_faces : ∀ F ∈ S.tiles, (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty →
      F.carrier ⊆ E) :
    ∃ H_carrier : Set Pt, square c h + Binf (2 * M.D) ⊆ H_carrier ∧
      H_carrier ⊆ square c h + Binf (3 * M.D) ∧
      H_carrier = closure (connectedComponentIn (Eᶜ) c) ∧
      IsConnected (interior H_carrier) ∧ IsConnected (H_carrierᶜ) := sorry

private lemma outsideAnchoredGrouping_step3_FaceGroup (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier)
    (E : Set Pt) (hE_conn : IsConnected (interior E))
    (hE_supset : (square c h + Binf (3 * M.D))ᶜ ⊆ interior E)
    (hE_faces : ∀ F ∈ S.tiles, (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty →
      F.carrier ⊆ E)
    (H_carrier : Set Pt) (hH_sub : H_carrier ⊆ square c h + Binf (3 * M.D))
    (hH_def : H_carrier = closure (connectedComponentIn (Eᶜ) c)) :
    ∃ H : FaceGroup S.tiles, H.carrier = H_carrier := sorry

private lemma outsideAnchoredGrouping_step4_anchor (M : MeshConstants P) (S : Patch P)
    (Ω : PolygonalDisk)
    (hcov : support S.tiles = Ω.carrier) (hsts : SideToSideSet S.tiles)
    (c : Pt) (h : ℝ) (hh : 0 < h)
    (hQ : square c h + Binf (10 * M.D) ⊆ interior Ω.carrier)
    (E : Set Pt)
    (hE_faces : ∀ F ∈ S.tiles, (interior F.carrier ∩ (square c h + Binf (3 * M.D))ᶜ).Nonempty →
      F.carrier ⊆ E)
    (H : FaceGroup S.tiles) (hH_sub : H.carrier ⊆ square c h + Binf (3 * M.D))
    (hH_def : H.carrier = closure (connectedComponentIn (Eᶜ) c))
    (hH_conn_int : IsConnected (interior H.carrier))
    (hH_conn_comp : IsConnected (H.carrierᶜ)) :
    H.OutsideAnchored (square c h + Binf (3 * M.D)) := sorry

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
  rcases s1 with ⟨E, hE_conn, hE_supset, hE_faces⟩
  have s2 := outsideAnchoredGrouping_step2_H M S Ω hcov hsts c h hh hQ E hE_conn
    hE_supset hE_faces
  rcases s2 with ⟨H_carrier, hH_supset, hH_subset, hH_def, hH_conn_int, hH_conn_comp⟩
  have s3 := outsideAnchoredGrouping_step3_FaceGroup M S Ω hcov hsts c h hh hQ E hE_conn
    hE_supset hE_faces H_carrier hH_subset hH_def
  rcases s3 with ⟨H, hH_eq⟩
  use H
  rw [hH_eq]
  refine ⟨hH_supset, hH_subset, ?_, hH_conn_comp⟩
  rw [← hH_eq] at hH_subset hH_def hH_conn_int hH_conn_comp
  exact outsideAnchoredGrouping_step4_anchor M S Ω hcov hsts c h hh hQ E hE_faces H
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
  sorry

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
  sorry

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

/-- Step 2 of the blueprint proof of `fingerprintSeparation`: Types in different
templates have disjoint possible fingerprints. -/
private lemma fingerprintSeparation_step2_templates (F : FingerprintData)
    (h_tmpl : ∀ t, ∀ v ∈ F.ordinary t, F.template v = F.template t)
    (h_orig_ne : ∀ u, F.kind u = .original → F.ordinary u ≠ 0)
    (h_small_ge : ∀ t, F.kind t = .small → 2 ≤ Multiset.card (F.ordinary t)) :
    ∀ t u, F.kind t ≠ .central → F.kind u ≠ .central → F.template t ≠ F.template u →
    Disjoint (F.possibleFingerprints t) (F.possibleFingerprints u) := sorry

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
    Disjoint (F.possibleFingerprints t) (F.possibleFingerprints u) := sorry

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
structure RoutingSetup (τ : Substitution P) where
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
  small_private : ∀ l α, 0 < l → ∀ X ∈ (retained l α).children.tiles, X ≠ central l α →
    SharesSide X (central l α) →
    4 ≤ {e | HasEdge X e ∧ ∃ Y ∈ (retained l α).children.tiles, (∃ p, Y.form = Sum.inr p) ∧
      HasEdge Y e ∧ ∀ Z ∈ (retained l α).children.tiles, Z ≠ X →
        (∃ β, Z.form = Sum.inl β) → Disjoint Y.carrier Z.carrier}.ncard
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
    (Rs : RoutingSetup τ) :
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
