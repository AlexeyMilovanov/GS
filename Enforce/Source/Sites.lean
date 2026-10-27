import Enforce.Source.Headers
import Enforce.Source.Edges

/-!
# Recursive coface traces and ordinary sites

A trace piece records its owner and every coface in the fixed flag. Thus owners
without a full coface chain never enter the trace. The bottom dimension is two,
except in dimension two, where it is one, exactly as prescribed after V4 1.22(c).
No selected site arms or statement 1.23(d) are included (Proposition 8.3).
-/

open Set Metric

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d}

/-- P17, V4 1.22, dimension-two paragraph: dimension of the recursive trace. -/
def traceDimension (d : ℕ) : ℕ := min 2 (d - 1)

/-- P17, V4 1.22: the trace dimension is positive in every allowed dimension. -/
theorem traceDimension_pos : 1 ≤ traceDimension d := by
  have hd : 2 ≤ d := Fact.out
  unfold traceDimension
  omega

/-- P17, V4 1.22: the trace is a boundary-dimensional cell. -/
theorem traceDimension_lt : traceDimension d < d := by
  have hd : 2 ≤ d := Fact.out
  unfold traceDimension
  omega

/-- P17, V4 1.22(c): indices of a coface chain starting at dimension `j`. -/
abbrev ChainIndex (d j : ℕ) := {i : Fin d // j ≤ i.val ∧ 1 ≤ i.val}

/-- P17, V4 1.22(c): an occurrence has a complete chain up to the outer facet.
The target flag is in the standard height-`r` root; the owner may have any height. -/
structure ChainOccurrence (A : S.ι) (F : FacetFlag S A) (r : ℕ)
    (C : FramedNode S) (h j : ℕ) where
  /-- P17, V4 1.22(c): named cells of the owner at every required dimension. -/
  cell : ChainIndex d j → CellName S C.ty
  /-- P17, V4 1.22(c): exact dimension at each index. -/
  dimension : ∀ i, (cell i).val.dim = i.val.val
  /-- P17, V4 1.22(c): the entire chain is nested. -/
  nested : ∀ i k, i.val.val ≤ k.val.val →
    (cell i).val.carrier ⊆ (cell k).val.carrier
  /-- P17, V4 1.22(c): every coface lies in the prescribed ancestral flag cell. -/
  contained : ∀ i, C.cell h (cell i).val ⊆
    (S.σ ^ r) '' (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier

/-- P17, V4 1.22(a): a native trace polygon (or edge) and its complete owner chain. -/
structure TracePiece (A : S.ι) (F : FacetFlag S A) (r : ℕ) where
  /-- P17, V4 1.22(a): exact native owner address. -/
  owner : S.RoleWord A r
  /-- P17, V4 1.22(a): recorded chain from the trace cell to the facet. -/
  chain : ChainOccurrence A F r (S.nativeTile A r owner) 0 (traceDimension d)

namespace TracePiece

variable {A : S.ι} {F : FacetFlag S A} {r : ℕ}

/-- P17, V4 1.22(a): the actual selected native owner. -/
def tile (a : TracePiece A F r) : FramedNode S := S.nativeTile A r a.owner

/-- P17, V4 1.22(a): bottom index of the coface chain. -/
def bottomIndex : ChainIndex d (traceDimension d) :=
  ⟨⟨traceDimension d, traceDimension_lt⟩, le_rfl, traceDimension_pos⟩

/-- P17, V4 1.22(a): the named polygon (or edge in dimension two). -/
def bottom (a : TracePiece A F r) : CellName S a.tile.ty :=
  a.chain.cell bottomIndex

/-- P17, V4 1.22(a): its actual native-scale placed carrier. -/
def carrier (a : TracePiece A F r) : Set (E d) := a.tile.cell 0 a.bottom.val

/-- P17, V4 1.22(a): native cell names of the recorded chain, with absent lower
indices recorded by `none`. These labels are finite and preserve all coface names. -/
def chainNames (a : TracePiece A F r) (i : Fin d) : Option (Cell d) := by
  classical
  exact if hi : traceDimension d ≤ i.val ∧ 1 ≤ i.val then
    some (a.chain.cell ⟨i, hi⟩).val else none

end TracePiece

/-- P17, V4 1.22(a): only finitely many owner/chain occurrences at a fixed depth. -/
theorem tracePieces_finite (A : S.ι) (F : FacetFlag S A) (r : ℕ) :
    Finite (TracePiece A F r) := by
  sorry

/-- P17, V4 1.22(a): the recursive trace `𝓟₂`, with owners and full recorded chains.
All chains are required to lie inside the fixed successive cofaces. The geometric
trace theorem proves that these occurrences give exactly a tiling of the bottom cell. -/
def recursiveTrace (A : S.ι) (F : FacetFlag S A) (r : ℕ) : Finset (TracePiece A F r) := by
  classical
  letI := tracePieces_finite A F r
  letI := Fintype.ofFinite (TracePiece A F r)
  exact Finset.univ

/-- P17, V4 1.22(a): the trace tiles the designated two-cell, or the edge when
`d = 2`, and its distinct occurrences have disjoint relative interiors. -/
theorem recursiveTrace_tiles (A : S.ι) (F : FacetFlag S A) (r : ℕ) :
    (⋃ a ∈ recursiveTrace A F r, a.carrier) =
      (S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
        traceDimension_lt⟩).val.carrier ∧
    Pairwise (fun a b : TracePiece A F r => Disjoint (relint a.carrier)
      (relint b.carrier)) ∧
    ∀ a : TracePiece A F r, ∀ i : ChainIndex d (traceDimension d),
      affineSpan ℝ (a.tile.cell 0 (a.chain.cell i).val) =
        affineSpan ℝ ((S.σ ^ r) ''
          (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier) := by
  sorry

/-- P17, V4 1.22(b): all standard native frames are compatible. -/
theorem nativeFrame_mem (A : S.ι) (r : ℕ) (w : S.RoleWord A r) :
    (S.nativeTile A r w).frame.linearIsometryEquiv ∈ S.rotGroup := by
  sorry

/-- P17, V4 1.22(b): inflate a native owner to a height-`s` node, keeping its
entire native subdivision, rather than choosing a geometric containing tile. -/
def inflatedNative (A : S.ι) (r : ℕ) (w : S.RoleWord A r) (s : ℕ) : FramedNode S :=
  ⟨(S.nativeTile A r w).ty,
    compatibleInflatedFrame (S.nativeTile A r w) (nativeFrame_mem A r w) s⟩

/-- P17, V4 1.22(b): finer trace pieces refine both the owner and every coface.
Native-scale levels `r` and `r+s` are compared by the common ambient map `σˢ`. -/
theorem trace_refines (A : S.ι) (F : FacetFlag S A) (r s : ℕ)
    (b : TracePiece A F (r + s)) :
    ∃ a : TracePiece A F r,
      b.tile.IsDescendant 0 (inflatedNative A r a.owner s) s ∧
      ∀ i : ChainIndex d (traceDimension d),
        b.tile.cell 0 (b.chain.cell i).val ⊆
          (S.σ ^ s) '' (a.tile.cell 0 (a.chain.cell i).val) := by
  sorry

/-- P17, V4 1.22(c): disjointness is asserted only for children with the full
coface chain, including zero-trace sectors correctly by excluding chainless cells. -/
theorem chain_occurrences_disjoint (A : S.ι) (F : FacetFlag S A) (r h : ℕ)
    (P : FramedNode S) (hP : S.IsStandardNode A r (h + 1) P)
    (i l : S.I P.ty) (hil : i ≠ l) (j : ℕ) (hj : 1 ≤ j) (hjd : j < d)
    (a : ChainOccurrence A F r (P.child h i) h j)
    (b : ChainOccurrence A F r (P.child h l) h j) :
    Disjoint (relint ((P.child h i).cell h
      (a.cell ⟨⟨j, hjd⟩, le_rfl, hj⟩).val))
      (relint ((P.child h l).cell h (b.cell ⟨⟨j, hjd⟩, le_rfl, hj⟩).val)) := by
  sorry

/-- P18, V4 1.23: the original flag edge at native scale after `r` expansions. -/
def flagEdge (A : S.ι) (F : FacetFlag S A) (r : ℕ) : Set (E d) :=
  (S.σ ^ r) '' (F.cell ⟨1, le_rfl, by have := (Fact.out : 2 ≤ d); omega⟩).val.carrier

/-- P18, V4 1.23: an edge of a trace polygon lying along the outer flag edge,
with the specified endpoint. This also covers the one-dimensional trace. -/
def BoundaryTraceEdge {A : S.ι} {F : FacetFlag S A} {r : ℕ}
    (a : TracePiece A F r) (q : E d) (K : Set (E d)) : Prop :=
  ∃ e : CellName S a.tile.ty, e.val.dim = 1 ∧ K = a.tile.cell 0 e.val ∧
    K ⊆ a.carrier ∧ K ⊆ flagEdge A F r ∧ q ∈ K ∧ a.tile.Lists 0 q

/-- P18, V4 1.23, dimension-two paragraph: inward trace arms.
For a planar trace the arm is an internal tile edge leaving the boundary edge;
otherwise it is an edge of a trace polygon entering the relative interior of `F₂`. -/
def InwardTraceArm (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d) : Prop :=
  if d = 2 then
    ∃ (w : S.RoleWord A r) (e : CellName S (S.nativeTile A r w).ty),
      e.val.dim = 1 ∧ (S.nativeTile A r w).Lists 0 q ∧
      q ∈ (S.nativeTile A r w).cell 0 e.val ∧
      relint ((S.nativeTile A r w).cell 0 e.val) ⊆ interior (S.supertile r A)
  else
    ∃ (a : TracePiece A F r) (e : CellName S a.tile.ty),
      e.val.dim = 1 ∧ a.tile.Lists 0 q ∧ q ∈ a.tile.cell 0 e.val ∧
      a.tile.cell 0 e.val ⊆ a.carrier ∧
      relint (a.tile.cell 0 e.val) ⊆
        relint ((S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
          traceDimension_lt⟩).val.carrier)

/-- P18, V4 1.23: ordinary sites, with two distinct owners adjacent along the
edge and an inward arm. Distinct native owners have least common ancestor at a
strictly smaller depth; the explicit common standard ancestor retains that condition. -/
def IsSite (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d) : Prop :=
  q ∈ relint (flagEdge A F r) ∧ InwardTraceArm A F r q ∧
    ∃ (a b : TracePiece A F r) (K L : Set (E d)),
      a.owner ≠ b.owner ∧ BoundaryTraceEdge a q K ∧ BoundaryTraceEdge b q L ∧
      (∃ x ∈ relint K, ∃ y ∈ relint L, q ∈ openSegment ℝ x y) ∧
      ∃ (j : ℕ) (P : FramedNode S), j < r ∧ S.IsStandardNode A r (r - j) P ∧
        a.tile.IsDescendant 0 P (r - j) ∧ b.tile.IsDescendant 0 P (r - j)

/-- P18, V4 1.23(a): arbitrarily many ordinary sites occur from some depth on.
The sites in the finite witness set are distinct; expansion provides the length. -/
theorem sites_exist (A : S.ι) (F : FacetFlag S A) (N : ℕ) (hN : 1 ≤ N) :
    ∃ r : ℕ, ∀ r' : ℕ, r ≤ r' →
      ∃ q : Finset (E d), N ≤ q.card ∧ ∀ p ∈ q, IsSite A F r' p := by
  sorry

/-- P18, V4 1.23(b): a selected-owner template records full relative frames,
vertex names and all recorded coface names, together with the normalized site. -/
abbrev SiteTemplate (S : SubstSystem d) :=
  E d × Set (FramedNode S × Cell d × (Fin d → Option (Cell d)))

/-- P18, V4 1.23(b): complete positioned star of selected owners at a site,
expressed in any one selected owner's frame. Owners without a trace chain are absent. -/
def siteTemplate {A : S.ι} {F : FacetFlag S A} {r : ℕ}
    (q : E d) (anchor : TracePiece A F r) : SiteTemplate S :=
  (anchor.tile.frame.symm q,
    {z | ∃ (a : TracePiece A F r) (v : Cell d), q ∈ a.carrier ∧
      v ∈ (S.cx a.tile.ty).vertices ∧ q ∈ a.tile.cell 0 v ∧
      z = (a.tile.move anchor.tile.frame.symm, v, a.chainNames)})

/-- P18, V4 1.23(b): all native-scale selected-owner templates, uniformly in
type, flag, depth, site and reference owner. -/
def siteTemplates (S : SubstSystem d) : Set (SiteTemplate S) :=
  {t | ∃ (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d)
    (anchor : TracePiece A F r), IsSite A F r q ∧ q ∈ anchor.carrier ∧
      t = siteTemplate q anchor}

/-- Step 1 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"translations are fixed by the common vertex". The native vertex coordinates
form a finite set, including when the type catalogue is empty. -/
private theorem site_fan_finite_step1_vertices (S : SubstSystem d) :
    {p : E d | ∃ A : S.ι, ∃ v ∈ (S.cx A).vertices, p ∈ v.carrier}.Finite := by
  have hv : ∀ (A : S.ι) (v : Cell d), v ∈ (S.cx A).vertices → v.carrier.Finite := by
    intro A v hv
    have hdim : v.dim = 0 := (Finset.mem_filter.mp hv).2
    have hzero : cellDirection v.carrier = ⊥ :=
      Submodule.finrank_eq_zero.mp (v.flat.dimension.trans hdim)
    apply ((vectorSpan_eq_bot_iff_subsingleton ℝ).mp ?_).finite
    simpa [cellDirection, direction_affineSpan] using hzero
  have hf := Set.finite_iUnion fun A : S.ι =>
    (S.cx A).vertices.finite_toSet.biUnion (hv A)
  exact hf.subset (by intro p hp; simpa using hp)

/-- Step 2 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"finitely many native choices". A full flag is determined by its finitely
many named cells; the geometric conditions add no further data. -/
private theorem site_fan_finite_step2_flags (A : S.ι) : Finite (FacetFlag S A) := by
  letI : Finite {j : ℕ // 1 ≤ j ∧ j < d} :=
    Finite.of_injective (fun j => (⟨j.val, j.property.2⟩ : Fin d))
      (by intro i j h; exact Subtype.ext (congrArg Fin.val h))
  apply Finite.of_injective (fun F : FacetFlag S A => F.cell)
  intro F G h
  cases F
  cases G
  cases h
  rfl

/-- Step 3 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"sign choices on the successive one-dimensional complements". On a real
line, fixing the norm of a vector leaves at most the two sign choices. -/
private theorem site_fan_finite_step3_line (V : Submodule ℝ (E d))
    (hV : Module.finrank ℝ V = 1) (z : E d) (hz : z ∈ V) :
    {x : E d | x ∈ V ∧ ‖x‖ = ‖z‖}.Finite := by
  apply (Set.toFinite ({z, -z} : Set (E d))).subset
  rintro x ⟨hx, hn⟩
  by_cases hzero : z = 0
  · have hxzero : x = 0 := norm_eq_zero.mp (by simpa [hzero] using hn)
    simp [hzero, hxzero]
  have hz' : (⟨z, hz⟩ : V) ≠ 0 := by simpa using hzero
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨z, hz⟩ : V) hz').mp hV ⟨x, hx⟩
  have heq : c • z = x := congrArg Subtype.val hc
  have hcabs : |c| = 1 := by
    have hnorm : |c| * ‖z‖ = 1 * ‖z‖ := by
      simpa [← heq, norm_smul, Real.norm_eq_abs] using hn
    exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hzero) hnorm
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hcabs with hc | hc
  · simp [← heq, hc]
  · simp [← heq, hc]

/-- Step 3 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"sign choices on the successive one-dimensional complements". An
orthogonal stabilizer of a complete flag has finite orbits on vectors. -/
private theorem site_fan_finite_step3_flag_orbit
    (V : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1)) :
    ∀ k ≤ d, ∀ x ∈ V k,
      {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = V i}.image
        (fun R => R x) |>.Finite := by
  intro k
  induction k with
  | zero =>
      intro hk x hx
      have hV : V 0 = ⊥ := Submodule.finrank_eq_zero.mp (hdim 0 (by omega))
      have hxzero : x = 0 := by simpa [hV] using hx
      subst x
      exact (Set.finite_singleton (0 : E d)).subset
        (by rintro _ ⟨R, hR, rfl⟩; simp)
  | succ k ih =>
      intro hk x hx
      obtain ⟨y, hy, z, hz, hsum⟩ := (V k).exists_add_mem_mem_orthogonal x
      have hle : V k ≤ V (k + 1) := hmono k (by omega)
      have hzV : z ∈ V (k + 1) := by
        have heq : z = x - y := by rw [hsum]; abel
        rw [heq]
        exact (V (k + 1)).sub_mem hx (hle hy)
      have hline : Module.finrank ℝ ((V k)ᗮ ⊓ V (k + 1) : Submodule ℝ (E d)) = 1 := by
        have hh := Submodule.finrank_add_inf_finrank_orthogonal hle
        rw [hdim k (by omega), hdim (k + 1) hk] at hh
        omega
      have hyfinite := ih (by omega) y hy
      have hzfinite := site_fan_finite_step3_line ((V k)ᗮ ⊓ V (k + 1)) hline z ⟨hz, hzV⟩
      apply ((hyfinite.prod hzfinite).image (fun yz : E d × E d => yz.1 + yz.2)).subset
      rintro _ ⟨R, hR, rfl⟩
      refine ⟨(R y, R z), ⟨⟨R, hR, rfl⟩, ?_⟩, ?_⟩
      · refine ⟨⟨?_, ?_⟩, R.norm_map z⟩
        · have horth : ((V k)ᗮ).map R.toLinearEquiv.toLinearMap = (V k)ᗮ := by
            rw [Submodule.map_orthogonal_equiv, hR k (by omega)]
          rw [← horth]
          exact Submodule.mem_map_of_mem hz
        · rw [← hR (k + 1) hk]
          exact Submodule.mem_map_of_mem hzV
      · simpa [map_add] using (congrArg R hsum).symm

/-- Step 3 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"sign choices on the successive one-dimensional complements". Values on
one basis turn the finite vector orbits into a finite orthogonal stabilizer. -/
private theorem site_fan_finite_step3_flag_stabilizer
    (V : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1)) :
    {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = V i}.Finite := by
  let H := {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = V i}
  let b := stdOrthonormalBasis ℝ (E d)
  have htop : V d = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using hdim d le_rfl)
  have hpoint : ∀ i, (H.image (fun R => R (b i))).Finite := by
    intro i
    exact site_fan_finite_step3_flag_orbit V hdim hmono d le_rfl (b i) (by simp [htop])
  have heval : ((fun R : Ortho d => fun i => R (b i)) '' H).Finite :=
    (Set.Finite.pi' hpoint).subset (by rintro _ ⟨R, hR, rfl⟩ i; exact ⟨R, hR, rfl⟩)
  apply Set.Finite.of_finite_image heval
  intro R hR T hT heq
  exact b.toBasis.ext_linearIsometryEquiv (fun i => congrFun heq i)

/-- Step 3 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"all relative placements ... lie in a finite set" once two full flags are
specified. The transporter is a translate of the finite flag stabilizer. -/
private theorem site_fan_finite_step3_flag_transporters
    (V W : ℕ → Submodule ℝ (E d))
    (hdim : ∀ i ≤ d, Module.finrank ℝ (V i) = i)
    (hmono : ∀ i < d, V i ≤ V (i + 1)) :
    {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = W i}.Finite := by
  classical
  let T := {R : Ortho d | ∀ i ≤ d, (V i).map R.toLinearEquiv.toLinearMap = W i}
  by_cases hT : T.Nonempty
  · obtain ⟨R₀, hR₀⟩ := hT
    apply ((site_fan_finite_step3_flag_stabilizer V hdim hmono).image
      (fun R => R.trans R₀)).subset
    intro R hR
    refine ⟨R.trans R₀.symm, ?_, ?_⟩
    · intro i hi
      change (V i).map (R₀.symm.toLinearEquiv.toLinearMap.comp
        R.toLinearEquiv.toLinearMap) = V i
      rw [Submodule.map_comp, hR i hi, ← hR₀ i hi, ← Submodule.map_comp]
      simp
    · apply LinearIsometryEquiv.ext
      intro x
      exact R₀.apply_symm_apply (R x)
  · exact Set.finite_empty.subset (by intro R hR; exact (hT ⟨R, hR⟩).elim)

/-- Step 3 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"The chains ... have direction spaces equal". Direction spaces commute
with the linear part of the actual isometric frame. -/
private theorem site_fan_finite_step3_direction_image (g : Iso d) (K : Set (E d)) :
    cellDirection (g '' K) =
      (cellDirection K).map g.linearIsometryEquiv.toLinearEquiv.toLinearMap := by
  change (affineSpan ℝ (g.toAffineEquiv.toAffineMap '' K)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  rfl

/-- Full flags include the zero subspace and the ambient space when used
as a complete sequence of direction spaces. -/
private def siteFanFlagDirections {A : S.ι} (F : FacetFlag S A)
    (i : ℕ) : Submodule ℝ (E d) :=
  if hi : 1 ≤ i ∧ i < d then cellDirection (F.cell ⟨i, hi⟩).val.carrier
  else if i = 0 then ⊥ else ⊤

/-- Step 3 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"preserving this partial flag" with an additional polygon edge gives a
complete flag of direction spaces, of dimensions zero through `d`. -/
private theorem site_fan_finite_step3_flag_directions {A : S.ι}
    (F : FacetFlag S A) :
    (∀ i ≤ d, Module.finrank ℝ (siteFanFlagDirections F i) = i) ∧
    (∀ i < d, siteFanFlagDirections F i ≤ siteFanFlagDirections F (i + 1)) := by
  constructor
  · intro i hi
    by_cases hmid : 1 ≤ i ∧ i < d
    · rw [show siteFanFlagDirections F i =
          cellDirection (F.cell ⟨i, hmid⟩).val.carrier from dif_pos hmid]
      exact (F.cell ⟨i, hmid⟩).val.flat.dimension.trans (F.dimension ⟨i, hmid⟩)
    · by_cases hz : i = 0
      · simp [siteFanFlagDirections, hmid, hz]
      · have hid : i = d := by omega
        rw [show siteFanFlagDirections F i = ⊤ by
          simp only [siteFanFlagDirections, dif_neg hmid, if_neg hz]]
        simp [hid]
  · intro i hi
    by_cases hz : i = 0
    · simp [siteFanFlagDirections, hz]
    by_cases ht : i + 1 < d
    · have hmid : 1 ≤ i ∧ i < d := ⟨by omega, hi⟩
      have hnext : 1 ≤ i + 1 ∧ i + 1 < d := ⟨by omega, ht⟩
      simp only [siteFanFlagDirections, dif_pos hmid, dif_pos hnext]
      simpa only [cellDirection, direction_affineSpan] using
        vectorSpan_mono ℝ (F.nested ⟨i, hmid⟩ ⟨i + 1, hnext⟩ (by simp))
    · have hnext : ¬(1 ≤ i + 1 ∧ i + 1 < d) := by omega
      simp only [siteFanFlagDirections, dif_neg hnext, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, if_false]
      exact le_top

/-- Step 3 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"translations are fixed by the common vertex". Two full native flags and
one prescribed point image admit only finitely many isometric frames. -/
private theorem site_fan_finite_step3_affine_transporters
    {A B : S.ι} (F : FacetFlag S A) (G : FacetFlag S B) (p q : E d) :
    {g : Iso d | g p = q ∧ ∀ i,
      cellDirection (g '' (F.cell i).val.carrier) =
        cellDirection (G.cell i).val.carrier}.Finite := by
  have hF := site_fan_finite_step3_flag_directions F
  have hrot := site_fan_finite_step3_flag_transporters
    (siteFanFlagDirections F) (siteFanFlagDirections G) hF.1 hF.2
  have himage : (AffineIsometryEquiv.linearIsometryEquiv ''
      {g : Iso d | g p = q ∧ ∀ i,
        cellDirection (g '' (F.cell i).val.carrier) =
          cellDirection (G.cell i).val.carrier}).Finite := by
    apply hrot.subset
    rintro _ ⟨g, hg, rfl⟩ i hi
    by_cases hmid : 1 ≤ i ∧ i < d
    · simpa only [siteFanFlagDirections, dif_pos hmid,
        site_fan_finite_step3_direction_image] using hg.2 ⟨i, hmid⟩
    · simp only [siteFanFlagDirections, dif_neg hmid]
      split_ifs <;> simp
  apply Set.Finite.of_finite_image himage
  intro g hg h hh heq
  apply AffineIsometryEquiv.ext
  intro x
  have hgx := g.map_vadd p (x - p)
  have hhx := h.map_vadd p (x - p)
  simp only [vadd_eq_add, sub_add_cancel, hg.1, hh.1, heq] at hgx hhx
  exact hgx.trans hhx.symm

/-- Step 4 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"at native scale". A height-zero named cell is placed by the native
isometric frame alone. -/
private theorem site_fan_finite_step4_cell_zero (C : FramedNode S) (e : Cell d) :
    C.cell 0 e = C.frame '' e.carrier := by
  simp [FramedNode.cell, FramedNode.prototypeFrame]

/-- Step 4 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"translations are fixed by the common vertex". Pulling a listed point
back by its owner's frame gives one of the native vertex coordinates. -/
private theorem site_fan_finite_step4_listed_coordinate (C : FramedNode S)
    (q : E d) (hq : C.Lists 0 q) :
    ∃ A : S.ι, ∃ v ∈ (S.cx A).vertices, C.frame.symm q ∈ v.carrier := by
  obtain ⟨v, hv, hp⟩ := hq
  rw [site_fan_finite_step4_cell_zero] at hp
  obtain ⟨p, hp, rfl⟩ := hp
  exact ⟨C.ty, v, hv, by simpa using hp⟩

/-- Two native owners have aligned full flags when all their placed
flag direction spaces, including the edge line, agree. -/
private def siteFanAligned (C D : FramedNode S) : Prop :=
  ∃ (F : FacetFlag S C.ty) (G : FacetFlag S D.ty), ∀ i,
    cellDirection (C.cell 0 (F.cell i).val) =
      cellDirection (D.cell 0 (G.cell i).val)

/-- Step 4 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"finitely many native choices ... and reflections". For owners sharing a
listed point and aligned full flags, their relative frame belongs to one
finite alphabet, independent of the common point or subdivision depth. -/
private theorem site_fan_finite_step4_transitions (S : SubstSystem d) :
    ∃ D : Set (Iso d), D.Finite ∧ ∀ (C B : FramedNode S) (q : E d),
      C.Lists 0 q → B.Lists 0 q → siteFanAligned C B →
      C.frame.trans B.frame.symm ∈ D := by
  classical
  let V := {p : E d | ∃ A : S.ι, ∃ v ∈ (S.cx A).vertices, p ∈ v.carrier}
  have hV : V.Finite := site_fan_finite_step1_vertices S
  letI : ∀ A : S.ι, Finite (FacetFlag S A) := site_fan_finite_step2_flags
  let D : Set (Iso d) := ⋃ (A : S.ι) (B : S.ι) (F : FacetFlag S A)
      (G : FacetFlag S B) (p ∈ V) (q ∈ V),
    {g : Iso d | g p = q ∧ ∀ i,
      cellDirection (g '' (F.cell i).val.carrier) =
        cellDirection (G.cell i).val.carrier}
  refine ⟨D, ?_, ?_⟩
  · exact Set.finite_iUnion fun A => Set.finite_iUnion fun B =>
      Set.finite_iUnion fun F => Set.finite_iUnion fun G =>
      hV.biUnion fun p hp => hV.biUnion fun q hq =>
        site_fan_finite_step3_affine_transporters F G p q
  · intro C B q hC hB hCB
    obtain ⟨F, G, hFG⟩ := hCB
    refine Set.mem_iUnion.mpr ⟨C.ty, Set.mem_iUnion.mpr ⟨B.ty,
      Set.mem_iUnion.mpr ⟨F, Set.mem_iUnion.mpr ⟨G,
      Set.mem_iUnion.mpr ⟨C.frame.symm q, Set.mem_iUnion.mpr
        ⟨site_fan_finite_step4_listed_coordinate C q hC,
      Set.mem_iUnion.mpr ⟨B.frame.symm q, Set.mem_iUnion.mpr
        ⟨site_fan_finite_step4_listed_coordinate B q hB, ?_⟩⟩⟩⟩⟩⟩⟩⟩
    constructor
    · simp
    · intro i
      have heq := congrArg
        (fun U : Submodule ℝ (E d) =>
          U.map B.frame.symm.linearIsometryEquiv.toLinearEquiv.toLinearMap) (hFG i)
      simp only [site_fan_finite_step4_cell_zero,
        ← site_fan_finite_step3_direction_image] at heq
      simpa [← Set.image_comp] using heq

/-- The selected owners, forgetting duplicate chain occurrences of one owner. -/
private def siteFanOwners {A : S.ι} {F : FacetFlag S A} {r : ℕ}
    (q : E d) : Set (FramedNode S) :=
  {C | ∃ a : TracePiece A F r, q ∈ a.carrier ∧ C = a.tile}

/-- Join distinct selected owners whenever their full native flags align.
Consecutive sectors in the planar fan supply such edges. -/
private def siteFanGraph {A : S.ι} {F : FacetFlag S A} {r : ℕ}
    (q : E d) : SimpleGraph (siteFanOwners (A := A) (F := F) (r := r) q) where
  Adj C B := C ≠ B ∧ siteFanAligned C.val B.val
  symm := by
    rintro C B ⟨hne, F, G, hFG⟩
    exact ⟨hne.symm, G, F, fun i => (hFG i).symm⟩
  loopless := ⟨by intro C h; exact h.1 rfl⟩

/-- Step 5 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"Each selected owner C lists q (as q is a vertex of its polygon ... and
a vertex of a cell of C is a vertex of C)." The two boundary trace edges
at a site exclude a selected polygon filling a whole half-disc at q. -/
private theorem site_fan_finite_step5_listed {A : S.ι} {F : FacetFlag S A}
    {r : ℕ} (q : E d) (hq : IsSite A F r q) (a : TracePiece A F r)
    (ha : q ∈ a.carrier) : a.tile.Lists 0 q := by
  obtain ⟨left, right, K, L, hne, hleft, hright, hbetween, hancestor⟩ := hq.2.2
  have hl : left.tile.Lists 0 q := by
    obtain ⟨e, he, hK, hsub, hflag, hqK, hl⟩ := hleft
    exact hl
  have hr : right.tile.Lists 0 q := by
    obtain ⟨e, he, hL, hsub, hflag, hqL, hr⟩ := hright
    exact hr
  by_cases h : a.owner = left.owner
  · simpa [TracePiece.tile, h] using hl
  by_cases h' : a.owner = right.owner
  · simpa [TracePiece.tile, h'] using hr
  sorry

/-- Step 6 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"The chains ... have direction spaces equal to those of F₂ ... F_{d-1}."
Containment and equality of dimensions give equality of direction spaces;
the ambient expansion need not be a similarity. -/
private theorem site_fan_finite_step6_chain_directions {A : S.ι}
    {F : FacetFlag S A} {r : ℕ} (a : TracePiece A F r)
    (i : ChainIndex d (traceDimension d)) :
    cellDirection (a.tile.cell 0 (a.chain.cell i).val) =
      cellDirection ((S.σ ^ r) ''
        (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier) := by
  have hdim (g : E d ≃ᵃ[ℝ] E d) (K : Set (E d)) :
      Module.finrank ℝ (cellDirection (g '' K)) =
        Module.finrank ℝ (cellDirection K) := by
    change Module.finrank ℝ (affineSpan ℝ (g.toAffineMap '' K)).direction = _
    rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
    exact LinearEquiv.finrank_map_eq g.linear (cellDirection K)
  have hle : cellDirection (a.tile.cell 0 (a.chain.cell i).val) ≤
      cellDirection ((S.σ ^ r) ''
        (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier) := by
    simpa only [cellDirection, direction_affineSpan] using
      vectorSpan_mono ℝ (a.chain.contained i)
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hleft : Module.finrank ℝ (cellDirection
      (a.tile.cell 0 (a.chain.cell i).val)) = i.val.val := by
    rw [site_fan_finite_step4_cell_zero]
    exact (hdim a.tile.frame.toAffineEquiv _).trans
      ((a.chain.cell i).val.flat.dimension.trans (a.chain.dimension i))
  have hright : Module.finrank ℝ (cellDirection ((S.σ ^ r) ''
      (F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.carrier)) = i.val.val :=
    (hdim (S.σ ^ r).toAffineEquiv _).trans
      ((F.cell ⟨i.val.val, i.property.2, i.val.isLt⟩).val.flat.dimension.trans
        (F.dimension ⟨i.val.val, i.property.2, i.val.isLt⟩))
  exact hleft.trans hright.symm

/-- Step 6 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"the polygons ... form a finite planar fan". Consecutive sectors share an
edge line, which extends their recorded coface chains to aligned full flags.
Thus all selected owners are connected by these full-flag transitions.
For `d = 2` the recorded chains already include the common edge line. -/
private theorem site_fan_finite_step6_connected {A : S.ι} {F : FacetFlag S A}
    {r : ℕ} (q : E d) (hq : IsSite A F r q) :
    ∀ C B : siteFanOwners (A := A) (F := F) (r := r) q,
      (siteFanGraph q).Reachable C B := by
  by_cases hd : traceDimension d = 1
  · intro C B
    by_cases hCB : C = B
    · subst B
      exact SimpleGraph.Reachable.refl C
    obtain ⟨a, ha, hCa⟩ := C.property
    obtain ⟨b, hb, hBb⟩ := B.property
    let idx : {j : ℕ // 1 ≤ j ∧ j < d} → ChainIndex d (traceDimension d) :=
      fun j => ⟨⟨j.val, j.property.2⟩, by simpa [hd] using j.property.1, j.property.1⟩
    let full : (a : TracePiece A F r) → FacetFlag S a.tile.ty := fun a =>
      { cell := fun j => a.chain.cell (idx j)
        dimension := fun j => a.chain.dimension (idx j)
        nested := fun i j hij => a.chain.nested (idx i) (idx j) hij }
    have hfull : siteFanAligned a.tile b.tile := by
      refine ⟨full a, full b, ?_⟩
      intro i
      exact (site_fan_finite_step6_chain_directions a (idx i)).trans
        (site_fan_finite_step6_chain_directions b (idx i)).symm
    exact SimpleGraph.Adj.reachable (show (siteFanGraph q).Adj C B from
      ⟨hCB, by simpa [hCa, hBb] using hfull⟩)
  · sorry

/-- Step 7 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"owners of polygons ... meeting q". A selected trace cell is contained
in its native owner, so the native tile multiplicity bound applies. -/
private theorem site_fan_finite_step7_carrier_subset {A : S.ι} {F : FacetFlag S A}
    {r : ℕ} (a : TracePiece A F r) : a.carrier ⊆ a.tile.carrier 0 := by
  have he : relint a.bottom.val.carrier ⊆ frontier (S.proto a.tile.ty).carrier := by
    rw [← (S.cx a.tile.ty).cover]
    exact Set.subset_iUnion_of_subset a.bottom.val
      (Set.subset_iUnion_of_subset a.bottom.property (Set.Subset.refl _))
  have hsub : a.bottom.val.carrier ⊆ (S.proto a.tile.ty).carrier := by
    calc a.bottom.val.carrier = closure (relint a.bottom.val.carrier) :=
        a.bottom.val.flat.regularClosed.symm
      _ ⊆ closure (frontier (S.proto a.tile.ty).carrier) := closure_mono he
      _ = frontier (S.proto a.tile.ty).carrier := isClosed_frontier.closure_eq
      _ ⊆ closure (S.proto a.tile.ty).carrier := frontier_subset_closure
      _ = (S.proto a.tile.ty).carrier := (S.proto a.tile.ty).compact.isClosed.closure_eq
  simpa [TracePiece.carrier, site_fan_finite_step4_cell_zero,
    FramedNode.carrier, SubstSystem.supertile, placedSet] using
      Set.image_mono (f := a.tile.frame) hsub

/-- Step 7 of the V4 proof of `site_fan_finite` (V4 1.23(b), 1.0(c)):
"there are at most ... of them". The uniform native tile multiplicity
bound bounds the number of selected owners, even without a site hypothesis.
This supplies a bound on transition-word length without choosing angles. -/
private theorem site_fan_finite_step7_owner_bound (S : SubstSystem d) :
    ∃ M : ℕ, ∀ (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d),
      (siteFanOwners (A := A) (F := F) (r := r) q).Finite ∧
      Nat.card (siteFanOwners (A := A) (F := F) (r := r) q) ≤ M := by
  obtain ⟨β, hβ, hβfull, hangle, hbound⟩ := point_multiplicity_bound S.proto S.cx
  refine ⟨⌊fullSolidAngle d / β⌋₊, ?_⟩
  intro A F r q
  have hdisj : Pairwise (fun a b : S.RoleWord A r => Disjoint
      (interior (placedSet (S.nativeTile A r a).frame
        (S.proto (S.nativeTile A r a).ty).carrier))
      (interior (placedSet (S.nativeTile A r b).frame
        (S.proto (S.nativeTile A r b).ty).carrier))) := by
    simpa [FramedNode.carrier, SubstSystem.supertile] using S.native_disjoint A r
  obtain ⟨hfinite, hcard⟩ := hbound (S.RoleWord A r)
    (fun w => (S.nativeTile A r w).ty) (fun w => (S.nativeTile A r w).frame) hdisj q
  let I := {w : S.RoleWord A r | q ∈ placedSet (S.nativeTile A r w).frame
    (S.proto (S.nativeTile A r w).ty).carrier}
  have hsub : siteFanOwners (A := A) (F := F) (r := r) q ⊆
      S.nativeTile A r '' I := by
    rintro C ⟨a, ha, rfl⟩
    refine ⟨a.owner, ?_, rfl⟩
    have hc := site_fan_finite_step7_carrier_subset a ha
    simpa [I, TracePiece.tile, FramedNode.carrier, SubstSystem.supertile] using hc
  have hfimage : (S.nativeTile A r '' I).Finite := hfinite.image _
  refine ⟨hfimage.subset hsub, ?_⟩
  exact (Set.ncard_le_ncard hsub hfimage).trans ((Set.ncard_image_le hfinite).trans hcard)

/-- Products of at most `n` transitions, using composition in the order
of relative frames along a path. -/
private def siteFanProducts (D : Set (Iso d)) : ℕ → Set (Iso d)
  | 0 => {AffineIsometryEquiv.refl ℝ (E d)}
  | n + 1 => siteFanProducts D n ∪
      (fun gh : Iso d × Iso d => gh.1.trans gh.2) '' (siteFanProducts D n ×ˢ D)

/-- Step 8 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"their angle word is one of finitely many". Bounded words in the finite
alphabet of full-flag transitions have finitely many products. -/
private theorem site_fan_finite_step8_products (D : Set (Iso d)) (hD : D.Finite) :
    ∀ n, (siteFanProducts D n).Finite := by
  intro n
  induction n with
  | zero => exact Set.finite_singleton _
  | succ n ih => exact ih.union ((ih.prod hD).image _)

/-- Step 8 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"their angle word is one of finitely many". Increasing the permitted
length only enlarges the set of transition products. -/
private theorem site_fan_finite_step8_products_mono (D : Set (Iso d)) :
    Monotone (siteFanProducts D) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Set.subset_union_left

/-- Step 8 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"all relative placements ... lie in a finite set". Along a graph walk,
successive relative frames telescope to the relative frame of its endpoints. -/
private theorem site_fan_finite_step8_walk {α : Type} (G : SimpleGraph α)
    (f : α → Iso d) (D : Set (Iso d))
    (hstep : ∀ a b, G.Adj a b → (f b).trans (f a).symm ∈ D)
    {a b : α} (p : G.Walk a b) :
    (f b).trans (f a).symm ∈ siteFanProducts D p.length := by
  induction p with
  | nil => simp [siteFanProducts]
  | @cons a b c hab p ih =>
      apply Or.inr
      refine ⟨((f c).trans (f b).symm, (f b).trans (f a).symm),
        ⟨ih, hstep a b hab⟩, ?_⟩
      apply AffineIsometryEquiv.ext
      intro x
      simp

/-- Step 8 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"at most ... of them" bounds the word length. Erasing loops from a walk
gives a path shorter than the number of owners. -/
private theorem site_fan_finite_step8_reachable {α : Type} [Finite α]
    (G : SimpleGraph α) (f : α → Iso d) (D : Set (Iso d)) (M : ℕ)
    (hcard : Nat.card α ≤ M)
    (hstep : ∀ a b, G.Adj a b → (f b).trans (f a).symm ∈ D)
    {a b : α} (hreach : G.Reachable a b) :
    (f b).trans (f a).symm ∈ siteFanProducts D M := by
  classical
  letI := Fintype.ofFinite α
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  have hlen : p.length ≤ M := by
    have hh := hp.length_lt
    rw [Nat.card_eq_fintype_card] at hcard
    omega
  exact site_fan_finite_step8_products_mono D hlen
    (site_fan_finite_step8_walk G f D hstep p)

/-- Step 9 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"Hence all relative placements of the selected owners lie in a finite
set". Connect the owners, erase loops, and multiply their finitely many
possible full-flag transitions. -/
private theorem site_fan_finite_step9_frames (S : SubstSystem d) :
    ∃ K : Set (Iso d), K.Finite ∧
      ∀ (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d), IsSite A F r q →
      ∀ (anchor a : TracePiece A F r), q ∈ anchor.carrier → q ∈ a.carrier →
        a.tile.frame.trans anchor.tile.frame.symm ∈ K := by
  obtain ⟨D, hD, hstep⟩ := site_fan_finite_step4_transitions S
  obtain ⟨M, hM⟩ := site_fan_finite_step7_owner_bound S
  refine ⟨siteFanProducts D M, site_fan_finite_step8_products D hD M, ?_⟩
  intro A F r q hq anchor a hanchor ha
  let O := siteFanOwners (A := A) (F := F) (r := r) q
  letI : Finite O := (hM A F r q).1.to_subtype
  let C : O := ⟨anchor.tile, anchor, hanchor, rfl⟩
  let B : O := ⟨a.tile, a, ha, rfl⟩
  have hlisted : ∀ C : O, C.val.Lists 0 q := by
    rintro ⟨C, a, ha, rfl⟩
    exact site_fan_finite_step5_listed q hq a ha
  exact site_fan_finite_step8_reachable (siteFanGraph q)
    (fun C : O => C.val.frame) D M (hM A F r q).2
    (fun C B hCB => hstep B.val C.val q (hlisted B) (hlisted C)
      (by obtain ⟨F, G, hFG⟩ := hCB.2; exact ⟨G, F, fun i => (hFG i).symm⟩))
    (site_fan_finite_step6_connected q hq C B)

/-- Step 10 of the V4 proof of `site_fan_finite` (V4 1.23(b)):
"with their chains". Vertex names and every optional coface name range
over a finite alphabet from the finite prototype complexes. -/
private theorem site_fan_finite_step10_labels (S : SubstSystem d) :
    ∃ L : Set (Cell d × (Fin d → Option (Cell d))), L.Finite ∧
      ∀ (A : S.ι) (F : FacetFlag S A) (r : ℕ) (a : TracePiece A F r)
        (v : Cell d), v ∈ (S.cx a.tile.ty).vertices → (v, a.chainNames) ∈ L := by
  classical
  let C : Set (Cell d) := ⋃ A : S.ι, (S.cx A).cells
  have hC : C.Finite := Set.finite_iUnion (fun A => (S.cx A).cells.finite_toSet)
  let L : Set (Fin d → Option (Cell d)) :=
    {c | ∀ i, c i ∈ insert none (some '' C)}
  have hL : L.Finite := Set.Finite.pi' (fun _ => (hC.image some).insert none)
  refine ⟨C ×ˢ L, hC.prod hL, ?_⟩
  intro A F r a v hv
  constructor
  · exact Set.mem_iUnion.mpr ⟨a.tile.ty, (Finset.mem_filter.mp hv).1⟩
  · intro i
    change a.chainNames i ∈ insert none (some '' C)
    unfold TracePiece.chainNames
    split_ifs with hi
    · exact Set.mem_insert_of_mem _ ⟨(a.chain.cell ⟨i, hi⟩).val,
        Set.mem_iUnion.mpr ⟨a.tile.ty, (a.chain.cell ⟨i, hi⟩).property⟩, rfl⟩
    · exact Set.mem_insert _ _

/-- P18, V4 1.23(b): finitely many positioned selected-owner fan templates. -/
theorem site_fan_finite (S : SubstSystem d) : (siteTemplates S).Finite := by
  obtain ⟨K, hK, hframes⟩ := site_fan_finite_step9_frames S
  obtain ⟨L, hL, hlabels⟩ := site_fan_finite_step10_labels S
  let V := {p : E d | ∃ A : S.ι, ∃ v ∈ (S.cx A).vertices, p ∈ v.carrier}
  have hV : V.Finite := site_fan_finite_step1_vertices S
  let N : Set (FramedNode S) := (fun z : S.ι × Iso d => ⟨z.1, z.2⟩) '' (Set.univ ×ˢ K)
  have hN : N.Finite := (Set.finite_univ.prod hK).image _
  apply (hV.prod (hN.prod hL).powerset).subset
  rintro t ⟨A, F, r, q, anchor, hq, hanchor, rfl⟩
  constructor
  · exact site_fan_finite_step4_listed_coordinate anchor.tile q
      (site_fan_finite_step5_listed q hq anchor hanchor)
  · rintro z ⟨a, v, ha, hv, hqv, rfl⟩
    constructor
    · exact ⟨(a.tile.ty, a.tile.frame.trans anchor.tile.frame.symm),
        ⟨Set.mem_univ _, hframes A F r q hq anchor a hanchor ha⟩, rfl⟩
    · exact hlabels A F r a v hv

/-- P18, V4 1.23(b): the actual trace pieces at a site form a finite fan:
their direction cones cover the outer half-plane (half-line when `d=2`) and have
disjoint relative interiors. Their number has one uniform bound over all depths. -/
theorem site_fan_geometry (S : SubstSystem d) :
    ∃ M : ℕ, ∀ (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d),
      IsSite A F r q →
      Nat.card {a : TracePiece A F r // q ∈ a.carrier} ≤ M ∧
      (⋃ a : {a : TracePiece A F r // q ∈ a.carrier},
        tangentCone a.val.carrier q) =
        tangentCone ((S.σ ^ r) '' (F.cell ⟨traceDimension d, traceDimension_pos,
          traceDimension_lt⟩).val.carrier) q ∧
      Pairwise (fun a b : {a : TracePiece A F r // q ∈ a.carrier} =>
        Disjoint (relint (tangentCone a.val.carrier q))
          (relint (tangentCone b.val.carrier q))) := by
  sorry

/-- P18, V4 1.23(c): every deeper trace polygon meeting a fixed site lists it,
as does its selected owner. Native-scale positions are compared by `σˢ`. -/
theorem site_listed (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d)
    (hq : IsSite A F r q) (s : ℕ) (a : TracePiece A F (r + s))
    (ha : (S.σ ^ s) q ∈ a.carrier) :
    ∃ v ∈ (S.cx a.tile.ty).vertices,
      (S.σ ^ s) q ∈ a.tile.cell 0 v ∧ a.tile.cell 0 v ⊆ a.carrier := by
  sorry

/-- P18, V4 1.23(a),(c): an ordinary site persists at every deeper subdivision. -/
theorem site_persists (A : S.ι) (F : FacetFlag S A) (r : ℕ) (q : E d)
    (hq : IsSite A F r q) (s : ℕ) : IsSite A F (r + s) ((S.σ ^ s) q) := by
  sorry

/-- P17/P18, V4 1.22--1.23: the scale normalization from a native-scale
height-`r` root to the depth-`r` subdivision of a placed height-`n` node.
Applications below require `r ≤ n`; the linear part need not be a similarity. -/
def tracePlacement (N : FramedNode S) (n r : ℕ) : E d ≃ᵃ[ℝ] E d :=
  (S.σ ^ (n - r)).toAffineEquiv.trans N.frame.toAffineEquiv

/-- P17, V4 1.22(a): the actual height-`n-r` owner of a placed trace piece,
with the exact role word and recursive hierarchy frame. -/
def placedTraceOwner (N : FramedNode S) (n r : ℕ) (F : FacetFlag S N.ty)
    (a : TracePiece N.ty F r) : FramedNode S :=
  (S.descendantNode N.ty (n - r) r a.owner).move N.frame

/-- P17, V4 1.22(a): placed trace polygon or edge, retaining its native-scale
owner and chain as the index rather than making fresh geometric choices. -/
def placedTraceCarrier (N : FramedNode S) (n r : ℕ) (F : FacetFlag S N.ty)
    (a : TracePiece N.ty F r) : Set (E d) := tracePlacement N n r '' a.carrier

/-- P17, V4 1.22(a): every recorded named cell is carried to the corresponding
cell of the actual owner node, at its actual height. -/
theorem placedTraceOwner_cells (N : FramedNode S) (n r : ℕ) (hr : r ≤ n)
    (F : FacetFlag S N.ty) (a : TracePiece N.ty F r) (e : Cell d) :
    (placedTraceOwner N n r F a).cell (n - r) e =
      tracePlacement N n r '' (a.tile.cell 0 e) := by
  sorry

/-- P17, V4 1.22(a): recursive traces tile the prescribed cell of every placed
node, with disjoint relative interiors, for every permitted subdivision depth. -/
theorem placed_recursiveTrace_tiles (N : FramedNode S) (n r : ℕ) (hr : r ≤ n)
    (F : FacetFlag S N.ty) :
    (⋃ a : TracePiece N.ty F r, placedTraceCarrier N n r F a) =
      N.cell n (F.cell ⟨traceDimension d, traceDimension_pos, traceDimension_lt⟩).val ∧
    Pairwise (fun a b : TracePiece N.ty F r =>
      Disjoint (relint (placedTraceCarrier N n r F a))
        (relint (placedTraceCarrier N n r F b))) := by
  sorry

/-- P17, V4 1.22(a): a selected trace owner is an actual node of the fixed
coherent hierarchy, rather than merely a congruent tile in an unrelated source. -/
theorem CoherentHierarchy.placedTraceOwner_mem {T : Tiling S}
    (H : CoherentHierarchy S T) (N : FramedNode S) (n r : ℕ)
    (hN : N ∈ H.nodes n) (hr : r ≤ n) (F : FacetFlag S N.ty)
    (a : TracePiece N.ty F r) : placedTraceOwner N n r F a ∈ H.nodes (n - r) := by
  sorry

/-- P18, V4 1.23(c): persistence in one placed source node, at every deeper
subdivision still available in that node. The same ambient point is used at each
depth; scale normalization changes the native coordinates, not the point itself. -/
theorem placed_site_listed (N : FramedNode S) (n r r' : ℕ)
    (hrr' : r ≤ r') (hr'n : r' ≤ n) (F : FacetFlag S N.ty) (q : E d)
    (hq : IsSite N.ty F r q) (a : TracePiece N.ty F r')
    (ha : tracePlacement N n r q ∈ placedTraceCarrier N n r' F a) :
    (placedTraceOwner N n r' F a).Lists (n - r') (tracePlacement N n r q) := by
  sorry

end Enforce
