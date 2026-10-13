import Tilings.Control.Composition
import Tilings.Alignment

/-!
# The strict variant of the control chapter (statements)

Blueprint: `main.tex`, `lem:schedule-compose` ("In the strict variant replace generated outer
fourth ranks by tagged `W` ... This repeats the finite control proof with a different
generated field; it does not claim the two decorated substitutions are the same function"),
`lem:strict-presentation`, `lem:strict-complete`, and the control chapter `composition.tex`,
whose finite proof is repeated here without the hereditary-sides hypothesis.

* Alphabet.  `SchedTag C hC` is the finite set of schedule values `W(α, e)`
  (`def:endpoint-schedule`: the tag is the geometric value, so different forms with equal
  data share a tag).  The strict alphabet `SU C hC` has disjoint tags for zero, schedules
  (in place of the positive ranks of the flexible `OrdIndex`), type labels, interface
  identities, `⊥` and headers.
* Tiles and the child rule.  `StrictDecTile`, the generated child `strictChild` (the repaired
  child rule of `def:control/substitution`, with the outer fourth cell replaced by the
  schedule tag of the child side; a copied cell takes the value of its `copySource`),
  `StrictLegal` (`def:control/legal`; origins are the flexible `HasOrigin` of the chain of
  types) and `IsStrictNormal` (the outer fourth cell is local).
* The decoration.  `strictDecoration C hC : SideDecoration C.Q`, `strictSubst C hC`, and the
  strict schedule system `strictSystem C hC`.  A legal typed tile is coloured by its full
  five-tuple; an illegal typed tile and an inert form `root α` (needed because the projection
  of a `SideDecoration` must be surjective, and `C.form` need not be) carry the fresh colour of
  the owner-side incidence (the inert-decoration device of `lem:glues`), so they never occur in
  a proper plane tiling: `(strictDecoration C hC).Proper` is strict matching of legal typed
  tiles (`strict_proper_iff`).
* Strict analogues of the composition chapter: assembly, common boundary header,
  reconstruction, signals, exactness, the cyclic / noncentral / acyclic legality cases,
  composed properness and the composition theorem `strict_compose_exists`.  The rank
  alignment lemma is replaced by `strict_opposing_macroside` (schedule alignment
  `lem:alignment-tuple` and whole-side ports `lem:whole-ports`).
* Completeness (`lem:strict-presentation`): `strict_actual_schedules_aligned`,
  `strict_lift_decorations`, `strict_lift_matched`, `strict_lift_hierarchy`.
* The conclusions of `lem:strict-presentation` for `strictSystem` and the bridge
  `exists_strict_schedule_system_of_certificate`.  The side-to-side dissections come from the
  clause `inside_supertile` of `C.Represents τ m` (every group lies, up to translation, in a
  supertile); STS of `Δ α` with `τ.STS` alone does not imply them.

Reuse of the flexible chapter.  Certificate notions, `copySource`, `HasOrigin` (through the
type shadow `typeShadow`), `IsLocal`, `taggedEquiv` and the header kernel are reused.  The
flexible alphabet `U c`, and with it `DecTile`, `IsChildOfWith` (whose outer clause is the
zero/rank rule), `IsNormal`, `headerLegal`, `ColouredBlock` and the composition statements, is
hard-wired to ranks, so strict copies of the same shape are defined here.

Definitions are real and `sorry`-free; all fields of `strictSystem` are proved.  Also proved:
`strictChild_cells` (the strict child satisfies the clauses of `IsChildOfWith` with the
schedule clause), `exists_boundary_side_of_outer`, `strict_proper_iff` (modulo the planar
lemma `exists_coincident_side`), `Substitution.STS.decomposeIter_sts_of_subset_supertile` and
the final assemblies.  Theorems proved by `sorry` are proof targets.
-/

open Set Pointwise

noncomputable section

namespace Tilings

namespace Planned

namespace Strict

open Geometry

variable {P : Protoset} {τ : Substitution P} {m : ℕ}

/-! ## The strict alphabet -/

section Alphabet

variable (C : MacroCertificate P) (hC : C.Represents τ m)

/-- The tagged endpoint schedule `W(α, e)` (`def:endpoint-schedule`) of a side occurrence `o`
of the template `σ' α`, `α = owner o`: the layered schedule of the segment of `o` (a whole
fine outer side of `α` when `o` is outer) at the power `m` of the representation. -/
def schedOf (o : C.SideOcc) : Alignment.LayerTag m → Set (ℝ × ℝ × ℝ × ℝ) :=
  Alignment.EndpointSchedule τ hC.groupedFamily m (C.owner o.1) (C.occStart o, C.occEnd o)

/-- The finite alphabet of schedule tags: the schedule values that occur.  A tag is the value
itself, not the occurrence. -/
abbrev SchedTag : Type := Set.range (schedOf C hC)

noncomputable instance instFintypeSchedTag : Fintype (SchedTag C hC) := by
  classical exact Set.fintypeRange _

noncomputable instance instDecEqSchedTag : DecidableEq (SchedTag C hC) := Classical.decEq _

/-- The ordinary strict index tags: schedule tags (in place of the positive ranks of the
flexible `OrdIndex`), type labels, exact interface identities, and `⊥`. -/
abbrev StrictOrdIndex : Type := SchedTag C hC ⊕ (C.Typ ⊕ (C.EdgeId ⊕ Unit))

/-- The finite tagged strict alphabet (`lem:schedule-compose`: disjoint tags for schedules,
headers, identities, zero and `⊥`). -/
abbrev SU : Type := HeaderKernel.TaggedIndex C.Typ C.Side (StrictOrdIndex C hC)

noncomputable instance instFintypeSU : Fintype (SU C hC) :=
  Fintype.ofEquiv _ (taggedEquiv C.Typ C.Side (StrictOrdIndex C hC)).symm

noncomputable instance instDecEqSU : DecidableEq (SU C hC) := Classical.decEq _

/-- The schedule tag of a side occurrence. -/
def schedU (o : C.SideOcc) : SU C hC := .ordinary (Sum.inl ⟨schedOf C hC o, o, rfl⟩)

/-- A type label. -/
def typeSU (t : C.Typ) : SU C hC := .ordinary (Sum.inr (Sum.inl t))

/-- An exact interface identity `(s, r, e)`, named by its edge `e`. -/
def identSU (e : C.EdgeId) : SU C hC := .ordinary (Sum.inr (Sum.inr (Sum.inl e)))

/-- The symbol `⊥`. -/
def botSU : SU C hC := .ordinary (Sum.inr (Sum.inr (Sum.inr ())))

/-- A header value. -/
def headerSU (h : HeaderKernel.Header C.Typ C.Side) : SU C hC := .header h

/-- The schedule value carried by an index, if it is a schedule tag. -/
def readSched : SU C hC → Option (Alignment.LayerTag m → Set (ℝ × ℝ × ℝ × ℝ))
  | .ordinary (Sum.inl w) => some w.1
  | _ => none

end Alphabet

/-! ## Strict decorated tiles, the strict child rule, legality -/

section Tiles

variable (C : MacroCertificate P) (hC : C.Represents τ m)

/-- A strict decorated tile (`def:control/typed-decoration`, strict variant): the type (stored
in the centre) and a five-tuple in the strict alphabet on every listed side. -/
structure StrictDecTile where
  typ : C.Typ
  cell : C.Side typ → Fin 5 → SU C hC

/-- Strict decorated tiles as a sigma type. -/
def strictDecTileEquiv : StrictDecTile C hC ≃ Σ t : C.Typ, (C.Side t → Fin 5 → SU C hC) where
  toFun A := ⟨A.typ, A.cell⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instFintypeStrictDecTile : Fintype (StrictDecTile C hC) :=
  Fintype.ofEquiv _ (strictDecTileEquiv C hC).symm

noncomputable instance instDecEqStrictDecTile : DecidableEq (StrictDecTile C hC) :=
  Classical.decEq _

/-- The header `H(A) = ⟨t, z_{t,a}⟩` of a strict tile (`def:control/header`), computed by the
compiled kernel from its type and fourth vector.  For a legal tile every outer fourth cell is
a schedule tag, so the zero mode is identically false. -/
def strictHeaderOf (A : StrictDecTile C hC) : HeaderKernel.Header C.Typ C.Side :=
  HeaderKernel.makeHeader C.outerB A.typ (fun d => A.cell d 3)

open Classical in
/-- The generated (origin) value of the cell `k` on the side occurrence `o` of a child of a
parent of form `α` with header `hdr` (`def:control/substitution`, strict variant): on a print
the interface identity in position 5; on a nonprint side the prescribed first identity (zero
on an outer side), zero second, third and fifth cells, and as fourth cell **the schedule tag
`W(α, o)` on an outer side**, the parent header on a boundary side and `⊥` on every other
inner side.  Copied cells are overridden in `strictGen`. -/
def strictGenCell (α : C.Q.Form) (hdr : SU C hC) (o : C.SideOcc) (k : Fin 5) : SU C hC :=
  if ∃ d, C.IsPrintOf α d o then (if k = 4 then identSU C hC (C.edge o) else 0)
  else if k = 0 then (if C.IsInner o then identSU C hC (C.edge o) else 0)
  else if k = 3 then
    (if C.IsOuter o then schedU C hC o else if C.IsBoundary o then hdr else botSU C hC)
  else 0

open Classical in
/-- The child of type `t` generated by the parent data `(α, pc, hdr)` (parent form, parent
cells, parent header): a copied cell (nonempty `copySource`: positions 1–4 of a print, the
third cell of a path side; by (G4) the source is unique) takes the value of its source cell,
every other cell is an origin and takes its generated value `strictGenCell`. -/
def strictGen (α : C.Q.Form) (pc : Fin (C.Q.disk α).n → Fin 5 → SU C hC) (hdr : SU C hC)
    (t : C.Typ) : StrictDecTile C hC where
  typ := t
  cell i k :=
    if h : (copySource C α (C.occ t i) k).Nonempty then pc h.some.1 h.some.2
    else strictGenCell C hC α hdr (C.occ t i) k

/-- **The strict child** of type `t` of a decorated parent `A` (`def:control/substitution` with
the generated outer fourth rank replaced by the tagged schedule, `lem:schedule-compose`); the
boundary clause carries the full parent header. -/
def strictChild (A : StrictDecTile C hC) (t : C.Typ) : StrictDecTile C hC :=
  strictGen C hC (C.form A.typ) A.cell (headerSU C hC (strictHeaderOf C hC A)) t

/-- `B` is a child of `A` in the strict decorated substitution: its type lies in the template
of the form of `A`, and its colours are the ones generated from `A`. -/
def IsStrictChildOf (A B : StrictDecTile C hC) : Prop :=
  C.owner B.typ = C.form A.typ ∧ B = strictChild C hC A B.typ

/-- The flexible decorated tile with the type of `A` and zero cells.  Copy sources and origins
depend only on types. -/
def typeShadow (A : StrictDecTile C hC) : DecTile C := ⟨A.typ, fun _ _ => 0⟩

/-- Origins along a strict ancestor chain (`def:control/origin`): the flexible `HasOrigin` of
the chain of types.  Schedule tags, headers and fixed cells are generated origins. -/
def StrictHasOrigin (ch : ℕ → StrictDecTile C hC) (n : ℕ) (i : C.Side (ch n).typ)
    (k : Fin 5) : Prop :=
  HasOrigin C (fun l => typeShadow C hC (ch l)) n i k

/-- **Strict legality** (`def:control/legal`, strict variant): an infinite ancestor chain under
the strict substitution in which every copied cell with no origin is zero. -/
def StrictLegal (A : StrictDecTile C hC) : Prop :=
  ∃ ch : ℕ → StrictDecTile C hC, ch 0 = A ∧ (∀ n, IsStrictChildOf C hC (ch (n + 1)) (ch n)) ∧
    ∀ (n : ℕ) (i : C.Side (ch n).typ) (k : Fin 5),
      (copySource C (C.form (ch (n + 1)).typ) (C.occ (ch n).typ i) k).Nonempty →
      ¬ StrictHasOrigin C hC ch n i k → (ch n).cell i k = 0

/-- The strict local cells: the local cells of the flexible variant (`IsLocal`) and the fourth
cell of an outer side, which is the generated schedule and thus fixed by the type
(`def:control/typed-decoration`). -/
def IsStrictLocal (o : C.SideOcc) (k : Fin 5) : Prop := IsLocal C o k ∨ (C.IsOuter o ∧ k = 3)

open Classical in
/-- The type-determined value of a strict local cell: as `prescribedCell`, except that the
fourth cell of an outer side is its schedule tag. -/
def strictPrescribedCell (o : C.SideOcc) (k : Fin 5) : SU C hC :=
  if k = 0 then (if C.IsInner o then identSU C hC (C.edge o) else 0)
  else if k = 3 then
    (if C.IsOuter o then schedU C hC o
      else if C.IsInner o ∧ ¬ C.IsBoundary o ∧ ¬ C.IsPrint o then botSU C hC else 0)
  else if k = 4 then (if C.IsPrint o then identSU C hC (C.edge o) else 0)
  else 0

/-- **Strict normality**: every strict local cell has its prescribed value. -/
def IsStrictNormal (A : StrictDecTile C hC) : Prop :=
  ∀ (i : C.Side A.typ) (k : Fin 5), IsStrictLocal C (C.occ A.typ i) k →
    A.cell i k = strictPrescribedCell C hC (C.occ A.typ i) k

/-- **Identity-correctness** (strict alphabet): every inner nonprint side carries its identity
in position 1, every print in position 5. -/
def IsStrictIdentityCorrect (A : StrictDecTile C hC) : Prop :=
  ∀ i : C.Side A.typ,
    (C.IsInner (C.occ A.typ i) → ¬ C.IsPrint (C.occ A.typ i) →
      A.cell i 0 = identSU C hC (C.edge (C.occ A.typ i))) ∧
    (C.IsPrint (C.occ A.typ i) → A.cell i 4 = identSU C hC (C.edge (C.occ A.typ i)))

end Tiles

/-! ## The strict typed side decoration and the strict substitution -/

section Decoration

variable (C : MacroCertificate P) (hC : C.Represents τ m)

/-- The forms of the strict decoration: typed decorated tiles, and one inert form `root α`
for every grouped form `α` (surjectivity of the projection). -/
inductive StrictForm where
  | typed (A : StrictDecTile C hC)
  | root (α : C.Q.Form)

/-- Strict forms as a sum type. -/
def strictFormEquiv : StrictForm C hC ≃ StrictDecTile C hC ⊕ C.Q.Form where
  toFun q := match q with
    | .typed A => Sum.inl A
    | .root α => Sum.inr α
  invFun x := match x with
    | Sum.inl A => .typed A
    | Sum.inr α => .root α
  left_inv q := by cases q <;> rfl
  right_inv x := by cases x <;> rfl

noncomputable instance instFintypeStrictForm : Fintype (StrictForm C hC) :=
  Fintype.ofEquiv _ (strictFormEquiv C hC).symm

noncomputable instance instDecEqStrictForm : DecidableEq (StrictForm C hC) :=
  Classical.decEq _

variable {C hC} in
/-- The grouped form underlying a strict form. -/
def StrictForm.proj : StrictForm C hC → C.Q.Form
  | .typed A => C.form A.typ
  | .root α => α

variable {C hC} in
/-- A strict form is legal if it is a typed form with a legal decorated tile; inert root forms
are never legal. -/
def StrictForm.IsLegal : StrictForm C hC → Prop
  | .typed A => StrictLegal C hC A
  | .root _ => False

/-- The strict typed protoset: the polygon of a typed tile of type `t` is that of `form t`,
the polygon of `root α` is that of `α`. -/
abbrev strictProtoset : Protoset where
  Form := StrictForm C hC
  disk q := C.Q.disk q.proj

/-- Side colours of the strict decoration: a five-tuple, or a fresh owner-side incidence. -/
abbrev StrictColour : Type :=
  (Fin 5 → SU C hC) ⊕ (Σ q : StrictForm C hC, Fin (C.Q.disk q.proj).n)

open Classical in
/-- Side colours: a legal typed tile carries its full five-tuple; an illegal typed tile and an
inert root form carry the fresh colour of the owner-side incidence (`lem:glues`: its only
possible matching incidence would force coincident interiors). -/
def strictColour : (q : StrictForm C hC) → Fin (C.Q.disk q.proj).n → StrictColour C hC
  | .typed A, i => if StrictLegal C hC A then Sum.inl (A.cell i) else Sum.inr ⟨.typed A, i⟩
  | .root α, i => Sum.inr ⟨.root α, i⟩

/-- **The strict typed side decoration** (`lem:strict-presentation`; the strict variant of
`def:control/typed-decoration` with second component zero, exact disks, schedule tags in the
outer fourth cells and strict matching of full five-tuples). -/
def strictDecoration : SideDecoration C.Q where
  P' := strictProtoset C hC
  proj := StrictForm.proj
  surj α := ⟨.root α, rfl⟩
  carrier_eq _ := rfl
  disk_eq _ := rfl
  Colour := StrictColour C hC
  colour := strictColour C hC

/-- The children generated by the parent data `(α, pc, hdr)`: for every child type `t` of the
template `σ' α`, the generated decorated child placed at `anchor t`. -/
def strictChildren (α : C.Q.Form) (pc : Fin (C.Q.disk α).n → Fin 5 → SU C hC)
    (hdr : SU C hC) : Set (PlacedTile (strictProtoset C hC)) :=
  (fun t => (⟨StrictForm.typed (strictGen C hC α pc hdr t), C.anchor t⟩ :
    PlacedTile (strictProtoset C hC))) '' {t | C.owner t = α}

theorem projTile_strictChildren (α : C.Q.Form) (pc : Fin (C.Q.disk α).n → Fin 5 → SU C hC)
    (hdr : SU C hC) :
    (strictDecoration C hC).toDecoration.projTile '' strictChildren C hC α pc hdr =
      (C.σ.rule α).tiles := by
  rw [C.rule_eq α, strictChildren, Set.image_image]
  rfl

theorem strictChildren_finite (α : C.Q.Form) (pc : Fin (C.Q.disk α).n → Fin 5 → SU C hC)
    (hdr : SU C hC) : (strictChildren C hC α pc hdr).Finite :=
  (Set.toFinite _).image _

theorem strictChildren_support (α : C.Q.Form) (pc : Fin (C.Q.disk α).n → Fin 5 → SU C hC)
    (hdr : SU C hC) :
    support (strictChildren C hC α pc hdr) = C.σ.θ • (C.Q.disk α).carrier := by
  rw [← C.σ.support_eq α, ← projTile_strictChildren C hC α pc hdr]
  simp only [support, Set.biUnion_image]
  rfl

theorem strictChildren_disjoint (α : C.Q.Form) (pc : Fin (C.Q.disk α).n → Fin 5 → SU C hC)
    (hdr : SU C hC) : DisjointInteriors (strictChildren C hC α pc hdr) := by
  have hmem : ∀ s, C.owner s = α →
      (⟨C.form s, C.anchor s⟩ : PlacedTile C.Q) ∈ (C.σ.rule α).tiles :=
    fun s hs => by rw [C.rule_eq α]; exact ⟨s, hs, rfl⟩
  have hc : ∀ s, (⟨StrictForm.typed (strictGen C hC α pc hdr s), C.anchor s⟩ :
      PlacedTile (strictProtoset C hC)).carrier =
        (⟨C.form s, C.anchor s⟩ : PlacedTile C.Q).carrier := fun _ => rfl
  intro X hX Y hY hXY
  obtain ⟨t, ht, rfl⟩ := hX
  obtain ⟨t', ht', rfl⟩ := hY
  have htt : t ≠ t' := by rintro rfl; exact hXY rfl
  have hne : (⟨C.form t, C.anchor t⟩ : PlacedTile C.Q) ≠ ⟨C.form t', C.anchor t'⟩ := by
    intro h
    injection h with h1 h2
    exact htt (C.type_injective t t' (ht.trans ht'.symm) h1 h2)
  have hd := (C.σ.rule α).disjoint (hmem t ht) (hmem t' ht') hne
  show Disjoint (interior (PlacedTile.carrier _)) (interior (PlacedTile.carrier _))
  rw [hc t, hc t']
  exact hd

/-- The patch of children generated by the parent data `(α, pc, hdr)`. -/
def strictChildPatch (α : C.Q.Form) (pc : Fin (C.Q.disk α).n → Fin 5 → SU C hC)
    (hdr : SU C hC) : Patch (strictProtoset C hC) where
  tiles := strictChildren C hC α pc hdr
  finite := strictChildren_finite C hC α pc hdr
  disjoint := strictChildren_disjoint C hC α pc hdr

variable {C hC} in
/-- The parent cells used to decompose a strict form (zero for an inert root form). -/
def StrictForm.parentCells : (q : StrictForm C hC) → Fin (C.Q.disk q.proj).n → Fin 5 → SU C hC
  | .typed A => A.cell
  | .root _ => fun _ _ => 0

variable {C hC} in
/-- The parent header used to decompose a strict form (zero for an inert root form). -/
def StrictForm.parentHeader : StrictForm C hC → SU C hC
  | .typed A => headerSU C hC (strictHeaderOf C hC A)
  | .root _ => 0

/-- **The strict coloured substitution** (`def:control/substitution`, strict variant): a typed
tile decomposes into its strict children (`strictChild`); an inert root form decomposes into
the children generated from zero data, which are inert unless legal. -/
def strictSubst : Substitution (strictProtoset C hC) where
  θ := C.σ.θ
  one_lt := C.σ.one_lt
  rule q := strictChildPatch C hC q.proj q.parentCells q.parentHeader
  support_eq q := strictChildren_support C hC q.proj q.parentCells q.parentHeader

/-! ### Schedules read off the colours -/

variable {C hC} in
/-- The schedule field of an inert colour `⟨q, i⟩`. -/
def inertSched : (q : StrictForm C hC) → Fin (C.Q.disk q.proj).n →
    Option (Alignment.LayerTag m → Set (ℝ × ℝ × ℝ × ℝ))
  | .typed A, i => readSched C hC (A.cell i 3)
  | .root _, _ => none

/-- The schedule field carried by a colour: the schedule tag in the fourth cell. -/
def colourSched : StrictColour C hC → Option (Alignment.LayerTag m → Set (ℝ × ℝ × ℝ × ℝ))
  | Sum.inl c => readSched C hC (c 3)
  | Sum.inr x => inertSched x.1 x.2

/-- The outer schedule field of a strict form, read off its side colour (so equal colours
force equal schedule fields). -/
def strictOuterSchedule (q : StrictForm C hC) (i : Fin (C.Q.disk q.proj).n) :
    Option (Alignment.LayerTag m → Set (ℝ × ℝ × ℝ × ℝ)) :=
  colourSched C hC (strictColour C hC q i)

theorem strictOuterSchedule_typed (A : StrictDecTile C hC) (i : C.Side A.typ) :
    strictOuterSchedule C hC (.typed A) i = readSched C hC (A.cell i 3) := by
  simp only [strictOuterSchedule, strictColour]
  split_ifs <;> rfl

/-- The partner of an inner side is inner. -/
private theorem isInner_partner {o : C.SideOcc} (h : C.IsInner o) : C.IsInner (C.partner o) := by
  have hp := C.g1_partner _ h
  unfold MacroData.IsInner MacroData.IsOuter at h ⊢
  rw [hp.2.2, hp.2.1]
  exact h

/-- Prints are inner sides. -/
private theorem isInner_of_isPrintOf {α : C.Q.Form} {d : Fin (C.Q.disk α).n} {o : C.SideOcc}
    (h : C.IsPrintOf α d o) : C.IsInner o := by
  rcases h with ⟨hm, rfl | rfl⟩
  · exact C.g4_print_inner α d hm
  · exact isInner_partner C (C.g4_print_inner α d hm)

/-- The printed parent side of a print is unique ((G1), (G4)). -/
private theorem isPrintOf_unique {α : C.Q.Form} {d d' : Fin (C.Q.disk α).n} {o : C.SideOcc}
    (h : C.IsPrintOf α d o) (h' : C.IsPrintOf α d' o) : d = d' := by
  have key : ∀ {e e' : Fin (C.Q.disk α).n}, C.marked α e → C.marked α e' →
      C.printOcc α e = C.printOcc α e' → e = e' := by
    intro e e' he he' hpe
    apply C.g4_print_injective α e e' he he'
    simp only [MacroData.printOcc, Sigma.mk.injEq, heq_eq_eq, true_and] at hpe
    exact hpe
  obtain ⟨hm, h1⟩ := h
  obtain ⟨hm', h2⟩ := h'
  have hin := C.g4_print_inner α d hm
  have hin' := C.g4_print_inner α d' hm'
  rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2
  · exact key hm hm' h2
  · exact absurd (by rw [← h2]; rfl) (C.g1_partner _ hin').1
  · exact absurd (by rw [h2]; rfl) (C.g1_partner _ hin).1
  · exact key hm hm' (by
      rw [← C.g1_partner_partner _ hin, h2, C.g1_partner_partner _ hin'])

/-- A nonprint side lies on at most one path of its template ((G4)). -/
private theorem path_source_unique {α : C.Q.Form} {o : C.SideOcc} (hα : C.owner o.1 = α)
    (hnp : ¬ C.IsPrint o) {d d' : Fin (C.Q.disk α).n} {j j' : Fin 5}
    (h : o ∈ C.path α d j) (h' : o ∈ C.path α d' j') : d = d' ∧ j = j' := by
  by_contra hne
  have hne' : (d, j) ≠ (d', j') := fun e => hne (Prod.mk.inj e)
  obtain ⟨rfl, hpr⟩ := C.g4_path_disjoint α d d' j j' hne' o h h'
  by_cases hm : C.marked α d
  · apply hnp
    unfold MacroData.IsPrint
    rw [hα]
    exact ⟨d, hm, hpr⟩
  · have htriv := C.g4_path_trivial α d j (fun hg => hm hg.1)
    rw [htriv, Option.mem_toList] at h
    have hmem : o ∈ C.outerList α d := List.mem_iff_getElem?.mpr ⟨_, h⟩
    have hout : C.IsOuter o := ((C.g3_outerList_mem α d o).1 hmem).2.1
    have hin : C.IsInner (C.printOcc α d) := (C.g2_central α (C.print α d)).1
    rcases hpr with rfl | rfl
    · exact hin hout
    · exact isInner_partner C hin hout

/-- The coloured rules project onto the grouped templates (`rule_proj`). -/
theorem strictSubst_rule_proj (q : StrictForm C hC) :
    (strictDecoration C hC).toDecoration.projTile '' ((strictSubst C hC).rule q).tiles =
      (C.σ.rule ((strictDecoration C hC).proj q)).tiles :=
  projTile_strictChildren C hC _ _ _

/-- Every outer side of a child of a coloured template carries the schedule `W(A, e)` of its
parent (`schedule_spec`). -/
theorem strictSubst_schedule_spec (q : StrictForm C hC) :
    ∀ X ∈ ((strictSubst C hC).rule q).tiles, ∀ i : Fin ((strictProtoset C hC).disk X.form).n,
      X.side i ⊆ frontier ((strictSubst C hC).θ • ((strictProtoset C hC).disk q).carrier) →
      strictOuterSchedule C hC X.form i =
        some (Alignment.EndpointSchedule τ hC.groupedFamily m q.proj
          (X.vertex i, X.vertex (finRotate _ i))) := by
  rintro X ⟨t, ht, rfl⟩ i hi
  have ht' : C.owner t = q.proj := ht
  have hout : C.IsOuter (C.occ t i) := by
    show C.occSide (C.occ t i) ⊆ C.macroBoundary (C.owner t)
    rw [ht']
    exact hi
  have hnp : ¬ ∃ d, C.IsPrintOf q.proj d (C.occ t i) := fun ⟨_, hd⟩ =>
    isInner_of_isPrintOf C hd hout
  have hcs : ¬ (copySource C q.proj (C.occ t i) 3).Nonempty := by
    rintro ⟨p, hp | hp⟩
    · exact hnp ⟨p.1, hp.1⟩
    · exact absurd hp.2.1 (by decide)
  have hcell : (strictGen C hC q.proj q.parentCells q.parentHeader t).cell i 3 =
      schedU C hC (C.occ t i) := by
    simp only [strictGen, dif_neg hcs, strictGenCell, if_neg hnp,
      if_neg (show (3 : Fin 5) ≠ 0 by decide), if_pos hout, ite_true]
  rw [strictOuterSchedule_typed, hcell]
  show some (Alignment.EndpointSchedule τ hC.groupedFamily m (C.owner t) _) = _
  rw [ht']
  rfl

/-- **The strict schedule system of a representing certificate** (`lem:strict-presentation`):
the grouped substitution of `hC`, the strict typed side decoration, the strict coloured
substitution, and the schedule fields read off the fourth cells of the colours. -/
def strictSystem : Alignment.StrictScheduleSystem τ where
  GS := hC.groupedSubstitution
  dec := strictDecoration C hC
  σc := strictSubst C hC
  θ_eq := rfl
  rule_proj := strictSubst_rule_proj C hC
  outerSchedule := strictOuterSchedule C hC
  schedule_spec := strictSubst_schedule_spec C hC
  schedule_colour _ _ _ _ h := congrArg (colourSched C hC) h

/-! ### Strict matching and legal tilings -/

/-- Every tile of `T` is a legal typed tile. -/
def AllStrictLegal (T : PlaneTiling (strictProtoset C hC)) : Prop :=
  ∀ X ∈ T.tiles, StrictForm.IsLegal X.form

/-- **Strict matching** (the strict properness rule on cells, without legality): the tiling is
side-to-side, and coincident sides of two distinct typed tiles carry equal five-tuples. -/
def IsStrictMatched (T : PlaneTiling (strictProtoset C hC)) : Prop :=
  T.SideToSide ∧
    ∀ (A B : StrictDecTile C hC) (v w : Pt),
      (⟨.typed A, v⟩ : PlacedTile (strictProtoset C hC)) ∈ T.tiles →
      (⟨.typed B, w⟩ : PlacedTile (strictProtoset C hC)) ∈ T.tiles →
      (⟨.typed A, v⟩ : PlacedTile (strictProtoset C hC)) ≠ ⟨.typed B, w⟩ →
      ∀ (i : C.Side A.typ) (j : C.Side B.typ),
        v +ᵥ (C.Q.disk (C.form A.typ)).side i = w +ᵥ (C.Q.disk (C.form B.typ)).side j →
        A.cell i = B.cell j

theorem strictColour_of_not_isLegal (q : StrictForm C hC) (hq : ¬ q.IsLegal)
    (i : Fin (C.Q.disk q.proj).n) : strictColour C hC q i = Sum.inr ⟨q, i⟩ := by
  cases q with
  | typed A => exact if_neg hq
  | root α => rfl

theorem strictColour_of_legal (A : StrictDecTile C hC) (hA : StrictLegal C hC A)
    (i : C.Side A.typ) : strictColour C hC (.typed A) i = Sum.inl (A.cell i) :=
  if_pos hA

end Decoration

/-! ## Geometric helpers -/

/-- In a side-to-side plane tiling every listed side of a tile coincides with a listed side of
another tile (plane coverage, local finiteness and disjoint interiors; classical planar
topology).  Used to exclude inert decorations from proper tilings (`lem:glues`) and in the
assembly argument. -/
theorem exists_coincident_side {Pr : Protoset} (T : PlaneTiling Pr)
    (hT : T.SideToSide) {X : PlacedTile Pr} (hX : X ∈ T.tiles) (i : Fin (Pr.disk X.form).n) :
    ∃ Y ∈ T.tiles, Y ≠ X ∧ ∃ j : Fin (Pr.disk Y.form).n, Y.side j = X.side i := by
  sorry

/-- `finRotate` has no fixed point on `Fin N`, `N ≥ 2`. -/
private theorem finRotate_ne_self {N : ℕ} (hN : 2 ≤ N) (x : Fin N) : finRotate N x ≠ x := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have := congrArg (· - x) h
  simp at this

/-- A predicate on a cyclic index set that holds somewhere and fails somewhere changes from
true to false at some step of `finRotate`. -/
private theorem exists_rotate_transition {N : ℕ} (hN : 2 ≤ N) (p : Fin N → Prop) {i j : Fin N}
    (hi : p i) (hj : ¬ p j) : ∃ k, p k ∧ ¬ p (finRotate N k) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  by_contra hcon
  push_neg at hcon
  have hall : ∀ r : ℕ, p ((finRotate (n + 2) ^ r) i) := by
    intro r
    induction r with
    | zero => simpa using hi
    | succ r ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hcon _ ih
  obtain ⟨r, hr⟩ := isCycle_finRotate.exists_pow_eq (finRotate_ne_self hN i)
    (finRotate_ne_self hN j)
  exact hj (hr ▸ hall r)

/-- Translates of a nondegenerate segment coincide only for equal translations. -/
private theorem vadd_segment_inj {a b v w : Pt} (hab : b - a ≠ 0)
    (h : v +ᵥ segment ℝ a b = w +ᵥ segment ℝ a b) : v = w := by
  have h1 : v + b ∈ w +ᵥ segment ℝ a b := by
    rw [← h]; exact Set.vadd_mem_vadd_set (right_mem_segment ℝ a b)
  have h2 : w + b ∈ v +ᵥ segment ℝ a b := by
    rw [h]; exact Set.vadd_mem_vadd_set (right_mem_segment ℝ a b)
  rw [Set.mem_vadd_set, segment_eq_image'] at h1 h2
  obtain ⟨_, ⟨t, ⟨-, ht1⟩, rfl⟩, hz1⟩ := h1
  obtain ⟨_, ⟨s, ⟨-, hs1⟩, rfl⟩, hz2⟩ := h2
  simp only [vadd_eq_add] at hz1 hz2
  have key : (t + s - 2) • (b - a) = 0 := by
    linear_combination (norm := module) hz1 + hz2
  rcases smul_eq_zero.mp key with hts | hzero
  · have ht : t = 1 := by linarith
    subst ht
    rw [one_smul] at hz1
    have : w + b = v + b := by rw [← hz1]; abel
    exact (add_right_cancel this).symm
  · exact absurd hzero hab

/-- Two placed tiles of one form with the same `i`-th side have the same anchor. -/
theorem anchor_eq_of_side_eq {Pr : Protoset} {q : Pr.Form}
    {v w : Pt} (i : Fin (Pr.disk q).n)
    (h : (⟨q, v⟩ : PlacedTile Pr).side i = (⟨q, w⟩ : PlacedTile Pr).side i) : v = w := by
  have hba : (Pr.disk q).vertex (finRotate _ i) - (Pr.disk q).vertex i ≠ 0 := by
    rw [sub_ne_zero]
    intro hab
    exact finRotate_ne_self (by have := (Pr.disk q).three_le; omega) i
      ((Pr.disk q).vertex_injective hab)
  exact vadd_segment_inj hba h

private theorem side_translate (A : PlacedTile P) (v : Pt) (i : Fin (P.disk A.form).n) :
    (A.translate v).side i = v +ᵥ A.side i := by
  simp only [PlacedTile.side, PlacedTile.translate, vadd_vadd, vadd_eq_add]

private theorem sts_mono {S S₁ : Set (PlacedTile P)} (h : S ⊆ S₁) (hS : SideToSideSet S₁) :
    SideToSideSet S :=
  fun A hA B hB i j hij => hS A (h hA) B (h hB) i j hij

private theorem sts_of_translateSet {S : Set (PlacedTile P)} {v : Pt}
    (hS : SideToSideSet (translateSet v S)) : SideToSideSet S := by
  intro A hA B hB i j hij
  have hA' : A.translate v ∈ translateSet v S := ⟨A, hA, rfl⟩
  have hB' : B.translate v ∈ translateSet v S := ⟨B, hB, rfl⟩
  have hov : OverlapPos ((A.translate v).side i) ((B.translate v).side j) := by
    obtain ⟨x, y, hxy, hseg⟩ := hij
    refine ⟨v +ᵥ x, v +ᵥ y, by simpa using hxy, ?_⟩
    rw [side_translate, side_translate]
    intro z hz
    have hz' : -v +ᵥ z ∈ segment ℝ x y := by
      rw [segment_eq_image'] at hz ⊢
      obtain ⟨t, ht, rfl⟩ := hz
      exact ⟨t, ht, by simp only [vadd_eq_add, add_sub_add_left_eq_sub]; abel⟩
    have := hseg hz'
    exact ⟨by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using this.1,
      by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using this.2⟩
  have := hS _ hA' _ hB' i j hov
  rw [side_translate, side_translate] at this
  exact (vadd_left_cancel_iff v).1 this

private theorem decompose_translateSet (τ : Substitution P) (v : Pt) (S : Set (PlacedTile P)) :
    τ.decompose (translateSet v S) = translateSet (τ.θ • v) (τ.decompose S) := by
  ext X
  simp only [Substitution.decompose, Substitution.decomposeTile, translateSet, Set.mem_iUnion,
    Set.mem_image, PlacedTile.translate, exists_prop]
  constructor
  · rintro ⟨_, ⟨A, hA, rfl⟩, Y, hY, rfl⟩
    refine ⟨⟨Y.form, τ.θ • A.anchor +ᵥ Y.anchor⟩, ⟨A, hA, Y, hY, rfl⟩, ?_⟩
    simp only [vadd_eq_add, smul_add, add_assoc]
  · rintro ⟨_, ⟨A, hA, Y, hY, rfl⟩, rfl⟩
    refine ⟨⟨A.form, v +ᵥ A.anchor⟩, ⟨A, hA, rfl⟩, Y, hY, ?_⟩
    simp only [vadd_eq_add, smul_add, add_assoc]

private theorem decomposeIter_translateSet (τ : Substitution P) (j : ℕ) (v : Pt)
    (S : Set (PlacedTile P)) :
    τ.decomposeIter j (translateSet v S) =
      translateSet (τ.θ ^ j • v) (τ.decomposeIter j S) := by
  induction j with
  | zero => simp [Substitution.decomposeIter]
  | succ j ih =>
    show τ.decompose (τ.decomposeIter j (translateSet v S)) =
      translateSet (τ.θ ^ (j + 1) • v) (τ.decompose (τ.decomposeIter j S))
    rw [ih, decompose_translateSet, smul_smul, pow_succ']

private theorem decomposeIter_mono (τ : Substitution P) (j : ℕ) {S S₁ : Set (PlacedTile P)}
    (h : S ⊆ S₁) : τ.decomposeIter j S ⊆ τ.decomposeIter j S₁ := by
  induction j with
  | zero => exact h
  | succ j ih => exact Set.biUnion_subset_biUnion_left ih

private theorem decomposeIter_decomposeIter (τ : Substitution P) (j n : ℕ)
    (S : Set (PlacedTile P)) :
    τ.decomposeIter j (τ.decomposeIter n S) = τ.decomposeIter (n + j) S := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show τ.decompose (τ.decomposeIter j (τ.decomposeIter n S)) =
      τ.decompose (τ.decomposeIter (n + j) S)
    rw [ih]

/-- STS of iterated decompositions of a patch that lies (up to translation) in a supertile.
STS of `S` and `τ.STS` alone do **not** suffice: for unit squares `a`, `b` with `τ a` a
`2 × 2` grid of `a` and `τ b` a `2 × 4` grid of half-height rectangles `r` (and `τ r` two
`a`), every supertile is a grid, but the side-to-side pair `{a, b}` side by side decomposes
into a patch that is not side-to-side. -/
theorem _root_.Tilings.Substitution.STS.decomposeIter_sts_of_subset_supertile
    {τ : Substitution P} (hτ : τ.STS) {S : Set (PlacedTile P)} {n : ℕ} {p : P.Form} {v : Pt}
    (hS : translateSet v S ⊆ τ.supertile n p) (j : ℕ) :
    SideToSideSet (τ.decomposeIter j S) := by
  have h1 : τ.decomposeIter j (translateSet v S) ⊆ τ.supertile (n + j) p := by
    have := decomposeIter_mono τ j hS
    rwa [Substitution.supertile, decomposeIter_decomposeIter] at this
  have h2 := sts_mono h1 (hτ (n + j) p)
  rw [decomposeIter_translateSet] at h2
  exact sts_of_translateSet h2

section Bridge

variable (C : MacroCertificate P) (hC : C.Represents τ m)

/-- Inert decorations (`lem:glues`): every tile of a proper strict plane tiling is a legal typed
tile, since an inert side (fresh owner-side colour) has a coincident side of another tile
(`exists_coincident_side`), whose equal colour would force the same form, the same
side and hence the same anchor. -/
theorem strict_proper_allLegal (T : PlaneTiling (strictProtoset C hC))
    (hT : (strictDecoration C hC).Proper T) : AllStrictLegal C hC T := by
  intro X hX
  by_contra hnl
  obtain ⟨q, v⟩ := X
  have h3 := (C.Q.disk q.proj).three_le
  let i0 : Fin (C.Q.disk q.proj).n := ⟨0, by omega⟩
  obtain ⟨Y, hY, hYX, j, hj⟩ := exists_coincident_side T hT.1 hX i0
  have hcol : strictColour C hC Y.form j = strictColour C hC q i0 := hT.2 Y hY _ hX hYX j _ hj
  rw [strictColour_of_not_isLegal C hC q hnl] at hcol
  obtain ⟨q', w⟩ := Y
  by_cases hYl : StrictForm.IsLegal q'
  · cases q' with
    | root α => exact hYl.elim
    | typed B =>
      rw [strictColour_of_legal C hC B hYl] at hcol
      cases hcol
  · rw [strictColour_of_not_isLegal C hC q' hYl] at hcol
    obtain ⟨hqq, hij⟩ := Sigma.mk.inj (Sum.inr.inj hcol)
    subst hqq
    have hji := eq_of_heq hij
    subst hji
    exact hYX (by rw [anchor_eq_of_side_eq _ hj])

/-- `(strictDecoration C hC).Proper` is strict matching of legal typed tiles. -/
theorem strict_proper_iff (T : PlaneTiling (strictProtoset C hC)) :
    (strictDecoration C hC).Proper T ↔ IsStrictMatched C hC T ∧ AllStrictLegal C hC T := by
  constructor
  · intro hT
    have hL := strict_proper_allLegal C hC T hT
    refine ⟨⟨hT.1, ?_⟩, hL⟩
    intro A B v w hA hB hne i j hij
    have hcol : strictColour C hC (.typed A) i = strictColour C hC (.typed B) j :=
      hT.2 _ hA _ hB hne i j hij
    rw [strictColour_of_legal C hC A (hL _ hA), strictColour_of_legal C hC B (hL _ hB)] at hcol
    exact Sum.inl.inj hcol
  · rintro ⟨hM, hL⟩
    refine ⟨hM.1, ?_⟩
    rintro ⟨q, v⟩ hX ⟨q', w⟩ hY hne i j hij
    cases q with
    | root α => exact (hL _ hX).elim
    | typed A =>
      cases q' with
      | root α => exact (hL _ hY).elim
      | typed B =>
        show strictColour C hC (.typed A) i = strictColour C hC (.typed B) j
        rw [strictColour_of_legal C hC A (hL _ hX), strictColour_of_legal C hC B (hL _ hY)]
        exact congrArg Sum.inl (hM.2 A B v w hX hY hne i j hij)

end Bridge

/-! ## Strict coloured macroblocks -/

section Blocks

variable (C : MacroCertificate P) (hC : C.Represents τ m)

/-- A positioned strict coloured realization of the template `σ' α` (strict analogue of
`ColouredBlock`): the child of type `t` is `⟨t, col t⟩` placed at `v + anchor t`. -/
structure StrictBlock where
  /-- the parent form -/
  α : C.Q.Form
  /-- the offset (`θ` times the parent anchor) -/
  v : Pt
  /-- the colours of the children -/
  col : (t : C.Typ) → C.Side t → Fin 5 → SU C hC

namespace StrictBlock

variable {C hC} (K : StrictBlock C hC)

/-- The decorated child of type `t`. -/
def tileOf (t : C.Typ) : StrictDecTile C hC := ⟨t, K.col t⟩

/-- The placed decorated child of type `t`. -/
def placed (t : C.Typ) : PlacedTile (strictProtoset C hC) :=
  ⟨.typed (K.tileOf t), K.v + C.anchor t⟩

/-- The tiles of the block. -/
def tiles : Set (PlacedTile (strictProtoset C hC)) := {X | ∃ t, C.owner t = K.α ∧ X = K.placed t}

/-- The placed segment of a child side occurrence. -/
def childSide (o : C.SideOcc) : Set Pt := (K.v + C.anchor o.1) +ᵥ (C.Q.disk (C.form o.1)).side o.2

/-- The placed scaled parent side `d` (a macroside). -/
def macroSide (d : Fin (C.Q.disk K.α).n) : Set Pt := K.v +ᵥ C.macroSide K.α d

/-- The centre of the block. -/
def centre : StrictDecTile C hC := K.tileOf (C.central K.α)

end StrictBlock

/-- A partition of a strict plane tiling into positioned strict macroblocks. -/
structure StrictMacroPartition (T : PlaneTiling (strictProtoset C hC)) where
  /-- index set of the blocks -/
  ι : Type
  /-- the blocks -/
  block : ι → StrictBlock C hC
  /-- distinct blocks are disjoint -/
  disjoint : Pairwise fun j j' => Disjoint (block j).tiles (block j').tiles
  /-- the blocks cover the tiling -/
  cover : ⋃ j, (block j).tiles = T.tiles

/-- A strictly matched finite realization: every inner side of a child has a complete
coincident side of another child of the block with the same five-tuple (strict matching
imposes this on every inner side, without the nontriviality condition of the flexible rule). -/
def IsStrictProperRealization (K : StrictBlock C hC) : Prop :=
  ∀ (t : C.Typ) (i : C.Side t), C.owner t = K.α → C.IsInner (C.occ t i) →
    ∃ (t' : C.Typ) (j : C.Side t'), C.owner t' = K.α ∧ t' ≠ t ∧
      K.childSide (C.occ t' j) = K.childSide (C.occ t i) ∧ ∀ k : Fin 5, K.col t' j k = K.col t i k

/-- The standing situation of `lem:comp/boundary-header` (strict): a strictly matched finite
realization of `σ' α` in which every tile except possibly the centre is legal. -/
def StrictBlockContext (K : StrictBlock C hC) : Prop :=
  IsStrictProperRealization C hC K ∧
    ∀ t, C.owner t = K.α → t ≠ C.central K.α → StrictLegal C hC (K.tileOf t)

/-- The conclusion of `lem:comp/boundary-header` (strict) for a header `h`. -/
def StrictCommonHeader (K : StrictBlock C hC) (h : HeaderKernel.Header C.Typ C.Side) : Prop :=
  C.form h.1 = K.α ∧
    ∀ (t : C.Typ) (i : C.Side t), C.owner t = K.α → C.IsBoundary (C.occ t i) →
      K.col t i 3 = headerSU C hC h

/-- The reconstructed parent `D` of type `t`: `D_i(d)` is the third cell of port `i` on
`σ'd` (`lem:comp/reconstruction`; port `4` transports the parent's own fourth value). -/
def strictReconstruct (K : StrictBlock C hC) (t : C.Typ) : StrictDecTile C hC where
  typ := t
  cell d k := match C.port (C.form t) d k with
    | some o => K.col o.1 o.2 2
    | none => 0

/-- The block `K` is the strict decomposition of `D`. -/
def IsStrictExactBlockOf (K : StrictBlock C hC) (D : StrictDecTile C hC) : Prop :=
  C.form D.typ = K.α ∧ ∀ t, C.owner t = K.α → IsStrictChildOf C hC D (K.tileOf t)

/-- `T'` is obtained from the macroblocks of `part` by replacing each block with a
reconstructed parent and scaling down by `θ`. -/
def IsStrictReconstruction {T : PlaneTiling (strictProtoset C hC)}
    (part : StrictMacroPartition C hC T) (T' : PlaneTiling (strictProtoset C hC)) : Prop :=
  (∀ X ∈ T'.tiles, ∃ j, (part.block j).v = C.σ.θ • X.anchor ∧
      ∃ t, X.form = StrictForm.typed (strictReconstruct C hC (part.block j) t)) ∧
  (∀ j, ∃ X ∈ T'.tiles, (part.block j).v = C.σ.θ • X.anchor ∧
      ∃ t, X.form = StrictForm.typed (strictReconstruct C hC (part.block j) t))

/-- The macroside `d` of block `j` has a complete opposing macroside of another block with the
same ordered subdivision (the strict replacement of the conclusion of `lem:comp/alignment`). -/
def StrictOpposingMacroside {T : PlaneTiling (strictProtoset C hC)}
    (part : StrictMacroPartition C hC T) (j : part.ι) (d : Fin (C.Q.disk (part.block j).α).n) :
    Prop :=
  ∃ j' : part.ι, j' ≠ j ∧ ∃ e : Fin (C.Q.disk (part.block j').α).n,
    (part.block j').macroSide e = (part.block j).macroSide d ∧
    List.Forall₂ (fun o o' => (part.block j).childSide o = (part.block j').childSide o')
      (C.outerList (part.block j).α d) (C.outerList (part.block j').α e)

end Blocks

/-! ## The finite control proof, strict variant (`lem:schedule-compose`) -/

section Composition

variable (C : MacroCertificate P) (hC : C.Represents τ m)

open Classical in
/-- `def:control/substitution` (strict variant), clause by clause: the strict child satisfies
the clauses of `IsChildOfWith` with the outer fourth clause replaced by the schedule tag. -/
theorem strictChild_cells (A : StrictDecTile C hC) (t : C.Typ) (ht : C.owner t = C.form A.typ)
    (i : C.Side t) :
    (∀ d : C.Side A.typ, C.IsPrintOf (C.form A.typ) d (C.occ t i) →
      (∀ k : Fin 5, k ≠ 4 → (strictChild C hC A t).cell i k = A.cell d k) ∧
      (strictChild C hC A t).cell i 4 = identSU C hC (C.edge (C.occ t i))) ∧
    (¬ C.IsPrint (C.occ t i) →
      (strictChild C hC A t).cell i 0 =
          (if C.IsInner (C.occ t i) then identSU C hC (C.edge (C.occ t i)) else 0) ∧
      (strictChild C hC A t).cell i 1 = 0 ∧
      (strictChild C hC A t).cell i 4 = 0 ∧
      (∀ (d : C.Side A.typ) (j : Fin 5), C.occ t i ∈ C.path (C.form A.typ) d j →
        (strictChild C hC A t).cell i 2 = A.cell d j) ∧
      ((∀ (d : C.Side A.typ) (j : Fin 5), C.occ t i ∉ C.path (C.form A.typ) d j) →
        (strictChild C hC A t).cell i 2 = 0) ∧
      (C.IsOuter (C.occ t i) → (strictChild C hC A t).cell i 3 = schedU C hC (C.occ t i)) ∧
      (C.IsBoundary (C.occ t i) →
        (strictChild C hC A t).cell i 3 = headerSU C hC (strictHeaderOf C hC A)) ∧
      (C.IsInner (C.occ t i) → ¬ C.IsBoundary (C.occ t i) →
        (strictChild C hC A t).cell i 3 = botSU C hC)) := by
  have hcell : ∀ k, (strictChild C hC A t).cell i k =
      if h : (copySource C (C.form A.typ) (C.occ t i) k).Nonempty then A.cell h.some.1 h.some.2
      else strictGenCell C hC (C.form A.typ) (headerSU C hC (strictHeaderOf C hC A))
        (C.occ t i) k := fun _ => rfl
  have ht' : C.owner (C.occ t i).1 = C.form A.typ := ht
  refine ⟨fun d hd => ?_, fun hnp => ?_⟩
  · have hpr : C.IsPrint (C.occ t i) := by
      unfold MacroData.IsPrint
      rw [ht']
      exact ⟨d, hd⟩
    refine ⟨fun k hk => ?_, ?_⟩
    · have hne : (copySource C (C.form A.typ) (C.occ t i) k).Nonempty :=
        ⟨(d, k), Or.inl ⟨hd, hk, rfl⟩⟩
      rw [hcell, dif_pos hne]
      rcases hne.some_mem with ⟨hp1, -, hp2⟩ | ⟨hnp, -, -⟩
      · rw [isPrintOf_unique C hp1 hd, hp2]
      · exact absurd hpr hnp
    · have hne : ¬ (copySource C (C.form A.typ) (C.occ t i) 4).Nonempty := by
        rintro ⟨p, ⟨-, h4, -⟩ | ⟨hnp, -, -⟩⟩
        · exact h4 rfl
        · exact hnp hpr
      rw [hcell, dif_neg hne]
      simp [strictGenCell, show ∃ d, C.IsPrintOf (C.form A.typ) d (C.occ t i) from ⟨d, hd⟩]
  · have hnp' : ¬ ∃ d, C.IsPrintOf (C.form A.typ) d (C.occ t i) := by
      rw [← ht']
      exact hnp
    have hcs : ∀ k, k ≠ 2 → ¬ (copySource C (C.form A.typ) (C.occ t i) k).Nonempty := by
      rintro k hk ⟨p, ⟨hp, -, -⟩ | ⟨-, hk2, -⟩⟩
      · exact hnp' ⟨_, hp⟩
      · exact hk hk2
    refine ⟨?_, ?_, ?_, fun d j hdj => ?_, fun hno => ?_, fun hout => ?_, fun hb => ?_,
      fun hin hnb => ?_⟩
    · rw [hcell, dif_neg (hcs 0 (by decide))]
      simp [strictGenCell, hnp']
    · rw [hcell, dif_neg (hcs 1 (by decide))]
      simp [strictGenCell, hnp']
    · rw [hcell, dif_neg (hcs 4 (by decide))]
      simp [strictGenCell, hnp']
    · have hne : (copySource C (C.form A.typ) (C.occ t i) 2).Nonempty :=
        ⟨(d, j), Or.inr ⟨hnp, rfl, hdj⟩⟩
      rw [hcell, dif_pos hne]
      rcases hne.some_mem with ⟨hp1, -, -⟩ | ⟨-, -, hp3⟩
      · exact absurd ⟨_, hp1⟩ hnp'
      · obtain ⟨h1, h2⟩ := path_source_unique C ht' hnp hp3 hdj
        rw [h1, h2]
    · have hne : ¬ (copySource C (C.form A.typ) (C.occ t i) 2).Nonempty := by
        rintro ⟨p, ⟨hp, -, -⟩ | ⟨-, -, hp3⟩⟩
        · exact hnp' ⟨_, hp⟩
        · exact hno p.1 p.2 hp3
      rw [hcell, dif_neg hne]
      simp [strictGenCell, hnp']
    · rw [hcell, dif_neg (hcs 3 (by decide))]
      simp [strictGenCell, hnp', hout]
    · have hout : ¬ C.IsOuter (C.occ t i) := hb.1
      rw [hcell, dif_neg (hcs 3 (by decide))]
      simp [strictGenCell, hnp', hout, hb]
    · have hout : ¬ C.IsOuter (C.occ t i) := hin
      rw [hcell, dif_neg (hcs 3 (by decide))]
      simp [strictGenCell, hnp', hout, hnb]

/-- `lem:comp/outer-boundary`, without the hereditary hypothesis: in a macrotemplate every
child type with an outer side also has a boundary side. -/
theorem exists_boundary_side_of_outer (t : C.Typ) (i : C.Side t)
    (hi : C.IsOuter (C.occ t i)) : ∃ j : C.Side t, C.IsBoundary (C.occ t j) := by
  obtain ⟨j, hj⟩ := C.g1_inner_side t
  obtain ⟨k, hk, hk'⟩ := exists_rotate_transition
    (by have := (C.Q.disk (C.form t)).three_le; omega) (fun k => C.IsOuter (C.occ t k)) hi hj
  have hmem : C.occEnd (C.occ t k) ∈ C.occSide (C.occ t k) := by
    dsimp [MacroData.occEnd, MacroData.occSide, MacroData.childTile, PlacedTile.side,
      PolygonalDisk.side]
    exact ⟨_, right_mem_segment ℝ _ _, rfl⟩
  exact ⟨finRotate _ k, hk', Or.inl (hk hmem)⟩

/-- `lem:comp/legal-properties` (strict variant): a legal tile has a legal parent, is strictly
normal (in particular every outer fourth cell is its schedule tag, fixed by the type) and
identity-correct; every child of a legal tile is legal; all boundary fourth cells equal the
header of one legal parent; third signals of one path agree. -/
theorem strictLegal_properties (A : StrictDecTile C hC) (hA : StrictLegal C hC A) :
    (∃ B, StrictLegal C hC B ∧ IsStrictChildOf C hC B A) ∧
    IsStrictNormal C hC A ∧ IsStrictIdentityCorrect C hC A ∧
    (∀ B, IsStrictChildOf C hC A B → StrictLegal C hC B) ∧
    (∃ B, StrictLegal C hC B ∧ IsStrictChildOf C hC B A ∧
      ∀ i : C.Side A.typ, C.IsBoundary (C.occ A.typ i) →
        A.cell i 3 = headerSU C hC (strictHeaderOf C hC B)) ∧
    (∀ (d : Fin (C.Q.disk (C.owner A.typ)).n) (j : Fin 5) (i i' : C.Side A.typ),
      C.occ A.typ i ∈ C.path (C.owner A.typ) d j → C.occ A.typ i' ∈ C.path (C.owner A.typ) d j →
      ¬ C.IsPrint (C.occ A.typ i) → ¬ C.IsPrint (C.occ A.typ i') →
      A.cell i 2 = A.cell i' 2) := by
  sorry

/-- `lem:comp/assembly` (strict variant): a strictly matched plane tiling of normal
identity-correct typed tiles admits a partition into positioned `σ'` macrotemplates.  Inner
identities force the neighbours exactly as in the flexible proof; strict matching replaces
the nontrivial-side rule (every side has a coincident side, and a schedule fourth cell with
fifth cell zero can match only another outer side). -/
theorem strict_assembleMacrotemplates (T : PlaneTiling (strictProtoset C hC))
    (hT : IsStrictMatched C hC T)
    (hN : ∀ X ∈ T.tiles, ∃ A, X.form = StrictForm.typed A ∧ IsStrictNormal C hC A ∧
      IsStrictIdentityCorrect C hC A) :
    Nonempty (StrictMacroPartition C hC T) := by
  sorry

/-- `lem:comp/assembly` (strict variant, final assertion): every strictly matched plane tiling
of legal typed tiles has such a partition. -/
theorem strict_assembleMacrotemplates_of_legal (T : PlaneTiling (strictProtoset C hC))
    (hT : IsStrictMatched C hC T) (hL : AllStrictLegal C hC T) :
    Nonempty (StrictMacroPartition C hC T) := by
  refine strict_assembleMacrotemplates C hC T hT fun X hX => ?_
  obtain ⟨q, v⟩ := X
  cases q with
  | root α => exact (hL _ hX).elim
  | typed A =>
    have hA := strictLegal_properties C hC A (hL _ hX)
    exact ⟨A, rfl, hA.2.1, hA.2.2.1⟩

/-- `lem:comp/boundary-header` (strict variant): in a strictly matched finite realization of
`σ' α` whose noncentral tiles are legal, every boundary fourth cell carries the same header
`h = (t, v)`, and `form t = α`. -/
theorem strict_boundary_header_constant (K : StrictBlock C hC) (hK : StrictBlockContext C hC K) :
    ∃ h : HeaderKernel.Header C.Typ C.Side, StrictCommonHeader C hC K h := by
  sorry

/-- `lem:comp/reconstruction` (strict variant): the reconstructed parent `D` of type `t` (with
`D_i(d)` the third cell of port `i` on `σ'd`) is strictly normal (its outer fourth cells, read
from port `4`, are the schedule tags of its type) and identity-correct, and `H(D) = h`. -/
theorem strict_reconstructed_header_eq (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h) :
    IsStrictNormal C hC (strictReconstruct C hC K h.1) ∧
      IsStrictIdentityCorrect C hC (strictReconstruct C hC K h.1) ∧
      strictHeaderOf C hC (strictReconstruct C hC K h.1) = h := by
  sorry

/-- `lem:comp/signals` (strict variant): every nonprint third signal on `P_i(d)` equals
`D_i(d)`, and the noncentral (small) owner of the print of `d` has first four cells
`D_1(d), …, D_4(d)` on that print. -/
theorem strict_path_and_print_recovery (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h) :
    (∀ (d : C.Side h.1) (j : Fin 5) (o : C.SideOcc), o ∈ C.path (C.form h.1) d j →
      ¬ C.IsPrint o → K.col o.1 o.2 2 = (strictReconstruct C hC K h.1).cell d j) ∧
    (∀ d : C.Side h.1, C.marked (C.form h.1) d → ∀ k : Fin 5, k ≠ 4 →
      K.col (C.partner (C.printOcc (C.form h.1) d)).1 (C.partner (C.printOcc (C.form h.1) d)).2 k =
        (strictReconstruct C hC K h.1).cell d k) := by
  sorry

/-- `lem:comp/exact` (strict variant): the block is the strict decomposition of its
reconstructed parent.  Legal boundary witnesses identify the template, so the generated
schedules `W(α, e)` of its outer sides agree with the decomposition of `D`, independently of
the fourth values of `D`. -/
theorem strict_macroblock_is_decomposition (K : StrictBlock C hC)
    (hK : StrictBlockContext C hC K) (h : HeaderKernel.Header C.Typ C.Side)
    (hh : StrictCommonHeader C hC K h) :
    IsStrictExactBlockOf C hC K (strictReconstruct C hC K h.1) := by
  sorry

/-- `lem:comp/cyclic-legal` (strict variant): if the centre of the block is legal and the type
of `D` is cyclic, then `D` is the centre and is legal. -/
theorem strict_reconstructed_cyclic_legal (K : StrictBlock C hC)
    (hK : StrictBlockContext C hC K) (h : HeaderKernel.Header C.Typ C.Side)
    (hh : StrictCommonHeader C hC K h) (hA : StrictLegal C hC K.centre)
    (hcyc : C.IsCyclic h.1) :
    strictReconstruct C hC K h.1 = K.centre ∧ StrictLegal C hC (strictReconstruct C hC K h.1) := by
  sorry

/-- `lem:comp/noncentral-legal` (strict variant): if the centre is legal and the type of `D` is
noncentral, then `D` is legal. -/
theorem strict_reconstructed_noncentral_legal (K : StrictBlock C hC)
    (hK : StrictBlockContext C hC K) (h : HeaderKernel.Header C.Typ C.Side)
    (hh : StrictCommonHeader C hC K h) (hA : StrictLegal C hC K.centre)
    (hnc : ¬ C.IsCentral h.1) : StrictLegal C hC (strictReconstruct C hC K h.1) := by
  sorry

/-- `lem:schedule-compose` ("Schedule alignment gives complete parent sides, and the whole-port
lemma then pairs equal numbered ports"; replaces the rank alignment `lem:comp/alignment`): in
a strictly matched plane tiling of legal tiles partitioned into macroblocks, every macroside
has a complete opposing macroside of another block with the same ordered subdivision.  Proof
plan: equal outer fourth cells give `Alignment.SchedulesAligned` for the grouped parents,
`Alignment.schedule_intermediate_sts` makes them side-to-side, and the outer lists of
coincident parent sides are the same whole fine sides in the global positive direction. -/
theorem strict_opposing_macroside (hτ : τ.STS)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (C.Δ α).tiles))
    (T : PlaneTiling (strictProtoset C hC)) (hT : IsStrictMatched C hC T)
    (hL : AllStrictLegal C hC T) (part : StrictMacroPartition C hC T) (j : part.ι)
    (d : Fin (C.Q.disk (part.block j).α).n) : StrictOpposingMacroside C hC part j d := by
  sorry

/-- `lem:comp/proper` (strict variant, `lem:schedule-compose`): for a strictly matched plane
tiling of legal tiles, replacing each assembled macroblock by its reconstructed parent and
scaling down gives a strictly matched tiling of normal identity-correct typed tiles of which
the input is the strict decomposition.  Coincident parent sides have the same numbered ports
(`strict_opposing_macroside`), whose third cells identify all five parent components. -/
theorem strict_composed_proper (hτ : τ.STS)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (C.Δ α).tiles))
    (T : PlaneTiling (strictProtoset C hC)) (hT : IsStrictMatched C hC T)
    (hL : AllStrictLegal C hC T) :
    ∃ (part : StrictMacroPartition C hC T) (T' : PlaneTiling (strictProtoset C hC)),
      IsStrictReconstruction C hC part T' ∧ IsStrictMatched C hC T' ∧
      (∀ X ∈ T'.tiles, ∃ D, X.form = StrictForm.typed D ∧ IsStrictNormal C hC D ∧
        IsStrictIdentityCorrect C hC D) ∧
      (strictSubst C hC).IsComposition T' T := by
  sorry

/-- The cell of a strict tile indexed by the value of a side index (zero out of range). -/
private def acycCellv (X : StrictDecTile C hC) (v : ℕ) (k : Fin 5) : SU C hC :=
  if h : v < (C.Q.disk (C.form X.typ)).n then X.cell ⟨v, h⟩ k else 0

private theorem acycCellv_side (X : StrictDecTile C hC) (i : C.Side X.typ) (k : Fin 5) :
    acycCellv C hC X i.val k = X.cell i k := by
  unfold acycCellv
  rw [dif_pos i.isLt]

private theorem acyc_identSU_ne_zero (e : C.EdgeId) : identSU C hC e ≠ 0 := by
  intro h; cases h

private theorem acyc_identSU_inj {e e' : C.EdgeId} (h : identSU C hC e = identSU C hC e') :
    e = e' := by
  simp only [identSU] at h
  cases h; rfl

private theorem acyc_large_of_central {s : C.Typ} (hs : C.IsCentral s) :
    C.kind (C.form s) = .large :=
  (C.g5_large_iff s).2 hs.symm

private theorem acyc_owner_not_large {s : C.Typ} (hs : C.IsCentral s) (ha : ¬ C.IsCyclic s) :
    C.kind (C.owner s) ≠ .large := by
  intro hl
  apply ha
  have h1 := C.g5_central_fixes_large _ hl
  rw [hs] at h1
  show C.central (C.form s) = s
  rw [h1]
  exact hs

private theorem acyc_central_sides {s : C.Typ} (hs : C.IsCentral s) (i : C.Side s) :
    ¬ C.IsOuter (C.occ s i) ∧ ¬ C.IsBoundary (C.occ s i) := by
  have h := C.g2_central (C.owner s)
  rw [hs] at h
  exact h i

private theorem acyc_isPrint_iff {s : C.Typ} {β : C.Q.Form} (hs : C.owner s = β) (i : C.Side s) :
    C.IsPrint (C.occ s i) ↔ ∃ d : Fin (C.Q.disk β).n, C.IsPrintOf β d (C.occ s i) := by
  subst hs
  rfl

private theorem acyc_not_on_path {s : C.Typ} {β : C.Q.Form} (hs : C.owner s = β) (i : C.Side s)
    (hm : ¬ C.IsMarked (C.occ s i)) (d : Fin (C.Q.disk β).n) (j : Fin 5) :
    C.occ s i ∉ C.path β d j := by
  subst hs
  intro hmem
  by_cases hg : C.IsGenuinePath (C.owner s) d j
  · exact hm (C.g7_marking _ (Or.inr (Or.inr (Or.inr ⟨d, j, hg, hmem⟩))))
  · rw [C.g4_path_trivial _ d j hg, Option.mem_toList] at hmem
    have hmem' : C.occ s i ∈ C.outerList _ d := List.mem_iff_getElem?.mpr ⟨_, hmem⟩
    exact hm (C.g7_marking _ (Or.inl ((C.g3_outerList_mem _ d _).1 hmem').2.1))

private theorem acyc_isPrint_of_cyclic {s : C.Typ} (hcyc : C.central (C.form s) = s)
    (hl : C.kind (C.form s) = .large) (d : C.Side s) (hd : C.marked (C.form s) d) :
    C.IsPrint (C.occ s d) := by
  have hown : C.owner s = C.form s := by
    have := C.g5_central_owner (C.form s)
    rw [hcyc] at this
    exact this
  have hval := C.g5_print_id_large (C.form s) d hl hd
  rw [acyc_isPrint_iff C hown]
  refine ⟨d, hd, Or.inl ?_⟩
  show (⟨s, d⟩ : C.SideOcc) = ⟨C.central (C.form s), C.print (C.form s) d⟩
  generalize C.print (C.form s) d = p at hval
  revert p
  rw [hcyc]
  intro p hp
  exact Sigma.ext rfl (heq_of_eq (Fin.ext hp.symm))

private theorem acyc_marked_cast {β β' : C.Q.Form} (h : β = β') (d : Fin (C.Q.disk β).n)
    (hd : C.marked β d) : C.marked β' (Fin.cast (congrArg (fun u => (C.Q.disk u).n) h) d) := by
  subst h
  exact hd

private theorem acyc_child_copy (Q' : StrictDecTile C hC) (s : C.Typ)
    (hs : C.central (C.form Q'.typ) = s) (hl : C.kind (C.form Q'.typ) = .large)
    (d : C.Side Q'.typ) (hd : C.marked (C.form Q'.typ) d) (k : Fin 5) (hk : k ≠ 4) :
    acycCellv C hC (strictChild C hC Q' s) d.val k = Q'.cell d k := by
  subst hs
  have hown := C.g5_central_owner (C.form Q'.typ)
  have hval := C.g5_print_id_large (C.form Q'.typ) d hl hd
  have hc := ((strictChild_cells C hC Q' _ hown (C.print (C.form Q'.typ) d)).1 d
    ⟨hd, Or.inl rfl⟩).1 k hk
  rw [← hc, ← acycCellv_side]
  rw [hval]

private theorem acyc_child_normal (Q' : StrictDecTile C hC) (s : C.Typ)
    (hs : C.owner s = C.form Q'.typ) :
    IsStrictNormal C hC (strictChild C hC Q' s) ∧
      IsStrictIdentityCorrect C hC (strictChild C hC Q' s) := by
  have hcells := strictChild_cells C hC Q' s hs
  have key : ∀ (i : C.Side s) (k : Fin 5), IsStrictLocal C (C.occ s i) k →
      (strictChild C hC Q' s).cell i k = strictPrescribedCell C hC (C.occ s i) k := by
    intro i k hloc
    by_cases hp : C.IsPrint (C.occ s i)
    · obtain ⟨d, hd⟩ := (acyc_isPrint_iff C hs i).1 hp
      have hin := isInner_of_isPrintOf C hd
      rcases hloc with (hnm | ⟨-, -, rfl⟩ | ⟨-, ⟨-, hnp⟩, -⟩) | ⟨hout, -⟩
      · exact absurd (C.g7_marking _ (Or.inr (Or.inr (Or.inl hp)))) hnm
      · rw [((hcells i).1 d hd).2]
        simp [strictPrescribedCell, hp]
      · exact absurd hp hnp
      · exact absurd hout hin
    · obtain ⟨h0, h1, h4, -, hno, hout, -, hib⟩ := (hcells i).2 hp
      rcases hloc with (hnm | ⟨-, -, rfl⟩ | ⟨-, -, rfl | rfl⟩) | ⟨hout', rfl⟩
      · have hnout : ¬ C.IsOuter (C.occ s i) := fun h => hnm (C.g7_marking _ (Or.inl h))
        have hnb : ¬ C.IsBoundary (C.occ s i) := fun h => hnm (C.g7_marking _ (Or.inr (Or.inl h)))
        have hnpath := acyc_not_on_path C hs i hnm
        obtain rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
          fin_cases k <;> simp
        · rw [h0]; simp [strictPrescribedCell]
        · rw [h1]; simp [strictPrescribedCell]
        · rw [hno hnpath]; simp [strictPrescribedCell]
        · rw [hib hnout hnb]
          simp [strictPrescribedCell, hnout, hnb, hp]
          exact fun h => absurd hnout h
        · rw [h4]; simp [strictPrescribedCell, hp]
      · rw [h4]; simp [strictPrescribedCell, hp]
      · rw [h0]; simp [strictPrescribedCell]
      · rw [h4]; simp [strictPrescribedCell, hp]
      · rw [hout hout']; simp [strictPrescribedCell, hout']
  refine ⟨key, fun i => ⟨fun hin hnp => ?_, fun hp => ?_⟩⟩
  · exact ((hcells i).2 hnp).1.trans (if_pos hin)
  · obtain ⟨d, hd⟩ := (acyc_isPrint_iff C hs i).1 hp
    exact ((hcells i).1 d hd).2


private theorem acyc_no_origin (f : ℕ → DecTile C)
    (hown : ∀ n, C.owner (f n).typ = C.form (f (n + 1)).typ)
    (hall : ∀ n, C.central (C.form (f (n + 1)).typ) = (f (n + 1)).typ ∧
      C.kind (C.form (f (n + 1)).typ) = .large)
    (n : ℕ) (i : C.Side (f n).typ) (k : Fin 5) (h : HasOrigin C f n i k) :
    C.IsPrint (C.occ (f n).typ i) → k ≠ 4 → False := by
  induction h with
  | origin n i k hempty =>
    intro hp hk
    obtain ⟨e, he⟩ := (acyc_isPrint_iff C (hown n) i).1 hp
    have hmem : (e, k) ∈ copySource C (C.form (f (n + 1)).typ) (C.occ (f n).typ i) k :=
      Or.inl ⟨he, hk, rfl⟩
    rw [hempty] at hmem
    exact hmem
  | step n i k d k' hmem _ ih =>
    intro hp hk
    rcases hmem with ⟨hpd, hk4, rfl⟩ | ⟨hnp, -, -⟩
    · exact ih (acyc_isPrint_of_cyclic C (hall n).1 (hall n).2 d hpd.1) hk4
    · exact hnp hp

private theorem acyc_origin_shift (f : ℕ → DecTile C) (a : ℕ) :
    ∀ (N : ℕ) (i : C.Side (f N).typ) (k : Fin 5), HasOrigin C f N i k →
      ∀ (n : ℕ) (hN : a + n = N),
        HasOrigin C (fun l => f (a + l)) n (by subst hN; exact i) k := by
  intro N i k h
  induction h with
  | origin N i k hempty =>
    intro n hN
    subst hN
    exact HasOrigin.origin (ch := fun l => f (a + l)) n i k hempty
  | step N i k d k' hmem _ ih =>
    intro n hN
    subst hN
    exact HasOrigin.step (ch := fun l => f (a + l)) n i k d k' hmem (ih (n + 1) rfl)

private theorem acyc_exists_good_side (s s' : C.Typ) (hf : C.form s' = C.form s)
    (hs : C.IsCentral s) (hsa : ¬ C.IsCyclic s) (hs' : C.IsCentral s') (hsa' : ¬ C.IsCyclic s') :
    ∃ d : C.Side s, C.marked (C.form s) d ∧ ¬ C.IsPrint (C.occ s d) ∧
      ¬ C.IsPrint (C.occ s' (Fin.cast (congrArg (fun u => (C.Q.disk u).n) hf.symm) d)) := by
  classical
  have hP : ∀ u : C.Typ, C.IsCentral u → ¬ C.IsCyclic u →
      (Finset.univ.filter fun i : C.Side u => C.IsPrint (C.occ u i)).card ≤ C.Qmax := by
    intro u hu hua
    have hlu := acyc_large_of_central C hu
    have hnl := acyc_owner_not_large C hu hua
    let g : Fin (C.Q.disk (C.owner u)).n → C.Side u := fun e =>
      Fin.cast (congrArg (fun t => (C.Q.disk (C.form t)).n) hu) (C.print (C.owner u) e)
    calc _ ≤ ((Finset.univ.filter fun e => C.marked (C.owner u) e).image g).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          obtain ⟨e, hm, ho⟩ := hi
          rcases ho with ho | ho
          · refine Finset.mem_image.2 ⟨e, by simpa using hm, ?_⟩
            apply Fin.ext
            have := congrArg (fun o : C.SideOcc => o.2.val) ho
            simp only [g, Fin.val_cast]
            exact this.symm
          · exfalso
            have h1 := congrArg Sigma.fst ho
            have h2 := C.g4_print_small _ e hm
            rw [← h1] at h2
            change C.kind (C.form u) = .small at h2
            rw [hlu] at h2
            cases h2
      _ ≤ (Finset.univ.filter fun e => C.marked (C.owner u) e).card := Finset.card_image_le
      _ ≤ C.Qmax := by
          have := C.g5_card_marked_small _ hnl
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
          exact this
  have hM : (Finset.univ.filter fun d : C.Side s => C.marked (C.form s) d).card = 4 * C.N := by
    have := C.g5_card_marked_large _ (acyc_large_of_central C hs)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    exact this
  have hn : (C.Q.disk (C.form s)).n = (C.Q.disk (C.form s')).n :=
    congrArg (fun u => (C.Q.disk u).n) hf.symm
  have hP' : (Finset.univ.filter fun d : C.Side s =>
      C.IsPrint (C.occ s' (Fin.cast hn d))).card ≤ C.Qmax := by
    refine le_trans (Finset.card_le_card_of_injOn (Fin.cast hn) ?_ ?_) (hP s' hs' hsa')
    · intro d hd
      simpa using hd
    · intro a _ b _ h
      exact Fin.cast_injective _ h
  by_contra hcon
  have hsub : (Finset.univ.filter fun d : C.Side s => C.marked (C.form s) d) ⊆
      (Finset.univ.filter fun i : C.Side s => C.IsPrint (C.occ s i)) ∪
      (Finset.univ.filter fun d : C.Side s => C.IsPrint (C.occ s' (Fin.cast hn d))) := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hd ⊢
    by_contra h2
    push_neg at h2
    exact hcon ⟨d, hd, h2.1, h2.2⟩
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h3 := C.g5_three_Q_lt
  have h4 := hP s hs hsa
  omega

private theorem acyc_ident (X Y : StrictDecTile C hC) (hXc : C.IsCentral X.typ)
    (hXa : ¬ C.IsCyclic X.typ) (hYc : C.IsCentral Y.typ) (hYa : ¬ C.IsCyclic Y.typ)
    (hf : C.form Y.typ = C.form X.typ)
    (hXN : IsStrictNormal C hC X) (hXI : IsStrictIdentityCorrect C hC X)
    (hYN : IsStrictNormal C hC Y) (hYI : IsStrictIdentityCorrect C hC Y)
    (hcell : ∀ d : C.Side X.typ, C.marked (C.form X.typ) d → ∀ k : Fin 5, k ≠ 4 →
      acycCellv C hC Y d.val k = X.cell d k) : Y = X := by
  obtain ⟨d, hdm, hdX, hdY⟩ := acyc_exists_good_side C X.typ Y.typ hf hXc hXa hYc hYa
  have hinX : C.IsInner (C.occ X.typ d) := (acyc_central_sides C hXc d).1
  have hinY := (acyc_central_sides C hYc
    (Fin.cast (congrArg (fun u => (C.Q.disk u).n) hf.symm) d)).1
  have e1 := (hXI d).1 hinX hdX
  have e2 := (hYI _).1 hinY hdY
  have e3 := hcell d hdm 0 (by decide)
  rw [← acycCellv_side] at e2
  rw [Fin.val_cast] at e2
  rw [e2, e1] at e3
  have hedge := acyc_identSU_inj C hC e3
  have htyp : Y.typ = X.typ := by
    rcases C.g1_edge_unique _ _ hinX hinY hedge.symm with h | h
    · exact congrArg Sigma.fst h
    · exfalso
      have h1 : Y.typ = (C.partner (C.occ X.typ d)).1 := congrArg Sigma.fst h
      obtain ⟨hne, hown, -⟩ := C.g1_partner _ hinX
      apply hne
      rw [← h1]
      calc Y.typ = C.central (C.owner Y.typ) := hYc.symm
        _ = C.central (C.owner X.typ) := by rw [h1, hown]
        _ = X.typ := hXc
  obtain ⟨tX, cX⟩ := X
  obtain ⟨tY, cY⟩ := Y
  simp only at htyp
  subst htyp
  congr
  funext i k
  by_cases hk : C.marked (C.form tY) i ∧ k ≠ 4
  · have := hcell i hk.1 k hk.2
    rw [acycCellv_side C hC ⟨tY, cY⟩ i] at this
    exact this
  · have hloc : IsStrictLocal C (C.occ tY i) k := by
      by_cases hm : C.marked (C.form tY) i
      · have hk4 : k = 4 := by
          by_contra h4
          exact hk ⟨hm, h4⟩
        by_cases hsp : C.special (C.occ tY i) ∨ C.IsPrint (C.occ tY i)
        · exact Or.inl (Or.inr (Or.inl ⟨hm, hsp, hk4⟩))
        · push_neg at hsp
          exact Or.inl (Or.inr (Or.inr ⟨hm, hsp, Or.inr hk4⟩))
      · exact Or.inl (Or.inl hm)
    exact (hYN i k hloc).trans (hXN i k hloc).symm


/-- `lem:comp/acyclic-legal` (strict variant): every reconstructed parent of central acyclic
type is legal (second-scale fingerprint argument, `L - Q > 2Q`). -/
theorem strict_reconstructed_acyclic_legal (T : PlaneTiling (strictProtoset C hC))
    (hT : IsStrictMatched C hC T) (hL : AllStrictLegal C hC T)
    (part : StrictMacroPartition C hC T) (T' : PlaneTiling (strictProtoset C hC))
    (hrec : IsStrictReconstruction C hC part T') (hT' : IsStrictMatched C hC T')
    (hN : ∀ X ∈ T'.tiles, ∃ D, X.form = StrictForm.typed D ∧ IsStrictNormal C hC D ∧
      IsStrictIdentityCorrect C hC D)
    (hex : (strictSubst C hC).IsComposition T' T) :
    ∀ X ∈ T'.tiles, ∀ D, X.form = StrictForm.typed D → C.IsCentral D.typ →
      ¬ C.IsCyclic D.typ → StrictLegal C hC D := by
  have _ := And.intro hT (And.intro hrec hT')
  intro X hX D hXD hcent hacyc
  obtain ⟨D', hD', hDN, hDI⟩ := hN X hX
  rw [hXD] at hD'
  cases hD'
  have hlα : C.kind (C.form D.typ) = .large := acyc_large_of_central C hcent
  have hcf : C.form (C.central (C.form D.typ)) = C.form D.typ := C.g5_central_fixes_large _ hlα
  have hco : C.owner (C.central (C.form D.typ)) = C.form D.typ := C.g5_central_owner _
  obtain ⟨v, hAT⟩ : ∃ v : Pt, (⟨StrictForm.typed (strictChild C hC D (C.central (C.form D.typ))), v⟩ :
      PlacedTile (strictProtoset C hC)) ∈ T.tiles := by
    refine ⟨C.σ.θ • X.anchor +ᵥ C.anchor (C.central (C.form D.typ)), ?_⟩
    rw [← hex]
    refine Set.mem_biUnion hX ?_
    show _ ∈ translateSet _ ((strictSubst C hC).rule X.form).tiles
    rw [hXD]
    exact ⟨_, ⟨C.central _, hco, rfl⟩, rfl⟩
  obtain ⟨ch, h0, hch, hleg⟩ : StrictLegal C hC (strictChild C hC D (C.central (C.form D.typ))) :=
    hL _ hAT
  have h0typ : (ch 0).typ = C.central (C.form D.typ) := by rw [h0]; rfl
  have hex1 : ∃ n, (ch (n + 1)).typ ≠ C.central (C.form D.typ) := by
    by_contra hall
    push_neg at hall
    have hall' : ∀ n, C.central (C.form (ch (n + 1)).typ) = (ch (n + 1)).typ ∧
        C.kind (C.form (ch (n + 1)).typ) = .large := by
      intro n
      rw [hall n, hcf]
      exact ⟨rfl, hlα⟩
    obtain ⟨d0, hd0m, hd0p, -⟩ := acyc_exists_good_side C D.typ D.typ rfl hcent hacyc hcent hacyc
    have hne : D.cell d0 0 ≠ 0 := by
      rw [(hDI d0).1 (acyc_central_sides C hcent d0).1 hd0p]
      exact acyc_identSU_ne_zero C hC _
    have hA0 : (strictChild C hC D (C.central (C.form D.typ))).cell (C.print (C.form D.typ) d0) 0 =
        D.cell d0 0 :=
      ((strictChild_cells C hC D _ hco (C.print _ d0)).1 d0 ⟨hd0m, Or.inl rfl⟩).1 0 (by decide)
    have hz : ∀ i : C.Side (ch 0).typ, C.IsPrint (C.occ (ch 0).typ i) → (ch 0).cell i 0 = 0 := by
      intro i hp
      apply hleg 0 i 0
      · obtain ⟨e, he⟩ := (acyc_isPrint_iff C (hch 0).1 i).1 hp
        exact ⟨(e, 0), Or.inl ⟨he, by decide, rfl⟩⟩
      · intro ho
        exact acyc_no_origin C (fun l => typeShadow C hC (ch l)) (fun n => (hch n).1) hall' 0 i 0 ho
          hp (by decide)
    rw [h0] at hz
    have hpA : C.IsPrint (C.occ (C.central (C.form D.typ)) (C.print (C.form D.typ) d0)) :=
      (acyc_isPrint_iff C hco _).2 ⟨d0, hd0m, Or.inl rfl⟩
    exact hne (hA0 ▸ hz _ hpA)
  classical
  have hn0 : (ch (Nat.find hex1 + 1)).typ ≠ C.central (C.form D.typ) := Nat.find_spec hex1
  have hlt : ∀ j ≤ Nat.find hex1, (ch j).typ = C.central (C.form D.typ) := by
    intro j hj
    cases j with
    | zero => exact h0typ
    | succ j =>
      by_contra h
      exact Nat.find_min hex1 (by omega : j < Nat.find hex1) h
  have hstep : ∀ j, (ch j).typ = C.central (C.form D.typ) → ∀ d : C.Side D.typ,
      C.marked (C.form D.typ) d → ∀ k : Fin 5, k ≠ 4 →
      acycCellv C hC (ch j) d.val k = acycCellv C hC (ch (j + 1)) d.val k := by
    intro j hj d hd k hk
    have hf : C.form (ch (j + 1)).typ = C.form D.typ := by rw [← (hch j).1, hj, hco]
    have hs' : C.central (C.form (ch (j + 1)).typ) = (ch j).typ := by rw [hf, hj]
    have hl' : C.kind (C.form (ch (j + 1)).typ) = .large := by rw [hf]; exact hlα
    have hd' := acyc_marked_cast C hf.symm d hd
    have := acyc_child_copy C hC (ch (j + 1)) (ch j).typ hs' hl' _ hd' k hk
    rw [← acycCellv_side, Fin.val_cast] at this
    rw [(hch j).2]
    exact this
  have htr : ∀ j ≤ Nat.find hex1, ∀ d : C.Side D.typ, C.marked (C.form D.typ) d →
      ∀ k : Fin 5, k ≠ 4 → acycCellv C hC (ch j) d.val k = D.cell d k := by
    intro j
    induction j with
    | zero =>
      intro _ d hd k hk
      rw [h0]
      exact acyc_child_copy C hC D _ rfl hlα d hd k hk
    | succ j ih =>
      intro hj d hd k hk
      rw [← ih (by omega) d hd k hk]
      exact (hstep j (hlt j (by omega)) d hd k hk).symm
  have hYf : C.form (ch (Nat.find hex1 + 1)).typ = C.form D.typ := by
    rw [← (hch _).1, hlt _ le_rfl, hco]
  have hYc : C.IsCentral (ch (Nat.find hex1 + 1)).typ :=
    ((C.g5_large_iff _).1 (by rw [hYf]; exact hlα)).symm
  have hYa : ¬ C.IsCyclic (ch (Nat.find hex1 + 1)).typ := by
    intro h
    apply hn0
    unfold MacroData.IsCyclic at h
    rw [hYf] at h
    exact h.symm
  have hYN := acyc_child_normal C hC (ch (Nat.find hex1 + 1 + 1)) (ch (Nat.find hex1 + 1)).typ
    (hch _).1
  rw [← (hch _).2] at hYN
  have hcellY : ∀ d : C.Side D.typ, C.marked (C.form D.typ) d → ∀ k : Fin 5, k ≠ 4 →
      acycCellv C hC (ch (Nat.find hex1 + 1)) d.val k = D.cell d k := by
    intro d hd k hk
    rw [← htr _ le_rfl d hd k hk]
    exact (hstep _ (hlt _ le_rfl) d hd k hk).symm
  have hYD := acyc_ident C hC D (ch (Nat.find hex1 + 1)) hcent hacyc hYc hYa hYf hDN hDI hYN.1
    hYN.2 hcellY
  refine ⟨fun n => ch (Nat.find hex1 + 1 + n), hYD, fun n => hch (Nat.find hex1 + 1 + n),
    fun n i k hne hno => hleg (Nat.find hex1 + 1 + n) i k hne (fun ho => hno ?_)⟩
  exact acyc_origin_shift C (fun l => typeShadow C hC (ch l)) (Nat.find hex1 + 1) _ i k ho n rfl

/-- **`lem:schedule-compose`, existence half** (strict analogue of `thm:compose`): every strictly
matched plane tiling of legal typed tiles has a strictly matched exact composition by legal
typed tiles. -/
theorem strict_compose_exists (hτ : τ.STS)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (C.Δ α).tiles))
    (T : PlaneTiling (strictProtoset C hC)) (hT : IsStrictMatched C hC T)
    (hL : AllStrictLegal C hC T) :
    ∃ T' : PlaneTiling (strictProtoset C hC), IsStrictMatched C hC T' ∧
      AllStrictLegal C hC T' ∧ (strictSubst C hC).IsComposition T' T := by
  sorry

end Composition

/-! ## Completeness (`lem:strict-presentation`) -/

section Completeness

variable (C : MacroCertificate P) (hC : C.Represents τ m)

/-- `lem:strict-presentation` (completeness, schedules): in an actual grouped level `T'` that is
side-to-side and whose scattered intermediate original levels `τ^j Δ T'`, `j ≤ m`, are
side-to-side, coincident whole fine outer sides of two parents carry equal schedules (a
layer-`j` side on the boundary of `sA` faces a single layer-`j` tile, which lies in the
neighbouring block). -/
theorem strict_actual_schedules_aligned (T' : PlaneTiling C.Q) (hT' : T'.SideToSide)
    (hlev : ∀ j ≤ m, SideToSideSet (τ.decomposeIter j (hC.groupedFamily.scatter T'.tiles))) :
    Alignment.SchedulesAligned τ hC.groupedFamily m T' := by
  sorry

/-- `lem:strict-presentation` (completeness, "origin chains give legal tiles"): every grouped
`σ'`-hierarchy lifts to compatible legal strict decorations (types from the positions in the
parent templates; generated cells fixed; a copied cell takes the value of the origin of its
source chain, or zero if there is none). -/
theorem strict_lift_decorations (seq' : ℕ → PlaneTiling C.Q)
    (hseq : ∀ n, C.σ.IsComposition (seq' (n + 1)) (seq' n)) :
    ∃ seq'' : ℕ → PlaneTiling (strictProtoset C hC),
      (∀ n, (strictDecoration C hC).toDecoration.project (seq'' n) = seq' n) ∧
      (∀ n, (strictSubst C hC).IsComposition (seq'' (n + 1)) (seq'' n)) ∧
      (∀ n, AllStrictLegal C hC (seq'' n)) := by
  sorry

/-- `lem:strict-presentation` (completeness, matching): if the grouped levels and the scattered
intermediate levels between consecutive grouped levels are side-to-side, the bottom level of a
legal strict lift is strictly matched (schedules by `strict_actual_schedules_aligned`; port
signals across persistent fault lines by induction up the levels, originless copied cells
being zero). -/
theorem strict_lift_matched (seq' : ℕ → PlaneTiling C.Q)
    (hseq : ∀ n, C.σ.IsComposition (seq' (n + 1)) (seq' n)) (hsts : ∀ n, (seq' n).SideToSide)
    (hlev : ∀ n, ∀ j ≤ m,
      SideToSideSet (τ.decomposeIter j (hC.groupedFamily.scatter (seq' (n + 1)).tiles)))
    (seq'' : ℕ → PlaneTiling (strictProtoset C hC))
    (hproj : ∀ n, (strictDecoration C hC).toDecoration.project (seq'' n) = seq' n)
    (hcomp : ∀ n, (strictSubst C hC).IsComposition (seq'' (n + 1)) (seq'' n))
    (hleg : ∀ n, AllStrictLegal C hC (seq'' n)) :
    IsStrictMatched C hC (seq'' 0) := by
  sorry

/-- Lifting an STS grouped hierarchy to a proper strict plane tiling (`lem:strict-presentation`,
completeness). -/
theorem strict_lift_hierarchy (seq' : ℕ → PlaneTiling C.Q)
    (hseq : ∀ n, C.σ.IsComposition (seq' (n + 1)) (seq' n)) (hsts : ∀ n, (seq' n).SideToSide)
    (hlev : ∀ n, ∀ j ≤ m,
      SideToSideSet (τ.decomposeIter j (hC.groupedFamily.scatter (seq' (n + 1)).tiles))) :
    ∃ T : PlaneTiling (strictProtoset C hC), (strictDecoration C hC).Proper T ∧
      (strictDecoration C hC).toDecoration.project T = seq' 0 := by
  obtain ⟨seq'', hproj, hcomp, hleg⟩ := strict_lift_decorations C hC seq' hseq
  exact ⟨seq'' 0, (strict_proper_iff C hC _).2
    ⟨strict_lift_matched C hC seq' hseq hsts hlev seq'' hproj hcomp hleg, hleg 0⟩, hproj 0⟩

end Completeness

/-! ## The strict presentation (`lem:strict-presentation`) -/

section Presentation

variable (C : MacroCertificate P) (hC : C.Represents τ m)

/-- `lem:strict-presentation`: every original form is a singleton group. -/
theorem strictSystem_singleton :
    ∀ p : P.Form, ∃ α, ((strictSystem C hC).GS.G.dissect α).tiles = {⟨p, 0⟩} :=
  hC.singleton

/-- `lem:strict-presentation`: the dissections stay side-to-side under all decompositions,
since every group is (up to translation) a set of tiles of a supertile (`inside_supertile`).
STS of `Δ α` with `τ.STS` alone does not suffice (see
`Substitution.STS.decomposeIter_sts_of_subset_supertile`). -/
theorem strictSystem_sts_dissections (hτ : τ.STS) :
    ∀ α j, SideToSideSet (τ.decomposeIter j ((strictSystem C hC).GS.G.dissect α).tiles) := by
  intro α j
  obtain ⟨n, p, v, h⟩ := hC.inside_supertile α
  exact Substitution.STS.decomposeIter_sts_of_subset_supertile hτ h j

/-- `lem:strict-presentation` (existence half of `lem:schedule-compose`): every proper strict
coloured plane tiling has an exact proper coloured composition. -/
theorem strictSystem_hasCompositions (hτ : τ.STS)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (C.Δ α).tiles)) :
    (strictSystem C hC).HasCompositions := by
  intro T hT
  obtain ⟨hM, hL⟩ := (strict_proper_iff C hC T).1 hT
  obtain ⟨T', hM', hL', hcomp⟩ := strict_compose_exists C hC hτ hΔ T hM hL
  exact ⟨T', (strict_proper_iff C hC T').2 ⟨hM', hL'⟩, hcomp⟩

/-- `lem:strict-presentation` (completeness): every grouped `σ'`-hierarchy whose levels and
intermediate original levels are side-to-side is the projection of a proper strict coloured
plane tiling. -/
theorem strictSystem_complete : (strictSystem C hC).Complete := by
  intro seq' hseq hsts hlev
  exact strict_lift_hierarchy C hC seq' hseq hsts hlev

end Presentation

/-- **The strict schedule system of a certificate** (`lem:strict-presentation`, modulo the
sorried pieces above): a certificate representing `τ` at the power `m` gives a strict schedule
system with singleton original groups, side-to-side dissections, exact proper compositions and
completeness.  With `existsMacroCertificate` this proves
`Alignment.exists_strict_schedule_system`. -/
theorem exists_strict_schedule_system_of_certificate (τ : Substitution P) (hτ : τ.STS)
    (C : MacroCertificate P) (m : ℕ) (hC : C.Represents τ m) :
    ∃ Sys : Alignment.StrictScheduleSystem τ,
      (∀ p : P.Form, ∃ α, (Sys.GS.G.dissect α).tiles = {⟨p, 0⟩}) ∧
      (∀ α j, SideToSideSet (τ.decomposeIter j (Sys.GS.G.dissect α).tiles)) ∧
      Sys.HasCompositions ∧ Sys.Complete :=
  ⟨strictSystem C hC, strictSystem_singleton C hC, strictSystem_sts_dissections C hC hτ,
    strictSystem_hasCompositions C hC hτ (strictSystem_sts_dissections C hC hτ),
    strictSystem_complete C hC⟩

end Strict

end Planned

end Tilings

end
