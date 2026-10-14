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

private theorem ecs_aux_push (x z nv : Pt) (ε δ : ℝ) (hz : dist z x < ε) (hδ : 0 < δ) (hn : nv ≠ 0)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∃ t : ℝ, 0 < t ∧ dist (z + (σ * t) • nv) z < δ ∧ dist (z + (σ * t) • nv) x < ε ∧
      inner ℝ (z + (σ * t) • nv - x) nv = inner ℝ (z - x) nv + σ * t * ‖nv‖ ^ 2 := by
  have hnp : 0 < ‖nv‖ := norm_pos_iff.mpr hn
  set r := min δ (ε - dist z x) with hr
  have hr0 : 0 < r := lt_min hδ (by linarith)
  have hq : 0 < r / (2 * ‖nv‖) := by positivity
  have h1 : dist (z + (σ * (r / (2 * ‖nv‖))) • nv) z = r / 2 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_mul]
    rcases hσ with rfl | rfl <;> simp [abs_of_pos hq] <;> field_simp
  refine ⟨r / (2 * ‖nv‖), hq, ?_, ?_, ?_⟩
  · rw [h1]; linarith [min_le_left δ (ε - dist z x)]
  · have := dist_triangle (z + (σ * (r / (2 * ‖nv‖))) • nv) z x
    linarith [min_le_right δ (ε - dist z x)]
  · rw [add_sub_right_comm, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp

private theorem ecs_aux_segment_compact (a b : Pt) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

private theorem ecs_aux_open_ne_left {a b x : Pt} (hab : a ≠ b) (hx : x ∈ openSegment ℝ a b) :
    x ≠ a := by
  rintro rfl
  exact hab ((left_mem_openSegment_iff).1 hx)

private theorem ecs_aux_open_ne_right {a b x : Pt} (hab : a ≠ b) (hx : x ∈ openSegment ℝ a b) :
    x ≠ b := by
  rintro rfl
  exact hab ((right_mem_openSegment_iff).1 hx)

private theorem ecs_aux_finRotate_ne {N : ℕ} (hN : 2 ≤ N) (x : Fin N) : finRotate N x ≠ x := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have := congrArg (· - x) h
  simp at this

private theorem ecs_aux_vertex_ne (D : PolygonalDisk) (i : Fin D.n) :
    D.vertex i ≠ D.vertex (finRotate _ i) := fun h =>
  ecs_aux_finRotate_ne (by have := D.three_le; omega) i (D.vertex_injective h).symm

/-- Points of a segment differ by multiples of its direction. -/
private theorem ecs_aux_inner_segment {a b x z nv : Pt} (hn : inner ℝ (b - a) nv = 0)
    (hx : x ∈ segment ℝ a b) (hz : z ∈ segment ℝ a b) : inner ℝ (z - x) nv = 0 := by
  rw [segment_eq_image'] at hx hz
  obtain ⟨t, -, rfl⟩ := hx
  obtain ⟨t', -, rfl⟩ := hz
  have : a + t' • (b - a) - (a + t • (b - a)) = (t' - t) • (b - a) := by module
  rw [this, inner_smul_left, hn]; simp

/-- Near a relative interior point of a side, the frontier of a polygonal disk lies on the
line of that side. -/
private theorem ecs_aux_frontier_local (D : PolygonalDisk) (i : Fin D.n) {x nv : Pt}
    (hx : x ∈ openSegment ℝ (D.vertex i) (D.vertex (finRotate _ i)))
    (hn : inner ℝ (D.vertex (finRotate _ i) - D.vertex i) nv = 0) :
    ∃ ε > 0, ∀ z, dist z x < ε → z ∈ frontier D.carrier → inner ℝ (z - x) nv = 0 := by
  have hab := ecs_aux_vertex_ne D i
  have hxa := ecs_aux_open_ne_left hab hx
  have hxb := ecs_aux_open_ne_right hab hx
  have hxs : x ∈ D.side i := openSegment_subset_segment _ _ _ hx
  have hev : ∀ᶠ z in nhds x, ∀ j : Fin D.n, j ≠ i → z ∉ D.side j := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall fun _ h => absurd hj h
    · have hxj : x ∉ D.side j := by
        intro hxj
        have := D.simple i j (Ne.symm hj) ⟨hxs, hxj⟩
        rcases this.1 with h | h
        · exact hxa h
        · exact hxb h
      filter_upwards [(ecs_aux_segment_compact _ _).isClosed.isOpen_compl.mem_nhds hxj] with z hz _
      exact hz
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, fun z hz hzf => ?_⟩
  rw [D.frontier_eq, Set.mem_iUnion] at hzf
  obtain ⟨j, hj⟩ := hzf
  by_cases hji : j = i
  · subst hji
    exact ecs_aux_inner_segment hn hxs hj
  · exact absurd hj (hball hz j hji)

/-- **Half-ball lemma.**  Near a relative interior point `x` of a side of a polygonal disk, one
open half-ball (with respect to a normal vector `nv` of the side) lies in the interior and the
other one outside the disk. -/
private theorem ecs_aux_half_ball (D : PolygonalDisk) (i : Fin D.n) {x nv : Pt}
    (hx : x ∈ openSegment ℝ (D.vertex i) (D.vertex (finRotate _ i)))
    (hn : inner ℝ (D.vertex (finRotate _ i) - D.vertex i) nv = 0) (hn0 : nv ≠ 0) :
    ∃ ε > 0, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z, dist z x < ε →
      (0 < σ * inner ℝ (z - x) nv → z ∈ interior D.carrier) ∧
      (σ * inner ℝ (z - x) nv < 0 → z ∉ D.carrier) := by
  obtain ⟨ε, hε, hloc⟩ := ecs_aux_frontier_local D i hx hn
  have hcl : IsClosed D.carrier := D.compact.isClosed
  have hxs : x ∈ D.side i := openSegment_subset_segment _ _ _ hx
  have hxf : x ∈ frontier D.carrier := by
    rw [D.frontier_eq, Set.mem_iUnion]; exact ⟨i, hxs⟩
  let H : ℝ → Set Pt := fun σ => {z | dist z x < ε ∧ 0 < σ * inner ℝ (z - x) nv}
  have hH : ∀ σ, H σ ⊆ interior D.carrier ∨ H σ ⊆ D.carrierᶜ := by
    intro σ
    have hconv : Convex ℝ (H σ) := by
      intro a ha b hb s t hs ht hst
      refine ⟨?_, ?_⟩
      · have := (convex_ball x ε) (show a ∈ Metric.ball x ε from ha.1)
          (show b ∈ Metric.ball x ε from hb.1) hs ht hst
        exact this
      · have he : s • a + t • b - x = s • (a - x) + t • (b - x) := by
          calc s • a + t • b - x = s • a + t • b - (s + t) • x := by rw [hst, one_smul]
            _ = s • (a - x) + t • (b - x) := by module
        show 0 < σ * inner ℝ (s • a + t • b - x) nv
        rw [he, inner_add_left, inner_smul_left, inner_smul_left]
        simp only [RCLike.conj_to_real]
        have h1 : 0 < σ * inner ℝ (a - x) nv := ha.2
        have h2 : 0 < σ * inner ℝ (b - x) nv := hb.2
        have hre : σ * (s * inner ℝ (a - x) nv + t * inner ℝ (b - x) nv) =
            s * (σ * inner ℝ (a - x) nv) + t * (σ * inner ℝ (b - x) nv) := by ring
        rw [hre]
        rcases hs.lt_or_eq with hs' | hs'
        · nlinarith [mul_nonneg ht h2.le, mul_pos hs' h1]
        · subst hs'
          have : t = 1 := by linarith
          subst this; simpa using h2
    have hopen : IsOpen (H σ) := by
      apply IsOpen.inter
      · exact Metric.isOpen_ball
      · have hc : Continuous fun z : Pt => σ * inner ℝ (z - x) nv :=
          continuous_const.mul ((continuous_id.sub continuous_const).inner continuous_const)
        exact isOpen_lt continuous_const hc
    refine hconv.isPreconnected.subset_or_subset isOpen_interior hcl.isOpen_compl
      (Set.disjoint_compl_right_iff_subset.2 interior_subset) ?_
    intro z hz
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hcon
    have hzf : z ∈ frontier D.carrier := ⟨subset_closure hcon.2, hcon.1⟩
    have := hloc z hz.1 hzf
    have h2 := hz.2
    rw [this, mul_zero] at h2
    exact lt_irrefl _ h2
  have hpush : ∀ z, dist z x < ε → inner ℝ (z - x) nv = 0 → ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      ∀ δ > 0, ∃ y ∈ H σ, dist y z < δ := by
    intro z hz h0 σ hσ δ hδ
    obtain ⟨t, ht, hd, hdx, hi⟩ := ecs_aux_push x z nv ε δ hz hδ hn0 σ hσ
    refine ⟨_, ⟨hdx, ?_⟩, hd⟩
    rw [hi, h0]
    have hnp : 0 < ‖nv‖ := norm_pos_iff.mpr hn0
    rcases hσ with rfl | rfl <;> nlinarith [sq_pos_of_pos hnp]
  have hsign : ∀ z, dist z x < ε → inner ℝ (z - x) nv ≠ 0 → z ∈ H 1 ∨ z ∈ H (-1) := by
    intro z hz h0
    rcases lt_or_gt_of_ne h0 with h | h
    · right; exact ⟨hz, by linarith⟩
    · left; exact ⟨hz, by linarith⟩
  rcases hH 1 with h1 | h1 <;> rcases hH (-1) with h2 | h2
  · exfalso
    have hball : Metric.ball x ε ⊆ D.carrier := by
      intro z hz
      by_cases h0 : inner ℝ (z - x) nv = 0
      · rw [← D.regular_closed, Metric.mem_closure_iff]
        intro δ hδ
        obtain ⟨y, hy, hyd⟩ := hpush z hz h0 1 (Or.inl rfl) δ hδ
        exact ⟨y, h1 hy, by rw [dist_comm]; exact hyd⟩
      · rcases hsign z hz h0 with h | h
        · exact interior_subset (h1 h)
        · exact interior_subset (h2 h)
    exact hxf.2 (interior_maximal hball Metric.isOpen_ball (Metric.mem_ball_self hε))
  · refine ⟨ε, hε, 1, Or.inl rfl, fun z hz => ⟨fun h => h1 ⟨hz, h⟩, fun h => h2 ⟨hz, by linarith⟩⟩⟩
  · refine ⟨ε, hε, -1, Or.inr rfl, fun z hz => ⟨fun h => h2 ⟨hz, h⟩, fun h => h1 ⟨hz, by linarith⟩⟩⟩
  · exfalso
    have hxc : x ∈ D.carrier := hcl.closure_eq ▸ frontier_subset_closure hxf
    rw [← D.regular_closed, Metric.mem_closure_iff] at hxc
    obtain ⟨w, hw, hwd⟩ := hxc ε hε
    rw [dist_comm] at hwd
    by_cases h0 : inner ℝ (w - x) nv = 0
    · obtain ⟨ρ, hρ, hρs⟩ := Metric.isOpen_iff.1 isOpen_interior w hw
      obtain ⟨y, hy, hyd⟩ := hpush w hwd h0 1 (Or.inl rfl) ρ hρ
      exact h1 hy (interior_subset (hρs hyd))
    · rcases hsign w hwd h0 with h | h
      · exact h1 h (interior_subset hw)
      · exact h2 h (interior_subset hw)

/-- The affine map `z ↦ w + θ • z` as a homeomorphism. -/
private def ecs_aux_homeo (θ : ℝ) (hθ : θ ≠ 0) (w : Pt) : Pt ≃ₜ Pt :=
  (Homeomorph.smulOfNeZero θ hθ).trans (Homeomorph.addLeft w)

private theorem ecs_aux_homeo_apply (θ : ℝ) (hθ : θ ≠ 0) (w z : Pt) :
    ecs_aux_homeo θ hθ w z = w + θ • z := rfl

private theorem ecs_aux_homeo_image (θ : ℝ) (hθ : θ ≠ 0) (w : Pt) (s : Set Pt) :
    ecs_aux_homeo θ hθ w '' s = w +ᵥ θ • s := by
  ext z
  simp only [Set.mem_image, ecs_aux_homeo_apply, Set.mem_vadd_set, Set.mem_smul_set, vadd_eq_add]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨θ • y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩

private theorem ecs_aux_homeo_segment (θ : ℝ) (hθ : θ ≠ 0) (w a b : Pt) :
    ecs_aux_homeo θ hθ w '' segment ℝ a b = segment ℝ (w + θ • a) (w + θ • b) := by
  rw [segment_eq_image', segment_eq_image', Set.image_image]
  refine Set.image_congr fun t _ => ?_
  rw [ecs_aux_homeo_apply]; module

/-- The image of a polygonal disk under `z ↦ w + θ • z`, `θ ≠ 0`. -/
private def ecs_aux_affDisk (D : PolygonalDisk) (θ : ℝ) (hθ : θ ≠ 0) (w : Pt) : PolygonalDisk where
  carrier := w +ᵥ θ • D.carrier
  n := D.n
  three_le := D.three_le
  vertex k := w + θ • D.vertex k
  vertex_injective k l h := D.vertex_injective (smul_right_injective Pt hθ (add_left_cancel h))
  compact := by
    rw [← ecs_aux_homeo_image θ hθ w]; exact D.compact.image (ecs_aux_homeo θ hθ w).continuous
  interior_nonempty := by
    rw [← ecs_aux_homeo_image θ hθ w, ← Homeomorph.image_interior]
    exact D.interior_nonempty.image _
  regular_closed := by
    rw [← ecs_aux_homeo_image θ hθ w, ← Homeomorph.image_interior, ← Homeomorph.image_closure,
      D.regular_closed]
  interior_pathConnected := by
    rw [← ecs_aux_homeo_image θ hθ w, ← Homeomorph.image_interior]
    exact D.interior_pathConnected.image (ecs_aux_homeo θ hθ w).continuous
  frontier_eq := by
    rw [← ecs_aux_homeo_image θ hθ w, ← Homeomorph.image_frontier, D.frontier_eq, Set.image_iUnion]
    simp only [ecs_aux_homeo_segment]
  simple i j hij := by
    have := Set.image_mono (f := ecs_aux_homeo θ hθ w) (D.simple i j hij)
    rw [Set.image_inter (ecs_aux_homeo θ hθ w).injective,
      Set.image_inter (ecs_aux_homeo θ hθ w).injective,
      ecs_aux_homeo_segment, ecs_aux_homeo_segment] at this
    simpa [Set.image_insert_eq, ecs_aux_homeo_apply] using this

private theorem ecs_aux_affDisk_side (D : PolygonalDisk) (θ : ℝ) (hθ : θ ≠ 0) (w : Pt)
    (i : Fin D.n) : (ecs_aux_affDisk D θ hθ w).side i = w +ᵥ θ • D.side i := by
  rw [← ecs_aux_homeo_image θ hθ w, PolygonalDisk.side, PolygonalDisk.side, ecs_aux_homeo_segment]
  rfl

private theorem ecs_aux_exists_normal (v : Pt) (hv : v ≠ 0) :
    ∃ nv : Pt, nv ≠ 0 ∧ inner ℝ v nv = 0 := by
  refine ⟨!₂[-(v 1), v 0], ?_, ?_⟩
  · intro h
    apply hv
    have h0 := congrFun (congrArg (fun w : Pt => (w : Fin 2 → ℝ)) h) 0
    have h1 := congrFun (congrArg (fun w : Pt => (w : Fin 2 → ℝ)) h) 1
    simp at h0 h1
    ext i; fin_cases i <;> simp [h0, h1]
  · simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

/-- The midpoint of a nondegenerate subsegment is a relative interior point, and normals of
the subsegment are normals of the segment. -/
private theorem ecs_aux_sub_segment {a b p q : Pt} (hpq : p ≠ q)
    (hs : segment ℝ p q ⊆ segment ℝ a b) :
    midpoint ℝ p q ∈ openSegment ℝ a b ∧
      ∀ nv, inner ℝ (q - p) nv = 0 → inner ℝ (b - a) nv = 0 := by
  have hp := hs (left_mem_segment ℝ p q)
  have hq := hs (right_mem_segment ℝ p q)
  rw [segment_eq_image'] at hp hq
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hp
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hq
  have hst : s ≠ t := by rintro rfl; exact hpq rfl
  have hba : b - a ≠ 0 := by
    intro h; apply hpq; rw [h]; simp
  have hdiff : a + t • (b - a) - (a + s • (b - a)) = (t - s) • (b - a) := by module
  have hmid : midpoint ℝ (a + s • (b - a)) (a + t • (b - a)) = a + ((s + t) / 2) • (b - a) := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]; module
  refine ⟨?_, fun nv hn => ?_⟩
  · rw [hmid, openSegment_eq_image']
    refine ⟨(s + t) / 2, ⟨?_, ?_⟩, rfl⟩
    · rcases lt_or_gt_of_ne hst with h | h <;> linarith
    · rcases lt_or_gt_of_ne hst with h | h <;> linarith
  · rw [hdiff, inner_smul_left] at hn
    simp only [RCLike.conj_to_real, mul_eq_zero] at hn
    rcases hn with h | h
    · exact absurd (sub_eq_zero.1 h).symm hst
    · exact h

/-- The half-ball lemma at the midpoint of a nondegenerate segment contained in a side. -/
private theorem ecs_aux_half_ball_seg (D : PolygonalDisk) (i : Fin D.n) {p q nv : Pt} (hpq : p ≠ q)
    (hs : segment ℝ p q ⊆ D.side i) (hn : inner ℝ (q - p) nv = 0) (hn0 : nv ≠ 0) :
    ∃ ε > 0, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z, dist z (midpoint ℝ p q) < ε →
      (0 < σ * inner ℝ (z - midpoint ℝ p q) nv → z ∈ interior D.carrier) ∧
      (σ * inner ℝ (z - midpoint ℝ p q) nv < 0 → z ∉ D.carrier) := by
  obtain ⟨hx, hnn⟩ := ecs_aux_sub_segment hpq hs
  exact ecs_aux_half_ball D i hx (hnn nv hn) hn0

/-- The translate of a polygonal disk. -/
private def ecs_aux_trDisk (D : PolygonalDisk) (w : Pt) : PolygonalDisk :=
  ecs_aux_affDisk D 1 one_ne_zero w

private theorem ecs_aux_trDisk_carrier (D : PolygonalDisk) (w : Pt) :
    (ecs_aux_trDisk D w).carrier = w +ᵥ D.carrier := by
  show w +ᵥ (1 : ℝ) • D.carrier = _
  rw [one_smul]

private theorem ecs_aux_trDisk_side (D : PolygonalDisk) (w : Pt) (i : Fin D.n) :
    (ecs_aux_trDisk D w).side i = w +ᵥ D.side i := by
  show (ecs_aux_affDisk D 1 one_ne_zero w).side i = _
  rw [ecs_aux_affDisk_side, one_smul]

/-- A separated subset of a ball is finite. -/
private theorem ecs_aux_sep_finite {S : Set Pt} {x : Pt} {M r : ℝ} (hr : 0 < r)
    (hS : S ⊆ Metric.closedBall x M) (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → r ≤ dist a b) : S.Finite := by
  have htb : TotallyBounded S := (isCompact_closedBall x M).totallyBounded.subset hS
  obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.1 htb (r / 2) (by positivity)
  refine (ht.biUnion fun y _ => (?_ : (S ∩ Metric.ball y (r / 2)).Finite)).subset ?_
  · refine Set.Subsingleton.finite fun a ha b hb => ?_
    by_contra hab
    have := hsep a ha.1 b hb.1 hab
    have h1 := Metric.mem_ball.1 ha.2
    have h2 := Metric.mem_ball.1 hb.2
    have := dist_triangle_right a b y
    linarith
  · intro a ha
    obtain ⟨y, hy, hay⟩ := Set.mem_iUnion₂.1 (hcov ha)
    exact Set.mem_iUnion₂.2 ⟨y, hy, ha, hay⟩

/-- Local finiteness of plane tilings: finitely many tiles meet a ball. -/
private theorem ecs_aux_locally_finite {Pr : Protoset} (T : PlaneTiling Pr) (x : Pt) (ρ : ℝ) :
    {Y ∈ T.tiles | (Y.carrier ∩ Metric.ball x ρ).Nonempty}.Finite := by
  let S : Pr.Form → Set Pt := fun f =>
    {a | (⟨f, a⟩ : PlacedTile Pr) ∈ T.tiles ∧ ((⟨f, a⟩ : PlacedTile Pr).carrier ∩ Metric.ball x ρ).Nonempty}
  have hfin : ∀ f, (S f).Finite := by
    intro f
    obtain ⟨R, hR⟩ := (Pr.disk f).compact.isBounded.subset_closedBall 0
    obtain ⟨c, hc⟩ := (Pr.disk f).interior_nonempty
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior c hc
    refine ecs_aux_sep_finite (M := ρ + R) (x := x) hr ?_ ?_
    · rintro a ⟨-, z, hz, hzx⟩
      obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.1 hz
      have hy' := Metric.mem_closedBall.1 (hR hy)
      rw [dist_zero_right] at hy'
      rw [Metric.mem_closedBall]
      have h1 := Metric.mem_ball.1 hzx
      have : dist a x ≤ dist (a + y) x + ‖y‖ := by
        rw [dist_eq_norm, dist_eq_norm]
        calc ‖a - x‖ = ‖(a + y - x) - y‖ := by congr 1; abel
          _ ≤ ‖a + y - x‖ + ‖y‖ := norm_sub_le _ _
      simp only [vadd_eq_add] at h1
      linarith
    · intro a ha b hb hab
      by_contra hlt
      push_neg at hlt
      have hne : (⟨f, a⟩ : PlacedTile Pr) ≠ ⟨f, b⟩ := fun h => hab (by cases h; rfl)
      have hd := T.disjoint ha.1 hb.1 hne
      set z := midpoint ℝ (a + c) (b + c)
      have hmem : ∀ e, dist (a + c) (b + c) < 2 * r → (e = a ∨ e = b) →
          z ∈ interior ((⟨f, e⟩ : PlacedTile Pr).carrier) := by
        intro e hdist he
        show z ∈ interior (e +ᵥ (Pr.disk f).carrier)
        rw [interior_vadd]
        refine Set.mem_vadd_set.2 ⟨z - e, hball ?_, by simp⟩
        rw [Metric.mem_ball]
        have h1 : dist z (a + c) = dist (a + c) (b + c) / 2 := by
          rw [dist_comm]; exact dist_left_midpoint (𝕜 := ℝ) _ _ |>.trans (by simp [div_eq_inv_mul])
        have h2 : dist z (b + c) = dist (a + c) (b + c) / 2 := by
          rw [dist_comm]; exact dist_right_midpoint (𝕜 := ℝ) _ _ |>.trans (by simp [div_eq_inv_mul])
        rcases he with rfl | rfl
        · have : dist (z - e) c = dist z (e + c) := by
            rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
          rw [this, h1]; linarith
        · have : dist (z - e) c = dist z (e + c) := by
            rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
          rw [this, h2]; linarith
      have hdist : dist (a + c) (b + c) < 2 * r := by
        rw [dist_add_right]; linarith
      exact Set.disjoint_left.1 hd (hmem a hdist (Or.inl rfl)) (hmem b hdist (Or.inr rfl))
  refine (Set.finite_iUnion fun f => (hfin f).image fun a => (⟨f, a⟩ : PlacedTile Pr)).subset ?_
  rintro ⟨f, a⟩ hY
  exact Set.mem_iUnion.2 ⟨f, a, hY, rfl⟩

private theorem ecs_aux_tile_carrier {Pr : Protoset} (X : PlacedTile Pr) :
    (ecs_aux_trDisk (Pr.disk X.form) X.anchor).carrier = X.carrier := ecs_aux_trDisk_carrier _ _

private theorem ecs_aux_tile_side {Pr : Protoset} (X : PlacedTile Pr) (i : Fin (Pr.disk X.form).n) :
    (ecs_aux_trDisk (Pr.disk X.form) X.anchor).side i = X.side i := ecs_aux_trDisk_side _ _ _

private theorem ecs_aux_tile_closed {Pr : Protoset} (X : PlacedTile Pr) : IsClosed X.carrier := by
  rw [← ecs_aux_tile_carrier]; exact (ecs_aux_trDisk _ _).compact.isClosed

/-- **Coincident sides.**  Step towards `exists_coincident_side`: the same statement, proved
directly (local half-ball separation at a relative-interior point of the side, local finiteness
of the tiling, and a pigeonhole argument on an infinite family of points of the side). -/
private theorem exists_coincident_side_aux_main {Pr : Protoset} (T : PlaneTiling Pr)
    (hT : T.SideToSide) {X : PlacedTile Pr} (hX : X ∈ T.tiles) (i : Fin (Pr.disk X.form).n) :
    ∃ Y ∈ T.tiles, Y ≠ X ∧ ∃ j : Fin (Pr.disk Y.form).n, Y.side j = X.side i := by
  classical
  set D := ecs_aux_trDisk (Pr.disk X.form) X.anchor
  set a := D.vertex i
  set b := D.vertex (finRotate _ i)
  have hab : a ≠ b := ecs_aux_vertex_ne D i
  have hDs : D.side i = segment ℝ a b := rfl
  obtain ⟨nv, hn0, hn⟩ := ecs_aux_exists_normal (b - a) (sub_ne_zero.2 hab.symm)
  obtain ⟨ε, hε, σ, hσ, hb⟩ := ecs_aux_half_ball_seg D i hab hDs.symm.subset hn hn0
  set x := midpoint ℝ a b
  rw [ecs_aux_tile_carrier] at hb
  set F := {Y ∈ T.tiles | (Y.carrier ∩ Metric.ball x ε).Nonempty}
  have hF : F.Finite := ecs_aux_locally_finite T x ε
  have hnp : 0 < ‖b - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hab.symm)
  set δ := min (1 / 2 : ℝ) (ε / (2 * ‖b - a‖))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  set J := (fun t : ℝ => x + t • (b - a)) '' Set.Ioo (-δ) δ
  have hxeq : x = a + (1 / 2 : ℝ) • (b - a) := by
    show midpoint ℝ a b = _
    rw [midpoint_eq_smul_add, invOf_eq_inv]; module
  have hJ : ∀ z ∈ J, z ∈ X.side i ∧ dist z x < ε ∧ inner ℝ (z - x) nv = 0 := by
    rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
    have hta : |t| < δ := abs_lt.2 ⟨ht1, ht2⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← ecs_aux_tile_side, hDs, segment_eq_image']
      refine ⟨1 / 2 + t, ⟨?_, ?_⟩, by rw [hxeq]; module⟩
      · linarith [min_le_left (1 / 2 : ℝ) (ε / (2 * ‖b - a‖))]
      · linarith [min_le_left (1 / 2 : ℝ) (ε / (2 * ‖b - a‖))]
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      have h1 : |t| < ε / (2 * ‖b - a‖) := lt_of_lt_of_le hta (min_le_right _ _)
      have h2 : |t| * ‖b - a‖ < ε / (2 * ‖b - a‖) * ‖b - a‖ :=
        mul_lt_mul_of_pos_right h1 hnp
      have h3 : ε / (2 * ‖b - a‖) * ‖b - a‖ = ε / 2 := by field_simp
      linarith
    · rw [add_sub_cancel_left, inner_smul_left, hn]; simp
  have hJinf : J.Infinite := by
    refine (Set.Ioo_infinite (by linarith)).image fun t _ s _ hts => ?_
    exact smul_left_injective ℝ (sub_ne_zero.2 hab.symm) (add_left_cancel hts)
  -- every point of `J` lies on a side of another tile meeting the ball
  have hcov : ∀ z ∈ J, ∃ Y ∈ F, Y ≠ X ∧ ∃ j : Fin (Pr.disk Y.form).n, z ∈ Y.side j := by
    intro z hzJ
    obtain ⟨-, hzx, hz0⟩ := hJ z hzJ
    have hmem : ∃ Y ∈ F, Y ≠ X ∧ z ∈ Y.carrier := by
      by_contra hcon
      push_neg at hcon
      have hev : ∀ᶠ y in nhds z, ∀ Y ∈ F, Y ≠ X → y ∉ Y.carrier := by
        rw [Filter.eventually_all_finite hF]
        intro Y hY
        by_cases hYX : Y = X
        · exact Filter.Eventually.of_forall fun _ h => absurd hYX h
        · filter_upwards [(ecs_aux_tile_closed Y).isOpen_compl.mem_nhds (hcon Y hY hYX)] with y hy _
          exact hy
      obtain ⟨η, hη, hηs⟩ := Metric.eventually_nhds_iff.1 hev
      have hσ' : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
      obtain ⟨t, ht, hd, hdx, hi⟩ := ecs_aux_push x z nv ε η hzx hη hn0 (-σ) hσ'
      set y := z + (-σ * t) • nv
      have hneg : σ * inner ℝ (y - x) nv < 0 := by
        rw [hi, hz0]
        have := sq_pos_of_pos (norm_pos_iff.2 hn0)
        rcases hσ with rfl | rfl <;> nlinarith
      have hyX : y ∉ X.carrier := (hb y hdx).2 hneg
      have hyU : y ∈ support T.tiles := by rw [T.cover]; trivial
      obtain ⟨Y, hY, hyY⟩ := Set.mem_iUnion₂.1 hyU
      have hYX : Y ≠ X := by rintro rfl; exact hyX hyY
      exact hηs hd Y ⟨hY, y, hyY, Metric.mem_ball.2 hdx⟩ hYX hyY
    obtain ⟨Y, hYF, hYX, hzY⟩ := hmem
    refine ⟨Y, hYF, hYX, ?_⟩
    have hzi : z ∉ interior Y.carrier := by
      intro hzi
      obtain ⟨η, hη, hηs⟩ := Metric.isOpen_iff.1 isOpen_interior z hzi
      obtain ⟨t, ht, hd, hdx, hi⟩ := ecs_aux_push x z nv ε η hzx hη hn0 σ hσ
      have hpos : 0 < σ * inner ℝ (z + (σ * t) • nv - x) nv := by
        rw [hi, hz0]
        have := sq_pos_of_pos (norm_pos_iff.2 hn0)
        rcases hσ with rfl | rfl <;> nlinarith
      have h1 := (hb _ hdx).1 hpos
      have h2 := hηs hd
      exact Set.disjoint_left.1 (T.disjoint hYF.1 hX hYX) h2 h1
    have hzf : z ∈ frontier (ecs_aux_trDisk (Pr.disk Y.form) Y.anchor).carrier := by
      rw [ecs_aux_tile_carrier]
      exact ⟨subset_closure hzY, hzi⟩
    rw [(ecs_aux_trDisk (Pr.disk Y.form) Y.anchor).frontier_eq, Set.mem_iUnion] at hzf
    obtain ⟨j, hj⟩ := hzf
    exact ⟨j, by rw [← ecs_aux_tile_side]; exact hj⟩
  -- pigeonhole: some side of another tile contains two points of `J`
  have hpig : ∃ Y ∈ F, Y ≠ X ∧ ∃ j : Fin (Pr.disk Y.form).n,
      ¬ (Y.side j ∩ J).Subsingleton := by
    by_contra hcon
    push_neg at hcon
    apply hJinf
    have hF' : {Y | Y ∈ F ∧ Y ≠ X}.Finite := hF.subset fun Y hY => hY.1
    refine (hF'.biUnion fun Y hY =>
      Set.finite_iUnion fun j => (hcon Y hY.1 hY.2 j).finite).subset ?_
    intro z hz
    obtain ⟨Y, hYF, hYX, j, hj⟩ := hcov z hz
    exact Set.mem_iUnion₂.2 ⟨Y, ⟨hYF, hYX⟩, Set.mem_iUnion.2 ⟨j, hj, hz⟩⟩
  obtain ⟨Y, hYF, hYX, j, hns⟩ := hpig
  obtain ⟨z₁, ⟨hz₁Y, hz₁J⟩, z₂, ⟨hz₂Y, hz₂J⟩, hz₁₂⟩ := Set.not_subsingleton_iff.1 hns
  refine ⟨Y, hYF.1, hYX, j, hT Y hYF.1 X hX j i ⟨z₁, z₂, hz₁₂, ?_⟩⟩
  have hcY : Convex ℝ (Y.side j) := by
    rw [← ecs_aux_tile_side]; exact convex_segment _ _
  have hcX : Convex ℝ (X.side i) := by
    rw [← ecs_aux_tile_side]; exact convex_segment _ _
  exact Set.subset_inter (hcY.segment_subset hz₁Y hz₂Y)
    (hcX.segment_subset (hJ z₁ hz₁J).1 (hJ z₂ hz₂J).1)

/-- In a side-to-side plane tiling every listed side of a tile coincides with a listed side of
another tile (plane coverage, local finiteness and disjoint interiors; classical planar
topology).  Used to exclude inert decorations from proper tilings (`lem:glues`) and in the
assembly argument. -/
theorem exists_coincident_side {Pr : Protoset} (T : PlaneTiling Pr)
    (hT : T.SideToSide) {X : PlacedTile Pr} (hX : X ∈ T.tiles) (i : Fin (Pr.disk X.form).n) :
    ∃ Y ∈ T.tiles, Y ≠ X ∧ ∃ j : Fin (Pr.disk Y.form).n, Y.side j = X.side i := by
  exact exists_coincident_side_aux_main T hT hX i

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
reconstructed parent and scaling down by `θ`.  The reconstructed parent of a block has the type
`h.1` of a common boundary header `h` of the block (`lem:comp/reconstruction`).  Repair of
14 October 2026: the type was an arbitrary witness before, and a relabelled parent of the same
form satisfied the old definition without being normal and identity-correct (codex). -/
def IsStrictReconstruction {T : PlaneTiling (strictProtoset C hC)}
    (part : StrictMacroPartition C hC T) (T' : PlaneTiling (strictProtoset C hC)) : Prop :=
  (∀ X ∈ T'.tiles, ∃ j, (part.block j).v = C.σ.θ • X.anchor ∧
      ∃ h, StrictCommonHeader C hC (part.block j) h ∧
        X.form = StrictForm.typed (strictReconstruct C hC (part.block j) h.1)) ∧
  (∀ j, ∃ X ∈ T'.tiles, (part.block j).v = C.σ.θ • X.anchor ∧
      ∃ h, StrictCommonHeader C hC (part.block j) h ∧
        X.form = StrictForm.typed (strictReconstruct C hC (part.block j) h.1))

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

private lemma strictLegal_properties_step1_parent_HasOrigin_shift_mp (ch : ℕ → StrictDecTile C hC) :
    ∀ ch' n i k, HasOrigin C ch' n i k → ∀ hch' : ch' = (fun l => typeShadow C hC (ch (l + 1))),
    HasOrigin C (fun l => typeShadow C hC (ch l)) (n + 1) (by subst hch'; exact i) k := by
  intro ch' n i k h
  induction h with
  | origin n' i' k' heq =>
    intro hch'
    subst hch'
    exact HasOrigin.origin _ _ _ heq
  | step n' i' k' d k'' hmem horig ih =>
    intro hch'
    subst hch'
    exact HasOrigin.step _ _ _ _ _ hmem (ih rfl)

private lemma strictLegal_properties_step1_parent_HasOrigin_shift_mpr
    (ch : ℕ → StrictDecTile C hC) :
    ∀ ch' n i k, HasOrigin C ch' n i k → ∀ hch' : ch' = (fun l => typeShadow C hC (ch l)),
    ∀ n0 : ℕ, ∀ hn0 : n = n0 + 1,
    HasOrigin C (fun l => typeShadow C hC (ch (l + 1))) n0
      (by subst hn0; subst hch'; exact i) k := by
  intro ch' n i k h
  induction h with
  | origin n' i' k' heq =>
    intro hch' n0 hn0
    subst hn0 hch'
    exact HasOrigin.origin _ _ _ heq
  | step n' i' k' d k'' hmem horig ih =>
    intro hch' n0 hn0
    subst hn0 hch'
    exact HasOrigin.step _ _ _ _ _ hmem (ih rfl _ rfl)

private lemma strictLegal_properties_step1_parent_HasOrigin_shift_aux (ch : ℕ → StrictDecTile C hC)
    (n : ℕ) (i : C.Side (ch (n + 1)).typ) (k : Fin 5) :
    HasOrigin C (fun l => typeShadow C hC (ch (l + 1))) n i k ↔
    HasOrigin C (fun l => typeShadow C hC (ch l)) (n + 1) i k := by
  constructor
  · intro h
    exact strictLegal_properties_step1_parent_HasOrigin_shift_mp C hC ch _ _ _ _ h rfl
  · intro h
    exact strictLegal_properties_step1_parent_HasOrigin_shift_mpr C hC ch _ _ _ _ h rfl _ rfl

private lemma strictLegal_properties_step1_parent_HasOrigin_shift (ch : ℕ → StrictDecTile C hC)
    (n : ℕ) (i : C.Side (ch (n + 1)).typ) (k : Fin 5) :
    StrictHasOrigin C hC (fun l => ch (l + 1)) n i k ↔ StrictHasOrigin C hC ch (n + 1) i k := by
  dsimp [StrictHasOrigin]
  exact strictLegal_properties_step1_parent_HasOrigin_shift_aux C hC ch n i k

/-- Step 1 of the blueprint proof of `strictLegal_properties`: deleting the first tile of
an infinite strict legality chain yields a legal strict parent of the given tile. -/
private lemma strictLegal_properties_step1_parent (A : StrictDecTile C hC)
    (hA : StrictLegal C hC A) :
    ∃ B, StrictLegal C hC B ∧ IsStrictChildOf C hC B A := by
  obtain ⟨ch, hch0, hchild, hleg⟩ := hA
  use ch 1
  constructor
  · use (fun n => ch (n + 1))
    refine ⟨rfl, fun n => hchild (n + 1), ?_⟩
    intro n i k hcs hno
    apply hleg (n + 1) i k hcs
    intro h
    exact hno ((strictLegal_properties_step1_parent_HasOrigin_shift C hC ch n i k).mpr h)
  · rw [← hch0]
    exact hchild 0

/-- Step 2 of the blueprint proof of `strictLegal_properties`: the generated child clauses
force strict normality and identity-correctness of a child of any parent. -/
private lemma strictLegal_properties_step2_child_normal (B A : StrictDecTile C hC)
    (hBA : IsStrictChildOf C hC B A) :
    IsStrictNormal C hC A ∧ IsStrictIdentityCorrect C hC A := by
  have hs : C.owner A.typ = C.form B.typ := hBA.1
  have hchild : A = strictChild C hC B A.typ := hBA.2
  have isPrint_iff : ∀ (β : C.Q.Form), C.owner A.typ = β → ∀ i : C.Side A.typ,
      C.IsPrint (C.occ A.typ i) ↔
        ∃ d : Fin (C.Q.disk β).n, C.IsPrintOf β d (C.occ A.typ i) := by
    intro β hβ i
    subst β
    rfl
  have not_on_path : ∀ (β : C.Q.Form), C.owner A.typ = β → ∀ (i : C.Side A.typ),
      ¬ C.IsMarked (C.occ A.typ i) → ∀ (d : Fin (C.Q.disk β).n) (j : Fin 5),
        C.occ A.typ i ∉ C.path β d j := by
    intro β hβ i hm d j hmem
    subst β
    by_cases hg : C.IsGenuinePath (C.owner A.typ) d j
    · exact hm (C.g7_marking _ (Or.inr (Or.inr (Or.inr ⟨d, j, hg, hmem⟩))))
    · rw [C.g4_path_trivial _ d j hg, Option.mem_toList] at hmem
      have hmem' : C.occ A.typ i ∈ C.outerList _ d :=
        List.mem_iff_getElem?.mpr ⟨_, hmem⟩
      exact hm (C.g7_marking _ (Or.inl ((C.g3_outerList_mem _ d _).1 hmem').2.1))
  have hcells := strictChild_cells C hC B A.typ hs
  have key : ∀ (i : C.Side A.typ) (k : Fin 5),
      IsStrictLocal C (C.occ A.typ i) k →
        (strictChild C hC B A.typ).cell i k =
          strictPrescribedCell C hC (C.occ A.typ i) k := by
    intro i k hloc
    by_cases hp : C.IsPrint (C.occ A.typ i)
    · obtain ⟨d, hd⟩ := (isPrint_iff (C.form B.typ) hs i).1 hp
      have hin := isInner_of_isPrintOf C hd
      rcases hloc with (hnm | ⟨-, -, rfl⟩ | ⟨-, ⟨-, hnp⟩, -⟩) | ⟨hout, -⟩
      · exact absurd (C.g7_marking _ (Or.inr (Or.inr (Or.inl hp)))) hnm
      · rw [((hcells i).1 d hd).2]
        simp [strictPrescribedCell, hp]
      · exact absurd hp hnp
      · exact absurd hout hin
    · obtain ⟨h0, h1, h4, -, hno, hout, -, hib⟩ := (hcells i).2 hp
      rcases hloc with (hnm | ⟨-, -, rfl⟩ | ⟨-, -, rfl | rfl⟩) | ⟨hout', rfl⟩
      · have hnout : ¬ C.IsOuter (C.occ A.typ i) :=
          fun h => hnm (C.g7_marking _ (Or.inl h))
        have hnb : ¬ C.IsBoundary (C.occ A.typ i) :=
          fun h => hnm (C.g7_marking _ (Or.inr (Or.inl h)))
        have hnpath := not_on_path (C.form B.typ) hs i hnm
        obtain rfl | rfl | rfl | rfl | rfl :
            k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
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
  have hgenerated :
      IsStrictNormal C hC (strictChild C hC B A.typ) ∧
        IsStrictIdentityCorrect C hC (strictChild C hC B A.typ) := by
    refine ⟨key, fun i => ⟨fun hin hnp => ?_, fun hp => ?_⟩⟩
    · exact ((hcells i).2 hnp).1.trans (if_pos hin)
    · obtain ⟨d, hd⟩ := (isPrint_iff (C.form B.typ) hs i).1 hp
      exact ((hcells i).1 d hd).2
  rw [hchild]
  exact hgenerated

/-- Step 3 of the blueprint proof of `strictLegal_properties`: prepend a strict child to an
infinite legality chain, shifting origins through the old chain. -/
private lemma strictLegal_properties_step3_child_legal (A : StrictDecTile C hC)
    (hA : StrictLegal C hC A) :
    ∀ B, IsStrictChildOf C hC A B → StrictLegal C hC B := by
  sorry

private theorem strictLegal_properties_step4_boundary_step1_print_not_boundary_seg_endpoints
    {a b c d : Pt} (hab : a ≠ b) (h : segment ℝ a b = segment ℝ c d) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  have mem_segment_iff' {x y z : Pt} :
      z ∈ segment ℝ x y ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = x + t • (y - x) := by
    rw [segment_eq_image']
    constructor
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      exact ⟨t, ht0, ht1, rfl⟩
    · rintro ⟨t, ht0, ht1, rfl⟩
      exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
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
    rw [zero_smul]
    exact (add_eq_left.1 hα.symm).symm
  have e2 : (1 : ℝ) • (b - a) = (s + β * (t - s)) • (b - a) := by
    rw [one_smul]
    have h' : a + (b - a) = a + (s + β * (t - s)) • (b - a) := by
      rw [← hβ]
      abel
    exact add_left_cancel h'
  have f1 := smul_left_injective ℝ hu e1
  have f2 := smul_left_injective ℝ hu e2
  have key : (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    have h3 : s * (1 - α) = 0 := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.2 ha1), mul_nonneg ha0 ht0]
    have h4 : α * t = 0 := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.2 ha1), mul_nonneg ha0 ht0]
    rcases mul_eq_zero.1 h3 with h3 | h3
    · subst h3
      have h' : β * t = 1 := by linarith
      left
      refine ⟨rfl, ?_⟩
      nlinarith
    · have hα1 : α = 1 := by linarith
      subst hα1
      have ht : t = 0 := by linarith
      subst ht
      right
      refine ⟨?_, rfl⟩
      nlinarith
  rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    constructor <;> simp
  · right
    constructor <;> simp

/-- Step 1 of the blueprint proof of `strictLegal_properties_step4_boundary`: a print side is
strictly internal to its template and therefore cannot be a boundary side. -/
private lemma strictLegal_properties_step4_boundary_step1_print_not_boundary
    (C : Geometry.MacroCertificate P) (o : C.SideOcc) (h_print : C.IsPrint o) :
    ¬ C.IsBoundary o := by
  obtain ⟨d, hpd⟩ := h_print
  let α : C.Q.Form := C.owner o.1
  change C.marked α d ∧ (o = C.printOcc α d ∨ o = C.partner (C.printOcc α d)) at hpd
  rcases hpd with ⟨hmarked, hprint | hpartner⟩
  · rw [hprint]
    exact (C.g2_central α (C.print α d)).2
  · have hprint_inner := C.g4_print_inner α d hmarked
    obtain ⟨_hneq, howner, hside⟩ := C.g1_partner (C.printOcc α d) hprint_inner
    intro hboundary
    rw [hpartner] at hboundary
    unfold MacroData.IsBoundary at hboundary
    have howner_print : C.owner (C.printOcc α d).1 = α := by
      change C.owner (C.central α) = α
      exact C.g5_central_owner α
    rw [howner, howner_print] at hboundary
    have hboundary_print : C.IsBoundary (C.printOcc α d) := by
      unfold MacroData.IsBoundary
      rw [howner_print]
      refine ⟨hprint_inner, ?_⟩
      have hne : C.occStart (C.printOcc α d) ≠ C.occEnd (C.printOcc α d) := by
        intro hend
        have hvertex :
            (C.Q.disk (C.form (C.printOcc α d).1)).vertex (C.printOcc α d).2 =
              (C.Q.disk (C.form (C.printOcc α d).1)).vertex
                (finRotate _ (C.printOcc α d).2) := by
          exact vadd_left_cancel (C.anchor (C.printOcc α d).1) hend
        have hindex := (C.Q.disk (C.form (C.printOcc α d).1)).vertex_injective hvertex
        exact finRotate_ne_self
          (by have := (C.Q.disk (C.form (C.printOcc α d).1)).three_le; omega)
          (C.printOcc α d).2 hindex.symm
      have hside' :
          segment ℝ (C.occStart (C.printOcc α d)) (C.occEnd (C.printOcc α d)) =
            segment ℝ (C.occStart (C.partner (C.printOcc α d)))
              (C.occEnd (C.partner (C.printOcc α d))) := by
        simpa [MacroData.occSide, MacroData.childTile, PlacedTile.side,
          PolygonalDisk.side, MacroData.occStart, MacroData.occEnd, vadd_segment] using hside.symm
      have hends :=
        strictLegal_properties_step4_boundary_step1_print_not_boundary_seg_endpoints hne hside'
      rcases hboundary.2 with hstart | hend
      · rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          rw [← h1]
          exact hstart
        · right
          rw [← h1]
          exact hstart
      · rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · right
          rw [← h2]
          exact hend
        · left
          rw [← h2]
          exact hend
    exact (C.g2_central α (C.print α d)).2 hboundary_print

/-- Step 4 of the blueprint proof of `strictLegal_properties`: a boundary fourth cell of a
generated child is the header of its parent. -/
private lemma strictLegal_properties_step4_boundary (B A : StrictDecTile C hC)
    (hBA : IsStrictChildOf C hC B A) :
    ∀ i : C.Side A.typ, C.IsBoundary (C.occ A.typ i) →
      A.cell i 3 = headerSU C hC (strictHeaderOf C hC B) := by
  intro i h_bound
  have h_owner := hBA.1
  have h_child := hBA.2
  have h_child_cell : ∀ k, A.cell i k = (strictChild C hC B A.typ).cell i k := by
    intro k
    obtain ⟨t, col⟩ := A
    injection h_child with htyp hcol
    exact congrFun (congrFun hcol i) k
  rw [h_child_cell 3]
  have hc := strictChild_cells C hC B A.typ h_owner i
  have hp : ¬ C.IsPrint (C.occ A.typ i) := fun hp =>
    strictLegal_properties_step4_boundary_step1_print_not_boundary C (C.occ A.typ i) hp h_bound
  have h_inner := hc.2 hp
  exact h_inner.2.2.2.2.2.2.1 h_bound

/-- Step 1 of the blueprint proof of `strictLegal_properties_step5_path`: paths are invariant under form casting. -/
private lemma strictLegal_properties_step5_path_step1_cast_path
    {P : Protoset} {τ : Substitution P} {m : ℕ}
    (C : MacroCertificate P) (hC : C.Represents τ m)
    {F1 F2 : C.Q.Form} (h : F1 = F2) (d : Fin (C.Q.disk F1).n) (j : Fin 5) (occ : C.SideOcc) :
    occ ∈ C.path F1 d j ↔ occ ∈ C.path F2 (cast (congrArg (fun F => Fin (C.Q.disk F).n) h) d) j := by
  have _ := hC
  subst h
  rfl

/-- Step 5 of the blueprint proof of `strictLegal_properties`: copied third cells on one path
of a generated child all come from the same parent cell. -/
private lemma strictLegal_properties_step5_path (B A : StrictDecTile C hC)
    (hBA : IsStrictChildOf C hC B A) :
    ∀ (d : Fin (C.Q.disk (C.owner A.typ)).n) (j : Fin 5) (i i' : C.Side A.typ),
      C.occ A.typ i ∈ C.path (C.owner A.typ) d j →
      C.occ A.typ i' ∈ C.path (C.owner A.typ) d j →
      ¬ C.IsPrint (C.occ A.typ i) → ¬ C.IsPrint (C.occ A.typ i') →
      A.cell i 2 = A.cell i' 2 := by
  dsimp [IsStrictChildOf] at hBA
  intro d j i i' hi hi' hnp hnp'
  have hd_eq := hBA.1
  let d' : Fin (C.Q.disk (C.form B.typ)).n :=
    cast (congrArg (fun F => Fin (C.Q.disk F).n) hd_eq) d
  have hchild_i : ∀ k, A.cell i k = (strictChild C hC B A.typ).cell i k := by
    intro k
    obtain ⟨t, col⟩ := A
    injection hBA.2 with _ hcol
    exact congrFun (congrFun hcol i) k
  have hchild_i' : ∀ k, A.cell i' k = (strictChild C hC B A.typ).cell i' k := by
    intro k
    obtain ⟨t, col⟩ := A
    injection hBA.2 with _ hcol
    exact congrFun (congrFun hcol i') k
  have hi_cast : C.occ A.typ i ∈ C.path (C.form B.typ) d' j := by
    rwa [← strictLegal_properties_step5_path_step1_cast_path C hC hd_eq d j]
  have hi'_cast : C.occ A.typ i' ∈ C.path (C.form B.typ) d' j := by
    rwa [← strictLegal_properties_step5_path_step1_cast_path C hC hd_eq d j]
  have h1 : A.cell i 2 = B.cell d' j :=
    (hchild_i 2).trans (((strictChild_cells C hC B A.typ hBA.1 i).2 hnp).2.2.2.1 d' j hi_cast)
  have h2 : A.cell i' 2 = B.cell d' j :=
    (hchild_i' 2).trans (((strictChild_cells C hC B A.typ hBA.1 i').2 hnp').2.2.2.1 d' j hi'_cast)
  exact h1.trans h2.symm

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
  obtain ⟨B, hB, hBA⟩ := strictLegal_properties_step1_parent C hC A hA
  have hnormal := strictLegal_properties_step2_child_normal C hC B A hBA
  refine ⟨⟨B, hB, hBA⟩, hnormal.1, hnormal.2,
    strictLegal_properties_step3_child_legal C hC A hA, ?_, ?_⟩
  · exact ⟨B, hB, hBA, strictLegal_properties_step4_boundary C hC B A hBA⟩
  · exact strictLegal_properties_step5_path C hC B A hBA

private theorem strict_assembleMacrotemplates_identNeZero (e : C.EdgeId) :
    identSU C hC e ≠ 0 := by
  simp [identSU]

private theorem strict_assembleMacrotemplates_identInj {e e' : C.EdgeId}
    (h : identSU C hC e = identSU C hC e') : e = e' := by
  simpa [identSU] using h

private theorem strict_assembleMacrotemplates_isLocalFour (o : C.SideOcc) :
    IsStrictLocal C o 4 := by
  apply Or.inl
  by_cases hm : C.IsMarked o
  · by_cases hs : C.special o ∨ C.IsPrint o
    · exact Or.inr (Or.inl ⟨hm, hs, rfl⟩)
    · push_neg at hs
      exact Or.inr (Or.inr ⟨hm, ⟨hs.1, hs.2⟩, Or.inr rfl⟩)
  · exact Or.inl hm

private theorem strict_assembleMacrotemplates_cellFourPrint {A : StrictDecTile C hC}
    (hA : IsStrictNormal C hC A) (i : C.Side A.typ) (hp : C.IsPrint (C.occ A.typ i)) :
    A.cell i 4 = identSU C hC (C.edge (C.occ A.typ i)) := by
  rw [hA i 4 (strict_assembleMacrotemplates_isLocalFour C _)]
  simp [strictPrescribedCell, hp]

private theorem strict_assembleMacrotemplates_cellFourNonprint {A : StrictDecTile C hC}
    (hA : IsStrictNormal C hC A) (i : C.Side A.typ) (hp : ¬ C.IsPrint (C.occ A.typ i)) :
    A.cell i 4 = 0 := by
  rw [hA i 4 (strict_assembleMacrotemplates_isLocalFour C _)]
  simp [strictPrescribedCell, hp]

private theorem strict_assembleMacrotemplates_printInner {o : C.SideOcc} (hp : C.IsPrint o) :
    C.IsInner o := by
  obtain ⟨d, hd⟩ := hp
  exact isInner_of_isPrintOf C hd

private theorem strict_assembleMacrotemplates_cellZeroOuter {A : StrictDecTile C hC}
    (hA : IsStrictNormal C hC A) (i : C.Side A.typ) (ho : C.IsOuter (C.occ A.typ i)) :
    A.cell i 0 = 0 := by
  have hloc : IsStrictLocal C (C.occ A.typ i) 0 := by
    apply Or.inl
    by_cases hm : C.IsMarked (C.occ A.typ i)
    · exact Or.inr (Or.inr ⟨hm, ⟨fun hs => C.g6_special_inner _ hs ho,
        fun hp => strict_assembleMacrotemplates_printInner C hp ho⟩, Or.inl rfl⟩)
    · exact Or.inl hm
  rw [hA _ 0 hloc]
  have hni : ¬ C.IsInner (C.occ A.typ i) := fun h => h ho
  simp [strictPrescribedCell, hni]

private theorem strict_assembleMacrotemplates_match {A B : StrictDecTile C hC}
    (hA : IsStrictNormal C hC A ∧ IsStrictIdentityCorrect C hC A)
    (hB : IsStrictNormal C hC B ∧ IsStrictIdentityCorrect C hC B)
    (i : C.Side A.typ) (j : C.Side B.typ) (hi : C.IsInner (C.occ A.typ i))
    (hc : ∀ k, B.cell j k = A.cell i k) :
    C.IsInner (C.occ B.typ j) ∧ C.edge (C.occ B.typ j) = C.edge (C.occ A.typ i) := by
  by_cases hp : C.IsPrint (C.occ A.typ i)
  · have h4 : A.cell i 4 = identSU C hC (C.edge (C.occ A.typ i)) := (hA.2 i).2 hp
    by_cases hq : C.IsPrint (C.occ B.typ j)
    · refine ⟨strict_assembleMacrotemplates_printInner C hq,
        strict_assembleMacrotemplates_identInj C hC ?_⟩
      rw [← strict_assembleMacrotemplates_cellFourPrint C hC hB.1 j hq, hc 4, h4]
    · exfalso
      have h5 := strict_assembleMacrotemplates_cellFourNonprint C hC hB.1 j hq
      rw [hc 4, h4] at h5
      exact strict_assembleMacrotemplates_identNeZero C hC _ h5
  · have h0 : A.cell i 0 = identSU C hC (C.edge (C.occ A.typ i)) := (hA.2 i).1 hi hp
    have hq : ¬ C.IsPrint (C.occ B.typ j) := by
      intro hq
      have h5 := strict_assembleMacrotemplates_cellFourPrint C hC hB.1 j hq
      rw [hc 4, strict_assembleMacrotemplates_cellFourNonprint C hC hA.1 i hp] at h5
      exact strict_assembleMacrotemplates_identNeZero C hC _ h5.symm
    have hin : C.IsInner (C.occ B.typ j) := by
      intro ho
      have h5 := strict_assembleMacrotemplates_cellZeroOuter C hC hB.1 j ho
      rw [hc 0, h0] at h5
      exact strict_assembleMacrotemplates_identNeZero C hC _ h5
    refine ⟨hin, strict_assembleMacrotemplates_identInj C hC ?_⟩
    rw [← (hB.2 j).1 hin hq, hc 0, h0]

private theorem strict_assembleMacrotemplates_isCompactSegment (x y : Pt) :
    IsCompact (segment ℝ x y) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

private theorem strict_assembleMacrotemplates_vaddCancel {S : Set Pt} (hS : IsCompact S)
    (hne : S.Nonempty) {a b : Pt} (h : a +ᵥ S = b +ᵥ S) : a = b := by
  obtain ⟨x0, hx0, hmax⟩ := hS.exists_isMaxOn hne
    ((continuous_id.inner continuous_const :
      Continuous fun x : Pt => inner ℝ x (a - b)).continuousOn)
  have h1 : a +ᵥ x0 ∈ b +ᵥ S := h ▸ Set.vadd_mem_vadd_set hx0
  obtain ⟨y, hy, hxy⟩ := h1
  have hy' : y = (a - b) + x0 := by
    simp only [vadd_eq_add] at hxy
    rw [sub_add_eq_add_sub, ← hxy]
    abel
  have h2 := hmax hy
  simp only [Set.mem_setOf_eq, id] at h2
  rw [hy', inner_add_left, real_inner_self_eq_norm_sq] at h2
  have h3 : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h3)

/-- The placed segment of a side occurrence translated by `a` (strict variant). -/
private def strict_assembleMacrotemplates_side (a : Pt) (o : C.SideOcc) : Set Pt :=
  a +ᵥ (C.Q.disk (C.form o.1)).side o.2

private theorem strict_assembleMacrotemplates_sideCancel {a b : Pt} {o : C.SideOcc}
    (h : strict_assembleMacrotemplates_side C a o =
      strict_assembleMacrotemplates_side C b o) : a = b :=
  strict_assembleMacrotemplates_vaddCancel
    (strict_assembleMacrotemplates_isCompactSegment _ _) ⟨_, left_mem_segment ℝ _ _⟩ h

private theorem strict_assembleMacrotemplates_innerOfOccSide {o o' : C.SideOcc}
    (ho : C.IsInner o) (hown : C.owner o'.1 = C.owner o.1) (hs : C.occSide o' = C.occSide o) :
    C.IsInner o' := by
  unfold MacroData.IsInner MacroData.IsOuter at *
  rwa [hs, hown]

private theorem strict_assembleMacrotemplates_partner {s s' : C.Typ} (i : C.Side s)
    (j : C.Side s') (hown : C.owner s' = C.owner s) (hne : s' ≠ s)
    (hi : C.IsInner (C.occ s i)) (hs : C.occSide (C.occ s' j) = C.occSide (C.occ s i)) :
    s' = (C.partner (C.occ s i)).1 :=
  congrArg Sigma.fst (C.g1_side_unique (C.occ s i) (C.occ s' j) hi hown hne hs)

private theorem strict_assembleMacrotemplates_tileUnique
    {T : PlaneTiling (strictProtoset C hC)} {X Y : PlacedTile (strictProtoset C hC)}
    (hX : X ∈ T.tiles) (hY : Y ∈ T.tiles) {A B : StrictDecTile C hC}
    (hXA : X.form = StrictForm.typed A) (hYB : Y.form = StrictForm.typed B)
    (ht : A.typ = B.typ) (ha : X.anchor = Y.anchor) : X = Y := by
  by_contra hne
  have hd : Disjoint (interior X.carrier) (interior Y.carrier) := T.disjoint hX hY hne
  have hXc : X.carrier = X.anchor +ᵥ (C.Q.disk (C.form A.typ)).carrier := by
    simp only [PlacedTile.carrier, hXA, StrictForm.proj]
  have hYc : Y.carrier = Y.anchor +ᵥ (C.Q.disk (C.form A.typ)).carrier := by
    simp only [PlacedTile.carrier, hYB, StrictForm.proj, ht]
  rw [hXc, hYc, ha] at hd
  obtain ⟨z, hz⟩ := (C.Q.disk (C.form A.typ)).interior_nonempty
  have hz' : Y.anchor +ᵥ z ∈ interior (Y.anchor +ᵥ (C.Q.disk (C.form A.typ)).carrier) := by
    rw [interior_vadd]; exact Set.vadd_mem_vadd_set hz
  exact Set.disjoint_left.1 hd hz' hz'

private theorem strict_assembleMacrotemplates_neighbour
    {T : PlaneTiling (strictProtoset C hC)} (hT : IsStrictMatched C hC T)
    (hN : ∀ X ∈ T.tiles, ∃ A, X.form = StrictForm.typed A ∧ IsStrictNormal C hC A ∧
      IsStrictIdentityCorrect C hC A) {A : StrictDecTile C hC} {a : Pt}
    (hX : (⟨StrictForm.typed A, a⟩ : PlacedTile (strictProtoset C hC)) ∈ T.tiles)
    (i : C.Side A.typ) (hi : C.IsInner (C.occ A.typ i)) :
    ∃ B : StrictDecTile C hC, B.typ = (C.partner (C.occ A.typ i)).1 ∧
      (⟨StrictForm.typed B, a - C.anchor A.typ + C.anchor (C.partner (C.occ A.typ i)).1⟩ :
        PlacedTile (strictProtoset C hC)) ∈ T.tiles := by
  obtain ⟨A0, hXA0, hNA, hIA⟩ := hN _ hX
  have hXA0' : StrictForm.typed A = StrictForm.typed A0 := hXA0
  have hAA0 : A = A0 := by injection hXA0'
  subst hAA0
  obtain ⟨Y, hY, hYX, j, hside⟩ := exists_coincident_side T hT.1 hX i
  obtain ⟨B0, hYB0, hNB, hIB⟩ := hN Y hY
  obtain ⟨Yf, Ya⟩ := Y
  have hYB0' : Yf = StrictForm.typed B0 := hYB0
  subst hYB0'
  have hside' : strict_assembleMacrotemplates_side C Ya (C.occ B0.typ j) =
      strict_assembleMacrotemplates_side C a (C.occ A.typ i) := hside
  have hcell : ∀ k, B0.cell j k = A.cell i k := by
    have heq := hT.2 A B0 a Ya hX hY (fun h => hYX h.symm) i j hside'.symm
    exact fun k => (congrFun heq k).symm
  obtain ⟨hjin, hje⟩ :=
    strict_assembleMacrotemplates_match C hC ⟨hNA, hIA⟩ ⟨hNB, hIB⟩ i j hi hcell
  rcases C.g1_edge_unique _ _ hi hjin hje.symm with ho | ho
  · exfalso
    have ht : B0.typ = A.typ := congrArg Sigma.fst ho
    rw [ho] at hside'
    have ha := strict_assembleMacrotemplates_sideCancel C hside'
    exact hYX (strict_assembleMacrotemplates_tileUnique C hC hY hX rfl rfl ht ha)
  · refine ⟨B0, congrArg Sigma.fst ho, ?_⟩
    rw [ho] at hside'
    obtain ⟨-, -, hp3⟩ := C.g1_partner _ hi
    have hp3' : strict_assembleMacrotemplates_side C
        (C.anchor (C.partner (C.occ A.typ i)).1) (C.partner (C.occ A.typ i)) =
        strict_assembleMacrotemplates_side C (C.anchor A.typ) (C.occ A.typ i) := hp3
    have hYa : Ya = a - C.anchor A.typ + C.anchor (C.partner (C.occ A.typ i)).1 := by
      apply strict_assembleMacrotemplates_sideCancel C (o := C.partner (C.occ A.typ i))
      rw [hside']
      unfold strict_assembleMacrotemplates_side at hp3' ⊢
      rw [← vadd_vadd, hp3', vadd_vadd, sub_add_cancel]
    rw [← hYa]
    exact hY

private theorem strict_assembleMacrotemplates_allPresent
    {T : PlaneTiling (strictProtoset C hC)} (hT : IsStrictMatched C hC T)
    (hN : ∀ X ∈ T.tiles, ∃ A, X.form = StrictForm.typed A ∧ IsStrictNormal C hC A ∧
      IsStrictIdentityCorrect C hC A) {A : StrictDecTile C hC} {a : Pt}
    (hX : (⟨StrictForm.typed A, a⟩ : PlacedTile (strictProtoset C hC)) ∈ T.tiles)
    (t : C.Typ) (ht : C.owner t = C.owner A.typ) :
    ∃ f : C.Side t → Fin 5 → SU C hC,
      (⟨StrictForm.typed ⟨t, f⟩, (a - C.anchor A.typ) + C.anchor t⟩ :
        PlacedTile (strictProtoset C hC)) ∈ T.tiles := by
  let Pres : {s : C.Typ // C.owner s = C.owner A.typ} → Prop := fun u =>
    ∃ f : C.Side u.1 → Fin 5 → SU C hC,
      (⟨StrictForm.typed ⟨u.1, f⟩, (a - C.anchor A.typ) + C.anchor u.1⟩ :
        PlacedTile (strictProtoset C hC)) ∈ T.tiles
  have step : ∀ u w, (C.innerGraph (C.owner A.typ)).Adj u w → Pres u → Pres w := by
    intro u w hadj hu
    obtain ⟨f, hf⟩ := hu
    rw [MacroData.innerGraph, SimpleGraph.fromRel_adj] at hadj
    obtain ⟨hne, hR⟩ := hadj
    have core : ∀ (p : C.Side u.1) (q : C.Side w.1), C.IsInner (C.occ u.1 p) →
        C.occSide (C.occ w.1 q) = C.occSide (C.occ u.1 p) → Pres w := by
      intro p q hp hs
      have hw : w.1 = (C.partner (C.occ u.1 p)).1 :=
        strict_assembleMacrotemplates_partner C p q (w.2.trans u.2.symm)
          (fun h => hne (Subtype.ext h.symm)) hp hs
      obtain ⟨B, hBt, hB⟩ := strict_assembleMacrotemplates_neighbour C hC hT hN hf p hp
      obtain ⟨Btyp, Bcell⟩ := B
      have hBt' : Btyp = w.1 := hBt.trans hw.symm
      subst hBt'
      refine ⟨Bcell, ?_⟩
      dsimp only at hB
      rw [← hw] at hB
      have heq : (a - C.anchor A.typ) + C.anchor u.1 - C.anchor u.1 +
          C.anchor w.1 = (a - C.anchor A.typ) + C.anchor w.1 := by
        rw [add_sub_cancel_right]
      rwa [heq] at hB
    rcases hR with ⟨p, q, hp, hs⟩ | ⟨q, p, hq, hs⟩
    · exact core p q hp hs.symm
    · exact core p q
        (strict_assembleMacrotemplates_innerOfOccSide C hq (u.2.trans w.2.symm) hs.symm) hs
  have base : Pres ⟨A.typ, rfl⟩ := ⟨A.cell, by rw [sub_add_cancel]; exact hX⟩
  obtain ⟨w⟩ := (C.g1_connected (C.owner A.typ)).preconnected ⟨A.typ, rfl⟩ ⟨t, ht⟩
  suffices H : ∀ u w' (p : (C.innerGraph (C.owner A.typ)).Walk u w'), Pres u → Pres w' from
    H _ _ w base
  intro u w' p
  induction p with
  | nil => exact id
  | cons h p ih => exact fun hu => ih (step _ _ h hu)

open Classical in
/-- The candidate strict block with parent form `α` and offset `v`, coloured by `T`. -/
private def strict_assembleMacrotemplates_block (T : PlaneTiling (strictProtoset C hC))
    (α : C.Q.Form) (v : Pt) : StrictBlock C hC where
  α := α
  v := v
  col t := if h : ∃ f : C.Side t → Fin 5 → SU C hC,
      (⟨StrictForm.typed ⟨t, f⟩, v + C.anchor t⟩ : PlacedTile (strictProtoset C hC)) ∈ T.tiles
    then h.choose else fun _ _ => 0

private theorem strict_assembleMacrotemplates_blockPlaced
    {T : PlaneTiling (strictProtoset C hC)} (α : C.Q.Form) (v : Pt) (t : C.Typ)
    (h : ∃ f : C.Side t → Fin 5 → SU C hC,
      (⟨StrictForm.typed ⟨t, f⟩, v + C.anchor t⟩ : PlacedTile (strictProtoset C hC)) ∈ T.tiles) :
    (strict_assembleMacrotemplates_block C hC T α v).placed t ∈ T.tiles := by
  have hcol : (strict_assembleMacrotemplates_block C hC T α v).col t = h.choose := by
    simp only [strict_assembleMacrotemplates_block]
    rw [dif_pos h]
  show (⟨StrictForm.typed ⟨t, (strict_assembleMacrotemplates_block C hC T α v).col t⟩,
    v + C.anchor t⟩ : PlacedTile (strictProtoset C hC)) ∈ T.tiles
  rw [hcol]
  exact h.choose_spec
theorem strict_assembleMacrotemplates (T : PlaneTiling (strictProtoset C hC))
    (hT : IsStrictMatched C hC T)
    (hN : ∀ X ∈ T.tiles, ∃ A, X.form = StrictForm.typed A ∧ IsStrictNormal C hC A ∧
      IsStrictIdentityCorrect C hC A) :
    Nonempty (StrictMacroPartition C hC T) := by
  have hsub : ∀ X (hX : X ∈ T.tiles) (A : StrictDecTile C hC), X.form = StrictForm.typed A →
      (strict_assembleMacrotemplates_block C hC T (C.owner A.typ)
        (X.anchor - C.anchor A.typ)).tiles ⊆ T.tiles := by
    rintro X hX A hXA Z ⟨t, ht, rfl⟩
    have ht' : C.owner t = C.owner A.typ := ht
    have hX' : (⟨StrictForm.typed A, X.anchor⟩ : PlacedTile (strictProtoset C hC)) ∈ T.tiles := by
      rw [← hXA]; exact hX
    exact strict_assembleMacrotemplates_blockPlaced C hC _ _ t
      (strict_assembleMacrotemplates_allPresent C hC hT hN hX' t ht')
  have hself : ∀ X (hX : X ∈ T.tiles) (A : StrictDecTile C hC), X.form = StrictForm.typed A →
      X ∈ (strict_assembleMacrotemplates_block C hC T (C.owner A.typ)
        (X.anchor - C.anchor A.typ)).tiles := by
    intro X hX A hXA
    refine ⟨A.typ, rfl, ?_⟩
    have hmem := strict_assembleMacrotemplates_blockPlaced C hC (C.owner A.typ)
      (X.anchor - C.anchor A.typ) A.typ ⟨A.cell, by
        rw [sub_add_cancel]
        show (⟨StrictForm.typed A, X.anchor⟩ : PlacedTile (strictProtoset C hC)) ∈ T.tiles
        rw [← hXA]; exact hX⟩
    exact strict_assembleMacrotemplates_tileUnique C hC hX hmem hXA rfl rfl
      (by show X.anchor = (X.anchor - C.anchor A.typ) + C.anchor A.typ; rw [sub_add_cancel])
  have hblk : ∀ X (hX : X ∈ T.tiles) (A : StrictDecTile C hC), X.form = StrictForm.typed A →
      ∀ Z ∈ (strict_assembleMacrotemplates_block C hC T (C.owner A.typ)
        (X.anchor - C.anchor A.typ)).tiles,
      ∀ B : StrictDecTile C hC, Z.form = StrictForm.typed B →
      strict_assembleMacrotemplates_block C hC T (C.owner B.typ) (Z.anchor - C.anchor B.typ) =
        strict_assembleMacrotemplates_block C hC T (C.owner A.typ)
          (X.anchor - C.anchor A.typ) := by
    rintro X hX A hXA Z ⟨t, ht, rfl⟩ B hZB
    have ht' : C.owner t = C.owner A.typ := ht
    have hZB' : StrictForm.typed (⟨t, (strict_assembleMacrotemplates_block C hC T
        (C.owner A.typ) (X.anchor - C.anchor A.typ)).col t⟩ : StrictDecTile C hC) =
        StrictForm.typed B := hZB
    have hBeq : (⟨t, (strict_assembleMacrotemplates_block C hC T (C.owner A.typ)
        (X.anchor - C.anchor A.typ)).col t⟩ : StrictDecTile C hC) = B := by
      injection hZB'
    rw [← hBeq]
    show strict_assembleMacrotemplates_block C hC T (C.owner t)
        ((X.anchor - C.anchor A.typ) + C.anchor t - C.anchor t) =
      strict_assembleMacrotemplates_block C hC T (C.owner A.typ) (X.anchor - C.anchor A.typ)
    rw [ht', add_sub_cancel_right]
  refine ⟨{ ι := {K : StrictBlock C hC // ∃ X ∈ T.tiles, ∃ A : StrictDecTile C hC,
              X.form = StrictForm.typed A ∧
              K = strict_assembleMacrotemplates_block C hC T (C.owner A.typ)
                (X.anchor - C.anchor A.typ)},
            block := Subtype.val,
            disjoint := ?_,
            cover := ?_ }⟩
  · rintro ⟨K, X, hX, A, hXA, rfl⟩ ⟨K', X', hX', A', hXA', rfl⟩ hne
    rw [Set.disjoint_left]
    intro Z hZ hZ'
    apply hne
    obtain ⟨B, hZB, -, -⟩ := hN Z (hsub X hX A hXA hZ)
    exact Subtype.ext ((hblk X hX A hXA Z hZ B hZB).symm.trans
      (hblk X' hX' A' hXA' Z hZ' B hZB))
  · apply Set.Subset.antisymm
    · intro Z hZ
      obtain ⟨⟨K, X, hX, A, hXA, rfl⟩, hZK⟩ := Set.mem_iUnion.1 hZ
      exact hsub X hX A hXA hZK
    · intro X hX
      obtain ⟨A, hXA, -, -⟩ := hN X hX
      exact Set.mem_iUnion.2 ⟨⟨strict_assembleMacrotemplates_block C hC T (C.owner A.typ)
        (X.anchor - C.anchor A.typ), X, hX, A, hXA, rfl⟩, hself X hX A hXA⟩

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

/-- Step 1 of the blueprint proof of `strict_boundary_header_constant`: a boundary tile is
legal. -/
private lemma strict_boundary_header_constant_step1_legal (K : StrictBlock C hC)
    (hK : StrictBlockContext C hC K) (t : C.Typ) (ht : C.owner t = K.α)
    (i : C.Side t) (hi : C.IsBoundary (C.occ t i)) :
    StrictLegal C hC (K.tileOf t) := by
  apply hK.2 t ht
  rintro rfl
  exact (C.g2_central K.α i).2 hi

/-- Step 2 of the blueprint proof of `strict_boundary_header_constant`: the boundary cells of a
single legal tile equal the header of any chosen legal parent, so it is a constant. -/
private lemma strict_boundary_header_constant_step2_header_eq (K : StrictBlock C hC)
    (hK : StrictBlockContext C hC K) (t : C.Typ) (ht : C.owner t = K.α)
    (i : C.Side t) (hi : C.IsBoundary (C.occ t i)) :
    ∃ h : HeaderKernel.Header C.Typ C.Side,
      (∀ j : C.Side t, C.IsBoundary (C.occ t j) → K.col t j 3 = headerSU C hC h) ∧
      C.form h.1 = K.α := by
  sorry

/-- Step 3 of the blueprint proof of `strict_boundary_header_constant`: any boundary side owner
is part of the boundary belt type. -/
private lemma strict_boundary_header_constant_step3_is_belt_type (α : C.Q.Form)
    (t : C.Typ) (ht : C.owner t = α) (i : C.Side t) (hi : C.IsBoundary (C.occ t i)) :
    C.IsBeltType α t := by
  dsimp [MacroData.IsBeltType]
  refine ⟨ht, ?_⟩
  dsimp [MacroData.IsBoundary] at hi
  rcases hi with ⟨_, h | h⟩
  · use C.occStart (C.occ t i)
    refine ⟨?_, by rw [← ht]; exact h⟩
    have h_mem_frontier : (C.Q.disk (C.form t)).vertex i ∈
        frontier (C.Q.disk (C.form t)).carrier := by
      rw [(C.Q.disk (C.form t)).frontier_eq]
      simp only [mem_iUnion]
      exact ⟨i, left_mem_segment ℝ _ _⟩
    have h_closed : IsClosed (C.Q.disk (C.form t)).carrier := by
      rw [← (C.Q.disk (C.form t)).regular_closed]
      exact isClosed_closure
    exact vadd_mem_vadd_set_iff.mpr (h_closed.closure_eq ▸ frontier_subset_closure h_mem_frontier)
  · use C.occEnd (C.occ t i)
    refine ⟨?_, by rw [← ht]; exact h⟩
    have h_mem_frontier : (C.Q.disk (C.form t)).vertex (finRotate _ i) ∈
        frontier (C.Q.disk (C.form t)).carrier := by
      rw [(C.Q.disk (C.form t)).frontier_eq]
      simp only [mem_iUnion]
      exact ⟨i, right_mem_segment ℝ _ _⟩
    have h_closed : IsClosed (C.Q.disk (C.form t)).carrier := by
      rw [← (C.Q.disk (C.form t)).regular_closed]
      exact isClosed_closure
    exact vadd_mem_vadd_set_iff.mpr (h_closed.closure_eq ▸ frontier_subset_closure h_mem_frontier)

/-- Step 1 of the blueprint proof of `strict_boundary_header_constant_step4_belt_eq_step1_adj`:
adjacent belt types have a common boundary side where their fourth cells (index 3) agree. -/
private lemma strict_boundary_header_constant_step4_belt_eq_step1_adj_step1_adj_sides
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (u v : {t : C.Typ // C.IsBeltType K.α t})
    (hadj : (C.beltGraph K.α).Adj u v) :
    ∃ (i_adj : C.Side u.1) (j_adj : C.Side v.1),
      C.IsBoundary (C.occ u.1 i_adj) ∧ C.IsBoundary (C.occ v.1 j_adj) ∧
      K.col u.1 i_adj 3 = K.col v.1 j_adj 3 := by
  sorry

/-- Step 4a of the blueprint proof of `strict_boundary_header_constant_step4_belt_eq`: adjacent
boundary-belt types have equal boundary fourth cells. -/
private lemma strict_boundary_header_constant_step4_belt_eq_step1_adj
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (u v : {t : C.Typ // C.IsBeltType K.α t})
    (hadj : (C.beltGraph K.α).Adj u v)
    (i : C.Side u.1) (hi : C.IsBoundary (C.occ u.1 i))
    (j : C.Side v.1) (hj : C.IsBoundary (C.occ v.1 j)) :
    K.col u.1 i 3 = K.col v.1 j 3 := by
  obtain ⟨i_adj, j_adj, hi_adj, hj_adj, h_col⟩ :=
    strict_boundary_header_constant_step4_belt_eq_step1_adj_step1_adj_sides C hC K hK u v hadj
  obtain ⟨h_u, hh_u, -⟩ := strict_boundary_header_constant_step2_header_eq C hC K hK u.1 u.2.1 i hi
  obtain ⟨h_v, hh_v, -⟩ := strict_boundary_header_constant_step2_header_eq C hC K hK v.1 v.2.1 j hj
  have h1 : K.col u.1 i_adj 3 = headerSU C hC h_u := hh_u i_adj hi_adj
  have h2 : K.col v.1 j_adj 3 = headerSU C hC h_v := hh_v j_adj hj_adj
  rw [hh_u i hi, hh_v j hj, ← h1, ← h2, h_col]

/-- Step 4b of the blueprint proof of `strict_boundary_header_constant_step4_belt_eq`: propagate
a fixed boundary colour along belt-graph reachability. -/
private lemma strict_boundary_header_constant_step4_belt_eq_step2_reachable
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (u v : {t : C.Typ // C.IsBeltType K.α t})
    (hreach : (C.beltGraph K.α).Reachable u v)
    (c : SU C hC)
    (hu : ∀ i : C.Side u.1, C.IsBoundary (C.occ u.1 i) → K.col u.1 i 3 = c) :
    ∀ j : C.Side v.1, C.IsBoundary (C.occ v.1 j) → K.col v.1 j 3 = c := by
  sorry

/-- Step 4 of the blueprint proof of `strict_boundary_header_constant`: connectedness
propagates equality to every boundary cell of the block. -/
private lemma strict_boundary_header_constant_step4_belt_eq (K : StrictBlock C hC)
    (hK : StrictBlockContext C hC K)
    (u v : {t : C.Typ // C.IsBeltType K.α t})
    (i : C.Side u.1) (hi : C.IsBoundary (C.occ u.1 i))
    (j : C.Side v.1) (hj : C.IsBoundary (C.occ v.1 j)) :
    K.col u.1 i 3 = K.col v.1 j 3 := by
  have hreach := (C.g2_belt_connected K.α).preconnected u v
  have hu : ∀ i' : C.Side u.1, C.IsBoundary (C.occ u.1 i') → K.col u.1 i' 3 = K.col u.1 i 3 := by
    intro i' hi'
    obtain ⟨h, hh, -⟩ := strict_boundary_header_constant_step2_header_eq C hC K hK u.1 u.2.1 i hi
    rw [hh i' hi', hh i hi]
  have hv :=
    strict_boundary_header_constant_step4_belt_eq_step2_reachable C hC K hK u v hreach
      (K.col u.1 i 3) hu
  exact (hv j hj).symm

/-- `lem:comp/boundary-header` (strict variant): in a strictly matched finite realization of
`σ' α` whose noncentral tiles are legal, every boundary fourth cell carries the same header
`h = (t, v)`, and `form t = α`. -/
theorem strict_boundary_header_constant (K : StrictBlock C hC) (hK : StrictBlockContext C hC K) :
    ∃ h : HeaderKernel.Header C.Typ C.Side, StrictCommonHeader C hC K h := by
  have h_ne := (C.g2_belt_connected K.α).nonempty
  let u := Classical.choice h_ne
  have hu_owner : C.owner u.1 = K.α := u.property.1
  have hu_belt_own : C.IsBeltType (C.owner u.1) u.1 := by
    rw [hu_owner]
    exact u.property
  obtain ⟨i, hi⟩ := C.g2_belt_edge u.1 hu_belt_own
  obtain ⟨h, hh1, hh2⟩ :=
    strict_boundary_header_constant_step2_header_eq C hC K hK u.1 hu_owner i hi
  use h
  constructor
  · exact hh2
  · intro t j ht hj
    have ht_belt : C.IsBeltType K.α t :=
      strict_boundary_header_constant_step3_is_belt_type C K.α t ht j hj
    let v : {t : C.Typ // C.IsBeltType K.α t} := ⟨t, ht_belt⟩
    have h_eq := strict_boundary_header_constant_step4_belt_eq C hC K hK v u j hj i hi
    rw [h_eq]
    exact hh1 i hi

private theorem rhe_isPrint_iff {s : C.Typ} {β : C.Q.Form} (hs : C.owner s = β) (i : C.Side s) :
    C.IsPrint (C.occ s i) ↔ ∃ d : Fin (C.Q.disk β).n, C.IsPrintOf β d (C.occ s i) := by
  subst hs
  rfl

private theorem rhe_not_on_path {s : C.Typ} {β : C.Q.Form} (hs : C.owner s = β) (i : C.Side s)
    (hm : ¬ C.IsMarked (C.occ s i)) (d : Fin (C.Q.disk β).n) (j : Fin 5) :
    C.occ s i ∉ C.path β d j := by
  subst hs
  intro hmem
  by_cases hg : C.IsGenuinePath (C.owner s) d j
  · exact hm (C.g7_marking _ (Or.inr (Or.inr (Or.inr ⟨d, j, hg, hmem⟩))))
  · rw [C.g4_path_trivial _ d j hg, Option.mem_toList] at hmem
    have hmem' : C.occ s i ∈ C.outerList _ d := List.mem_iff_getElem?.mpr ⟨_, hmem⟩
    exact hm (C.g7_marking _ (Or.inl ((C.g3_outerList_mem _ d _).1 hmem').2.1))


private theorem rhe_child_normal (Q' : StrictDecTile C hC) (s : C.Typ)
    (hs : C.owner s = C.form Q'.typ) :
    IsStrictNormal C hC (strictChild C hC Q' s) ∧
      IsStrictIdentityCorrect C hC (strictChild C hC Q' s) := by
  have hcells := strictChild_cells C hC Q' s hs
  have key : ∀ (i : C.Side s) (k : Fin 5), IsStrictLocal C (C.occ s i) k →
      (strictChild C hC Q' s).cell i k = strictPrescribedCell C hC (C.occ s i) k := by
    intro i k hloc
    by_cases hp : C.IsPrint (C.occ s i)
    · obtain ⟨d, hd⟩ := (rhe_isPrint_iff C hs i).1 hp
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
        have hnpath := rhe_not_on_path C hs i hnm
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
  · obtain ⟨d, hd⟩ := (rhe_isPrint_iff C hs i).1 hp
    exact ((hcells i).1 d hd).2

/-- The cell of a strict tile indexed by the value of a side index (zero out of range). -/
private def rhe_cellv (X : StrictDecTile C hC) (v : ℕ) (k : Fin 5) : SU C hC :=
  if h : v < (C.Q.disk (C.form X.typ)).n then X.cell ⟨v, h⟩ k else 0

private theorem rhe_cellv_side (X : StrictDecTile C hC) (i : C.Side X.typ) (k : Fin 5) :
    rhe_cellv C hC X i.val k = X.cell i k := by
  unfold rhe_cellv
  rw [dif_pos i.isLt]

/-- Equal nondegenerate segments have the same endpoints. -/
private theorem rhe_seg_endpoints
    {a b c d : Pt} (hab : a ≠ b) (h : segment ℝ a b = segment ℝ c d) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  have mem_segment_iff' {x y z : Pt} :
      z ∈ segment ℝ x y ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = x + t • (y - x) := by
    rw [segment_eq_image']
    constructor
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      exact ⟨t, ht0, ht1, rfl⟩
    · rintro ⟨t, ht0, ht1, rfl⟩
      exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
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
    rw [zero_smul]
    exact (add_eq_left.1 hα.symm).symm
  have e2 : (1 : ℝ) • (b - a) = (s + β * (t - s)) • (b - a) := by
    rw [one_smul]
    have h' : a + (b - a) = a + (s + β * (t - s)) • (b - a) := by
      rw [← hβ]
      abel
    exact add_left_cancel h'
  have f1 := smul_left_injective ℝ hu e1
  have f2 := smul_left_injective ℝ hu e2
  have key : (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    have h3 : s * (1 - α) = 0 := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.2 ha1), mul_nonneg ha0 ht0]
    have h4 : α * t = 0 := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.2 ha1), mul_nonneg ha0 ht0]
    rcases mul_eq_zero.1 h3 with h3 | h3
    · subst h3
      have h' : β * t = 1 := by linarith
      left
      refine ⟨rfl, ?_⟩
      nlinarith
    · have hα1 : α = 1 := by linarith
      subst hα1
      have ht : t = 0 := by linarith
      subst ht
      right
      refine ⟨?_, rfl⟩
      nlinarith
  rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    constructor <;> simp
  · right
    constructor <;> simp

/-- A print side is
strictly internal to its template and therefore cannot be a boundary side. -/
private theorem rhe_print_not_boundary (o : C.SideOcc) (h_print : C.IsPrint o) :
    ¬ C.IsBoundary o := by
  obtain ⟨d, hpd⟩ := h_print
  let α : C.Q.Form := C.owner o.1
  change C.marked α d ∧ (o = C.printOcc α d ∨ o = C.partner (C.printOcc α d)) at hpd
  rcases hpd with ⟨hmarked, hprint | hpartner⟩
  · rw [hprint]
    exact (C.g2_central α (C.print α d)).2
  · have hprint_inner := C.g4_print_inner α d hmarked
    obtain ⟨_hneq, howner, hside⟩ := C.g1_partner (C.printOcc α d) hprint_inner
    intro hboundary
    rw [hpartner] at hboundary
    unfold MacroData.IsBoundary at hboundary
    have howner_print : C.owner (C.printOcc α d).1 = α := by
      change C.owner (C.central α) = α
      exact C.g5_central_owner α
    rw [howner, howner_print] at hboundary
    have hboundary_print : C.IsBoundary (C.printOcc α d) := by
      unfold MacroData.IsBoundary
      rw [howner_print]
      refine ⟨hprint_inner, ?_⟩
      have hne : C.occStart (C.printOcc α d) ≠ C.occEnd (C.printOcc α d) := by
        intro hend
        have hvertex :
            (C.Q.disk (C.form (C.printOcc α d).1)).vertex (C.printOcc α d).2 =
              (C.Q.disk (C.form (C.printOcc α d).1)).vertex
                (finRotate _ (C.printOcc α d).2) := by
          exact vadd_left_cancel (C.anchor (C.printOcc α d).1) hend
        have hindex := (C.Q.disk (C.form (C.printOcc α d).1)).vertex_injective hvertex
        exact finRotate_ne_self
          (by have := (C.Q.disk (C.form (C.printOcc α d).1)).three_le; omega)
          (C.printOcc α d).2 hindex.symm
      have hside' :
          segment ℝ (C.occStart (C.printOcc α d)) (C.occEnd (C.printOcc α d)) =
            segment ℝ (C.occStart (C.partner (C.printOcc α d)))
              (C.occEnd (C.partner (C.printOcc α d))) := by
        simpa [MacroData.occSide, MacroData.childTile, PlacedTile.side,
          PolygonalDisk.side, MacroData.occStart, MacroData.occEnd, vadd_segment] using hside.symm
      have hends :=
        rhe_seg_endpoints hne hside'
      rcases hboundary.2 with hstart | hend
      · rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          rw [← h1]
          exact hstart
        · right
          rw [← h1]
          exact hstart
      · rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · right
          rw [← h2]
          exact hend
        · left
          rw [← h2]
          exact hend
    exact (C.g2_central α (C.print α d)).2 hboundary_print

/-- A legal tile is the child of a normal identity-correct parent. -/
private theorem rhe_parent (X : StrictDecTile C hC) (hX : StrictLegal C hC X) :
    ∃ F : StrictDecTile C hC, C.owner X.typ = C.form F.typ ∧ X = strictChild C hC F X.typ ∧
      IsStrictNormal C hC F ∧ IsStrictIdentityCorrect C hC F := by
  obtain ⟨ch, h0, hch, -⟩ := hX
  subst h0
  have hN := rhe_child_normal C hC (ch (1 + 1)) (ch 1).typ (hch 1).1
  rw [← (hch 1).2] at hN
  exact ⟨ch 1, (hch 0).1, (hch 0).2, hN⟩

/-- The cells of a block tile which is the child of `F`. -/
private theorem rhe_tile_cell (K : StrictBlock C hC) (s : C.Typ) (F : StrictDecTile C hC)
    (hX : K.tileOf s = strictChild C hC F s) (i : C.Side s) (k : Fin 5) :
    K.col s i k = (strictChild C hC F s).cell i k := by
  have h2 : (⟨s, K.col s⟩ : StrictDecTile C hC) = ⟨s, (strictChild C hC F s).cell⟩ := hX
  have h3 := eq_of_heq (StrictDecTile.mk.inj h2).2
  rw [h3]

/-- A nonprint side on the path `P_j(d)` carries the parent cell `(d, j)` as third cell. -/
private theorem rhe_child_path (Q' : StrictDecTile C hC) (β : C.Q.Form) (hβ : C.form Q'.typ = β)
    (s : C.Typ) (hs : C.owner s = β) (i : C.Side s) (hnp : ¬ C.IsPrint (C.occ s i))
    (d : Fin (C.Q.disk β).n) (j : Fin 5) (hmem : C.occ s i ∈ C.path β d j) :
    (strictChild C hC Q' s).cell i 2 = rhe_cellv C hC Q' d.val j := by
  subst hβ
  rw [((strictChild_cells C hC Q' s hs i).2 hnp).2.2.2.1 d j hmem, rhe_cellv_side]


/-- Every port exists ((G3): every outer list has at least five entries). -/
private theorem rhe_port_some (β : C.Q.Form) (d : Fin (C.Q.disk β).n) (k : Fin 5) :
    ∃ o, C.port β d k = some o := by
  unfold MacroData.port
  have h5 := C.g3_five_le β d
  have hr : MacroData.portRank (C.outerList β d).length k ≤ (C.outerList β d).length := by
    unfold MacroData.portRank
    have : (k.val + 1) * (C.outerList β d).length ≤ 5 * (C.outerList β d).length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

/-- The reconstructed cell `(d, k)` is the third cell of the port `k` of `d`. -/
private theorem rhe_recon_port (K : StrictBlock C hC) (t : C.Typ) (β : C.Q.Form)
    (hβ : C.form t = β) (d : Fin (C.Q.disk β).n) (k : Fin 5) (o : C.SideOcc)
    (ho : C.port β d k = some o) :
    rhe_cellv C hC (strictReconstruct C hC K t) d.val k = K.col o.1 o.2 2 := by
  subst hβ
  rw [rhe_cellv_side C hC (strictReconstruct C hC K t) d]
  simp [strictReconstruct, ho]


/-- The parent of a block tile with an outer side has the common header. -/
private theorem rhe_header_eq (K : StrictBlock C hC) (h : HeaderKernel.Header C.Typ C.Side)
    (hh : StrictCommonHeader C hC K h) (s : C.Typ) (hs : C.owner s = K.α) (i0 : C.Side s)
    (hout : C.IsOuter (C.occ s i0)) (F : StrictDecTile C hC) (hown : C.owner s = C.form F.typ)
    (hX : K.tileOf s = strictChild C hC F s) : strictHeaderOf C hC F = h := by
  obtain ⟨j, hj⟩ := exists_boundary_side_of_outer C s i0 hout
  have hnp : ¬ C.IsPrint (C.occ s j) := fun hp => rhe_print_not_boundary C _ hp hj
  have e1 := hh.2 s j hs hj
  rw [rhe_tile_cell C hC K s F hX, ((strictChild_cells C hC F s hown j).2 hnp).2.2.2.2.2.2.1 hj]
    at e1
  simp only [headerSU] at e1
  injection e1

/-- Each reconstructed cell is the corresponding cell of a normal identity-correct tile of the
header type whose header is the common header. -/
private theorem rhe_recon_cell (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h)
    (i : C.Side h.1) (k : Fin 5) :
    ∃ c : C.Side h.1 → Fin 5 → SU C hC, IsStrictNormal C hC ⟨h.1, c⟩ ∧
      IsStrictIdentityCorrect C hC ⟨h.1, c⟩ ∧ strictHeaderOf C hC ⟨h.1, c⟩ = h ∧
      (strictReconstruct C hC K h.1).cell i k = c i k := by
  have htf : C.form h.1 = K.α := hh.1
  obtain ⟨o, ho⟩ := rhe_port_some C K.α (Fin.cast (congrArg (fun u => (C.Q.disk u).n) htf) i) k
  have hrec := rhe_recon_port C hC K h.1 K.α htf _ k o ho
  obtain ⟨hown, hout, -⟩ := (C.g3_outerList_mem _ _ _).1 (List.mem_of_getElem? ho)
  have hnc : o.1 ≠ C.central K.α := by
    obtain ⟨s, j⟩ := o
    rintro rfl
    exact (C.g2_central K.α j).1 hout
  have hmemP : o ∈ C.path K.α (Fin.cast (congrArg (fun u => (C.Q.disk u).n) htf) i) k := by
    by_cases hg : C.IsGenuinePath K.α (Fin.cast (congrArg (fun u => (C.Q.disk u).n) htf) i) k
    · exact List.mem_of_mem_head? ((C.g4_path_head _ _ _ hg).trans ho)
    · rw [C.g4_path_trivial _ _ _ hg, ho]
      simp
  have hnp : ¬ C.IsPrint o := fun ⟨_, hp⟩ => isInner_of_isPrintOf C hp hout
  obtain ⟨F, hFown, hX, hFN, hFI⟩ := rhe_parent C hC _ (hK.2 o.1 hown hnc)
  have hFh : strictHeaderOf C hC F = h := rhe_header_eq C hC K h hh o.1 hown o.2 hout F hFown hX
  have hFt : F.typ = h.1 := by rw [← hFh]; rfl
  have hval : K.col o.1 o.2 2 =
      rhe_cellv C hC F (Fin.cast (congrArg (fun u => (C.Q.disk u).n) htf) i).val k := by
    rw [rhe_tile_cell C hC K o.1 F hX]
    exact rhe_child_path C hC F K.α (hFown.symm.trans hown) o.1 hown o.2 hnp _ k hmemP
  obtain ⟨tF, cF⟩ := F
  simp only at hFt
  subst hFt
  refine ⟨cF, hFN, hFI, hFh, ?_⟩
  exact (rhe_cellv_side C hC (strictReconstruct C hC K h.1) i k).symm.trans
    ((hrec.trans hval).trans (rhe_cellv_side C hC ⟨h.1, cF⟩ i k))

/-- `lem:comp/reconstruction` (strict variant): the reconstructed parent `D` of type `t` (with
`D_i(d)` the third cell of port `i` on `σ'd`) is strictly normal (its outer fourth cells, read
from port `4`, are the schedule tags of its type) and identity-correct, and `H(D) = h`. -/
theorem strict_reconstructed_header_eq (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h) :
    IsStrictNormal C hC (strictReconstruct C hC K h.1) ∧
      IsStrictIdentityCorrect C hC (strictReconstruct C hC K h.1) ∧
      strictHeaderOf C hC (strictReconstruct C hC K h.1) = h := by
  refine ⟨fun i k hloc => ?_, fun i => ⟨fun hin hnp => ?_, fun hp => ?_⟩, ?_⟩
  · obtain ⟨c, hN, -, -, he⟩ := rhe_recon_cell C hC K hK h hh i k
    rw [he]
    exact hN i k hloc
  · obtain ⟨c, -, hI, -, he⟩ := rhe_recon_cell C hC K hK h hh i 0
    rw [he]
    exact (hI i).1 hin hnp
  · obtain ⟨c, -, hI, -, he⟩ := rhe_recon_cell C hC K hK h hh i 4
    rw [he]
    exact (hI i).2 hp
  · obtain ⟨t, z⟩ := h
    have key : ∀ d : C.Side t, ∃ c : C.Side t → Fin 5 → SU C hC,
        HeaderKernel.zeroMode C.outerB t (fun d' => c d' 3) = z ∧
          (strictReconstruct C hC K t).cell d 3 = c d 3 := by
      intro d
      obtain ⟨c, -, -, hH, he⟩ := rhe_recon_cell C hC K hK ⟨t, z⟩ hh d 3
      exact ⟨c, eq_of_heq (Sigma.mk.inj hH).2, he⟩
    show (⟨t, HeaderKernel.zeroMode C.outerB t (fun d => (strictReconstruct C hC K t).cell d 3)⟩ :
      HeaderKernel.Header C.Typ C.Side) = ⟨t, z⟩
    congr 1
    funext d
    obtain ⟨c, hz, he⟩ := key d
    rw [← hz]
    simp only [HeaderKernel.zeroMode, he]

/-- Step 1 of the blueprint proof of `strict_path_and_print_recovery`: every nonprint
third signal on a path equals the corresponding reconstructed parent cell. -/
private lemma strict_path_and_print_recovery_step1_signals_aux1
    (C : MacroCertificate P)
    {α : C.Q.Form} {d : Fin (C.Q.disk α).n} {j : Fin 5}
    (hG : C.IsGenuinePath α d j) {o : C.SideOcc}
    (ho : o ∈ C.path α d j) (hp : C.IsPrint o) :
    o = C.partner (C.printOcc α d) := by
  have hown : C.owner o.1 = α := C.g4_path_owner α d j o ho
  have hp' : ∃ e : Fin (C.Q.disk α).n, C.IsPrintOf α e o := by
    unfold MacroData.IsPrint at hp
    rwa [hown] at hp
  obtain ⟨e, hme, hcase⟩ := hp'
  rcases hcase with rfl | rfl
  · exact absurd rfl (C.g4_path_not_central α d j hG _ ho)
  · by_cases hde : e = d
    · rw [hde]
    · exfalso
      have hlast : (C.path α e 0).getLast? =
          some (C.partner (C.printOcc α e)) := C.g4_path_last α e 0 ⟨hme, by decide⟩
      rw [List.getLast?_eq_getElem?] at hlast
      have hterm : C.partner (C.printOcc α e) ∈ C.path α e 0 :=
        List.mem_of_getElem? hlast
      have hne' : (d, j) ≠ (e, (0 : Fin 5)) :=
        fun heq => hde (congrArg Prod.fst heq).symm
      obtain ⟨hde', -⟩ := C.g4_path_disjoint α d e j 0 hne' _ ho hterm
      exact hde hde'.symm

/-- Step 2 of the blueprint proof of `strict_path_and_print_recovery_step1_signals`:
only the final position of a genuine path can carry a print occurrence. -/
private lemma strict_path_and_print_recovery_step1_signals_aux2
    (C : MacroCertificate P)
    {α : C.Q.Form} {d : Fin (C.Q.disk α).n} {j : Fin 5}
    (hG : C.IsGenuinePath α d j) {n : ℕ}
    (hn : n + 1 < (C.path α d j).length) {o : C.SideOcc}
    (ho : (C.path α d j)[n]? = some o) : ¬ C.IsPrint o := by
  intro hp
  have hmem : o ∈ C.path α d j := List.mem_of_getElem? ho
  have heq := strict_path_and_print_recovery_step1_signals_aux1 C hG hmem hp
  have hlast : (C.path α d j).getLast? = some o := by
    rw [heq]
    exact C.g4_path_last α d j hG
  rw [List.getLast?_eq_getElem?] at hlast
  have hnodup := C.g4_path_nodup α d j
  have hne := (List.nodup_iff_getElem?_ne_getElem?).1 hnodup n
    ((C.path α d j).length - 1) (by omega) (by omega)
  exact hne (ho.trans hlast.symm)

/-- A fixed vector cancels in set vadd for the strict block geometry. -/
private lemma strict_path_and_print_recovery_step1_signals_aux_vadd_cancel
    (a : Pt) {S T : Set Pt} (h : a +ᵥ S = a +ᵥ T) : S = T := by
  have hinj : Function.Injective (fun x : Pt => a +ᵥ x) := by
    intro x y hxy
    simpa using hxy
  rw [← Set.image_vadd, ← Set.image_vadd] at h
  exact (Set.image_eq_image hinj).mp h

/-- A placed child side is the block offset added to the unplaced strict side. -/
private lemma strict_path_and_print_recovery_step1_signals_aux_childSide
    (C : MacroCertificate P) (hC : C.Represents τ m)
    (K : StrictBlock C hC) (o : C.SideOcc) :
    K.childSide o = K.v +ᵥ C.occSide o := by
  show (K.v + C.anchor o.1) +ᵥ (C.Q.disk (C.form o.1)).side o.2 =
    K.v +ᵥ (C.anchor o.1 +ᵥ (C.Q.disk (C.form o.1)).side o.2)
  rw [add_vadd]

/-- Step 3 of the blueprint proof of `strict_path_and_print_recovery_step1_signals`:
consecutive nonprint occurrences carry equal third signals. -/
private lemma strict_path_and_print_recovery_step1_signals_aux3
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    {α : C.Q.Form} (hα : α = K.α) {d : Fin (C.Q.disk α).n} {j : Fin 5}
    (hG : C.IsGenuinePath α d j) {o o' : C.SideOcc}
    (hmem : o ∈ C.path α d j) (hmem' : o' ∈ C.path α d j)
    (hchain : o.1 = o'.1 ∨ (C.IsInner o ∧ o' = C.partner o))
    (hnp : ¬ C.IsPrint o) (hnp' : ¬ C.IsPrint o') :
    K.col o.1 o.2 2 = K.col o'.1 o'.2 2 := by
  rcases hchain with hsame | ⟨hinner, hpartner⟩
  · obtain ⟨t, i⟩ := o
    subst hsame
    have hown : C.owner o'.1 = α := C.g4_path_owner α d j (C.occ o'.1 i) hmem
    have hnc : o'.1 ≠ C.central α := C.g4_path_not_central α d j hG (C.occ o'.1 i) hmem
    have hownK : C.owner o'.1 = K.α := hown.trans hα
    have hncK : o'.1 ≠ C.central K.α := by
      rw [← hα]
      exact hnc
    have hlegal : StrictLegal C hC (K.tileOf o'.1) := hK.2 o'.1 hownK hncK
    obtain ⟨B, -, hBA⟩ := strictLegal_properties_step1_parent C hC
      (K.tileOf o'.1) hlegal
    have heqF : α = C.owner o'.1 := hown.symm
    have hcast : C.occ o'.1 i ∈ C.path (C.owner o'.1)
        (cast (congrArg (fun F => Fin (C.Q.disk F).n) heqF) d) j :=
      (strictLegal_properties_step5_path_step1_cast_path C hC heqF d j
        (C.occ o'.1 i)).1 hmem
    have hcast' : C.occ o'.1 o'.2 ∈ C.path (C.owner o'.1)
        (cast (congrArg (fun F => Fin (C.Q.disk F).n) heqF) d) j :=
      (strictLegal_properties_step5_path_step1_cast_path C hC heqF d j
        (C.occ o'.1 o'.2)).1 hmem'
    exact strictLegal_properties_step5_path C hC B (K.tileOf o'.1) hBA _ j i o'.2
      hcast hcast' hnp hnp'
  · subst hpartner
    have hown : C.owner o.1 = α := C.g4_path_owner α d j o hmem
    have hownK : C.owner o.1 = K.α := hown.trans hα
    obtain ⟨t2, j2, hown2, hne2, hside2, hcol2⟩ :=
      hK.1 o.1 o.2 hownK hinner
    have hsideEq : C.occSide (C.occ t2 j2) = C.occSide o := by
      have e1 : K.childSide (C.occ t2 j2) = K.v +ᵥ C.occSide (C.occ t2 j2) :=
        strict_path_and_print_recovery_step1_signals_aux_childSide C hC K (C.occ t2 j2)
      have e2 : K.childSide o = K.v +ᵥ C.occSide o :=
        strict_path_and_print_recovery_step1_signals_aux_childSide C hC K o
      rw [e1, e2] at hside2
      exact strict_path_and_print_recovery_step1_signals_aux_vadd_cancel K.v hside2
    have heqOcc : (C.occ t2 j2 : C.SideOcc) = C.partner o :=
      C.g1_side_unique o (C.occ t2 j2) hinner (hown2.trans hownK.symm) hne2 hsideEq
    have hcolEq : K.col t2 j2 2 = K.col (C.partner o).1 (C.partner o).2 2 :=
      congrArg (fun (p : C.SideOcc) => K.col p.1 p.2 2) heqOcc
    exact (hcol2 2).symm.trans hcolEq

/-- Step 4 of the blueprint proof of `strict_path_and_print_recovery_step1_signals`:
induction along a genuine path from its port to an arbitrary nonprint position. -/
private lemma strict_path_and_print_recovery_step1_signals_aux4
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    {α : C.Q.Form} (hα : α = K.α) {d : Fin (C.Q.disk α).n} {j : Fin 5}
    (hG : C.IsGenuinePath α d j) :
    ∀ n : ℕ, ∀ o : C.SideOcc, (C.path α d j)[n]? = some o → ¬ C.IsPrint o →
      K.col o.1 o.2 2 =
        (match C.port α d j with | some o0 => K.col o0.1 o0.2 2 | none => 0 : SU C hC) := by
  intro n
  induction n with
  | zero =>
    intro o ho _
    have hhead : (C.path α d j).head? = C.port α d j := C.g4_path_head α d j hG
    have h0 : (C.path α d j)[0]? = C.port α d j := by
      rw [← List.head?_eq_getElem?]
      exact hhead
    rw [ho] at h0
    rw [← h0]
  | succ n ih =>
    intro o' ho' hnp'
    obtain ⟨hlt1, -⟩ := (List.getElem?_eq_some_iff).1 ho'
    have hlt0 : n < (C.path α d j).length := by omega
    obtain ⟨o, ho⟩ : ∃ o, (C.path α d j)[n]? = some o :=
      ⟨(C.path α d j)[n], List.getElem?_eq_some_iff.mpr ⟨hlt0, rfl⟩⟩
    have hnp := strict_path_and_print_recovery_step1_signals_aux2 C hG hlt1 ho
    have heqD := ih o ho hnp
    have hmem : o ∈ C.path α d j := List.mem_of_getElem? ho
    have hmem' : o' ∈ C.path α d j := List.mem_of_getElem? ho'
    have hchain := C.g4_path_chain α d j n o o' ho ho'
    have heq2 := strict_path_and_print_recovery_step1_signals_aux3 C hC K hK hα hG
      hmem hmem' hchain hnp hnp'
    rw [← heq2]
    exact heqD

private theorem strict_path_and_print_recovery_step1_signals
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h) :
    ∀ (d : C.Side h.1) (j : Fin 5) (o : C.SideOcc),
      o ∈ C.path (C.form h.1) d j → ¬ C.IsPrint o →
        K.col o.1 o.2 2 = (strictReconstruct C hC K h.1).cell d j := by
  intro d j o ho hnp
  show K.col o.1 o.2 2 = match C.port (C.form h.1) d j with
    | some o0 => K.col o0.1 o0.2 2 | none => 0
  by_cases hG : C.IsGenuinePath (C.form h.1) d j
  · obtain ⟨n, hlt, hn⟩ := List.getElem_of_mem ho
    have ho2 : (C.path (C.form h.1) d j)[n]? = some o :=
      List.getElem?_eq_some_iff.mpr ⟨hlt, hn⟩
    exact strict_path_and_print_recovery_step1_signals_aux4 C hC K hK hh.1 hG n o ho2 hnp
  · rw [C.g4_path_trivial (C.form h.1) d j hG, Option.mem_toList] at ho
    rw [ho]

/-- Step 1 of the blueprint proof of `strict_path_and_print_recovery_step2_prints`: the
penultimate side of the path is an ordinary side of the small owner. -/
private lemma strict_path_and_print_recovery_step2_prints_step1_penultimate
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h)
    (d : C.Side h.1) (hd : C.marked (C.form h.1) d) (k : Fin 5) (hk : k ≠ 4) :
    ∃ o, (C.path (C.form h.1) d k)[(C.path (C.form h.1) d k).length - 2]? = some o ∧
      o.1 = (C.partner (C.printOcc (C.form h.1) d)).1 ∧ C.IsOrdinary o := by
  have _ := hK
  have _ := hh
  have hg : C.IsGenuinePath (C.form h.1) d k := ⟨hd, by omega⟩
  obtain ⟨p, hp⟩ := rhe_port_some C (C.form h.1) d k
  have hhead := (C.g4_path_head _ _ _ hg).trans hp
  have hlast := C.g4_path_last _ _ _ hg
  have hpout : C.IsOuter p :=
    ((C.g3_outerList_mem _ _ _).1 (List.mem_of_getElem? hp)).2.1
  have hpin := C.g4_print_inner (C.form h.1) d hd
  have hne : p ≠ C.partner (C.printOcc (C.form h.1) d) := by
    intro e
    exact isInner_partner C hpin (e ▸ hpout)
  have hlen : 2 ≤ (C.path (C.form h.1) d k).length := by
    generalize hpath : C.path (C.form h.1) d k = l
    cases l with
    | nil => simp [hpath] at hhead
    | cons x l =>
        cases l with
        | nil =>
            simp [hpath] at hhead hlast
            exact absurd (hhead.symm.trans hlast) hne
        | cons y l => simp
  obtain ⟨o, ho⟩ : ∃ o, (C.path (C.form h.1) d k)[
      (C.path (C.form h.1) d k).length - 2]? = some o :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨hop, hord⟩ := C.g4_path_penultimate _ _ _ hg o ho
  exact ⟨o, ho, hop, hord⟩

/-- Step 2 of the blueprint proof of `strict_path_and_print_recovery_step2_prints`: the
penultimate side of the path transports the signal to the reconstructed parent cell. -/
private lemma strict_path_and_print_recovery_step2_prints_step2_signal_transport
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h)
    (d : C.Side h.1) (hd : C.marked (C.form h.1) d) (k : Fin 5) (hk : k ≠ 4)
    (o : C.SideOcc)
    (ho : (C.path (C.form h.1) d k)[(C.path (C.form h.1) d k).length - 2]? = some o)
    (ho_partner : o.1 = (C.partner (C.printOcc (C.form h.1) d)).1)
    (ho_ord : C.IsOrdinary o) :
    K.col o.1 o.2 2 = (strictReconstruct C hC K h.1).cell d k := by
  sorry

/-- Step 3 of the blueprint proof of `strict_path_and_print_recovery_step2_prints`: the
print clause copies the cell from the ordinary side. -/
private lemma strict_path_and_print_recovery_step2_prints_step3_print_clause
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h)
    (d : C.Side h.1) (hd : C.marked (C.form h.1) d) (k : Fin 5) (hk : k ≠ 4)
    (o : C.SideOcc)
    (ho : (C.path (C.form h.1) d k)[(C.path (C.form h.1) d k).length - 2]? = some o)
    (ho_partner : o.1 = (C.partner (C.printOcc (C.form h.1) d)).1)
    (ho_ord : C.IsOrdinary o)
    (F : StrictDecTile C hC) (hFo : C.owner o.1 = C.form F.typ)
    (hX : K.tileOf o.1 = strictChild C hC F o.1) :
    K.col (C.partner (C.printOcc (C.form h.1) d)).1 (C.partner (C.printOcc (C.form h.1) d)).2 k =
      K.col o.1 o.2 2 := by
  sorry

/-- Step 2 of the blueprint proof of `strict_path_and_print_recovery`: the noncentral
owner of each marked print carries the first four reconstructed parent cells. -/
private theorem strict_path_and_print_recovery_step2_prints
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h) :
    ∀ d : C.Side h.1, C.marked (C.form h.1) d → ∀ k : Fin 5, k ≠ 4 →
      K.col (C.partner (C.printOcc (C.form h.1) d)).1
          (C.partner (C.printOcc (C.form h.1) d)).2 k =
        (strictReconstruct C hC K h.1).cell d k := by
  intro d hd k hk
  obtain ⟨o, ho, hop, hord⟩ :=
    strict_path_and_print_recovery_step2_prints_step1_penultimate C hC K hK h hh d hd k hk
  have htrans := strict_path_and_print_recovery_step2_prints_step2_signal_transport C hC K hK h hh
    d hd k hk o ho hop hord
  have hl_nc : o.1 ≠ C.central K.α := by
    rw [hop]
    have h_small := C.g4_print_small (C.form h.1) d hd
    intro h_eq
    have h_owner := C.g5_central_owner K.α
    have heq1 : C.central K.α = C.central (C.owner (C.central K.α)) := by
      rw [h_owner]
    have h_large := (C.g5_large_iff (C.central K.α)).mpr heq1
    rw [← h_eq] at h_large
    rw [h_small] at h_large
    contradiction
  have h_owner : C.owner o.1 = K.α := by
    rw [hop]
    have hp_owner := C.g5_central_owner (C.form h.1)
    have hp_partner :=
      (C.g1_partner (C.printOcc (C.form h.1) d) (C.g4_print_inner (C.form h.1) d hd)).2.1
    have h_eq : C.owner (C.partner (C.printOcc (C.form h.1) d)).1 = C.form h.1 := by
      exact hp_partner.trans hp_owner
    exact h_eq.trans hh.1
  have hL := hK.2 o.1 h_owner hl_nc
  obtain ⟨ch, hch0, hch_step, hch_origin⟩ := hL
  have hc : IsStrictChildOf C hC (ch 1) (K.tileOf o.1) := by
    have h_eq : ch 0 = K.tileOf o.1 := hch0
    rw [← h_eq]
    exact hch_step 0
  have heq : C.owner o.1 = C.form (ch 1).typ := hc.1
  have hcl := strict_path_and_print_recovery_step2_prints_step3_print_clause C hC K hK h hh
    d hd k hk o ho hop hord (ch 1) heq hc.2
  exact hcl.trans htrans



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
  exact ⟨strict_path_and_print_recovery_step1_signals C hC K hK h hh,
    strict_path_and_print_recovery_step2_prints C hC K hK h hh⟩

/-- Step 1 of the blueprint proof of `strict_macroblock_is_decomposition_step1_noncentral`: owner matches. -/
private theorem strict_macroblock_is_decomposition_step1_noncentral_step1_owner
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h)
    (t : C.Typ) (ht_owner : C.owner t = K.α) (ht_nc : t ≠ C.central K.α) :
    C.owner t = C.form (strictReconstruct C hC K h.1).typ := by
  have _ := hK
  have _ := ht_nc
  rw [ht_owner, ← hh.1]
  rfl

/-- Step 2 of the blueprint proof of `strict_macroblock_is_decomposition_step1_noncentral`: prints are correct. -/
private theorem strict_macroblock_is_decomposition_step1_noncentral_step2_prints
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h)
    (t : C.Typ) (ht_owner : C.owner t = K.α) (ht_nc : t ≠ C.central K.α) :
    ∀ i : C.Side t,
      C.IsPrint (C.occ t i) →
        ∀ j : Fin 5, (K.tileOf t).cell i j = (strictChild C hC (strictReconstruct C hC K h.1) t).cell i j := by
  sorry

/-- Step 1 of the blueprint proof of `strict_macroblock_is_decomposition_step1_noncentral_step3_nonprints`: nonprints are correct for origin cells. -/
private lemma strict_macroblock_is_decomposition_step1_noncentral_step3_nonprints_aux1_origin
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h)
    (t : C.Typ) (ht_owner : C.owner t = K.α) (ht_nc : t ≠ C.central K.α) :
    ∀ i : C.Side t,
      ¬ C.IsPrint (C.occ t i) →
        ∀ j : Fin 5,
        ¬ (copySource C (C.form (strictReconstruct C hC K h.1).typ) (C.occ t i) j).Nonempty →
          (K.tileOf t).cell i j = (strictChild C hC (strictReconstruct C hC K h.1) t).cell i j := by
  intros i hnp j hns
  have hL : StrictLegal C hC (K.tileOf t) := hK.2 t ht_owner ht_nc
  rcases hL with ⟨ch, ch_zero, ch_child, _⟩
  have hchild : IsStrictChildOf C hC (ch 1) (ch 0) := ch_child 0
  have hchild0 : IsStrictChildOf C hC (ch 1) (K.tileOf t) := ch_zero ▸ hchild
  rcases hchild0 with ⟨hF_ch1, h_eq⟩
  have hF2 : C.form (strictReconstruct C hC K h.1).typ = K.α := by
    calc C.form (strictReconstruct C hC K h.1).typ = C.form h.1 := rfl
    _ = K.α := hh.1
  have H_LHS : (K.tileOf t).cell i j = strictGenCell C hC K.α (headerSU C hC (strictHeaderOf C hC (ch 1))) (C.occ t i) j := by
    have H1 : (K.tileOf t).cell i j = (strictChild C hC (ch 1) (K.tileOf t).typ).cell i j := by congr 1
    have H2 : (K.tileOf t).cell i j = (strictChild C hC (ch 1) t).cell i j := H1
    rw [H2]
    dsimp [strictChild, strictGen]
    have hF1 : C.form (ch 1).typ = K.α := by
      calc C.form (ch 1).typ = C.owner (K.tileOf t).typ := hF_ch1.symm
      _ = C.owner t := rfl
      _ = K.α := ht_owner
    have hns_K : ¬(copySource C K.α (C.occ t i) j).Nonempty := hF2 ▸ hns
    have hns_ch1 : ¬(copySource C (C.form (ch 1).typ) (C.occ t i) j).Nonempty := hF1.symm ▸ hns_K
    rw [dif_neg hns_ch1]
    congr 2
  have H_RHS : (strictChild C hC (strictReconstruct C hC K h.1) t).cell i j = strictGenCell C hC K.α (headerSU C hC h) (C.occ t i) j := by
    dsimp [strictChild, strictGen]
    rw [dif_neg hns]
    have h_hdr : strictHeaderOf C hC (strictReconstruct C hC K h.1) = h := (strict_reconstructed_header_eq C hC K hK h hh).2.2
    rw [h_hdr]
    congr 2
  rw [H_LHS, H_RHS]
  dsimp [strictGenCell]
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · subst h5
    have H_hh : (K.tileOf t).cell i 3 = headerSU C hC h := hh.2 t i ht_owner h7
    have H_LHS_3 : (K.tileOf t).cell i 3 = strictGenCell C hC K.α (headerSU C hC (strictHeaderOf C hC (ch 1))) (C.occ t i) 3 := H_LHS
    have H_LHS_4 : strictGenCell C hC K.α (headerSU C hC (strictHeaderOf C hC (ch 1))) (C.occ t i) 3 = headerSU C hC (strictHeaderOf C hC (ch 1)) := by
      dsimp [strictGenCell]
      rw [if_neg h1, if_neg h6, if_pos h7]
    have H_eq : headerSU C hC (strictHeaderOf C hC (ch 1)) = headerSU C hC h := by
      calc headerSU C hC (strictHeaderOf C hC (ch 1)) = strictGenCell C hC K.α (headerSU C hC (strictHeaderOf C hC (ch 1))) (C.occ t i) 3 := H_LHS_4.symm
      _ = (K.tileOf t).cell i 3 := H_LHS_3.symm
      _ = headerSU C hC h := H_hh
    rw [H_eq]
  · rfl
  · rfl

/-- Step 2 of the blueprint proof of `strict_macroblock_is_decomposition_step1_noncentral_step3_nonprints`: nonprints are correct for copied cells. -/
private lemma strict_macroblock_is_decomposition_step1_noncentral_step3_nonprints_aux2_copied
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h)
    (t : C.Typ) (ht_owner : C.owner t = K.α) (ht_nc : t ≠ C.central K.α) :
    ∀ i : C.Side t,
      ¬ C.IsPrint (C.occ t i) →
        ∀ j : Fin 5,
        (copySource C (C.form (strictReconstruct C hC K h.1).typ) (C.occ t i) j).Nonempty →
          (K.tileOf t).cell i j = (strictChild C hC (strictReconstruct C hC K h.1) t).cell i j := by
  sorry

/-- Step 3 of the blueprint proof of `strict_macroblock_is_decomposition_step1_noncentral`: nonprints are correct. -/
private theorem strict_macroblock_is_decomposition_step1_noncentral_step3_nonprints
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h)
    (t : C.Typ) (ht_owner : C.owner t = K.α) (ht_nc : t ≠ C.central K.α) :
    ∀ i : C.Side t,
      ¬ C.IsPrint (C.occ t i) →
        ∀ j : Fin 5, (K.tileOf t).cell i j = (strictChild C hC (strictReconstruct C hC K h.1) t).cell i j := by
  intro i hnp j
  by_cases hsource : (copySource C (C.form (strictReconstruct C hC K h.1).typ) (C.occ t i) j).Nonempty
  · exact strict_macroblock_is_decomposition_step1_noncentral_step3_nonprints_aux2_copied C hC K hK h hh t ht_owner ht_nc i hnp j hsource
  · exact strict_macroblock_is_decomposition_step1_noncentral_step3_nonprints_aux1_origin C hC K hK h hh t ht_owner ht_nc i hnp j hsource

/-- Step 1 of the blueprint proof of `strict_macroblock_is_decomposition`: every noncentral
tile in the block has the required strict child colours of the reconstructed parent. -/
private theorem strict_macroblock_is_decomposition_step1_noncentral
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h)
    (t : C.Typ) (ht_owner : C.owner t = K.α) (ht_nc : t ≠ C.central K.α) :
    IsStrictChildOf C hC (strictReconstruct C hC K h.1) (K.tileOf t) := by
  dsimp [IsStrictChildOf]
  constructor
  · exact strict_macroblock_is_decomposition_step1_noncentral_step1_owner C hC K hK h hh t ht_owner ht_nc
  · have ht : K.tileOf t = ⟨t, (K.tileOf t).cell⟩ := rfl
    have hc : strictChild C hC (strictReconstruct C hC K h.1) ((K.tileOf t).typ) = ⟨t, (strictChild C hC (strictReconstruct C hC K h.1) t).cell⟩ := rfl
    nth_rewrite 1 [ht]
    nth_rewrite 1 [hc]
    congr 1
    funext d j
    by_cases hp : C.IsPrint (C.occ t d)
    · exact strict_macroblock_is_decomposition_step1_noncentral_step2_prints C hC K hK h hh t ht_owner ht_nc d hp j
    · exact strict_macroblock_is_decomposition_step1_noncentral_step3_nonprints C hC K hK h hh t ht_owner ht_nc d hp j

/-- Step 2 of the blueprint proof of `strict_macroblock_is_decomposition`: the central tile
has the required strict child colours of the reconstructed parent. -/
private theorem strict_macroblock_is_decomposition_step2_central
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h)
    (t : C.Typ) (ht_owner : C.owner t = K.α) (ht_c : t = C.central K.α) :
    IsStrictChildOf C hC (strictReconstruct C hC K h.1) (K.tileOf t) := by
  sorry

/-- `lem:comp/exact` (strict variant): the block is the strict decomposition of its
reconstructed parent.  Legal boundary witnesses identify the template, so the generated
schedules `W(α, e)` of its outer sides agree with the decomposition of `D`, independently of
the fourth values of `D`. -/
theorem strict_macroblock_is_decomposition (K : StrictBlock C hC)
    (hK : StrictBlockContext C hC K) (h : HeaderKernel.Header C.Typ C.Side)
    (hh : StrictCommonHeader C hC K h) :
    IsStrictExactBlockOf C hC K (strictReconstruct C hC K h.1) := by
  refine ⟨hh.1, ?_⟩
  intro t ht_owner
  by_cases ht_c : t = C.central K.α
  · exact strict_macroblock_is_decomposition_step2_central C hC K hK h hh t ht_owner ht_c
  · exact strict_macroblock_is_decomposition_step1_noncentral C hC K hK h hh t ht_owner ht_c

/-- Step 1 of the blueprint proof of `strict_reconstructed_cyclic_legal`: exact decomposition
identifies the centre as the central child of the reconstructed parent. -/
private theorem strict_reconstructed_cyclic_legal_step1_central_child
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h) :
    IsStrictChildOf C hC (strictReconstruct C hC K h.1) K.centre := by
  have hex := strict_macroblock_is_decomposition C hC K hK h hh
  exact hex.2 _ (C.g5_central_owner K.α)

/-- Step 2 of the blueprint proof of `strict_reconstructed_cyclic_legal`: on a marked side,
the cyclic central child copies the reconstructed parent's first four cells. -/
private theorem strict_reconstructed_cyclic_legal_step2_marked_first_four
    (D A : StrictDecTile C hC) (hDA : IsStrictChildOf C hC D A)
    (hcyc : C.IsCyclic D.typ) (hEq : D.typ = A.typ) :
    ∀ i : C.Side A.typ, C.marked (C.form A.typ) i → ∀ k : Fin 5, k ≠ 4 →
      D.cell (Fin.cast (congrArg (fun t => (C.Q.disk (C.form t)).n) hEq.symm) i) k =
        A.cell i k := by
  obtain ⟨tD, cD⟩ := D
  obtain ⟨tA, cA⟩ := A
  dsimp only at hEq
  subst tA
  change C.central (C.form tD) = tD at hcyc
  have hown : C.owner tD = C.form tD := by
    have h := C.g5_central_owner (C.form tD)
    rw [hcyc] at h
    exact h
  have hlarge : C.kind (C.form tD) = .large := by
    apply (C.g5_large_iff tD).2
    rw [hown]
    exact hcyc.symm
  intro i hm k hk
  have hprint : C.IsPrintOf (C.form tD) i (C.occ tD i) := by
    refine ⟨hm, Or.inl ?_⟩
    have hp := C.g5_print_id_large (C.form tD) i hlarge hm
    show (⟨tD, i⟩ : C.SideOcc) =
      ⟨C.central (C.form tD), C.print (C.form tD) i⟩
    generalize C.print (C.form tD) i = p at hp
    revert p
    rw [hcyc]
    intro p hp
    exact Sigma.ext rfl (heq_of_eq (Fin.ext hp.symm))
  have hcopy : (strictChild C hC ⟨tD, cD⟩ tD).cell i k = cD i k :=
    ((strictChild_cells C hC ⟨tD, cD⟩ tD hown i).1 i hprint).1 k hk
  have h3 : cA = (strictChild C hC ⟨tD, cD⟩ tD).cell :=
    eq_of_heq (StrictDecTile.mk.inj hDA.2).2
  change cD i k = cA i k
  rw [h3]
  exact hcopy.symm

/-- Step 3 of the blueprint proof of `strict_reconstructed_cyclic_legal`: the fifth cell on a
marked side agrees because it is local on nonprints and the print identity is fixed. -/
private theorem strict_reconstructed_cyclic_legal_step3_marked_fifth
    (D A : StrictDecTile C hC) (hDA : IsStrictChildOf C hC D A)
    (hcyc : C.IsCyclic D.typ) (hEq : D.typ = A.typ)
    (hDN : IsStrictNormal C hC D) (hAN : IsStrictNormal C hC A) :
    ∀ i : C.Side A.typ, C.marked (C.form A.typ) i →
      D.cell (Fin.cast (congrArg (fun t => (C.Q.disk (C.form t)).n) hEq.symm) i) 4 =
        A.cell i 4 := by
  obtain ⟨tD, cD⟩ := D
  obtain ⟨tA, cA⟩ := A
  dsimp only at hEq
  subst hEq
  intro i hm
  have h_locA : IsStrictLocal C (C.occ tD i) 4 := by
    left; unfold IsLocal
    by_cases hp : C.IsPrint (C.occ tD i)
    · right; left; exact ⟨hm, Or.inr hp, rfl⟩
    · by_cases hs : C.special (C.occ tD i)
      · right; left; exact ⟨hm, Or.inl hs, rfl⟩
      · right; right; exact ⟨hm, ⟨hs, hp⟩, Or.inr rfl⟩
  have eqA := hAN i 4 h_locA
  have eqD := hDN (Fin.cast rfl i) 4 (by exact h_locA)
  change cD _ 4 = cA i 4
  change cD _ 4 = _ at eqD
  change cA i 4 = _ at eqA
  rw [eqD, eqA]
  rfl

/-- Step 4 of the blueprint proof of `strict_reconstructed_cyclic_legal`: every cell on an
unmarked side is local and therefore is determined by the common type. -/
private theorem strict_reconstructed_cyclic_legal_step4_unmarked_local
    (D A : StrictDecTile C hC) (hDA : IsStrictChildOf C hC D A)
    (hEq : D.typ = A.typ) (hDN : IsStrictNormal C hC D)
    (hAN : IsStrictNormal C hC A) :
    ∀ i : C.Side A.typ, ¬ C.marked (C.form A.typ) i → ∀ k : Fin 5,
      D.cell (Fin.cast (congrArg (fun t => (C.Q.disk (C.form t)).n) hEq.symm) i) k =
        A.cell i k := by
  intro i hUnmarked k
  let i' := Fin.cast (congrArg (fun t => (C.Q.disk (C.form t)).n) hEq.symm) i
  have hOccEq : C.occ D.typ i' = C.occ A.typ i := by
    dsimp [i']
    obtain ⟨tA, cA⟩ := A
    obtain ⟨tD, cD⟩ := D
    dsimp at hEq i ⊢
    subst hEq
    rfl
  have hLocalA : IsStrictLocal C (C.occ A.typ i) k := by
    left
    unfold IsLocal
    left
    exact hUnmarked
  have hLocalD : IsStrictLocal C (C.occ D.typ i') k := by
    rw [hOccEq]
    exact hLocalA
  have hPresc : strictPrescribedCell C hC (C.occ D.typ i') k = strictPrescribedCell C hC (C.occ A.typ i) k := by
    rw [hOccEq]
  rw [hDN i' k hLocalD, hAN i k hLocalA, hPresc]

/-- `lem:comp/cyclic-legal` (strict variant): if the centre of the block is legal and the type
of `D` is cyclic, then `D` is the centre and is legal. -/
theorem strict_reconstructed_cyclic_legal (K : StrictBlock C hC)
    (hK : StrictBlockContext C hC K) (h : HeaderKernel.Header C.Typ C.Side)
    (hh : StrictCommonHeader C hC K h) (hA : StrictLegal C hC K.centre)
    (hcyc : C.IsCyclic h.1) :
    strictReconstruct C hC K h.1 = K.centre ∧ StrictLegal C hC (strictReconstruct C hC K h.1) := by
  let D := strictReconstruct C hC K h.1
  let A := K.centre
  have hcentral : C.central K.α = h.1 := by
    rw [← hh.1]
    exact hcyc
  have hEq : D.typ = A.typ := hcentral.symm
  have hDA : IsStrictChildOf C hC D A := by
    exact strict_reconstructed_cyclic_legal_step1_central_child C hC K hK h hh
  have hDprops := strict_reconstructed_header_eq C hC K hK h hh
  have hDN : IsStrictNormal C hC D ∧ IsStrictIdentityCorrect C hC D :=
    ⟨hDprops.1, hDprops.2.1⟩
  have hAN : IsStrictNormal C hC A := (strictLegal_properties C hC K.centre hA).2.1
  have hmarked := strict_reconstructed_cyclic_legal_step2_marked_first_four C hC D A hDA hcyc hEq
  have hfifth := strict_reconstructed_cyclic_legal_step3_marked_fifth C hC D A hDA hcyc hEq
    hDN.1 hAN
  have hunmarked := strict_reconstructed_cyclic_legal_step4_unmarked_local C hC D A hDA hEq
    hDN.1 hAN
  have hDA_eq : D = A := by
    obtain ⟨tD, cD⟩ := D
    obtain ⟨tA, cA⟩ := A
    simp only at hEq
    subst hEq
    congr
    funext i k
    by_cases hm : C.marked (C.form tD) i
    · by_cases hk : k = 4
      · subst hk
        exact hfifth i hm
      · exact hmarked i hm k hk
    · exact hunmarked i hm k
  have hlegD : StrictLegal C hC D := by
    rw [hDA_eq]
    exact hA
  exact ⟨by simpa [D, A] using hDA_eq, by simpa [D] using hlegD⟩

private theorem ncl_identSU_ne_zero (e : C.EdgeId) : identSU C hC e ≠ 0 := by
  intro h; cases h

private theorem ncl_identSU_inj {e e' : C.EdgeId} (h : identSU C hC e = identSU C hC e') :
    e = e' := by
  simp only [identSU] at h
  cases h; rfl


private theorem ncl_isPrint_iff {s : C.Typ} {β : C.Q.Form} (hs : C.owner s = β) (i : C.Side s) :
    C.IsPrint (C.occ s i) ↔ ∃ d : Fin (C.Q.disk β).n, C.IsPrintOf β d (C.occ s i) := by
  subst hs
  rfl

private theorem ncl_not_on_path {s : C.Typ} {β : C.Q.Form} (hs : C.owner s = β) (i : C.Side s)
    (hm : ¬ C.IsMarked (C.occ s i)) (d : Fin (C.Q.disk β).n) (j : Fin 5) :
    C.occ s i ∉ C.path β d j := by
  subst hs
  intro hmem
  by_cases hg : C.IsGenuinePath (C.owner s) d j
  · exact hm (C.g7_marking _ (Or.inr (Or.inr (Or.inr ⟨d, j, hg, hmem⟩))))
  · rw [C.g4_path_trivial _ d j hg, Option.mem_toList] at hmem
    have hmem' : C.occ s i ∈ C.outerList _ d := List.mem_iff_getElem?.mpr ⟨_, hmem⟩
    exact hm (C.g7_marking _ (Or.inl ((C.g3_outerList_mem _ d _).1 hmem').2.1))


private theorem ncl_child_normal (Q' : StrictDecTile C hC) (s : C.Typ)
    (hs : C.owner s = C.form Q'.typ) :
    IsStrictNormal C hC (strictChild C hC Q' s) ∧
      IsStrictIdentityCorrect C hC (strictChild C hC Q' s) := by
  have hcells := strictChild_cells C hC Q' s hs
  have key : ∀ (i : C.Side s) (k : Fin 5), IsStrictLocal C (C.occ s i) k →
      (strictChild C hC Q' s).cell i k = strictPrescribedCell C hC (C.occ s i) k := by
    intro i k hloc
    by_cases hp : C.IsPrint (C.occ s i)
    · obtain ⟨d, hd⟩ := (ncl_isPrint_iff C hs i).1 hp
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
        have hnpath := ncl_not_on_path C hs i hnm
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
  · obtain ⟨d, hd⟩ := (ncl_isPrint_iff C hs i).1 hp
    exact ((hcells i).1 d hd).2


private theorem ncl_origin_shift (f : ℕ → DecTile C) (a : ℕ) :
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

/-- The cell of a strict tile indexed by the value of a side index (zero out of range). -/
private def ncl_cellv (X : StrictDecTile C hC) (v : ℕ) (k : Fin 5) : SU C hC :=
  if h : v < (C.Q.disk (C.form X.typ)).n then X.cell ⟨v, h⟩ k else 0

private theorem ncl_cellv_side (X : StrictDecTile C hC) (i : C.Side X.typ) (k : Fin 5) :
    ncl_cellv C hC X i.val k = X.cell i k := by
  unfold ncl_cellv
  rw [dif_pos i.isLt]

private theorem ncl_marked_cast_iff {β β' : C.Q.Form} (h : β = β') (d : Fin (C.Q.disk β).n) :
    C.marked β' (Fin.cast (congrArg (fun u => (C.Q.disk u).n) h) d) ↔ C.marked β d := by
  subst h
  rfl

private theorem ncl_anchor_eq {q q' : C.Q.Form} (h : q' = q) (v w : Pt) (i : Fin (C.Q.disk q).n)
    (hs : (⟨q', w⟩ : PlacedTile C.Q).side (Fin.cast (congrArg (fun u => (C.Q.disk u).n) h.symm) i) =
      (⟨q, v⟩ : PlacedTile C.Q).side i) : w = v := by
  subst h
  exact anchor_eq_of_side_eq i hs

/-- A print side of a noncentral type is its special side. -/
private theorem ncl_print_special {s : C.Typ} (hs : ¬ C.IsCentral s) (i : C.Side s)
    (hp : C.IsPrint (C.occ s i)) : C.special (C.occ s i) := by
  obtain ⟨d, hm, h | h⟩ := hp
  · exact absurd (congrArg Sigma.fst h).symm hs
  · rw [h]
    exact C.g4_print_special _ d hm

/-- A marked outer side of a normal tile has first cell zero. -/
private theorem ncl_outer_cell0 (Z : StrictDecTile C hC) (hN : IsStrictNormal C hC Z)
    (i : C.Side Z.typ) (hm : C.marked (C.form Z.typ) i) (ho : C.IsOuter (C.occ Z.typ i)) :
    Z.cell i 0 = 0 := by
  have hsp : ¬ C.special (C.occ Z.typ i) := fun h => C.g6_special_inner _ h ho
  have hpr : ¬ C.IsPrint (C.occ Z.typ i) := fun ⟨_, hd⟩ => isInner_of_isPrintOf C hd ho
  rw [hN i 0 (Or.inl (Or.inr (Or.inr ⟨hm, ⟨hsp, hpr⟩, Or.inl rfl⟩)))]
  simp [strictPrescribedCell, MacroData.IsInner, ho]

/-- The type components of a first-cell interface identity. -/
private def ncl_fp : SU C hC → Multiset C.Typ
  | .ordinary (Sum.inr (Sum.inr (Sum.inl e))) => {(C.edgeTypes e).1, (C.edgeTypes e).2}
  | _ => 0

private theorem ncl_fp_card (x : SU C hC) : Multiset.card (ncl_fp C hC x) ≤ 2 := by
  rcases x with _ | (_ | _ | _ | _ | _) | _ <;> simp [ncl_fp]

open Classical in
/-- The marked first-cell fingerprint of a normal identity-correct small noncentral tile is
one of the possible fingerprints of its type. -/
private theorem ncl_fp_mem (Z : StrictDecTile C hC) (hZc : ¬ C.IsCentral Z.typ)
    (hs : C.kind (C.form Z.typ) = .small)
    (hN : IsStrictNormal C hC Z) (hI : IsStrictIdentityCorrect C hC Z) :
    (∑ i : C.Side Z.typ, if C.marked (C.form Z.typ) i then ncl_fp C hC (Z.cell i 0) else 0) ∈
      C.possibleFingerprints Z.typ := by
  obtain ⟨s, hs1, hs2⟩ := C.g6_special_unique Z.typ hs
  unfold MacroData.possibleFingerprints
  rw [if_pos hs]
  refine ⟨if C.marked (C.form Z.typ) s then ncl_fp C hC (Z.cell s 0) else 0, ?_, ?_⟩
  · split_ifs
    · exact ncl_fp_card C hC _
    · simp
  · have hx : (if C.marked (C.form Z.typ) s then ncl_fp C hC (Z.cell s 0) else 0) =
        ∑ i : C.Side Z.typ,
          if i = s then (if C.marked (C.form Z.typ) i then ncl_fp C hC (Z.cell i 0) else 0)
          else 0 := by
      simp
    unfold MacroData.baseFingerprint
    rw [hx, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases his : i = s
    · subst his
      have hnfp : ¬ C.IsFingerprintSide (C.occ Z.typ i) := fun h => h.2.1.1 hs1
      simp [hnfp]
    · rw [if_neg his, add_zero]
      by_cases hm : C.marked (C.form Z.typ) i
      · rw [if_pos hm]
        by_cases hin : C.IsInner (C.occ Z.typ i)
        · have hsp : ¬ C.special (C.occ Z.typ i) := fun h => his (hs2 i h)
          have hpr : ¬ C.IsPrint (C.occ Z.typ i) := fun h => hsp (ncl_print_special C hZc i h)
          have hfp : C.IsFingerprintSide (C.occ Z.typ i) := ⟨hin, ⟨hsp, hpr⟩, fun _ => hm⟩
          rw [if_pos hfp, (hI i).1 hin hpr]
          rfl
        · have hnfp : ¬ C.IsFingerprintSide (C.occ Z.typ i) := fun h => hin h.1
          rw [if_neg hnfp, ncl_outer_cell0 C hC Z hN i hm (not_not.1 hin)]
          rfl
      · have hnfp : ¬ C.IsFingerprintSide (C.occ Z.typ i) := fun h => hm (h.2.2 hs)
        rw [if_neg hm, if_neg hnfp]

open Classical in
/-- Two normal identity-correct noncentral tiles of the same form agreeing on the first four
cells of all marked sides have the same type (`(G1)` for original forms, the fingerprint
certificate `(G6)` for small forms). -/
private theorem ncl_typ_eq (X Y : StrictDecTile C hC) (hXc : ¬ C.IsCentral X.typ)
    (hYc : ¬ C.IsCentral Y.typ) (hf : C.form Y.typ = C.form X.typ)
    (hXN : IsStrictNormal C hC X) (hXI : IsStrictIdentityCorrect C hC X)
    (hYN : IsStrictNormal C hC Y) (hYI : IsStrictIdentityCorrect C hC Y)
    (hcell : ∀ d : C.Side X.typ, C.marked (C.form X.typ) d → ∀ k : Fin 5, k ≠ 4 →
      ncl_cellv C hC Y d.val k = X.cell d k) : Y.typ = X.typ := by
  have hn : (C.Q.disk (C.form X.typ)).n = (C.Q.disk (C.form Y.typ)).n :=
    congrArg (fun u => (C.Q.disk u).n) hf.symm
  have hcast : ∀ d : C.Side X.typ, ncl_cellv C hC Y d.val 0 = Y.cell (Fin.cast hn d) 0 := by
    intro d
    rw [← ncl_cellv_side C hC Y (Fin.cast hn d), Fin.val_cast]
  have hmk : ∀ d : C.Side X.typ, C.marked (C.form Y.typ) (Fin.cast hn d) ↔
      C.marked (C.form X.typ) d := ncl_marked_cast_iff C hf.symm
  have hnl : C.kind (C.form X.typ) ≠ .large := fun hl => hXc ((C.g5_large_iff _).1 hl).symm
  by_contra hne
  cases hk : C.kind (C.form X.typ) with
  | large => exact hnl hk
  | original =>
    obtain ⟨i, hin, hm⟩ := C.g5_original_marked X.typ hk
    have hXp : ¬ C.IsPrint (C.occ X.typ i) := by
      intro hp
      have h1 := C.g6_special_small _ (ncl_print_special C hXc i hp)
      change C.kind (C.form X.typ) = .small at h1
      rw [hk] at h1
      cases h1
    have hYk : C.kind (C.form Y.typ) = .original := by rw [hf]; exact hk
    have hYp : ¬ C.IsPrint (C.occ Y.typ (Fin.cast hn i)) := by
      intro hp
      have h1 := C.g6_special_small _ (ncl_print_special C hYc _ hp)
      change C.kind (C.form Y.typ) = .small at h1
      rw [hYk] at h1
      cases h1
    have e3 := hcell i hm 0 (by decide)
    rw [hcast, (hXI i).1 hin hXp] at e3
    have hYin : C.IsInner (C.occ Y.typ (Fin.cast hn i)) := by
      intro ho
      rw [ncl_outer_cell0 C hC Y hYN _ ((hmk i).2 hm) ho] at e3
      exact ncl_identSU_ne_zero C hC _ e3.symm
    rw [(hYI _).1 hYin hYp] at e3
    have hedge := ncl_identSU_inj C hC e3
    rcases C.g1_edge_unique _ _ hin hYin hedge.symm with h | h
    · exact hne (congrArg Sigma.fst h)
    · obtain ⟨hpne, hown, hside⟩ := C.g1_partner _ hin
      rw [← h] at hpne hown hside
      have ha : C.anchor Y.typ = C.anchor X.typ := ncl_anchor_eq C hf _ _ i hside
      exact hpne (C.type_injective _ _ hown hf ha)
  | small =>
    have hYs : C.kind (C.form Y.typ) = .small := by rw [hf]; exact hk
    refine Set.disjoint_left.1 (C.g6_fingerprint _ _ hne hYc hXc)
      (ncl_fp_mem C hC Y hYc hYs hYN hYI) ?_
    convert ncl_fp_mem C hC X hXc hk hXN hXI using 1
    rw [← Equiv.sum_comp (finCongr hn)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [finCongr_apply]
    by_cases hm : C.marked (C.form X.typ) i
    · rw [if_pos ((hmk i).2 hm), if_pos hm, ← hcast, hcell i hm 0 (by decide)]
    · rw [if_neg hm, if_neg (fun h => hm ((hmk i).1 h))]

/-- Two normal identity-correct noncentral tiles of the same form agreeing on the first four
cells of all marked sides are equal. -/
private theorem ncl_ident (X Y : StrictDecTile C hC) (hXc : ¬ C.IsCentral X.typ)
    (hYc : ¬ C.IsCentral Y.typ) (hf : C.form Y.typ = C.form X.typ)
    (hXN : IsStrictNormal C hC X) (hXI : IsStrictIdentityCorrect C hC X)
    (hYN : IsStrictNormal C hC Y) (hYI : IsStrictIdentityCorrect C hC Y)
    (hcell : ∀ d : C.Side X.typ, C.marked (C.form X.typ) d → ∀ k : Fin 5, k ≠ 4 →
      ncl_cellv C hC Y d.val k = X.cell d k) : Y = X := by
  have htyp := ncl_typ_eq C hC X Y hXc hYc hf hXN hXI hYN hYI hcell
  obtain ⟨tX, cX⟩ := X
  obtain ⟨tY, cY⟩ := Y
  simp only at htyp
  subst htyp
  congr
  funext i k
  by_cases hk : C.marked (C.form tY) i ∧ k ≠ 4
  · have := hcell i hk.1 k hk.2
    rw [ncl_cellv_side C hC ⟨tY, cY⟩ i] at this
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

/-- The central child of a parent copies the first four cells of every marked parent side
onto its print. -/
private theorem ncl_child_copy (Q' : StrictDecTile C hC) (β : C.Q.Form) (hβ : C.form Q'.typ = β)
    (d : Fin (C.Q.disk β).n) (hd : C.marked β d) (k : Fin 5) (hk : k ≠ 4) :
    ncl_cellv C hC (strictChild C hC Q' (C.central β)) (C.print β d).val k =
      ncl_cellv C hC Q' d.val k := by
  subst hβ
  have hown := C.g5_central_owner (C.form Q'.typ)
  have hc := ((strictChild_cells C hC Q' _ hown (C.print (C.form Q'.typ) d)).1 d
    ⟨hd, Or.inl rfl⟩).1 k hk
  rw [ncl_cellv_side C hC (strictChild C hC Q' (C.central (C.form Q'.typ))) (C.print _ d), hc,
    ncl_cellv_side]

/-- Equal nondegenerate segments have the same endpoints. -/
private theorem ncl_seg_endpoints
    {a b c d : Pt} (hab : a ≠ b) (h : segment ℝ a b = segment ℝ c d) :
    (c = a ∧ d = b) ∨ (c = b ∧ d = a) := by
  have mem_segment_iff' {x y z : Pt} :
      z ∈ segment ℝ x y ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = x + t • (y - x) := by
    rw [segment_eq_image']
    constructor
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      exact ⟨t, ht0, ht1, rfl⟩
    · rintro ⟨t, ht0, ht1, rfl⟩
      exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
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
    rw [zero_smul]
    exact (add_eq_left.1 hα.symm).symm
  have e2 : (1 : ℝ) • (b - a) = (s + β * (t - s)) • (b - a) := by
    rw [one_smul]
    have h' : a + (b - a) = a + (s + β * (t - s)) • (b - a) := by
      rw [← hβ]
      abel
    exact add_left_cancel h'
  have f1 := smul_left_injective ℝ hu e1
  have f2 := smul_left_injective ℝ hu e2
  have key : (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    have h3 : s * (1 - α) = 0 := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.2 ha1), mul_nonneg ha0 ht0]
    have h4 : α * t = 0 := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.2 ha1), mul_nonneg ha0 ht0]
    rcases mul_eq_zero.1 h3 with h3 | h3
    · subst h3
      have h' : β * t = 1 := by linarith
      left
      refine ⟨rfl, ?_⟩
      nlinarith
    · have hα1 : α = 1 := by linarith
      subst hα1
      have ht : t = 0 := by linarith
      subst ht
      right
      refine ⟨?_, rfl⟩
      nlinarith
  rcases key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    constructor <;> simp
  · right
    constructor <;> simp

/-- A print side is
strictly internal to its template and therefore cannot be a boundary side. -/
private theorem ncl_print_not_boundary (o : C.SideOcc) (h_print : C.IsPrint o) :
    ¬ C.IsBoundary o := by
  obtain ⟨d, hpd⟩ := h_print
  let α : C.Q.Form := C.owner o.1
  change C.marked α d ∧ (o = C.printOcc α d ∨ o = C.partner (C.printOcc α d)) at hpd
  rcases hpd with ⟨hmarked, hprint | hpartner⟩
  · rw [hprint]
    exact (C.g2_central α (C.print α d)).2
  · have hprint_inner := C.g4_print_inner α d hmarked
    obtain ⟨_hneq, howner, hside⟩ := C.g1_partner (C.printOcc α d) hprint_inner
    intro hboundary
    rw [hpartner] at hboundary
    unfold MacroData.IsBoundary at hboundary
    have howner_print : C.owner (C.printOcc α d).1 = α := by
      change C.owner (C.central α) = α
      exact C.g5_central_owner α
    rw [howner, howner_print] at hboundary
    have hboundary_print : C.IsBoundary (C.printOcc α d) := by
      unfold MacroData.IsBoundary
      rw [howner_print]
      refine ⟨hprint_inner, ?_⟩
      have hne : C.occStart (C.printOcc α d) ≠ C.occEnd (C.printOcc α d) := by
        intro hend
        have hvertex :
            (C.Q.disk (C.form (C.printOcc α d).1)).vertex (C.printOcc α d).2 =
              (C.Q.disk (C.form (C.printOcc α d).1)).vertex
                (finRotate _ (C.printOcc α d).2) := by
          exact vadd_left_cancel (C.anchor (C.printOcc α d).1) hend
        have hindex := (C.Q.disk (C.form (C.printOcc α d).1)).vertex_injective hvertex
        exact finRotate_ne_self
          (by have := (C.Q.disk (C.form (C.printOcc α d).1)).three_le; omega)
          (C.printOcc α d).2 hindex.symm
      have hside' :
          segment ℝ (C.occStart (C.printOcc α d)) (C.occEnd (C.printOcc α d)) =
            segment ℝ (C.occStart (C.partner (C.printOcc α d)))
              (C.occEnd (C.partner (C.printOcc α d))) := by
        simpa [MacroData.occSide, MacroData.childTile, PlacedTile.side,
          PolygonalDisk.side, MacroData.occStart, MacroData.occEnd, vadd_segment] using hside.symm
      have hends :=
        ncl_seg_endpoints hne hside'
      rcases hboundary.2 with hstart | hend
      · rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          rw [← h1]
          exact hstart
        · right
          rw [← h1]
          exact hstart
      · rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · right
          rw [← h2]
          exact hend
        · left
          rw [← h2]
          exact hend
    exact (C.g2_central α (C.print α d)).2 hboundary_print

/-- A legal tile is the child of a normal identity-correct parent. -/
private theorem ncl_parent (X : StrictDecTile C hC) (hX : StrictLegal C hC X) :
    ∃ F : StrictDecTile C hC, C.owner X.typ = C.form F.typ ∧ X = strictChild C hC F X.typ ∧
      IsStrictNormal C hC F ∧ IsStrictIdentityCorrect C hC F := by
  obtain ⟨ch, h0, hch, -⟩ := hX
  subst h0
  have hN := ncl_child_normal C hC (ch (1 + 1)) (ch 1).typ (hch 1).1
  rw [← (hch 1).2] at hN
  exact ⟨ch 1, (hch 0).1, (hch 0).2, hN⟩

/-- The cells of a block tile which is the child of `F`. -/
private theorem ncl_tile_cell (K : StrictBlock C hC) (s : C.Typ) (F : StrictDecTile C hC)
    (hX : K.tileOf s = strictChild C hC F s) (i : C.Side s) (k : Fin 5) :
    K.col s i k = (strictChild C hC F s).cell i k := by
  have h2 : (⟨s, K.col s⟩ : StrictDecTile C hC) = ⟨s, (strictChild C hC F s).cell⟩ := hX
  have h3 := eq_of_heq (StrictDecTile.mk.inj h2).2
  rw [h3]

/-- A nonprint side on the path `P_j(d)` carries the parent cell `(d, j)` as third cell. -/
private theorem ncl_child_path (Q' : StrictDecTile C hC) (β : C.Q.Form) (hβ : C.form Q'.typ = β)
    (s : C.Typ) (hs : C.owner s = β) (i : C.Side s) (hnp : ¬ C.IsPrint (C.occ s i))
    (d : Fin (C.Q.disk β).n) (j : Fin 5) (hmem : C.occ s i ∈ C.path β d j) :
    (strictChild C hC Q' s).cell i 2 = ncl_cellv C hC Q' d.val j := by
  subst hβ
  rw [((strictChild_cells C hC Q' s hs i).2 hnp).2.2.2.1 d j hmem, ncl_cellv_side]

/-- A print of `d` carries the first four parent cells of `d`. -/
private theorem ncl_child_print (Q' : StrictDecTile C hC) (β : C.Q.Form) (hβ : C.form Q'.typ = β)
    (s : C.Typ) (hs : C.owner s = β) (i : C.Side s) (d : Fin (C.Q.disk β).n)
    (hp : C.IsPrintOf β d (C.occ s i)) (k : Fin 5) (hk : k ≠ 4) :
    (strictChild C hC Q' s).cell i k = ncl_cellv C hC Q' d.val k := by
  subst hβ
  rw [((strictChild_cells C hC Q' s hs i).1 d hp).1 k hk, ncl_cellv_side]

/-- In a strictly matched block the two occurrences of an inner side carry the same cells. -/
private theorem ncl_match (K : StrictBlock C hC) (hK : IsStrictProperRealization C hC K)
    (o : C.SideOcc) (ho : C.owner o.1 = K.α) (hin : C.IsInner o) (k : Fin 5) :
    K.col (C.partner o).1 (C.partner o).2 k = K.col o.1 o.2 k := by
  obtain ⟨t', j, hown, hne, hside, hcol⟩ := hK o.1 o.2 ho hin
  have e : ∀ o' : C.SideOcc, K.childSide o' = K.v +ᵥ C.occSide o' := by
    intro o'
    simp only [StrictBlock.childSide, MacroData.occSide, MacroData.childTile, PlacedTile.side,
      vadd_vadd]
  have hside' : C.occSide ⟨t', j⟩ = C.occSide o := by
    rw [e, e] at hside
    exact (vadd_left_cancel_iff K.v).1 hside
  have hp := C.g1_side_unique o ⟨t', j⟩ hin (hown.trans ho.symm) hne hside'
  rw [← hp]
  exact hcol k

/-- Every port exists ((G3): every outer list has at least five entries). -/
private theorem ncl_port_some (β : C.Q.Form) (d : Fin (C.Q.disk β).n) (k : Fin 5) :
    ∃ o, C.port β d k = some o := by
  unfold MacroData.port
  have h5 := C.g3_five_le β d
  have hr : MacroData.portRank (C.outerList β d).length k ≤ (C.outerList β d).length := by
    unfold MacroData.portRank
    have : (k.val + 1) * (C.outerList β d).length ≤ 5 * (C.outerList β d).length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  exact ⟨_, List.getElem?_eq_getElem (by omega)⟩

/-- The reconstructed cell `(d, k)` is the third cell of the port `k` of `d`. -/
private theorem ncl_recon_port (K : StrictBlock C hC) (t : C.Typ) (β : C.Q.Form)
    (hβ : C.form t = β) (d : Fin (C.Q.disk β).n) (k : Fin 5) (o : C.SideOcc)
    (ho : C.port β d k = some o) :
    ncl_cellv C hC (strictReconstruct C hC K t) d.val k = K.col o.1 o.2 2 := by
  subst hβ
  rw [ncl_cellv_side C hC (strictReconstruct C hC K t) d]
  simp [strictReconstruct, ho]

/-- A list whose first and last entries differ has at least two entries. -/
private theorem ncl_two_le {γ : Type*} (l : List γ) {a b : γ} (ha : l.head? = some a)
    (hb : l.getLast? = some b) (hab : a ≠ b) : 2 ≤ l.length := by
  match l, ha, hb with
  | [x], ha, hb =>
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at ha hb
    exact absurd (ha.symm.trans hb) hab
  | _ :: _ :: _, _, _ => simp

/-- The parent of a block tile with an outer side has the type of the common header. -/
private theorem ncl_header_typ (K : StrictBlock C hC) (h : HeaderKernel.Header C.Typ C.Side)
    (hh : StrictCommonHeader C hC K h) (s : C.Typ) (hs : C.owner s = K.α) (i0 : C.Side s)
    (hout : C.IsOuter (C.occ s i0)) (F : StrictDecTile C hC) (hown : C.owner s = C.form F.typ)
    (hX : K.tileOf s = strictChild C hC F s) : F.typ = h.1 := by
  obtain ⟨j, hj⟩ := exists_boundary_side_of_outer C s i0 hout
  have hnp : ¬ C.IsPrint (C.occ s j) := fun hp => ncl_print_not_boundary C _ hp hj
  have e1 := hh.2 s j hs hj
  rw [ncl_tile_cell C hC K s F hX, ((strictChild_cells C hC F s hown j).2 hnp).2.2.2.2.2.2.1 hj]
    at e1
  simp only [headerSU] at e1
  injection e1 with e2
  rw [← e2]
  rfl

/-- Along a genuine path of a strictly matched block whose noncentral tiles are legal, the third
cell of the port equals the cell of the central print. -/
private theorem ncl_path_signal (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (d : Fin (C.Q.disk K.α).n) (k : Fin 5) (hg : C.IsGenuinePath K.α d k)
    (o : C.SideOcc) (ho : C.port K.α d k = some o) :
    K.col o.1 o.2 2 = K.col (C.central K.α) (C.print K.α d) k := by
  have hco := C.g5_central_owner K.α
  have hk4 : k ≠ 4 := by
    intro h4
    subst h4
    exact absurd hg.2 (by decide)
  have hpin : C.IsInner (C.printOcc K.α d) := C.g4_print_inner K.α d hg.1
  obtain ⟨hpne, hpown, -⟩ := C.g1_partner _ hpin
  have hpown' : C.owner (C.partner (C.printOcc K.α d)).1 = K.α := hpown.trans hco
  have hlegal : ∀ s, C.owner s = K.α → s ≠ C.central K.α → ∃ F : StrictDecTile C hC,
      C.owner s = C.form F.typ ∧ K.tileOf s = strictChild C hC F s := by
    intro s hs hne
    obtain ⟨F, h1, h2, -⟩ := ncl_parent C hC _ (hK.2 s hs hne)
    exact ⟨F, h1, h2⟩
  have htile : ∀ o' ∈ C.path K.α d k, ¬ C.IsPrint o' → ∀ F : StrictDecTile C hC,
      C.owner o'.1 = C.form F.typ → K.tileOf o'.1 = strictChild C hC F o'.1 →
      K.col o'.1 o'.2 2 = ncl_cellv C hC F d.val k := by
    intro o' hmem hnp F hown hX
    have hown' := C.g4_path_owner _ _ _ o' hmem
    rw [ncl_tile_cell C hC K o'.1 F hX]
    exact ncl_child_path C hC F K.α (hown.symm.trans hown') o'.1 hown' o'.2 hnp d k hmem
  have hprint : ∀ o' ∈ C.path K.α d k, C.IsPrint o' → o' = C.partner (C.printOcc K.α d) := by
    intro o' hmem hp
    obtain ⟨d', hd'⟩ := (ncl_isPrint_iff C (C.g4_path_owner _ _ _ o' hmem) o'.2).1 hp
    rcases hd' with ⟨hm', h1 | h1⟩
    · exact absurd (congrArg Sigma.fst h1) (C.g4_path_not_central _ _ _ hg o' hmem)
    · by_cases hdd : d = d'
      · subst hdd
        exact h1
      · have hg' : C.IsGenuinePath K.α d' 0 := ⟨hm', by decide⟩
        have hmem' : o' ∈ C.path K.α d' 0 := by
          show C.occ o'.1 o'.2 ∈ _
          rw [h1]
          exact List.mem_of_getLast? (C.g4_path_last _ _ _ hg')
        exact absurd (C.g4_path_disjoint _ _ _ _ _ (fun e => hdd (Prod.mk.inj e).1) o' hmem
          hmem').1 hdd
  have hhead : (C.path K.α d k).head? = some o := (C.g4_path_head _ _ _ hg).trans ho
  have hlast : (C.path K.α d k).getLast? = some (C.partner (C.printOcc K.α d)) :=
    C.g4_path_last _ _ _ hg
  have hnd := C.g4_path_nodup K.α d k
  have hoout : C.IsOuter o := ((C.g3_outerList_mem _ _ _).1 (List.mem_of_getElem? ho)).2.1
  have hlen : 2 ≤ (C.path K.α d k).length :=
    ncl_two_le _ hhead hlast (fun e => isInner_partner C hpin (e ▸ hoout))
  have hlast' : (C.path K.α d k)[(C.path K.α d k).length - 1]? =
      some (C.partner (C.printOcc K.α d)) := by
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  have hnp : ∀ n o', n + 1 < (C.path K.α d k).length → (C.path K.α d k)[n]? = some o' →
      ¬ C.IsPrint o' := by
    intro n o' hn h1 hp
    have h2 := hprint o' (List.mem_of_getElem? h1) hp
    rw [h2] at h1
    obtain ⟨hb1, e1⟩ := List.getElem?_eq_some_iff.1 h1
    obtain ⟨hb2, e2⟩ := List.getElem?_eq_some_iff.1 hlast'
    have := (List.Nodup.getElem_inj_iff hnd).1 (e1.trans e2.symm)
    omega
  obtain ⟨open', hpen⟩ : ∃ o', (C.path K.α d k)[(C.path K.α d k).length - 2]? = some o' :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hchain : ∀ m n o1, n + m = (C.path K.α d k).length - 2 → (C.path K.α d k)[n]? = some o1 →
      K.col o1.1 o1.2 2 = K.col open'.1 open'.2 2 := by
    intro m
    induction m with
    | zero =>
      intro n o1 hn h1
      rw [add_zero] at hn
      subst hn
      rw [hpen] at h1
      cases h1
      rfl
    | succ m ih =>
      intro n o1 hn h1
      obtain ⟨o2, h2⟩ : ∃ o2, (C.path K.α d k)[n + 1]? = some o2 :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [← ih (n + 1) o2 (by omega) h2]
      have hm1 := List.mem_of_getElem? h1
      have hm2 := List.mem_of_getElem? h2
      have hnp1 := hnp n o1 (by omega) h1
      have hnp2 := hnp (n + 1) o2 (by omega) h2
      have hown1 := C.g4_path_owner _ _ _ o1 hm1
      rcases C.g4_path_chain _ _ _ n o1 o2 h1 h2 with heq | ⟨hin, hpart⟩
      · obtain ⟨F, hFo, hX⟩ := hlegal o1.1 hown1 (C.g4_path_not_central _ _ _ hg o1 hm1)
        rw [htile o1 hm1 hnp1 F hFo hX]
        rw [heq] at hFo hX
        rw [htile o2 hm2 hnp2 F hFo hX]
      · rw [hpart]
        exact (ncl_match C hC K hK.1 o1 hown1 hin 2).symm
  have hhead' : (C.path K.α d k)[0]? = some o := by
    rw [← List.head?_eq_getElem?]
    exact hhead
  rw [hchain ((C.path K.α d k).length - 2) 0 o (by omega) hhead']
  obtain ⟨hS, hord⟩ := C.g4_path_penultimate _ _ _ hg open' hpen
  have hmpen := List.mem_of_getElem? hpen
  obtain ⟨F, hFo, hX⟩ := hlegal _ hpown' (fun e => hpne (by rw [e]; rfl))
  have e1 : K.col open'.1 open'.2 2 = ncl_cellv C hC F d.val k := by
    apply htile open' hmpen hord.2 F
    · rw [hS]; exact hFo
    · rw [hS]; exact hX
  have e2 : K.col (C.partner (C.printOcc K.α d)).1 (C.partner (C.printOcc K.α d)).2 k =
      ncl_cellv C hC F d.val k := by
    rw [ncl_tile_cell C hC K _ F hX]
    exact ncl_child_print C hC F K.α (hFo.symm.trans hpown') _ hpown' _ d ⟨hg.1, Or.inr rfl⟩ k hk4
  rw [e1, ← e2]
  exact ncl_match C hC K hK.1 (C.printOcc K.α d) hco hpin k

/-- Each reconstructed cell is the corresponding cell of a normal identity-correct tile of the
header type. -/
private theorem ncl_recon_cell (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h)
    (i : C.Side h.1) (k : Fin 5) :
    ∃ c : C.Side h.1 → Fin 5 → SU C hC, IsStrictNormal C hC ⟨h.1, c⟩ ∧
      IsStrictIdentityCorrect C hC ⟨h.1, c⟩ ∧ (strictReconstruct C hC K h.1).cell i k = c i k := by
  have htf : C.form h.1 = K.α := hh.1
  obtain ⟨o, ho⟩ := ncl_port_some C K.α (Fin.cast (congrArg (fun u => (C.Q.disk u).n) htf) i) k
  have hrec := ncl_recon_port C hC K h.1 K.α htf _ k o ho
  obtain ⟨hown, hout, -⟩ := (C.g3_outerList_mem _ _ _).1 (List.mem_of_getElem? ho)
  have hnc : o.1 ≠ C.central K.α := by
    obtain ⟨s, j⟩ := o
    rintro rfl
    exact (C.g2_central K.α j).1 hout
  have hmemP : o ∈ C.path K.α (Fin.cast (congrArg (fun u => (C.Q.disk u).n) htf) i) k := by
    by_cases hg : C.IsGenuinePath K.α (Fin.cast (congrArg (fun u => (C.Q.disk u).n) htf) i) k
    · exact List.mem_of_mem_head? ((C.g4_path_head _ _ _ hg).trans ho)
    · rw [C.g4_path_trivial _ _ _ hg, ho]
      simp
  have hnp : ¬ C.IsPrint o := fun ⟨_, hp⟩ => isInner_of_isPrintOf C hp hout
  obtain ⟨F, hFown, hX, hFN, hFI⟩ := ncl_parent C hC _ (hK.2 o.1 hown hnc)
  have hFt : F.typ = h.1 := ncl_header_typ C hC K h hh o.1 hown o.2 hout F hFown hX
  have hval : K.col o.1 o.2 2 =
      ncl_cellv C hC F (Fin.cast (congrArg (fun u => (C.Q.disk u).n) htf) i).val k := by
    rw [ncl_tile_cell C hC K o.1 F hX]
    exact ncl_child_path C hC F K.α (hFown.symm.trans hown) o.1 hown o.2 hnp _ k hmemP
  obtain ⟨tF, cF⟩ := F
  simp only at hFt
  subst hFt
  refine ⟨cF, hFN, hFI, ?_⟩
  exact (ncl_cellv_side C hC (strictReconstruct C hC K h.1) i k).symm.trans
    ((hrec.trans hval).trans (ncl_cellv_side C hC ⟨h.1, cF⟩ i k))

/-- The reconstructed parent is strictly normal and identity-correct. -/
private theorem ncl_recon_normal (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h) :
    IsStrictNormal C hC (strictReconstruct C hC K h.1) ∧
      IsStrictIdentityCorrect C hC (strictReconstruct C hC K h.1) := by
  refine ⟨fun i k hloc => ?_, fun i => ⟨fun hin hnp => ?_, fun hp => ?_⟩⟩
  · obtain ⟨c, hN, -, he⟩ := ncl_recon_cell C hC K hK h hh i k
    rw [he]
    exact hN i k hloc
  · obtain ⟨c, -, hI, he⟩ := ncl_recon_cell C hC K hK h hh i 0
    rw [he]
    exact (hI i).1 hin hnp
  · obtain ⟨c, -, hI, he⟩ := ncl_recon_cell C hC K hK h hh i 4
    rw [he]
    exact (hI i).2 hp

/-- `lem:comp/noncentral-legal` (strict variant): if the centre is legal and the type of `D` is
noncentral, then `D` is legal. -/
theorem strict_reconstructed_noncentral_legal (K : StrictBlock C hC)
    (hK : StrictBlockContext C hC K) (h : HeaderKernel.Header C.Typ C.Side)
    (hh : StrictCommonHeader C hC K h) (hA : StrictLegal C hC K.centre)
    (hnc : ¬ C.IsCentral h.1) : StrictLegal C hC (strictReconstruct C hC K h.1) := by
  obtain ⟨ch, h0, hch, hleg⟩ := hA
  have hco : C.owner (C.central K.α) = K.α := C.g5_central_owner K.α
  have h0typ : (ch 0).typ = C.central K.α := by rw [h0]; rfl
  have hEf : C.form (ch 1).typ = K.α := by rw [← (hch 0).1, h0typ, hco]
  have htf : C.form h.1 = K.α := hh.1
  have hnl : C.kind K.α ≠ .large := by
    intro hl
    apply hnc
    rw [← htf] at hl
    exact ((C.g5_large_iff _).1 hl).symm
  have hEc : ¬ C.IsCentral (ch 1).typ := by
    intro hc
    apply hnl
    rw [← hEf]
    exact (C.g5_large_iff _).2 hc.symm
  have hEleg : StrictLegal C hC (ch 1) :=
    ⟨fun n => ch (1 + n), rfl, fun n => hch (1 + n), fun n i k hne hno =>
      hleg (1 + n) i k hne (fun ho => hno (ncl_origin_shift C (fun l => typeShadow C hC (ch l)) 1 _ i k
        ho n rfl))⟩
  have hEN := ncl_child_normal C hC (ch (1 + 1)) (ch 1).typ (hch 1).1
  rw [← (hch 1).2] at hEN
  have hD := ncl_recon_normal C hC K hK h hh
  have hEc' : K.centre = strictChild C hC (ch 1) (C.central K.α) := by
    have := (hch 0).2
    rw [h0] at this
    exact this
  have hcell : ∀ d : C.Side (ch 1).typ, C.marked (C.form (ch 1).typ) d → ∀ k : Fin 5, k ≠ 4 →
      ncl_cellv C hC (strictReconstruct C hC K h.1) d.val k = (ch 1).cell d k := by
    intro d hd k hk
    have hd' := (ncl_marked_cast_iff C hEf d).2 hd
    have hk' : k.val < 4 := by
      have := k.isLt
      have : k.val ≠ 4 := fun e => hk (Fin.ext e)
      omega
    obtain ⟨o, ho⟩ := ncl_port_some C K.α (Fin.cast (congrArg (fun u => (C.Q.disk u).n) hEf) d) k
    have e1 := ncl_child_copy C hC (ch 1) K.α hEf _ hd' k hk
    rw [← hEc'] at e1
    calc ncl_cellv C hC (strictReconstruct C hC K h.1) d.val k = K.col o.1 o.2 2 :=
          ncl_recon_port C hC K h.1 K.α htf _ k o ho
      _ = K.col (C.central K.α) (C.print K.α _) k := ncl_path_signal C hC K hK _ k ⟨hd', hk'⟩ o ho
      _ = ncl_cellv C hC (ch 1) d.val k := (ncl_cellv_side C hC K.centre _ k).symm.trans e1
      _ = (ch 1).cell d k := ncl_cellv_side C hC (ch 1) d k
  have hDE := ncl_ident C hC (ch 1) (strictReconstruct C hC K h.1) hEc hnc (htf.trans hEf.symm)
    hEN.1 hEN.2 hD.1 hD.2 hcell
  rw [hDE]
  exact hEleg

/-! ### Geometric and combinatorial helpers for `strict_opposing_macroside` -/

/-- Pushing a point of a ball slightly along a vector stays in the ball. -/
private theorem som_push (x z nv : Pt) (ε δ : ℝ) (hz : dist z x < ε) (hδ : 0 < δ) (hn : nv ≠ 0)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    ∃ t : ℝ, 0 < t ∧ dist (z + (σ * t) • nv) z < δ ∧ dist (z + (σ * t) • nv) x < ε ∧
      inner ℝ (z + (σ * t) • nv - x) nv = inner ℝ (z - x) nv + σ * t * ‖nv‖ ^ 2 := by
  have hnp : 0 < ‖nv‖ := norm_pos_iff.mpr hn
  set r := min δ (ε - dist z x) with hr
  have hr0 : 0 < r := lt_min hδ (by linarith)
  have hq : 0 < r / (2 * ‖nv‖) := by positivity
  have h1 : dist (z + (σ * (r / (2 * ‖nv‖))) • nv) z = r / 2 := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_mul]
    rcases hσ with rfl | rfl <;> simp [abs_of_pos hq] <;> field_simp
  refine ⟨r / (2 * ‖nv‖), hq, ?_, ?_, ?_⟩
  · rw [h1]; linarith [min_le_left δ (ε - dist z x)]
  · have := dist_triangle (z + (σ * (r / (2 * ‖nv‖))) • nv) z x
    linarith [min_le_right δ (ε - dist z x)]
  · rw [add_sub_right_comm, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp

private theorem som_segment_compact (a b : Pt) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

private theorem som_openSegment_ne_left {a b x : Pt} (hab : a ≠ b) (hx : x ∈ openSegment ℝ a b) :
    x ≠ a := by
  rintro rfl
  exact hab ((left_mem_openSegment_iff).1 hx)

private theorem som_openSegment_ne_right {a b x : Pt} (hab : a ≠ b) (hx : x ∈ openSegment ℝ a b) :
    x ≠ b := by
  rintro rfl
  exact hab ((right_mem_openSegment_iff).1 hx)

private theorem som_finRotate_ne {N : ℕ} (hN : 2 ≤ N) (x : Fin N) : finRotate N x ≠ x := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have := congrArg (· - x) h
  simp at this

private theorem som_vertex_ne (D : PolygonalDisk) (i : Fin D.n) :
    D.vertex i ≠ D.vertex (finRotate _ i) := fun h =>
  som_finRotate_ne (by have := D.three_le; omega) i (D.vertex_injective h).symm

/-- Points of a segment differ by multiples of its direction. -/
private theorem som_inner_segment {a b x z nv : Pt} (hn : inner ℝ (b - a) nv = 0)
    (hx : x ∈ segment ℝ a b) (hz : z ∈ segment ℝ a b) : inner ℝ (z - x) nv = 0 := by
  rw [segment_eq_image'] at hx hz
  obtain ⟨t, -, rfl⟩ := hx
  obtain ⟨t', -, rfl⟩ := hz
  have : a + t' • (b - a) - (a + t • (b - a)) = (t' - t) • (b - a) := by module
  rw [this, inner_smul_left, hn]; simp

/-- Near a relative interior point of a side, the frontier of a polygonal disk lies on the
line of that side. -/
private theorem som_frontier_local (D : PolygonalDisk) (i : Fin D.n) {x nv : Pt}
    (hx : x ∈ openSegment ℝ (D.vertex i) (D.vertex (finRotate _ i)))
    (hn : inner ℝ (D.vertex (finRotate _ i) - D.vertex i) nv = 0) :
    ∃ ε > 0, ∀ z, dist z x < ε → z ∈ frontier D.carrier → inner ℝ (z - x) nv = 0 := by
  have hab := som_vertex_ne D i
  have hxa := som_openSegment_ne_left hab hx
  have hxb := som_openSegment_ne_right hab hx
  have hxs : x ∈ D.side i := openSegment_subset_segment _ _ _ hx
  have hev : ∀ᶠ z in nhds x, ∀ j : Fin D.n, j ≠ i → z ∉ D.side j := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = i
    · exact Filter.Eventually.of_forall fun _ h => absurd hj h
    · have hxj : x ∉ D.side j := by
        intro hxj
        have := D.simple i j (Ne.symm hj) ⟨hxs, hxj⟩
        rcases this.1 with h | h
        · exact hxa h
        · exact hxb h
      filter_upwards [(som_segment_compact _ _).isClosed.isOpen_compl.mem_nhds hxj] with z hz _
      exact hz
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, fun z hz hzf => ?_⟩
  rw [D.frontier_eq, Set.mem_iUnion] at hzf
  obtain ⟨j, hj⟩ := hzf
  by_cases hji : j = i
  · subst hji
    exact som_inner_segment hn hxs hj
  · exact absurd hj (hball hz j hji)

/-- **Half-ball lemma.**  Near a relative interior point `x` of a side of a polygonal disk, one
open half-ball (with respect to a normal vector `nv` of the side) lies in the interior and the
other one outside the disk. -/
private theorem som_half_ball (D : PolygonalDisk) (i : Fin D.n) {x nv : Pt}
    (hx : x ∈ openSegment ℝ (D.vertex i) (D.vertex (finRotate _ i)))
    (hn : inner ℝ (D.vertex (finRotate _ i) - D.vertex i) nv = 0) (hn0 : nv ≠ 0) :
    ∃ ε > 0, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z, dist z x < ε →
      (0 < σ * inner ℝ (z - x) nv → z ∈ interior D.carrier) ∧
      (σ * inner ℝ (z - x) nv < 0 → z ∉ D.carrier) := by
  obtain ⟨ε, hε, hloc⟩ := som_frontier_local D i hx hn
  have hcl : IsClosed D.carrier := D.compact.isClosed
  have hxs : x ∈ D.side i := openSegment_subset_segment _ _ _ hx
  have hxf : x ∈ frontier D.carrier := by
    rw [D.frontier_eq, Set.mem_iUnion]; exact ⟨i, hxs⟩
  let H : ℝ → Set Pt := fun σ => {z | dist z x < ε ∧ 0 < σ * inner ℝ (z - x) nv}
  have hH : ∀ σ, H σ ⊆ interior D.carrier ∨ H σ ⊆ D.carrierᶜ := by
    intro σ
    have hconv : Convex ℝ (H σ) := by
      intro a ha b hb s t hs ht hst
      refine ⟨?_, ?_⟩
      · have := (convex_ball x ε) (show a ∈ Metric.ball x ε from ha.1)
          (show b ∈ Metric.ball x ε from hb.1) hs ht hst
        exact this
      · have he : s • a + t • b - x = s • (a - x) + t • (b - x) := by
          calc s • a + t • b - x = s • a + t • b - (s + t) • x := by rw [hst, one_smul]
            _ = s • (a - x) + t • (b - x) := by module
        show 0 < σ * inner ℝ (s • a + t • b - x) nv
        rw [he, inner_add_left, inner_smul_left, inner_smul_left]
        simp only [RCLike.conj_to_real]
        have h1 : 0 < σ * inner ℝ (a - x) nv := ha.2
        have h2 : 0 < σ * inner ℝ (b - x) nv := hb.2
        have hre : σ * (s * inner ℝ (a - x) nv + t * inner ℝ (b - x) nv) =
            s * (σ * inner ℝ (a - x) nv) + t * (σ * inner ℝ (b - x) nv) := by ring
        rw [hre]
        rcases hs.lt_or_eq with hs' | hs'
        · nlinarith [mul_nonneg ht h2.le, mul_pos hs' h1]
        · subst hs'
          have : t = 1 := by linarith
          subst this; simpa using h2
    have hopen : IsOpen (H σ) := by
      apply IsOpen.inter
      · exact Metric.isOpen_ball
      · have hc : Continuous fun z : Pt => σ * inner ℝ (z - x) nv :=
          continuous_const.mul ((continuous_id.sub continuous_const).inner continuous_const)
        exact isOpen_lt continuous_const hc
    refine hconv.isPreconnected.subset_or_subset isOpen_interior hcl.isOpen_compl
      (Set.disjoint_compl_right_iff_subset.2 interior_subset) ?_
    intro z hz
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hcon
    have hzf : z ∈ frontier D.carrier := ⟨subset_closure hcon.2, hcon.1⟩
    have := hloc z hz.1 hzf
    have h2 := hz.2
    rw [this, mul_zero] at h2
    exact lt_irrefl _ h2
  have hpush : ∀ z, dist z x < ε → inner ℝ (z - x) nv = 0 → ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      ∀ δ > 0, ∃ y ∈ H σ, dist y z < δ := by
    intro z hz h0 σ hσ δ hδ
    obtain ⟨t, ht, hd, hdx, hi⟩ := som_push x z nv ε δ hz hδ hn0 σ hσ
    refine ⟨_, ⟨hdx, ?_⟩, hd⟩
    rw [hi, h0]
    have hnp : 0 < ‖nv‖ := norm_pos_iff.mpr hn0
    rcases hσ with rfl | rfl <;> nlinarith [sq_pos_of_pos hnp]
  have hsign : ∀ z, dist z x < ε → inner ℝ (z - x) nv ≠ 0 → z ∈ H 1 ∨ z ∈ H (-1) := by
    intro z hz h0
    rcases lt_or_gt_of_ne h0 with h | h
    · right; exact ⟨hz, by linarith⟩
    · left; exact ⟨hz, by linarith⟩
  rcases hH 1 with h1 | h1 <;> rcases hH (-1) with h2 | h2
  · exfalso
    have hball : Metric.ball x ε ⊆ D.carrier := by
      intro z hz
      by_cases h0 : inner ℝ (z - x) nv = 0
      · rw [← D.regular_closed, Metric.mem_closure_iff]
        intro δ hδ
        obtain ⟨y, hy, hyd⟩ := hpush z hz h0 1 (Or.inl rfl) δ hδ
        exact ⟨y, h1 hy, by rw [dist_comm]; exact hyd⟩
      · rcases hsign z hz h0 with h | h
        · exact interior_subset (h1 h)
        · exact interior_subset (h2 h)
    exact hxf.2 (interior_maximal hball Metric.isOpen_ball (Metric.mem_ball_self hε))
  · refine ⟨ε, hε, 1, Or.inl rfl, fun z hz => ⟨fun h => h1 ⟨hz, h⟩, fun h => h2 ⟨hz, by linarith⟩⟩⟩
  · refine ⟨ε, hε, -1, Or.inr rfl, fun z hz => ⟨fun h => h2 ⟨hz, h⟩, fun h => h1 ⟨hz, by linarith⟩⟩⟩
  · exfalso
    have hxc : x ∈ D.carrier := hcl.closure_eq ▸ frontier_subset_closure hxf
    rw [← D.regular_closed, Metric.mem_closure_iff] at hxc
    obtain ⟨w, hw, hwd⟩ := hxc ε hε
    rw [dist_comm] at hwd
    by_cases h0 : inner ℝ (w - x) nv = 0
    · obtain ⟨ρ, hρ, hρs⟩ := Metric.isOpen_iff.1 isOpen_interior w hw
      obtain ⟨y, hy, hyd⟩ := hpush w hwd h0 1 (Or.inl rfl) ρ hρ
      exact h1 hy (interior_subset (hρs hyd))
    · rcases hsign w hwd h0 with h | h
      · exact h1 h (interior_subset hw)
      · exact h2 h (interior_subset hw)

/-- The affine map `z ↦ w + θ • z` as a homeomorphism. -/
private def som_homeo (θ : ℝ) (hθ : θ ≠ 0) (w : Pt) : Pt ≃ₜ Pt :=
  (Homeomorph.smulOfNeZero θ hθ).trans (Homeomorph.addLeft w)

private theorem som_homeo_apply (θ : ℝ) (hθ : θ ≠ 0) (w z : Pt) :
    som_homeo θ hθ w z = w + θ • z := rfl

private theorem som_homeo_image (θ : ℝ) (hθ : θ ≠ 0) (w : Pt) (s : Set Pt) :
    som_homeo θ hθ w '' s = w +ᵥ θ • s := by
  ext z
  simp only [Set.mem_image, som_homeo_apply, Set.mem_vadd_set, Set.mem_smul_set, vadd_eq_add]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨θ • y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩

private theorem som_homeo_segment (θ : ℝ) (hθ : θ ≠ 0) (w a b : Pt) :
    som_homeo θ hθ w '' segment ℝ a b = segment ℝ (w + θ • a) (w + θ • b) := by
  rw [segment_eq_image', segment_eq_image', Set.image_image]
  refine Set.image_congr fun t _ => ?_
  rw [som_homeo_apply]; module

/-- The image of a polygonal disk under `z ↦ w + θ • z`, `θ ≠ 0`. -/
private def som_affDisk (D : PolygonalDisk) (θ : ℝ) (hθ : θ ≠ 0) (w : Pt) : PolygonalDisk where
  carrier := w +ᵥ θ • D.carrier
  n := D.n
  three_le := D.three_le
  vertex k := w + θ • D.vertex k
  vertex_injective k l h := D.vertex_injective (smul_right_injective Pt hθ (add_left_cancel h))
  compact := by
    rw [← som_homeo_image θ hθ w]; exact D.compact.image (som_homeo θ hθ w).continuous
  interior_nonempty := by
    rw [← som_homeo_image θ hθ w, ← Homeomorph.image_interior]
    exact D.interior_nonempty.image _
  regular_closed := by
    rw [← som_homeo_image θ hθ w, ← Homeomorph.image_interior, ← Homeomorph.image_closure,
      D.regular_closed]
  interior_pathConnected := by
    rw [← som_homeo_image θ hθ w, ← Homeomorph.image_interior]
    exact D.interior_pathConnected.image (som_homeo θ hθ w).continuous
  frontier_eq := by
    rw [← som_homeo_image θ hθ w, ← Homeomorph.image_frontier, D.frontier_eq, Set.image_iUnion]
    simp only [som_homeo_segment]
  simple i j hij := by
    have := Set.image_mono (f := som_homeo θ hθ w) (D.simple i j hij)
    rw [Set.image_inter (som_homeo θ hθ w).injective, Set.image_inter (som_homeo θ hθ w).injective,
      som_homeo_segment, som_homeo_segment] at this
    simpa [Set.image_insert_eq, som_homeo_apply] using this

private theorem som_affDisk_side (D : PolygonalDisk) (θ : ℝ) (hθ : θ ≠ 0) (w : Pt) (i : Fin D.n) :
    (som_affDisk D θ hθ w).side i = w +ᵥ θ • D.side i := by
  rw [← som_homeo_image θ hθ w, PolygonalDisk.side, PolygonalDisk.side, som_homeo_segment]
  rfl

private theorem som_exists_normal (v : Pt) (hv : v ≠ 0) : ∃ nv : Pt, nv ≠ 0 ∧ inner ℝ v nv = 0 := by
  refine ⟨!₂[-(v 1), v 0], ?_, ?_⟩
  · intro h
    apply hv
    have h0 := congrFun (congrArg (fun w : Pt => (w : Fin 2 → ℝ)) h) 0
    have h1 := congrFun (congrArg (fun w : Pt => (w : Fin 2 → ℝ)) h) 1
    simp at h0 h1
    ext i; fin_cases i <;> simp [h0, h1]
  · simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

/-- The midpoint of a nondegenerate subsegment is a relative interior point, and normals of
the subsegment are normals of the segment. -/
private theorem som_sub_segment {a b p q : Pt} (hpq : p ≠ q) (hs : segment ℝ p q ⊆ segment ℝ a b) :
    midpoint ℝ p q ∈ openSegment ℝ a b ∧
      ∀ nv, inner ℝ (q - p) nv = 0 → inner ℝ (b - a) nv = 0 := by
  have hp := hs (left_mem_segment ℝ p q)
  have hq := hs (right_mem_segment ℝ p q)
  rw [segment_eq_image'] at hp hq
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hp
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hq
  have hst : s ≠ t := by rintro rfl; exact hpq rfl
  have hba : b - a ≠ 0 := by
    intro h; apply hpq; rw [h]; simp
  have hdiff : a + t • (b - a) - (a + s • (b - a)) = (t - s) • (b - a) := by module
  have hmid : midpoint ℝ (a + s • (b - a)) (a + t • (b - a)) = a + ((s + t) / 2) • (b - a) := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]; module
  refine ⟨?_, fun nv hn => ?_⟩
  · rw [hmid, openSegment_eq_image']
    refine ⟨(s + t) / 2, ⟨?_, ?_⟩, rfl⟩
    · rcases lt_or_gt_of_ne hst with h | h <;> linarith
    · rcases lt_or_gt_of_ne hst with h | h <;> linarith
  · rw [hdiff, inner_smul_left] at hn
    simp only [RCLike.conj_to_real, mul_eq_zero] at hn
    rcases hn with h | h
    · exact absurd (sub_eq_zero.1 h).symm hst
    · exact h

/-- The half-ball lemma at the midpoint of a nondegenerate segment contained in a side. -/
private theorem som_half_ball_seg (D : PolygonalDisk) (i : Fin D.n) {p q nv : Pt} (hpq : p ≠ q)
    (hs : segment ℝ p q ⊆ D.side i) (hn : inner ℝ (q - p) nv = 0) (hn0 : nv ≠ 0) :
    ∃ ε > 0, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ z, dist z (midpoint ℝ p q) < ε →
      (0 < σ * inner ℝ (z - midpoint ℝ p q) nv → z ∈ interior D.carrier) ∧
      (σ * inner ℝ (z - midpoint ℝ p q) nv < 0 → z ∉ D.carrier) := by
  obtain ⟨hx, hnn⟩ := som_sub_segment hpq hs
  exact som_half_ball D i hx (hnn nv hn) hn0

/-- Two polygonal disks with disjoint interiors sharing a nondegenerate segment on their sides
fill a neighbourhood of its midpoint off the line: any closed set containing both carriers is a
neighbourhood of the midpoint. -/
private theorem som_two_cover (D₁ D₂ : PolygonalDisk) (i₁ : Fin D₁.n) (i₂ : Fin D₂.n) {p q : Pt}
    (hpq : p ≠ q) (h₁ : segment ℝ p q ⊆ D₁.side i₁) (h₂ : segment ℝ p q ⊆ D₂.side i₂)
    (hdis : Disjoint (interior D₁.carrier) (interior D₂.carrier)) {R : Set Pt} (hR : IsClosed R)
    (hR₁ : D₁.carrier ⊆ R) (hR₂ : D₂.carrier ⊆ R) : midpoint ℝ p q ∈ interior R := by
  obtain ⟨nv, hn0, hn⟩ := som_exists_normal (q - p) (sub_ne_zero.2 hpq.symm)
  set x := midpoint ℝ p q
  obtain ⟨ε₁, hε₁, σ₁, hσ₁, hb₁⟩ := som_half_ball_seg D₁ i₁ hpq h₁ hn hn0
  obtain ⟨ε₂, hε₂, σ₂, hσ₂, hb₂⟩ := som_half_ball_seg D₂ i₂ hpq h₂ hn hn0
  set ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hnp : 0 < ‖nv‖ := norm_pos_iff.mpr hn0
  have hopp : σ₂ = -σ₁ := by
    by_contra hne
    have heq : σ₂ = σ₁ := by
      rcases hσ₁ with rfl | rfl <;> rcases hσ₂ with rfl | rfl <;>
        first | rfl | (exfalso; apply hne; norm_num)
    obtain ⟨t, ht, -, hdx, hi⟩ := som_push x x nv ε 1 (by simp [hε]) one_pos hn0 σ₁ hσ₁
    have hpos : 0 < σ₁ * inner ℝ (x + (σ₁ * t) • nv - x) nv := by
      rw [hi, sub_self, inner_zero_left]
      rcases hσ₁ with rfl | rfl <;> nlinarith [sq_pos_of_pos hnp]
    have hz₁ := (hb₁ _ (lt_of_lt_of_le hdx (min_le_left _ _))).1 hpos
    have hz₂ := (hb₂ _ (lt_of_lt_of_le hdx (min_le_right _ _))).1 (by rw [heq]; exact hpos)
    exact Set.disjoint_left.1 hdis hz₁ hz₂
  have hoff : ∀ z, dist z x < ε → inner ℝ (z - x) nv ≠ 0 → z ∈ R := by
    intro z hz h0
    have hz₁ := hb₁ z (lt_of_lt_of_le hz (min_le_left _ _))
    have hz₂ := hb₂ z (lt_of_lt_of_le hz (min_le_right _ _))
    rw [hopp] at hz₂
    rcases lt_or_gt_of_ne h0 with h | h
    · rcases hσ₁ with rfl | rfl
      · exact hR₂ (interior_subset (hz₂.1 (by linarith)))
      · exact hR₁ (interior_subset (hz₁.1 (by linarith)))
    · rcases hσ₁ with rfl | rfl
      · exact hR₁ (interior_subset (hz₁.1 (by linarith)))
      · exact hR₂ (interior_subset (hz₂.1 (by linarith)))
  have hball : Metric.ball x ε ⊆ R := by
    intro z hz
    by_cases h0 : inner ℝ (z - x) nv = 0
    · rw [← hR.closure_eq, Metric.mem_closure_iff]
      intro δ hδ
      obtain ⟨t, ht, hd, hdx, hi⟩ := som_push x z nv ε δ hz hδ hn0 1 (Or.inl rfl)
      refine ⟨_, hoff _ hdx ?_, by rw [dist_comm]; exact hd⟩
      rw [hi, h0]; positivity
    · exact hoff z hz h0
  exact interior_maximal hball Metric.isOpen_ball (Metric.mem_ball_self hε)

/-- Three polygonal disks sharing a nondegenerate segment on their sides: two of them have
intersecting interiors. -/
private theorem som_three (D₁ D₂ D₃ : PolygonalDisk) (i₁ : Fin D₁.n) (i₂ : Fin D₂.n) (i₃ : Fin D₃.n)
    {p q : Pt} (hpq : p ≠ q) (h₁ : segment ℝ p q ⊆ D₁.side i₁) (h₂ : segment ℝ p q ⊆ D₂.side i₂)
    (h₃ : segment ℝ p q ⊆ D₃.side i₃) :
    (interior D₁.carrier ∩ interior D₂.carrier).Nonempty ∨
      (interior D₁.carrier ∩ interior D₃.carrier).Nonempty ∨
      (interior D₂.carrier ∩ interior D₃.carrier).Nonempty := by
  obtain ⟨nv, hn0, hn⟩ := som_exists_normal (q - p) (sub_ne_zero.2 hpq.symm)
  set x := midpoint ℝ p q
  obtain ⟨ε₁, hε₁, σ₁, hσ₁, hb₁⟩ := som_half_ball_seg D₁ i₁ hpq h₁ hn hn0
  obtain ⟨ε₂, hε₂, σ₂, hσ₂, hb₂⟩ := som_half_ball_seg D₂ i₂ hpq h₂ hn hn0
  obtain ⟨ε₃, hε₃, σ₃, hσ₃, hb₃⟩ := som_half_ball_seg D₃ i₃ hpq h₃ hn hn0
  have hnp : 0 < ‖nv‖ := norm_pos_iff.mpr hn0
  have key : ∀ (εa εb σ : ℝ), 0 < εa → 0 < εb → (σ = 1 ∨ σ = -1) →
      ∃ z, dist z x < εa ∧ dist z x < εb ∧ 0 < σ * inner ℝ (z - x) nv := by
    intro εa εb σ ha hb hσ
    obtain ⟨t, ht, -, hdx, hi⟩ := som_push x x nv (min εa εb) 1 (by simp [ha, hb]) one_pos hn0 σ hσ
    refine ⟨_, lt_of_lt_of_le hdx (min_le_left _ _), lt_of_lt_of_le hdx (min_le_right _ _), ?_⟩
    rw [hi, sub_self, inner_zero_left]
    rcases hσ with rfl | rfl <;> nlinarith [sq_pos_of_pos hnp]
  rcases hσ₁ with rfl | rfl <;> rcases hσ₂ with rfl | rfl <;> rcases hσ₃ with rfl | rfl
  all_goals first
    | (obtain ⟨z, hza, hzb, hz⟩ := key ε₁ ε₂ _ hε₁ hε₂ (Or.inl rfl)
       exact Or.inl ⟨z, (hb₁ z hza).1 hz, (hb₂ z hzb).1 hz⟩)
    | (obtain ⟨z, hza, hzb, hz⟩ := key ε₁ ε₂ _ hε₁ hε₂ (Or.inr rfl)
       exact Or.inl ⟨z, (hb₁ z hza).1 hz, (hb₂ z hzb).1 hz⟩)
    | (obtain ⟨z, hza, hzb, hz⟩ := key ε₁ ε₃ _ hε₁ hε₃ (Or.inl rfl)
       exact Or.inr (Or.inl ⟨z, (hb₁ z hza).1 hz, (hb₃ z hzb).1 hz⟩))
    | (obtain ⟨z, hza, hzb, hz⟩ := key ε₁ ε₃ _ hε₁ hε₃ (Or.inr rfl)
       exact Or.inr (Or.inl ⟨z, (hb₁ z hza).1 hz, (hb₃ z hzb).1 hz⟩))
    | (obtain ⟨z, hza, hzb, hz⟩ := key ε₂ ε₃ _ hε₂ hε₃ (Or.inl rfl)
       exact Or.inr (Or.inr ⟨z, (hb₂ z hza).1 hz, (hb₃ z hzb).1 hz⟩))
    | (obtain ⟨z, hza, hzb, hz⟩ := key ε₂ ε₃ _ hε₂ hε₃ (Or.inr rfl)
       exact Or.inr (Or.inr ⟨z, (hb₂ z hza).1 hz, (hb₃ z hzb).1 hz⟩))

/-- The translate of a polygonal disk. -/
private def som_trDisk (D : PolygonalDisk) (w : Pt) : PolygonalDisk := som_affDisk D 1 one_ne_zero w

private theorem som_trDisk_carrier (D : PolygonalDisk) (w : Pt) :
    (som_trDisk D w).carrier = w +ᵥ D.carrier := by
  show w +ᵥ (1 : ℝ) • D.carrier = _
  rw [one_smul]

private theorem som_trDisk_side (D : PolygonalDisk) (w : Pt) (i : Fin D.n) :
    (som_trDisk D w).side i = w +ᵥ D.side i := by
  show (som_affDisk D 1 one_ne_zero w).side i = _
  rw [som_affDisk_side, one_smul]

/-- A separated subset of a ball is finite. -/
private theorem som_sep_finite {S : Set Pt} {x : Pt} {M r : ℝ} (hr : 0 < r)
    (hS : S ⊆ Metric.closedBall x M) (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → r ≤ dist a b) : S.Finite := by
  have htb : TotallyBounded S := (isCompact_closedBall x M).totallyBounded.subset hS
  obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.1 htb (r / 2) (by positivity)
  refine (ht.biUnion fun y _ => (?_ : (S ∩ Metric.ball y (r / 2)).Finite)).subset ?_
  · refine Set.Subsingleton.finite fun a ha b hb => ?_
    by_contra hab
    have := hsep a ha.1 b hb.1 hab
    have h1 := Metric.mem_ball.1 ha.2
    have h2 := Metric.mem_ball.1 hb.2
    have := dist_triangle_right a b y
    linarith
  · intro a ha
    obtain ⟨y, hy, hay⟩ := Set.mem_iUnion₂.1 (hcov ha)
    exact Set.mem_iUnion₂.2 ⟨y, hy, ha, hay⟩

/-- Local finiteness of plane tilings: finitely many tiles meet a ball. -/
private theorem som_locally_finite {Pr : Protoset} (T : PlaneTiling Pr) (x : Pt) (ρ : ℝ) :
    {Y ∈ T.tiles | (Y.carrier ∩ Metric.ball x ρ).Nonempty}.Finite := by
  let S : Pr.Form → Set Pt := fun f =>
    {a | (⟨f, a⟩ : PlacedTile Pr) ∈ T.tiles ∧ ((⟨f, a⟩ : PlacedTile Pr).carrier ∩ Metric.ball x ρ).Nonempty}
  have hfin : ∀ f, (S f).Finite := by
    intro f
    obtain ⟨R, hR⟩ := (Pr.disk f).compact.isBounded.subset_closedBall 0
    obtain ⟨c, hc⟩ := (Pr.disk f).interior_nonempty
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior c hc
    refine som_sep_finite (M := ρ + R) (x := x) hr ?_ ?_
    · rintro a ⟨-, z, hz, hzx⟩
      obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.1 hz
      have hy' := Metric.mem_closedBall.1 (hR hy)
      rw [dist_zero_right] at hy'
      rw [Metric.mem_closedBall]
      have h1 := Metric.mem_ball.1 hzx
      have : dist a x ≤ dist (a + y) x + ‖y‖ := by
        rw [dist_eq_norm, dist_eq_norm]
        calc ‖a - x‖ = ‖(a + y - x) - y‖ := by congr 1; abel
          _ ≤ ‖a + y - x‖ + ‖y‖ := norm_sub_le _ _
      simp only [vadd_eq_add] at h1
      linarith
    · intro a ha b hb hab
      by_contra hlt
      push_neg at hlt
      have hne : (⟨f, a⟩ : PlacedTile Pr) ≠ ⟨f, b⟩ := fun h => hab (by cases h; rfl)
      have hd := T.disjoint ha.1 hb.1 hne
      set z := midpoint ℝ (a + c) (b + c)
      have hmem : ∀ e, dist (a + c) (b + c) < 2 * r → (e = a ∨ e = b) →
          z ∈ interior ((⟨f, e⟩ : PlacedTile Pr).carrier) := by
        intro e hdist he
        show z ∈ interior (e +ᵥ (Pr.disk f).carrier)
        rw [interior_vadd]
        refine Set.mem_vadd_set.2 ⟨z - e, hball ?_, by simp⟩
        rw [Metric.mem_ball]
        have h1 : dist z (a + c) = dist (a + c) (b + c) / 2 := by
          rw [dist_comm]; exact dist_left_midpoint (𝕜 := ℝ) _ _ |>.trans (by simp [div_eq_inv_mul])
        have h2 : dist z (b + c) = dist (a + c) (b + c) / 2 := by
          rw [dist_comm]; exact dist_right_midpoint (𝕜 := ℝ) _ _ |>.trans (by simp [div_eq_inv_mul])
        rcases he with rfl | rfl
        · have : dist (z - e) c = dist z (e + c) := by
            rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
          rw [this, h1]; linarith
        · have : dist (z - e) c = dist z (e + c) := by
            rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
          rw [this, h2]; linarith
      have hdist : dist (a + c) (b + c) < 2 * r := by
        rw [dist_add_right]; linarith
      exact Set.disjoint_left.1 hd (hmem a hdist (Or.inl rfl)) (hmem b hdist (Or.inr rfl))
  refine (Set.finite_iUnion fun f => (hfin f).image fun a => (⟨f, a⟩ : PlacedTile Pr)).subset ?_
  rintro ⟨f, a⟩ hY
  exact Set.mem_iUnion.2 ⟨f, a, hY, rfl⟩

private theorem som_tile_carrier {Pr : Protoset} (X : PlacedTile Pr) :
    (som_trDisk (Pr.disk X.form) X.anchor).carrier = X.carrier := som_trDisk_carrier _ _

private theorem som_tile_side {Pr : Protoset} (X : PlacedTile Pr) (i : Fin (Pr.disk X.form).n) :
    (som_trDisk (Pr.disk X.form) X.anchor).side i = X.side i := som_trDisk_side _ _ _

private theorem som_tile_closed {Pr : Protoset} (X : PlacedTile Pr) : IsClosed X.carrier := by
  rw [← som_tile_carrier]; exact (som_trDisk _ _).compact.isClosed

/-- **Coincident sides.**  In a side-to-side plane tiling every listed side of a tile coincides
with a listed side of another tile. -/
private theorem som_coincident_side {Pr : Protoset} (T : PlaneTiling Pr) (hT : T.SideToSide)
    {X : PlacedTile Pr} (hX : X ∈ T.tiles) (i : Fin (Pr.disk X.form).n) :
    ∃ Y ∈ T.tiles, Y ≠ X ∧ ∃ j : Fin (Pr.disk Y.form).n, Y.side j = X.side i := by
  classical
  set D := som_trDisk (Pr.disk X.form) X.anchor
  set a := D.vertex i
  set b := D.vertex (finRotate _ i)
  have hab : a ≠ b := som_vertex_ne D i
  have hDs : D.side i = segment ℝ a b := rfl
  obtain ⟨nv, hn0, hn⟩ := som_exists_normal (b - a) (sub_ne_zero.2 hab.symm)
  obtain ⟨ε, hε, σ, hσ, hb⟩ := som_half_ball_seg D i hab hDs.symm.subset hn hn0
  set x := midpoint ℝ a b
  rw [som_tile_carrier] at hb
  set F := {Y ∈ T.tiles | (Y.carrier ∩ Metric.ball x ε).Nonempty}
  have hF : F.Finite := som_locally_finite T x ε
  have hnp : 0 < ‖b - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hab.symm)
  set δ := min (1 / 2 : ℝ) (ε / (2 * ‖b - a‖))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  set J := (fun t : ℝ => x + t • (b - a)) '' Set.Ioo (-δ) δ
  have hxeq : x = a + (1 / 2 : ℝ) • (b - a) := by
    show midpoint ℝ a b = _
    rw [midpoint_eq_smul_add, invOf_eq_inv]; module
  have hJ : ∀ z ∈ J, z ∈ X.side i ∧ dist z x < ε ∧ inner ℝ (z - x) nv = 0 := by
    rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
    have hta : |t| < δ := abs_lt.2 ⟨ht1, ht2⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← som_tile_side, hDs, segment_eq_image']
      refine ⟨1 / 2 + t, ⟨?_, ?_⟩, by rw [hxeq]; module⟩
      · linarith [min_le_left (1 / 2 : ℝ) (ε / (2 * ‖b - a‖))]
      · linarith [min_le_left (1 / 2 : ℝ) (ε / (2 * ‖b - a‖))]
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      have h1 : |t| < ε / (2 * ‖b - a‖) := lt_of_lt_of_le hta (min_le_right _ _)
      have h2 : |t| * ‖b - a‖ < ε / (2 * ‖b - a‖) * ‖b - a‖ :=
        mul_lt_mul_of_pos_right h1 hnp
      have h3 : ε / (2 * ‖b - a‖) * ‖b - a‖ = ε / 2 := by field_simp
      linarith
    · rw [add_sub_cancel_left, inner_smul_left, hn]; simp
  have hJinf : J.Infinite := by
    refine (Set.Ioo_infinite (by linarith)).image fun t _ s _ hts => ?_
    exact smul_left_injective ℝ (sub_ne_zero.2 hab.symm) (add_left_cancel hts)
  -- every point of `J` lies on a side of another tile meeting the ball
  have hcov : ∀ z ∈ J, ∃ Y ∈ F, Y ≠ X ∧ ∃ j : Fin (Pr.disk Y.form).n, z ∈ Y.side j := by
    intro z hzJ
    obtain ⟨-, hzx, hz0⟩ := hJ z hzJ
    have hmem : ∃ Y ∈ F, Y ≠ X ∧ z ∈ Y.carrier := by
      by_contra hcon
      push_neg at hcon
      have hev : ∀ᶠ y in nhds z, ∀ Y ∈ F, Y ≠ X → y ∉ Y.carrier := by
        rw [Filter.eventually_all_finite hF]
        intro Y hY
        by_cases hYX : Y = X
        · exact Filter.Eventually.of_forall fun _ h => absurd hYX h
        · filter_upwards [(som_tile_closed Y).isOpen_compl.mem_nhds (hcon Y hY hYX)] with y hy _
          exact hy
      obtain ⟨η, hη, hηs⟩ := Metric.eventually_nhds_iff.1 hev
      have hσ' : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
      obtain ⟨t, ht, hd, hdx, hi⟩ := som_push x z nv ε η hzx hη hn0 (-σ) hσ'
      set y := z + (-σ * t) • nv
      have hneg : σ * inner ℝ (y - x) nv < 0 := by
        rw [hi, hz0]
        have := sq_pos_of_pos (norm_pos_iff.2 hn0)
        rcases hσ with rfl | rfl <;> nlinarith
      have hyX : y ∉ X.carrier := (hb y hdx).2 hneg
      have hyU : y ∈ support T.tiles := by rw [T.cover]; trivial
      obtain ⟨Y, hY, hyY⟩ := Set.mem_iUnion₂.1 hyU
      have hYX : Y ≠ X := by rintro rfl; exact hyX hyY
      exact hηs hd Y ⟨hY, y, hyY, Metric.mem_ball.2 hdx⟩ hYX hyY
    obtain ⟨Y, hYF, hYX, hzY⟩ := hmem
    refine ⟨Y, hYF, hYX, ?_⟩
    have hzi : z ∉ interior Y.carrier := by
      intro hzi
      obtain ⟨η, hη, hηs⟩ := Metric.isOpen_iff.1 isOpen_interior z hzi
      obtain ⟨t, ht, hd, hdx, hi⟩ := som_push x z nv ε η hzx hη hn0 σ hσ
      have hpos : 0 < σ * inner ℝ (z + (σ * t) • nv - x) nv := by
        rw [hi, hz0]
        have := sq_pos_of_pos (norm_pos_iff.2 hn0)
        rcases hσ with rfl | rfl <;> nlinarith
      have h1 := (hb _ hdx).1 hpos
      have h2 := hηs hd
      exact Set.disjoint_left.1 (T.disjoint hYF.1 hX hYX) h2 h1
    have hzf : z ∈ frontier (som_trDisk (Pr.disk Y.form) Y.anchor).carrier := by
      rw [som_tile_carrier]
      exact ⟨subset_closure hzY, hzi⟩
    rw [(som_trDisk (Pr.disk Y.form) Y.anchor).frontier_eq, Set.mem_iUnion] at hzf
    obtain ⟨j, hj⟩ := hzf
    exact ⟨j, by rw [← som_tile_side]; exact hj⟩
  -- pigeonhole: some side of another tile contains two points of `J`
  have hpig : ∃ Y ∈ F, Y ≠ X ∧ ∃ j : Fin (Pr.disk Y.form).n,
      ¬ (Y.side j ∩ J).Subsingleton := by
    by_contra hcon
    push_neg at hcon
    apply hJinf
    have hF' : {Y | Y ∈ F ∧ Y ≠ X}.Finite := hF.subset fun Y hY => hY.1
    refine (hF'.biUnion fun Y hY =>
      Set.finite_iUnion fun j => (hcon Y hY.1 hY.2 j).finite).subset ?_
    intro z hz
    obtain ⟨Y, hYF, hYX, j, hj⟩ := hcov z hz
    exact Set.mem_iUnion₂.2 ⟨Y, ⟨hYF, hYX⟩, Set.mem_iUnion.2 ⟨j, hj, hz⟩⟩
  obtain ⟨Y, hYF, hYX, j, hns⟩ := hpig
  obtain ⟨z₁, ⟨hz₁Y, hz₁J⟩, z₂, ⟨hz₂Y, hz₂J⟩, hz₁₂⟩ := Set.not_subsingleton_iff.1 hns
  refine ⟨Y, hYF.1, hYX, j, hT Y hYF.1 X hX j i ⟨z₁, z₂, hz₁₂, ?_⟩⟩
  have hcY : Convex ℝ (Y.side j) := by
    rw [← som_tile_side]; exact convex_segment _ _
  have hcX : Convex ℝ (X.side i) := by
    rw [← som_tile_side]; exact convex_segment _ _
  exact Set.subset_inter (hcY.segment_subset hz₁Y hz₂Y)
    (hcX.segment_subset (hJ z₁ hz₁J).1 (hJ z₂ hz₂J).1)

/-- A segment determines its endpoints up to order. -/
private theorem som_segment_endpoints {a b c d : Pt} (h : segment ℝ a b = segment ℝ c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  by_cases hab : a = b
  · subst hab
    rw [segment_same] at h
    have hc : c ∈ ({a} : Set Pt) := h ▸ left_mem_segment ℝ c d
    have hd : d ∈ ({a} : Set Pt) := h ▸ right_mem_segment ℝ c d
    rw [Set.mem_singleton_iff] at hc hd
    exact Or.inl ⟨hc.symm, hd.symm⟩
  have hc : c ∈ segment ℝ a b := h ▸ left_mem_segment ℝ c d
  have hd : d ∈ segment ℝ a b := h ▸ right_mem_segment ℝ c d
  have ha : a ∈ segment ℝ c d := h ▸ left_mem_segment ℝ a b
  have hb : b ∈ segment ℝ c d := h ▸ right_mem_segment ℝ a b
  rw [segment_eq_image'] at hc hd ha hb
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hc
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hd
  obtain ⟨u, ⟨hu0, hu1⟩, hu⟩ := ha
  obtain ⟨w, ⟨hw0, hw1⟩, hw⟩ := hb
  simp only at hu hw
  have hv : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have e1 : (s + u * (t - s)) • (b - a) = 0 := by
    have : a + s • (b - a) + u • (a + t • (b - a) - (a + s • (b - a))) - a =
        (s + u * (t - s)) • (b - a) := by module
    rw [← this, hu, sub_self]
  have e2 : (s + w * (t - s) - 1) • (b - a) = 0 := by
    have : a + s • (b - a) + w • (a + t • (b - a) - (a + s • (b - a))) - b =
        (s + w * (t - s) - 1) • (b - a) := by module
    rw [← this, hw, sub_self]
  have f1 := (smul_eq_zero.1 e1).resolve_right hv
  have f2 := (smul_eq_zero.1 e2).resolve_right hv
  rcases lt_trichotomy s t with hst | hst | hst
  · have hs : s = 0 := by nlinarith
    subst hs
    have ht : t = 1 := by nlinarith
    subst ht
    left; constructor <;> simp
  · subst hst; simp at f1 f2; linarith
  · have ht : t = 0 := by nlinarith
    subst ht
    have hs : s = 1 := by nlinarith
    subst hs
    right; constructor <;> simp

private theorem som_cond_neg (v : Pt) (hv : v ≠ 0) :
    (0 < (-v) 0 ∨ ((-v) 0 = 0 ∧ 0 < (-v) 1)) ↔ ¬ (0 < v 0 ∨ (v 0 = 0 ∧ 0 < v 1)) := by
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    ext i; fin_cases i
    · exact h.1
    · exact h.2
  simp only [PiLp.neg_apply]
  constructor
  · rintro (h | ⟨h1, h2⟩) <;> intro h' <;> rcases h' with h' | ⟨h1', h2'⟩ <;> linarith
  · intro h
    push_neg at h
    rcases lt_trichotomy (v 0) 0 with h0 | h0 | h0
    · left; linarith
    · right
      refine ⟨by rw [h0]; simp, ?_⟩
      have := h.2 h0
      rcases hv' with h' | h'
      · exact absurd h0 h'
      · have : v 1 < 0 := lt_of_le_of_ne this h'
        linarith
    · exact absurd h0 (not_lt.2 h.1)

private theorem som_canonDir_neg (v : Pt) (hv : v ≠ 0) : Alignment.canonDir (-v) = Alignment.canonDir v := by
  unfold Alignment.canonDir
  rw [norm_neg]
  by_cases h : 0 < v 0 ∨ (v 0 = 0 ∧ 0 < v 1)
  · rw [if_pos h, if_neg ((som_cond_neg v hv).not.2 (not_not.2 h))]
    simp
  · rw [if_neg h, if_pos ((som_cond_neg v hv).2 h)]
    simp

private theorem som_frameOrigin_swap (x y : Pt) (hxy : x ≠ y) : Alignment.frameOrigin y x = Alignment.frameOrigin x y := by
  unfold Alignment.frameOrigin
  have hv : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  have hneg : x - y = -(y - x) := by abel
  rw [hneg]
  by_cases h : 0 < (y - x) 0 ∨ ((y - x) 0 = 0 ∧ 0 < (y - x) 1)
  · rw [if_pos h, if_neg ((som_cond_neg _ hv).not.2 (not_not.2 h))]
  · rw [if_neg h, if_pos ((som_cond_neg _ hv).2 h)]

private theorem som_segCoord_swap (x y z : Pt) (hxy : x ≠ y) : Alignment.segCoord y x z = Alignment.segCoord x y z := by
  unfold Alignment.segCoord
  rw [som_frameOrigin_swap x y hxy]
  have hneg : x - y = -(y - x) := by abel
  rw [hneg, som_canonDir_neg _ (sub_ne_zero.2 hxy.symm)]

private theorem som_segCoord_translate (x y z v : Pt) :
    Alignment.segCoord (v + x) (v + y) (v + z) = Alignment.segCoord x y z := by
  unfold Alignment.segCoord Alignment.frameOrigin Alignment.coord
  rw [add_sub_add_left_eq_sub]
  split_ifs <;> simp

private theorem som_coord_eq_inner (o u z : Pt) : Alignment.coord o u z = inner ℝ (z - o) u := by
  simp [Alignment.coord, PiLp.inner_apply, Fin.sum_univ_two]

private theorem som_canonDir_spec (v : Pt) (hv : v ≠ 0) :
    ‖Alignment.canonDir v‖ = 1 ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ v = (s * ‖v‖) • Alignment.canonDir v := by
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  unfold Alignment.canonDir
  split_ifs
  · refine ⟨?_, 1, Or.inl rfl, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    · rw [smul_smul, one_mul, mul_inv_cancel₀ hn.ne', one_smul]
  · refine ⟨?_, -1, Or.inr rfl, ?_⟩
    · rw [norm_neg, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    · rw [smul_neg, smul_smul, neg_one_mul, neg_mul, mul_inv_cancel₀ hn.ne', neg_smul, one_smul,
        neg_neg]

/-- A point of the line of a nondegenerate segment is recovered from its canonical
coordinate. -/
private theorem som_line_recover (x y z : Pt) (hxy : x ≠ y) (hz : ∃ r : ℝ, z = x + r • (y - x)) :
    z = Alignment.frameOrigin x y + Alignment.segCoord x y z • Alignment.canonDir (y - x) := by
  obtain ⟨r, rfl⟩ := hz
  have hv : y - x ≠ 0 := sub_ne_zero.2 hxy.symm
  obtain ⟨hu, s, hs, hvs⟩ := som_canonDir_spec (y - x) hv
  set u := Alignment.canonDir (y - x)
  have hfo : ∃ μ : ℝ, x + r • (y - x) - Alignment.frameOrigin x y = μ • u := by
    unfold Alignment.frameOrigin
    split_ifs
    · exact ⟨r * (s * ‖y - x‖), by rw [add_sub_cancel_left, mul_smul, ← hvs]⟩
    · refine ⟨(r - 1) * (s * ‖y - x‖), ?_⟩
      rw [mul_smul, ← hvs]; module
  obtain ⟨μ, hμ⟩ := hfo
  unfold Alignment.segCoord
  rw [som_coord_eq_inner, hμ, inner_smul_left, real_inner_self_eq_norm_sq, hu]
  simp only [RCLike.conj_to_real, one_pow, mul_one]
  rw [← hμ]; abel

/-- The endpoints of a segment overlapping a nondegenerate segment with positive length lie on
the line of the latter. -/
private theorem som_on_line_of_overlap {x y c₁ c₂ : Pt}
    (h : OverlapPos (segment ℝ c₁ c₂) (segment ℝ x y)) :
    (∃ r : ℝ, c₁ = x + r • (y - x)) ∧ (∃ r : ℝ, c₂ = x + r • (y - x)) := by
  obtain ⟨p, q, hpq, hs⟩ := h
  have hp := hs (left_mem_segment ℝ p q)
  have hq := hs (right_mem_segment ℝ p q)
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hq1, hq2⟩ := hq
  rw [segment_eq_image'] at hp1 hp2 hq1 hq2
  obtain ⟨α, -, hα⟩ := hp1
  obtain ⟨β, -, hβ⟩ := hq1
  obtain ⟨γ, -, hγ⟩ := hp2
  obtain ⟨δ, -, hδ⟩ := hq2
  simp only at hα hβ hγ hδ
  have hαβ : β - α ≠ 0 := by
    intro h0
    apply hpq
    rw [← hα, ← hβ, sub_eq_zero.1 h0]
  have heq : (β - α) • (c₂ - c₁) = (δ - γ) • (y - x) := by
    have : (β - α) • (c₂ - c₁) = (c₁ + β • (c₂ - c₁)) - (c₁ + α • (c₂ - c₁)) := by module
    rw [this, hα, hβ, ← hγ, ← hδ]; module
  set κ := (β - α)⁻¹ * (δ - γ)
  have hdir : c₂ - c₁ = κ • (y - x) := by
    have := congrArg ((β - α)⁻¹ • ·) heq
    simp only [smul_smul, inv_mul_cancel₀ hαβ, one_smul] at this
    exact this
  have hc₁ : c₁ = x + (γ - α * κ) • (y - x) := by
    have h1 : c₁ = (c₁ + α • (c₂ - c₁)) - α • (c₂ - c₁) := by abel
    rw [h1, hα, ← hγ, hdir]; module
  refine ⟨⟨_, hc₁⟩, ⟨γ - α * κ + κ, ?_⟩⟩
  have h2 : c₂ = c₁ + (c₂ - c₁) := by abel
  rw [h2, hdir, hc₁]; module

/-- **Atoms determine coarse sides.**  If coincident fine sides carry equal atoms of two
coarse sides overlapping them, the placed coarse sides coincide. -/
private theorem som_atom_seg {x y x' y' v w : Pt} {c c' : Pt × Pt} (hxy : x ≠ y)
    (hseg : segment ℝ (v + x) (v + y) = segment ℝ (w + x') (w + y'))
    (hc : OverlapPos (segment ℝ c.1 c.2) (segment ℝ x y))
    (hc' : OverlapPos (segment ℝ c'.1 c'.2) (segment ℝ x' y'))
    (hat : Alignment.atom (x, y) c = Alignment.atom (x', y') c') :
    segment ℝ (v + c.1) (v + c.2) = segment ℝ (w + c'.1) (w + c'.2) := by
  have hend := som_segment_endpoints hseg
  have hx'y' : x' ≠ y' := by
    rintro rfl
    rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hxy (add_left_cancel (h1.trans h2.symm))
    · exact hxy (add_left_cancel (h1.trans h2.symm))
  have hrel : ∀ z, Alignment.segCoord x y z = Alignment.segCoord x' y' (z + (v - w)) := by
    intro z
    have hz : v + z = w + (z + (v - w)) := by abel
    rw [← som_segCoord_translate x y z v]
    rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hz, som_segCoord_translate]
    · rw [h1, h2, hz, som_segCoord_translate, som_segCoord_swap _ _ _ hx'y']
  obtain ⟨hl₁, hl₂⟩ := som_on_line_of_overlap hc
  obtain ⟨hl₁', hl₂'⟩ := som_on_line_of_overlap hc'
  set d₁ := c'.1 + (w - v)
  set d₂ := c'.2 + (w - v)
  have hd : ∀ z, (∃ r : ℝ, z = x' + r • (y' - x')) → ∃ r : ℝ, z + (w - v) = x + r • (y - x) := by
    rintro z ⟨r, rfl⟩
    rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨r, ?_⟩
      have hx : x = x' + (w - v) := by rw [← add_sub_cancel_left v x, h1]; abel
      have hy : y = y' + (w - v) := by rw [← add_sub_cancel_left v y, h2]; abel
      rw [hx, hy]; module
    · refine ⟨1 - r, ?_⟩
      have hx : x = y' + (w - v) := by rw [← add_sub_cancel_left v x, h1]; abel
      have hy : y = x' + (w - v) := by rw [← add_sub_cancel_left v y, h2]; abel
      rw [hx, hy]; module
  have hsd : ∀ z, Alignment.segCoord x' y' z = Alignment.segCoord x y (z + (w - v)) := by
    intro z; rw [hrel]; congr 1; abel
  have hmin : min (Alignment.segCoord x y c.1) (Alignment.segCoord x y c.2) = min (Alignment.segCoord x y d₁) (Alignment.segCoord x y d₂) := by
    have := congrArg (fun t => t.2.2.1) hat
    simp only [Alignment.atom] at this
    rw [this, hsd, hsd]
  have hmax : max (Alignment.segCoord x y c.1) (Alignment.segCoord x y c.2) = max (Alignment.segCoord x y d₁) (Alignment.segCoord x y d₂) := by
    have := congrArg (fun t => t.2.2.2) hat
    simp only [Alignment.atom] at this
    rw [this, hsd, hsd]
  have hpair : (Alignment.segCoord x y c.1 = Alignment.segCoord x y d₁ ∧ Alignment.segCoord x y c.2 = Alignment.segCoord x y d₂) ∨
      (Alignment.segCoord x y c.1 = Alignment.segCoord x y d₂ ∧ Alignment.segCoord x y c.2 = Alignment.segCoord x y d₁) := by
    rcases le_total (Alignment.segCoord x y c.1) (Alignment.segCoord x y c.2) with h | h <;>
      rcases le_total (Alignment.segCoord x y d₁) (Alignment.segCoord x y d₂) with h' | h'
    · rw [min_eq_left h, min_eq_left h'] at hmin; rw [max_eq_right h, max_eq_right h'] at hmax
      exact Or.inl ⟨hmin, hmax⟩
    · rw [min_eq_left h, min_eq_right h'] at hmin; rw [max_eq_right h, max_eq_left h'] at hmax
      exact Or.inr ⟨hmin, hmax⟩
    · rw [min_eq_right h, min_eq_left h'] at hmin; rw [max_eq_left h, max_eq_right h'] at hmax
      exact Or.inr ⟨hmax, hmin⟩
    · rw [min_eq_right h, min_eq_right h'] at hmin; rw [max_eq_left h, max_eq_left h'] at hmax
      exact Or.inl ⟨hmax, hmin⟩
  have hrec : ∀ z z', (∃ r : ℝ, z = x + r • (y - x)) → (∃ r : ℝ, z' = x + r • (y - x)) →
      Alignment.segCoord x y z = Alignment.segCoord x y z' → z = z' := by
    intro z z' hz hz' he
    rw [som_line_recover x y z hxy hz, som_line_recover x y z' hxy hz', he]
  have hw₁ : w + c'.1 = v + d₁ := by simp only [d₁]; abel
  have hw₂ : w + c'.2 = v + d₂ := by simp only [d₂]; abel
  rw [hw₁, hw₂]
  rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hrec _ _ hl₁ (hd _ hl₁') h1, hrec _ _ hl₂ (hd _ hl₂') h2]
  · rw [hrec _ _ hl₁ (hd _ hl₂') h1, hrec _ _ hl₂ (hd _ hl₁') h2, segment_symm]

/-- Cells of a legal tile on a side whose fifth cell is zero and whose fourth cell is a
schedule tag: the side is outer and the fourth cell is its own schedule tag. -/
private theorem som_legal_outer_cell {A : StrictDecTile C hC} (hA : StrictLegal C hC A)
    (i : C.Side A.typ) (h4 : A.cell i 4 = 0) (h3 : (readSched C hC (A.cell i 3)).isSome) :
    C.IsOuter (C.occ A.typ i) ∧ A.cell i 3 = schedU C hC (C.occ A.typ i) := by
  classical
  obtain ⟨ch, h0, hch, -⟩ := hA
  have hc := (hch 0).2
  rw [h0] at hc
  have hcell : ∀ k, A.cell i k = (strictChild C hC (ch (0 + 1)) A.typ).cell i k := by
    intro k
    obtain ⟨t, col⟩ := A
    injection hc with _ hcol
    exact congrFun (congrFun hcol i) k
  simp only [strictChild, strictGen] at hcell
  have hnp : ¬ ∃ d, C.IsPrintOf (C.form (ch (0 + 1)).typ) d (C.occ A.typ i) := by
    intro hp
    have e4 := hcell 4
    have hcs : ¬ (copySource C (C.form (ch (0 + 1)).typ) (C.occ A.typ i) 4).Nonempty := by
      rintro ⟨p, hp | hp⟩
      · exact hp.2.1 rfl
      · exact absurd hp.2.1 (by decide)
    rw [dif_neg hcs, strictGenCell, if_pos hp, if_pos rfl, h4] at e4
    cases e4
  have hcs3 : ¬ (copySource C (C.form (ch (0 + 1)).typ) (C.occ A.typ i) 3).Nonempty := by
    rintro ⟨p, hp | hp⟩
    · exact hnp ⟨p.1, hp.1⟩
    · exact absurd hp.2.1 (by decide)
  have e3 := hcell 3
  rw [dif_neg hcs3, strictGenCell, if_neg hnp, if_neg (by decide), if_pos rfl] at e3
  by_cases ho : C.IsOuter (C.occ A.typ i)
  · rw [if_pos ho] at e3
    exact ⟨ho, e3⟩
  · rw [if_neg ho] at e3
    exfalso
    split_ifs at e3 with hb
    · rw [e3] at h3; simp [readSched, headerSU] at h3
    · rw [e3] at h3; simp [readSched, botSU] at h3

/-- Two lists strictly sorted by real keys, each element of one having an element of the other
with the same key (and related by `R` in the forward direction), are related by `Forall₂ R`. -/
private theorem som_forall₂_of_sorted {α β : Type*} (R : α → β → Prop) (f : α → ℝ) (f' : β → ℝ) :
    ∀ (L : List α) (L' : List β), L.Pairwise (fun a b => f a < f b) →
      L'.Pairwise (fun a b => f' a < f' b) →
      (∀ a ∈ L, ∃ b ∈ L', R a b ∧ f' b = f a) → (∀ b ∈ L', ∃ a ∈ L, f a = f' b) →
      List.Forall₂ R L L' := by
  intro L
  induction L with
  | nil =>
    intro L' _ _ _ h2
    cases L' with
    | nil => exact List.Forall₂.nil
    | cons b L' =>
      obtain ⟨a, ha, -⟩ := h2 b List.mem_cons_self
      cases ha
  | cons a L ih =>
    intro L' hL hL' h1 h2
    cases L' with
    | nil =>
      obtain ⟨b, hb, -⟩ := h1 a List.mem_cons_self
      cases hb
    | cons b L' =>
      rw [List.pairwise_cons] at hL hL'
      obtain ⟨b₁, hb₁, hR, hfb⟩ := h1 a List.mem_cons_self
      obtain ⟨a₁, ha₁, hfa⟩ := h2 b List.mem_cons_self
      have hle1 : f' b ≤ f' b₁ := by
        rcases List.mem_cons.1 hb₁ with rfl | h
        · exact le_rfl
        · exact (hL'.1 _ h).le
      have hle2 : f a ≤ f a₁ := by
        rcases List.mem_cons.1 ha₁ with rfl | h
        · exact le_rfl
        · exact (hL.1 _ h).le
      have hab : f a = f' b := by linarith
      have hbb : b₁ = b := by
        rcases List.mem_cons.1 hb₁ with h | h
        · exact h
        · have := hL'.1 _ h; linarith
      subst hbb
      refine List.Forall₂.cons hR (ih L' hL.2 hL'.2 ?_ ?_)
      · intro a' ha'
        obtain ⟨b', hb', hR', hf'⟩ := h1 a' (List.mem_cons_of_mem _ ha')
        refine ⟨b', ?_, hR', hf'⟩
        rcases List.mem_cons.1 hb' with h | h
        · subst h; have := hL.1 _ ha'; linarith
        · exact h
      · intro b' hb'
        obtain ⟨a', ha', hf'⟩ := h2 b' (List.mem_cons_of_mem _ hb')
        refine ⟨a', ?_, hf'⟩
        rcases List.mem_cons.1 ha' with h | h
        · subst h; have := hL'.1 _ hb'; linarith
        · exact h

private theorem som_placed_mem {T : PlaneTiling (strictProtoset C hC)}
    (part : StrictMacroPartition C hC T) (j : part.ι) (t : C.Typ) (ht : C.owner t = (part.block j).α) :
    (part.block j).placed t ∈ T.tiles := by
  rw [← part.cover]; exact Set.mem_iUnion.2 ⟨j, t, ht, rfl⟩

private theorem som_mem_block {T : PlaneTiling (strictProtoset C hC)}
    (part : StrictMacroPartition C hC T) {Y : PlacedTile (strictProtoset C hC)} (hY : Y ∈ T.tiles) :
    ∃ j t, C.owner t = (part.block j).α ∧ Y = (part.block j).placed t := by
  rw [← part.cover] at hY
  obtain ⟨j, t, ht, rfl⟩ := Set.mem_iUnion.1 hY
  exact ⟨j, t, ht, rfl⟩

private theorem som_childSide_eq (K : StrictBlock C hC) (o : C.SideOcc) :
    K.childSide o = K.v +ᵥ C.occSide o := by
  simp only [StrictBlock.childSide, MacroData.occSide, MacroData.childTile, PlacedTile.side, vadd_vadd]

private theorem som_placed_carrier (K : StrictBlock C hC) (t : C.Typ) :
    (K.placed t).carrier = K.v +ᵥ (C.childTile t).carrier := by
  simp only [StrictBlock.placed, PlacedTile.carrier, MacroData.childTile, vadd_vadd]
  rfl

private theorem som_childTile_mem (t : C.Typ) : C.childTile t ∈ (C.σ.rule (C.owner t)).tiles := by
  rw [C.rule_eq]; exact ⟨t, rfl, rfl⟩

private theorem som_placed_carrier_subset (K : StrictBlock C hC) (t : C.Typ) (ht : C.owner t = K.α) :
    (K.placed t).carrier ⊆ K.v +ᵥ C.σ.θ • (C.Q.disk K.α).carrier := by
  rw [som_placed_carrier, ← C.σ.support_eq, ← ht]
  exact Set.vadd_set_mono (Set.subset_biUnion_of_mem (som_childTile_mem C t))

private theorem som_region_subset (K : StrictBlock C hC) :
    K.v +ᵥ C.σ.θ • (C.Q.disk K.α).carrier ⊆ ⋃ t ∈ {t | C.owner t = K.α}, (K.placed t).carrier := by
  rw [← C.σ.support_eq]
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨A, hA, hzA⟩ := Set.mem_iUnion₂.1 hz
  rw [C.rule_eq] at hA
  obtain ⟨t, ht, rfl⟩ := hA
  refine Set.mem_iUnion₂.2 ⟨t, ht, ?_⟩
  rw [som_placed_carrier]
  exact Set.vadd_mem_vadd_set hzA

/-- An open nonempty set covered by finitely many closed sets meets the interior of one. -/
private theorem som_open_cover_interior {ι : Type*} (F : ι → Set Pt) (hF : ∀ k, IsClosed (F k)) :
    ∀ (s : Finset ι) (U : Set Pt), IsOpen U → U.Nonempty → U ⊆ ⋃ k ∈ s, F k →
      ∃ k ∈ s, (U ∩ interior (F k)).Nonempty := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro U _ ⟨z, hz⟩ hU
    simpa using hU hz
  | insert k s hk ih =>
    intro U hUo hUn hU
    by_cases hsub : U ⊆ F k
    · exact ⟨k, Finset.mem_insert_self _ _, hUn.mono fun z hz =>
        ⟨hz, interior_maximal hsub hUo hz⟩⟩
    · obtain ⟨z, hzU, hzk⟩ := Set.not_subset.1 hsub
      obtain ⟨k', hk', hne⟩ := ih (U \ F k) (hUo.sdiff (hF k)) ⟨z, hzU, hzk⟩ (by
        intro y ⟨hyU, hyk⟩
        have := hU hyU
        simp only [Finset.mem_insert, Set.mem_iUnion, exists_prop] at this
        obtain ⟨k'', hk'', hy⟩ := this
        rcases hk'' with rfl | hk''
        · exact absurd hy hyk
        · exact Set.mem_iUnion₂.2 ⟨k'', hk'', hy⟩)
      exact ⟨k', Finset.mem_insert_of_mem hk', hne.mono fun y hy => ⟨hy.1.1, hy.2⟩⟩

/-- Macroregions of distinct blocks have disjoint interiors. -/
private theorem som_region_disjoint {T : PlaneTiling (strictProtoset C hC)}
    (part : StrictMacroPartition C hC T) {j₁ j₂ : part.ι} (hne : j₁ ≠ j₂) :
    Disjoint (interior ((part.block j₁).v +ᵥ C.σ.θ • (C.Q.disk (part.block j₁).α).carrier))
      (interior ((part.block j₂).v +ᵥ C.σ.θ • (C.Q.disk (part.block j₂).α).carrier)) := by
  classical
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  have hcov : ∀ (jj : part.ι) (U : Set Pt), IsOpen U → U.Nonempty →
      U ⊆ (part.block jj).v +ᵥ C.σ.θ • (C.Q.disk (part.block jj).α).carrier →
      ∃ t, C.owner t = (part.block jj).α ∧ (U ∩ interior ((part.block jj).placed t).carrier).Nonempty := by
    intro jj U hU hUn hsub
    obtain ⟨t, ht, hne⟩ := som_open_cover_interior (fun t => ((part.block jj).placed t).carrier)
      (fun t => som_tile_closed _) (Finset.univ.filter fun t => C.owner t = (part.block jj).α) U hU hUn
      (by
        intro y hy
        obtain ⟨t, ht, hyt⟩ := Set.mem_iUnion₂.1 (som_region_subset C hC _ (hsub hy))
        exact Set.mem_iUnion₂.2 ⟨t, by simpa using ht, hyt⟩)
    exact ⟨t, by simpa using ht, hne⟩
  obtain ⟨t₁, ht₁, y, ⟨hy₁, hy₂⟩, hyX₁⟩ := hcov j₁ _ (isOpen_interior.inter isOpen_interior)
    ⟨z, hz₁, hz₂⟩ (fun y hy => interior_subset hy.1)
  obtain ⟨t₂, ht₂, w, ⟨hw₁, hw₂⟩, hwX₂⟩ := hcov j₂ _ (isOpen_interior.inter isOpen_interior)
    ⟨y, hy₂, hyX₁⟩ (fun y hy => interior_subset hy.1)
  have hX₁ := som_placed_mem C hC part j₁ t₁ ht₁
  have hX₂ := som_placed_mem C hC part j₂ t₂ ht₂
  have heq : (part.block j₁).placed t₁ = (part.block j₂).placed t₂ := by
    by_contra hXne
    exact Set.disjoint_left.1 (T.disjoint hX₁ hX₂ hXne) hw₂ hwX₂
  have hm₁ : (part.block j₁).placed t₁ ∈ (part.block j₁).tiles := ⟨t₁, ht₁, rfl⟩
  have hm₂ : (part.block j₁).placed t₁ ∈ (part.block j₂).tiles := heq ▸ ⟨t₂, ht₂, rfl⟩
  exact Set.disjoint_left.1 (part.disjoint hne) hm₁ hm₂

private theorem som_finRotate_two_ne {n : ℕ} (hn : 3 ≤ n) (d : Fin n) :
    finRotate n (finRotate n d) ≠ d := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [finRotate_succ_apply, finRotate_succ_apply]
  intro h
  have h2 : (1 : Fin (k + 1)) + 1 = 0 := by
    have : d + (1 + 1) = d + 0 := by rw [add_zero, ← add_assoc]; exact h
    exact add_left_cancel this
  have := congrArg Fin.val h2
  rw [Fin.val_add, Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (show 1 < k + 1 by omega),
    Nat.mod_eq_of_lt (show 1 + 1 < k + 1 by omega)] at this
  omega

/-- A polygonal disk with distinct sides `d ≠ e` has distinct side segments. -/
private theorem som_side_inj (D : PolygonalDisk) {d e : Fin D.n} (h : D.side e = D.side d) : e = d := by
  rcases som_segment_endpoints h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact D.vertex_injective h1
  · have he := D.vertex_injective h1
    have hd := D.vertex_injective h2
    exfalso
    apply som_finRotate_two_ne D.three_le d
    rw [← he, hd]

private theorem som_theta_ne : C.σ.θ ≠ 0 := by linarith [C.σ.one_lt]

/-- The macroregion of a block as a polygonal disk. -/
private def som_macroDisk (K : StrictBlock C hC) : PolygonalDisk :=
  som_affDisk (C.Q.disk K.α) C.σ.θ (som_theta_ne C) K.v

private theorem som_macroDisk_carrier (K : StrictBlock C hC) :
    (som_macroDisk C hC K).carrier = K.v +ᵥ C.σ.θ • (C.Q.disk K.α).carrier := rfl

private theorem som_macroDisk_side (K : StrictBlock C hC) (d : Fin (C.Q.disk K.α).n) :
    (som_macroDisk C hC K).side d = K.macroSide d := by
  show (som_affDisk (C.Q.disk K.α) C.σ.θ (som_theta_ne C) K.v).side d = _
  rw [som_affDisk_side]; rfl

private theorem som_macroSide_inj (K : StrictBlock C hC) {d e : Fin (C.Q.disk K.α).n}
    (h : K.macroSide e = K.macroSide d) : e = d := by
  rw [← som_macroDisk_side, ← som_macroDisk_side] at h
  exact som_side_inj (som_macroDisk C hC K) h

/-- Two distinct children of one block cannot share a side contained in a macroside. -/
private theorem som_not_same_block {T : PlaneTiling (strictProtoset C hC)}
    (part : StrictMacroPartition C hC T) (jj : part.ι) {t t' : C.Typ} (ht : C.owner t = (part.block jj).α)
    (ht' : C.owner t' = (part.block jj).α) (hne : t' ≠ t) (i : C.Side t) (i' : C.Side t')
    (d : Fin (C.Q.disk (part.block jj).α).n)
    (hside : (part.block jj).childSide (C.occ t' i') = (part.block jj).childSide (C.occ t i))
    (hsub : (part.block jj).childSide (C.occ t i) ⊆ (part.block jj).macroSide d) : False := by
  set X := (part.block jj).placed t
  set Y := (part.block jj).placed t'
  have hX := som_placed_mem C hC part jj t ht
  have hY := som_placed_mem C hC part jj t' ht'
  have hXY : Y ≠ X := by
    intro h
    apply hne
    have := congrArg PlacedTile.form h
    simp only [Y, X, StrictBlock.placed, StrictBlock.tileOf, StrictForm.typed.injEq] at this
    exact congrArg StrictDecTile.typ this
  set D₁ := som_trDisk ((strictProtoset C hC).disk X.form) X.anchor
  set D₂ := som_trDisk ((strictProtoset C hC).disk Y.form) Y.anchor
  have hpq := som_vertex_ne D₁ i
  have h₁ : D₁.side i = X.side i := som_tile_side X i
  have h₂ : D₂.side i' = X.side i := (som_tile_side Y i').trans hside
  have hR := som_two_cover D₁ D₂ i i' hpq le_rfl (h₂.trans h₁.symm).symm.subset
    (by rw [som_tile_carrier, som_tile_carrier]; exact T.disjoint hX hY hXY.symm)
    (som_macroDisk C hC (part.block jj)).compact.isClosed
    (by rw [som_tile_carrier]; exact som_placed_carrier_subset C hC (part.block jj) t ht)
    (by rw [som_tile_carrier]; exact som_placed_carrier_subset C hC (part.block jj) t' ht')
  have hmid : midpoint ℝ (D₁.vertex i) (D₁.vertex (finRotate _ i)) ∈ (part.block jj).macroSide d := by
    apply hsub
    show _ ∈ X.side i
    rw [← h₁]
    exact openSegment_subset_segment _ _ _ (som_sub_segment hpq le_rfl).1
  rw [← som_macroDisk_side] at hmid
  have hf : midpoint ℝ (D₁.vertex i) (D₁.vertex (finRotate _ i)) ∈
      frontier (som_macroDisk C hC (part.block jj)).carrier := by
    rw [(som_macroDisk C hC (part.block jj)).frontier_eq, Set.mem_iUnion]; exact ⟨d, hmid⟩
  exact hf.2 hR

/-- Three pairwise distinct blocks cannot share a macroside. -/
private theorem som_three_blocks {T : PlaneTiling (strictProtoset C hC)}
    (part : StrictMacroPartition C hC T) {j₁ j₂ j₃ : part.ι} (h₁₂ : j₁ ≠ j₂) (h₁₃ : j₁ ≠ j₃)
    (h₂₃ : j₂ ≠ j₃) (e₁ : Fin (C.Q.disk (part.block j₁).α).n) (e₂ : Fin (C.Q.disk (part.block j₂).α).n)
    (e₃ : Fin (C.Q.disk (part.block j₃).α).n)
    (h₂ : (part.block j₂).macroSide e₂ = (part.block j₁).macroSide e₁)
    (h₃ : (part.block j₃).macroSide e₃ = (part.block j₁).macroSide e₁) : False := by
  set D₁ := som_macroDisk C hC (part.block j₁)
  have hpq := som_vertex_ne D₁ e₁
  have hs₁ : D₁.side e₁ = (part.block j₁).macroSide e₁ := som_macroDisk_side C hC _ e₁
  rcases som_three D₁ (som_macroDisk C hC (part.block j₂)) (som_macroDisk C hC (part.block j₃)) e₁ e₂ e₃
      hpq le_rfl (by rw [som_macroDisk_side, h₂, ← hs₁]; rfl)
      (by rw [som_macroDisk_side, h₃, ← hs₁]; rfl) with h | h | h
  · exact Set.disjoint_iff.1 (som_region_disjoint C hC part h₁₂) h.some_mem
  · exact Set.disjoint_iff.1 (som_region_disjoint C hC part h₁₃) h.some_mem
  · exact Set.disjoint_iff.1 (som_region_disjoint C hC part h₂₃) h.some_mem

private theorem som_vadd_segment (w a b : Pt) : w +ᵥ segment ℝ a b = segment ℝ (w + a) (w + b) := by
  rw [← segment_translate_image]; rfl

private theorem som_affine_segment (θ : ℝ) (hθ : θ ≠ 0) (w a b : Pt) :
    w +ᵥ θ • segment ℝ a b = segment ℝ (w + θ • a) (w + θ • b) := by
  rw [← som_homeo_image θ hθ w, som_homeo_segment]

private theorem som_occSide_eq (o : C.SideOcc) : C.occSide o = segment ℝ (C.occStart o) (C.occEnd o) := by
  simp only [MacroData.occSide, MacroData.childTile, PlacedTile.side, PolygonalDisk.side,
    som_vadd_segment, MacroData.occStart, MacroData.occEnd]

private theorem som_occStart_ne (o : C.SideOcc) : C.occStart o ≠ C.occEnd o := by
  intro h
  exact som_vertex_ne _ o.2 (add_left_cancel h)

private theorem som_isInner_of_isPrintOf {α : C.Q.Form} {d : Fin (C.Q.disk α).n} {o : C.SideOcc}
    (h : C.IsPrintOf α d o) : C.IsInner o := by
  rcases h with ⟨hm, rfl | rfl⟩
  · exact C.g4_print_inner α d hm
  · have hin := C.g4_print_inner α d hm
    have hp := C.g1_partner _ hin
    unfold MacroData.IsInner MacroData.IsOuter at hin ⊢
    rw [hp.2.2, hp.2.1]
    exact hin

/-- Cells of a legal tile on an outer side: zero fifth cell and its own schedule tag. -/
private theorem som_legal_outer_cells {A : StrictDecTile C hC} (hA : StrictLegal C hC A)
    (i : C.Side A.typ) (ho : C.IsOuter (C.occ A.typ i)) :
    A.cell i 4 = 0 ∧ A.cell i 3 = schedU C hC (C.occ A.typ i) := by
  classical
  obtain ⟨ch, h0, hch, -⟩ := hA
  have hc := (hch 0).2
  rw [h0] at hc
  have hcell : ∀ k, A.cell i k = (strictChild C hC (ch (0 + 1)) A.typ).cell i k := by
    intro k
    obtain ⟨t, col⟩ := A
    injection hc with _ hcol
    exact congrFun (congrFun hcol i) k
  simp only [strictChild, strictGen] at hcell
  have hnp : ¬ ∃ d, C.IsPrintOf (C.form (ch (0 + 1)).typ) d (C.occ A.typ i) := fun ⟨_, hd⟩ =>
    som_isInner_of_isPrintOf C hd ho
  have hcs : ∀ k, k ≠ 2 → ¬ (copySource C (C.form (ch (0 + 1)).typ) (C.occ A.typ i) k).Nonempty := by
    rintro k hk ⟨p, hp | hp⟩
    · exact hnp ⟨p.1, hp.1⟩
    · exact hk hp.2.1
  have e4 := hcell 4
  rw [dif_neg (hcs 4 (by decide)), strictGenCell, if_neg hnp] at e4
  have e3 := hcell 3
  rw [dif_neg (hcs 3 (by decide)), strictGenCell, if_neg hnp, if_neg (by decide), if_pos rfl,
    if_pos ho] at e3
  exact ⟨by rw [e4]; rfl, e3⟩

private theorem som_schedU_inj {o o' : C.SideOcc} (h : schedU C hC o = schedU C hC o') :
    schedOf C hC o = schedOf C hC o' := by
  simp only [schedU] at h
  injection h with h
  injection h with h
  exact congrArg Subtype.val h

private theorem som_macroSide_cast {α β : C.Q.Form} (h : α = β) (d : Fin (C.Q.disk β).n) :
    C.macroSide α (Fin.cast (by rw [h]) d) = C.macroSide β d := by
  subst h; rfl

private theorem som_macroSide_segment (α : C.Q.Form) (d : Fin (C.Q.disk α).n) :
    C.macroSide α d = segment ℝ (Alignment.parentSide τ hC.groupedFamily m α d).1
      (Alignment.parentSide τ hC.groupedFamily m α d).2 := by
  have := som_affine_segment C.σ.θ (som_theta_ne C) 0 ((C.Q.disk α).vertex d)
    ((C.Q.disk α).vertex (finRotate _ d))
  rw [zero_vadd, zero_add, zero_add] at this
  rw [MacroData.macroSide, PolygonalDisk.side, this, hC.θ_eq]
  rfl

/-- The scaled parent side containing an outer fine side contributes its atom to the top layer
of the schedule of that side. -/
private theorem som_top_atom (o : C.SideOcc) (d : Fin (C.Q.disk (C.owner o.1)).n)
    (hsub : C.occSide o ⊆ C.macroSide (C.owner o.1) d) :
    Alignment.atom (C.occStart o, C.occEnd o) (Alignment.parentSide τ hC.groupedFamily m (C.owner o.1) d) ∈
        schedOf C hC o .top ∧
      OverlapPos (segment ℝ (Alignment.parentSide τ hC.groupedFamily m (C.owner o.1) d).1
        (Alignment.parentSide τ hC.groupedFamily m (C.owner o.1) d).2)
        (segment ℝ (C.occStart o) (C.occEnd o)) := by
  have hov : OverlapPos (segment ℝ (Alignment.parentSide τ hC.groupedFamily m (C.owner o.1) d).1
      (Alignment.parentSide τ hC.groupedFamily m (C.owner o.1) d).2)
      (segment ℝ (C.occStart o) (C.occEnd o)) := by
    refine ⟨C.occStart o, C.occEnd o, som_occStart_ne C o, Set.subset_inter ?_ le_rfl⟩
    rw [← som_macroSide_segment C hC, ← som_occSide_eq]
    exact hsub
  exact ⟨⟨_, ⟨d, rfl⟩, hov, rfl⟩, hov⟩

/-- **Opposite macroside of one outer side.**  The tile across an outer fine side of a
macroside lies in another block, on a complete macroside coinciding with the given one, and the
fine side is a listed outer side of that macroside. -/
private theorem som_opposite {T : PlaneTiling (strictProtoset C hC)} (hT : IsStrictMatched C hC T)
    (hL : AllStrictLegal C hC T) (part : StrictMacroPartition C hC T) (jj : part.ι)
    (dd : Fin (C.Q.disk (part.block jj).α).n) (o : C.SideOcc)
    (ho : o ∈ C.outerList (part.block jj).α dd) :
    ∃ j₂, j₂ ≠ jj ∧ ∃ e : Fin (C.Q.disk (part.block j₂).α).n,
      (part.block j₂).macroSide e = (part.block jj).macroSide dd ∧
      ∃ o₂ ∈ C.outerList (part.block j₂).α e, (part.block j₂).childSide o₂ = (part.block jj).childSide o := by
  obtain ⟨hown, hout, hsub⟩ := (C.g3_outerList_mem _ dd o).1 ho
  obtain ⟨t, i⟩ := o
  have hX := som_placed_mem C hC part jj t hown
  obtain ⟨Y, hY, hYX, jY, hjY⟩ := som_coincident_side T hT.1 hX i
  obtain ⟨j₂, t₂, ht₂, rfl⟩ := som_mem_block C hC part hY
  change C.Side t₂ at jY
  have hside : (part.block j₂).childSide ⟨t₂, jY⟩ = (part.block jj).childSide ⟨t, i⟩ := hjY
  have hcol : (part.block jj).col t i = (part.block j₂).col t₂ jY :=
    hT.2 ((part.block jj).tileOf t) ((part.block j₂).tileOf t₂) _ _ hX hY hYX.symm i jY hjY.symm
  have hlX : StrictLegal C hC ((part.block jj).tileOf t) := hL _ hX
  have hlY : StrictLegal C hC ((part.block j₂).tileOf t₂) := hL _ hY
  obtain ⟨hX4, hX3⟩ := som_legal_outer_cells C hC hlX i hout
  have hY4 : ((part.block j₂).tileOf t₂).cell jY 4 = 0 := by
    show (part.block j₂).col t₂ jY 4 = 0
    rw [← hcol]; exact hX4
  have hY3s : (readSched C hC (((part.block j₂).tileOf t₂).cell jY 3)).isSome := by
    show (readSched C hC ((part.block j₂).col t₂ jY 3)).isSome
    rw [← hcol]
    change (readSched C hC (((part.block jj).tileOf t).cell i 3)).isSome
    rw [hX3]; rfl
  obtain ⟨hYout, hY3⟩ := som_legal_outer_cell C hC hlY jY hY4 hY3s
  have hsch : schedOf C hC ⟨t, i⟩ = schedOf C hC ⟨t₂, jY⟩ :=
    som_schedU_inj C hC (hX3.symm.trans ((congrFun hcol 3).trans hY3))
  set d' : Fin (C.Q.disk (C.owner t)).n := Fin.cast (by rw [hown]) dd
  have hmd : C.macroSide (C.owner t) d' = C.macroSide (part.block jj).α dd :=
    som_macroSide_cast C hown dd
  obtain ⟨hat, hov⟩ := som_top_atom C hC ⟨t, i⟩ d'
    (by show C.occSide _ ⊆ C.macroSide (C.owner t) d'; rw [hmd]; exact hsub)
  rw [hsch] at hat
  obtain ⟨c', ⟨a, rfl⟩, hov', hat'⟩ := hat
  set e : Fin (C.Q.disk (part.block j₂).α).n := Fin.cast (congrArg (fun α => (C.Q.disk α).n) ht₂) a
  have hme : C.macroSide (C.owner t₂) a = C.macroSide (part.block j₂).α e := by
    rw [← som_macroSide_cast C ht₂ e]
    rfl
  have hseg : segment ℝ ((part.block jj).v + C.occStart ⟨t, i⟩) ((part.block jj).v + C.occEnd ⟨t, i⟩) =
      segment ℝ ((part.block j₂).v + C.occStart ⟨t₂, jY⟩) ((part.block j₂).v + C.occEnd ⟨t₂, jY⟩) := by
    rw [← som_vadd_segment, ← som_vadd_segment, ← som_occSide_eq, ← som_occSide_eq,
      ← som_childSide_eq, ← som_childSide_eq, hside]
  have hcs := som_atom_seg (som_occStart_ne C _) hseg hov hov' hat'
  have hmacro : (part.block j₂).macroSide e = (part.block jj).macroSide dd := by
    show (part.block j₂).v +ᵥ C.macroSide _ e = (part.block jj).v +ᵥ C.macroSide _ dd
    rw [← hme, ← hmd, som_macroSide_segment C hC, som_macroSide_segment C hC, som_vadd_segment,
      som_vadd_segment, hcs]
  have hsub' : (part.block jj).childSide ⟨t, i⟩ ⊆ (part.block jj).macroSide dd := by
    rw [som_childSide_eq]; exact Set.vadd_set_mono hsub
  refine ⟨j₂, ?_, e, hmacro, ⟨t₂, jY⟩, ?_, hside⟩
  · rintro rfl
    refine som_not_same_block C hC part j₂ hown ht₂ ?_ i jY dd hside hsub'
    rintro rfl
    exact hYX rfl
  · rw [C.g3_outerList_mem]
    refine ⟨ht₂, hYout, ?_⟩
    have : (part.block j₂).v +ᵥ C.occSide ⟨t₂, jY⟩ ⊆ (part.block j₂).v +ᵥ C.macroSide _ e := by
      rw [← som_childSide_eq, hside]
      exact hsub'.trans hmacro.symm.subset
    exact (Set.vadd_set_subset_vadd_set_iff).1 this

private theorem som_add_midpoint (v a b : Pt) : v + midpoint ℝ a b = midpoint ℝ (v + a) (v + b) := by
  rw [midpoint_eq_smul_add, midpoint_eq_smul_add, invOf_eq_inv]; module

private theorem som_childSide_segment (K : StrictBlock C hC) (o : C.SideOcc) :
    K.childSide o = segment ℝ (K.v + C.occStart o) (K.v + C.occEnd o) := by
  rw [som_childSide_eq, som_occSide_eq, som_vadd_segment]

/-- Coincident placed fine sides have the same placed midpoint. -/
private theorem som_mid_of_childSide {K K' : StrictBlock C hC} {o o' : C.SideOcc}
    (h : K.childSide o = K'.childSide o') : K.v + C.occMid o = K'.v + C.occMid o' := by
  rw [som_childSide_segment, som_childSide_segment] at h
  simp only [MacroData.occMid, som_add_midpoint]
  rcases som_segment_endpoints h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, midpoint_comm]

private theorem som_posDir_eq {u v u' v' : Pt} (h : v' - u' = v - u ∨ v' - u' = -(v - u))
    (hne : v - u ≠ 0) : C.posDir u' v' = C.posDir u v := by
  unfold MacroData.posDir
  have e1 : u' - v' = -(v' - u') := by abel
  have e2 : u - v = -(v - u) := by abel
  rw [e1, e2]
  rcases h with h | h
  · rw [h]
  · rw [h, neg_neg]
    by_cases hp : C.IsPositive (v - u)
    · rw [if_pos hp, if_neg ((C.g3_pos_iff _ hne).1 hp)]
    · rw [if_neg hp, if_pos (by by_contra hn; exact hp ((C.g3_pos_iff _ hne).2 hn))]

private theorem som_macroSide_segment' (K : StrictBlock C hC) (d : Fin (C.Q.disk K.α).n) :
    K.macroSide d = segment ℝ (K.v + C.σ.θ • (C.Q.disk K.α).vertex d)
      (K.v + C.σ.θ • (C.Q.disk K.α).vertex (finRotate _ d)) :=
  som_affine_segment _ (som_theta_ne C) _ _ _

private theorem som_macroSideDir_ne (α : C.Q.Form) (d : Fin (C.Q.disk α).n) : C.macroSideDir α d ≠ 0 := by
  have hne : C.σ.θ • (C.Q.disk α).vertex (finRotate _ d) - C.σ.θ • (C.Q.disk α).vertex d ≠ 0 := by
    rw [← smul_sub]
    exact smul_ne_zero (som_theta_ne C) (sub_ne_zero.2 (som_vertex_ne _ d).symm)
  unfold MacroData.macroSideDir MacroData.posDir
  split_ifs
  · exact hne
  · intro h; apply hne; rw [← neg_sub, h, neg_zero]

/-- Coinciding macrosides have the same positive direction. -/
private theorem som_macroSideDir_eq {K K' : StrictBlock C hC} {d : Fin (C.Q.disk K.α).n}
    {e : Fin (C.Q.disk K'.α).n} (h : K'.macroSide e = K.macroSide d) :
    C.macroSideDir K'.α e = C.macroSideDir K.α d := by
  rw [som_macroSide_segment', som_macroSide_segment'] at h
  apply som_posDir_eq C
  · rcases som_segment_endpoints h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      calc _ = K'.v + C.σ.θ • (C.Q.disk K'.α).vertex (finRotate _ e) -
            (K'.v + C.σ.θ • (C.Q.disk K'.α).vertex e) := by abel
        _ = _ := by rw [h1, h2]; abel
    · right
      calc _ = K'.v + C.σ.θ • (C.Q.disk K'.α).vertex (finRotate _ e) -
            (K'.v + C.σ.θ • (C.Q.disk K'.α).vertex e) := by abel
        _ = _ := by rw [h1, h2]; abel
  · rw [← smul_sub]
    exact smul_ne_zero (som_theta_ne C) (sub_ne_zero.2 (som_vertex_ne _ d).symm)

/-- The outer list of a macroside is strictly sorted by the coordinate of the placed midpoints
along its positive direction. -/
private theorem som_sorted (K : StrictBlock C hC) (d : Fin (C.Q.disk K.α).n) (w : Pt) (v : Pt)
    (hw : w = C.macroSideDir K.α d) :
    (C.outerList K.α d).Pairwise
      (fun o o' => inner ℝ (v + C.occMid o) w < inner ℝ (v + C.occMid o') w) := by
  refine (C.g3_outerList_sorted K.α d).imp ?_
  rintro o o' ⟨r, hr, hro⟩
  have hw0 : w ≠ 0 := hw ▸ som_macroSideDir_ne C K.α d
  have : inner ℝ (v + C.occMid o') w - inner ℝ (v + C.occMid o) w = r * ‖w‖ ^ 2 := by
    rw [← inner_sub_left, add_sub_add_left_eq_sub, hro, ← hw, inner_smul_left,
      real_inner_self_eq_norm_sq]
    simp
  have : 0 < r * ‖w‖ ^ 2 := mul_pos hr (pow_pos (norm_pos_iff.2 hw0) 2)
  linarith

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
  have _ := hτ
  have _ := hΔ
  obtain ⟨o₀, ho₀⟩ := List.exists_mem_of_length_pos
    (lt_of_lt_of_le (by norm_num) (C.g3_five_le (part.block j).α d))
  obtain ⟨j', hj', e, hme, -⟩ := som_opposite C hC hT hL part j d o₀ ho₀
  refine ⟨j', hj', e, hme, ?_⟩
  set w := C.macroSideDir (part.block j).α d
  refine som_forall₂_of_sorted _ (fun o => inner ℝ ((part.block j).v + C.occMid o) w)
    (fun o => inner ℝ ((part.block j').v + C.occMid o) w) _ _
    (som_sorted C hC _ d w _ rfl) (som_sorted C hC _ e w _ (som_macroSideDir_eq C hC hme).symm) ?_ ?_
  · intro o ho
    obtain ⟨j₂, hj₂, e₂, hme₂, o₂, ho₂, hs₂⟩ := som_opposite C hC hT hL part j d o ho
    have hjj : j₂ = j' := by
      by_contra hne
      exact som_three_blocks C hC part (Ne.symm hj') (Ne.symm hj₂) (Ne.symm hne) d e e₂ hme hme₂
    subst hjj
    have hee : e₂ = e := som_macroSide_inj C hC _ (hme₂.trans hme.symm)
    subst hee
    exact ⟨o₂, ho₂, hs₂.symm, by simp only [som_mid_of_childSide C hC hs₂]⟩
  · intro o' ho'
    obtain ⟨j₃, hj₃, e₃, hme₃, o₃, ho₃, hs₃⟩ := som_opposite C hC hT hL part j' e o' ho'
    have hjj : j₃ = j := by
      by_contra hne
      exact som_three_blocks C hC part (Ne.symm hj') (Ne.symm hne) (Ne.symm hj₃) d e e₃ hme (hme₃.trans hme)
    subst hjj
    have hdd : e₃ = d := som_macroSide_inj C hC _ (hme₃.trans hme)
    subst hdd
    exact ⟨o₃, ho₃, by simp only [som_mid_of_childSide C hC hs₃]⟩

private theorem scr_open_meets_interior {ι : Type*} (F : ι → Set Pt) (hF : ∀ i, IsClosed (F i))
    (s : Finset ι) : ∀ U : Set Pt, IsOpen U → U.Nonempty → U ⊆ ⋃ i ∈ s, F i →
      ∃ i ∈ s, (U ∩ interior (F i)).Nonempty := by
  classical
  induction s using Finset.induction_on with
  | empty => intro U _ ⟨x, hx⟩ hs; simpa using hs hx
  | insert a s ha ih =>
    intro U hU hne hsub
    by_cases h : (U ∩ interior (F a)).Nonempty
    · exact ⟨a, Finset.mem_insert_self _ _, h⟩
    · have hne' : (U \ F a).Nonempty := by
        by_contra h'
        rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at h'
        exact h (by rw [Set.inter_eq_left.mpr (interior_maximal h' hU)]; exact hne)
      obtain ⟨i, hi, hx⟩ := ih (U \ F a) (hU.sdiff (hF a)) hne' (by
        intro x hx
        have := hsub hx.1
        simp only [Finset.set_biUnion_insert, Set.mem_union] at this
        exact this.resolve_left hx.2)
      exact ⟨i, Finset.mem_insert_of_mem hi, hx.mono (Set.inter_subset_inter_left _ Set.diff_subset)⟩

private theorem scr_block_support_eq_biUnion (K : StrictBlock C hC) :
    support K.tiles = ⋃ t ∈ Finset.univ.filter (fun t => C.owner t = K.α), (K.placed t).carrier := by
  ext x
  simp [support, StrictBlock.tiles]

private theorem scr_placed_closed (K : StrictBlock C hC) (t : C.Typ) : IsClosed (K.placed t).carrier :=
  ((C.Q.disk (C.form t)).compact.vadd _).isClosed

private theorem scr_block_support (K : StrictBlock C hC) :
    support K.tiles = K.v +ᵥ C.σ.θ • (C.Q.disk K.α).carrier := by
  rw [← C.σ.support_eq, C.rule_eq]
  ext x
  simp only [support, StrictBlock.tiles, StrictBlock.placed, PlacedTile.carrier, Set.mem_iUnion,
    Set.mem_setOf_eq, Set.biUnion_image, Set.mem_vadd_set, vadd_eq_add, exists_prop]
  constructor
  · rintro ⟨_, ⟨i, h1, rfl⟩, y, h2, rfl⟩
    exact ⟨_, ⟨i, h1, y, h2, rfl⟩, (add_assoc _ _ _).symm⟩
  · rintro ⟨_, ⟨i, h1, y, h2, rfl⟩, rfl⟩
    exact ⟨_, ⟨i, h1, rfl⟩, y, h2, add_assoc _ _ _⟩

private theorem scr_recon_carrier (K : StrictBlock C hC) (t : C.Typ) (ht : C.form t = K.α) :
    C.σ.θ • (⟨.typed (strictReconstruct C hC K t), C.σ.θ⁻¹ • K.v⟩ : PlacedTile (strictProtoset C hC)).carrier =
      support K.tiles := by
  have hθ : C.σ.θ ≠ 0 := (zero_lt_one.trans C.σ.one_lt).ne'
  rw [scr_block_support]
  show C.σ.θ • (C.σ.θ⁻¹ • K.v +ᵥ (C.Q.disk (C.form t)).carrier) = _
  rw [ht]
  ext x
  simp only [Set.mem_smul_set, Set.mem_vadd_set, vadd_eq_add]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, by rw [smul_add, smul_inv_smul₀ hθ]⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, by rw [smul_add, smul_inv_smul₀ hθ]⟩

/-- Step 1 of the blueprint proof of
`strict_composed_proper_step1_reconstruction_step1_headers`: establish strict proper realization
of each assembled block from strict matching and the partition. -/
private theorem strict_composed_proper_step1_reconstruction_step1_headers_step1_proper
    (T : PlaneTiling (strictProtoset C hC)) (hT : IsStrictMatched C hC T)
    (part : StrictMacroPartition C hC T) (j : part.ι) :
    IsStrictProperRealization C hC (part.block j) := by
  sorry

/-- Step 2 of the blueprint proof of
`strict_composed_proper_step1_reconstruction_step1_headers`: establish legality of every
noncentral child from legality of the original tiling and the partition cover. -/
private theorem strict_composed_proper_step1_reconstruction_step1_headers_step2_legal
    (T : PlaneTiling (strictProtoset C hC)) (hL : AllStrictLegal C hC T)
    (part : StrictMacroPartition C hC T) (j : part.ι) :
    ∀ t, C.owner t = (part.block j).α → t ≠ C.central (part.block j).α →
      StrictLegal C hC ((part.block j).tileOf t) := by
  sorry

/-- Step 1 of the blueprint proof of `strict_composed_proper_step1_reconstruction`: every block
of the assembled strict partition of a strictly matched legal tiling has a common boundary header
(`lem:comp/boundary-header`): the block is a `StrictBlockContext` (a strictly matched realization
whose noncentral children are legal, from `hT`, `hL` and `part`) and
`strict_boundary_header_constant` applies. -/
private theorem strict_composed_proper_step1_reconstruction_step1_headers
    (T : PlaneTiling (strictProtoset C hC)) (hT : IsStrictMatched C hC T)
    (hL : AllStrictLegal C hC T) (part : StrictMacroPartition C hC T) (j : part.ι) :
    ∃ h : HeaderKernel.Header C.Typ C.Side, StrictCommonHeader C hC (part.block j) h := by
  exact strict_boundary_header_constant C hC (part.block j) ⟨
    strict_composed_proper_step1_reconstruction_step1_headers_step1_proper C hC T hT part j,
    strict_composed_proper_step1_reconstruction_step1_headers_step2_legal C hC T hL part j⟩

/-- Step 1 of the blueprint proof of `strict_composed_proper`: construct the plane tiling
of reconstructed parents from an assembled strict macro-partition.  Strict matching and
legality of `T` are needed: a `StrictBlock` records only its form `α`, offset and colours, and
the reconstructed parent must be a typed tile whose polygon is that of `α`, i.e. of a type `t`
with `C.form t = α` (nothing in `MacroCertificate` makes `C.form` surjective).  With them every
block is a `StrictBlockContext`, its boundary fourth cells carry a common header whose type has
form `α` (`lem:comp/boundary-header`), and already the legality of one child gives a parent of
form `α`. -/
private theorem strict_composed_proper_step1_reconstruction (hτ : τ.STS)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (C.Δ α).tiles))
    (T : PlaneTiling (strictProtoset C hC)) (hT : IsStrictMatched C hC T)
    (hL : AllStrictLegal C hC T) (part : StrictMacroPartition C hC T) :
    ∃ T' : PlaneTiling (strictProtoset C hC),
      IsStrictReconstruction C hC part T' := by
  have _ := hτ; have _ := hΔ; have _ := hT
  classical
  have hθ : C.σ.θ ≠ 0 := (zero_lt_one.trans C.σ.one_lt).ne'
  choose hd hhd using strict_composed_proper_step1_reconstruction_step1_headers C hC T hT hL part
  have htj : ∀ j, C.form (hd j).1 = (part.block j).α := fun j => (hhd j).1
  let X : part.ι → PlacedTile (strictProtoset C hC) := fun j =>
    ⟨.typed (strictReconstruct C hC (part.block j) (hd j).1), C.σ.θ⁻¹ • (part.block j).v⟩
  have hX : ∀ j, C.σ.θ • (X j).carrier = support (part.block j).tiles := fun j =>
    scr_recon_carrier C hC _ _ (htj j)
  have hsuppT : support T.tiles = ⋃ j, support (part.block j).tiles := by
    rw [← part.cover]
    ext x
    simp only [support, Set.mem_iUnion, exists_prop]
    exact ⟨fun ⟨A, ⟨j, hA⟩, hx⟩ => ⟨j, A, hA, hx⟩, fun ⟨j, A, hA, hx⟩ => ⟨A, ⟨j, hA⟩, hx⟩⟩
  refine ⟨⟨Set.range X, ?_, ?_⟩, ?_, ?_⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    have hx : C.σ.θ • x ∈ support T.tiles := T.cover ▸ Set.mem_univ _
    rw [hsuppT, Set.mem_iUnion] at hx
    obtain ⟨j, hj⟩ := hx
    rw [← hX j, Set.smul_mem_smul_set_iff₀ hθ] at hj
    exact Set.mem_biUnion (Set.mem_range_self j) hj
  · rintro _ ⟨j, rfl⟩ _ ⟨j', rfl⟩ hne
    have hjj : j ≠ j' := fun h => hne (h ▸ rfl)
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    have hy : C.σ.θ • x ∈ interior (support (part.block j).tiles) := by
      rw [← hX j, interior_smul₀ hθ]; exact Set.smul_mem_smul_set hx
    have hy' : C.σ.θ • x ∈ interior (support (part.block j').tiles) := by
      rw [← hX j', interior_smul₀ hθ]; exact Set.smul_mem_smul_set hx'
    obtain ⟨t, ht, hU⟩ := scr_open_meets_interior _ (scr_placed_closed C hC (part.block j)) _ _
      (isOpen_interior.inter isOpen_interior) ⟨_, hy, hy'⟩
      ((Set.inter_subset_left.trans interior_subset).trans (scr_block_support_eq_biUnion C hC _).subset)
    obtain ⟨t', ht', hU'⟩ := scr_open_meets_interior _ (scr_placed_closed C hC (part.block j')) _ _
      ((isOpen_interior.inter isOpen_interior).inter isOpen_interior) hU
      (((Set.inter_subset_left.trans Set.inter_subset_right).trans interior_subset).trans
        (scr_block_support_eq_biUnion C hC _).subset)
    obtain ⟨z, ⟨-, hz⟩, hz'⟩ := hU'
    have hA : (part.block j).placed t ∈ (part.block j).tiles :=
      ⟨t, (Finset.mem_filter.1 ht).2, rfl⟩
    have hB : (part.block j').placed t' ∈ (part.block j').tiles :=
      ⟨t', (Finset.mem_filter.1 ht').2, rfl⟩
    have hAB : (part.block j).placed t ≠ (part.block j').placed t' := fun h =>
      Set.disjoint_left.1 (part.disjoint hjj) hA (h ▸ hB)
    have hAT : (part.block j).placed t ∈ T.tiles := part.cover ▸ Set.mem_iUnion.2 ⟨j, hA⟩
    have hBT : (part.block j').placed t' ∈ T.tiles := part.cover ▸ Set.mem_iUnion.2 ⟨j', hB⟩
    exact Set.disjoint_left.1 (T.disjoint hAT hBT hAB) hz hz'
  · rintro _ ⟨j, rfl⟩
    exact ⟨j, (smul_inv_smul₀ hθ _).symm, hd j, hhd j, rfl⟩
  · intro j
    exact ⟨X j, Set.mem_range_self j, (smul_inv_smul₀ hθ _).symm, hd j, hhd j, rfl⟩

/-- Step 1 of the blueprint proof of `strict_composed_proper_step2_exact`: obtain the
strict block context needed by the boundary-header and exactness lemmas. -/
private theorem strict_composed_proper_step2_exact_step1_block_context
    (T : PlaneTiling (strictProtoset C hC)) (hT : IsStrictMatched C hC T)
    (hL : AllStrictLegal C hC T) (part : StrictMacroPartition C hC T) (j : part.ι) :
    StrictBlockContext C hC (part.block j) := by
  refine ⟨fun t i ht hin => ?_, fun t ht _ => hL _ (som_placed_mem C hC part j t ht)⟩
  obtain ⟨hne, hown, hside⟩ := C.g1_partner (C.occ t i) hin
  refine ⟨(C.partner (C.occ t i)).1, (C.partner (C.occ t i)).2, hown.trans ht, hne, ?_,
    fun k => ?_⟩
  · rw [som_childSide_eq, som_childSide_eq]
    exact congrArg _ hside
  · have hA := som_placed_mem C hC part j _ (hown.trans ht)
    have hB := som_placed_mem C hC part j t ht
    have hAB : (part.block j).placed (C.partner (C.occ t i)).1 ≠ (part.block j).placed t := by
      intro h
      apply hne
      simp only [StrictBlock.placed, PlacedTile.mk.injEq, StrictForm.typed.injEq] at h
      exact congrArg StrictDecTile.typ h.1
    have hcol := hT.2 _ _ _ _ hA hB hAB (C.partner (C.occ t i)).2 i (by
      exact (som_childSide_eq C hC _ _).trans
        ((congrArg _ hside).trans (som_childSide_eq C hC _ (C.occ t i)).symm))
    exact congrFun hcol k

/-- Step 2 of the blueprint proof of `strict_composed_proper_step2_exact`: apply exact repaired
decomposition to one assembled block and its common boundary header. -/
private theorem strict_composed_proper_step2_exact_step2_exact_block
    (K : StrictBlock C hC) (hK : StrictBlockContext C hC K)
    (h : HeaderKernel.Header C.Typ C.Side) (hh : StrictCommonHeader C hC K h) :
    IsStrictExactBlockOf C hC K (strictReconstruct C hC K h.1) := by
  sorry

/-- Step 3 of the blueprint proof of `strict_composed_proper_step2_exact`: identify the
substitution patch of a reconstructed parent with its assembled block. -/
private theorem strict_composed_proper_step2_exact_step3_block_patch
    (K : StrictBlock C hC) (D : StrictDecTile C hC)
    (X : PlacedTile (strictProtoset C hC))
    (hE : IsStrictExactBlockOf C hC K D)
    (hv : K.v = C.σ.θ • X.anchor)
    (hform : X.form = StrictForm.typed D) :
    (strictSubst C hC).decomposeTile X = K.tiles := by
  sorry

/-- Step 4 of the blueprint proof of `strict_composed_proper_step2_exact`: glue the local
block-patch equalities into the global decomposition equality. -/
private theorem strict_composed_proper_step2_exact_step4_set_union_glue
    (T : PlaneTiling (strictProtoset C hC)) (part : StrictMacroPartition C hC T)
    (T' : PlaneTiling (strictProtoset C hC))
    (hleft : ∀ X ∈ T'.tiles, ∃ j, (strictSubst C hC).decomposeTile X =
      (part.block j).tiles)
    (hright : ∀ j, ∃ X ∈ T'.tiles, (strictSubst C hC).decomposeTile X =
      (part.block j).tiles) :
    (strictSubst C hC).decompose T'.tiles = T.tiles := by
  unfold Substitution.decompose
  rw [← part.cover]
  apply Set.Subset.antisymm
  · intro Y hY
    obtain ⟨X, hX⟩ := Set.mem_iUnion.1 hY
    obtain ⟨hXT, hYX⟩ := Set.mem_iUnion.1 hX
    obtain ⟨j, hpatch⟩ := hleft X hXT
    exact Set.mem_iUnion.2 ⟨j, hpatch ▸ hYX⟩
  · intro Y hY
    obtain ⟨j, hY⟩ := Set.mem_iUnion.1 hY
    obtain ⟨X, hXT, hpatch⟩ := hright j
    exact Set.mem_iUnion.2 ⟨X, Set.mem_iUnion.2 ⟨hXT, hpatch.symm ▸ hY⟩⟩

/-- Step 2 of the blueprint proof of `strict_composed_proper`: each assembled block is an
exact strict decomposition of its reconstructed parent. -/
private theorem strict_composed_proper_step2_exact (hτ : τ.STS)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (C.Δ α).tiles))
    (T : PlaneTiling (strictProtoset C hC)) (hT : IsStrictMatched C hC T)
    (hL : AllStrictLegal C hC T) (part : StrictMacroPartition C hC T)
    (T' : PlaneTiling (strictProtoset C hC))
    (hrec : IsStrictReconstruction C hC part T') :
    (strictSubst C hC).IsComposition T' T := by
  have _ := hτ
  have _ := hΔ
  have hleft : ∀ X ∈ T'.tiles, ∃ j,
      (strictSubst C hC).decomposeTile X = (part.block j).tiles := by
    intro X hX
    obtain ⟨j, hv, h, hh, hform⟩ := hrec.1 X hX
    have hK := strict_composed_proper_step2_exact_step1_block_context C hC T hT hL part j
    have hex := strict_composed_proper_step2_exact_step2_exact_block C hC (part.block j) hK h hh
    exact ⟨j, strict_composed_proper_step2_exact_step3_block_patch C hC
      (part.block j) (strictReconstruct C hC (part.block j) h.1) X hex hv hform⟩
  have hright : ∀ j, ∃ X ∈ T'.tiles, (strictSubst C hC).decomposeTile X =
      (part.block j).tiles := by
    intro j
    obtain ⟨X, hX, hv, h, hh, hform⟩ := hrec.2 j
    have hK := strict_composed_proper_step2_exact_step1_block_context C hC T hT hL part j
    have hex := strict_composed_proper_step2_exact_step2_exact_block C hC (part.block j) hK h hh
    exact ⟨X, hX, strict_composed_proper_step2_exact_step3_block_patch C hC
      (part.block j) (strictReconstruct C hC (part.block j) h.1) X hex hv hform⟩
  exact strict_composed_proper_step2_exact_step4_set_union_glue C hC T part T' hleft hright

/-- Every block of a strict macro-partition of a strictly matched legal tiling is a
`StrictBlockContext`. -/
private theorem step3_blockContext (T : PlaneTiling (strictProtoset C hC)) (hT : IsStrictMatched C hC T)
    (hL : AllStrictLegal C hC T) (part : StrictMacroPartition C hC T) (j : part.ι) :
    StrictBlockContext C hC (part.block j) := by
  refine ⟨fun t i ht hin => ?_, fun t ht _ => hL _ (som_placed_mem C hC part j t ht)⟩
  obtain ⟨hne, hown, hside⟩ := C.g1_partner (C.occ t i) hin
  refine ⟨(C.partner (C.occ t i)).1, (C.partner (C.occ t i)).2, hown.trans ht, hne, ?_, fun k => ?_⟩
  · rw [som_childSide_eq, som_childSide_eq]
    exact congrArg _ hside
  · have hA := som_placed_mem C hC part j _ (hown.trans ht)
    have hB := som_placed_mem C hC part j t ht
    have hAB : (part.block j).placed (C.partner (C.occ t i)).1 ≠ (part.block j).placed t := by
      intro h
      apply hne
      simp only [StrictBlock.placed, PlacedTile.mk.injEq, StrictForm.typed.injEq] at h
      exact congrArg StrictDecTile.typ h.1
    have := hT.2 _ _ _ _ hA hB hAB (C.partner (C.occ t i)).2 i (by
      exact (som_childSide_eq C hC _ _).trans ((congrArg _ hside).trans (som_childSide_eq C hC _ (C.occ t i)).symm))
    exact congrFun this k

/-- Step 3 of the blueprint proof of `strict_composed_proper`: reconstructed parents are
normal and identity-correct. -/
private theorem strict_composed_proper_step3_properties (hτ : τ.STS)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (C.Δ α).tiles))
    (T : PlaneTiling (strictProtoset C hC)) (hT : IsStrictMatched C hC T)
    (hL : AllStrictLegal C hC T) (part : StrictMacroPartition C hC T)
    (T' : PlaneTiling (strictProtoset C hC))
    (hrec : IsStrictReconstruction C hC part T') :
    ∀ X ∈ T'.tiles, ∃ D, X.form = StrictForm.typed D ∧ IsStrictNormal C hC D ∧
      IsStrictIdentityCorrect C hC D := by
  have _ := hτ; have _ := hΔ
  intro X hX
  obtain ⟨j, -, h, hh, hform⟩ := hrec.1 X hX
  obtain ⟨hN, hI, -⟩ := strict_reconstructed_header_eq C hC (part.block j)
    (step3_blockContext C hC T hT hL part j) h hh
  exact ⟨_, hform, hN, hI⟩

/-- Step 1 of the blueprint proof of `strict_composed_proper_step4_matched`: the geometric
side-to-side part. -/
private theorem strict_composed_proper_step4_matched_step1_sides (hτ : τ.STS)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (C.Δ α).tiles))
    (T : PlaneTiling (strictProtoset C hC)) (hT : IsStrictMatched C hC T)
    (hL : AllStrictLegal C hC T) (part : StrictMacroPartition C hC T)
    (T' : PlaneTiling (strictProtoset C hC))
    (hrec : IsStrictReconstruction C hC part T') :
    T'.SideToSide := by
  sorry

/-- Step 2 of the blueprint proof of `strict_composed_proper_step4_matched`: the numbered-port
colour step. -/
private theorem strict_composed_proper_step4_matched_step2_colours (hτ : τ.STS)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (C.Δ α).tiles))
    (T : PlaneTiling (strictProtoset C hC)) (hT : IsStrictMatched C hC T)
    (hL : AllStrictLegal C hC T) (part : StrictMacroPartition C hC T)
    (T' : PlaneTiling (strictProtoset C hC))
    (hrec : IsStrictReconstruction C hC part T') :
    ∀ (A B : StrictDecTile C hC) (v w : Pt),
      (⟨.typed A, v⟩ : PlacedTile (strictProtoset C hC)) ∈ T'.tiles →
      (⟨.typed B, w⟩ : PlacedTile (strictProtoset C hC)) ∈ T'.tiles →
      (⟨.typed A, v⟩ : PlacedTile (strictProtoset C hC)) ≠ ⟨.typed B, w⟩ →
      ∀ (i : C.Side A.typ) (j : C.Side B.typ),
        v +ᵥ (C.Q.disk (C.form A.typ)).side i = w +ᵥ (C.Q.disk (C.form B.typ)).side j →
        A.cell i = B.cell j := by
  sorry

/-- Step 4 of the blueprint proof of `strict_composed_proper`: equal parent sides are
strictly matched, using `strict_opposing_macroside` and the numbered ports. -/
private theorem strict_composed_proper_step4_matched (hτ : τ.STS)
    (hΔ : ∀ α j, SideToSideSet (τ.decomposeIter j (C.Δ α).tiles))
    (T : PlaneTiling (strictProtoset C hC)) (hT : IsStrictMatched C hC T)
    (hL : AllStrictLegal C hC T) (part : StrictMacroPartition C hC T)
    (T' : PlaneTiling (strictProtoset C hC))
    (hrec : IsStrictReconstruction C hC part T') :
    IsStrictMatched C hC T' := by
  exact ⟨strict_composed_proper_step4_matched_step1_sides C hC hτ hΔ T hT hL part T' hrec,
    strict_composed_proper_step4_matched_step2_colours C hC hτ hΔ T hT hL part T' hrec⟩

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
  obtain ⟨part⟩ := strict_assembleMacrotemplates_of_legal C hC T hT hL
  obtain ⟨T', hrec⟩ := strict_composed_proper_step1_reconstruction C hC hτ hΔ T hT hL part
  exact ⟨part, T', hrec,
    strict_composed_proper_step4_matched C hC hτ hΔ T hT hL part T' hrec,
    strict_composed_proper_step3_properties C hC hτ hΔ T hT hL part T' hrec,
    strict_composed_proper_step2_exact C hC hτ hΔ T hT hL part T' hrec⟩

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

open Alignment in
private lemma scs1_segment_infinite {x y : Pt} (hxy : x ≠ y) : (segment ℝ x y).Infinite := by
  rw [segment_eq_image_lineMap]
  refine (Set.Icc_infinite (zero_lt_one' ℝ)).image ?_
  exact (AffineMap.lineMap_injective ℝ hxy).injOn

open Alignment in
private lemma scs1_cover {x y : Pt} (hxy : x ≠ y) {S : Set (Set Pt)} (hS : S.Finite)
    (hconv : ∀ T ∈ S, Convex ℝ T) (hcov : segment ℝ x y ⊆ ⋃₀ S) :
    ∃ T ∈ S, ∃ u v : Pt, u ≠ v ∧ segment ℝ u v ⊆ segment ℝ x y ∩ T := by
  by_contra hcon
  push_neg at hcon
  have hsub : ∀ T ∈ S, (segment ℝ x y ∩ T).Subsingleton := by
    intro T hT u hu v hv
    by_contra huv
    exact hcon T hT u v huv (((convex_segment x y).inter (hconv T hT)).segment_subset hu hv)
  apply scs1_segment_infinite hxy
  refine Set.Finite.subset (hS.biUnion fun T hT => (hsub T hT).finite) ?_
  intro z hz
  obtain ⟨T, hT, hzT⟩ := hcov hz
  exact Set.mem_biUnion hT ⟨hz, hzT⟩

open Alignment in
private lemma scs1_placedSeg_eq (v : Pt) (e : Pt × Pt) :
    placedSeg v e = v +ᵥ segment ℝ e.1 e.2 := (vadd_segment _ _ _ _).symm

open Alignment in
private lemma scs1_tile_side_eq (B : PlacedTile P) (i : Fin (P.disk B.form).n) :
    B.side i = segment ℝ (B.vertex i) (B.vertex (finRotate _ i)) := by
  simp [PlacedTile.side, PolygonalDisk.side, PlacedTile.vertex, vadd_segment]

open Alignment in
private lemma scs1_translate_side (B : PlacedTile P) (v : Pt) (i : Fin (P.disk B.form).n) :
    (B.translate v).side i = placedSeg v (B.vertex i, B.vertex (finRotate _ i)) := by
  rw [scs1_tile_side_eq, placedSeg]
  simp only [PlacedTile.translate, PlacedTile.vertex, vadd_eq_add, add_assoc]

open Alignment in
private lemma scs1_frontier_vadd (v : Pt) (s : Set Pt) : frontier (v +ᵥ s) = v +ᵥ frontier s := by
  have := (Homeomorph.addLeft v).image_frontier s
  rw [Homeomorph.coe_addLeft] at this
  exact this.symm

open Alignment in
private lemma scs1_frontier_smul {c : ℝ} (hc : c ≠ 0) (s : Set Pt) : frontier (c • s) = c • frontier s :=
  ((Homeomorph.smulOfNeZero c hc).image_frontier s).symm

open Alignment in
private lemma scs1_frontier_carrier (B : PlacedTile P) : frontier B.carrier = ⋃ i, B.side i := by
  rw [PlacedTile.carrier, scs1_frontier_vadd, (P.disk B.form).frontier_eq, Set.vadd_set_iUnion]
  rfl

open Alignment in
private lemma scs1_closure_interior_carrier (B : PlacedTile P) :
    closure (interior B.carrier) = B.carrier := by
  rw [PlacedTile.carrier, interior_vadd, closure_vadd, (P.disk B.form).regular_closed]

open Alignment in
private lemma scs1_carrier_closed (B : PlacedTile P) : IsClosed B.carrier := by
  rw [← scs1_closure_interior_carrier]; exact isClosed_closure

open Alignment in
private lemma scs1_side_subset_carrier (B : PlacedTile P) (i : Fin (P.disk B.form).n) :
    B.side i ⊆ B.carrier := by
  intro z hz
  have : z ∈ frontier B.carrier := by
    rw [scs1_frontier_carrier]; exact Set.mem_iUnion.2 ⟨i, hz⟩
  exact (scs1_carrier_closed B).frontier_subset this

open Alignment in
private lemma scs1_translate_carrier (B : PlacedTile P) (v : Pt) :
    (B.translate v).carrier = v +ᵥ B.carrier := by
  ext x
  simp only [PlacedTile.carrier, PlacedTile.translate, Set.mem_vadd_set_iff_neg_vadd_mem,
    vadd_eq_add, neg_add_rev]
  rw [← add_assoc]


open Alignment in
private lemma scs1_decomposeIter_mono (τ : Substitution P)
    (n : ℕ) {S S' : Set (PlacedTile P)} (h : S ⊆ S') :
    τ.decomposeIter n S ⊆ τ.decomposeIter n S' := by
  induction n with
  | zero => exact h
  | succ n ih =>
    intro B hB
    change B ∈ τ.decompose (τ.decomposeIter n S) at hB
    change B ∈ τ.decompose (τ.decomposeIter n S')
    simp only [Substitution.decompose, Set.mem_iUnion] at hB ⊢
    obtain ⟨C, hC, hBC⟩ := hB
    exact ⟨C, ih hC, hBC⟩

open Alignment in
private lemma scs1_decomposeIter_translate (τ : Substitution P)
    (n : ℕ) (v : Pt) (S : Set (PlacedTile P))
    (B : PlacedTile P) (hB : B ∈ τ.decomposeIter n S) :
    B.translate ((τ.θ ^ n) • v) ∈ τ.decomposeIter n (translateSet v S) := by
  induction n generalizing B with
  | zero =>
    show B.translate ((τ.θ ^ 0) • v) ∈ translateSet v S
    rw [pow_zero, one_smul]
    exact ⟨B, hB, rfl⟩
  | succ n ih =>
    change B ∈ τ.decompose (τ.decomposeIter n S) at hB
    change _ ∈ τ.decompose (τ.decomposeIter n (translateSet v S))
    simp only [Substitution.decompose, Set.mem_iUnion] at hB ⊢
    obtain ⟨C, hC, hBC⟩ := hB
    refine ⟨C.translate ((τ.θ ^ n) • v), ih C hC, ?_⟩
    simp only [Substitution.decomposeTile, translateSet, Set.mem_image] at hBC ⊢
    obtain ⟨R, hR, rfl⟩ := hBC
    refine ⟨R, hR, ?_⟩
    simp only [PlacedTile.translate, PlacedTile.mk.injEq, true_and, vadd_eq_add, smul_add,
      pow_succ', mul_smul]
    abel

open Alignment in
private lemma scs1_fine_mem (τ : Substitution P) (G : GroupedFamily P)
    (m : ℕ) (T' : PlaneTiling G.P') (A : PlacedTile G.P')
    (hA : A ∈ T'.tiles) (B : PlacedTile P) (hB : B ∈ fineTiles τ G m A.form) :
    B.translate ((τ.θ ^ m) • A.anchor) ∈ τ.decomposeIter m (G.scatter T'.tiles) := by
  apply scs1_decomposeIter_mono τ m (S := G.scatterTile A)
  · intro C hC
    exact Set.mem_biUnion hA hC
  · exact scs1_decomposeIter_translate τ m A.anchor _ B hB

open Alignment in
private lemma scs1_support_translateSet (v : Pt) (S : Set (PlacedTile P)) :
    support (translateSet v S) = v +ᵥ support S := by
  ext x
  simp only [support, translateSet, PlacedTile.translate, PlacedTile.carrier,
    Set.mem_iUnion, Set.mem_image, Set.mem_vadd_set_iff_neg_vadd_mem]
  constructor
  · rintro ⟨A, ⟨B, hB, rfl⟩, hx⟩
    exact ⟨B, hB, by simpa [← add_assoc] using hx⟩
  · rintro ⟨A, hA, hx⟩
    refine ⟨⟨A.form, v +ᵥ A.anchor⟩, ⟨A, hA, rfl⟩, ?_⟩
    simpa [← add_assoc] using hx

open Alignment in
private lemma scs1_support_decomposeTile (τ : Substitution P) (A : PlacedTile P) :
    support (τ.decomposeTile A) = τ.θ • A.carrier := by
  dsimp [Substitution.decomposeTile]
  rw [scs1_support_translateSet, τ.support_eq, PlacedTile.carrier]
  ext x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, hx⟩
    refine ⟨A.anchor + y, ?_, ?_⟩
    · simpa
    · rw [smul_add]
      calc
        τ.θ • A.anchor + τ.θ • y =
            τ.θ • A.anchor + (-(τ.θ • A.anchor) + x) := by congr 1
        _ = x := by abel
  · rintro ⟨y, hy, rfl⟩
    refine ⟨-A.anchor + y, ?_, ?_⟩
    · simpa
    · simp [smul_add]

open Alignment in
private lemma scs1_support_decompose (τ : Substitution P) (S : Set (PlacedTile P)) :
    support (τ.decompose S) = τ.θ • support S := by
  dsimp [Substitution.decompose, support]
  rw [Set.smul_set_iUnion₂]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨A, ⟨B, hB, hA⟩, hx⟩
    refine ⟨B, hB, ?_⟩
    have h : x ∈ support (τ.decomposeTile B) := by
      simp only [support, Set.mem_iUnion]
      exact ⟨A, hA, hx⟩
    rwa [scs1_support_decomposeTile] at h
  · rintro ⟨A, hA, hx⟩
    have h : x ∈ support (τ.decomposeTile A) := by
      rwa [scs1_support_decomposeTile]
    simp only [support, Set.mem_iUnion] at h
    rcases h with ⟨B, hB, hxB⟩
    exact ⟨B, ⟨A, hA, hB⟩, hxB⟩

open Alignment in
private lemma scs1_fineTiles_support (τ : Substitution P) (G : GroupedFamily P)
    (m : ℕ) (A : G.P'.Form) :
    support (fineTiles τ G m A) = parentRegion τ G m A := by
  induction m with
  | zero => simpa [fineTiles, parentRegion, Substitution.decomposeIter] using G.support_eq A
  | succ m ih =>
      change support (τ.decompose (τ.decomposeIter m (G.dissect A).tiles)) = _
      rw [scs1_support_decompose]
      change support (τ.decomposeIter m (G.dissect A).tiles) = _ at ih
      rw [ih, parentRegion, parentRegion, smul_smul, pow_succ']

open Alignment in
private lemma scs1_fineTiles_finite (τ : Substitution P) (G : GroupedFamily P)
    (m : ℕ) (A : G.P'.Form) : (fineTiles τ G m A).Finite := by
  unfold fineTiles
  have key : ∀ n (S : Set (PlacedTile P)), S.Finite → (τ.decomposeIter n S).Finite := by
    intro n S hS
    induction n with
    | zero => exact hS
    | succ n ih =>
      change (τ.decompose (τ.decomposeIter n S)).Finite
      exact ih.biUnion fun B _ => (τ.rule B.form).finite.image _
  exact key m _ (G.dissect A).finite

open Alignment in
private lemma scs1_region_closed (τ : Substitution P) (G : GroupedFamily P)
    (m : ℕ) (A : G.P'.Form) : IsClosed (parentRegion τ G m A) :=
  ((G.P'.disk A).compact.smul (τ.θ ^ m)).isClosed

open Alignment in
private lemma scs1_region_eq (τ : Substitution P) (G : GroupedFamily P)
    (m : ℕ) (A : PlacedTile G.P') :
    ((τ.θ ^ m) • A.anchor) +ᵥ parentRegion τ G m A.form = (τ.θ ^ m) • A.carrier := by
  simp only [parentRegion, PlacedTile.carrier, ← Set.image_vadd, ← Set.image_smul, Set.image_image,
    vadd_eq_add, smul_add]

open Alignment in
private lemma scs1_frontier_cover (τ : Substitution P) (G : GroupedFamily P)
    (m : ℕ) (α : G.P'.Form) (a : Pt) :
    frontier (a +ᵥ parentRegion τ G m α) ⊆ ⋃₀ {T | ∃ B ∈ fineTiles τ G m α,
      ∃ i : Fin (P.disk B.form).n, T = placedSeg a (B.vertex i, B.vertex (finRotate _ i))} := by
  intro z hz
  rw [scs1_frontier_vadd, Set.mem_vadd_set] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hwR : w ∈ parentRegion τ G m α := (scs1_region_closed τ G m α).frontier_subset hw
  rw [← scs1_fineTiles_support] at hwR
  simp only [support, Set.mem_iUnion] at hwR
  obtain ⟨B, hB, hwB⟩ := hwR
  have hBR : B.carrier ⊆ parentRegion τ G m α := by
    rw [← scs1_fineTiles_support]
    exact Set.subset_biUnion_of_mem (u := fun B => B.carrier) hB
  have hwF : w ∈ frontier B.carrier := ⟨subset_closure hwB, fun h => hw.2 (interior_mono hBR h)⟩
  rw [scs1_frontier_carrier, Set.mem_iUnion] at hwF
  obtain ⟨i, hi⟩ := hwF
  refine ⟨_, ⟨B, hB, i, rfl⟩, ?_⟩
  rw [scs1_placedSeg_eq, ← scs1_tile_side_eq]
  exact Set.vadd_mem_vadd_set hi

open Alignment in
private lemma scs1_cover_finite (τ : Substitution P) (G : GroupedFamily P)
    (m : ℕ) (α : G.P'.Form) (a : Pt) :
    {T | ∃ B ∈ fineTiles τ G m α, ∃ i : Fin (P.disk B.form).n,
      T = placedSeg a (B.vertex i, B.vertex (finRotate _ i))}.Finite := by
  refine Set.Finite.subset ((scs1_fineTiles_finite τ G m α).biUnion fun B _ =>
    Set.finite_range (fun i : Fin (P.disk B.form).n =>
      placedSeg a (B.vertex i, B.vertex (finRotate _ i)))) ?_
  rintro T ⟨B, hB, i, rfl⟩
  exact Set.mem_biUnion hB ⟨i, rfl⟩

open Alignment in
private lemma scs1_placed_side_sub (τ : Substitution P) (G : GroupedFamily P)
    (m : ℕ) (α : G.P'.Form) (a : Pt) (B : PlacedTile P)
    (hB : B ∈ fineTiles τ G m α) (i : Fin (P.disk B.form).n) :
    placedSeg a (B.vertex i, B.vertex (finRotate _ i)) ⊆
      closure (interior (a +ᵥ parentRegion τ G m α)) := by
  rw [← scs1_translate_side]
  refine (scs1_side_subset_carrier (B.translate a) i).trans ?_
  rw [← scs1_closure_interior_carrier]
  refine closure_mono (interior_mono ?_)
  rw [scs1_translate_carrier]
  apply Set.vadd_set_mono
  rw [← scs1_fineTiles_support]
  exact Set.subset_biUnion_of_mem (u := fun B => B.carrier) hB

open Alignment in
private lemma scs1_outer (τ : Substitution P) (G : GroupedFamily P)
    (m : ℕ) (α : G.P'.Form) (a : Pt) (B : PlacedTile P)
    (hB : B ∈ fineTiles τ G m α) (i : Fin (P.disk B.form).n) (X : Set Pt)
    (hX : placedSeg a (B.vertex i, B.vertex (finRotate _ i)) ⊆ closure (interior X))
    (hdisj : Disjoint (interior (a +ᵥ parentRegion τ G m α)) (interior X)) :
    segment ℝ (B.vertex i) (B.vertex (finRotate _ i)) ⊆ frontier (parentRegion τ G m α) := by
  intro w hw
  have hwR : w ∈ parentRegion τ G m α := by
    rw [← scs1_fineTiles_support]
    exact Set.mem_biUnion hB (scs1_side_subset_carrier B i (by rwa [scs1_tile_side_eq]))
  refine ⟨subset_closure hwR, fun hint => ?_⟩
  have h1 : a +ᵥ w ∈ interior (a +ᵥ parentRegion τ G m α) := by
    rw [interior_vadd]
    exact Set.vadd_mem_vadd_set hint
  have h2 : a +ᵥ w ∈ closure (interior X) := hX (by
    rw [scs1_placedSeg_eq]
    exact Set.vadd_mem_vadd_set hw)
  rw [mem_closure_iff] at h2
  obtain ⟨q, hq1, hq2⟩ := h2 _ isOpen_interior h1
  exact Set.disjoint_left.mp hdisj hq1 hq2

open Alignment in
private lemma scs1_disj (τ : Substitution P) (G : GroupedFamily P)
    (m : ℕ) (T' : PlaneTiling G.P') (A A'' : PlacedTile G.P')
    (hA : A ∈ T'.tiles) (hA'' : A'' ∈ T'.tiles) (hne : A ≠ A'') :
    Disjoint (interior (((τ.θ ^ m) • A.anchor) +ᵥ parentRegion τ G m A.form))
      (interior (((τ.θ ^ m) • A''.anchor) +ᵥ parentRegion τ G m A''.form)) := by
  have hs : τ.θ ^ m ≠ 0 := pow_ne_zero _ (by linarith [τ.one_lt])
  rw [scs1_region_eq, scs1_region_eq, interior_smul₀ hs, interior_smul₀ hs]
  exact (Set.disjoint_image_iff (smul_right_injective Pt hs)).mpr (T'.disjoint hA hA'' hne)

open Alignment in
private lemma scs1_overlap_of_placed {w : Pt} {p q : Pt × Pt} {u v : Pt} (huv : u ≠ v)
    (h : segment ℝ u v ⊆ placedSeg w p ∩ placedSeg w q) :
    OverlapPos (segment ℝ p.1 p.2) (segment ℝ q.1 q.2) := by
  refine ⟨-w +ᵥ u, -w +ᵥ v, fun h' => huv (vadd_left_cancel _ h'), ?_⟩
  rw [← vadd_segment]
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨h1, h2⟩ := h hz
  rw [scs1_placedSeg_eq] at h1 h2
  obtain ⟨z1, hz1, rfl⟩ := h1
  obtain ⟨z2, hz2, he⟩ := h2
  refine ⟨by simpa using hz1, ?_⟩
  have : z2 = z1 := vadd_left_cancel _ he
  subst this
  simpa using hz2

private lemma scs1_smul_segment (r : ℝ) (p p' : Pt) :
    segment ℝ (r • p) (r • p') = r • segment ℝ p p' := by
  let f : Pt →ᵃ[ℝ] Pt := (LinearMap.lsmul ℝ Pt r).toAffineMap
  exact (image_segment ℝ f p p').symm

open Alignment in
private lemma scs1_placedSeg_smul (r q : ℝ) (v p p' : Pt) :
    placedSeg ((r * q) • v) (r • p, r • p') = r • placedSeg (q • v) (p, p') := by
  simp only [placedSeg]
  rw [← scs1_smul_segment, mul_smul, smul_add, smul_add]

private lemma scs1_overlap_unscale {s : ℝ} (hs : s ≠ 0) {u v : Pt} (huv : u ≠ v) {X Y : Set Pt}
    (h : segment ℝ u v ⊆ s • X ∩ s • Y) : OverlapPos X Y := by
  refine ⟨s⁻¹ • u, s⁻¹ • v, fun h' => huv (smul_right_injective Pt (inv_ne_zero hs) h'), ?_⟩
  rw [scs1_smul_segment]
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨hwX, hwY⟩ := h hw
  obtain ⟨a, ha, rfl⟩ := Set.mem_smul_set.mp hwX
  obtain ⟨b, hb, hab⟩ := Set.mem_smul_set.mp hwY
  have : b = a := smul_right_injective Pt hs hab
  subst this
  show s⁻¹ • s • _ ∈ X ∩ Y
  rw [inv_smul_smul₀ hs]
  exact ⟨ha, hb⟩

open Alignment in
private lemma scs1_overlap_placed (w : Pt) {c e : Pt × Pt}
    (h : OverlapPos (segment ℝ c.1 c.2) (segment ℝ e.1 e.2)) :
    ∃ x y : Pt, x ≠ y ∧ segment ℝ x y ⊆ placedSeg w c ∩ placedSeg w e := by
  obtain ⟨x, y, hxy, hsub⟩ := h
  refine ⟨w +ᵥ x, w +ᵥ y, fun h' => hxy (vadd_left_cancel _ h'), ?_⟩
  rw [scs1_placedSeg_eq, scs1_placedSeg_eq, ← Set.vadd_set_inter, ← vadd_segment]
  exact Set.vadd_set_mono hsub

open Alignment in
private lemma scs1_region_scale (τ : Substitution P) (G : GroupedFamily P) (m j : ℕ) (r q : ℝ)
    (hrq : τ.θ ^ m = r * q) (hq : q = τ.θ ^ j) (α : G.P'.Form) (a : Pt) :
    ((τ.θ ^ m) • a) +ᵥ parentRegion τ G m α = r • ((q • a) +ᵥ parentRegion τ G j α) := by
  simp only [parentRegion, ← Set.image_vadd, ← Set.image_smul, Set.image_image]
  rw [hrq, ← hq]
  congr 1
  funext z
  simp only [vadd_eq_add, smul_add, mul_smul]

open Alignment in
private lemma scs1_region_scale' (τ : Substitution P) (G : GroupedFamily P) (m j : ℕ) (r q : ℝ)
    (hrq : τ.θ ^ m = r * q) (hq : q = τ.θ ^ j) (α : G.P'.Form) :
    parentRegion τ G m α = r • parentRegion τ G j α := by
  simp only [parentRegion]
  rw [hrq, ← hq, mul_smul]

open Alignment in
private lemma scs1_top_side (G : GroupedFamily P) (T' : PlaneTiling G.P') (hT' : T'.SideToSide)
    (s : ℝ) (hs : s ≠ 0) (A A' : PlacedTile G.P') (hA : A ∈ T'.tiles) (hA' : A' ∈ T'.tiles)
    (k0 : Fin (G.P'.disk A.form).n) (x y : Pt) (hxy : x ≠ y)
    (hc : segment ℝ x y ⊆ placedSeg (s • A.anchor)
      (s • (G.P'.disk A.form).vertex k0, s • (G.P'.disk A.form).vertex (finRotate _ k0)))
    (hfr : segment ℝ x y ⊆ frontier (s • A'.carrier)) :
    ∃ k : Fin (G.P'.disk A'.form).n,
      placedSeg (s • A.anchor)
          (s • (G.P'.disk A.form).vertex k0, s • (G.P'.disk A.form).vertex (finRotate _ k0)) =
        placedSeg (s • A'.anchor)
          (s • (G.P'.disk A'.form).vertex k, s • (G.P'.disk A'.form).vertex (finRotate _ k)) := by
  have key : ∀ (X : PlacedTile G.P') (k : Fin (G.P'.disk X.form).n),
      placedSeg (s • X.anchor) (s • (G.P'.disk X.form).vertex k,
        s • (G.P'.disk X.form).vertex (finRotate _ k)) = s • X.side k := by
    intro X k
    have h := scs1_placedSeg_smul s 1 X.anchor ((G.P'.disk X.form).vertex k)
      ((G.P'.disk X.form).vertex (finRotate _ k))
    rw [mul_one, one_smul] at h
    rw [h, scs1_tile_side_eq]
    rfl
  rw [key] at hc
  rw [scs1_frontier_smul hs, scs1_frontier_carrier, Set.smul_set_iUnion] at hfr
  obtain ⟨_, ⟨k, rfl⟩, u, v, huv, hsub⟩ := scs1_cover hxy (S := Set.range fun k => s • A'.side k)
    (Set.finite_range _) (by rintro _ ⟨k, rfl⟩; show Convex ℝ (s • A'.side k); rw [scs1_tile_side_eq]; exact (convex_segment _ _).smul s)
    (by rw [Set.sUnion_range]; exact hfr)
  refine ⟨k, ?_⟩
  rw [key, key, hT' A hA A' hA' k0 k (scs1_overlap_unscale hs huv fun z hz => ⟨hc (hsub hz).1, (hsub hz).2⟩)]

open Alignment in
private lemma scs1_level_side (τ : Substitution P) (G : GroupedFamily P) (m j : ℕ) (hj : j ≤ m)
    (T' : PlaneTiling G.P') (hlev : SideToSideSet (τ.decomposeIter j (G.scatter T'.tiles)))
    (A A' : PlacedTile G.P') (hA : A ∈ T'.tiles) (hA' : A' ∈ T'.tiles) (hne : A ≠ A')
    (B : PlacedTile P) (hB : B ∈ τ.decomposeIter j (G.dissect A.form).tiles)
    (i : Fin (P.disk B.form).n) (x y : Pt) (hxy : x ≠ y)
    (hc : segment ℝ x y ⊆ placedSeg ((τ.θ ^ m) • A.anchor)
      ((τ.θ ^ (m - j)) • B.vertex i, (τ.θ ^ (m - j)) • B.vertex (finRotate _ i)))
    (hfr : segment ℝ x y ⊆ frontier (((τ.θ ^ m) • A'.anchor) +ᵥ parentRegion τ G m A'.form)) :
    ∃ B' ∈ τ.decomposeIter j (G.dissect A'.form).tiles, ∃ k : Fin (P.disk B'.form).n,
      placedSeg ((τ.θ ^ m) • A.anchor)
          ((τ.θ ^ (m - j)) • B.vertex i, (τ.θ ^ (m - j)) • B.vertex (finRotate _ i)) =
        placedSeg ((τ.θ ^ m) • A'.anchor)
          ((τ.θ ^ (m - j)) • B'.vertex k, (τ.θ ^ (m - j)) • B'.vertex (finRotate _ k)) ∧
      segment ℝ ((τ.θ ^ (m - j)) • B'.vertex k) ((τ.θ ^ (m - j)) • B'.vertex (finRotate _ k)) ⊆
        frontier (parentRegion τ G m A'.form) := by
  have hθ : τ.θ ≠ 0 := by linarith [τ.one_lt]
  have hr0 : τ.θ ^ (m - j) ≠ 0 := pow_ne_zero _ hθ
  have hsrq : τ.θ ^ m = τ.θ ^ (m - j) * τ.θ ^ j := by rw [← pow_add, Nat.sub_add_cancel hj]
  rw [scs1_region_scale τ G m j _ _ hsrq rfl, scs1_frontier_smul hr0] at hfr
  rw [hsrq, scs1_placedSeg_smul] at hc
  have hcov : segment ℝ x y ⊆ ⋃₀ ((fun S => τ.θ ^ (m - j) • S) '' {T | ∃ B' ∈ fineTiles τ G j A'.form,
      ∃ k : Fin (P.disk B'.form).n, T = placedSeg (τ.θ ^ j • A'.anchor) (B'.vertex k, B'.vertex (finRotate _ k))}) := by
    refine hfr.trans ?_
    rw [Set.sUnion_image]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨S, hS, hzS⟩ := scs1_frontier_cover τ G j A'.form _ hz
    exact Set.mem_biUnion hS (Set.smul_mem_smul_set hzS)
  obtain ⟨_, ⟨S, ⟨B', hB', k, rfl⟩, rfl⟩, u, v, huv, hsub⟩ := scs1_cover hxy
    ((scs1_cover_finite τ G j A'.form _).image _)
    (by rintro _ ⟨S, ⟨B', -, k, rfl⟩, rfl⟩; exact (convex_segment _ _).smul _) hcov
  have hov : OverlapPos ((B.translate (τ.θ ^ j • A.anchor)).side i)
      ((B'.translate (τ.θ ^ j • A'.anchor)).side k) := by
    rw [scs1_translate_side, scs1_translate_side]
    exact scs1_overlap_unscale hr0 huv (fun z hz => ⟨hc (hsub hz).1, (hsub hz).2⟩)
  have hE := hlev _ (scs1_fine_mem τ G j T' A hA B hB) _ (scs1_fine_mem τ G j T' A' hA' B' hB') i k hov
  rw [scs1_translate_side, scs1_translate_side] at hE
  refine ⟨B', hB', k, ?_, ?_⟩
  · rw [hsrq, scs1_placedSeg_smul, scs1_placedSeg_smul, hE]
  · have h1 := scs1_outer τ G j A'.form (τ.θ ^ j • A'.anchor) B' hB' k _
      (by rw [← hE]; exact scs1_placed_side_sub τ G j A.form _ B hB i)
      (scs1_disj τ G j T' A A' hA hA' hne).symm
    rw [scs1_smul_segment, scs1_region_scale' τ G m j _ _ hsrq rfl, scs1_frontier_smul hr0]
    exact Set.smul_set_mono h1

/-- Step 1 of the blueprint proof of `strict_actual_schedules_aligned`: at a
shared whole fine side, a positively overlapping boundary side in one layer
has the single neighbouring boundary side in the other parent. -/
private theorem strict_actual_schedules_aligned_step1_crossing_side
    (T' : PlaneTiling C.Q) (hT' : T'.SideToSide)
    (hlev : ∀ j ≤ m,
      SideToSideSet (τ.decomposeIter j (hC.groupedFamily.scatter T'.tiles)))
    (A A' : PlacedTile C.Q) (hA : A ∈ T'.tiles) (hA' : A' ∈ T'.tiles)
    (e e' : Pt × Pt)
    (he : e ∈ Alignment.fineOuterSides τ hC.groupedFamily m A.form)
    (he' : e' ∈ Alignment.fineOuterSides τ hC.groupedFamily m A'.form)
    (heq : Alignment.placedSeg ((τ.θ ^ m) • A.anchor) e =
      Alignment.placedSeg ((τ.θ ^ m) • A'.anchor) e')
    (t : Alignment.LayerTag m) (c : Pt × Pt)
    (hc : c ∈ Alignment.layerSides τ hC.groupedFamily m A.form t)
    (hov : OverlapPos (segment ℝ c.1 c.2) (segment ℝ e.1 e.2)) :
    ∃ d, d ∈ Alignment.layerSides τ hC.groupedFamily m A'.form t ∧
      OverlapPos (segment ℝ d.1 d.2) (segment ℝ e'.1 e'.2) ∧
      Alignment.placedSeg ((τ.θ ^ m) • A.anchor) c =
        Alignment.placedSeg ((τ.θ ^ m) • A'.anchor) d := by
  have _ := he
  have hs : τ.θ ^ m ≠ 0 := pow_ne_zero _ (by linarith [τ.one_lt])
  obtain ⟨x, y, hxy, hxyI⟩ := scs1_overlap_placed ((τ.θ ^ m) • A.anchor) hov
  have hX : segment ℝ x y ⊆
      frontier (((τ.θ ^ m) • A'.anchor) +ᵥ Alignment.parentRegion τ hC.groupedFamily m A'.form) := by
    obtain ⟨B, -, i, rfl, hsub⟩ := he'
    intro z hz
    have h1 := (hxyI hz).2
    rw [heq, scs1_placedSeg_eq] at h1
    rw [scs1_frontier_vadd]
    exact Set.vadd_set_mono hsub h1
  have hfin : ∀ d, Alignment.placedSeg ((τ.θ ^ m) • A.anchor) c =
      Alignment.placedSeg ((τ.θ ^ m) • A'.anchor) d →
      OverlapPos (segment ℝ d.1 d.2) (segment ℝ e'.1 e'.2) := fun d hcd =>
    scs1_overlap_of_placed hxy fun z hz => ⟨hcd ▸ (hxyI hz).1, heq ▸ (hxyI hz).2⟩
  by_cases hAA : A = A'
  · subst hAA
    exact ⟨c, hc, hfin c rfl, rfl⟩
  cases t with
  | top =>
    obtain ⟨k0, rfl⟩ := hc
    obtain ⟨k, hk⟩ := scs1_top_side hC.groupedFamily T' hT' _ hs A A' hA hA' k0 x y hxy
      (fun z hz => (hxyI hz).1) (by rw [← scs1_region_eq τ hC.groupedFamily m A']; exact hX)
    exact ⟨_, ⟨k, rfl⟩, hfin _ hk, hk⟩
  | level j =>
    obtain ⟨B, hB, i, rfl, -⟩ := hc
    obtain ⟨B', hB', k, hk, hfr⟩ := scs1_level_side τ hC.groupedFamily m j j.isLt.le T'
      (hlev j j.isLt.le) A A' hA hA' hAA B hB i x y hxy (fun z hz => (hxyI hz).1) hX
    exact ⟨_, ⟨B', hB', k, rfl, hfr⟩, hfin _ hk, hk⟩

/-- Step 2 of the blueprint proof of `strict_actual_schedules_aligned`: once
the two layer sides and the two fine sides are physically coincident, their
positive overlaps have equal endpoint coordinates in the common frame. -/
private theorem strict_actual_schedules_aligned_step2_atom_eq
    (A A' : PlacedTile C.Q) (e e' c d : Pt × Pt)
    (heq : Alignment.placedSeg ((τ.θ ^ m) • A.anchor) e =
      Alignment.placedSeg ((τ.θ ^ m) • A'.anchor) e')
    (hcd : Alignment.placedSeg ((τ.θ ^ m) • A.anchor) c =
      Alignment.placedSeg ((τ.θ ^ m) • A'.anchor) d)
    (hov : OverlapPos (segment ℝ c.1 c.2) (segment ℝ e.1 e.2))
    (hov' : OverlapPos (segment ℝ d.1 d.2) (segment ℝ e'.1 e'.2)) :
    Alignment.atom e c = Alignment.atom e' d := by
  have _ := hov
  let va : Pt := (τ.θ ^ m) • A.anchor
  let vb : Pt := (τ.θ ^ m) • A'.anchor
  have overlap_right_ne : ∀ {a b c d : Pt},
      OverlapPos (segment ℝ a b) (segment ℝ c d) → c ≠ d := by
    intro a b c d h hcd
    obtain ⟨x, y, hxy, hsub⟩ := h
    subst d
    have hx : x = c := by
      have hx' := (hsub (left_mem_segment ℝ x y)).2
      simpa only [segment_same, mem_singleton_iff] using hx'
    have hy : y = c := by
      have hy' := (hsub (right_mem_segment ℝ x y)).2
      simpa only [segment_same, mem_singleton_iff] using hy'
    exact hxy (hx.trans hy.symm)
  have he'_ne : e'.1 ≠ e'.2 := overlap_right_ne hov'
  have hends :
      (va + e.1 = vb + e'.1 ∧ va + e.2 = vb + e'.2) ∨
        (va + e.1 = vb + e'.2 ∧ va + e.2 = vb + e'.1) := by
    apply som_segment_endpoints
    simpa only [Alignment.placedSeg, va, vb] using heq
  have hcd_ends :
      (va + c.1 = vb + d.1 ∧ va + c.2 = vb + d.2) ∨
        (va + c.1 = vb + d.2 ∧ va + c.2 = vb + d.1) := by
    apply som_segment_endpoints
    simpa only [Alignment.placedSeg, va, vb] using hcd
  have hrel : ∀ z : Pt,
      Alignment.segCoord e.1 e.2 z =
        Alignment.segCoord e'.1 e'.2 (z + (va - vb)) := by
    intro z
    have hz : va + z = vb + (z + (va - vb)) := by abel
    rw [← som_segCoord_translate e.1 e.2 z va]
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2, hz, som_segCoord_translate]
    · rw [h1, h2, hz, som_segCoord_translate,
      som_segCoord_swap e'.1 e'.2 _ he'_ne]
  have hshift : ∀ {x y : Pt}, va + x = vb + y → x + (va - vb) = y := by
    intro x y h
    calc
      x + (va - vb) = (va + x) - vb := by abel
      _ = (vb + y) - vb := by rw [h]
      _ = y := by abel
  have hpair :
      (Alignment.segCoord e.1 e.2 c.1 = Alignment.segCoord e'.1 e'.2 d.1 ∧
        Alignment.segCoord e.1 e.2 c.2 = Alignment.segCoord e'.1 e'.2 d.2) ∨
      (Alignment.segCoord e.1 e.2 c.1 = Alignment.segCoord e'.1 e'.2 d.2 ∧
        Alignment.segCoord e.1 e.2 c.2 = Alignment.segCoord e'.1 e'.2 d.1) := by
    rcases hcd_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      constructor
      · rw [hrel c.1, hshift h1]
      · rw [hrel c.2, hshift h2]
    · right
      constructor
      · rw [hrel c.1, hshift h1]
      · rw [hrel c.2, hshift h2]
  have hp :
      min (Alignment.segCoord e.1 e.2 c.1) (Alignment.segCoord e.1 e.2 c.2) =
        min (Alignment.segCoord e'.1 e'.2 d.1) (Alignment.segCoord e'.1 e'.2 d.2) := by
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, min_comm]
  have hq :
      max (Alignment.segCoord e.1 e.2 c.1) (Alignment.segCoord e.1 e.2 c.2) =
        max (Alignment.segCoord e'.1 e'.2 d.1) (Alignment.segCoord e'.1 e'.2 d.2) := by
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, max_comm]
  have hdist : dist e.1 e.2 = dist e'.1 e'.2 := by
    have hdist_translate : ∀ (v x y : Pt), dist (v + x) (v + y) = dist x y := by
      intro v x y
      rw [dist_eq_norm_vsub, dist_eq_norm_vsub]
      congr 1
      simp only [vsub_eq_sub]
      abel
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · calc
        dist e.1 e.2 = dist (va + e.1) (va + e.2) := (hdist_translate va _ _).symm
        _ = dist (vb + e'.1) (vb + e'.2) := by rw [h1, h2]
        _ = dist e'.1 e'.2 := hdist_translate vb _ _
    · calc
        dist e.1 e.2 = dist (va + e.1) (va + e.2) := (hdist_translate va _ _).symm
        _ = dist (vb + e'.2) (vb + e'.1) := by rw [h1, h2]
        _ = dist e'.1 e'.2 := by rw [dist_comm]; exact hdist_translate vb _ _
  simp only [Alignment.atom]
  rw [hp, hq, hdist]

/-- `lem:strict-presentation` (completeness, schedules): in an actual grouped level `T'` that is
side-to-side and whose scattered intermediate original levels `τ^j Δ T'`, `j ≤ m`, are
side-to-side, coincident whole fine outer sides of two parents carry equal schedules (a
layer-`j` side on the boundary of `sA` faces a single layer-`j` tile, which lies in the
neighbouring block). -/
theorem strict_actual_schedules_aligned (T' : PlaneTiling C.Q) (hT' : T'.SideToSide)
    (hlev : ∀ j ≤ m, SideToSideSet (τ.decomposeIter j (hC.groupedFamily.scatter T'.tiles))) :
    Alignment.SchedulesAligned τ hC.groupedFamily m T' := by
  intro A hA A' hA' e he e' he' heq
  funext t
  ext r
  constructor
  · intro hr
    rcases hr with ⟨c, hc, hov, rfl⟩
    obtain ⟨d, hd, hov', hcd⟩ := strict_actual_schedules_aligned_step1_crossing_side C hC T'
      hT' hlev A A' hA hA' e e' he he' heq t c hc hov
    have hat := strict_actual_schedules_aligned_step2_atom_eq C A A' e e' c d heq hcd hov hov'
    exact ⟨d, hd, hov', hat⟩
  · intro hr
    rcases hr with ⟨d, hd, hov', rfl⟩
    obtain ⟨c, hc, hov, hcd⟩ := strict_actual_schedules_aligned_step1_crossing_side C hC T'
      hT' hlev A' A hA' hA e' e he' he heq.symm t d hd hov'
    have hat := strict_actual_schedules_aligned_step2_atom_eq C A' A e' e d c heq.symm hcd hov' hov
    exact ⟨c, hc, hov, hat⟩

private structure StrictTypeChain (C : MacroCertificate P) where
  X : ℕ → Type
  par : ∀ n, X n → X (n + 1)
  typ : ∀ n, X n → C.Typ
  adm : ∀ n x, C.owner (typ n x) = C.form (typ (n + 1) (par n x))

private def stcState {C : MacroCertificate P} (H : StrictTypeChain C) :=
  Σ n, Σ x : H.X n, C.Side (H.typ n x) × Fin 5

open Classical in
private def stcSource {C : MacroCertificate P} (H : StrictTypeChain C) (n : ℕ) (x : H.X n)
    (i : C.Side (H.typ n x)) (k : Fin 5) :
    Option (C.Side (H.typ (n + 1) (H.par n x)) × Fin 5) :=
  if h : (copySource C (C.form (H.typ (n + 1) (H.par n x)))
      (C.occ (H.typ n x) i) k).Nonempty then some h.some else none

private def stcStep {C : MacroCertificate P} (H : StrictTypeChain C) : stcState H → Option (stcState H)
  | ⟨n, x, i, k⟩ => (stcSource H n x i k).map fun p =>
      ⟨n + 1, H.par n x, p.1, p.2⟩

private def stcIter {C : MacroCertificate P} (H : StrictTypeChain C) : ℕ → stcState H → Option (stcState H)
  | 0, s => some s
  | j + 1, s => (stcStep H s).bind (stcIter H j)

private lemma stcIter_add {C : MacroCertificate P} (H : StrictTypeChain C)
    (j l : ℕ) (s : stcState H) :
    stcIter H (j + l) s = (stcIter H j s).bind (stcIter H l) := by
  induction j generalizing s with
  | zero => simp [stcIter]
  | succ j ih =>
    rw [show j + 1 + l = (j + l) + 1 by omega]
    simp only [stcIter, ih, Option.bind_assoc]

private lemma stcIter_origin_unique {C : MacroCertificate P} (H : StrictTypeChain C) {j j' : ℕ}
    {s a b : stcState H} (ha : stcIter H j s = some a) (ha' : stcStep H a = none)
    (hb : stcIter H j' s = some b) (hb' : stcStep H b = none) : a = b := by
  have key : ∀ {u v : ℕ} {a b : stcState H}, u ≤ v → stcIter H u s = some a →
      stcStep H a = none → stcIter H v s = some b → a = b := by
    intro u v a b huv hua hstop hub
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le huv
    rw [stcIter_add, hua] at hub
    cases l with
    | zero => simpa [stcIter] using hub
    | succ l => simp [stcIter, hstop] at hub
  rcases le_total j j' with h | h
  · exact key h ha ha' hb
  · exact (key h hb hb' ha).symm

private def stcTerminates {C : MacroCertificate P} (H : StrictTypeChain C) (s : stcState H) : Prop :=
  ∃ j a, stcIter H j s = some a ∧ stcStep H a = none

private def stcHeader (C : MacroCertificate P) (hC : C.Represents τ m)
    (H : StrictTypeChain C) (n : ℕ) (x : H.X n) : SU C hC :=
  headerSU C hC ⟨H.typ (n + 1) (H.par n x), fun _ => false⟩

private def stcOrigin (C : MacroCertificate P) (hC : C.Represents τ m)
    (H : StrictTypeChain C) : stcState H → SU C hC
  | ⟨n, x, i, k⟩ => strictGenCell C hC (C.form (H.typ (n + 1) (H.par n x)))
      (stcHeader C hC H n x) (C.occ (H.typ n x) i) k

open Classical in
private def stcValue (C : MacroCertificate P) (hC : C.Represents τ m)
    (H : StrictTypeChain C) (s : stcState H) : SU C hC :=
  if h : stcTerminates H s then stcOrigin C hC H h.choose_spec.choose else 0

private lemma stcValue_stop {C : MacroCertificate P} {τ : Substitution P} {m : ℕ}
    {hC : C.Represents τ m} (H : StrictTypeChain C) (s : stcState H)
    (hs : stcStep H s = none) :
    stcValue C hC H s = stcOrigin C hC H s := by
  have h : stcTerminates H s := ⟨0, s, rfl, hs⟩
  unfold stcValue
  rw [dif_pos h]
  congr 1
  exact stcIter_origin_unique H (j' := 0) h.choose_spec.choose_spec.1
    h.choose_spec.choose_spec.2 rfl hs

private lemma stcValue_step {C : MacroCertificate P} {τ : Substitution P} {m : ℕ}
    {hC : C.Represents τ m} (H : StrictTypeChain C) (s s' : stcState H)
    (hs : stcStep H s = some s') : stcValue C hC H s = stcValue C hC H s' := by
  have hiff : stcTerminates H s ↔ stcTerminates H s' := by
    constructor
    · rintro ⟨j, a, ha, ha'⟩
      cases j with
      | zero =>
        simp only [stcIter, Option.some.injEq] at ha
        subst ha
        rw [hs] at ha'
        cases ha'
      | succ j => exact ⟨j, a, by simpa [stcIter, hs] using ha, ha'⟩
    · rintro ⟨j, a, ha, ha'⟩
      exact ⟨j + 1, a, by simpa [stcIter, hs] using ha, ha'⟩
  unfold stcValue
  by_cases h : stcTerminates H s
  · have h' := hiff.1 h
    rw [dif_pos h, dif_pos h']
    congr 1
    apply stcIter_origin_unique H (j := h.choose + 0) (s := s)
    · simpa using h.choose_spec.choose_spec.1
    · exact h.choose_spec.choose_spec.2
    · show stcIter H (h'.choose + 1) s = _
      simpa [stcIter, hs] using h'.choose_spec.choose_spec.1
    · exact h'.choose_spec.choose_spec.2
  · rw [dif_neg h, dif_neg (fun h' => h (hiff.2 h'))]

private def stcTile (C : MacroCertificate P) (hC : C.Represents τ m)
    (H : StrictTypeChain C) (n : ℕ) (x : H.X n) : StrictDecTile C hC :=
  ⟨H.typ n x, fun i k => stcValue C hC H ⟨n, x, i, k⟩⟩

private lemma stcTile_copy {C : MacroCertificate P} {τ : Substitution P} {m : ℕ}
    {hC : C.Represents τ m} (H : StrictTypeChain C) (n : ℕ) (x : H.X n)
    (i : C.Side (H.typ n x)) (k : Fin 5)
    (hne : (copySource C (C.form (H.typ (n + 1) (H.par n x)))
      (C.occ (H.typ n x) i) k).Nonempty) :
    (stcTile C hC H n x).cell i k =
      (stcTile C hC H (n + 1) (H.par n x)).cell hne.some.1 hne.some.2 := by
  apply stcValue_step
  simp [stcStep, stcSource, hne]

private lemma stcTile_origin {C : MacroCertificate P} {τ : Substitution P} {m : ℕ}
    {hC : C.Represents τ m} (H : StrictTypeChain C) (n : ℕ) (x : H.X n)
    (i : C.Side (H.typ n x)) (k : Fin 5)
    (hempty : ¬ (copySource C (C.form (H.typ (n + 1) (H.par n x)))
      (C.occ (H.typ n x) i) k).Nonempty) :
    (stcTile C hC H n x).cell i k = stcOrigin C hC H ⟨n, x, i, k⟩ := by
  apply stcValue_stop
  simp [stcStep, stcSource, hempty]

private lemma schedU_ne_zero {C : MacroCertificate P} {τ : Substitution P} {m : ℕ}
    {hC : C.Represents τ m} (o : C.SideOcc) : schedU C hC o ≠ 0 := by
  intro h
  cases h

private lemma stcTile_outer {C : MacroCertificate P} {τ : Substitution P} {m : ℕ}
    {hC : C.Represents τ m} (H : StrictTypeChain C) (n : ℕ) (x : H.X n)
    (i : C.Side (H.typ n x)) (ho : C.IsOuter (C.occ (H.typ n x) i)) :
    (stcTile C hC H n x).cell i 3 = schedU C hC (C.occ (H.typ n x) i) := by
  rw [stcTile_origin]
  · simp only [stcOrigin, strictGenCell]
    have hnp : ¬ ∃ d, C.IsPrintOf (C.form (H.typ (n + 1) (H.par n x))) d
        (C.occ (H.typ n x) i) := fun ⟨_, hd⟩ => isInner_of_isPrintOf C hd ho
    rw [if_neg hnp, if_neg (by decide), if_pos ho]
    simp only [if_true]
  · rintro ⟨p, hp | hp⟩
    · exact isInner_of_isPrintOf C hp.1 ho
    · exact absurd hp.2.1 (by decide)

private lemma stcHeader_eq {C : MacroCertificate P} {τ : Substitution P} {m : ℕ}
    {hC : C.Represents τ m} (H : StrictTypeChain C) (n : ℕ) (x : H.X n) :
    stcHeader C hC H n x =
      headerSU C hC (strictHeaderOf C hC (stcTile C hC H (n + 1) (H.par n x))) := by
  unfold stcHeader headerSU
  congr 1
  unfold strictHeaderOf
  dsimp only [stcTile]
  unfold HeaderKernel.makeHeader
  congr 1
  funext d
  unfold HeaderKernel.zeroMode
  by_cases ho : C.outerB (H.typ (n + 1) (H.par n x)) d = true
  · have ho' : C.IsOuter (C.occ (H.typ (n + 1) (H.par n x)) d) := by
      simpa [MacroData.outerB] using ho
    rw [ho]
    simp only [Bool.true_and]
    have hv : stcValue C hC H ⟨n + 1, H.par n x, d, 3⟩ ≠ 0 := by
      change (stcTile C hC H (n + 1) (H.par n x)).cell d 3 ≠ 0
      rw [stcTile_outer H (n + 1) (H.par n x) d ho']
      exact schedU_ne_zero _
    simp [hv]
  · simp [ho]

private lemma stcTile_child {C : MacroCertificate P} {τ : Substitution P} {m : ℕ}
    {hC : C.Represents τ m} (H : StrictTypeChain C) (n : ℕ) (x : H.X n) :
    IsStrictChildOf C hC (stcTile C hC H (n + 1) (H.par n x))
      (stcTile C hC H n x) := by
  refine ⟨H.adm n x, ?_⟩
  dsimp only [stcTile, strictChild, strictGen]
  congr 1
  funext i k
  split_ifs with hs
  · exact stcTile_copy H n x i k hs
  · change (stcTile C hC H n x).cell i k = _
    rw [stcTile_origin H n x i k hs, stcOrigin, stcHeader_eq]
    rfl

private def stcAncestor {C : MacroCertificate P} (H : StrictTypeChain C) (n : ℕ) (x : H.X n) :
    (j : ℕ) → H.X (n + j)
  | 0 => x
  | j + 1 => H.par (n + j) (stcAncestor H n x j)

private lemma stc_hasOrigin {C : MacroCertificate P} {τ : Substitution P} {m : ℕ}
    {hC : C.Represents τ m} (H : StrictTypeChain C) (n : ℕ) (x : H.X n) :
    ∀ (j l : ℕ) (i : C.Side (H.typ (n + l) (stcAncestor H n x l)))
      (k : Fin 5) (a : stcState H),
      stcIter H j ⟨n + l, stcAncestor H n x l, i, k⟩ = some a →
      stcStep H a = none →
      HasOrigin C (fun j => typeShadow C hC (stcTile C hC H (n + j)
        (stcAncestor H n x j))) l i k := by
  intro j
  induction j with
  | zero =>
    intro l i k a ha ha'
    simp only [stcIter, Option.some.injEq] at ha
    subst ha
    apply HasOrigin.origin
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hne
    have hne' : (copySource C (C.form (H.typ (n + l + 1)
        (H.par (n + l) (stcAncestor H n x l))))
        (C.occ (H.typ (n + l) (stcAncestor H n x l)) i) k).Nonempty := by
      simpa [typeShadow, stcTile, stcAncestor, Nat.add_assoc] using hne
    simp [stcStep, stcSource, hne'] at ha'
  | succ j ih =>
    intro l i k a ha ha'
    by_cases hne : (copySource C (C.form (H.typ (n + l + 1)
        (H.par (n + l) (stcAncestor H n x l))))
        (C.occ (H.typ (n + l) (stcAncestor H n x l)) i) k).Nonempty
    · simp only [stcIter, stcStep, stcSource, dif_pos hne, Option.map_some,
        Option.bind_some] at ha
      have horigin := ih (l + 1) hne.some.1 hne.some.2 a ha ha'
      have hmem := hne.some_mem
      simpa [typeShadow, stcTile, stcAncestor, Nat.add_assoc] using
        (HasOrigin.step (ch := fun j => typeShadow C hC (stcTile C hC H (n + j)
          (stcAncestor H n x j))) l i k hne.some.1 hne.some.2 hmem horigin)
    · simp [stcIter, stcStep, stcSource, hne] at ha

private lemma stcTile_legal {C : MacroCertificate P} {τ : Substitution P} {m : ℕ}
    {hC : C.Represents τ m} (H : StrictTypeChain C) (n : ℕ) (x : H.X n) :
    StrictLegal C hC (stcTile C hC H n x) := by
  refine ⟨fun j => stcTile C hC H (n + j) (stcAncestor H n x j), rfl,
    fun j => stcTile_child H (n + j) (stcAncestor H n x j), ?_⟩
  intro j i k _ hno
  show stcValue C hC H ⟨n + j, stcAncestor H n x j, i, k⟩ = 0
  unfold stcValue
  rw [dif_neg]
  rintro ⟨l, a, ha, ha'⟩
  exact hno (stc_hasOrigin H n x l j i k a ha ha')

private lemma strict_parent_exists (C : MacroCertificate P) {T' T : PlaneTiling C.Q}
    (h : C.σ.IsComposition T' T) {Z : PlacedTile C.Q} (hZ : Z ∈ T.tiles) :
    ∃ Y ∈ T'.tiles, ∃ t, C.owner t = Y.form ∧
      Z = ⟨C.form t, C.σ.θ • Y.anchor +ᵥ C.anchor t⟩ := by
  rw [← h] at hZ
  simp only [Substitution.decompose, Substitution.decomposeTile, translateSet, C.rule_eq,
    Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq] at hZ
  obtain ⟨Y, hY, _, ⟨t, ht, rfl⟩, rfl⟩ := hZ
  exact ⟨Y, hY, t, ht, rfl⟩

private lemma strict_child_mem (C : MacroCertificate P) {T' T : PlaneTiling C.Q}
    (h : C.σ.IsComposition T' T) {Y : PlacedTile C.Q} (hY : Y ∈ T'.tiles) {t : C.Typ}
    (ht : C.owner t = Y.form) :
    (⟨C.form t, C.σ.θ • Y.anchor +ᵥ C.anchor t⟩ : PlacedTile C.Q) ∈ T.tiles := by
  rw [← h]
  simp only [Substitution.decompose, Substitution.decomposeTile, translateSet, C.rule_eq,
    Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq]
  exact ⟨Y, hY, _, ⟨t, ht, rfl⟩, rfl⟩

private lemma strict_child_carrier_subset (C : MacroCertificate P) {Y : PlacedTile C.Q} {t : C.Typ}
    (ht : C.owner t = Y.form) :
    (⟨C.form t, C.σ.θ • Y.anchor +ᵥ C.anchor t⟩ : PlacedTile C.Q).carrier ⊆
      C.σ.θ • Y.carrier := by
  have hmem : (⟨C.form t, C.anchor t⟩ : PlacedTile C.Q) ∈ (C.σ.rule Y.form).tiles := by
    rw [C.rule_eq]
    exact ⟨t, ht, rfl⟩
  have hsub : (⟨C.form t, C.anchor t⟩ : PlacedTile C.Q).carrier ⊆
      C.σ.θ • (C.Q.disk Y.form).carrier := by
    rw [← C.σ.support_eq]
    exact Set.subset_biUnion_of_mem (u := fun A => A.carrier) hmem
  intro z hz
  simp only [PlacedTile.carrier, Set.mem_vadd_set] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hw' : C.anchor t +ᵥ w ∈ C.σ.θ • (C.Q.disk Y.form).carrier :=
    hsub (Set.vadd_mem_vadd_set hw)
  obtain ⟨u, hu, hu'⟩ := Set.mem_smul_set.1 hw'
  refine Set.mem_smul_set.2 ⟨Y.anchor +ᵥ u, Set.vadd_mem_vadd_set hu, ?_⟩
  simp only [vadd_eq_add, smul_add] at hu' ⊢
  rw [hu']
  abel

private lemma strict_parent_unique (C : MacroCertificate P) (T' : PlaneTiling C.Q)
    {Y Y' : PlacedTile C.Q} (hY : Y ∈ T'.tiles) (hY' : Y' ∈ T'.tiles) {t t' : C.Typ}
    (ht : C.owner t = Y.form) (ht' : C.owner t' = Y'.form)
    (he : (⟨C.form t, C.σ.θ • Y.anchor +ᵥ C.anchor t⟩ : PlacedTile C.Q) =
      ⟨C.form t', C.σ.θ • Y'.anchor +ᵥ C.anchor t'⟩) : Y = Y' ∧ t = t' := by
  have hθ : C.σ.θ ≠ 0 := by
    have := C.σ.one_lt
    positivity
  have hYY : Y = Y' := by
    by_contra hne
    set Z : PlacedTile C.Q := ⟨C.form t, C.σ.θ • Y.anchor +ᵥ C.anchor t⟩ with hZ
    have h1 := strict_child_carrier_subset C ht
    have h2 := strict_child_carrier_subset C ht'
    rw [← he] at h2
    obtain ⟨z, hz⟩ := (C.Q.disk (C.form t)).interior_nonempty
    have hzi : (C.σ.θ • Y.anchor +ᵥ C.anchor t) +ᵥ z ∈ interior Z.carrier := by
      simp only [Z, PlacedTile.carrier]
      rw [interior_vadd]
      exact Set.vadd_mem_vadd_set hz
    have i1 := interior_mono h1 hzi
    have i2 := interior_mono h2 hzi
    rw [interior_smul₀ hθ] at i1 i2
    obtain ⟨w, hw, hw'⟩ := Set.mem_smul_set.1 i1
    obtain ⟨w', hw2, hw2'⟩ := Set.mem_smul_set.1 i2
    have hww : w = w' := smul_right_injective _ hθ (hw'.trans hw2'.symm)
    subst hww
    exact Set.disjoint_left.1 (T'.disjoint hY hY' hne) hw hw2
  subst hYY
  refine ⟨rfl, C.type_injective t t' (ht.trans ht'.symm) (congrArg PlacedTile.form he) ?_⟩
  have ha := congrArg PlacedTile.anchor he
  simpa using ha

private def strictLiftTiling (C : MacroCertificate P) (hC : C.Represents τ m)
    (T : PlaneTiling C.Q) (f : T.tiles → StrictDecTile C hC)
    (hf : ∀ Z, C.form (f Z).typ = Z.1.form) : PlaneTiling (strictProtoset C hC) where
  tiles := Set.range fun Z =>
    (⟨StrictForm.typed (f Z), Z.1.anchor⟩ : PlacedTile (strictProtoset C hC))
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro z
    have hz : z ∈ support T.tiles := by rw [T.cover]; exact Set.mem_univ z
    simp only [support, Set.mem_iUnion] at hz ⊢
    obtain ⟨Z, hZ, hz⟩ := hz
    refine ⟨_, ⟨⟨Z, hZ⟩, rfl⟩, ?_⟩
    simpa only [PlacedTile.carrier, strictProtoset, StrictForm.proj, hf] using hz
  disjoint := by
    rintro _ ⟨Z, rfl⟩ _ ⟨Z', rfl⟩ hne
    simp only [Function.onFun, PlacedTile.carrier, StrictForm.proj, hf]
    apply T.disjoint Z.2 Z'.2
    intro he
    apply hne
    rw [Subtype.ext he]

private def strictLiftChain (C : MacroCertificate P) (seq : ℕ → PlaneTiling C.Q)
    (par : ∀ n, (seq n).tiles → (seq (n + 1)).tiles)
    (typ : ∀ n, (seq n).tiles → C.Typ)
    (hspec : ∀ n Z, C.owner (typ n Z) = (par n Z).1.form ∧
      Z.1 = ⟨C.form (typ n Z), C.σ.θ • (par n Z).1.anchor +ᵥ C.anchor (typ n Z)⟩) :
    StrictTypeChain C where
  X n := (seq n).tiles
  par := par
  typ := typ
  adm n Z := (hspec n Z).1.trans (congrArg PlacedTile.form (hspec (n + 1) (par n Z)).2)

private lemma strict_planeTiling_ext {Q : Protoset} {T U : PlaneTiling Q}
    (h : T.tiles = U.tiles) : T = U := by
  cases T
  cases U
  congr

/-- The founded property of a strict lift of a hierarchy (`lem:strict-presentation`,
completeness): every decorated tile is legal along its *actual* ancestor chain in the lift (the
tiles `Y` of the higher levels containing it): every originless copied cell of that chain is zero.
`AllStrictLegal` alone only asks for *some* legality chain, which may divert from the actual
hierarchy; then a persistent fault line can carry a constant nonzero copied signal on one side
(argon audit of 14 October 2026, the strict twin of the repair fac433f). The lift constructed by
`strict_lift_decorations` (cells `stcValue`: the origin of the actual chain, or zero) is founded. -/
def StrictLiftFounded (C : MacroCertificate P) (hC : C.Represents τ m)
    (seq'' : ℕ → PlaneTiling (strictProtoset C hC)) : Prop :=
  ∀ n, ∀ X ∈ (seq'' n).tiles, ∀ A, X.form = StrictForm.typed A →
    ∃ ch : ℕ → StrictDecTile C hC, ch 0 = A ∧ (∀ k, IsStrictChildOf C hC (ch (k + 1)) (ch k)) ∧
      (∀ k, ∃ Y ∈ (seq'' (n + k)).tiles, Y.form = StrictForm.typed (ch k) ∧
        X.carrier ⊆ ((strictSubst C hC).θ ^ k) • Y.carrier) ∧
      ∀ (k : ℕ) (i : C.Side (ch k).typ) (l : Fin 5),
        (copySource C (C.form (ch (k + 1)).typ) (C.occ (ch k).typ i) l).Nonempty →
        ¬ StrictHasOrigin C hC ch k i l → (ch k).cell i l = 0

/-- Step 1 of the blueprint proof of `strict_lift_decorations`: the constructed lift is founded.
The legality chain of a lifted tile can be taken along the actual hierarchy (`stcTile` of the
iterated parents), whose copied cells are `stcValue`: the origin of a terminating copy chain, or
zero when the chain has no origin. -/
private lemma strict_lift_decorations_step1_founded (C : MacroCertificate P)
    (hC : C.Represents τ m)
    (seq : ℕ → PlaneTiling C.Q) (hseq : ∀ n, C.σ.IsComposition (seq (n + 1)) (seq n))
    (par : ∀ n, (seq n).tiles → (seq (n + 1)).tiles)
    (typ : ∀ n, (seq n).tiles → C.Typ)
    (hspec : ∀ n Z, C.owner (typ n Z) = (par n Z).1.form ∧
      Z.1 = ⟨C.form (typ n Z), C.σ.θ • (par n Z).1.anchor +ᵥ C.anchor (typ n Z)⟩)
    (hform : ∀ n (Z : (seq n).tiles),
      C.form (stcTile C hC (strictLiftChain C seq par typ hspec) n Z).typ = Z.1.form) :
    StrictLiftFounded C hC fun n =>
      strictLiftTiling C hC (seq n) (stcTile C hC (strictLiftChain C seq par typ hspec) n) (hform n) := by
  sorry

private lemma strictLift_main (C : MacroCertificate P) (hC : C.Represents τ m)
    (seq : ℕ → PlaneTiling C.Q) (hseq : ∀ n, C.σ.IsComposition (seq (n + 1)) (seq n))
    (par : ∀ n, (seq n).tiles → (seq (n + 1)).tiles)
    (typ : ∀ n, (seq n).tiles → C.Typ)
    (hspec : ∀ n Z, C.owner (typ n Z) = (par n Z).1.form ∧
      Z.1 = ⟨C.form (typ n Z), C.σ.θ • (par n Z).1.anchor +ᵥ C.anchor (typ n Z)⟩) :
    ∃ seq'' : ℕ → PlaneTiling (strictProtoset C hC),
      (∀ n, (strictDecoration C hC).toDecoration.project (seq'' n) = seq n) ∧
      (∀ n, (strictSubst C hC).IsComposition (seq'' (n + 1)) (seq'' n)) ∧
      (∀ n, AllStrictLegal C hC (seq'' n)) ∧ StrictLiftFounded C hC seq'' := by
  let H := strictLiftChain C seq par typ hspec
  have hform : ∀ n (Z : (seq n).tiles), C.form (stcTile C hC H n Z).typ = Z.1.form :=
    fun n Z => (congrArg PlacedTile.form (hspec n Z).2).symm
  have hchild : ∀ n (Y : (seq (n + 1)).tiles) (t : C.Typ) (ht : C.owner t = Y.1.form),
      ∃ Z : (seq n).tiles, par n Z = Y ∧ typ n Z = t ∧
        Z.1 = ⟨C.form t, C.σ.θ • Y.1.anchor +ᵥ C.anchor t⟩ := by
    intro n Y t ht
    let Z : (seq n).tiles := ⟨_, strict_child_mem C (hseq n) Y.2 ht⟩
    obtain ⟨h1, h2⟩ := strict_parent_unique C (seq (n + 1)) (par n Z).2 Y.2
      (hspec n Z).1 ht ((hspec n Z).2.symm.trans rfl)
    exact ⟨Z, Subtype.ext h1, h2, rfl⟩
  let lift : ℕ → PlaneTiling (strictProtoset C hC) := fun n =>
    strictLiftTiling C hC (seq n) (stcTile C hC H n) (hform n)
  refine ⟨lift, ?_, ?_, ?_,
    strict_lift_decorations_step1_founded C hC seq hseq par typ hspec hform⟩
  · intro n
    apply strict_planeTiling_ext
    ext W
    constructor
    · rintro ⟨_, ⟨Z, rfl⟩, rfl⟩
      convert Z.2 using 1
      exact PlacedTile.ext (hform n Z) rfl
    · intro hW
      refine ⟨_, ⟨⟨W, hW⟩, rfl⟩, ?_⟩
      exact PlacedTile.ext (hform n ⟨W, hW⟩) rfl
  · intro n
    unfold Substitution.IsComposition Substitution.decompose
    ext W
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨X, hX, hWX⟩
      obtain ⟨Zp, rfl⟩ := hX
      change W ∈ translateSet _ (strictChildren C hC _ _ _) at hWX
      obtain ⟨V, hV, rfl⟩ := hWX
      obtain ⟨t, ht, rfl⟩ := hV
      have ht' : C.owner t = Zp.1.form := ht.trans (hform (n + 1) Zp)
      obtain ⟨Z, hp, htyp, hZ⟩ := hchild n Zp t ht'
      refine ⟨Z, ?_⟩
      apply PlacedTile.ext
      · simp only [PlacedTile.translate, StrictForm.typed.injEq]
        rw [← htyp, ← hp]
        exact (stcTile_child H n Z).2
      · simp only [PlacedTile.translate]
        rw [hZ]
        rfl
    · rintro ⟨Z, rfl⟩
      let X : PlacedTile (strictProtoset C hC) :=
        ⟨.typed (stcTile C hC H (n + 1) (par n Z)), (par n Z).1.anchor⟩
      refine ⟨X, ⟨par n Z, rfl⟩, ?_⟩
      change _ ∈ translateSet _ (strictChildren C hC _ _ _)
      let V : PlacedTile (strictProtoset C hC) :=
        ⟨.typed (stcTile C hC H n Z), C.anchor (typ n Z)⟩
      refine ⟨V, ?_, ?_⟩
      · change (⟨.typed (stcTile C hC H n Z), C.anchor (typ n Z)⟩ :
          PlacedTile (strictProtoset C hC)) ∈ strictChildren C hC _ _ _
        refine ⟨typ n Z, ?_, ?_⟩
        · exact (hspec n Z).1.trans (hform (n + 1) (par n Z)).symm
        · apply PlacedTile.ext
          · simp only [StrictForm.typed.injEq]
            exact (stcTile_child H n Z).2.symm
          · rfl
      · apply PlacedTile.ext
        · rfl
        · simp only [X, V, PlacedTile.translate, strictSubst]
          rw [(hspec n Z).2]
  · rintro n _ ⟨Z, rfl⟩
    exact stcTile_legal H n Z

/-- `lem:strict-presentation` (completeness, "origin chains give legal tiles"): every grouped
`σ'`-hierarchy lifts to compatible legal strict decorations (types from the positions in the
parent templates; generated cells fixed; a copied cell takes the value of the origin of its
source chain, or zero if there is none). -/
theorem strict_lift_decorations (seq' : ℕ → PlaneTiling C.Q)
    (hseq : ∀ n, C.σ.IsComposition (seq' (n + 1)) (seq' n)) :
    ∃ seq'' : ℕ → PlaneTiling (strictProtoset C hC),
      (∀ n, (strictDecoration C hC).toDecoration.project (seq'' n) = seq' n) ∧
      (∀ n, (strictSubst C hC).IsComposition (seq'' (n + 1)) (seq'' n)) ∧
      (∀ n, AllStrictLegal C hC (seq'' n)) ∧ StrictLiftFounded C hC seq'' := by
  classical
  have hpar : ∀ n (Z : (seq' n).tiles),
      ∃ Y : (seq' (n + 1)).tiles, ∃ t, C.owner t = Y.1.form ∧
        Z.1 = ⟨C.form t, C.σ.θ • Y.1.anchor +ᵥ C.anchor t⟩ := by
    intro n Z
    obtain ⟨Y, hY, t, ht, he⟩ := strict_parent_exists C (hseq n) Z.2
    exact ⟨⟨Y, hY⟩, t, ht, he⟩
  choose par typ hspec using hpar
  exact strictLift_main C hC seq' hseq par typ hspec

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
    (hleg : ∀ n, AllStrictLegal C hC (seq'' n)) (hfounded : StrictLiftFounded C hC seq'') :
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
  obtain ⟨seq'', hproj, hcomp, hleg, hfounded⟩ := strict_lift_decorations C hC seq' hseq
  exact ⟨seq'' 0, (strict_proper_iff C hC _).2
    ⟨strict_lift_matched C hC seq' hseq hsts hlev seq'' hproj hcomp hleg hfounded, hleg 0⟩, hproj 0⟩

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
