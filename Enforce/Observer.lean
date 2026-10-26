import Enforce.Parser.Assembly

/-!
# Complete observers and finite descent saturation

O1--O6, V4 4.1--4.6, in the lossless one-state form of V4 8.1.
The window stores only its highest state and the intervening roles, in bottom-up
index order. Descent reads those roles in reverse order. Every node facet retains
its attached packet, including NULL and possible phantom packets on output faults.
The joint source range is an actual image over honest sources, not a product of
marginal ranges. Rendering is shared by honest sources and arbitrary proper outputs.

DEVIATION: the transition is total on raw observer tuples and raw roles. On a
role/type mismatch it returns the input observer. Missing internal incidences or
empty raw masks give NULL. These branches never occur on source or parsed child
transitions. This is only a totalization of the explicit V4 4.3(i)--(iii) formulas;
no arbitrary honest witness defines the transition. See SKEL-NOTES.md, D11.

DEVIATION: observer extraction uses the same formula at all natural heights. The
joint source range and saturation still start at H, and rendering starts at K.
This uniform raw extraction avoids extra membership arguments; see D12.
-/

open Set

noncomputable section

namespace Enforce

variable {d : ℕ} [Fact (2 ≤ d)] {S : SubstSystem d} {P : Params S}
variable {C : ClusterData S P}

/-- O1, V4 4.1, 8.1: the observer window is nonempty, with room to shift it. -/
theorem Params.observer_window_bound (P : Params S) : 3 ≤ P.w := by
  have h := P.k_lower
  rw [P.w_eq]
  omega

/-- O1, V4 8.1: the compressed consecutive window, before admissibility.
The roles are indexed from the lowest node upward; reconstruction descends in
reverse order. Inconsistent raw tuples are not asserted to occur. -/
@[ext]
structure ObserverWindow (P : Params S) where
  /-- O1, V4 8.1: the state at offset `w-1`. -/
  top : State P
  /-- O1, V4 8.1: the intervening roles, with exactly `w-1` letters. -/
  roles : Fin (P.w - 1) → S.Role

namespace ObserverWindow

/-- O1, V4 8.1: reconstruct downward from the highest state by `childMap`. -/
def descend (a : ObserverWindow P) : ℕ → State P
  | 0 => a.top
  | n + 1 => if hn : n < P.w - 1 then
      childMap P (a.descend n) (a.roles ⟨P.w - 2 - n, by omega⟩)
    else a.descend n

/-- O1, V4 8.1: the state at a specified offset above the lowest node. -/
def stateAt (a : ObserverWindow P) (j : Fin P.w) : State P :=
  a.descend (P.w - 1 - j.val)

/-- O1, V4 4.1, 8.1: the reconstructed lowest state. -/
def head (a : ObserverWindow P) : State P :=
  a.stateAt ⟨0, by have := P.observer_window_bound; omega⟩

/-- O3, V4 4.3(i), 8.1: shift the window down by one role.
The new highest state is the old offset `w-2`; the bottom role is prepended.
This is the compressed form of `(D_S(s₀,i),s₀,...,s_(w-2))`. -/
def child (a : ObserverWindow P) (r : S.Role) : ObserverWindow P where
  top := a.stateAt ⟨P.w - 2, by have := P.observer_window_bound; omega⟩
  roles j := if h : j.val = 0 then r else a.roles ⟨j.val - 1, by omega⟩

/-- O3, V4 4.3(i), 8.1: the explicit shift reconstructs the prescribed child head.
This is an algebraic identity of the compressed representation, even on raw windows. -/
theorem child_head (a : ObserverWindow P) (r : S.Role) :
    (a.child r).head = childMap P a.head r := by
  sorry

/-- O1, V4 4.1, 8.1: extract the window from one hierarchy and one state assignment.
Ancestors exist without an upper cutoff, including over the floor height. -/
def ofHierarchy {T : Tiling S} (H : CoherentHierarchy S T)
    (state : H.Node → State P) (q : H.Node) : ObserverWindow P where
  top := state (H.ancestor q (P.w - 1))
  roles j := H.nodeRole (H.ancestor q j.val)

end ObserverWindow

/-- O1, V4 4.1, 8.1: an observer consists of a compressed window and exactly
one packet-or-NULL record per facet of its lowest prototype. The redundant type
and its equality proof merely keep facet indexing independent of reconstruction. -/
@[ext]
structure Observer (P : Params S) where
  /-- O1, V4 4.1: the lowest node's prototype. -/
  ty : S.ι
  /-- O1, V4 8.1: highest state and downward role word. -/
  window : ObserverWindow P
  /-- O1, V4 4.1, 8.1: the reconstructed lowest state has the recorded type. -/
  head_type : window.head.ty = ty
  /-- O1, V4 4.1: the entire side attachment, not a provider chosen from its state. -/
  packets : FacetName S ty → Option (Packet P)

/-- O1, V4 4.1: the finite ambient alphabet `𝓙` in compressed coordinates.
Only the highest state and each non-NULL packet must lie in their finite honest
alphabets. Joint occurrence is a separate, stronger condition in `jointSourceRange`. -/
def observerAlphabet (S : SubstSystem d) (P : Params S) : Set (Observer P) :=
  {a | a.window.top ∈ honestStates S P ∧
    ∀ F q, a.packets F = some q → q ∈ honestPackets S P}

/-- O1, V4 4.1, 8.1: finitely many compressed observers.
This asserts finiteness of `𝓙`, not of the ambient type with arbitrary raw states. -/
theorem observers_finite (S : SubstSystem d) (P : Params S) :
    (observerAlphabet S P).Finite := by
  sorry

/-- O1, V4 4.1, 8.1: the parsed compressed window recovers every actual ancestor state. -/
theorem parsedWindow_at (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (j : Fin P.w) :
    (ObserverWindow.ofHierarchy (parsedHierarchy Y hY) (parsedState Y hY) q).stateAt j =
      parsedState Y hY ((parsedHierarchy Y hY).ancestor q j.val) := by
  sorry

/-- O1, V4 4.1, 8.1: the honest compressed window recovers every ancestor state. -/
theorem honestWindow_at (U : HonestSource S) (P : Params S) (q : U.Node)
    (j : Fin P.w) :
    (ObserverWindow.ofHierarchy U.hierarchy (stateOf U P) q).stateAt j =
      stateOf U P (U.hierarchy.ancestor q j.val) := by
  sorry

/-- O1, V4 4.1, 8.1: reconstruction preserves the parsed node's prototype. -/
theorem parsedWindow_type (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) :
    (ObserverWindow.ofHierarchy (parsedHierarchy Y hY) (parsedState Y hY) q).head.ty =
      q.2.val.ty := by
  have h := parsedWindow_at Y hY q ⟨0, by have := P.observer_window_bound; omega⟩
  change _ = parsedState Y hY q at h
  exact (congrArg State.ty h).trans (parsedState_type_residue Y hY q).2.1

/-- O1, V4 4.1, 8.1: reconstruction preserves the honest node's prototype. -/
theorem honestWindow_type (U : HonestSource S) (P : Params S) (q : U.Node) :
    (ObserverWindow.ofHierarchy U.hierarchy (stateOf U P) q).head.ty = q.2.val.ty := by
  have h := honestWindow_at U P q ⟨0, by have := P.observer_window_bound; omega⟩
  change _ = stateOf U P q at h
  exact congrArg State.ty h

/-- O1, V4 4.1, 8.1: the actual observer of a parsed node of a proper output.
DEVIATION: the same formula is defined below the observer floor (D12); saturation
uses it only at heights at least H. No source provider is inferred on a fault. -/
def observerOf (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) : Observer P where
  ty := q.2.val.ty
  window := ObserverWindow.ofHierarchy (parsedHierarchy Y hY) (parsedState Y hY) q
  head_type := parsedWindow_type Y hY q
  packets := parsedFacetPacket Y hY q

/-- O1, V4 4.1, 8.1: the observer of an honest source node.
All facet records are the existing actual provider packet or NULL extraction.
DEVIATION: extraction is also defined below H, without adding such nodes to 𝓑 (D12). -/
def HonestSource.observerOf (U : HonestSource S) (P : Params S) (q : U.Node) :
    Observer P where
  ty := q.2.val.ty
  window := ObserverWindow.ofHierarchy U.hierarchy (stateOf U P) q
  head_type := honestWindow_type U P q
  packets := U.facetPacket P q

/-- O1, V4 4.1: every parsed observer belongs to the finite ambient alphabet. -/
theorem observerOf_mem (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) : observerOf Y hY q ∈ observerAlphabet S P := by
  exact ⟨(parsedState_type_residue Y hY _).1,
    fun F p hp => parsedFacetPacket_honest Y hY q F p hp⟩

/-- O1, V4 4.1: every honest observer belongs to the finite ambient alphabet. -/
theorem HonestSource.observerOf_mem (U : HonestSource S) (P : Params S) (q : U.Node) :
    U.observerOf P q ∈ observerAlphabet S P := by
  sorry

/-- O1, V4 4.1: the joint source range `𝓑`, with a single witness for the whole tuple.
It may be empty when there is no honest source; no nonemptiness is postulated. -/
def jointSourceRange (S : SubstSystem d) (P : Params S) : Set (Observer P) :=
  {a | ∃ (U : HonestSource S) (q : U.Node), P.H ≤ q.1 ∧ U.observerOf P q = a}

/-- O1, V4 4.1: an actual source node above the floor contributes its whole observer. -/
theorem honestObserver_mem_range (U : HonestSource S) (P : Params S) (q : U.Node)
    (hq : P.H ≤ q.1) : U.observerOf P q ∈ jointSourceRange S P :=
  ⟨U, q, hq, rfl⟩

/-- O1, V4 4.1: the joint source range is contained in the finite alphabet. -/
theorem jointSourceRange_subset (S : SubstSystem d) (P : Params S) :
    jointSourceRange S P ⊆ observerAlphabet S P := by
  rintro a ⟨U, q, _, rfl⟩
  exact U.observerOf_mem P q

namespace Observer

/-- O3, V4 4.3(iii), 8.1: construct a newly born packet from the parent window.
The maximum PRESENT slot and its state are computed from the actual mask formula.
DEVIATION: an empty mask on an inconsistent raw tuple is totalized by NULL (D11). -/
def bornPacket (a : Observer P) (ι : P.Incidence) : Option (Packet P) := by
  classical
  let slots := Finset.univ.filter (packetMask P ι a.window.head)
  exact if h : slots.Nonempty then
    let j := slots.max' h
    some {
      incidence := ι
      jstar := j
      sstar := a.window.stateAt ⟨j.val, by have := j.isLt; rw [P.w_eq]; exact this⟩
      roles := fun t => a.window.roles ⟨t.val, by
        have := j.isLt
        have := t.isLt
        rw [P.w_eq]
        omega⟩ }
    else none

/-- O3, V4 4.3(ii)--(iii): packet on a named child facet, in the fixed substitution.
Inherited facets copy the unique parent attachment. Internal facets use the canonical
incidence of that positioned first-generation facet and `bornPacket`. All lookups
are geometric, in `σ A`, and retain the general linear expansion.
DEVIATION: missing raw incidences yield NULL; actual internal facets have one (D11). -/
def childPacket (a : Observer P) (r : S.Role) (f : Cell d) : Option (Packet P) := by
  classical
  exact if h : ∃ F : FacetName S a.ty,
      placedSet (S.child r.1 r.2).frame f.carrier ⊆ S.σ '' F.val.carrier then
    a.packets (Classical.choose h)
    else if hι : ∃ ι : P.Incidence, ι.val.ty = a.ty ∧
        ι.val.positioned = placedSet (S.child r.1 r.2).frame f.carrier then
      a.bornPacket (Classical.choose hι)
    else none

/-- O3, V4 4.3(i)--(iii), 8.1: the explicit compressed child transition `D_Ĵ`.
Only `childMap`, the shifted window, inherited attachments and the computed birth
packet are used. DEVIATION: invalid raw type/role pairs return the input (D11). -/
def transition (a : Observer P) (r : S.Role) : Observer P := by
  classical
  let w := a.window.child r
  exact if h : r.1 = a.ty ∧ w.head.ty = (S.child r.1 r.2).ty then {
    ty := (S.child r.1 r.2).ty
    window := w
    head_type := h.2
    packets := fun f => a.childPacket r f.val }
    else a

/-- O3/O6, V4 4.3, 4.6: a fixed enumeration of the prescribed child roles.
DEVIATION: Finset.toList chooses an order for the abstract descent forest; changing
it only reorders siblings and does not change any geometric statement (D11). -/
def roles (A : S.ι) : List (S.I A) := by
  classical
  exact (Finset.univ : Finset (S.I A)).toList

/-- O3/O6, V4 4.3, 4.6: the complete prescribed observer child list. -/
def children (a : Observer P) : List (Observer P) :=
  (roles a.ty).map (fun i => a.transition ⟨a.ty, i⟩)

/-- O3/O6, V4 4.3, 4.6: every prescribed role occurs once. -/
theorem roles_nodup (A : S.ι) : (roles A).Nodup := by
  classical
  exact Finset.nodup_toList _

/-- O3/O6, V4 4.3, 4.6: every child role is present in the enumeration. -/
theorem mem_roles (A : S.ι) (i : S.I A) : i ∈ roles A := by
  classical
  exact Finset.mem_toList.mpr (Finset.mem_univ i)

/-- O3/O6, V4 4.3, 4.6: child lists are nonempty, including one-child types.
An actual prototype has children by H3, independently of any source tiling. -/
theorem roles_ne_nil (A : S.ι) : roles A ≠ [] := by
  obtain ⟨i⟩ := Parser.roles_nonempty A
  intro h
  have := mem_roles A i
  simp only [h, List.not_mem_nil] at this

end Observer

/-- O3, V4 4.3(0): every joint source observer has a witness strictly above H.
Exact-scale transfer raises a floor-only witness by the residue modulus L and
preserves its entire upward hierarchy, even for arbitrarily high facet providers. -/
theorem range_raise (a : Observer P) (ha : a ∈ jointSourceRange S P) :
    ∃ (U : HonestSource S) (q : U.Node), P.H + 1 ≤ q.1 ∧ U.observerOf P q = a := by
  sorry

/-- O3, V4 4.3(1): the explicit transition computes every honest child's observer.
The height hypothesis places both observers in the joint source range. -/
theorem honest_observer_transition (U : HonestSource S) (P : Params S) (q : U.Node)
    (hq : P.H + 1 ≤ q.1) (i : S.I q.2.val.ty) :
    U.observerOf P (U.childNode q (by omega) i) =
      (U.observerOf P q).transition ⟨q.2.val.ty, i⟩ := by
  sorry

/-- O3, V4 4.3(0),(1): the joint source range is forward closed under the
explicit transition, with the prescribed child type. Floor-only witnesses are
raised before taking children, rather than assumed to have children above H. -/
theorem range_forward_closed (a : Observer P) (ha : a ∈ jointSourceRange S P)
    (i : S.I a.ty) :
    a.transition ⟨a.ty, i⟩ ∈ jointSourceRange S P ∧
      (a.transition ⟨a.ty, i⟩).ty = (S.child a.ty i).ty := by
  sorry

/-- O4/O6, V4 4.4, 4.6: an actual prescribed child of a parsed positive-height node. -/
def parsedChild (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) :
    (parsedHierarchy Y hY).Node :=
  ⟨q.1 - 1, ⟨q.2.val.child (q.1 - 1) i,
    (parsedHierarchy Y hY).children_mem (q.1 - 1) q.2.val
      (by simpa only [Nat.sub_add_cancel hq] using q.2.property) i⟩⟩

/-- O4, V4 4.4: exact observer transition in an arbitrary proper output.
This includes certificate nodes below K. W4 calibrates internal births, and I5
copies inherited packets, including NULL and phantom fault packets. -/
theorem observer_transition (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : P.H + 1 ≤ q.1) (i : S.I q.2.val.ty) :
    observerOf Y hY (parsedChild Y hY q (by omega) i) =
      (observerOf Y hY q).transition ⟨q.2.val.ty, i⟩ := by
  sorry

/-- O5, V4 4.5: the entire observer of each height-H node occurs jointly in
one honest source node. The window and facet packets are read from one honest
K-certificate, using H+w ≤ K; separate marginal witnesses would not suffice. -/
theorem ground_actuality (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : q.1 = P.H) :
    observerOf Y hY q ∈ jointSourceRange S P := by
  sorry

namespace Observer

/-- O6, V4 4.6: the finite stateUniverse `𝓙_*`, containing honest and occurring observers.
Source and output witnesses are retained as alternatives, without any global
nonemptiness assumption on the species. -/
def stateUniverse (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) : Set (Observer P) :=
  jointSourceRange S P ∪
    {a | ∃ q : (parsedHierarchy Y hY).Node, P.H ≤ q.1 ∧ observerOf Y hY q = a}

/-- O6, V4 4.6: the saturation stateUniverse is a finite subset of `𝓙`. -/
theorem universe_finite (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    (stateUniverse Y hY).Finite := by
  apply (observers_finite S P).subset
  rintro a (ha | ⟨q, _, rfl⟩)
  · exact jointSourceRange_subset S P ha
  · exact observerOf_mem Y hY q

/-- O6, V4 4.6: every observer in `𝓙_*` has a source or output witness above H.
For output witnesses at H, ground actuality supplies a source witness and 4.3(0)
raises it. Thus the explicit transition stays inside the chosen finite stateUniverse. -/
theorem universe_closed (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (a : Observer P) (ha : a ∈ stateUniverse Y hY) (i : S.I a.ty) :
    a.transition ⟨a.ty, i⟩ ∈ stateUniverse Y hY := by
  sorry

/-- O6, V4 4.6: prescribed child list restricted to the actual finite stateUniverse. -/
def universeD (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (a : stateUniverse Y hY) : List (stateUniverse Y hY) :=
  (roles a.val.ty).map (fun i =>
    ⟨a.val.transition ⟨a.val.ty, i⟩, universe_closed Y hY a.val a.property i⟩)

/-- O6, V4 4.6: every state of the finite stateUniverse has a nonempty child list. -/
theorem universeD_nonempty (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (a : stateUniverse Y hY) : universeD Y hY a ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  simp only [universeD, List.length_map, List.length_nil] at hlen
  exact roles_ne_nil a.val.ty (List.length_eq_zero_iff.mp hlen)

/-- O6, V4 4.6: the honest subset of `𝓙_*` is forward closed. -/
theorem universe_forward_closed (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    ForwardClosed (universeD Y hY) {a | a.val ∈ jointSourceRange S P} := by
  intro a ha b hb
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
  exact (range_forward_closed a.val ha i).1

/-- O6, V4 4.6: actual forest nodes are the parsed nodes at or above H. -/
abbrev FloorNode (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :=
  {q : (parsedHierarchy Y hY).Node // P.H ≤ q.1}

/-- O6, V4 4.6: every actual forest node has its next-height parent above H. -/
def floorParent (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : FloorNode Y hY) : FloorNode Y hY :=
  ⟨(parsedHierarchy Y hY).parentNode q.val, Nat.le_trans q.property (Nat.le_succ _)⟩

/-- O6, V4 4.6: the complete actual child list, cut off at the floor.
Above H the list has one entry for every role, with its exact parsed frame. -/
def floorChildren (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : FloorNode Y hY) : List (FloorNode Y hY) := by
  classical
  exact if h : P.H < q.val.1 then
    (roles q.val.2.val.ty).map (fun i =>
      ⟨parsedChild Y hY q.val (by omega) i, by change P.H ≤ q.val.1 - 1; omega⟩)
    else []

/-- O6, V4 4.6: every actual node's observer is an element of `𝓙_*`. -/
def floorState (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : FloorNode Y hY) : stateUniverse Y hY :=
  ⟨observerOf Y hY q.val, Or.inr ⟨q.val, q.property, rfl⟩⟩

/-- O6, V4 4.6: distinct roles give distinct actual child nodes. -/
theorem floorChildren_nodup (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : FloorNode Y hY) : (floorChildren Y hY q).Nodup := by
  sorry

/-- O6, V4 4.6: actual children lie exactly one level below their parent. -/
theorem floorChildren_level (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q r : FloorNode Y hY) (hr : r ∈ floorChildren Y hY q) :
    q.val.1 - P.H = (r.val.1 - P.H) + 1 := by
  sorry

/-- O6, V4 4.6: every actual node occurs in its parent's complete child list. -/
theorem floor_mem_parent (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : FloorNode Y hY) : q ∈ floorChildren Y hY (floorParent Y hY q) := by
  sorry

/-- O6, V4 4.6: the listed parent is the unique actual hierarchy parent. -/
theorem floor_child_parent (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q r : FloorNode Y hY) (hr : r ∈ floorChildren Y hY q) :
    floorParent Y hY r = q := by
  sorry

/-- O6, V4 4.6: exact child order and multiplicities agree with the explicit transition.
This is the list form of 4.4; repetitions of observer values remain repetitions. -/
theorem floor_prescribed (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : FloorNode Y hY) (hq : 1 ≤ q.val.1 - P.H) :
    (floorChildren Y hY q).map (floorState Y hY) = universeD Y hY (floorState Y hY q) := by
  sorry

/-- O6, V4 4.6: the genuine forest used by C1, with no new choice of observers.
Its states are the actual compressed readouts, with a finite-stateUniverse membership proof. -/
def forest (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) :
    DescentForest (stateUniverse Y hY) (universeD Y hY) where
  Node := FloorNode Y hY
  level q := q.val.1 - P.H
  parent := floorParent Y hY
  parent_level q := by
    change q.val.1 + 1 - P.H = (q.val.1 - P.H) + 1
    have := q.property
    omega
  state := floorState Y hY
  children := floorChildren Y hY
  children_nodup := floorChildren_nodup Y hY
  child_level := floorChildren_level Y hY
  mem_parent := floor_mem_parent Y hY
  child_parent := floor_child_parent Y hY
  prescribed := floor_prescribed Y hY

end Observer

/-- O6, V4 4.6: every parsed observer above the floor has a single honest witness.
The proof assembles C1 with the actual forest, finite stateUniverse, forward closure
and ground actuality. Persistent faults receive no extra provider assumption. -/
theorem saturation (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : P.H ≤ q.1) :
    observerOf Y hY q ∈ jointSourceRange S P := by
  letI := (Observer.universe_finite Y hY).fintype
  have ground : ∀ x : (Observer.forest Y hY).Node,
      (Observer.forest Y hY).level x = 0 →
        (Observer.forest Y hY).state x ∈ {a | a.val ∈ jointSourceRange S P} := by
    intro x hx
    apply ground_actuality Y hY x.val
    change x.val.1 - P.H = 0 at hx
    have := x.property
    omega
  exact descent_saturation (Observer.universeD Y hY)
    (Observer.universeD_nonempty Y hY) {a | a.val ∈ jointSourceRange S P}
    (Observer.universe_forward_closed Y hY) (Observer.forest Y hY) ground ⟨q, hq⟩

/-- O2, V4 4.2: complete patterns observed in either an honest source or a
proper output, at one fixed height and one exact observer. The common type is
part of the observer; all comparisons use full normalized isometric frames. -/
def ObservedPattern (C : ClusterData S P) (n : ℕ) (a : Observer P)
    (q : Pattern S (Colour S P) n a.ty) : Prop :=
  (∃ (U : HonestSource S) (φ : Iso d)
      (hN : (⟨a.ty, φ⟩ : FramedNode S) ∈ U.hierarchy.nodes n),
    U.observerOf P ⟨n, ⟨⟨a.ty, φ⟩, hN⟩⟩ = a ∧
      q = normalisedPattern (honestLift C U) n a.ty φ) ∨
  ∃ (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) (φ : Iso d)
      (hN : (⟨a.ty, φ⟩ : FramedNode S) ∈ (parsedHierarchy Y hY).nodes n),
    observerOf Y hY ⟨n, ⟨⟨a.ty, φ⟩, hN⟩⟩ = a ∧
      q = normalisedPattern Y n a.ty φ

/-- O2, V4 4.2: the complete closed pattern is determined by the joint observer.
This compares any source/output pair. Leaf certificates use the reconstructed
window and all facet packets; no height-bounded assumption on providers is made. -/
theorem observedPattern_unique (C : ClusterData S P) (n : ℕ) (hn : P.K ≤ n)
    (a : Observer P) (q q' : Pattern S (Colour S P) n a.ty)
    (hq : ObservedPattern C n a q) (hq' : ObservedPattern C n a q') : q = q' := by
  sorry

/-- O2, V4 4.2: the common rendering function `Rend_n`.
A realized pattern supplies the choice; unused raw observers receive the constant
boundary pattern. Only heights n ≥ K are asserted to render uniquely. -/
def Rend (C : ClusterData S P) (n : ℕ) (a : Observer P) :
    Pattern S (Colour S P) n a.ty := by
  classical
  exact if h : ∃ q, ObservedPattern C n a q then Classical.choose h
    else fun _ => Colour.boundary

/-- O2, V4 4.2: any realized closed pattern equals the common rendering. -/
theorem Rend_eq (C : ClusterData S P) (n : ℕ) (hn : P.K ≤ n) (a : Observer P)
    (q : Pattern S (Colour S P) n a.ty) (hq : ObservedPattern C n a q) :
    Rend C n a = q := by
  classical
  have h : ∃ q, ObservedPattern C n a q := ⟨q, hq⟩
  rw [Rend, dif_pos h]
  exact observedPattern_unique C n hn a _ q (Classical.choose_spec h) hq

/-- O2, V4 4.2: every parsed node of height at least K has its rendered pattern. -/
theorem observer_renders (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : P.K ≤ q.1) :
    normalisedPattern Y q.1 q.2.val.ty q.2.val.frame = Rend C q.1 (observerOf Y hY q) := by
  symm
  apply Rend_eq C q.1 hq
  exact Or.inr ⟨Y, hY, q.2.val.frame, q.2.property, rfl, rfl⟩

/-- O2, V4 4.2: the very same renderer gives every honest source node pattern. -/
theorem honest_observer_renders (U : HonestSource S) (P : Params S)
    (C : ClusterData S P) (q : U.Node) (hq : P.K ≤ q.1) :
    normalisedPattern (honestLift C U) q.1 q.2.val.ty q.2.val.frame =
      Rend C q.1 (U.observerOf P q) := by
  symm
  apply Rend_eq C q.1 hq
  exact Or.inl ⟨U, q.2.val.frame, q.2.property, rfl, rfl⟩

end Enforce
