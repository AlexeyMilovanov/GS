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
  have hw : {w : ObserverWindow P | w.top ∈ honestStates S P}.Finite := by
    have h1 : {w : ObserverWindow P | w.top ∈ honestStates S P} ⊆ 
        (fun p : State P × (Fin (P.w - 1) → S.Role) => ⟨p.1, p.2⟩) '' (honestStates S P ×ˢ (univ : Set (Fin (P.w - 1) → S.Role))) := by
      rintro ⟨top, roles⟩ ht
      exact ⟨(top, roles), ⟨ht, trivial⟩, rfl⟩
    haveI : Fintype (Fin (P.w - 1) → S.Role) := inferInstance
    have h2 : (univ : Set (Fin (P.w - 1) → S.Role)).Finite := toFinite _
    exact Finite.subset (Finite.image (fun p : State P × (Fin (P.w - 1) → S.Role) => ⟨p.1, p.2⟩) (Finite.prod (states_finite S P) h2)) h1
    
  have hp : ∀ ty : S.ι, {p : FacetName S ty → Option (Packet P) | ∀ F q, p F = some q → q ∈ honestPackets S P}.Finite := by
    intro ty
    let P_set : Set (Option (Packet P)) := insert none (some '' honestPackets S P)
    have hP_fin : P_set.Finite := Finite.insert none (Finite.image some (packets_finite S P))
    have h1 : {p : FacetName S ty → Option (Packet P) | ∀ F q, p F = some q → q ∈ honestPackets S P} ⊆ 
        {p : FacetName S ty → Option (Packet P) | ∀ F, p F ∈ P_set} := by
      intro p hp_ F
      cases h : p F
      · exact mem_insert none _
      · apply mem_insert_of_mem none
        exact mem_image_of_mem _ (hp_ F _ h)
    haveI : Fintype (FacetName S ty) := inferInstance
    have h2 : {p : FacetName S ty → Option (Packet P) | ∀ F, p F ∈ P_set}.Finite := by
      apply Finite.subset (Finite.pi fun _ => hP_fin)
      intro p hp' F _
      exact hp' F
    exact Finite.subset h2 h1

  have hsub : observerAlphabet S P ⊆ 
      ⋃ (ty : S.ι), 
        (fun p : {w : ObserverWindow P | w.top ∈ honestStates S P ∧ w.head.ty = ty} × 
                 {p : FacetName S ty → Option (Packet P) | ∀ F q, p F = some q → q ∈ honestPackets S P} => 
                 { ty := ty, window := p.1.val, head_type := p.1.prop.2, packets := p.2.val } : _ → Observer P) '' univ := by
    rintro ⟨ty, window, h_head, packets⟩ ⟨hw_top, hp_packets⟩
    simp only [mem_iUnion, mem_image, mem_univ, true_and, Subtype.exists, Prod.exists]
    exact ⟨ty, window, ⟨hw_top, h_head⟩, packets, hp_packets, rfl⟩
  apply Finite.subset _ hsub
  have h_union : (⋃ (ty : S.ι), (fun p : {w : ObserverWindow P | w.top ∈ honestStates S P ∧ w.head.ty = ty} × {p : FacetName S ty → Option (Packet P) | ∀ F q, p F = some q → q ∈ honestPackets S P} => { ty := ty, window := p.1.val, head_type := p.1.prop.2, packets := p.2.val } : _ → Observer P) '' univ) = ⋃ (ty ∈ (univ : Set S.ι)), (fun p : {w : ObserverWindow P | w.top ∈ honestStates S P ∧ w.head.ty = ty} × {p : FacetName S ty → Option (Packet P) | ∀ F q, p F = some q → q ∈ honestPackets S P} => { ty := ty, window := p.1.val, head_type := p.1.prop.2, packets := p.2.val } : _ → Observer P) '' univ := by
    ext x
    simp only [mem_iUnion, mem_univ]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, trivial, hi⟩, fun ⟨i, _, hi⟩ => ⟨i, hi⟩⟩
  rw [h_union]
  haveI : Fintype S.ι := inferInstance
  apply Finite.biUnion (toFinite (univ : Set S.ι))
  intro ty _
  apply Finite.image
  have h1 : {w : ObserverWindow P | w.top ∈ honestStates S P ∧ w.head.ty = ty}.Finite := by
    apply Finite.subset hw
    intro x hx
    exact hx.1
  have h2 : {p : FacetName S ty → Option (Packet P) | ∀ F q, p F = some q → q ∈ honestPackets S P}.Finite := hp ty
  haveI : Fintype {w : ObserverWindow P // w.top ∈ honestStates S P ∧ w.head.ty = ty} := h1.fintype
  haveI : Fintype {p : FacetName S ty → Option (Packet P) // ∀ F q, p F = some q → q ∈ honestPackets S P} := h2.fintype
  exact toFinite (univ : Set ({w : ObserverWindow P // w.top ∈ honestStates S P ∧ w.head.ty = ty} × {p : FacetName S ty → Option (Packet P) // ∀ F q, p F = some q → q ∈ honestPackets S P}))
/-- O1, V4 4.1, 8.1: the parsed compressed window recovers every actual ancestor state. -/
theorem parsedWindow_at (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (j : Fin P.w) :
    (ObserverWindow.ofHierarchy (parsedHierarchy Y hY) (parsedState Y hY) q).stateAt j =
      parsedState Y hY ((parsedHierarchy Y hY).ancestor q j.val) := by
  let H := parsedHierarchy Y hY
  let state := parsedState Y hY
  change (ObserverWindow.ofHierarchy H state q).stateAt j = state (H.ancestor q j.val)
  let a := ObserverWindow.ofHierarchy H state q
  have h_descend : ∀ (k : ℕ), k < P.w → a.descend k = state (H.ancestor q (P.w - 1 - k)) := by
    intro k hk
    induction' k with k ih
    · dsimp [ObserverWindow.descend, a, ObserverWindow.ofHierarchy]
    · have hk' : k < P.w - 1 := by omega
      rw [ObserverWindow.descend]
      rw [dif_pos hk']
      rw [ih (by omega)]
      have h_role : a.roles ⟨P.w - 2 - k, by omega⟩ = H.nodeRole (H.ancestor q (P.w - 2 - k)) := by rfl
      rw [h_role]
      let q' := H.ancestor q (P.w - 2 - k)
      have hd : H.parentNode q' = H.ancestor q (P.w - 1 - k) := by
        change H.ancestor q' 1 = H.ancestor q (P.w - 1 - k)
        rw [CoherentHierarchy.ancestor_add]
        congr 2
        omega
      have h_child_eq := parsedState_child Y hY (H.parentNode q') (by
        change 1 ≤ q'.1 + 1
        omega
      ) (H.role q'.1 q'.2) (by
        have h_eq : (H.parent q'.1 q'.2).val.child q'.1 (H.role q'.1 q'.2) = q'.2.val := (H.child_eq q'.1 q'.2).symm
        change (H.parent q'.1 q'.2).val.child q'.1 (H.role q'.1 q'.2) ∈ H.nodes q'.1
        rw [h_eq]
        exact q'.2.2
      )
      have h_nodeRole_eq : H.nodeRole q' = ⟨(H.parentNode q').2.val.ty, H.role q'.1 q'.2⟩ := rfl
      rw [h_nodeRole_eq]
      have h_target : childMap P (state (H.ancestor q (P.w - 1 - k))) ⟨(H.parentNode q').2.val.ty, H.role q'.1 q'.2⟩ = state (H.ancestor q (P.w - 1 - (k + 1))) := by
        have hk_succ : P.w - 1 - (k + 1) = P.w - 2 - k := by omega
        rw [hk_succ]
        change childMap P (state (H.ancestor q (P.w - 1 - k))) ⟨(H.parentNode q').2.val.ty, H.role q'.1 q'.2⟩ = state q'
        rw [← hd]
        have hd2 : H.parentNode q' = ⟨q'.1 + 1, H.parent q'.1 q'.2⟩ := rfl
        have h_child_eq_subst : state ⟨q'.1, ⟨(H.parent q'.1 q'.2).val.child q'.1 (H.role q'.1 q'.2), by
          have h_eq : (H.parent q'.1 q'.2).val.child q'.1 (H.role q'.1 q'.2) = q'.2.val := (H.child_eq q'.1 q'.2).symm
          change (H.parent q'.1 q'.2).val.child q'.1 (H.role q'.1 q'.2) ∈ H.nodes q'.1
          rw [h_eq]
          exact q'.2.2
        ⟩⟩ = childMap P (state (H.parentNode q')) ⟨(H.parentNode q').2.val.ty, H.role q'.1 q'.2⟩ := h_child_eq
        rw [← h_child_eq_subst]
        congr 2
        apply Subtype.ext
        dsimp [CoherentHierarchy.parentNode, CoherentHierarchy.parent]
        change (H.parent q'.1 q'.2).val.child q'.1 (H.role q'.1 q'.2) = q'.2.val
        have h_eq : (H.parent q'.1 q'.2).val.child q'.1 (H.role q'.1 q'.2) = q'.2.val := (H.child_eq q'.1 q'.2).symm
        exact h_eq
      exact h_target
  change a.descend (P.w - 1 - j.val) = state (H.ancestor q j.val)
  have h_j : P.w - 1 - (P.w - 1 - j.val) = j.val := by
    have h_w : j.val < P.w := j.isLt
    omega
  have H_descend := h_descend (P.w - 1 - j.val) (by omega)
  rw [H_descend]
  rw [h_j]
private theorem stateOf_eq_childMap_parent (U : HonestSource S) (P : Params S)
    (q : U.Node) :
    stateOf U P q = childMap P (stateOf U P (U.hierarchy.parentNode q))
      (U.hierarchy.nodeRole q) := by
  have hq : 1 ≤ (U.hierarchy.parentNode q).1 := Nat.le_add_left 1 q.1
  have hc : U.childNode (U.hierarchy.parentNode q) hq
      (U.hierarchy.role q.1 q.2) = q := by
    obtain ⟨n, N, hN⟩ := q
    exact Sigma.subtype_ext rfl (U.hierarchy.child_eq n ⟨N, hN⟩).symm
  have h := childMap_spec U P (U.hierarchy.parentNode q) hq
    (U.hierarchy.role q.1 q.2)
  simpa only [hc] using h

/-- O1, V4 4.1, 8.1: the honest compressed window recovers every ancestor state. -/
theorem honestWindow_at (U : HonestSource S) (P : Params S) (q : U.Node)
    (j : Fin P.w) :
    (ObserverWindow.ofHierarchy U.hierarchy (stateOf U P) q).stateAt j =
      stateOf U P (U.hierarchy.ancestor q j.val) := by
  have hdesc : ∀ (n jv : ℕ), jv + n = P.w - 1 →
      (ObserverWindow.ofHierarchy U.hierarchy (stateOf U P) q).descend n =
        stateOf U P (U.hierarchy.ancestor q jv) := by
    intro n
    induction n with
    | zero =>
      intro jv hjv
      have hj : jv = P.w - 1 := by omega
      subst jv
      rfl
    | succ n ih =>
      intro jv hjv
      have hn : n < P.w - 1 := by omega
      rw [ObserverWindow.descend, dif_pos hn, ih (jv + 1) (by omega)]
      have hidx : P.w - 2 - n = jv := by omega
      have hparent : U.hierarchy.parentNode (U.hierarchy.ancestor q jv) =
          U.hierarchy.ancestor q (jv + 1) := by
        simp only [CoherentHierarchy.ancestor, Function.iterate_succ_apply']
      change childMap P (stateOf U P (U.hierarchy.ancestor q (jv + 1)))
        (U.hierarchy.nodeRole (U.hierarchy.ancestor q (P.w - 2 - n))) = _
      rw [hidx, ← hparent]
      exact (stateOf_eq_childMap_parent U P (U.hierarchy.ancestor q jv)).symm
  exact hdesc (P.w - 1 - j.val) j.val (by have := j.isLt; omega)
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
  dsimp [observerAlphabet, HonestSource.observerOf]
  constructor
  · exact stateOf_mem U P (U.hierarchy.ancestor q (P.w - 1))
  · intro F p hp
    dsimp [HonestSource.facetPacket] at hp
    by_cases hf : U.hierarchy.IsFault q F
    · rw [dif_pos hf] at hp
      cases hp
    · rw [dif_neg hf] at hp
      injection hp with hp_eq
      subst hp_eq
      unfold honestPackets
      exact ⟨U, U.providerOccurrence P q F hf, rfl⟩
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
/-- Step 1 of the V4 proof of `range_raise` (V4 4.3(0)):
Exact-scale transfer preserves the full joint observer data. -/
private lemma dummy (P : Params S)
    {U V : HonestSource S} {a b : ℕ} {J : Iso d} (e : ScaleTailEquiv U V a b J)
    (hab : a % P.L = b % P.L) (q : U.hierarchy.Tail a) :
    V.observerOf P (e.toEquiv q).val = U.observerOf P q.val := by
  sorry

/-- Step 1 of the V4 proof of `range_raise` (V4 4.3(0)):
Exact-scale transfer preserves the full joint observer data. -/
private lemma range_raise_step1_observer_transfer (P : Params S)
    {U V : HonestSource S} {a b : ℕ} {J : Iso d} (e : ScaleTailEquiv U V a b J)
    (hab : a % P.L = b % P.L) (q : U.hierarchy.Tail a) :
    V.observerOf P (e.toEquiv q).val = U.observerOf P q.val := by
  sorry

/-- O3, V4 4.3(0): every joint source observer has a witness strictly above H.
Exact-scale transfer raises a floor-only witness by the residue modulus L and
preserves its entire upward hierarchy, even for arbitrarily high facet providers. -/
theorem range_raise (a : Observer P) (ha : a ∈ jointSourceRange S P) :
    ∃ (U : HonestSource S) (q : U.Node), P.H + 1 ≤ q.1 ∧ U.observerOf P q = a := by
  obtain ⟨U, q, hq, ho⟩ := ha
  by_cases h : P.H + 1 ≤ q.1
  · exact ⟨U, q, h, ho⟩
  · have h_eq : q.1 = P.H := by omega
    rcases q with ⟨q1, q2_val, q2_prop⟩
    cases h_eq
    have hL := P.L_pos
    have h_sub1 : P.H - (P.H + P.L) = 0 := by omega
    have h_sub2 : P.H + P.L - P.H = P.L := by omega
    obtain ⟨V, e, q', heq⟩ := exactScaleTransfer U P.H q2_val q2_prop (P.H + P.L) 1
    have h_le : P.H + 1 ≤ P.H + P.L := by omega
    refine ⟨V, ⟨P.H + P.L, q'⟩, h_le, ?_⟩
    have hq' : (e.toEquiv ⟨⟨P.H, ⟨q2_val, q2_prop⟩⟩, Nat.sub_le _ _⟩).val = ⟨P.H + P.L, q'⟩ :=
      congrArg Subtype.val heq
    rw [← hq']
    have hab : (P.H - (P.H + P.L)) % P.L = (P.H + P.L - P.H) % P.L := by
      rw [h_sub1, h_sub2, Nat.mod_self, Nat.zero_mod]
    have h_trans := range_raise_step1_observer_transfer P e hab ⟨⟨P.H, ⟨q2_val, q2_prop⟩⟩, Nat.sub_le _ _⟩
    rwa [ho] at h_trans
open private exists_childMap_step2_parent exists_childMap_step2_role
  from Enforce.State.State in
/-- Step 1 of the V4 proof of `honest_observer_transition` (V4 4.3(1)(i)):
"the state tuple of C̃ is (D_S(S(Ã),i),S(Ã),…,S(Ã_{m+w-2}))" (Prop. 2.3).
In compressed coordinates, the child's window is the parent's window shifted
down by the role `(A,i)`. -/
private theorem honest_observer_transition_step1_window (U : HonestSource S)
    (P : Params S) (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) :
    ObserverWindow.ofHierarchy U.hierarchy (stateOf U P) (U.childNode q hq i) =
      (ObserverWindow.ofHierarchy U.hierarchy (stateOf U P) q).child
        ⟨q.2.val.ty, i⟩ := by
  have hpar := exists_childMap_step2_parent U q hq i
  have hanc : ∀ n : ℕ, U.hierarchy.ancestor (U.childNode q hq i) (n + 1) =
      U.hierarchy.ancestor q n := by
    intro n
    simp only [CoherentHierarchy.ancestor, Function.iterate_succ_apply, hpar]
  have hw := P.observer_window_bound
  apply ObserverWindow.ext
  · change stateOf U P (U.hierarchy.ancestor (U.childNode q hq i) (P.w - 1)) =
      (ObserverWindow.ofHierarchy U.hierarchy (stateOf U P) q).stateAt
        ⟨P.w - 2, by omega⟩
    rw [honestWindow_at]
    have h := hanc (P.w - 2)
    rw [show P.w - 2 + 1 = P.w - 1 by omega] at h
    rw [h]
  · funext j
    change U.hierarchy.nodeRole (U.hierarchy.ancestor (U.childNode q hq i) j.val) =
      (if h : j.val = 0 then (⟨q.2.val.ty, i⟩ : S.Role) else
        U.hierarchy.nodeRole (U.hierarchy.ancestor q (j.val - 1)))
    by_cases h : j.val = 0
    · rw [dif_pos h, h]
      exact exists_childMap_step2_role U q hq i
    · rw [dif_neg h]
      have h' := hanc (j.val - 1)
      rw [show j.val - 1 + 1 = j.val by omega] at h'
      rw [h']
open private exists_childMap_step2_parent exists_childMap_step4_containment
  from Enforce.State.State in
/-- Step 2 of the V4 proof of `honest_observer_transition` (V4 4.3(1)(ii)):
"for a facet f of C̃ contained in a facet F of Ã: O_f(C̃)=O_F(Ã)" (Lemma 2.6(d)).
The containment is tested in the normalized one-step geometry. -/
private theorem honest_observer_transition_step2_inherited (U : HonestSource S)
    (P : Params S) (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty) (F : FacetName S q.2.val.ty)
    (hF : rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier) :
    U.facetPacket P (U.childNode q hq i) f = U.facetPacket P q F :=
  packet_inherited U P q (U.childNode q hq i) 1
    (by simpa only [CoherentHierarchy.ancestor, Function.iterate_one] using
      exists_childMap_step2_parent U q hq i)
    F f ((exists_childMap_step4_containment U q hq i f.val F.val).mpr hF)
/-- Step 3 of the V4 proof of `honest_observer_transition` (V4 4.3(1)(ii)--(iii)):
"a facet f of C̃ contained in a facet F of Ã" is the same test whether it is
read in `σ A` or in the normalized parent prototype. -/
private theorem honest_observer_transition_step3_test (r : S.Role) (X Y : Set (E d)) :
    placedSet (S.child r.1 r.2).frame X ⊆ S.σ '' Y ↔ rolePlacement r '' X ⊆ Y := by
  have h : rolePlacement r '' X = S.σ.symm '' placedSet (S.child r.1 r.2).frame X := by
    rw [placedSet, Set.image_image]
    rfl
  rw [h]
  constructor
  · rintro hXY _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hXY hx
    rw [← hyx, LinearEquiv.symm_apply_apply]
    exact hy
  · intro hXY x hx
    exact ⟨S.σ.symm x, hXY ⟨x, hx, rfl⟩, LinearEquiv.apply_symm_apply _ _⟩
open private exists_childMap_step2_role exists_childMap_step4_internal_provider
  from Enforce.State.State in
/-- Step 4 of the V4 proof of `honest_observer_transition` (V4 4.3(1)(iii)):
"for a facet f of C̃ internal to Ã (first-generation in Ã)" — Definition 2.5
with `P_b = Ã`: its provider is born in Ã and its canonical incidence `ι(f)`
has parent type `A` and positioned facet `f`. -/
private theorem honest_observer_transition_step4_internal (U : HonestSource S)
    (P : Params S) (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty)
    (hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f)
    (hint : ¬ ∃ F : FacetName S q.2.val.ty,
      rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier) :
    (U.providerOccurrence P (U.childNode q hq i) f hf).birth = q ∧
      (U.recordIncidence P (U.childNode q hq i) f hf).val.ty = q.2.val.ty ∧
      (U.recordIncidence P (U.childNode q hq i) f hf).val.positioned =
        placedSet (S.child q.2.val.ty i).frame f.val.carrier := by
  obtain ⟨hserv, hbirth, ha⟩ := exists_childMap_step4_internal_provider U q hq i f hf hint
  have hfirst : (U.hierarchy.firstProvider (U.childNode q hq i) f hf).2.val = f.val := by
    obtain ⟨hsub, ht⟩ := U.hierarchy.stratumMap_facet _ f hf (facetCell f) rfl
    exact ht.symm.trans (U.hierarchy.stratumMap_age_one _ f hf ha (facetCell f) hsub)
  let a := U.hierarchy.providerIncidence (U.childNode q hq i) f hf
  have haspec := U.hierarchy.providerIncidence_spec (U.childNode q hq i) f hf
  have harole : (⟨a.ty, a.left⟩ : S.Role) = ⟨q.2.val.ty, i⟩ :=
    haspec.2.1.trans ((congrArg U.hierarchy.nodeRole hserv).trans
      (exists_childMap_step2_role U q hq i))
  have hafacet : a.leftFacet.val = f.val := haspec.2.2.1.trans hfirst
  have hc := P.canonical_spec a
  refine ⟨hbirth, ?_, ?_⟩
  · exact hc.1.symm.trans (congrArg Sigma.fst harole)
  · refine hc.2.symm.trans ?_
    change placedSet (S.child a.ty a.left).frame a.leftFacet.val.carrier = _
    rw [hafacet, congrArg (fun r : S.Role => (S.child r.1 r.2).frame) harole]
/-- Step 5 of the V4 proof of `honest_observer_transition` (V4 4.3(1)(iii), 8.1):
"O_f(C̃)=(ι(f),μ,(S(Ã_{m+j}))_{j PRESENT}) with μ the mask determined by ι(f) and
α(S(Ã)), all of whose entries are among the w states of Ĵ(Ã)". The compressed
packet of a primitive occurrence is computed by `bornPacket` from the observer
of its birth node. -/
private theorem honest_observer_transition_step5_born (U : HonestSource S)
    (P : Params S) (g : PrimitiveOccurrence U P) :
    (U.observerOf P g.birth).bornPacket g.incidence = some (packetOf U P g) := by
  classical
  have hw := P.observer_window_bound
  have hhead : (U.observerOf P g.birth).window.head = stateOf U P g.birth :=
    honestWindow_at U P g.birth ⟨0, by omega⟩
  have hslots : Finset.univ.filter
      (packetMask P g.incidence (U.observerOf P g.birth).window.head) =
      presentSlots U P g := by
    ext j
    simp only [presentSlots, Finset.mem_filter, Finset.mem_univ, true_and, hhead,
      packet_mask_fn U P g j]
  have hne : (Finset.univ.filter
      (packetMask P g.incidence (U.observerOf P g.birth).window.head)).Nonempty := by
    rw [hslots]
    exact presentSlots_nonempty U P g
  have hmax : ∀ (s t : Finset (Fin P.k)) (_ : s = t) (hs : s.Nonempty) (ht : t.Nonempty),
      s.max' hs = t.max' ht := by
    rintro s t rfl hs ht
    rfl
  have hb1 : ∀ j : Fin P.k, j.val < P.w := fun j => by
    have := j.isLt
    rw [P.w_eq]
    omega
  have hb2 : ∀ (j : Fin P.k) (t : Fin j.val), t.val < P.w - 1 := fun j t => by
    have := j.isLt
    have := t.isLt
    rw [P.w_eq]
    omega
  have key : ∀ j : Fin P.k, j = topSlot U P g →
      some (Packet.mk g.incidence j
        ((U.observerOf P g.birth).window.stateAt ⟨j.val, hb1 j⟩)
        (fun t => (U.observerOf P g.birth).window.roles ⟨t.val, hb2 j t⟩)) =
        some (packetOf U P g) := by
    rintro j rfl
    simp only [packetOf]
    have h : (U.observerOf P g.birth).window.stateAt ⟨(topSlot U P g).val, hb1 _⟩ =
        stateOf U P (U.hierarchy.ancestor g.birth (topSlot U P g).val) :=
      honestWindow_at U P g.birth _
    rw [h]
    rfl
  unfold Observer.bornPacket
  dsimp only
  rw [dif_pos hne]
  exact key _ (hmax _ _ hslots hne (presentSlots_nonempty U P g))
open private exists_childMap_step4_fault from Enforce.State.State in
/-- Step 6 of the V4 proof of `honest_observer_transition` (V4 4.3(1)(ii)--(iii)):
every facet of C̃ is either contained in a facet of Ã (case (ii)) or internal
to Ã (case (iii)), and in both cases the explicit packet formula is the actual
attached packet. -/
private theorem honest_observer_transition_step6_packet (U : HonestSource S)
    (P : Params S) (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty) :
    U.facetPacket P (U.childNode q hq i) f =
      (U.observerOf P q).childPacket ⟨q.2.val.ty, i⟩ f.val := by
  classical
  unfold Observer.childPacket
  by_cases h1 : ∃ F : FacetName S (U.observerOf P q).ty,
      placedSet (S.child q.2.val.ty i).frame f.val.carrier ⊆ S.σ '' F.val.carrier
  · rw [dif_pos h1]
    exact honest_observer_transition_step2_inherited U P q hq i f _
      ((honest_observer_transition_step3_test ⟨q.2.val.ty, i⟩ _ _).mp
        (Classical.choose_spec h1))
  · rw [dif_neg h1]
    have hint : ¬ ∃ F : FacetName S q.2.val.ty,
        rolePlacement ⟨q.2.val.ty, i⟩ '' f.val.carrier ⊆ F.val.carrier := by
      rintro ⟨F, hF⟩
      exact h1 ⟨F, (honest_observer_transition_step3_test ⟨q.2.val.ty, i⟩ _ _).mpr hF⟩
    have hf : ¬ U.hierarchy.IsFault (U.childNode q hq i) f := by
      rw [exists_childMap_step4_fault U q hq i f]
      rintro ⟨F, hF, _⟩
      exact hint ⟨F, hF⟩
    obtain ⟨hbirth, hty, hpos⟩ :=
      honest_observer_transition_step4_internal U P q hq i f hf hint
    have hι : ∃ ι : P.Incidence, ι.val.ty = (U.observerOf P q).ty ∧
        ι.val.positioned = placedSet (S.child q.2.val.ty i).frame f.val.carrier :=
      ⟨_, hty, hpos⟩
    rw [dif_pos hι]
    have hchoose : Classical.choose hι = U.recordIncidence P (U.childNode q hq i) f hf := by
      obtain ⟨h1', h2'⟩ := Classical.choose_spec hι
      exact (P.incidence_complete (Classical.choose hι).val).unique ⟨rfl, rfl⟩
        ⟨h1'.trans hty.symm, h2'.trans hpos.symm⟩
    rw [hchoose]
    have hb := honest_observer_transition_step5_born U P
      (U.providerOccurrence P (U.childNode q hq i) f hf)
    rw [hbirth] at hb
    unfold HonestSource.facetPacket
    rw [dif_neg hf]
    exact hb.symm
/-- O3, V4 4.3(1): the explicit transition computes every honest child's observer.
The height hypothesis places both observers in the joint source range. -/
theorem honest_observer_transition (U : HonestSource S) (P : Params S) (q : U.Node)
    (hq : P.H + 1 ≤ q.1) (i : S.I q.2.val.ty) :
    U.observerOf P (U.childNode q (by omega) i) =
      (U.observerOf P q).transition ⟨q.2.val.ty, i⟩ := by
  classical
  have hq1 : 1 ≤ q.1 := by omega
  have hwin := honest_observer_transition_step1_window U P q hq1 i
  have hhead : ((U.observerOf P q).window.child ⟨q.2.val.ty, i⟩).head.ty =
      (S.child q.2.val.ty i).ty := by
    change ((ObserverWindow.ofHierarchy U.hierarchy (stateOf U P) q).child
      ⟨q.2.val.ty, i⟩).head.ty = _
    rw [← hwin]
    exact honestWindow_type U P (U.childNode q hq1 i)
  have hcond : (⟨q.2.val.ty, i⟩ : S.Role).1 = (U.observerOf P q).ty ∧
      ((U.observerOf P q).window.child ⟨q.2.val.ty, i⟩).head.ty =
        (S.child (⟨q.2.val.ty, i⟩ : S.Role).1 (⟨q.2.val.ty, i⟩ : S.Role).2).ty :=
    ⟨rfl, hhead⟩
  unfold Observer.transition
  dsimp only
  rw [dif_pos hcond]
  apply Observer.ext
  · rfl
  · exact hwin
  · apply heq_of_eq
    funext f
    exact honest_observer_transition_step6_packet U P q hq1 i f
/-- O3, V4 4.3(0),(1): the joint source range is forward closed under the
explicit transition, with the prescribed child type. Floor-only witnesses are
raised before taking children, rather than assumed to have children above H. -/
theorem range_forward_closed (a : Observer P) (ha : a ∈ jointSourceRange S P)
    (i : S.I a.ty) :
    a.transition ⟨a.ty, i⟩ ∈ jointSourceRange S P ∧
      (a.transition ⟨a.ty, i⟩).ty = (S.child a.ty i).ty := by
  obtain ⟨U, q, hq, ho⟩ := range_raise a ha
  subst ho
  have H2 := honest_observer_transition U P q hq i
  constructor
  · change (U.observerOf P q).transition ⟨q.2.val.ty, i⟩ ∈ _
    rw [← H2]
    have hq_pos : 1 ≤ q.1 := by omega
    have h_child_height : (U.childNode q hq_pos i).1 = q.1 - 1 := rfl
    have hc : P.H ≤ (U.childNode q hq_pos i).1 := by omega
    exact honestObserver_mem_range U P (U.childNode q hq_pos i) hc
  · change ((U.observerOf P q).transition ⟨q.2.val.ty, i⟩).ty = _
    rw [← H2]
    rfl
/-- O4/O6, V4 4.4, 4.6: an actual prescribed child of a parsed positive-height node. -/
def parsedChild (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) :
    (parsedHierarchy Y hY).Node :=
  ⟨q.1 - 1, ⟨q.2.val.child (q.1 - 1) i,
    (parsedHierarchy Y hY).children_mem (q.1 - 1) q.2.val
      (by simpa only [Nat.sub_add_cancel hq] using q.2.property) i⟩⟩
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 1 of the V4 4.2 proof):
"fixed by position". Equal heights and frames identify hierarchy nodes. -/
private theorem observer_transition_aux_step1_node_eq {T : Tiling S}
    (H : CoherentHierarchy S T) {n m : ℕ} {N M : FramedNode S}
    (hn : N ∈ H.nodes n) (hm : M ∈ H.nodes m) (h : n = m) (hNM : N = M) :
    (⟨n, ⟨N, hn⟩⟩ : H.Node) = ⟨m, ⟨M, hm⟩⟩ := by
  cases h
  cases hNM
  rfl
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 1 of the V4 4.2 proof):
"the K-ancestor B_t of t lies inside A". The parent of a prescribed child is its root. -/
private theorem observer_transition_aux_step1_parent {T : Tiling S}
    (H : CoherentHierarchy S T) (n : ℕ) (N : FramedNode S)
    (hN : N ∈ H.nodes (n + 1)) (i : S.I N.ty)
    (hc : N.child n i ∈ H.nodes n) :
    H.parentNode ⟨n, ⟨N.child n i, hc⟩⟩ = ⟨n + 1, ⟨N, hN⟩⟩ := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact (H.parent_unique n _ N hN ⟨i, rfl⟩).symm
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 1 of the V4 4.2 proof):
"type and frame (fixed)". The affine prototype frame obeys the child equation. -/
private theorem observer_transition_aux_step1_child_frame (N : FramedNode S)
    (n : ℕ) (i : S.I N.ty) :
    (N.child n i).prototypeFrame n =
      (rolePlacement (⟨N.ty, i⟩ : S.Role)).trans (N.prototypeFrame (n + 1)) := by
  apply AffineEquiv.ext
  intro x
  change N.frame (S.placeChild n i ((S.σ ^ n) x)) =
    N.frame ((S.σ ^ (n + 1)) (S.σ.symm ((S.child N.ty i).frame x)))
  congr 1
  rw [S.placeChild_apply]
  simp [linearConj, Child.frame, rigidMotion, pow_succ, zpow_neg,
    LinearEquiv.mul_apply, ← map_add]
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 1 of the V4 4.2 proof):
"i_t ... (fixed by position)". Distinct roles have disjoint nonempty interiors. -/
private theorem observer_transition_aux_step1_role_injective (N : FramedNode S) (n : ℕ) :
    Function.Injective (N.child n) := by
  intro i j h
  have hty : (S.child N.ty i).ty = (S.child N.ty j).ty := congrArg FramedNode.ty h
  have he := congrArg (fun M : FramedNode S => M.prototypeFrame n) h
  dsimp only at he
  rw [observer_transition_aux_step1_child_frame, observer_transition_aux_step1_child_frame] at he
  have hframe : (S.child N.ty i).frame = (S.child N.ty j).frame := by
    apply AffineIsometryEquiv.ext
    intro x
    have hx := congrArg (fun e : E d ≃ᵃ[ℝ] E d => e x) he
    exact S.σ.symm.injective ((N.prototypeFrame (n + 1)).injective hx)
  by_contra hij
  have hd := S.children_disjoint N.ty hij
  dsimp only at hd
  rw [hty, hframe] at hd
  have hn : (interior (placedSet (S.child N.ty j).frame
      (S.proto (S.child N.ty j).ty).carrier)).Nonempty := by
    change (interior ((S.child N.ty j).frame.toHomeomorph ''
      (S.proto (S.child N.ty j).ty).carrier)).Nonempty
    rw [← Homeomorph.image_interior]
    exact (S.proto (S.child N.ty j).ty).interior_nonempty.image _
  obtain ⟨x, hx⟩ := hn
  exact Set.disjoint_left.mp hd hx hx
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 1 of the V4 4.2 proof):
"i_t ... (fixed by position)". A prescribed child's hierarchy role is its index. -/
private theorem observer_transition_aux_step1_role {T : Tiling S}
    (H : CoherentHierarchy S T) (n : ℕ) (N : FramedNode S)
    (hN : N ∈ H.nodes (n + 1)) (i : S.I N.ty) (hc : N.child n i ∈ H.nodes n) :
    H.nodeRole ⟨n, ⟨N.child n i, hc⟩⟩ = ⟨N.ty, i⟩ := by
  have hp : (H.parent n ⟨N.child n i, hc⟩).val = N :=
    (H.parent_unique n _ N hN ⟨i, rfl⟩).symm
  have he := H.child_eq n ⟨N.child n i, hc⟩
  have aux (M : FramedNode S) (j : S.I M.ty) (hM : M = N)
      (h : N.child n i = M.child n j) : (⟨M.ty, j⟩ : S.Role) = ⟨N.ty, i⟩ := by
    subst M
    exact congrArg (Sigma.mk N.ty) ((observer_transition_aux_step1_role_injective N n h).symm)
  exact aux _ _ hp he
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 2 of the V4 4.2 proof):
"all listed in Ĵ(A)". The compressed window shifts using its actual parent
and role; the highest new state is the old offset w-2. -/
private theorem observer_transition_aux_step2_window {T : Tiling S}
    (H : CoherentHierarchy S T) (state : H.Node → State P) (c q : H.Node)
    (r : S.Role) (hp : H.parentNode c = q) (hr : H.nodeRole c = r)
    (hat : (ObserverWindow.ofHierarchy H state q).stateAt
      ⟨P.w - 2, by have := P.observer_window_bound; omega⟩ =
        state (H.ancestor q (P.w - 2))) :
    ObserverWindow.ofHierarchy H state c = (ObserverWindow.ofHierarchy H state q).child r := by
  apply ObserverWindow.ext
  · change state (H.ancestor c (P.w - 1)) =
      (ObserverWindow.ofHierarchy H state q).stateAt _
    rw [hat]
    have hw : P.w - 1 = P.w - 2 + 1 := by have := P.observer_window_bound; omega
    rw [hw]
    simp only [CoherentHierarchy.ancestor, Function.iterate_succ_apply, hp]
  · funext j
    change H.nodeRole (H.ancestor c j.val) =
      if hj : j.val = 0 then r else H.nodeRole (H.ancestor q (j.val - 1))
    by_cases hj : j.val = 0
    · simp only [hj, dif_pos, CoherentHierarchy.ancestor, Function.iterate_zero, id_eq, hr]
    · rw [dif_neg hj]
      have he : H.ancestor c j.val = H.ancestor q (j.val - 1) := by
        conv_lhs => rw [show j.val = (j.val - 1) + 1 by omega]
        simp only [CoherentHierarchy.ancestor, Function.iterate_succ_apply, hp]
      rw [he]
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 2 of the V4 4.2 proof):
"the attached packet is O_F(A)". Inherited containment is checked in the
fixed first-generation coordinates. -/
private theorem observer_transition_aux_step2_containment (N : FramedNode S)
    (n : ℕ) (i : S.I N.ty) (f F : Cell d) :
    (N.child n i).cell n f ⊆ N.cell (n + 1) F ↔
      placedSet (S.child N.ty i).frame f.carrier ⊆ S.σ '' F.carrier := by
  change (N.child n i).prototypeFrame n '' f.carrier ⊆
    N.prototypeFrame (n + 1) '' F.carrier ↔ _
  rw [observer_transition_aux_step1_child_frame]
  change (N.prototypeFrame (n + 1) ∘ rolePlacement (⟨N.ty, i⟩ : S.Role)) ''
    f.carrier ⊆ N.prototypeFrame (n + 1) '' F.carrier ↔ _
  rw [Set.image_comp, Set.image_subset_image_iff (N.prototypeFrame (n + 1)).injective]
  change (S.σ.symm ∘ (S.child N.ty i).frame) '' f.carrier ⊆ F.carrier ↔ _
  rw [Set.image_comp]
  constructor
  · intro h x hx
    exact ⟨S.σ.symm x, h ⟨x, hx, rfl⟩, S.σ.apply_symm_apply x⟩
  · rintro h x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, he⟩ := h hy
    simpa only [← he, S.σ.symm_apply_apply] using hz
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 2 of the V4 4.2 proof):
"μ determined by ι(g) and ... S(P_b)". An honest compressed packet is exactly
the birth computation when the window supplies its highest state and roles. -/
private theorem observer_transition_aux_step2_born_eq (a : Observer P) (p : Packet P)
    (hp : p ∈ honestPackets S P) (hh : p.head = a.window.head)
    (hs : p.sstar = a.window.stateAt
      ⟨p.jstar.val, by have := p.jstar.isLt; rw [P.w_eq]; exact this⟩)
    (hr : ∀ j : Fin p.jstar.val, p.roles j =
      a.window.roles ⟨j.val, by have := p.jstar.isLt; have := j.isLt; rw [P.w_eq]; omega⟩) :
    a.bornPacket p.incidence = some p := by
  classical
  let slots := Finset.univ.filter (packetMask P p.incidence a.window.head)
  have hmem (j : Fin P.k) : j ∈ slots ↔ p.mask j := by
    simp only [slots, Finset.mem_filter, Finset.mem_univ, true_and, Packet.mask, hh]
  have hadm := honest_packet_admissible P p hp
  have hn : slots.Nonempty := ⟨p.jstar, (hmem _).mpr hadm.2.2.1⟩
  have hmax : slots.max' hn = p.jstar := by
    apply le_antisymm
    · exact Finset.max'_le _ _ _ (fun j hj => hadm.2.2.2.1 j ((hmem j).mp hj))
    · exact Finset.le_max' _ _ ((hmem _).mpr hadm.2.2.1)
  have hbuild (j : Fin P.k) (hj : j = p.jstar) :
      ({ incidence := p.incidence
         jstar := j
         sstar := a.window.stateAt ⟨j.val, by rw [P.w_eq]; exact j.isLt⟩
         roles := fun t => a.window.roles ⟨t.val, by
           have := t.isLt; have := j.isLt; rw [P.w_eq]; omega⟩ } : Packet P) = p := by
    cases hj
    cases p with
    | mk incidence jstar sstar roles =>
        dsimp only at hs hr ⊢
        congr 1
        · exact hs.symm
        · funext j
          exact (hr j).symm
  unfold Observer.bornPacket
  change (if h : slots.Nonempty then some _ else none) = some p
  rw [dif_pos hn]
  exact congrArg some (hbuild (slots.max' hn) hmax)
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 2 of the V4 4.2 proof):
"by W4 (Theorem 3.13 in Y)". Calibration identifies the entire compressed
primitive packet, including roles and the maximum PRESENT slot. -/
private theorem observer_transition_aux_step2_output_born
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Parser.BornFacet P) (hg : g.birth ∈ (parsedHierarchy Y hY).nodes g.height) :
    (observerOf Y hY (g.hierarchyBirth (parsedHierarchy Y hY) hg)).bornPacket g.incidence =
      parsedPrimitivePacket Y hY g hg := by
  obtain ⟨hl, hr, _, p, hp, hhonest, hinc, hhead, hslots⟩ := calibration_W4 Y hY g hg
  have hread : parsedPrimitivePacket Y hY g hg = some p := hp
  rw [hread, ← hinc]
  apply observer_transition_aux_step2_born_eq _ p hhonest
  · exact hhead.trans (parsedWindow_at Y hY (g.hierarchyBirth (parsedHierarchy Y hY) hg)
      ⟨0, by have := P.observer_window_bound; omega⟩).symm
  · have ht := (packet_top_spec P p hhonest).1
    have hm := (honest_packet_admissible P p hhonest).2.2.1
    have hs := (hslots p.jstar).2 hm
    have he := Option.some.inj (ht.symm.trans hs)
    exact he.trans (parsedWindow_at Y hY (g.hierarchyBirth (parsedHierarchy Y hY) hg)
      ⟨p.jstar.val, by have := p.jstar.isLt; rw [P.w_eq]; exact this⟩).symm
  · intro j
    rw [packet_roles_from_head P p hhonest j, hhead,
      parsedState_address Y hY (g.hierarchyBirth (parsedHierarchy Y hY) hg)
        ⟨j.val, lt_trans j.isLt p.jstar.isLt⟩]
    rfl
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 2 of the V4 4.2 proof):
"which g ... is determined by the position". Canonical incidences of the
same parent type and positioned facet coincide. -/
private theorem observer_transition_aux_step2_incidence_eq (ι η : P.Incidence)
    (ht : ι.val.ty = η.val.ty) (hp : ι.val.positioned = η.val.positioned) : ι = η :=
  (P.canonical_idempotent ι).symm.trans (P.canonical_unique ι.val η ⟨ht, hp⟩)
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 2 of the V4 4.2 proof):
"which g, P_b ... is determined by the position". Equality of actual child
and primitive carriers is equality in first-generation coordinates. -/
private theorem observer_transition_aux_step2_positioned (N : FramedNode S)
    (n : ℕ) (i : S.I N.ty) (f : Cell d) (ι : P.Incidence)
    (h : P.incidencePlacement N (n + 1) ι '' ι.val.leftFacet.val.carrier =
      (N.child n i).cell n f) :
    ι.val.positioned = placedSet (S.child N.ty i).frame f.carrier := by
  apply Set.image_injective.mpr S.σ.symm.injective
  apply Set.image_injective.mpr (N.prototypeFrame (n + 1)).injective
  rw [FramedNode.cell, observer_transition_aux_step1_child_frame] at h
  simpa only [Params.incidencePlacement, PrimitiveIncidence.positioned, rolePlacement,
    placedSet, Set.image_image, AffineEquiv.coe_trans, LinearEquiv.coe_toAffineEquiv,
    AffineIsometryEquiv.coe_toAffineEquiv, Function.comp_def] using h
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 1 of the V4 4.2 proof):
"fixed subdivision geometry". At native height the conjugated child frame is
the original prescribed isometry. -/
private theorem observer_transition_aux_step1_place_zero (A : S.ι) (i : S.I A) :
    S.placeChild 0 i = (S.child A i).frame := by
  apply AffineIsometryEquiv.ext
  intro x
  simp [SubstSystem.placeChild_apply, linearConj, Child.frame, rigidMotion]
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 1 of the V4 4.2 proof):
"which ... F is determined by the position". A cell's carrier fixes its
dimension and hence its full cell name. -/
private theorem observer_transition_aux_step1_cell_eq (e f : Cell d)
    (h : e.carrier = f.carrier) : e = f := by
  rcases e with ⟨K, j, hj⟩
  rcases f with ⟨L, k, hk⟩
  cases h
  have hjk : j = k := hj.dimension.symm.trans hk.dimension
  cases hjk
  rfl
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 2 of the V4 4.2 proof):
"either in a primitive facet g ... or in a facet F of A". An internal
first-generation facet has an honest age-one record in the child state. -/
private theorem observer_transition_aux_step2_internal_record
    (s : State P) (hs : s ∈ honestStates S P) (r : S.Role)
    (hr : s.address ⟨0, P.k_pos⟩ = r) (f : FacetName S s.ty)
    (hb : ¬ ∃ F : FacetName S r.1,
      placedSet (S.child r.1 r.2).frame f.val.carrier ⊆ S.σ '' F.val.carrier) :
    ∃ R : FacetRecord P, s.facetRecord f = some R ∧ AgeOneRecord s R := by
  let N : FramedNode S := ⟨r.1, AffineIsometryEquiv.refl ℝ (E d)⟩
  have ht : (S.child r.1 r.2).ty = s.ty := by rw [← hr]; exact s.address_start
  let f' : FacetName S (N.child 0 r.2).ty := ⟨f.val, by
    change f.val ∈ (S.cx (S.child r.1 r.2).ty).facets
    rw [ht]
    exact f.property⟩
  have hc (e : Cell d) : (N.child 0 r.2).cell 0 e =
      placedSet (S.child r.1 r.2).frame e.carrier := by
    simp [FramedNode.cell, FramedNode.prototypeFrame, FramedNode.child,
      observer_transition_aux_step1_place_zero, N, placedSet]
  have hF (e : Cell d) : N.cell 1 e = S.σ '' e.carrier := by
    simp [FramedNode.cell, FramedNode.prototypeFrame, N]
  have hint : s.InternalFacet f := by
    rcases facet_dichotomy N (N.child 0 r.2) 1 0
      (Parser.child_descendant N 0 r.2) f' with ⟨F, hF', _⟩ | hi
    · exact False.elim (hb ⟨F, by simpa only [hc, hF] using hF'⟩)
    · unfold State.InternalFacet
      rw [hr]
      simpa [hc, FramedNode.carrier, N, placedSet] using hi
  exact (state_semantics_a P s hs f).1.mp hint
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 2 of the V4 4.2 proof):
"which g ... is determined by the position". Both canonical side names
refer to the same positioned primitive facet. -/
private theorem observer_transition_aux_step2_side_positioned (ι : P.Incidence) (b : Bool) :
    ι.val.positioned = placedSet
      (S.child (ι.val.sideRole b).1 (ι.val.sideRole b).2).frame
      (ι.val.sideFacet b).val.carrier := by
  cases b
  · rfl
  · exact ι.val.paired
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 2 of the V4 4.2 proof):
"which g, P_b ... is determined by the position". Honest age-one semantics
identify the canonical side, including its actual facet name. -/
private theorem observer_transition_aux_step2_record_side
    (s : State P) (r : S.Role) (hr : s.address ⟨0, P.k_pos⟩ = r)
    (f : FacetName S s.ty) (R : FacetRecord P) (hR : s.facetRecord f = some R)
    (hA : AgeOneRecord s R) :
    R.incidence.val.sideRole R.sideIndex = r ∧
      R.incidence.val.positioned = placedSet (S.child r.1 r.2).frame f.val.carrier ∧
      (R.incidence.val.sideFacet R.sideIndex).val = f.val := by
  have hs : R.servingRole = r := hA.2.1.trans hr
  have hrole : R.incidence.val.sideRole R.sideIndex = r := R.side_eq.symm.trans hs
  have hpos : R.incidence.val.positioned = placedSet (S.child r.1 r.2).frame f.val.carrier := by
    rw [hA.2.2.1, (s.facetRecord_valid f R hR).2,
      congrArg (fun t : S.Role => (S.child t.1 t.2).frame) hs]
  refine ⟨hrole, hpos, ?_⟩
  apply observer_transition_aux_step1_cell_eq
  apply Set.image_injective.mpr (S.child r.1 r.2).frame.injective
  have hside := observer_transition_aux_step2_side_positioned R.incidence R.sideIndex
  rw [hrole] at hside
  exact hside.symm.trans hpos
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 2 of the V4 4.2 proof):
"the attached packet". Equal hierarchy nodes and equal facet names give
the same parsed packet; membership proofs carry no extra data. -/
private theorem observer_transition_aux_step2_output_packet_congr
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q q' : (parsedHierarchy Y hY).Node) (he : q = q')
    (f : FacetName S q.2.val.ty) (f' : FacetName S q'.2.val.ty) (hf : f.val = f'.val) :
    parsedFacetPacket Y hY q f = parsedFacetPacket Y hY q' f' := by
  cases he
  have hff : f = f' := Subtype.ext hf
  cases hff
  rfl
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 2 of the V4 4.2 proof):
"by W4 (Theorem 3.13 in Y)" or "O_F(A) by (I5)".
One output child facet is computed without assigning providers to faults. -/
private theorem observer_transition_aux_step2_output_packet
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (parsedChild Y hY q hq i).2.val.ty) :
    parsedFacetPacket Y hY (parsedChild Y hY q hq i) f =
      (observerOf Y hY q).childPacket ⟨q.2.val.ty, i⟩ f.val := by
  classical
  rcases q with ⟨m, N, hN⟩
  cases m with
  | zero => change 1 ≤ 0 at hq; omega
  | succ n =>
      let H := parsedHierarchy Y hY
      let hc := H.children_mem n N hN i
      let c : H.Node := ⟨n, ⟨N.child n i, hc⟩⟩
      let q : H.Node := ⟨n + 1, ⟨N, hN⟩⟩
      change parsedFacetPacket Y hY c f = (observerOf Y hY q).childPacket ⟨N.ty, i⟩ f.val
      by_cases hb : ∃ F : FacetName S N.ty,
          placedSet (S.child N.ty i).frame f.val.carrier ⊆ S.σ '' F.val.carrier
      · unfold Observer.childPacket
        dsimp only [observerOf]
        rw [dif_pos hb]
        symm
        apply parsedFacetPacket_inherited Y hY q c
          (Parser.child_descendant N n i) (Classical.choose hb) f
        exact (observer_transition_aux_step2_containment N n i f.val _).mpr (Classical.choose_spec hb)
      · let s := parsedState Y hY c
        have hsty : s.ty = (S.child N.ty i).ty := (parsedState_type_residue Y hY c).2.1
        let fs : FacetName S s.ty := ⟨f.val, by rw [hsty]; exact f.property⟩
        have hrole : s.address ⟨0, P.k_pos⟩ = (⟨N.ty, i⟩ : S.Role) :=
          (parsedState_role Y hY c).trans (observer_transition_aux_step1_role H n N hN i hc)
        obtain ⟨R, hR, hA⟩ := observer_transition_aux_step2_internal_record s
          (parsedState_type_residue Y hY c).1 ⟨N.ty, i⟩ hrole fs hb
        obtain ⟨hside, hpos, hfacet⟩ := observer_transition_aux_step2_record_side s
          ⟨N.ty, i⟩ hrole fs R hR hA
        have hty : R.incidence.val.ty = N.ty := congrArg Sigma.fst hside
        let g : Parser.BornFacet P :=
          ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), N, R.incidence, hty⟩
        have hex : ∃ ι : P.Incidence, ι.val.ty = N.ty ∧
            ι.val.positioned = placedSet (S.child N.ty i).frame f.val.carrier :=
          ⟨R.incidence, hty, hpos⟩
        unfold Observer.childPacket
        dsimp only [observerOf]
        rw [dif_neg hb, dif_pos hex]
        have he : Classical.choose hex = R.incidence :=
          observer_transition_aux_step2_incidence_eq _ _
            ((Classical.choose_spec hex).1.trans hty.symm)
            ((Classical.choose_spec hex).2.trans hpos.symm)
        rw [he]
        change parsedFacetPacket Y hY c f = (observerOf Y hY q).bornPacket g.incidence
        have hborn := observer_transition_aux_step2_output_born Y hY g hN
        change (observerOf Y hY q).bornPacket g.incidence = parsedPrimitivePacket Y hY g hN at hborn
        rw [hborn]
        cases hbside : R.sideIndex with
        | false =>
            have hnode : g.leftNode = N.child n i := by
              have he := congrArg (fun r : S.Role =>
                (⟨r.1, N.frame⟩ : FramedNode S).child n r.2) hside
              simpa only [hbside, PrimitiveIncidence.sideRole, PrimitiveIncidence.sideIndex,
                Bool.false_eq_true, ↓reduceIte] using he
            exact observer_transition_aux_step2_output_packet_congr Y hY c
              ⟨g.height - 1, ⟨g.leftNode, g.left_mem H hN⟩⟩
              (observer_transition_aux_step1_node_eq H hc _ rfl hnode.symm) f
              g.incidence.val.leftFacet (by
                have h := hfacet.symm
                rw [hbside] at h
                exact h)
        | true =>
            have hnode : g.rightNode = N.child n i := by
              have he := congrArg (fun r : S.Role =>
                (⟨r.1, N.frame⟩ : FramedNode S).child n r.2) hside
              simpa only [hbside, PrimitiveIncidence.sideRole, PrimitiveIncidence.sideIndex,
                ↓reduceIte] using he
            have hp := observer_transition_aux_step2_output_packet_congr Y hY c
              ⟨g.height - 1, ⟨g.rightNode, g.right_mem H hN⟩⟩
              (observer_transition_aux_step1_node_eq H hc _ rfl hnode.symm) f
              g.incidence.val.rightFacet (by
                have h := hfacet.symm
                rw [hbside] at h
                exact h)
            exact hp.trans (parsedPrimitivePacket_spec Y hY g hN).1.symm
/-- Auxiliary for `observer_transition` (V4 4.4, copied from Step 2 of the V4 4.2 proof):
"by W4 (Theorem 3.13 in Y)" and "the attached packet is O_F(A) by (I5)".
The one-step formula includes certificate-subdivision nodes below the floor. -/
private theorem observer_transition_aux_step2_output_child
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) :
    observerOf Y hY (parsedChild Y hY q hq i) =
      (observerOf Y hY q).transition ⟨q.2.val.ty, i⟩ := by
  rcases q with ⟨m, N, hN⟩
  cases m with
  | zero => change 1 ≤ 0 at hq; omega
  | succ n =>
      let hc := (parsedHierarchy Y hY).children_mem n N hN i
      let c : (parsedHierarchy Y hY).Node := ⟨n, ⟨N.child n i, hc⟩⟩
      let q : (parsedHierarchy Y hY).Node := ⟨n + 1, ⟨N, hN⟩⟩
      have hw := observer_transition_aux_step2_window (parsedHierarchy Y hY) (parsedState Y hY)
        c q ⟨N.ty, i⟩
        (observer_transition_aux_step1_parent (parsedHierarchy Y hY) n N hN i hc)
        (observer_transition_aux_step1_role (parsedHierarchy Y hY) n N hN i hc)
        (parsedWindow_at Y hY q ⟨P.w - 2, by have := P.observer_window_bound; omega⟩)
      have hhead : ((observerOf Y hY q).window.child ⟨N.ty, i⟩).head.ty = (S.child N.ty i).ty := by
        change ((ObserverWindow.ofHierarchy (parsedHierarchy Y hY) (parsedState Y hY) q).child
          ⟨N.ty, i⟩).head.ty = _
        rw [← hw]
        exact parsedWindow_type Y hY c
      change observerOf Y hY c = (observerOf Y hY q).transition ⟨N.ty, i⟩
      unfold Observer.transition
      rw [dif_pos ⟨rfl, hhead⟩]
      apply Observer.ext
      · rfl
      · exact hw
      · apply heq_of_eq
        funext f
        exact observer_transition_aux_step2_output_packet Y hY q hq i f
/-- O4, V4 4.4: exact observer transition in an arbitrary proper output.
This includes certificate nodes below K. W4 calibrates internal births, and I5
copies inherited packets, including NULL and phantom fault packets. -/
theorem observer_transition (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : P.H + 1 ≤ q.1) (i : S.I q.2.val.ty) :
    observerOf Y hY (parsedChild Y hY q (by omega) i) =
      (observerOf Y hY q).transition ⟨q.2.val.ty, i⟩ := by
  exact observer_transition_aux_step2_output_child Y hY q (by omega) i
/-- Step 1 of the V4 proof of `ground_actuality` (V4 4.5): "Let B be the
K-ancestor of A in Y's hierarchy". One more parent step extends an exact
downward address by its top letter, the role of the old ancestor. -/
private theorem ground_actuality_step1_address_extend (h r n : ℕ) (N M : FramedNode S)
    (i : S.I N.ty) (hM : M = N.child n i) (hn : n = h + r) (w : S.RoleWord M.ty r) :
    ∃ w' : S.RoleWord N.ty (r + 1),
      (S.descendantNode N.ty h (r + 1) w').move N.frame =
        (S.descendantNode M.ty h r w).move M.frame := by
  subst hM
  subst hn
  exact ⟨⟨i, w⟩, rfl⟩
/-- Step 1 of the V4 proof of `ground_actuality` (V4 4.5): "Let B be the
K-ancestor of A in Y's hierarchy". Every node sits at an exact downward role-word
address inside its r-th ancestor, in any coherent hierarchy. -/
private theorem ground_actuality_step1_address {T : Tiling S}
    (H : CoherentHierarchy S T) (c : H.Node) (r : ℕ) :
    ∃ w : S.RoleWord (H.ancestor c r).2.val.ty r,
      (S.descendantNode (H.ancestor c r).2.val.ty c.1 r w).move
        (H.ancestor c r).2.val.frame = c.2.val := by
  induction r with
  | zero =>
      refine ⟨(), ?_⟩
      apply FramedNode.ext
      · rfl
      · apply AffineIsometryEquiv.ext
        intro x
        rfl
  | succ r ih =>
      obtain ⟨w, hw⟩ := ih
      have hanc : H.ancestor c (r + 1) = H.parentNode (H.ancestor c r) := by
        rw [← H.ancestor_add c r 1]
        rfl
      rw [hanc]
      obtain ⟨w', hw'⟩ := ground_actuality_step1_address_extend c.1 r (H.ancestor c r).1
        (H.parentNode (H.ancestor c r)).2.val (H.ancestor c r).2.val
        (H.role (H.ancestor c r).1 (H.ancestor c r).2)
        (H.child_eq (H.ancestor c r).1 (H.ancestor c r).2)
        (H.ancestor_height c r) w
      exact ⟨w', hw'.trans hw⟩
/-- Step 1 of the V4 proof of `ground_actuality` (V4 4.5): "Let B be the
K-ancestor of A in Y's hierarchy (a K-block, Theorem 2.17(a))". The ancestor at
height K is a certificate block, and the node is at an exact address inside it. -/
private theorem ground_actuality_step1_K_block (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (c : (parsedHierarchy Y hY).Node) (r : ℕ) (hcr : c.1 + r = P.K) :
    ∃ (B : KBlock Y) (w : S.RoleWord B.certificate.val.ty r),
      (S.descendantNode B.certificate.val.ty c.1 r w).move B.frame = c.2.val := by
  set a := (parsedHierarchy Y hY).ancestor c r with ha_def
  have ha : a.1 = P.K := by
    rw [ha_def, CoherentHierarchy.ancestor_height]
    exact hcr
  have hmem : a.2.val ∈ (parsedHierarchy Y hY).nodes P.K := ha ▸ a.2.property
  have hroot : a.2.val ∈ Set.range (fun B : KBlock Y => B.node) := by
    rw [← (parsedHierarchy_base Y hY).1, ← parsedDecodedLevel_upper Y hY P.K le_rfl,
      parsedHierarchy_nodes]
    exact hmem
  obtain ⟨B, hB⟩ := hroot
  have key : ∀ M : FramedNode S, B.node = M →
      (∃ w : S.RoleWord M.ty r, (S.descendantNode M.ty c.1 r w).move M.frame = c.2.val) →
      ∃ w : S.RoleWord B.certificate.val.ty r,
        (S.descendantNode B.certificate.val.ty c.1 r w).move B.frame = c.2.val := by
    intro M hM h
    subst hM
    exact h
  exact ⟨B, key a.2.val hB (ground_actuality_step1_address (parsedHierarchy Y hY) c r)⟩
/-- Step 2 of the V4 proof of `ground_actuality` (V4 4.5): "the corresponding
node Ã inside B̃". Moving from the frame of B to the frame of B̃ composes frames. -/
private theorem ground_actuality_step2_move (X : FramedNode S) (φ ψ : Iso d) :
    (X.move φ).move (φ.symm.trans ψ) = X.move ψ := by
  apply FramedNode.ext
  · rfl
  · apply AffineIsometryEquiv.ext
    intro x
    simp [FramedNode.move]
/-- Step 2 of the V4 proof of `ground_actuality` (V4 4.5): "fixed by position".
Exact downward addresses invert ancestry (copied from Step 1 of the V4 4.2 proof). -/
private theorem ground_actuality_step2_root_ancestor {T : Tiling S}
    (H : CoherentHierarchy S T) (h r : ℕ) (N : FramedNode S)
    (hN : N ∈ H.nodes (h + r)) (w : S.RoleWord N.ty r)
    (hc : (S.descendantNode N.ty h r w).move N.frame ∈ H.nodes h) :
    H.ancestor ⟨h, ⟨(S.descendantNode N.ty h r w).move N.frame, hc⟩⟩ r =
      ⟨h + r, ⟨N, hN⟩⟩ := by
  induction r generalizing N with
  | zero =>
      simp [CoherentHierarchy.ancestor, SubstSystem.descendantNode, FramedNode.move]
  | succ r ih =>
      have hchild := H.children_mem (h + r) N (by simpa [Nat.add_assoc] using hN) w.1
      have hc' : (S.descendantNode (N.child (h + r) w.1).ty h r w.2).move
          (N.child (h + r) w.1).frame ∈ H.nodes h := by
        have e : (S.descendantNode (N.child (h + r) w.1).ty h r w.2).move
            (N.child (h + r) w.1).frame = (S.descendantNode N.ty h (r + 1) w).move N.frame :=
          rfl
        rw [e]
        exact hc
      have hi := ih (N.child (h + r) w.1) hchild w.2 hc'
      rw [← H.ancestor_add]
      change H.parentNode (H.ancestor _ r) = _
      have he : (⟨h, ⟨(S.descendantNode N.ty h (r + 1) w).move N.frame, hc⟩⟩ :
          H.Node) = ⟨h, ⟨(S.descendantNode (N.child (h + r) w.1).ty h r w.2).move
            (N.child (h + r) w.1).frame, hc'⟩⟩ := rfl
      rw [he, hi]
      exact observer_transition_aux_step1_parent H (h + r) N hN w.1 hchild
/-- Step 2 of the V4 proof of `ground_actuality` (V4 4.5): "inside B".
A node whose ancestor is the K-block B has an exact address inside B. -/
private theorem ground_actuality_step2_block_address (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (B : KBlock Y) (c : (parsedHierarchy Y hY).Node) (s : ℕ)
    (hanc : ((parsedHierarchy Y hY).ancestor c s).2.val = B.node) :
    ∃ w : S.RoleWord B.certificate.val.ty s,
      (S.descendantNode B.certificate.val.ty c.1 s w).move B.frame = c.2.val := by
  have key : ∀ M : FramedNode S, M = B.node →
      (∃ w : S.RoleWord M.ty s, (S.descendantNode M.ty c.1 s w).move M.frame = c.2.val) →
      ∃ w : S.RoleWord B.certificate.val.ty s,
        (S.descendantNode B.certificate.val.ty c.1 s w).move B.frame = c.2.val := by
    intro M hM h
    subst hM
    exact h
  exact key _ hanc (ground_actuality_step1_address (parsedHierarchy Y hY) c s)
/-- Step 2 of the V4 proof of `ground_actuality` (V4 4.5): "the corresponding
node Ã inside B̃". Every node inside B, moved to the frame of B̃, is a source node. -/
private theorem ground_actuality_step2_source_mem (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (B : KBlock Y) (U : HonestSource S) (ψ : Iso d)
    (hN : (⟨B.certificate.val.ty, ψ⟩ : FramedNode S) ∈ U.hierarchy.nodes P.K)
    (c : (parsedHierarchy Y hY).Node) (s : ℕ) (hcs : c.1 + s = P.K)
    (hanc : ((parsedHierarchy Y hY).ancestor c s).2.val = B.node) :
    c.2.val.move (B.frame.symm.trans ψ) ∈ U.hierarchy.nodes c.1 := by
  obtain ⟨w, hw⟩ := ground_actuality_step2_block_address Y hY B c s hanc
  have hs : s ≤ P.K := by omega
  have hm : (S.descendantNode B.certificate.val.ty (P.K - s) s w).move ψ ∈
      U.hierarchy.nodes (P.K - s) :=
    U.descendant_mem ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ s hs w
  have hh : P.K - s = c.1 := by omega
  rw [← hw, ground_actuality_step2_move]
  rw [hh] at hm
  exact hm
/-- Step 2 of the V4 proof of `ground_actuality` (V4 4.5): "same table".
The S-table of a certificate of an honest node lists its descendants' states. -/
private theorem ground_actuality_step2_table (U : HonestSource S) (ψ : Iso d)
    (D : Certificate P) (hN : (⟨D.ty, ψ⟩ : FramedNode S) ∈ U.hierarchy.nodes P.K)
    (hcert : certOf U P ⟨D.ty, ψ⟩ hN = D) (s : ℕ) (hs : s ≤ P.K)
    (w : S.RoleWord D.ty s) :
    D.table s hs w = stateOf U P (U.descendant ⟨P.K, ⟨⟨D.ty, ψ⟩, hN⟩⟩ s hs w) := by
  have aux : ∀ X Z : Certificate P, X = Z → ∀ (h : X.ty = Z.ty) (v : S.RoleWord X.ty s),
      X.table s hs v = Z.table s hs (h ▸ v) := by
    intro X Z e h v
    subst e
    rfl
  exact (aux _ _ hcert rfl w).symm
/-- Step 2 of the V4 proof of `ground_actuality` (V4 4.5): "The states of nodes
inside B are the table entries of D (Lemma 3.2)" (copied from Step 3 of the
V4 4.2 proof). -/
private theorem ground_actuality_step2_output_table
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) (B : KBlock Y)
    (r : ℕ) (hr : r ≤ P.K) (w : S.RoleWord B.certificate.val.ty r) :
    ∃ hc : B.innerNode r hr w ∈ (parsedHierarchy Y hY).nodes (P.K - r),
      B.table r hr w = parsedState Y hY ⟨P.K - r, ⟨B.innerNode r hr w, hc⟩⟩ := by
  obtain ⟨hc, he⟩ := (parsedHierarchy_base Y hY).2 B r hr w
  have hc' : B.innerNode r hr w ∈
      (parsedDecodedLevel Y hY P.K).geometry.nodes (P.K - r) := by
    rw [parsedDecodedLevel_upper Y hY P.K le_rfl]
    exact hc
  have hm : B.innerNode r hr w ∈ (parsedHierarchy Y hY).nodes (P.K - r) := by
    rw [← parsedHierarchy_inner_nodes Y hY P.K (P.K - r) (Nat.sub_le _ _)]
    exact hc'
  refine ⟨hm, ?_⟩
  have hagree := parsedState_agrees Y hY P.K (P.K - r) (B.innerNode r hr w) hc' hm
  have htable : ∀ hc' : B.innerNode r hr w ∈
      (parsedDecodedLevel Y hY P.K).geometry.nodes (P.K - r),
      (parsedDecodedLevel Y hY P.K).stateAt (P.K - r) (B.innerNode r hr w) hc' =
        B.table r hr w := by
    rw [parsedDecodedLevel_upper Y hY P.K le_rfl]
    intro hc'
    exact he
  exact (htable hc').symm.trans hagree
/-- Step 2 of the V4 proof of `ground_actuality` (V4 4.5): "Hence Ĵ(A) equals
Ĵ(Ã) ... (same table)". Corresponding nodes inside B and B̃ have equal states. -/
private theorem ground_actuality_step2_state (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (B : KBlock Y) (U : HonestSource S) (ψ : Iso d)
    (hN : (⟨B.certificate.val.ty, ψ⟩ : FramedNode S) ∈ U.hierarchy.nodes P.K)
    (hcert : certOf U P ⟨B.certificate.val.ty, ψ⟩ hN = B.certificate.val)
    (e : (parsedHierarchy Y hY).Node) (e' : U.Node) (s : ℕ) (hes : e.1 + s = P.K)
    (hanc : ((parsedHierarchy Y hY).ancestor e s).2.val = B.node)
    (h1 : e'.1 = e.1) (h2 : e'.2.val = e.2.val.move (B.frame.symm.trans ψ)) :
    parsedState Y hY e = stateOf U P e' := by
  obtain ⟨w, hw⟩ := ground_actuality_step2_block_address Y hY B e s hanc
  have hs : s ≤ P.K := by omega
  obtain ⟨hm, ht⟩ := ground_actuality_step2_output_table Y hY B s hs w
  have hh : P.K - s = e.1 := by omega
  have hY1 : e = ⟨P.K - s, ⟨B.innerNode s hs w, hm⟩⟩ := by
    obtain ⟨n, E, hE⟩ := e
    apply observer_transition_aux_step1_node_eq (parsedHierarchy Y hY) hE hm hh.symm
    show E = (S.descendantNode B.certificate.val.ty (P.K - s) s w).move B.frame
    rw [hh]
    exact hw.symm
  have hU1 : e' = U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ s hs w := by
    obtain ⟨n, E, hE⟩ := e'
    dsimp only at h1 h2
    apply observer_transition_aux_step1_node_eq U.hierarchy hE _ (h1.trans hh.symm)
    show E = (S.descendantNode B.certificate.val.ty (P.K - s) s w).move ψ
    rw [h2, ← hw, ground_actuality_step2_move, hh]
  rw [hY1, hU1, ← ht]
  exact ground_actuality_step2_table U ψ B.certificate.val hN hcert s hs w
/-- Step 2 of the V4 proof of `ground_actuality` (V4 4.5): "the nodes
A_H, ..., A_{H+w-1} all lie inside B". The parent and role of corresponding
nodes inside B and B̃ correspond. -/
private theorem ground_actuality_step2_parent (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (B : KBlock Y) (U : HonestSource S) (ψ : Iso d)
    (hN : (⟨B.certificate.val.ty, ψ⟩ : FramedNode S) ∈ U.hierarchy.nodes P.K)
    (c : (parsedHierarchy Y hY).Node) (c' : U.Node) (s : ℕ) (hcs : c.1 + 1 + s = P.K)
    (hanc : ((parsedHierarchy Y hY).ancestor
      ((parsedHierarchy Y hY).parentNode c) s).2.val = B.node)
    (h1 : c'.1 = c.1) (h2 : c'.2.val = c.2.val.move (B.frame.symm.trans ψ)) :
    (U.hierarchy.parentNode c').2.val =
        ((parsedHierarchy Y hY).parentNode c).2.val.move (B.frame.symm.trans ψ) ∧
      U.hierarchy.nodeRole c' = (parsedHierarchy Y hY).nodeRole c := by
  have hmem := ground_actuality_step2_source_mem Y hY B U ψ hN
    ((parsedHierarchy Y hY).parentNode c) s hcs hanc
  have hmem' : ((parsedHierarchy Y hY).parentNode c).2.val.move (B.frame.symm.trans ψ) ∈
      U.hierarchy.nodes (c'.1 + 1) := by
    rw [h1]
    exact hmem
  have hchild : c'.2.val = (((parsedHierarchy Y hY).parentNode c).2.val.move
      (B.frame.symm.trans ψ)).child c'.1 ((parsedHierarchy Y hY).role c.1 c.2) := by
    rw [h2, h1, (parsedHierarchy Y hY).child_eq c.1 c.2]
    rfl
  have hpar := U.hierarchy.parent_unique c'.1 c'.2 _ hmem' ⟨_, hchild⟩
  refine ⟨hpar.symm, ?_⟩
  have hc'' : (((parsedHierarchy Y hY).parentNode c).2.val.move
      (B.frame.symm.trans ψ)).child c'.1 ((parsedHierarchy Y hY).role c.1 c.2) ∈
        U.hierarchy.nodes c'.1 := hchild ▸ c'.2.property
  have hnode : c' = ⟨c'.1, ⟨_, hc''⟩⟩ := by
    obtain ⟨n, E, hE⟩ := c'
    exact observer_transition_aux_step1_node_eq U.hierarchy hE hc'' rfl hchild
  rw [hnode, observer_transition_aux_step1_role U.hierarchy c'.1 _ hmem' _ hc'']
  rfl
/-- Step 2 of the V4 proof of `ground_actuality` (V4 4.5): "the nodes
A_H, ..., A_{H+w-1} all lie inside B". Ancestors of corresponding nodes, up to
the height of B, correspond. -/
private theorem ground_actuality_step2_ancestor (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (B : KBlock Y) (U : HonestSource S) (ψ : Iso d)
    (hN : (⟨B.certificate.val.ty, ψ⟩ : FramedNode S) ∈ U.hierarchy.nodes P.K)
    (c : (parsedHierarchy Y hY).Node) (c' : U.Node) (s : ℕ) (hcs : c.1 + s = P.K)
    (hanc : ((parsedHierarchy Y hY).ancestor c s).2.val = B.node)
    (h1 : c'.1 = c.1) (h2 : c'.2.val = c.2.val.move (B.frame.symm.trans ψ))
    (j : ℕ) (hj : j ≤ s) :
    (U.hierarchy.ancestor c' j).2.val =
      ((parsedHierarchy Y hY).ancestor c j).2.val.move (B.frame.symm.trans ψ) := by
  induction j with
  | zero => exact h2
  | succ j ih =>
      have ih := ih (by omega)
      have hYa : (parsedHierarchy Y hY).ancestor c (j + 1) =
          (parsedHierarchy Y hY).parentNode ((parsedHierarchy Y hY).ancestor c j) := by
        rw [← CoherentHierarchy.ancestor_add (parsedHierarchy Y hY) c j 1]
        rfl
      have hUa : U.hierarchy.ancestor c' (j + 1) =
          U.hierarchy.parentNode (U.hierarchy.ancestor c' j) := by
        rw [← U.hierarchy.ancestor_add c' j 1]
        rfl
      have hpa : ((parsedHierarchy Y hY).ancestor
          ((parsedHierarchy Y hY).parentNode ((parsedHierarchy Y hY).ancestor c j))
            (s - (j + 1))).2.val = B.node := by
        rw [← hYa, CoherentHierarchy.ancestor_add,
          show j + 1 + (s - (j + 1)) = s by omega]
        exact hanc
      have hk : ((parsedHierarchy Y hY).ancestor c j).1 + 1 + (s - (j + 1)) = P.K := by
        rw [CoherentHierarchy.ancestor_height]
        omega
      have hh : (U.hierarchy.ancestor c' j).1 = ((parsedHierarchy Y hY).ancestor c j).1 := by
        rw [CoherentHierarchy.ancestor_height, CoherentHierarchy.ancestor_height, h1]
      rw [hYa, hUa]
      exact (ground_actuality_step2_parent Y hY B U ψ hN _ _ (s - (j + 1)) hk hpa hh ih).1
/-- Step 2 of the V4 proof of `ground_actuality` (V4 4.5): "Since K ≥ H+w, the
nodes A=A_H, A_{H+1}, ..., A_{H+w-1} all lie inside B ... The states of nodes
inside B are the table entries of D (Lemma 3.2)". For an inner node of a K-block
at depth r ≥ w, the compressed window (highest state and intervening roles) is
the window of the same-address node below the honest node whose certificate is D. -/
private theorem ground_actuality_step2_window (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (B : KBlock Y) (U : HonestSource S) (ψ : Iso d)
    (hN : (⟨B.certificate.val.ty, ψ⟩ : FramedNode S) ∈ U.hierarchy.nodes P.K)
    (hcert : certOf U P ⟨B.certificate.val.ty, ψ⟩ hN = B.certificate.val)
    (r : ℕ) (hr : r ≤ P.K) (hwr : P.w ≤ r) (w : S.RoleWord B.certificate.val.ty r)
    (hc : B.innerNode r hr w ∈ (parsedHierarchy Y hY).nodes (P.K - r)) :
    ObserverWindow.ofHierarchy (parsedHierarchy Y hY) (parsedState Y hY)
        ⟨P.K - r, ⟨B.innerNode r hr w, hc⟩⟩ =
      ObserverWindow.ofHierarchy U.hierarchy (stateOf U P)
        (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w) := by
  have hBK : B.node ∈ (parsedHierarchy Y hY).nodes P.K := by
    have h0 : B.node ∈ Set.range (fun B : KBlock Y => B.node) := ⟨B, rfl⟩
    rw [← (parsedHierarchy_base Y hY).1, ← parsedDecodedLevel_upper Y hY P.K le_rfl,
      parsedHierarchy_nodes] at h0
    exact h0
  have hBK' : B.node ∈ (parsedHierarchy Y hY).nodes (P.K - r + r) := by
    rw [Nat.sub_add_cancel hr]
    exact hBK
  have hanc0 := ground_actuality_step2_root_ancestor (parsedHierarchy Y hY) (P.K - r) r
    B.node hBK' w hc
  have hanc : ((parsedHierarchy Y hY).ancestor
      ⟨P.K - r, ⟨B.innerNode r hr w, hc⟩⟩ r).2.val = B.node := by
    have e : (⟨P.K - r, ⟨B.innerNode r hr w, hc⟩⟩ : (parsedHierarchy Y hY).Node) =
        ⟨P.K - r, ⟨(S.descendantNode B.node.ty (P.K - r) r w).move B.node.frame, hc⟩⟩ :=
      rfl
    rw [e, hanc0]
  have h2 : (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w).2.val =
      (B.innerNode r hr w).move (B.frame.symm.trans ψ) :=
    (ground_actuality_step2_move _ _ _).symm
  have hcs : (P.K - r) + r = P.K := Nat.sub_add_cancel hr
  have hcorr := ground_actuality_step2_ancestor Y hY B U ψ hN
    ⟨P.K - r, ⟨B.innerNode r hr w, hc⟩⟩
    (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w) r hcs hanc rfl h2
  have hw3 := P.observer_window_bound
  apply ObserverWindow.ext
  · show parsedState Y hY ((parsedHierarchy Y hY).ancestor
        ⟨P.K - r, ⟨B.innerNode r hr w, hc⟩⟩ (P.w - 1)) =
      stateOf U P (U.hierarchy.ancestor
        (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w) (P.w - 1))
    apply ground_actuality_step2_state Y hY B U ψ hN hcert _ _ (r - (P.w - 1))
    · rw [CoherentHierarchy.ancestor_height]
      dsimp only
      omega
    · rw [CoherentHierarchy.ancestor_add, show P.w - 1 + (r - (P.w - 1)) = r by omega]
      exact hanc
    · rw [CoherentHierarchy.ancestor_height, CoherentHierarchy.ancestor_height]
      rfl
    · exact hcorr (P.w - 1) (by omega)
  · funext j
    show (parsedHierarchy Y hY).nodeRole ((parsedHierarchy Y hY).ancestor
        ⟨P.K - r, ⟨B.innerNode r hr w, hc⟩⟩ j.val) =
      U.hierarchy.nodeRole (U.hierarchy.ancestor
        (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w) j.val)
    have hj := j.isLt
    refine (ground_actuality_step2_parent Y hY B U ψ hN _ _ (r - (j.val + 1)) ?_ ?_ ?_
      (hcorr j.val (by omega))).2.symm
    · rw [CoherentHierarchy.ancestor_height]
      dsimp only
      omega
    · have hYa : (parsedHierarchy Y hY).parentNode ((parsedHierarchy Y hY).ancestor
          ⟨P.K - r, ⟨B.innerNode r hr w, hc⟩⟩ j.val) = (parsedHierarchy Y hY).ancestor
          ⟨P.K - r, ⟨B.innerNode r hr w, hc⟩⟩ (j.val + 1) := by
        rw [← CoherentHierarchy.ancestor_add (parsedHierarchy Y hY) _ j.val 1]
        rfl
      rw [hYa, CoherentHierarchy.ancestor_add,
        show j.val + 1 + (r - (j.val + 1)) = r by omega]
      exact hanc
    · rw [CoherentHierarchy.ancestor_height, CoherentHierarchy.ancestor_height]
      rfl
/-- Step 3 of the V4 proof of `ground_actuality` (V4 4.5): "the corresponding
node Ã inside B̃". Moving a node moves each of its named cells. -/
private theorem ground_actuality_step3_cell_move (N : FramedNode S) (n : ℕ)
    (F : Cell d) (γ : Iso d) : (N.move γ).cell n F = γ '' N.cell n F := by
  simp only [FramedNode.cell, Set.image_image]
  rfl
/-- Step 3 of the V4 proof of `ground_actuality` (V4 4.5): "the packets on the
tiles inside B are those of the leaf pre-patterns of D". The leaf pre-patterns of
the certificate of an honest node are those of its native descendants. -/
private theorem ground_actuality_step3_leaves (U : HonestSource S) (ψ : Iso d)
    (D : Certificate P) (hN : (⟨D.ty, ψ⟩ : FramedNode S) ∈ U.hierarchy.nodes P.K)
    (hcert : certOf U P ⟨D.ty, ψ⟩ hN = D) (v : S.RoleWord D.ty P.K) :
    D.leaves v = prePatternOf U P (U.descendant ⟨P.K, ⟨⟨D.ty, ψ⟩, hN⟩⟩ P.K le_rfl v)
      (Nat.sub_self P.K) := by
  have aux : ∀ X Z : Certificate P, X = Z → ∀ (h : X.ty = Z.ty)
      (v : S.RoleWord X.ty P.K), X.leaves v = Z.leaves (h ▸ v) := by
    intro X Z e h v
    subst e
    rfl
  exact (aux _ _ hcert rfl v).symm
/-- Step 3 of the V4 proof of `ground_actuality` (V4 4.5): "all tiles inside A
with pieces on the facets of A" lie inside B, and the actual tiles inside the
K-block B are its prescribed leaves (Theorem 2.17(a)): an actual tile whose
decoded native node is a ground descendant of B is one of B's leaves. -/
private theorem ground_actuality_step3_tile_leaf {Y : MarkedTiling (systemM S P C)}
    (B : KBlock Y) (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (htd : (tileNode t).IsDescendant 0 B.node P.K) :
    ∃ v : S.RoleWord B.certificate.val.ty P.K, t = B.leaf v := by
  obtain ⟨r', hr', v, hv⟩ := htd
  have hr'' : r' = P.K := by omega
  subst hr''
  refine ⟨v, ?_⟩
  have hleaf : tileNode (B.leaf v) =
      (S.descendantNode B.certificate.val.ty 0 P.K v).move B.frame := by
    apply FramedNode.ext
    · change (compilerLeaf C (B.leaf v)).prototype = _
      rw [(B.leaf_data v).1]
      rfl
    · change compilerFrame C (B.leaf v) = _
      rw [(B.leaf_data v).2]
      rfl
  have hsame : tileNode t = tileNode (B.leaf v) := hv.trans hleaf.symm
  have hcar : t.carrier = (B.leaf v).carrier := by
    rw [compilerFrame_carrier C t, compilerFrame_carrier C (B.leaf v)]
    have h1 : compilerFrame C t = compilerFrame C (B.leaf v) :=
      congrArg FramedNode.frame hsame
    have h2 : (compilerLeaf C t).prototype = (compilerLeaf C (B.leaf v)).prototype := by
      have h3 := congrArg FramedNode.ty hsame
      exact h3
    rw [h1, h2]
  by_contra hne
  have hd := Y.disjoint ht (B.leaf_mem v) hne
  change Disjoint (interior t.carrier) (interior (B.leaf v).carrier) at hd
  rw [hcar] at hd
  have hn : (interior (B.leaf v).carrier).Nonempty := by
    rw [compilerFrame_carrier C (B.leaf v)]
    change (interior ((compilerFrame C (B.leaf v)).toHomeomorph ''
      (S.proto (compilerLeaf C (B.leaf v)).prototype).carrier)).Nonempty
    rw [← Homeomorph.image_interior]
    exact (S.proto _).interior_nonempty.image _
  obtain ⟨x, hx⟩ := hn
  exact Set.disjoint_left.mp hd hx hx
/-- Step 3 of the V4 proof of `ground_actuality` (V4 4.5): "so do all tiles
inside A with pieces on the facets of A (only these enter O_F(A)) ... the packets
on the tiles inside B are those of the leaf pre-patterns of D". Every facet
packet of an inner node of a K-block equals the honest facet packet of the
same-address node below the honest node whose certificate is D (NULL included). -/
private theorem ground_actuality_step3_packets (Y : MarkedTiling (systemM S P C))
    (hY : MProper Y) (B : KBlock Y) (U : HonestSource S) (ψ : Iso d)
    (hN : (⟨B.certificate.val.ty, ψ⟩ : FramedNode S) ∈ U.hierarchy.nodes P.K)
    (hcert : certOf U P ⟨B.certificate.val.ty, ψ⟩ hN = B.certificate.val)
    (r : ℕ) (hr : r ≤ P.K) (w : S.RoleWord B.certificate.val.ty r)
    (hc : B.innerNode r hr w ∈ (parsedHierarchy Y hY).nodes (P.K - r))
    (F : FacetName S (B.innerNode r hr w).ty) :
    parsedFacetPacket Y hY ⟨P.K - r, ⟨B.innerNode r hr w, hc⟩⟩ F =
      U.facetPacket P (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w) F := by
  classical
  have hblock : IsBlock Y (P.K - r) (B.innerNode r hr w) := by
    have h1 : B.innerNode r hr w ∈ (parsedHierarchy Y hY).nodes (P.K - r) := hc
    rw [← parsedHierarchy_nodes,
      ← (parsedDecodedLevel Y hY (P.K - r)).geometry.nodes_top] at h1
    exact (parsedDecodedLevel Y hY (P.K - r)).geometry.node_actual (P.K - r) _ h1
  obtain ⟨t, f, ht, htd, htf⟩ := Parser.facet_piece_exists Y (P.K - r) _ hblock F
  have hread := parsedFacetPacket_spec Y hY ⟨P.K - r, ⟨B.innerNode r hr w, hc⟩⟩ F t f
    ⟨ht, htd, htf⟩
  have htB : (tileNode t).IsDescendant 0 B.node P.K :=
    Parser.descendant_trans _ _ _ 0 (P.K - r) P.K htd
      ⟨r, (Nat.sub_add_cancel hr).symm, w, rfl⟩
  obtain ⟨v, rfl⟩ := ground_actuality_step3_tile_leaf B t ht htB
  rw [← hread, (B.leaf_data v).1]
  have he : tileNode (B.leaf v) = B.innerNode P.K le_rfl v := by
    apply FramedNode.ext
    · change (compilerLeaf C (B.leaf v)).prototype = _
      rw [(B.leaf_data v).1]
      simp only [LeafType.prototype, KBlock.innerNode, Nat.sub_self,
        FramedNode.move, SubstSystem.nativeTile]
    · change compilerFrame C (B.leaf v) = _
      rw [(B.leaf_data v).2]
      simp only [LeafType.position, KBlock.innerNode, Nat.sub_self,
        FramedNode.move, SubstSystem.nativeTile]
  have hℓnode : (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ P.K le_rfl v).2.val =
      (tileNode (B.leaf v)).move (B.frame.symm.trans ψ) := by
    rw [he]
    exact (ground_actuality_step2_move _ _ _).symm
  have hty : (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ P.K le_rfl v).2.val.ty =
      (tileNode (B.leaf v)).ty := by
    have h3 := congrArg FramedNode.ty hℓnode
    exact h3
  have hfl : f.val ∈ (S.cx (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩
      P.K le_rfl v).2.val.ty).facets := by
    rw [hty]
    exact f.property
  have hlp : leafPacket (⟨B.certificate, v⟩ : LeafType P) f.val =
      U.facetPacket P (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ P.K le_rfl v)
        ⟨f.val, hfl⟩ := by
    unfold leafPacket
    have hl := ground_actuality_step3_leaves U ψ B.certificate.val hN hcert v
    rw [show LeafType.prePattern (⟨B.certificate, v⟩ : LeafType P) = _ from hl]
    split_ifs with h
    · rfl
    · exact absurd hfl h
  rw [hlp]
  obtain ⟨r1, hr1, u, hu⟩ := htd
  have hc'node : (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w).2.val =
      (B.innerNode r hr w).move (B.frame.symm.trans ψ) :=
    (ground_actuality_step2_move _ _ _).symm
  have hc'mem : (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w).2.val ∈
      U.hierarchy.nodes (0 + r1) := by
    rw [← hr1]
    exact (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w).2.property
  have hX : (S.descendantNode (B.innerNode r hr w).ty 0 r1 u).move
      (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w).2.val.frame =
        (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ P.K le_rfl v).2.val := by
    rw [hℓnode, hu, hc'node]
    rfl
  have hXm : (S.descendantNode (B.innerNode r hr w).ty 0 r1 u).move
      (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w).2.val.frame ∈
        U.hierarchy.nodes 0 := by
    have h0 : (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ P.K le_rfl v).2.val ∈
        U.hierarchy.nodes (P.K - P.K) :=
      (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ P.K le_rfl v).2.property
    rw [Nat.sub_self] at h0
    rw [hX]
    exact h0
  have hroot := ground_actuality_step2_root_ancestor U.hierarchy 0 r1
    (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w).2.val hc'mem u hXm
  have hℓ : U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ P.K le_rfl v =
      ⟨0, ⟨_, hXm⟩⟩ :=
    observer_transition_aux_step1_node_eq U.hierarchy
      (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ P.K le_rfl v).2.property hXm
      (Nat.sub_self P.K) hX.symm
  have hc' : (⟨0 + r1, ⟨_, hc'mem⟩⟩ : U.Node) =
      U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w :=
    observer_transition_aux_step1_node_eq U.hierarchy hc'mem
      (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w).2.property hr1.symm rfl
  have hca : U.hierarchy.ancestor
      (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ P.K le_rfl v) r1 =
        U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w := by
    rw [hℓ]
    exact hroot.trans hc'
  have hgf : (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ P.K le_rfl v).2.val.cell
      (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ P.K le_rfl v).1 f.val ⊆
        (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w).2.val.cell
          (U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ r hr w).1 F.val := by
    show _ ⊆ _
    rw [hℓnode, hc'node, ground_actuality_step3_cell_move, ground_actuality_step3_cell_move]
    show (B.frame.symm.trans ψ) '' (tileNode (B.leaf v)).cell (P.K - P.K) f.val ⊆
      (B.frame.symm.trans ψ) '' (B.innerNode r hr w).cell (P.K - r) F.val
    rw [Nat.sub_self]
    exact Set.image_mono htf
  exact packet_inherited U P _ _ r1 hca F ⟨f.val, hfl⟩ hgf
/-- O5, V4 4.5: the entire observer of each height-H node occurs jointly in
one honest source node. The window and facet packets are read from one honest
K-certificate, using H+w ≤ K; separate marginal witnesses would not suffice. -/
theorem ground_actuality (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : q.1 = P.H) :
    observerOf Y hY q ∈ jointSourceRange S P := by
  obtain ⟨n, Q, hQ⟩ := q
  dsimp only at hq
  subst hq
  have hHK : P.H + P.w ≤ P.K := P.K_window
  obtain ⟨B, w, hw⟩ := ground_actuality_step1_K_block Y hY ⟨P.H, ⟨Q, hQ⟩⟩ (P.K - P.H)
    (by dsimp only; omega)
  obtain ⟨U, ⟨A, ψ⟩, hN, hcert⟩ := B.honest_table
  have hA : A = B.certificate.val.ty := congrArg Certificate.ty hcert
  subst hA
  have hr : P.K - P.H ≤ P.K := Nat.sub_le _ _
  have hh : P.K - (P.K - P.H) = P.H := by omega
  have hc : B.innerNode (P.K - P.H) hr w ∈
      (parsedHierarchy Y hY).nodes (P.K - (P.K - P.H)) := by
    show (S.descendantNode B.certificate.val.ty (P.K - (P.K - P.H)) (P.K - P.H) w).move
      B.frame ∈ _
    rw [hh]
    dsimp only at hw
    rw [hw]
    exact hQ
  have hq' : (⟨P.H, ⟨Q, hQ⟩⟩ : (parsedHierarchy Y hY).Node) =
      ⟨P.K - (P.K - P.H), ⟨B.innerNode (P.K - P.H) hr w, hc⟩⟩ := by
    apply observer_transition_aux_step1_node_eq (parsedHierarchy Y hY) hQ hc hh.symm
    show Q = (S.descendantNode B.certificate.val.ty (P.K - (P.K - P.H)) (P.K - P.H) w).move
      B.frame
    rw [hh]
    exact hw.symm
  refine ⟨U, U.descendant ⟨P.K, ⟨⟨B.certificate.val.ty, ψ⟩, hN⟩⟩ (P.K - P.H) hr w,
    ?_, ?_⟩
  · show P.H ≤ P.K - (P.K - P.H)
    omega
  · rw [hq']
    apply Observer.ext
    · rfl
    · exact (ground_actuality_step2_window Y hY B U ψ hN hcert (P.K - P.H) hr
        (by omega) w hc).symm
    · apply heq_of_eq
      funext F
      exact (ground_actuality_step3_packets Y hY B U ψ hN hcert (P.K - P.H) hr w hc F).symm
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
  cases ha with
  | inl h_source =>
      exact Or.inl (range_forward_closed a h_source i).1
  | inr h_output =>
      obtain ⟨q, hq, rfl⟩ := h_output
      by_cases h_strict : P.H + 1 ≤ q.1
      · apply Or.inr
        use parsedChild Y hY q (by omega) i
        constructor
        · change P.H ≤ q.1 - 1
          omega
        · exact observer_transition Y hY q h_strict i
      · have h_eq_H : q.1 = P.H := by omega
        have h_ground := ground_actuality Y hY q h_eq_H
        exact Or.inl (range_forward_closed (observerOf Y hY q) h_ground i).1
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
  unfold floorChildren
  split_ifs with h
  · apply List.Nodup.map
    · intro i j heq
      have heq1 : parsedChild Y hY q.val (by omega) i = parsedChild Y hY q.val (by omega) j := Subtype.mk.inj heq
      have heq2 : (parsedChild Y hY q.val (by omega) i).2.val = (parsedChild Y hY q.val (by omega) j).2.val :=
        congrArg (fun (x : (parsedHierarchy Y hY).Node) => x.2.val) heq1
      exact observer_transition_aux_step1_role_injective _ _ heq2
    · exact roles_nodup q.val.2.val.ty
  · exact List.nodup_nil
/-- O6, V4 4.6: actual children lie exactly one level below their parent. -/
theorem floorChildren_level (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q r : FloorNode Y hY) (hr : r ∈ floorChildren Y hY q) :
    q.val.1 - P.H = (r.val.1 - P.H) + 1 := by
  unfold floorChildren at hr
  by_cases h : P.H < q.val.1
  · rw [dif_pos h] at hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    show q.val.1 - P.H = (q.val.1 - 1 - P.H) + 1
    omega
  · rw [dif_neg h] at hr
    simp at hr
/-- O6, V4 4.6: every actual node occurs in its parent's complete child list. -/
theorem floor_mem_parent (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : FloorNode Y hY) : q ∈ floorChildren Y hY (floorParent Y hY q) := by
  obtain ⟨⟨n, ⟨N, hN⟩⟩, h_floor⟩ := q
  unfold floorChildren
  have h_lt : P.H < (floorParent Y hY ⟨⟨n, ⟨N, hN⟩⟩, h_floor⟩).val.1 := by
    change P.H < n + 1
    change P.H ≤ n at h_floor
    omega
  rw [dif_pos h_lt]
  apply List.mem_map.mpr
  let H := parsedHierarchy Y hY
  let i := H.role n ⟨N, hN⟩
  have hi : i ∈ roles ((floorParent Y hY ⟨⟨n, ⟨N, hN⟩⟩, h_floor⟩).val.2.val.ty) :=
    mem_roles _ i
  use i
  refine ⟨hi, ?_⟩
  apply Subtype.ext
  dsimp [parsedChild]
  have he : (H.parent n ⟨N, hN⟩).val.child n i = N := by
    have := H.child_eq n ⟨N, hN⟩
    exact this.symm
  apply Sigma.ext
  · change n + 1 - 1 = n
    omega
  · change HEq (⟨(H.parent n ⟨N, hN⟩).val.child (n + 1 - 1) i, _⟩ : {M // M ∈ H.nodes (n + 1 - 1)}) (⟨N, hN⟩ : {M // M ∈ H.nodes n})
    revert he
    change (H.parent n ⟨N, hN⟩).val.child (n + 1 - 1) i = N → _
    intro he
    apply heq_of_eq
    apply Subtype.ext
    exact he
/-- O6, V4 4.6: the listed parent is the unique actual hierarchy parent. -/
theorem floor_child_parent (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q r : FloorNode Y hY) (hr : r ∈ floorChildren Y hY q) :
    floorParent Y hY r = q := by
  have key : ∀ (m : (parsedHierarchy Y hY).Node) (hm : 1 ≤ m.1) (i : S.I m.2.val.ty),
      (parsedHierarchy Y hY).parentNode (parsedChild Y hY m hm i) = m := by
    intro m hm i
    rcases m with ⟨k, N, hN⟩
    cases k with
    | zero => change 1 ≤ 0 at hm; omega
    | succ n =>
        exact observer_transition_aux_step1_parent (parsedHierarchy Y hY) n N hN i ((parsedHierarchy Y hY).children_mem n N hN i)
  unfold floorChildren at hr
  by_cases h : P.H < q.val.1
  · rw [dif_pos h] at hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    exact Subtype.ext (key q.val (by omega) i)
  · rw [dif_neg h] at hr
    simp at hr
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
/-- Step 1 of the V4 proof of `observedPattern_unique` (V4 4.2):
"at their fixed positions". Read an observer along a fixed downward role word. -/
private def observedPattern_unique_down (a : Observer P) :
    (A : S.ι) → (r : ℕ) → S.RoleWord A r → Observer P
  | _, 0, _ => a
  | A, r + 1, w => observedPattern_unique_down
      (a.transition ⟨A, w.1⟩) (S.child A w.1).ty r w.2
/-- Step 1 of the V4 proof of `observedPattern_unique` (V4 4.2):
"at their fixed positions". A cell-indexed packet readout avoids dependent casts. -/
private def observedPattern_unique_packet (a : Observer P) (f : Cell d) :
    Option (Packet P) := by
  classical
  exact if hf : f ∈ (S.cx a.ty).facets then a.packets ⟨f, hf⟩ else none
/-- Step 1 of the V4 proof of `observedPattern_unique` (V4 4.2):
"the states of all nodes inside B_t" and "the packets on their facets".
These are precisely the non-geometric fields of a certificate. -/
private def observedPattern_unique_readout (a : Observer P)
    (D : CertificateSymbol S P) : Prop :=
  D.val.ty = a.ty ∧
    (∀ r hr w, D.val.table r hr w =
      (observedPattern_unique_down a D.val.ty r w).window.head) ∧
    ∀ w f, leafPacket (⟨D, w⟩ : LeafType P) f =
      observedPattern_unique_packet (observedPattern_unique_down a D.val.ty P.K w) f
/-- Step 1 of the V4 proof of `observedPattern_unique` (V4 4.2):
"fixed by position". Moving a standard descendant twice composes its frames. -/
private theorem observedPattern_unique_step1_move (N : FramedNode S) (φ ψ : Iso d) :
    (N.move φ).move ψ = N.move (φ.trans ψ) := rfl
/-- Step 1 of the V4 proof of `observedPattern_unique` (V4 4.2):
"fixed by position". Equal heights and frames identify hierarchy nodes. -/
private theorem observedPattern_unique_step1_node_eq {T : Tiling S}
    (H : CoherentHierarchy S T) {n m : ℕ} {N M : FramedNode S}
    (hn : N ∈ H.nodes n) (hm : M ∈ H.nodes m) (h : n = m) (hNM : N = M) :
    (⟨n, ⟨N, hn⟩⟩ : H.Node) = ⟨m, ⟨M, hm⟩⟩ := by
  cases h
  cases hNM
  rfl
/-- Step 1 of the V4 proof of `observedPattern_unique` (V4 4.2):
"the K-ancestor B_t of t lies inside A". The parent of a prescribed child is its root. -/
private theorem observedPattern_unique_step1_parent {T : Tiling S}
    (H : CoherentHierarchy S T) (n : ℕ) (N : FramedNode S)
    (hN : N ∈ H.nodes (n + 1)) (i : S.I N.ty)
    (hc : N.child n i ∈ H.nodes n) :
    H.parentNode ⟨n, ⟨N.child n i, hc⟩⟩ = ⟨n + 1, ⟨N, hN⟩⟩ := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    exact (H.parent_unique n _ N hN ⟨i, rfl⟩).symm
/-- Step 1 of the V4 proof of `observedPattern_unique` (V4 4.2):
"the K-ancestor B_t of t lies inside A". Exact downward addresses invert ancestry. -/
private theorem observedPattern_unique_step1_ancestor {T : Tiling S}
    (H : CoherentHierarchy S T) (h r : ℕ) (N : FramedNode S)
    (hN : N ∈ H.nodes (h + r)) (w : S.RoleWord N.ty r)
    (hc : (S.descendantNode N.ty h r w).move N.frame ∈ H.nodes h) :
    H.ancestor ⟨h, ⟨(S.descendantNode N.ty h r w).move N.frame, hc⟩⟩ r =
      ⟨h + r, ⟨N, hN⟩⟩ := by
  induction r generalizing N with
  | zero =>
      simp [CoherentHierarchy.ancestor, SubstSystem.descendantNode, FramedNode.move]
  | succ r ih =>
      have hchild := H.children_mem (h + r) N (by simpa [Nat.add_assoc] using hN) w.1
      have hc' : (S.descendantNode (N.child (h + r) w.1).ty h r w.2).move
          (N.child (h + r) w.1).frame ∈ H.nodes h := by
        simpa only [SubstSystem.descendantNode, observedPattern_unique_step1_move,
          FramedNode.child] using hc
      have hi := ih (N.child (h + r) w.1) hchild w.2 hc'
      rw [← H.ancestor_add]
      change H.parentNode (H.ancestor _ r) = _
      have he : (⟨h, ⟨(S.descendantNode N.ty h (r + 1) w).move N.frame, hc⟩⟩ :
          H.Node) = ⟨h, ⟨(S.descendantNode (N.child (h + r) w.1).ty h r w.2).move
            (N.child (h + r) w.1).frame, hc'⟩⟩ := rfl
      rw [he, hi]
      exact observedPattern_unique_step1_parent H (h + r) N hN w.1 hchild
/-- Step 1 of the V4 proof of `observedPattern_unique` (V4 4.2):
"type and frame (fixed)". The affine prototype frame obeys the child equation. -/
private theorem observedPattern_unique_step1_child_frame (N : FramedNode S)
    (n : ℕ) (i : S.I N.ty) :
    (N.child n i).prototypeFrame n =
      (rolePlacement (⟨N.ty, i⟩ : S.Role)).trans (N.prototypeFrame (n + 1)) := by
  apply AffineEquiv.ext
  intro x
  change N.frame (S.placeChild n i ((S.σ ^ n) x)) =
    N.frame ((S.σ ^ (n + 1)) (S.σ.symm ((S.child N.ty i).frame x)))
  congr 1
  rw [S.placeChild_apply]
  simp [linearConj, Child.frame, rigidMotion, pow_succ, zpow_neg,
    LinearEquiv.mul_apply, ← map_add]
/-- Step 1 of the V4 proof of `observedPattern_unique` (V4 4.2):
"i_t ... (fixed by position)". Distinct roles have disjoint nonempty interiors. -/
private theorem observedPattern_unique_step1_role_injective (N : FramedNode S) (n : ℕ) :
    Function.Injective (N.child n) := by
  intro i j h
  have hty : (S.child N.ty i).ty = (S.child N.ty j).ty := congrArg FramedNode.ty h
  have he := congrArg (fun M : FramedNode S => M.prototypeFrame n) h
  dsimp only at he
  rw [observedPattern_unique_step1_child_frame, observedPattern_unique_step1_child_frame] at he
  have hframe : (S.child N.ty i).frame = (S.child N.ty j).frame := by
    apply AffineIsometryEquiv.ext
    intro x
    have hx := congrArg (fun e : E d ≃ᵃ[ℝ] E d => e x) he
    exact S.σ.symm.injective ((N.prototypeFrame (n + 1)).injective hx)
  by_contra hij
  have hd := S.children_disjoint N.ty hij
  dsimp only at hd
  rw [hty, hframe] at hd
  have hn : (interior (placedSet (S.child N.ty j).frame
      (S.proto (S.child N.ty j).ty).carrier)).Nonempty := by
    change (interior ((S.child N.ty j).frame.toHomeomorph ''
      (S.proto (S.child N.ty j).ty).carrier)).Nonempty
    rw [← Homeomorph.image_interior]
    exact (S.proto (S.child N.ty j).ty).interior_nonempty.image _
  obtain ⟨x, hx⟩ := hn
  exact Set.disjoint_left.mp hd hx hx
/-- Step 1 of the V4 proof of `observedPattern_unique` (V4 4.2):
"i_t ... (fixed by position)". A prescribed child's hierarchy role is its index. -/
private theorem observedPattern_unique_step1_role {T : Tiling S}
    (H : CoherentHierarchy S T) (n : ℕ) (N : FramedNode S)
    (hN : N ∈ H.nodes (n + 1)) (i : S.I N.ty) (hc : N.child n i ∈ H.nodes n) :
    H.nodeRole ⟨n, ⟨N.child n i, hc⟩⟩ = ⟨N.ty, i⟩ := by
  have hp : (H.parent n ⟨N.child n i, hc⟩).val = N :=
    (H.parent_unique n _ N hN ⟨i, rfl⟩).symm
  have he := H.child_eq n ⟨N.child n i, hc⟩
  have aux (M : FramedNode S) (j : S.I M.ty) (hM : M = N)
      (h : N.child n i = M.child n j) : (⟨M.ty, j⟩ : S.Role) = ⟨N.ty, i⟩ := by
    subst M
    exact congrArg (Sigma.mk N.ty) ((observedPattern_unique_step1_role_injective N n h).symm)
  exact aux _ _ hp he
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"all listed in Ĵ(A)". The compressed window shifts using its actual parent
and role; the highest new state is the old offset w-2. -/
private theorem observedPattern_unique_step2_window {T : Tiling S}
    (H : CoherentHierarchy S T) (state : H.Node → State P) (c q : H.Node)
    (r : S.Role) (hp : H.parentNode c = q) (hr : H.nodeRole c = r)
    (hat : (ObserverWindow.ofHierarchy H state q).stateAt
      ⟨P.w - 2, by have := P.observer_window_bound; omega⟩ =
        state (H.ancestor q (P.w - 2))) :
    ObserverWindow.ofHierarchy H state c = (ObserverWindow.ofHierarchy H state q).child r := by
  apply ObserverWindow.ext
  · change state (H.ancestor c (P.w - 1)) =
      (ObserverWindow.ofHierarchy H state q).stateAt _
    rw [hat]
    have hw : P.w - 1 = P.w - 2 + 1 := by have := P.observer_window_bound; omega
    rw [hw]
    simp only [CoherentHierarchy.ancestor, Function.iterate_succ_apply, hp]
  · funext j
    change H.nodeRole (H.ancestor c j.val) =
      if hj : j.val = 0 then r else H.nodeRole (H.ancestor q (j.val - 1))
    by_cases hj : j.val = 0
    · simp only [hj, dif_pos, CoherentHierarchy.ancestor, Function.iterate_zero, id_eq, hr]
    · rw [dif_neg hj]
      have he : H.ancestor c j.val = H.ancestor q (j.val - 1) := by
        conv_lhs => rw [show j.val = (j.val - 1) + 1 by omega]
        simp only [CoherentHierarchy.ancestor, Function.iterate_succ_apply, hp]
      rw [he]
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"the attached packet is O_F(A)". Inherited containment is checked in the
fixed first-generation coordinates. -/
private theorem observedPattern_unique_step2_containment (N : FramedNode S)
    (n : ℕ) (i : S.I N.ty) (f F : Cell d) :
    (N.child n i).cell n f ⊆ N.cell (n + 1) F ↔
      placedSet (S.child N.ty i).frame f.carrier ⊆ S.σ '' F.carrier := by
  change (N.child n i).prototypeFrame n '' f.carrier ⊆
    N.prototypeFrame (n + 1) '' F.carrier ↔ _
  rw [observedPattern_unique_step1_child_frame]
  change (N.prototypeFrame (n + 1) ∘ rolePlacement (⟨N.ty, i⟩ : S.Role)) ''
    f.carrier ⊆ N.prototypeFrame (n + 1) '' F.carrier ↔ _
  rw [Set.image_comp, Set.image_subset_image_iff (N.prototypeFrame (n + 1)).injective]
  change (S.σ.symm ∘ (S.child N.ty i).frame) '' f.carrier ⊆ F.carrier ↔ _
  rw [Set.image_comp]
  constructor
  · intro h x hx
    exact ⟨S.σ.symm x, h ⟨x, hx, rfl⟩, S.σ.apply_symm_apply x⟩
  · rintro h x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, he⟩ := h hy
    simpa only [← he, S.σ.symm_apply_apply] using hz
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"μ determined by ι(g) and ... S(P_b)". An honest compressed packet is exactly
the birth computation when the window supplies its highest state and roles. -/
private theorem observedPattern_unique_step2_born_eq (a : Observer P) (p : Packet P)
    (hp : p ∈ honestPackets S P) (hh : p.head = a.window.head)
    (hs : p.sstar = a.window.stateAt
      ⟨p.jstar.val, by have := p.jstar.isLt; rw [P.w_eq]; exact this⟩)
    (hr : ∀ j : Fin p.jstar.val, p.roles j =
      a.window.roles ⟨j.val, by have := p.jstar.isLt; have := j.isLt; rw [P.w_eq]; omega⟩) :
    a.bornPacket p.incidence = some p := by
  classical
  let slots := Finset.univ.filter (packetMask P p.incidence a.window.head)
  have hmem (j : Fin P.k) : j ∈ slots ↔ p.mask j := by
    simp only [slots, Finset.mem_filter, Finset.mem_univ, true_and, Packet.mask, hh]
  have hadm := honest_packet_admissible P p hp
  have hn : slots.Nonempty := ⟨p.jstar, (hmem _).mpr hadm.2.2.1⟩
  have hmax : slots.max' hn = p.jstar := by
    apply le_antisymm
    · exact Finset.max'_le _ _ _ (fun j hj => hadm.2.2.2.1 j ((hmem j).mp hj))
    · exact Finset.le_max' _ _ ((hmem _).mpr hadm.2.2.1)
  have hbuild (j : Fin P.k) (hj : j = p.jstar) :
      ({ incidence := p.incidence
         jstar := j
         sstar := a.window.stateAt ⟨j.val, by rw [P.w_eq]; exact j.isLt⟩
         roles := fun t => a.window.roles ⟨t.val, by
           have := t.isLt; have := j.isLt; rw [P.w_eq]; omega⟩ } : Packet P) = p := by
    cases hj
    cases p with
    | mk incidence jstar sstar roles =>
        dsimp only at hs hr ⊢
        congr 1
        · exact hs.symm
        · funext j
          exact (hr j).symm
  unfold Observer.bornPacket
  change (if h : slots.Nonempty then some _ else none) = some p
  rw [dif_pos hn]
  exact congrArg some (hbuild (slots.max' hn) hmax)
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"Definition 2.5 in sources". The honest window supplies the state and roles
retained by the packet at a specified primitive birth. -/
private theorem observedPattern_unique_step2_source_born
    (U : HonestSource S) (g : PrimitiveOccurrence U P) :
    (U.observerOf P g.birth).bornPacket g.incidence = some (packetOf U P g) := by
  apply observedPattern_unique_step2_born_eq _ (packetOf U P g) ⟨U, g, rfl⟩
  · exact (packet_head U P g).trans
      (honestWindow_at U P g.birth ⟨0, by have := P.observer_window_bound; omega⟩).symm
  · exact (honestWindow_at U P g.birth
      ⟨(topSlot U P g).val, by have := (topSlot U P g).isLt; rw [P.w_eq]; exact this⟩).symm
  · intro j
    rfl
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"by W4 (Theorem 3.13 in Y)". Calibration identifies the entire compressed
primitive packet, including roles and the maximum PRESENT slot. -/
private theorem observedPattern_unique_step2_output_born
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (g : Parser.BornFacet P) (hg : g.birth ∈ (parsedHierarchy Y hY).nodes g.height) :
    (observerOf Y hY (g.hierarchyBirth (parsedHierarchy Y hY) hg)).bornPacket g.incidence =
      parsedPrimitivePacket Y hY g hg := by
  obtain ⟨hl, hr, _, p, hp, hhonest, hinc, hhead, hslots⟩ := calibration_W4 Y hY g hg
  have hread : parsedPrimitivePacket Y hY g hg = some p := hp
  rw [hread, ← hinc]
  apply observedPattern_unique_step2_born_eq _ p hhonest
  · exact hhead.trans (parsedWindow_at Y hY (g.hierarchyBirth (parsedHierarchy Y hY) hg)
      ⟨0, by have := P.observer_window_bound; omega⟩).symm
  · have ht := (packet_top_spec P p hhonest).1
    have hm := (honest_packet_admissible P p hhonest).2.2.1
    have hs := (hslots p.jstar).2 hm
    have he := Option.some.inj (ht.symm.trans hs)
    exact he.trans (parsedWindow_at Y hY (g.hierarchyBirth (parsedHierarchy Y hY) hg)
      ⟨p.jstar.val, by have := p.jstar.isLt; rw [P.w_eq]; exact this⟩).symm
  · intro j
    rw [packet_roles_from_head P p hhonest j, hhead,
      parsedState_address Y hY (g.hierarchyBirth (parsedHierarchy Y hY) hg)
        ⟨j.val, lt_trans j.isLt p.jstar.isLt⟩]
    rfl
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"which g ... is determined by the position". Canonical incidences of the
same parent type and positioned facet coincide. -/
private theorem observedPattern_unique_step2_incidence_eq (ι η : P.Incidence)
    (ht : ι.val.ty = η.val.ty) (hp : ι.val.positioned = η.val.positioned) : ι = η :=
  (P.canonical_idempotent ι).symm.trans (P.canonical_unique ι.val η ⟨ht, hp⟩)
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"which g, P_b ... is determined by the position". Equality of actual child
and primitive carriers is equality in first-generation coordinates. -/
private theorem observedPattern_unique_step2_positioned (N : FramedNode S)
    (n : ℕ) (i : S.I N.ty) (f : Cell d) (ι : P.Incidence)
    (h : P.incidencePlacement N (n + 1) ι '' ι.val.leftFacet.val.carrier =
      (N.child n i).cell n f) :
    ι.val.positioned = placedSet (S.child N.ty i).frame f.carrier := by
  apply Set.image_injective.mpr S.σ.symm.injective
  apply Set.image_injective.mpr (N.prototypeFrame (n + 1)).injective
  rw [FramedNode.cell, observedPattern_unique_step1_child_frame] at h
  simpa only [Params.incidencePlacement, PrimitiveIncidence.positioned, rolePlacement,
    placedSet, Set.image_image, AffineEquiv.coe_trans, LinearEquiv.coe_toAffineEquiv,
    AffineIsometryEquiv.coe_toAffineEquiv, Function.comp_def] using h
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"by W4 ... Definition 2.5 in sources" or "O_F(A) ... Lemma 2.6(d)".
One source child facet is computed by the internal-birth/inherited-facet formula. -/
private theorem observedPattern_unique_step2_source_packet
    (U : HonestSource S) (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (U.childNode q hq i).2.val.ty) :
    U.facetPacket P (U.childNode q hq i) f =
      (U.observerOf P q).childPacket ⟨q.2.val.ty, i⟩ f.val := by
  classical
  rcases q with ⟨m, N, hN⟩
  cases m with
  | zero => change 1 ≤ 0 at hq; omega
  | succ n =>
      let hc := U.hierarchy.children_mem n N hN i
      let c : U.Node := ⟨n, ⟨N.child n i, hc⟩⟩
      let q : U.Node := ⟨n + 1, ⟨N, hN⟩⟩
      have hp : U.hierarchy.parentNode c = q :=
        observedPattern_unique_step1_parent U.hierarchy n N hN i hc
      change U.facetPacket P c f = (U.observerOf P q).childPacket ⟨N.ty, i⟩ f.val
      by_cases hb : ∃ F : FacetName S N.ty,
          placedSet (S.child N.ty i).frame f.val.carrier ⊆ S.σ '' F.val.carrier
      · unfold Observer.childPacket
        dsimp only [HonestSource.observerOf]
        rw [dif_pos hb]
        apply packet_inherited U P q c 1
          (by simpa only [CoherentHierarchy.ancestor, Function.iterate_one] using hp)
          (Classical.choose hb) f
        exact (observedPattern_unique_step2_containment N n i f.val _).mpr (Classical.choose_spec hb)
      · have hi : relint ((N.child n i).cell n f.val) ⊆ interior (N.carrier (n + 1)) := by
          rcases facet_dichotomy N (N.child n i) (n + 1) n (Parser.child_descendant N n i) f with
            ⟨F, hF, _⟩ | hi
          · exact False.elim (hb ⟨F, (observedPattern_unique_step2_containment N n i f.val F.val).mp hF⟩)
          · exact hi
        obtain ⟨hf, hcarrier, hbirth, _⟩ := U.hierarchy.restriction_det_internal c f
          (by rw [hp]; exact hi)
        let g := U.providerOccurrence P c f hf
        have hg : g.birth = q := hbirth.trans hp
        have hty : g.incidence.val.ty = N.ty :=
          g.parent_type.trans (congrArg (fun t : U.Node => t.2.val.ty) hg)
        have hplaced : P.incidencePlacement N (n + 1) g.incidence ''
            g.incidence.val.leftFacet.val.carrier = (N.child n i).cell n f.val := by
          have h := record_provider_carrier U P c f hf
          change P.incidencePlacement g.birth.2.val g.birth.1 g.incidence ''
            g.incidence.val.leftFacet.val.carrier = _ at h
          rw [hg] at h
          exact h.trans hcarrier
        have hpos := observedPattern_unique_step2_positioned N n i f.val g.incidence hplaced
        have hex : ∃ ι : P.Incidence, ι.val.ty = N.ty ∧
            ι.val.positioned = placedSet (S.child N.ty i).frame f.val.carrier :=
          ⟨g.incidence, hty, hpos⟩
        unfold Observer.childPacket
        dsimp only [HonestSource.observerOf]
        rw [dif_neg hb, dif_pos hex]
        have he : Classical.choose hex = g.incidence :=
          observedPattern_unique_step2_incidence_eq _ _
            ((Classical.choose_spec hex).1.trans hty.symm)
            ((Classical.choose_spec hex).2.trans hpos.symm)
        rw [he, HonestSource.facetPacket, dif_neg hf]
        change some (packetOf U P g) = (U.observerOf P q).bornPacket g.incidence
        rw [← hg]
        exact (observedPattern_unique_step2_source_born U g).symm
/-- Step 1 of the V4 proof of `observedPattern_unique` (V4 4.2):
"fixed subdivision geometry". At native height the conjugated child frame is
the original prescribed isometry. -/
private theorem observedPattern_unique_step1_place_zero (A : S.ι) (i : S.I A) :
    S.placeChild 0 i = (S.child A i).frame := by
  apply AffineIsometryEquiv.ext
  intro x
  simp [SubstSystem.placeChild_apply, linearConj, Child.frame, rigidMotion]
/-- Step 1 of the V4 proof of `observedPattern_unique` (V4 4.2):
"which ... F is determined by the position". A cell's carrier fixes its
dimension and hence its full cell name. -/
private theorem observedPattern_unique_step1_cell_eq (e f : Cell d)
    (h : e.carrier = f.carrier) : e = f := by
  rcases e with ⟨K, j, hj⟩
  rcases f with ⟨L, k, hk⟩
  cases h
  have hjk : j = k := hj.dimension.symm.trans hk.dimension
  cases hjk
  rfl
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"either in a primitive facet g ... or in a facet F of A". An internal
first-generation facet has an honest age-one record in the child state. -/
private theorem observedPattern_unique_step2_internal_record
    (s : State P) (hs : s ∈ honestStates S P) (r : S.Role)
    (hr : s.address ⟨0, P.k_pos⟩ = r) (f : FacetName S s.ty)
    (hb : ¬ ∃ F : FacetName S r.1,
      placedSet (S.child r.1 r.2).frame f.val.carrier ⊆ S.σ '' F.val.carrier) :
    ∃ R : FacetRecord P, s.facetRecord f = some R ∧ AgeOneRecord s R := by
  let N : FramedNode S := ⟨r.1, AffineIsometryEquiv.refl ℝ (E d)⟩
  have ht : (S.child r.1 r.2).ty = s.ty := by rw [← hr]; exact s.address_start
  let f' : FacetName S (N.child 0 r.2).ty := ⟨f.val, by
    change f.val ∈ (S.cx (S.child r.1 r.2).ty).facets
    rw [ht]
    exact f.property⟩
  have hc (e : Cell d) : (N.child 0 r.2).cell 0 e =
      placedSet (S.child r.1 r.2).frame e.carrier := by
    simp [FramedNode.cell, FramedNode.prototypeFrame, FramedNode.child,
      observedPattern_unique_step1_place_zero, N, placedSet]
  have hF (e : Cell d) : N.cell 1 e = S.σ '' e.carrier := by
    simp [FramedNode.cell, FramedNode.prototypeFrame, N]
  have hint : s.InternalFacet f := by
    rcases facet_dichotomy N (N.child 0 r.2) 1 0
      (Parser.child_descendant N 0 r.2) f' with ⟨F, hF', _⟩ | hi
    · exact False.elim (hb ⟨F, by simpa only [hc, hF] using hF'⟩)
    · unfold State.InternalFacet
      rw [hr]
      simpa [hc, FramedNode.carrier, N, placedSet] using hi
  exact (state_semantics_a P s hs f).1.mp hint
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"which g ... is determined by the position". Both canonical side names
refer to the same positioned primitive facet. -/
private theorem observedPattern_unique_step2_side_positioned (ι : P.Incidence) (b : Bool) :
    ι.val.positioned = placedSet
      (S.child (ι.val.sideRole b).1 (ι.val.sideRole b).2).frame
      (ι.val.sideFacet b).val.carrier := by
  cases b
  · rfl
  · exact ι.val.paired
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"which g, P_b ... is determined by the position". Honest age-one semantics
identify the canonical side, including its actual facet name. -/
private theorem observedPattern_unique_step2_record_side
    (s : State P) (r : S.Role) (hr : s.address ⟨0, P.k_pos⟩ = r)
    (f : FacetName S s.ty) (R : FacetRecord P) (hR : s.facetRecord f = some R)
    (hA : AgeOneRecord s R) :
    R.incidence.val.sideRole R.sideIndex = r ∧
      R.incidence.val.positioned = placedSet (S.child r.1 r.2).frame f.val.carrier ∧
      (R.incidence.val.sideFacet R.sideIndex).val = f.val := by
  have hs : R.servingRole = r := hA.2.1.trans hr
  have hrole : R.incidence.val.sideRole R.sideIndex = r := R.side_eq.symm.trans hs
  have hpos : R.incidence.val.positioned = placedSet (S.child r.1 r.2).frame f.val.carrier := by
    rw [hA.2.2.1, (s.facetRecord_valid f R hR).2,
      congrArg (fun t : S.Role => (S.child t.1 t.2).frame) hs]
  refine ⟨hrole, hpos, ?_⟩
  apply observedPattern_unique_step1_cell_eq
  apply Set.image_injective.mpr (S.child r.1 r.2).frame.injective
  have hside := observedPattern_unique_step2_side_positioned R.incidence R.sideIndex
  rw [hrole] at hside
  exact hside.symm.trans hpos
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"the attached packet". Equal hierarchy nodes and equal facet names give
the same parsed packet; membership proofs carry no extra data. -/
private theorem observedPattern_unique_step2_output_packet_congr
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q q' : (parsedHierarchy Y hY).Node) (he : q = q')
    (f : FacetName S q.2.val.ty) (f' : FacetName S q'.2.val.ty) (hf : f.val = f'.val) :
    parsedFacetPacket Y hY q f = parsedFacetPacket Y hY q' f' := by
  cases he
  have hff : f = f' := Subtype.ext hf
  cases hff
  rfl
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"by W4 (Theorem 3.13 in Y)" or "O_F(A) by (I5)".
One output child facet is computed without assigning providers to faults. -/
private theorem observedPattern_unique_step2_output_packet
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty)
    (f : FacetName S (parsedChild Y hY q hq i).2.val.ty) :
    parsedFacetPacket Y hY (parsedChild Y hY q hq i) f =
      (observerOf Y hY q).childPacket ⟨q.2.val.ty, i⟩ f.val := by
  classical
  rcases q with ⟨m, N, hN⟩
  cases m with
  | zero => change 1 ≤ 0 at hq; omega
  | succ n =>
      let H := parsedHierarchy Y hY
      let hc := H.children_mem n N hN i
      let c : H.Node := ⟨n, ⟨N.child n i, hc⟩⟩
      let q : H.Node := ⟨n + 1, ⟨N, hN⟩⟩
      change parsedFacetPacket Y hY c f = (observerOf Y hY q).childPacket ⟨N.ty, i⟩ f.val
      by_cases hb : ∃ F : FacetName S N.ty,
          placedSet (S.child N.ty i).frame f.val.carrier ⊆ S.σ '' F.val.carrier
      · unfold Observer.childPacket
        dsimp only [observerOf]
        rw [dif_pos hb]
        symm
        apply parsedFacetPacket_inherited Y hY q c
          (Parser.child_descendant N n i) (Classical.choose hb) f
        exact (observedPattern_unique_step2_containment N n i f.val _).mpr (Classical.choose_spec hb)
      · let s := parsedState Y hY c
        have hsty : s.ty = (S.child N.ty i).ty := (parsedState_type_residue Y hY c).2.1
        let fs : FacetName S s.ty := ⟨f.val, by rw [hsty]; exact f.property⟩
        have hrole : s.address ⟨0, P.k_pos⟩ = (⟨N.ty, i⟩ : S.Role) :=
          (parsedState_role Y hY c).trans (observedPattern_unique_step1_role H n N hN i hc)
        obtain ⟨R, hR, hA⟩ := observedPattern_unique_step2_internal_record s
          (parsedState_type_residue Y hY c).1 ⟨N.ty, i⟩ hrole fs hb
        obtain ⟨hside, hpos, hfacet⟩ := observedPattern_unique_step2_record_side s
          ⟨N.ty, i⟩ hrole fs R hR hA
        have hty : R.incidence.val.ty = N.ty := congrArg Sigma.fst hside
        let g : Parser.BornFacet P :=
          ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), N, R.incidence, hty⟩
        have hex : ∃ ι : P.Incidence, ι.val.ty = N.ty ∧
            ι.val.positioned = placedSet (S.child N.ty i).frame f.val.carrier :=
          ⟨R.incidence, hty, hpos⟩
        unfold Observer.childPacket
        dsimp only [observerOf]
        rw [dif_neg hb, dif_pos hex]
        have he : Classical.choose hex = R.incidence :=
          observedPattern_unique_step2_incidence_eq _ _
            ((Classical.choose_spec hex).1.trans hty.symm)
            ((Classical.choose_spec hex).2.trans hpos.symm)
        rw [he]
        change parsedFacetPacket Y hY c f = (observerOf Y hY q).bornPacket g.incidence
        have hborn := observedPattern_unique_step2_output_born Y hY g hN
        change (observerOf Y hY q).bornPacket g.incidence = parsedPrimitivePacket Y hY g hN at hborn
        rw [hborn]
        cases hbside : R.sideIndex with
        | false =>
            have hnode : g.leftNode = N.child n i := by
              have he := congrArg (fun r : S.Role =>
                (⟨r.1, N.frame⟩ : FramedNode S).child n r.2) hside
              simpa only [hbside, PrimitiveIncidence.sideRole, PrimitiveIncidence.sideIndex,
                Bool.false_eq_true, ↓reduceIte] using he
            exact observedPattern_unique_step2_output_packet_congr Y hY c
              ⟨g.height - 1, ⟨g.leftNode, g.left_mem H hN⟩⟩
              (observedPattern_unique_step1_node_eq H hc _ rfl hnode.symm) f
              g.incidence.val.leftFacet (by
                have h := hfacet.symm
                rw [hbside] at h
                exact h)
        | true =>
            have hnode : g.rightNode = N.child n i := by
              have he := congrArg (fun r : S.Role =>
                (⟨r.1, N.frame⟩ : FramedNode S).child n r.2) hside
              simpa only [hbside, PrimitiveIncidence.sideRole, PrimitiveIncidence.sideIndex,
                ↓reduceIte] using he
            have hp := observedPattern_unique_step2_output_packet_congr Y hY c
              ⟨g.height - 1, ⟨g.rightNode, g.right_mem H hN⟩⟩
              (observedPattern_unique_step1_node_eq H hc _ rfl hnode.symm) f
              g.incidence.val.rightFacet (by
                have h := hfacet.symm
                rw [hbside] at h
                exact h)
            exact hp.trans (parsedPrimitivePacket_spec Y hY g hN).1.symm
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"all listed in Ĵ(A) or determined ... by D_S". The window shift and the
one-facet packet formulas give the entire source child observer at every height. -/
private theorem observedPattern_unique_step2_source_child
    (U : HonestSource S) (q : U.Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) :
    U.observerOf P (U.childNode q hq i) =
      (U.observerOf P q).transition ⟨q.2.val.ty, i⟩ := by
  rcases q with ⟨m, N, hN⟩
  cases m with
  | zero => change 1 ≤ 0 at hq; omega
  | succ n =>
      let hc := U.hierarchy.children_mem n N hN i
      let c : U.Node := ⟨n, ⟨N.child n i, hc⟩⟩
      let q : U.Node := ⟨n + 1, ⟨N, hN⟩⟩
      have hw := observedPattern_unique_step2_window U.hierarchy (stateOf U P) c q ⟨N.ty, i⟩
        (observedPattern_unique_step1_parent U.hierarchy n N hN i hc)
        (observedPattern_unique_step1_role U.hierarchy n N hN i hc)
        (honestWindow_at U P q ⟨P.w - 2, by have := P.observer_window_bound; omega⟩)
      have hhead : ((U.observerOf P q).window.child ⟨N.ty, i⟩).head.ty = (S.child N.ty i).ty := by
        change ((ObserverWindow.ofHierarchy U.hierarchy (stateOf U P) q).child ⟨N.ty, i⟩).head.ty = _
        rw [← hw]
        exact honestWindow_type U P c
      change U.observerOf P c = (U.observerOf P q).transition ⟨N.ty, i⟩
      unfold Observer.transition
      rw [dif_pos ⟨rfl, hhead⟩]
      apply Observer.ext
      · rfl
      · exact hw
      · apply heq_of_eq
        funext f
        exact observedPattern_unique_step2_source_packet U q hq i f
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"by W4 (Theorem 3.13 in Y)" and "the attached packet is O_F(A) by (I5)".
The one-step formula includes certificate-subdivision nodes below the floor. -/
private theorem observedPattern_unique_step2_output_child
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (q : (parsedHierarchy Y hY).Node) (hq : 1 ≤ q.1) (i : S.I q.2.val.ty) :
    observerOf Y hY (parsedChild Y hY q hq i) =
      (observerOf Y hY q).transition ⟨q.2.val.ty, i⟩ := by
  rcases q with ⟨m, N, hN⟩
  cases m with
  | zero => change 1 ≤ 0 at hq; omega
  | succ n =>
      let hc := (parsedHierarchy Y hY).children_mem n N hN i
      let c : (parsedHierarchy Y hY).Node := ⟨n, ⟨N.child n i, hc⟩⟩
      let q : (parsedHierarchy Y hY).Node := ⟨n + 1, ⟨N, hN⟩⟩
      have hw := observedPattern_unique_step2_window (parsedHierarchy Y hY) (parsedState Y hY)
        c q ⟨N.ty, i⟩
        (observedPattern_unique_step1_parent (parsedHierarchy Y hY) n N hN i hc)
        (observedPattern_unique_step1_role (parsedHierarchy Y hY) n N hN i hc)
        (parsedWindow_at Y hY q ⟨P.w - 2, by have := P.observer_window_bound; omega⟩)
      have hhead : ((observerOf Y hY q).window.child ⟨N.ty, i⟩).head.ty = (S.child N.ty i).ty := by
        change ((ObserverWindow.ofHierarchy (parsedHierarchy Y hY) (parsedState Y hY) q).child
          ⟨N.ty, i⟩).head.ty = _
        rw [← hw]
        exact parsedWindow_type Y hY c
      change observerOf Y hY c = (observerOf Y hY q).transition ⟨N.ty, i⟩
      unfold Observer.transition
      rw [dif_pos ⟨rfl, hhead⟩]
      apply Observer.ext
      · rfl
      · exact hw
      · apply heq_of_eq
        funext f
        exact observedPattern_unique_step2_output_packet Y hY q hq i f
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"all listed in Ĵ(A) or determined ... by D_S". Iterating the one-step formula
recovers the observer at every fixed descendant, without a provider-height bound. -/
private theorem observedPattern_unique_step2_descend {T : Tiling S}
    (H : CoherentHierarchy S T) (o : H.Node → Observer P)
    (hstep : ∀ n N (hN : N ∈ H.nodes (n + 1)) (i : S.I N.ty),
      o ⟨n, ⟨N.child n i, H.children_mem n N hN i⟩⟩ =
        (o ⟨n + 1, ⟨N, hN⟩⟩).transition ⟨N.ty, i⟩)
    (h r : ℕ) (N : FramedNode S) (hN : N ∈ H.nodes (h + r))
    (w : S.RoleWord N.ty r)
    (hc : (S.descendantNode N.ty h r w).move N.frame ∈ H.nodes h) :
    o ⟨h, ⟨(S.descendantNode N.ty h r w).move N.frame, hc⟩⟩ =
      observedPattern_unique_down (o ⟨h + r, ⟨N, hN⟩⟩) N.ty r w := by
  induction r generalizing N with
  | zero =>
      simp [observedPattern_unique_down, SubstSystem.descendantNode, FramedNode.move]
  | succ r ih =>
      have hchild := H.children_mem (h + r) N (by simpa [Nat.add_assoc] using hN) w.1
      have hc' : (S.descendantNode (N.child (h + r) w.1).ty h r w.2).move
          (N.child (h + r) w.1).frame ∈ H.nodes h := by
        simpa only [SubstSystem.descendantNode, observedPattern_unique_step1_move,
          FramedNode.child] using hc
      change o ⟨h, ⟨(S.descendantNode (N.child (h + r) w.1).ty h r w.2).move
          (N.child (h + r) w.1).frame, hc'⟩⟩ = _
      rw [ih _ hchild _ hc', hstep]
      rfl
/-- Step 3 of the V4 proof of `observedPattern_unique` (V4 4.2):
"D_t = cert(B_t) consists of (i) ... states ...; (ii) the pre-patterns".
The complete table and every facet packet determine the certificate, including
its fixed frame markers and all leaf states. -/
private def observedPattern_unique_prepacket (u : PrePattern P) (f : Cell d) :
    Option (Packet P) := by
  classical
  exact if hf : f ∈ (S.cx u.ty).facets then u.packets ⟨f, hf⟩ else none
/-- Step 3 of the V4 proof of `observedPattern_unique` (V4 4.2):
"type and frame (fixed), state (as in (i)), and the packets on their facets".
These fields identify the entire pre-pattern. -/
private theorem observedPattern_unique_step3_prepattern_ext
    (u v : PrePattern P) (hty : u.ty = v.ty) (hs : u.state = v.state)
    (hp : ∀ f : Cell d, observedPattern_unique_prepacket u f =
      observedPattern_unique_prepacket v f) : u = v := by
  classical
  rcases u with ⟨A, marker, hm, s, hst, packets⟩
  rcases v with ⟨A', marker', hm', s', hst', packets'⟩
  dsimp only at hty hs hp
  cases hty
  cases hs
  have hpack : packets = packets' := by
    funext f
    simpa only [observedPattern_unique_prepacket, dif_pos f.property] using hp f.val
  subst packets'
  subst marker
  subst marker'
  rfl
/-- Step 3 of the V4 proof of `observedPattern_unique` (V4 4.2):
"D_t = cert(B_t) consists of (i) ... states ...; (ii) the pre-patterns".
Equality includes the whole certificate, not merely the indicated leaf. -/
private theorem observedPattern_unique_step3_certificate_ext
    (a : Observer P) (D E : CertificateSymbol S P)
    (hD : observedPattern_unique_readout a D)
    (hE : observedPattern_unique_readout a E) : D = E := by
  obtain ⟨hDty, hDt, hDp⟩ := hD
  obtain ⟨hEty, hEt, hEp⟩ := hE
  have hty : D.val.ty = E.val.ty := hDty.trans hEty.symm
  apply Subtype.ext
  rcases D with ⟨⟨A, leaves, leaf_ty, table, table_ty⟩, hD⟩
  rcases E with ⟨⟨A', leaves', leaf_ty', table', table_ty'⟩, hE⟩
  dsimp only at hty
  subst A'
  have ht : table = table' := by
    funext r hr w
    exact (hDt r hr w).trans (hEt r hr w).symm
  have hl : leaves = leaves' := by
    funext w
    have hs : (leaves w).state = (leaves' w).state := by
      exact (certificate_leaf_state ⟨_, hD⟩ w).symm.trans
        ((congrFun (congrFun (congrFun ht P.K) le_rfl) w).trans
          (certificate_leaf_state ⟨_, hE⟩ w))
    exact observedPattern_unique_step3_prepattern_ext _ _
      ((leaf_ty w).trans (leaf_ty' w).symm) hs (fun f => (hDp w f).trans (hEp w f).symm)
  subst leaves'
  subst table'
  rfl
/-- Step 2 of the V4 proof of `observedPattern_unique` (V4 4.2):
"determined ... via D_S (Proposition 2.3 in sources)". Source descent uses the
same role-word computation as the parsed descent. -/
private theorem observedPattern_unique_step2_source_descend
    (U : HonestSource S) (n : ℕ) (N : FramedNode S) (hN : N ∈ U.hierarchy.nodes n)
    (r : ℕ) (hr : r ≤ n) (w : S.RoleWord N.ty r) :
    U.observerOf P (U.descendant ⟨n, ⟨N, hN⟩⟩ r hr w) =
      observedPattern_unique_down (U.observerOf P ⟨n, ⟨N, hN⟩⟩) N.ty r w := by
  have hstep : ∀ m M (hM : M ∈ U.hierarchy.nodes (m + 1)) (i : S.I M.ty),
      U.observerOf P ⟨m, ⟨M.child m i, U.hierarchy.children_mem m M hM i⟩⟩ =
        (U.observerOf P ⟨m + 1, ⟨M, hM⟩⟩).transition ⟨M.ty, i⟩ := by
    intro m M hM i
    simpa only [HonestSource.childNode, Nat.add_sub_cancel] using
      observedPattern_unique_step2_source_child (P := P) U ⟨m + 1, ⟨M, hM⟩⟩
        (Nat.succ_le_succ (Nat.zero_le m)) i
  have hd := observedPattern_unique_step2_descend U.hierarchy (U.observerOf P) hstep
    (n - r) r N (by simpa only [Nat.sub_add_cancel hr] using hN) w
      (U.descendant_mem ⟨n, ⟨N, hN⟩⟩ r hr w)
  rw [observedPattern_unique_step1_node_eq U.hierarchy _ hN (Nat.sub_add_cancel hr) rfl] at hd
  exact hd
/-- Step 3 of the V4 proof of `observedPattern_unique` (V4 4.2):
"D_t = cert(B_t)". A source certificate has exactly the reconstructed state
table and the reconstructed leaf packets. -/
private theorem observedPattern_unique_step3_source_readout
    (U : HonestSource S) (N : FramedNode S) (hN : N ∈ U.hierarchy.nodes P.K) :
    observedPattern_unique_readout (U.observerOf P ⟨P.K, ⟨N, hN⟩⟩)
      ⟨certOf U P N hN, ⟨U, N, hN, rfl⟩⟩ := by
  refine ⟨rfl, ?_, ?_⟩
  · intro r hr w
    change stateOf U P (U.descendant ⟨P.K, ⟨N, hN⟩⟩ r hr w) =
      (observedPattern_unique_down (U.observerOf P ⟨P.K, ⟨N, hN⟩⟩) N.ty r w).window.head
    rw [← observedPattern_unique_step2_source_descend (P := P) U P.K N hN r hr w]
    have hh := honestWindow_at U P (U.descendant ⟨P.K, ⟨N, hN⟩⟩ r hr w)
      ⟨0, by have := P.observer_window_bound; omega⟩
    exact hh.symm
  · intro w f
    change leafPacket (⟨⟨certOf U P N hN, ⟨U, N, hN, rfl⟩⟩, w⟩ : LeafType P) f =
      observedPattern_unique_packet
        (observedPattern_unique_down (U.observerOf P ⟨P.K, ⟨N, hN⟩⟩) N.ty P.K w) f
    rw [← observedPattern_unique_step2_source_descend (P := P) U P.K N hN P.K le_rfl w]
    rfl
/-- Step 3 of the V4 proof of `observedPattern_unique` (V4 4.2):
"i_t is the role word of t below B_t (fixed by position)". At height K the
source leaf tuple consists of the one root certificate with its respective words. -/
private theorem observedPattern_unique_step3_source_labels
    (U : HonestSource S) (N : FramedNode S) (hN : N ∈ U.hierarchy.nodes P.K)
    (w : S.RoleWord N.ty P.K) :
    leafTypeOf U P (U.descendant ⟨P.K, ⟨N, hN⟩⟩ P.K le_rfl w) (Nat.sub_self P.K) =
      (⟨⟨certOf U P N hN, ⟨U, N, hN, rfl⟩⟩, w⟩ : LeafType P) := by
  have ha := observedPattern_unique_step1_ancestor U.hierarchy 0 P.K N
    (by simpa using hN) w
    (by simpa only [Nat.sub_self] using U.descendant_mem ⟨P.K, ⟨N, hN⟩⟩ P.K le_rfl w)
  have ha' : U.hierarchy.ancestor
      (U.descendant ⟨P.K, ⟨N, hN⟩⟩ P.K le_rfl w) P.K = ⟨P.K, ⟨N, hN⟩⟩ := by
    have hc := observedPattern_unique_step1_node_eq U.hierarchy
      (M := (S.descendantNode N.ty 0 P.K w).move N.frame)
      (U.descendant_mem ⟨P.K, ⟨N, hN⟩⟩ P.K le_rfl w)
      (by simpa only [Nat.sub_self] using U.descendant_mem ⟨P.K, ⟨N, hN⟩⟩ P.K le_rfl w)
      (Nat.sub_self P.K)
      (by simp only [Nat.sub_self])
    change U.hierarchy.ancestor ⟨P.K - P.K, _⟩ P.K = _
    rw [hc]
    exact ha.trans (observedPattern_unique_step1_node_eq U.hierarchy _ hN
      (Nat.zero_add P.K) rfl)
  have hw := (Classical.choose_spec (U.leafIndex_exists P
    (U.descendant ⟨P.K, ⟨N, hN⟩⟩ P.K le_rfl w) (Nat.sub_self P.K))).1
  change (S.nativeTile _ P.K (U.leafIndex P
    (U.descendant ⟨P.K, ⟨N, hN⟩⟩ P.K le_rfl w) (Nat.sub_self P.K))).move _ = _ at hw
  unfold leafTypeOf
  generalize hi : U.leafIndex P (U.descendant ⟨P.K, ⟨N, hN⟩⟩ P.K le_rfl w)
    (Nat.sub_self P.K) = i at hw ⊢
  have hunique := U.leafIndex_exists P
    (U.descendant ⟨P.K, ⟨N, hN⟩⟩ P.K le_rfl w) (Nat.sub_self P.K)
  rw [ha'] at hunique
  have aux (M : FramedNode S) (hM : M ∈ U.hierarchy.nodes P.K) (he : M = N)
      (j : S.RoleWord M.ty P.K)
      (hj : (S.nativeTile M.ty P.K j).move M.frame =
        (U.descendant ⟨P.K, ⟨N, hN⟩⟩ P.K le_rfl w).2.val) :
      (⟨⟨certOf U P M hM, ⟨U, M, hM, rfl⟩⟩, j⟩ : LeafType P) =
        ⟨⟨certOf U P N hN, ⟨U, N, hN, rfl⟩⟩, w⟩ := by
    subst M
    have hjw : j = w := ExistsUnique.unique hunique hj
      (by simp only [HonestSource.descendant, Nat.sub_self, SubstSystem.nativeTile])
    subst j
    rfl
  exact aux _ _ (congrArg (fun q : U.Node => q.2.val) ha') i hw
/-- Step 3 of the V4 proof of `observedPattern_unique` (V4 4.2):
"the packets on their facets". At height zero the parsed attachment reads the
physical leaf itself, including NULL. -/
private theorem observedPattern_unique_step3_ground_packet
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y)
    (t : PlacedMarkedTile (systemM S P C)) (ht : t ∈ Y.tiles)
    (hN : tileNode t ∈ (parsedHierarchy Y hY).nodes 0) (f : Cell d) :
    leafPacket (compilerLeaf C t) f = observedPattern_unique_packet
      (observerOf Y hY ⟨0, ⟨tileNode t, hN⟩⟩) f := by
  classical
  by_cases hf : f ∈ (S.cx (tileNode t).ty).facets
  · have he := parsedFacetPacket_spec Y hY ⟨0, ⟨tileNode t, hN⟩⟩ ⟨f, hf⟩
      t ⟨f, hf⟩ ⟨ht, Parser.descendant_refl _ _, Set.Subset.rfl⟩
    simpa only [observedPattern_unique_packet, observerOf, dif_pos hf] using he
  · have hpre : ¬ f ∈ (S.cx (compilerLeaf C t).prePattern.ty).facets := by
      rw [LeafType.prePattern_type]
      exact hf
    simp only [leafPacket, dif_neg hpre, observedPattern_unique_packet,
      observerOf, dif_neg hf]
/-- Step 3 of the V4 proof of `observedPattern_unique` (V4 4.2):
"the states of all nodes inside B_t ... (I2) in Y". The certificate table is
the actual global parsed state assignment on its exact inner nodes. -/
private theorem observedPattern_unique_step3_output_table
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) (B : KBlock Y)
    (r : ℕ) (hr : r ≤ P.K) (w : S.RoleWord B.certificate.val.ty r) :
    ∃ hc : B.innerNode r hr w ∈ (parsedHierarchy Y hY).nodes (P.K - r),
      B.table r hr w = parsedState Y hY ⟨P.K - r, ⟨B.innerNode r hr w, hc⟩⟩ := by
  obtain ⟨hc, he⟩ := (parsedHierarchy_base Y hY).2 B r hr w
  have hc' : B.innerNode r hr w ∈
      (parsedDecodedLevel Y hY P.K).geometry.nodes (P.K - r) := by
    rw [parsedDecodedLevel_upper Y hY P.K le_rfl]
    exact hc
  have hm : B.innerNode r hr w ∈ (parsedHierarchy Y hY).nodes (P.K - r) := by
    rw [← parsedHierarchy_inner_nodes Y hY P.K (P.K - r) (Nat.sub_le _ _)]
    exact hc'
  refine ⟨hm, ?_⟩
  have hagree := parsedState_agrees Y hY P.K (P.K - r) (B.innerNode r hr w) hc' hm
  have htable : ∀ hc' : B.innerNode r hr w ∈
      (parsedDecodedLevel Y hY P.K).geometry.nodes (P.K - r),
      (parsedDecodedLevel Y hY P.K).stateAt (P.K - r) (B.innerNode r hr w) hc' =
        B.table r hr w := by
    rw [parsedDecodedLevel_upper Y hY P.K le_rfl]
    intro hc'
    exact he
  exact (htable hc').symm.trans hagree
/-- Step 3 of the V4 proof of `observedPattern_unique` (V4 4.2):
"D_t = cert(B_t)". An output certificate has the reconstructed table and all
reconstructed leaf packets, with no interpretation of boundary faults as providers. -/
private theorem observedPattern_unique_step3_output_readout
    (Y : MarkedTiling (systemM S P C)) (hY : MProper Y) (B : KBlock Y)
    (hB : B.node ∈ (parsedHierarchy Y hY).nodes P.K) :
    observedPattern_unique_readout (observerOf Y hY ⟨P.K, ⟨B.node, hB⟩⟩)
      B.certificate := by
  have hstep : ∀ m M (hM : M ∈ (parsedHierarchy Y hY).nodes (m + 1)) (i : S.I M.ty),
      observerOf Y hY ⟨m, ⟨M.child m i, (parsedHierarchy Y hY).children_mem m M hM i⟩⟩ =
        (observerOf Y hY ⟨m + 1, ⟨M, hM⟩⟩).transition ⟨M.ty, i⟩ := by
    intro m M hM i
    simpa only [parsedChild, Nat.add_sub_cancel] using
      observedPattern_unique_step2_output_child Y hY ⟨m + 1, ⟨M, hM⟩⟩
        (Nat.succ_le_succ (Nat.zero_le m)) i
  have hdown (r : ℕ) (hr : r ≤ P.K) (w : S.RoleWord B.certificate.val.ty r)
      (hc : B.innerNode r hr w ∈ (parsedHierarchy Y hY).nodes (P.K - r)) :
      observerOf Y hY ⟨P.K - r, ⟨B.innerNode r hr w, hc⟩⟩ =
        observedPattern_unique_down (observerOf Y hY ⟨P.K, ⟨B.node, hB⟩⟩)
          B.certificate.val.ty r w := by
    have hd := observedPattern_unique_step2_descend (parsedHierarchy Y hY)
      (observerOf Y hY) hstep (P.K - r) r B.node
      (by simpa only [Nat.sub_add_cancel hr] using hB) w hc
    rw [observedPattern_unique_step1_node_eq (parsedHierarchy Y hY) _ hB
      (Nat.sub_add_cancel hr) rfl] at hd
    exact hd
  refine ⟨rfl, ?_, ?_⟩
  · intro r hr w
    obtain ⟨hc, ht⟩ := observedPattern_unique_step3_output_table Y hY B r hr w
    rw [← hdown r hr w hc]
    exact ht.trans (parsedWindow_at Y hY ⟨P.K - r, ⟨B.innerNode r hr w, hc⟩⟩
      ⟨0, by have := P.observer_window_bound; omega⟩).symm
  · intro w f
    obtain ⟨hc, _⟩ := observedPattern_unique_step3_output_table Y hY B P.K le_rfl w
    rw [← hdown P.K le_rfl w hc]
    have he : tileNode (B.leaf w) = B.innerNode P.K le_rfl w := by
      apply FramedNode.ext
      · change (compilerLeaf C (B.leaf w)).prototype = _
        rw [(B.leaf_data w).1]
        simp only [LeafType.prototype, KBlock.innerNode, Nat.sub_self,
          FramedNode.move, SubstSystem.nativeTile]
      · change compilerFrame C (B.leaf w) = _
        rw [(B.leaf_data w).2]
        simp only [LeafType.position, KBlock.innerNode, Nat.sub_self,
          FramedNode.move, SubstSystem.nativeTile]
    have hm : tileNode (B.leaf w) ∈ (parsedHierarchy Y hY).nodes 0 := by
      simpa only [he, Nat.sub_self] using hc
    have hn := observedPattern_unique_step1_node_eq (parsedHierarchy Y hY) hc hm
      (Nat.sub_self P.K) he.symm
    rw [hn, ← (B.leaf_data w).1]
    exact observedPattern_unique_step3_ground_packet Y hY (B.leaf w) (B.leaf_mem w) hm f
/-- Step 4 of the V4 proof of `observedPattern_unique` (V4 4.2):
"The pattern is the union of the augmented markings of the leaves ... at their
fixed positions (Proposition 2.16)". This also holds for an arbitrary output. -/
private theorem observedPattern_unique_step4_render
    (Y : MarkedTiling (systemM S P C)) (n : ℕ) (A : S.ι) (φ : Iso d)
    (labels : S.RoleWord A n → LeafType P)
    (hlabels : ∀ w, ∃ t ∈ Y.tiles, compilerLeaf C t = labels w ∧
      tileNode t = (S.nativeTile A n w).move φ) :
    normalisedPattern Y n A φ = renderLeafTuple C n A labels := by
  classical
  funext x
  have hcover : ∃ w : S.RoleWord A n,
      x.val ∈ placedSet (S.nativeTile A n w).frame
        (S.proto (S.nativeTile A n w).ty).carrier := by
    have hx := (S.native_cover A n).symm.subset x.property
    simpa [FramedNode.carrier, SubstSystem.supertile] using hx
  let w := Classical.choose hcover
  obtain ⟨t, ht, hl, hn⟩ := hlabels w
  have hty := congrArg FramedNode.ty hn
  change (compilerLeaf C t).prototype = (S.nativeTile A n w).ty at hty
  have hframe : compilerFrame C t = (S.nativeTile A n w).frame.trans φ :=
    congrArg FramedNode.frame hn
  have hx : φ x.val ∈ t.carrier := by
    rw [compilerFrame_carrier, hty, hframe]
    obtain ⟨u, hu, he⟩ := Classical.choose_spec hcover
    exact ⟨u, hu, congrArg φ he⟩
  change Y.marking (φ x.val) = _
  rw [Y.marking_eq_tile t ht _ hx, compilerFrame_marking, hl, hframe]
  simp only [renderLeafTuple, dif_pos hcover]
  congr 1
  change (S.nativeTile A n w).frame.symm (φ.symm (φ x.val)) =
    (S.nativeTile A n w).frame.symm x.val
  rw [φ.symm_apply_apply]
/-- Step 4 of the V4 proof of `observedPattern_unique` (V4 4.2):
"the leaf type (D_t,i_t)" at "fixed positions". A forced certificate has
exactly its prescribed physical leaves, in their full isometric frames. -/
private theorem observedPattern_unique_step4_block_leaf
    {Y : MarkedTiling (systemM S P C)} (B : KBlock Y)
    (w : S.RoleWord B.certificate.val.ty P.K) :
    tileNode (B.leaf w) = (S.nativeTile B.certificate.val.ty P.K w).move B.frame := by
  apply FramedNode.ext
  · change (compilerLeaf C (B.leaf w)).prototype = _
    rw [(B.leaf_data w).1]
    rfl
  · change compilerFrame C (B.leaf w) = _
    exact (B.leaf_data w).2
/-- Step 4 of the V4 proof of `observedPattern_unique` (V4 4.2):
"Since n ≥ K, the K-ancestor B_t of t lies inside A". At the base height the
whole pattern is the rendering of the single reconstructed certificate. -/
private theorem observedPattern_unique_step4_base
    (a : Observer P) (q : Pattern S (Colour S P) P.K a.ty)
    (hq : ObservedPattern C P.K a q) :
    ∃ D : CertificateSymbol S P, observedPattern_unique_readout a D ∧
      HEq q (renderLeafTuple C P.K D.val.ty (fun w => ⟨D, w⟩)) := by
  rcases hq with ⟨U, φ, hN, ho, rfl⟩ | ⟨Y, hY, φ, hN, ho, rfl⟩
  · let D : CertificateSymbol S P := ⟨certOf U P ⟨a.ty, φ⟩ hN, ⟨U, _, hN, rfl⟩⟩
    refine ⟨D, ?_, ?_⟩
    · have hr := observedPattern_unique_step3_source_readout (P := P) U ⟨a.ty, φ⟩ hN
      change observedPattern_unique_readout (U.observerOf P ⟨P.K, ⟨⟨a.ty, φ⟩, hN⟩⟩) D at hr
      rwa [ho] at hr
    · apply heq_of_eq
      rw [renderLeafTuple_source C U P.K a.ty φ hN]
      congr 1
      funext w
      exact observedPattern_unique_step3_source_labels U ⟨a.ty, φ⟩ hN w
  · have hroots : (parsedLevels Y hY P.K le_rfl).geometry.roots =
        (parsedHierarchy Y hY).nodes P.K := by
      rw [← parsedDecodedLevel_upper Y hY P.K le_rfl]
      exact parsedHierarchy_nodes Y hY P.K
    have hcert : (⟨a.ty, φ⟩ : FramedNode S) ∈ Set.range (fun B : KBlock Y => B.node) := by
      rw [← (parsedHierarchy_base Y hY).1, hroots]
      exact hN
    obtain ⟨B, he⟩ := hcert
    change B.node = ⟨a.ty, φ⟩ at he
    have hB : B.node ∈ (parsedHierarchy Y hY).nodes P.K := by
      rw [he]
      exact hN
    have honode := observedPattern_unique_step1_node_eq (parsedHierarchy Y hY) hB hN rfl he
    have hoB : observerOf Y hY ⟨P.K, ⟨B.node, hB⟩⟩ = a :=
      (congrArg (observerOf Y hY) honode).trans ho
    refine ⟨B.certificate, ?_, ?_⟩
    · have hr := observedPattern_unique_step3_output_readout Y hY B hB
      rwa [hoB] at hr
    · have hr := observedPattern_unique_step4_render Y P.K B.certificate.val.ty B.frame
        (fun w => (⟨B.certificate, w⟩ : LeafType P))
        (fun w => ⟨B.leaf w, B.leaf_mem w, (B.leaf_data w).1,
          observedPattern_unique_step4_block_leaf B w⟩)
      have htransport (M N : FramedNode S) (heq : M = N) :
          HEq (normalisedPattern Y P.K M.ty M.frame)
            (normalisedPattern Y P.K N.ty N.frame) := by
        cases heq
        rfl
      exact (htransport B.node ⟨a.ty, φ⟩ he).symm.trans (heq_of_eq hr)
/-- Step 4 of the V4 proof of `observedPattern_unique` (V4 4.2):
"the pattern is the union ... at their fixed positions". The immediate closed
children cover the closed parent, also for a general linear expansion. -/
private theorem observedPattern_unique_step4_children_cover (n : ℕ) (A : S.ι) :
    S.supertile (n + 1) A =
      ⋃ i : S.I A, placedSet (S.placeChild n i) (S.supertile n (S.child A i).ty) := by
  have hplace (i : S.I A) (x : E d) : S.placeChild n i ((S.σ ^ n) x) =
      (S.σ ^ n) ((S.child A i).frame x) := by
    change linearConj S.σ (n : ℤ) (S.child A i).rotation.toLinearEquiv
        ((S.σ ^ n) x) + (S.σ ^ n) (S.child A i).offset =
      (S.σ ^ n) ((S.child A i).rotation x + (S.child A i).offset)
    simp [linearConj, zpow_neg, LinearEquiv.mul_apply]
  calc
    S.supertile (n + 1) A = (S.σ ^ n) '' (S.σ '' (S.proto A).carrier) := by
      simp only [SubstSystem.supertile, pow_succ, Set.image_image]
      rfl
    _ = ⋃ i : S.I A,
        (S.σ ^ n) '' placedSet (S.child A i).frame (S.proto (S.child A i).ty).carrier := by
      rw [S.children_cover, Set.image_iUnion]
    _ = _ := by
      apply Set.iUnion_congr
      intro i
      simp only [placedSet, SubstSystem.supertile, Set.image_image]
      congr 1
      funext x
      exact (hplace i x).symm
/-- Step 4 of the V4 proof of `observedPattern_unique` (V4 4.2):
"restriction of the marking ... transported ... by the inverse isometric frame".
Restriction to a prescribed child is a fixed function of the parent pattern. -/
private def observedPattern_unique_restrict {n : ℕ} {A : S.ι}
    (q : Pattern S (Colour S P) (n + 1) A) (i : S.I A) :
    Pattern S (Colour S P) n (S.child A i).ty :=
  fun x => q ⟨S.placeChild n i x.val,
    (observedPattern_unique_step4_children_cover n A).symm.subset
      (Set.mem_iUnion.mpr ⟨i, ⟨x.val, x.property, rfl⟩⟩)⟩
/-- Step 4 of the V4 proof of `observedPattern_unique` (V4 4.2):
"the pattern is the union". Equality on each prescribed closed child gives
equality on the complete closed parent. -/
private theorem observedPattern_unique_step4_children_ext {n : ℕ} {A : S.ι}
    (q q' : Pattern S (Colour S P) (n + 1) A)
    (h : ∀ i : S.I A, observedPattern_unique_restrict q i =
      observedPattern_unique_restrict q' i) : q = q' := by
  funext x
  have hx := (observedPattern_unique_step4_children_cover n A).subset x.property
  obtain ⟨i, y, hy, he⟩ := Set.mem_iUnion.mp hx
  have hh := congrFun (h i) ⟨y, hy⟩
  change q ⟨S.placeChild n i y, _⟩ = q' ⟨S.placeChild n i y, _⟩ at hh
  simpa only [he] using hh
/-- Step 4 of the V4 proof of `observedPattern_unique` (V4 4.2):
"determined ... by D_S" and "Which case applies ... is determined by the
position". Restricting an observed pattern follows the common observer transition. -/
private theorem observedPattern_unique_step4_child
    (n : ℕ) (a : Observer P) (q : Pattern S (Colour S P) (n + 1) a.ty)
    (hq : ObservedPattern C (n + 1) a q) (i : S.I a.ty) :
    ∃ b : Observer P, b = a.transition ⟨a.ty, i⟩ ∧
      ∃ p : Pattern S (Colour S P) n b.ty, ObservedPattern C n b p ∧
        HEq p (observedPattern_unique_restrict q i) := by
  rcases hq with ⟨U, φ, hN, ho, rfl⟩ | ⟨Y, hY, φ, hN, ho, rfl⟩
  · let N : FramedNode S := ⟨a.ty, φ⟩
    let hc := U.hierarchy.children_mem n N hN i
    let c : U.Node := ⟨n, ⟨N.child n i, hc⟩⟩
    refine ⟨U.observerOf P c, ?_, normalisedPattern (honestLift C U) n
      (S.child a.ty i).ty ((S.placeChild n i).trans φ), ?_, HEq.rfl⟩
    · have hs := observedPattern_unique_step2_source_child (P := P) U
        ⟨n + 1, ⟨N, hN⟩⟩ (Nat.succ_le_succ (Nat.zero_le n)) i
      change U.observerOf P c = (U.observerOf P ⟨n + 1, ⟨N, hN⟩⟩).transition ⟨a.ty, i⟩ at hs
      exact hs.trans (congrArg (fun b : Observer P => b.transition ⟨a.ty, i⟩) ho)
    · exact Or.inl ⟨U, (S.placeChild n i).trans φ, hc, rfl, rfl⟩
  · let N : FramedNode S := ⟨a.ty, φ⟩
    let hc := (parsedHierarchy Y hY).children_mem n N hN i
    let c : (parsedHierarchy Y hY).Node := ⟨n, ⟨N.child n i, hc⟩⟩
    refine ⟨observerOf Y hY c, ?_, normalisedPattern Y n
      (S.child a.ty i).ty ((S.placeChild n i).trans φ), ?_, HEq.rfl⟩
    · have hs := observedPattern_unique_step2_output_child Y hY
        ⟨n + 1, ⟨N, hN⟩⟩ (Nat.succ_le_succ (Nat.zero_le n)) i
      change observerOf Y hY c = (observerOf Y hY ⟨n + 1, ⟨N, hN⟩⟩).transition ⟨a.ty, i⟩ at hs
      exact hs.trans (congrArg (fun b : Observer P => b.transition ⟨a.ty, i⟩) ho)
    · exact Or.inr ⟨Y, hY, (S.placeChild n i).trans φ, hc, rfl, rfl⟩
/-- O2, V4 4.2: the complete closed pattern is determined by the joint observer.
This compares any source/output pair. Leaf certificates use the reconstructed
window and all facet packets; no height-bounded assumption on providers is made. -/
theorem observedPattern_unique (C : ClusterData S P) (n : ℕ) (hn : P.K ≤ n)
    (a : Observer P) (q q' : Pattern S (Colour S P) n a.ty)
    (hq : ObservedPattern C n a q) (hq' : ObservedPattern C n a q') : q = q' := by
  induction n, hn using Nat.le_induction generalizing a with
  | base =>
      obtain ⟨D, hD, hqD⟩ := observedPattern_unique_step4_base a q hq
      obtain ⟨E, hE, hqE⟩ := observedPattern_unique_step4_base a q' hq'
      have he := observedPattern_unique_step3_certificate_ext a D E hD hE
      subst E
      exact eq_of_heq (hqD.trans hqE.symm)
  | succ n hn ih =>
      apply observedPattern_unique_step4_children_ext q q'
      intro i
      obtain ⟨b, hb, p, hp, he⟩ := observedPattern_unique_step4_child n a q hq i
      obtain ⟨b', hb', p', hp', he'⟩ := observedPattern_unique_step4_child n a q' hq' i
      have hbb : b' = b := hb'.trans hb.symm
      cases hbb
      exact eq_of_heq (he.symm.trans ((heq_of_eq (ih b p p' hp hp')).trans he'))
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
