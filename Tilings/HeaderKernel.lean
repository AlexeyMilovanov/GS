import Mathlib

/-!
A small kernel for the proposed boundary-header repair.

This file proves only facts about finite headers and recovery of their Boolean
fields from fourth-index values. It does not claim the assembly, composition,
alignment, legality, geometric construction, or lifting theorems.
-/

universe u v w

namespace Tilings.HeaderKernel

/-- Side sets depend on the parent type. A header retains that type. -/
abbrev Header (T : Type u) (Side : T → Type v) :=
  Sigma fun t => Side t → Bool

noncomputable instance headerFintype (T : Type u) (Side : T → Type v)
    [Fintype T] [∀ t, Fintype (Side t)] : Fintype (Header T Side) := by
  classical
  exact inferInstance

variable {T : Type u} {Side : T → Type v} {I : Type w}

/-- A zero mode requires an outer side as well as a zero fourth value. -/
def zeroMode [Zero I] [DecidableEq I]
    (outer : (t : T) → Side t → Bool) (t : T)
    (fourth : Side t → I) : Side t → Bool :=
  fun d => outer t d && decide (fourth d = 0)

/-- The complete finite vector of modes, indexed by the parent's own sides. -/
def makeHeader [Zero I] [DecidableEq I]
    (outer : (t : T) → Side t → Bool) (t : T)
    (fourth : Side t → I) : Header T Side :=
  ⟨t, zeroMode outer t fourth⟩

section Recovery

variable [Zero I] [DecidableEq I]
variable (outer : (t : T) → Side t → Bool)
variable {t : T} (a b : Side t → I)

@[simp] theorem makeHeader_type : (makeHeader outer t a).1 = t := rfl

@[simp] theorem makeHeader_modes :
    (makeHeader outer t a).2 = zeroMode outer t a := rfl

theorem zeroMode_eq_true_iff (d : Side t) :
    zeroMode outer t a d = true ↔ outer t d = true ∧ a d = 0 := by
  simp [zeroMode]

theorem zeroMode_eq_false_of_inner (d : Side t) (h : outer t d = false) :
    zeroMode outer t a d = false := by
  simp [zeroMode, h]

theorem zeroMode_eq_false_of_ne_zero (d : Side t) (h : a d ≠ 0) :
    zeroMode outer t a d = false := by
  simp [zeroMode, h]

theorem zeroMode_eq_true_of_outer_zero (d : Side t)
    (ho : outer t d = true) (hz : a d = 0) :
    zeroMode outer t a d = true := by
  simp [zeroMode, ho, hz]

theorem zeroMode_congr (h : ∀ d, a d = b d) :
    zeroMode outer t a = zeroMode outer t b := by
  funext d
  simp only [zeroMode, h d]

/-- Equal fourth vectors at the same type determine equal headers. -/
theorem makeHeader_eq_of_fourth_eq (h : ∀ d, a d = b d) :
    makeHeader outer t a = makeHeader outer t b := by
  unfold makeHeader
  rw [zeroMode_congr outer a b h]

/-- A fourth-port signal that recovers both vectors determines their header. -/
theorem makeHeader_eq_of_port_recovery (port4 : Side t → I)
    (ha : ∀ d, port4 d = a d) (hb : ∀ d, port4 d = b d) :
    makeHeader outer t a = makeHeader outer t b := by
  apply makeHeader_eq_of_fourth_eq outer a b
  intro d
  exact (ha d).symm.trans (hb d)

/-- Side families must be transported when the parent types are identified. -/
theorem makeHeader_eq_of_aligned_fourth {s : T} (ht : t = s)
    (c : Side s → I) (h : ∀ d : Side t, a d = c (ht ▸ d)) :
    makeHeader outer t a = makeHeader outer s c := by
  cases ht
  exact makeHeader_eq_of_fourth_eq outer a c h

end Recovery

/-- A tagged extension of an ordinary colour alphabet. Constructors are disjoint. -/
inductive TaggedIndex (T : Type u) (Side : T → Type v) (Other : Type w) where
  | zero
  | ordinary (value : Other)
  | header (value : Header T Side)

instance (T : Type u) (Side : T → Type v) (Other : Type w) :
    Zero (TaggedIndex T Side Other) := ⟨TaggedIndex.zero⟩

variable {Other : Type w}

@[simp] theorem tagged_header_ne_zero (h : Header T Side) :
    TaggedIndex.header h ≠ (0 : TaggedIndex T Side Other) := by
  intro he
  cases he

@[simp] theorem tagged_header_ne_ordinary (h : Header T Side) (o : Other) :
    TaggedIndex.header h ≠ (TaggedIndex.ordinary o : TaggedIndex T Side Other) := by
  intro he
  cases he

theorem tagged_header_injective :
    Function.Injective (TaggedIndex.header : Header T Side → TaggedIndex T Side Other) := by
  intro h k he
  cases he
  rfl

end Tilings.HeaderKernel
