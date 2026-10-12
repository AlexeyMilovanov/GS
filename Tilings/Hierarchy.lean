import Tilings.Basic

/-!
# Hierarchies, compositions, powers (skeleton)

Statements of the blueprint nodes of `models.tex` and two nodes of
`crowns.tex`/`main.tex` that only need the basic model:

* `lem:localfinite`        — `PlaneTiling.locallyFinite`, `PlaneTiling.countable`
* `lem:finiteparents`      — `Substitution.iterate_support`, `Substitution.finite_parents`
* `lem:substitution-hierarchy` — `SubstitutionTiling.exists_composition`
* `lem:hierarchy-step`     — `hierarchical_power_iff`
* `lem:finite-idempotent`  — `FiniteMap.exists_idempotent_iterate` (proved)
* `lem:sts-flc`            — `Substitution.STS.finite_crowns`
* `lem:covered-tile-belongs` — `Patch.mem_of_carrier_subset_union`
* `lem:allowed-hierarchy`  — `allowed_crowns_hierarchy_is_substitutive`

All proofs except `FiniteMap.exists_idempotent_iterate` are `sorry`.
-/

open Set Pointwise

noncomputable section

namespace Tilings

open Substitution

variable {P : Protoset}

/-! ## `lem:localfinite` -/

namespace PlaneTiling

/-- `lem:localfinite` (local finiteness): every compact set meets only
finitely many tiles of a plane tiling by a finite protoset. -/
theorem locallyFinite (T : PlaneTiling P) {K : Set Pt} (hK : IsCompact K) :
    {A ∈ T.tiles | (A.carrier ∩ K).Nonempty}.Finite := by
  sorry

/-- `lem:localfinite` (countability): a plane tiling has countably many tiles. -/
theorem countable (T : PlaneTiling P) : T.tiles.Countable := by
  have H_disj : T.tiles.PairwiseDisjoint (fun A => interior A.carrier) := T.disjoint
  have H_open : ∀ A ∈ T.tiles, IsOpen (interior A.carrier) := fun A _ => isOpen_interior
  have H_nonempty : ∀ A ∈ T.tiles, (interior A.carrier).Nonempty := by
    intro A _
    have hc : A.carrier = A.anchor +ᵥ (P.disk A.form).carrier := rfl
    rw [hc, interior_vadd]
    exact (P.disk A.form).interior_nonempty.image (A.anchor +ᵥ ·)
  exact H_disj.countable_of_isOpen H_open H_nonempty

end PlaneTiling

/-! ## `lem:finiteparents` -/

namespace Substitution

variable (τ : Substitution P)

/-- `lem:finiteparents` (supports): the support of the supertile `τ^n p`
(anchored at the origin) is `θ^n • B_p`. -/
theorem iterate_support (n : ℕ) (p : P.Form) :
    support (τ.supertile n p) = (τ.θ ^ n) • (P.disk p).carrier := by
  sorry

/-- `lem:finiteparents` (finite parents): a fixed placed child has only
finitely many possible placed parents under `τ`. -/
theorem finite_parents (B : PlacedTile P) :
    {A : PlacedTile P | B ∈ τ.decomposeTile A}.Finite := by
  sorry

/-- `lem:sts-flc`: under STS the allowed pointed crowns form a finite set
(they are normalized to centre `0`, i.e. taken up to translation).
This is the manifest name of the fact stated in `Main.lean` as `STS.flc`. -/
theorem STS.finite_crowns (h : τ.STS) : τ.FLC := by
  sorry

end Substitution

/-! ## `lem:substitution-hierarchy` -/

namespace SubstitutionTiling

/-- `lem:substitution-hierarchy`: every substitution plane tiling has a
composition which is again a substitution plane tiling. -/
theorem exists_composition (τ : Substitution P) {T : PlaneTiling P}
    (hT : τ.IsSubstitutionTiling T) :
    ∃ T' : PlaneTiling P, τ.IsComposition T' T ∧ τ.IsSubstitutionTiling T' := by
  sorry

end SubstitutionTiling

/-! ## `lem:hierarchy-step` -/

/-- `lem:hierarchy-step`: for `m > 0`, a plane tiling is `τ`-hierarchical
iff it is `τ^m`-hierarchical.  (Side-to-side hierarchy is *not* claimed to
transfer; that needs the alignment tuples.) -/
theorem hierarchical_power_iff (τ : Substitution P) (m : ℕ) (hm : 0 < m)
    (T : PlaneTiling P) :
    τ.IsHierarchical T ↔ (τ.pow m hm).IsHierarchical T := by
  sorry

/-! ## `lem:finite-idempotent` -/

namespace FiniteMap

/-- `lem:finite-idempotent`: an endofunction of a finite type has an
idempotent positive iterate: `c^[2ℓ] = c^[ℓ]` for some `ℓ > 0`. -/
theorem exists_idempotent_iterate {S : Type*} [Finite S] (c : S → S) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ c^[2 * ℓ] = c^[ℓ] := by
  have main : ∀ a p : ℕ, 0 < p → c^[a] = c^[a + p] →
      ∃ ℓ : ℕ, 0 < ℓ ∧ c^[2 * ℓ] = c^[ℓ] := by
    intro a p hp heq
    have key : ∀ k : ℕ, c^[a + k * p] = c^[a] := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show a + (k + 1) * p = k * p + (a + p) by ring,
          Function.iterate_add c (k * p) (a + p), ← heq,
          ← Function.iterate_add c (k * p) a, Nat.add_comm (k * p) a, ih]
    have key' : ∀ n : ℕ, a ≤ n → ∀ k : ℕ, c^[n + k * p] = c^[n] := by
      intro n hn k
      obtain ⟨m, rfl⟩ : ∃ m, n = a + m := ⟨n - a, by omega⟩
      rw [show a + m + k * p = m + (a + k * p) by ring,
        Function.iterate_add c m (a + k * p), key k,
        ← Function.iterate_add c m a, Nat.add_comm m a]
    refine ⟨(a + 1) * p, Nat.mul_pos (Nat.succ_pos a) hp, ?_⟩
    rw [two_mul]
    have hle : a ≤ (a + 1) * p :=
      calc a ≤ (a + 1) * 1 := by omega
        _ ≤ (a + 1) * p := Nat.mul_le_mul (le_refl _) hp
    exact key' _ hle (a + 1)
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => c^[n])
  have heq' : c^[a] = c^[b] := heq
  rcases lt_or_gt_of_ne hab with h | h
  · exact main a (b - a) (by omega) (by rw [Nat.add_sub_of_le h.le]; exact heq')
  · exact main b (a - b) (by omega) (by rw [Nat.add_sub_of_le h.le]; exact heq'.symm)

end FiniteMap

/-! ## `lem:covered-tile-belongs` -/

namespace Patch

/-- `lem:covered-tile-belongs`: if a tile `X` has interior disjoint from the
interior of every tile of the finite patch `F` other than `X`, and the carrier
of `X` is covered by the support of `F`, then `X ∈ F`. -/
theorem mem_of_carrier_subset_union (F : Patch P) (X : PlacedTile P)
    (hdisj : ∀ A ∈ F.tiles, A ≠ X → Disjoint (interior X.carrier) (interior A.carrier))
    (hsub : X.carrier ⊆ support F.tiles) : X ∈ F.tiles := by
  sorry

end Patch

/-! ## `lem:allowed-hierarchy` -/

/-- `lem:allowed-hierarchy`: if `τ` has FLC and `T = seq 0, seq 1, …` is a
`τ^m`-hierarchy (`seq k` plays the role of `T_{km}`) all of whose full
pointed crowns, at every level and every listed vertex, are `τ`-allowed,
then `T` is a `τ`-substitution tiling. -/
theorem allowed_crowns_hierarchy_is_substitutive (τ : Substitution P) (hflc : τ.FLC)
    (m : ℕ) (hm : 0 < m) (seq : ℕ → PlaneTiling P)
    (hseq : ∀ k, (τ.pow m hm).IsComposition (seq (k + 1)) (seq k))
    (hcrown : ∀ k (w : Pt), IsVertexOf (seq k).tiles w →
      τ.IsAllowedCrown (translateSet (-w) (crown (seq k).tiles w))) :
    τ.IsSubstitutionTiling (seq 0) := by
  sorry

end Tilings

end
