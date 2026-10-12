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
private lemma iterate_support_translateSet (v : Pt) (S : Set (PlacedTile P)) :
    support (translateSet v S) = v +ᵥ support S := by
  ext x
  simp only [support, translateSet, PlacedTile.translate, PlacedTile.carrier, mem_iUnion,
    mem_image, mem_vadd_set_iff_neg_vadd_mem]
  constructor
  · rintro ⟨A, ⟨B, hB, rfl⟩, hx⟩
    exact ⟨B, hB, by simpa [←add_assoc] using hx⟩
  · rintro ⟨A, hA, hx⟩
    refine ⟨⟨A.form, v +ᵥ A.anchor⟩, ⟨A, hA, rfl⟩, ?_⟩
    simpa [←add_assoc] using hx

private lemma iterate_support_decomposeTile (A : PlacedTile P) :
    support (τ.decomposeTile A) = τ.θ • A.carrier := by
  dsimp [decomposeTile]
  rw [iterate_support_translateSet, τ.support_eq, PlacedTile.carrier]
  ext x
  simp only [mem_vadd_set_iff_neg_vadd_mem, mem_smul_set]
  constructor
  · rintro ⟨y, hy, hx⟩
    refine ⟨A.anchor + y, ?_, ?_⟩
    · simpa
    · rw [smul_add]
      calc τ.θ • A.anchor + τ.θ • y = τ.θ • A.anchor + (-(τ.θ • A.anchor) + x) := by congr 1
        _ = x := by abel
  · rintro ⟨y, hy, rfl⟩
    refine ⟨-A.anchor + y, ?_, ?_⟩
    · simpa
    · simp [smul_add]

private lemma iterate_support_decompose (S : Set (PlacedTile P)) :
    support (τ.decompose S) = τ.θ • support S := by
  dsimp [decompose, support]
  rw [smul_set_iUnion₂]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨A, ⟨B, hB, hA⟩, hx⟩
    refine ⟨B, hB, ?_⟩
    have h : x ∈ support (τ.decomposeTile B) := by
      simp only [support, mem_iUnion]
      exact ⟨A, hA, hx⟩
    rw [iterate_support_decomposeTile] at h
    exact h
  · rintro ⟨A, hA, hx⟩
    have h : x ∈ support (τ.decomposeTile A) := by
      rw [iterate_support_decomposeTile]
      exact hx
    simp only [support, mem_iUnion] at h
    rcases h with ⟨B, hB, hx'⟩
    exact ⟨B, ⟨A, hA, hB⟩, hx'⟩

theorem iterate_support (n : ℕ) (p : P.Form) :
    support (τ.supertile n p) = (τ.θ ^ n) • (P.disk p).carrier := by
  induction' n with n ih
  · dsimp [supertile, decomposeIter, support, PlacedTile.carrier]
    ext x
    simp
  · change support (τ.decompose (τ.supertile n p)) = τ.θ ^ (n + 1) • (P.disk p).carrier
    rw [iterate_support_decompose]
    rw [ih, smul_smul, pow_succ']

private lemma decomposeTile_inv_eq (B : PlacedTile P) :
    {A : PlacedTile P | B ∈ τ.decomposeTile A} =
    ⋃ (p : P.Form) (C ∈ (τ.rule p).tiles) (_h : C.form = B.form),
       { (⟨p, τ.θ⁻¹ • (B.anchor -ᵥ C.anchor)⟩ : PlacedTile P) } := by
  ext A
  simp only [decomposeTile, translateSet, PlacedTile.translate, mem_setOf_eq, mem_image, mem_iUnion,
    mem_singleton_iff]
  constructor
  · rintro ⟨C, hC, hB⟩
    use A.form, C, hC
    have h1 : C.form = B.form := by rw [← hB]
    use h1
    have h2 : τ.θ • A.anchor +ᵥ C.anchor = B.anchor := congrArg PlacedTile.anchor hB
    have h3 : τ.θ • A.anchor = B.anchor -ᵥ C.anchor := by rw [← h2, vadd_vsub]
    have h4 : τ.θ⁻¹ • τ.θ • A.anchor = τ.θ⁻¹ • (B.anchor -ᵥ C.anchor) := congrArg (τ.θ⁻¹ • ·) h3
    have h5 : τ.θ ≠ 0 := by linarith [τ.one_lt]
    have h6 : A.anchor = τ.θ⁻¹ • (B.anchor -ᵥ C.anchor) := by
      rw [← h4]
      exact (inv_smul_smul₀ h5 A.anchor).symm
    cases A
    dsimp at h6 ⊢
    subst h6
    rfl
  · rintro ⟨p, C, hC, h1, h2⟩
    have hp : p = A.form := congrArg PlacedTile.form h2.symm
    subst hp
    use C, hC
    have h3 : A.anchor = τ.θ⁻¹ • (B.anchor -ᵥ C.anchor) := congrArg PlacedTile.anchor h2
    cases B with
    | mk form anchor =>
      dsimp at h1
      subst h1
      have ht : { form := C.form, anchor := τ.θ • A.anchor +ᵥ C.anchor : PlacedTile P } =
          { form := C.form, anchor := anchor } := by
        congr 1
        dsimp at h3 ⊢
        rw [h3]
        have h5 : τ.θ ≠ 0 := by linarith [τ.one_lt]
        have h6 : (τ.θ • τ.θ⁻¹ • (anchor -ᵥ C.anchor : Pt) : Pt) = anchor -ᵥ C.anchor :=
          smul_inv_smul₀ h5 _
        exact Eq.trans (congrArg (· +ᵥ C.anchor) h6) (vsub_vadd anchor C.anchor)
      exact ht

/-- `lem:finiteparents` (finite parents): a fixed placed child has only
finitely many possible placed parents under `τ`. -/
theorem finite_parents (B : PlacedTile P) :
    {A : PlacedTile P | B ∈ τ.decomposeTile A}.Finite := by
  rw [decomposeTile_inv_eq]
  apply finite_iUnion
  intro p
  apply Finite.biUnion
  · exact (τ.rule p).finite
  · intro C _
    apply finite_iUnion
    intro _
    exact finite_singleton _

/-- `lem:sts-flc`: under STS the allowed pointed crowns form a finite set
(they are normalized to centre `0`, i.e. taken up to translation).
This is the manifest name of the fact stated in `Main.lean` as `STS.flc`. -/
theorem STS.finite_crowns (h : τ.STS) : τ.FLC := by
  sorry

end Substitution

/-! ## `lem:substitution-hierarchy` -/

namespace SubstitutionTiling

/-- Step 1 of the blueprint proof of `exists_composition`: by thinning a sequence
of parent covers using the finite-parent lemma (or by Kőnig's lemma on a finite inverse
system), there exists a global parent assignment `T'` whose decomposition covers `T`
and whose finite patches occur in supertiles. -/
private lemma exists_composition_step1_parents (τ : Substitution P) {T : PlaneTiling P}
    (hT : τ.IsSubstitutionTiling T) :
    ∃ T' : Set (PlacedTile P),
      (∀ F' ⊆ T', F'.Finite → ∃ (n : ℕ) (p : P.Form), OccursIn F' (τ.supertile n p)) ∧
      T.tiles ⊆ τ.decompose T' := by
  sorry

/-- Step 2 of the blueprint proof of `exists_composition`: a parent assignment whose finite
patches occur in supertiles must have disjoint interiors. -/
private lemma exists_composition_step2_disjoint (τ : Substitution P) (T' : Set (PlacedTile P))
    (h_subst : ∀ F' ⊆ T', F'.Finite → ∃ (n : ℕ) (p : P.Form), OccursIn F' (τ.supertile n p)) :
    DisjointInteriors T' := by
  sorry

/-- Step 3 of the blueprint proof of `exists_composition`: no extra child can occur in
the decomposition because the plane is already covered by `T` with disjoint interiors,
so the decomposition is exactly `T`. -/
private lemma exists_composition_step3_decompose_eq (τ : Substitution P) {T : PlaneTiling P}
    (T' : Set (PlacedTile P))
    (h_disj : DisjointInteriors T') (h_cov : T.tiles ⊆ τ.decompose T') :
    τ.decompose T' = T.tiles := by
  sorry

/-- Step 4 of the blueprint proof of `exists_composition`: scaling gives coverage of the
parent plane, so `T'` covers the plane. -/
private lemma exists_composition_step4_cover (τ : Substitution P) (T' : Set (PlacedTile P))
    {T : PlaneTiling P} (h_decomp : τ.decompose T' = T.tiles) :
    support T' = univ := by
  sorry

/-- `lem:substitution-hierarchy`: every substitution plane tiling has a
composition which is again a substitution plane tiling. -/
theorem exists_composition (τ : Substitution P) {T : PlaneTiling P}
    (hT : τ.IsSubstitutionTiling T) :
    ∃ T' : PlaneTiling P, τ.IsComposition T' T ∧ τ.IsSubstitutionTiling T' := by
  rcases exists_composition_step1_parents τ hT with ⟨T'_set, h_subst, h_subset⟩
  have h_disj := exists_composition_step2_disjoint τ T'_set h_subst
  have h_decomp := exists_composition_step3_decompose_eq τ T'_set h_disj h_subset
  have h_cov := exists_composition_step4_cover τ T'_set h_decomp
  let T' : PlaneTiling P := ⟨T'_set, h_cov, h_disj⟩
  use T'
  exact ⟨h_decomp, h_subst⟩

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
