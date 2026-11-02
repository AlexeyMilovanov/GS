import Enforce.Basic

/-!
# Local non-separation by a low-dimensional cell

The reusable topological nodes CS1–CS14 of the cell-separation blueprint. Brouwer's
fixed point theorem is an explicit hypothesis, so this module is independent of Routing.
-/

namespace Enforce

noncomputable section

open Metric Set

namespace CellSeparation

/-- CS1: `X` topological space, `g : C(X, ↥(sphere (0 : E n) 1))`, `p ∈ sphere 0 1`,
`∀ x, (g x : E n) ≠ p` ⇒ `g.Nullhomotopic`. -/
theorem nullhomotopic_of_ne (n : ℕ) {X : Type*} [TopologicalSpace X]
    (g : C(X, ↥(sphere (0 : E n) 1))) (p : E n) (hp : p ∈ sphere (0 : E n) 1)
    (hne : ∀ x, (g x : E n) ≠ p) : g.Nullhomotopic := by
  have hpNorm : ‖p‖ = 1 := by simpa using hp
  let v : ↥(Icc (0 : ℝ) 1) × X → E n :=
    fun z => (1 - (z.1 : ℝ)) • (g z.2 : E n) - (z.1 : ℝ) • p
  have hv : ∀ z, v z ≠ 0 := by
    rintro ⟨t, x⟩ hz
    have heq : (1 - (t : ℝ)) • (g x : E n) = (t : ℝ) • p := sub_eq_zero.mp hz
    have ht : 1 - (t : ℝ) = (t : ℝ) := by
      have h := congrArg norm heq
      have hgNorm : ‖(g x : E n)‖ = 1 := by simp
      simpa [norm_smul, hgNorm, hpNorm, abs_of_nonneg t.property.1,
        abs_of_nonneg (sub_nonneg.mpr t.property.2)] using h
    have ht0 : (t : ℝ) ≠ 0 := by linarith
    exact hne x (smul_right_injective (E n) ht0 (by simpa [ht] using heq))
  have hvCont : Continuous v :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (g.continuous.comp continuous_snd))).sub
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const)
  refine ⟨⟨-p, by simpa [mem_sphere, dist_zero_right] using hpNorm⟩, ⟨?_⟩⟩
  refine
    { toFun := fun z => ⟨‖v z‖⁻¹ • v z, ?_⟩
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }
  · rw [mem_sphere, dist_zero_right, norm_smul, norm_inv,
      Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hv z))]
  · exact ((hvCont.norm.inv₀ fun z => norm_ne_zero_iff.mpr (hv z)).smul hvCont).subtype_mk _
  · intro x
    apply Subtype.ext
    have hgNorm : ‖(g x : E n)‖ = 1 := by simp
    simp [v, hgNorm]
  · intro x
    apply Subtype.ext
    simp [v, hpNorm]

/-- CS2: `radialMap (a : E n) (Y : Set (E n)) (ha : a ∉ Y)` is the continuous map
`y ↦ ‖y - a‖⁻¹ • (y - a)` to the unit sphere. -/
def radialMap (n : ℕ) (a : E n) (Y : Set (E n)) (ha : a ∉ Y) :
    C(↥Y, ↥(sphere (0 : E n) 1)) where
  toFun y := ⟨‖(y : E n) - a‖⁻¹ • ((y : E n) - a), by
    have hne : (y : E n) - a ≠ 0 := sub_ne_zero.mpr fun h => ha (h ▸ y.property)
    rw [mem_sphere, dist_zero_right, norm_smul, norm_inv,
      Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hsub : Continuous fun y : Y => (y : E n) - a :=
      continuous_subtype_val.sub continuous_const
    exact (hsub.norm.inv₀ fun y => norm_ne_zero_iff.mpr
      (sub_ne_zero.mpr fun h => ha (h ▸ y.property))).smul hsub

/-- CS3: `Y ⊆ closedBall 0 R`, `R < ‖a‖` (so `a ∉ Y`) ⇒
`(radialMap n a Y ha).Nullhomotopic`. The dimension is positive so the sphere is nonempty. -/
theorem radialMap_nullhomotopic_of_far (n : ℕ) (hn : 1 ≤ n) (Y : Set (E n)) (R : ℝ)
    (hY : Y ⊆ closedBall (0 : E n) R) (a : E n) (hfar : R < ‖a‖) (ha : a ∉ Y) :
    (radialMap n a Y ha).Nullhomotopic := by
  classical
  by_cases hne : Y.Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hR : 0 ≤ R := (norm_nonneg y₀).trans (by simpa using hY hy₀)
    have haNorm : 0 < ‖a‖ := lt_of_le_of_lt hR hfar
    have hp : ‖a‖⁻¹ • a ∈ sphere (0 : E n) 1 := by
      rw [mem_sphere, dist_zero_right, norm_smul, norm_inv,
        Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ haNorm.ne']
    apply nullhomotopic_of_ne n _ _ hp
    intro y heq
    have hd : (y : E n) - a ≠ 0 := sub_ne_zero.mpr fun h => ha (h ▸ y.property)
    have hdNorm : 0 < ‖(y : E n) - a‖ := norm_pos_iff.mpr hd
    have heq' : ‖(y : E n) - a‖⁻¹ • ((y : E n) - a) = ‖a‖⁻¹ • a := heq
    have hv : (y : E n) - a = (‖(y : E n) - a‖ / ‖a‖) • a := by
      calc
        (y : E n) - a = ‖(y : E n) - a‖ •
            (‖(y : E n) - a‖⁻¹ • ((y : E n) - a)) := by
          rw [smul_smul, mul_inv_cancel₀ hdNorm.ne', one_smul]
        _ = (‖(y : E n) - a‖ / ‖a‖) • a := by
          rw [heq', smul_smul, div_eq_mul_inv]
    have hy : (y : E n) = (1 + ‖(y : E n) - a‖ / ‖a‖) • a := by
      rw [add_smul, one_smul, ← hv]
      abel
    have hyNorm : ‖(y : E n)‖ = ‖a‖ + ‖(y : E n) - a‖ := by
      calc
        ‖(y : E n)‖ = (1 + ‖(y : E n) - a‖ / ‖a‖) * ‖a‖ := by
          conv_lhs => rw [hy]
          rw [norm_smul, Real.norm_of_nonneg (by positivity)]
        _ = ‖a‖ + ‖(y : E n) - a‖ := by field_simp
    have hyR : ‖(y : E n)‖ ≤ R := by simpa using hY y.property
    linarith
  · let p : E n := EuclideanSpace.single ⟨0, hn⟩ 1
    have hp : p ∈ sphere (0 : E n) 1 := by simp [p]
    exact nullhomotopic_of_ne n _ p hp fun y => (hne ⟨y, y.property⟩).elim

/-- CS4: `a a' ∉ Y`, `JoinedIn Yᶜ a a'` ⇒
`(radialMap n a Y ha).Homotopic (radialMap n a' Y ha')`. -/
theorem radialMap_homotopic_of_joinedIn (n : ℕ) (Y : Set (E n)) (a a' : E n)
    (ha : a ∉ Y) (ha' : a' ∉ Y) (hjoin : JoinedIn Yᶜ a a') :
    (radialMap n a Y ha).Homotopic (radialMap n a' Y ha') := by
  let γ := hjoin.somePath
  let v : ↥(Icc (0 : ℝ) 1) × ↥Y → E n := fun z => (z.2 : E n) - γ z.1
  have hv : ∀ z, v z ≠ 0 := by
    intro z hz
    have heq : (z.2 : E n) = γ z.1 := sub_eq_zero.mp hz
    exact hjoin.somePath_mem z.1 (heq ▸ z.2.property)
  have hvCont : Continuous v :=
    (continuous_subtype_val.comp continuous_snd).sub (γ.continuous.comp continuous_fst)
  refine ⟨{ toFun := fun z => ⟨‖v z‖⁻¹ • v z, ?_⟩
            continuous_toFun := ?_
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · rw [mem_sphere, dist_zero_right, norm_smul, norm_inv,
      Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hv z))]
  · exact ((hvCont.norm.inv₀ fun z => norm_ne_zero_iff.mpr (hv z)).smul hvCont).subtype_mk _
  · intro y
    apply Subtype.ext
    simp [v, γ, radialMap]
  · intro y
    apply Subtype.ext
    simp [v, γ, radialMap]

/-- CS5: `Y ⊆ closedBall 0 R`, `a ∉ Y`,
`∃ a', JoinedIn Yᶜ a a' ∧ R < ‖a'‖` ⇒ nullhomotopic, in positive ambient dimension. -/
theorem radialMap_nullhomotopic_of_escape (n : ℕ) (hn : 1 ≤ n) (Y : Set (E n)) (R : ℝ)
    (hY : Y ⊆ closedBall (0 : E n) R) (a : E n) (ha : a ∉ Y)
    (hescape : ∃ a', JoinedIn Yᶜ a a' ∧ R < ‖a'‖) :
    (radialMap n a Y ha).Nullhomotopic := by
  obtain ⟨a', hjoin, hfar⟩ := hescape
  have ha' : a' ∉ Y := hjoin.target_mem
  have h1 := radialMap_homotopic_of_joinedIn n Y a a' ha ha' hjoin
  have h2 := radialMap_nullhomotopic_of_far n hn Y R hY a' hfar ha'
  rcases h2 with ⟨y, hy⟩
  exact ⟨y, h1.trans hy⟩

/-- CS6: `m + 1 ≤ n`, `G : E m → E n`, `ContDiff ℝ 1 G` ⇒
`volume {z : E n | ∃ t : ℝ, ∃ y ∈ sphere (0 : E m) 1, z = t • G y} = 0`. -/
theorem cone_image_null (m n : ℕ) (hmn : m + 1 ≤ n) (G : E m → E n)
    (hG : ContDiff ℝ 1 G) :
    MeasureTheory.volume
      {z : E n | ∃ t : ℝ, ∃ y ∈ sphere (0 : E m) 1, z = t • G y} = 0 := by
  sorry

/-- CS7: The same hypotheses as CS6 imply `∃ p ∈ sphere (0 : E n) 1,
∀ t : ℝ, ∀ y ∈ sphere (0 : E m) 1, t • G y ≠ p`. -/
theorem exists_direction_off_cone (m n : ℕ) (hmn : m + 1 ≤ n) (G : E m → E n)
    (hG : ContDiff ℝ 1 G) :
    ∃ p ∈ sphere (0 : E n) 1, ∀ t : ℝ, ∀ y ∈ sphere (0 : E m) 1, t • G y ≠ p := by
  by_contra h
  push_neg at h
  let S := {z : E n | ∃ t : ℝ, ∃ y ∈ sphere (0 : E m) 1, z = t • G y}
  have h_sub : (univ : Set (E n)) ⊆ S ∪ {0} := by
    intro z _
    by_cases hz0 : z = 0
    · right; exact hz0
    · left
      have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
      obtain ⟨t, y, hy, hty⟩ := h (‖z‖⁻¹ • z) (by rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn])
      use ‖z‖ * t, y, hy
      have hty_symm : ‖z‖⁻¹ • z = t • G y := hty.symm
      rw [mul_smul, ← hty_symm, smul_smul, mul_inv_cancel₀ hn, one_smul]
  have h_meas : MeasureTheory.volume (univ : Set (E n)) ≤ MeasureTheory.volume S + MeasureTheory.volume ({0} : Set (E n)) := by
    calc MeasureTheory.volume (univ : Set (E n)) ≤ MeasureTheory.volume (S ∪ {0}) := MeasureTheory.measure_mono h_sub
      _ ≤ MeasureTheory.volume S + MeasureTheory.volume ({0} : Set (E n)) := MeasureTheory.measure_union_le S {0}
  have hS : MeasureTheory.volume S = 0 := cone_image_null m n hmn G hG
  haveI : Nontrivial (E n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by have hE : Module.finrank ℝ (E n) = n := finrank_euclideanSpace_fin; rw [hE]; exact (by linarith : 1 ≤ n))
  have h0 : MeasureTheory.volume ({0} : Set (E n)) = 0 := MeasureTheory.measure_singleton (0 : E n)
  rw [hS, h0, add_zero] at h_meas
  exact (IsOpen.measure_pos MeasureTheory.volume isOpen_univ ⟨0, mem_univ 0⟩).ne.symm (nonpos_iff_eq_zero.mp h_meas)


/-- Step 1 of the V4 proof of `nullhomotopic_sphere_to_sphere`: smooth approximation. -/
private lemma nullhomotopic_sphere_to_sphere_step1_approx (m n : ℕ)
    (g : C(↥(sphere (0 : E m) 1), ↥(sphere (0 : E n) 1))) :
    ∃ G : E m → E n, ContDiff ℝ 1 G ∧ ∀ y : ↥(sphere (0 : E m) 1), ‖(g y : E n) - G (y : E m)‖ < 1 := by
  sorry

/-- Step 2 of the V4 proof of `nullhomotopic_sphere_to_sphere`: homotopy missing a point. -/
private lemma nullhomotopic_sphere_to_sphere_step2_homotopic (m n : ℕ)
    (g : C(↥(sphere (0 : E m) 1), ↥(sphere (0 : E n) 1))) (G : E m → E n)
    (h_approx : ∀ y : ↥(sphere (0 : E m) 1), ‖(g y : E n) - G (y : E m)‖ < 1)
    (p : E n) (hp : p ∈ sphere (0 : E n) 1)
    (h_miss : ∀ t : ℝ, ∀ y ∈ sphere (0 : E m) 1, t • G y ≠ p) :
    g.Nullhomotopic := by
  sorry

/-- CS8: `1 ≤ m`, `m < n`,
`g : C(↥(sphere (0 : E m) 1), ↥(sphere (0 : E n) 1))` ⇒ `g.Nullhomotopic`.
This is `π_(m-1)(S^(n-1)) = 0`. -/
theorem nullhomotopic_sphere_to_sphere (m n : ℕ) (hm : 1 ≤ m) (hmn : m < n)
    (g : C(↥(sphere (0 : E m) 1), ↥(sphere (0 : E n) 1))) : g.Nullhomotopic := by
  obtain ⟨G, hG_diff, hG_approx⟩ := nullhomotopic_sphere_to_sphere_step1_approx m n g
  have hmn_le : m + 1 ≤ n := by omega
  obtain ⟨p, hp, h_miss⟩ := exists_direction_off_cone m n hmn_le G hG_diff
  exact nullhomotopic_sphere_to_sphere_step2_homotopic m n g G hG_approx p hp h_miss

private lemma extend_sphere_to_closedBall_of_nullhomotopic_step1_t (m : ℕ) (p : E m) (hp : p ∈ closedBall (0 : E m) 1) :
    1 - ‖p‖ ∈ Icc (0 : ℝ) 1 := by
  rw [mem_closedBall, dist_zero_right] at hp
  exact ⟨by linarith, by have := norm_nonneg p; linarith⟩

private lemma extend_sphere_to_closedBall_of_nullhomotopic_step2_y (m : ℕ) (p : E m) (hp0 : p ≠ 0) :
    ‖p‖⁻¹ • p ∈ sphere (0 : E m) 1 := by
  rw [mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_pos_iff.mpr hp0).ne']

/-- Step 3a of the V4 proof of extend_sphere_to_closedBall_of_nullhomotopic (V4 CS9): continuous away from 0. -/
private lemma extend_sphere_to_closedBall_of_nullhomotopic_step3a_continuousOn_ne_zero
    (m : ℕ) {Z : Type*} [TopologicalSpace Z] (g : C(↥(sphere (0 : E m) 1), Z))
    (x : Z) (H : g.Homotopy (ContinuousMap.const _ x)) :
    ContinuousOn (fun p : ↥(closedBall (0 : E m) 1) =>
      if hp : (p : E m) = 0 then x else
      H (⟨1 - ‖(p:E m)‖, extend_sphere_to_closedBall_of_nullhomotopic_step1_t m p p.2⟩,
         ⟨‖(p:E m)‖⁻¹ • (p:E m), extend_sphere_to_closedBall_of_nullhomotopic_step2_y m p hp⟩))
    {p : ↥(closedBall (0 : E m) 1) | (p : E m) ≠ 0} := by
  sorry

/-- Step 3b of the V4 proof of extend_sphere_to_closedBall_of_nullhomotopic (V4 CS9): continuous at 0. -/
private lemma extend_sphere_to_closedBall_of_nullhomotopic_step3b_continuousAt_zero
    (m : ℕ) {Z : Type*} [TopologicalSpace Z] (g : C(↥(sphere (0 : E m) 1), Z))
    (x : Z) (H : g.Homotopy (ContinuousMap.const _ x)) :
    ContinuousAt (fun p : ↥(closedBall (0 : E m) 1) =>
      if hp : (p : E m) = 0 then x else
      H (⟨1 - ‖(p:E m)‖, extend_sphere_to_closedBall_of_nullhomotopic_step1_t m p p.2⟩,
         ⟨‖(p:E m)‖⁻¹ • (p:E m), extend_sphere_to_closedBall_of_nullhomotopic_step2_y m p hp⟩))
    ⟨0, by simp⟩ := by
  sorry

/-- Step 3 of the V4 proof of extend_sphere_to_closedBall_of_nullhomotopic (V4 CS9): continuous over the closed ball. -/
private lemma extend_sphere_to_closedBall_of_nullhomotopic_step3_continuous
    (m : ℕ) {Z : Type*} [TopologicalSpace Z] (g : C(↥(sphere (0 : E m) 1), Z))
    (x : Z) (H : g.Homotopy (ContinuousMap.const _ x)) :
    ∃ F : C(↥(closedBall (0 : E m) 1), Z),
      (F ⟨0, by simp⟩ = x) ∧
      (∀ (p : ↥(closedBall (0 : E m) 1)) (hp0 : (p : E m) ≠ 0),
        F p = H (⟨1 - ‖(p : E m)‖, extend_sphere_to_closedBall_of_nullhomotopic_step1_t m p p.2⟩,
                 ⟨‖(p : E m)‖⁻¹ • (p : E m), extend_sphere_to_closedBall_of_nullhomotopic_step2_y m p hp0⟩)) := by
  let f : ↥(closedBall (0 : E m) 1) → Z := fun p =>
    if hp : (p : E m) = 0 then x else
    H (⟨1 - ‖(p : E m)‖, extend_sphere_to_closedBall_of_nullhomotopic_step1_t m p p.2⟩,
       ⟨‖(p : E m)‖⁻¹ • (p : E m), extend_sphere_to_closedBall_of_nullhomotopic_step2_y m p hp⟩)
  have h_cont_ne_zero := extend_sphere_to_closedBall_of_nullhomotopic_step3a_continuousOn_ne_zero m g x H
  have h_cont_zero := extend_sphere_to_closedBall_of_nullhomotopic_step3b_continuousAt_zero m g x H
  have h_cont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro p
    by_cases hp : (p : E m) = 0
    · have eq_p : p = ⟨0, by simp⟩ := Subtype.ext hp
      rw [eq_p]
      exact h_cont_zero
    · have H_open : IsOpen {p : ↥(closedBall (0 : E m) 1) | (p : E m) ≠ 0} := by
        exact (isClosed_singleton (x := (0 : E m))).isOpen_compl.preimage continuous_subtype_val
      exact h_cont_ne_zero.continuousAt (H_open.mem_nhds hp)
  use ⟨f, h_cont⟩
  constructor
  · dsimp [f]
    rw [dif_pos (by rfl)]
  · intro p hp0
    dsimp [f]
    rw [dif_neg hp0]

/-- CS9: `1 ≤ m`, `Z` topological space, `g : C(↥(sphere (0 : E m) 1), Z)`
nullhomotopic ⇒ a continuous extension over `closedBall (0 : E m) 1` agreeing on the sphere. -/
theorem extend_sphere_to_closedBall_of_nullhomotopic (m : ℕ) (hm : 1 ≤ m)
    {Z : Type*} [TopologicalSpace Z] (g : C(↥(sphere (0 : E m) 1), Z))
    (hg : g.Nullhomotopic) :
    ∃ F : C(↥(closedBall (0 : E m) 1), Z), ∀ y (hy : y ∈ sphere (0 : E m) 1),
      F ⟨y, sphere_subset_closedBall hy⟩ = g ⟨y, hy⟩ := by
  obtain ⟨x, ⟨H⟩⟩ := hg
  obtain ⟨F, _, hF_ne_zero⟩ := extend_sphere_to_closedBall_of_nullhomotopic_step3_continuous m g x H
  use F
  intro y hy
  have _ := hm -- to suppress unused warning
  have hy0 : (y : E m) ≠ 0 := by
    rintro rfl
    rw [mem_sphere, dist_zero_right, norm_zero] at hy
    norm_num at hy
  have hy1 : ‖(y : E m)‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hy
  have hF_eval := hF_ne_zero ⟨y, sphere_subset_closedBall hy⟩ hy0
  have hyt : 1 - ‖(y : E m)‖ = 0 := by simp [hy1]
  have hyy : ‖(y : E m)‖⁻¹ • (y : E m) = y := by simp [hy1]
  have eq_t : (⟨1 - ‖(y : E m)‖, extend_sphere_to_closedBall_of_nullhomotopic_step1_t m y (sphere_subset_closedBall hy)⟩ : unitInterval) = (0 : unitInterval) := Subtype.ext hyt
  have eq_y : (⟨‖(y : E m)‖⁻¹ • (y : E m), extend_sphere_to_closedBall_of_nullhomotopic_step2_y m y hy0⟩ : ↥(sphere (0 : E m) 1)) = (⟨y, hy⟩ : ↥(sphere (0 : E m) 1)) := Subtype.ext hyy
  rw [hF_eval, eq_t, eq_y]
  exact H.apply_zero ⟨y, hy⟩

/-- CS10: `X ⊆ E n` compact, `F ⊆ X` closed,
`f : C(↥F, ↥(sphere (0 : E n) 1))` nullhomotopic ⇒ a continuous extension over `X`
agreeing on `F` (Borsuk's extension lemma). -/
theorem exists_extension_of_nullhomotopic (n : ℕ) (X F : Set (E n))
    (hX : IsCompact X) (hF : IsClosed F) (hFX : F ⊆ X)
    (f : C(↥F, ↥(sphere (0 : E n) 1))) (hf : f.Nullhomotopic) :
    ∃ g : C(↥X, ↥(sphere (0 : E n) 1)), ∀ x (hx : x ∈ F),
      g ⟨x, hFX hx⟩ = f ⟨x, hx⟩ := by
  sorry

/-- CS11: Brouwer for the closed unit ball, `a : E n`, `0 < R`, `ρ : E n → E n`,
`ContinuousOn ρ (closedBall a R)`, `MapsTo ρ (closedBall a R) (sphere a R)`,
`∀ x ∈ sphere a R, ρ x = x` ⇒ `False`. -/
theorem no_retraction_of_brouwer (n : ℕ)
    (hB : ∀ F : E n → E n, ContinuousOn F (closedBall 0 1) →
      MapsTo F (closedBall 0 1) (closedBall 0 1) →
      ∃ x ∈ closedBall (0 : E n) 1, F x = x)
    (a : E n) (R : ℝ) (hR : 0 < R) (ρ : E n → E n)
    (hρ : ContinuousOn ρ (closedBall a R))
    (hmaps : MapsTo ρ (closedBall a R) (sphere a R))
    (hfix : ∀ x ∈ sphere a R, ρ x = x) : False := by
  let T : E n → E n := fun u => a + R • u
  have hT : MapsTo T (closedBall 0 1) (closedBall a R) := by
    intro u hu
    have huNorm : ‖u‖ ≤ 1 := by simpa using hu
    rw [mem_closedBall, dist_eq_norm]
    change ‖a + R • u - a‖ ≤ R
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hR.le]
    nlinarith
  have hTcont : Continuous T := continuous_const.add (continuous_const.smul continuous_id)
  let F : E n → E n := fun u => -(R⁻¹ • (ρ (T u) - a))
  have hF : ContinuousOn F (closedBall 0 1) :=
    (continuousOn_const.smul
      ((hρ.comp hTcont.continuousOn hT).sub continuousOn_const)).neg
  have hFnorm : ∀ u ∈ closedBall (0 : E n) 1, ‖F u‖ = 1 := by
    intro u hu
    have hnorm : ‖ρ (T u) - a‖ = R := by
      simpa [mem_sphere, dist_eq_norm] using hmaps (hT hu)
    change ‖-(R⁻¹ • (ρ (T u) - a))‖ = 1
    rw [norm_neg, norm_smul, norm_inv, Real.norm_of_nonneg hR.le, hnorm,
      inv_mul_cancel₀ hR.ne']
  obtain ⟨u, hu, hFu⟩ := hB F hF (by
    intro u hu
    rw [mem_closedBall, dist_zero_right, hFnorm u hu])
  have huNorm : ‖u‖ = 1 := by simpa [hFu] using hFnorm u hu
  have hTu : T u ∈ sphere a R := by
    rw [mem_sphere, dist_eq_norm]
    change ‖a + R • u - a‖ = R
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hR.le, huNorm, mul_one]
  have hFneg : F u = -u := by
    change -(R⁻¹ • (ρ (T u) - a)) = -u
    rw [hfix (T u) hTu]
    dsimp [T]
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
  have huSum : u + u = 0 := by
    calc
      u + u = -u + u := congrArg (fun v => v + u) (hFu.symm.trans hFneg)
      _ = 0 := neg_add_cancel u
  have huZero : u = 0 := by
    have htwo : (2 : ℝ) • u = 0 := by simpa [two_smul] using huSum
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  simp [huZero] at huNorm

/-- CS12a: For `J := EuclideanGeometry.inversion b (1 : ℝ)`,
`ContinuousOn J {b}ᶜ`. -/
theorem continuousOn_inversion (n : ℕ) (b : E n) :
    ContinuousOn (EuclideanGeometry.inversion b (1 : ℝ)) ({b}ᶜ : Set (E n)) := by
  exact continuousOn_const.inversion continuousOn_const continuousOn_id fun _ hx => hx

/-- CS12b: `S ∩ ball b ε = ∅`, `0 < ε` ⇒ `J '' S ⊆ closedBall b ε⁻¹`,
for `J := EuclideanGeometry.inversion b (1 : ℝ)`. -/
theorem inversion_image_bounded (n : ℕ) (b : E n) (S : Set (E n)) (ε : ℝ)
    (hε : 0 < ε) (hS : S ∩ ball b ε = ∅) :
    EuclideanGeometry.inversion b (1 : ℝ) '' S ⊆ closedBall b ε⁻¹ := by
  rintro z ⟨x, hx, rfl⟩
  have hxε : ε ≤ dist x b := by
    by_contra h
    have hxball : x ∈ ball b ε := mem_ball.mpr (lt_of_not_ge h)
    have : x ∈ S ∩ ball b ε := ⟨hx, hxball⟩
    rw [hS] at this
    exact this
  rw [mem_closedBall, EuclideanGeometry.dist_inversion_center, one_pow, ← one_div]
  exact one_div_le_one_div_of_le hε hxε

/-- CS12c: `IsClosed S`, `b ∉ S` ⇒ `IsCompact (insert b (J '' S))`,
for `J := EuclideanGeometry.inversion b (1 : ℝ)`. -/
theorem isCompact_inversion_image_insert (n : ℕ) (b : E n) (S : Set (E n))
    (hS : IsClosed S) (hb : b ∉ S) :
    IsCompact (insert b (EuclideanGeometry.inversion b (1 : ℝ) '' S)) := by
  have hinv := EuclideanGeometry.inversion_involutive b (one_ne_zero : (1 : ℝ) ≠ 0)
  have hclosed : IsClosed (insert b (EuclideanGeometry.inversion b (1 : ℝ) '' S)) := by
    rw [← isOpen_compl_iff, hinv.image_eq_preimage_symm]
    convert (continuousOn_inversion n b).isOpen_inter_preimage
      isClosed_singleton.isOpen_compl hS.isOpen_compl using 1
    ext x
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, mem_preimage,
      mem_inter_iff]
    tauto
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hS.isOpen_compl b hb
  have hdisj : S ∩ ball b ε = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hball hx.2 hx.1
  apply (isCompact_closedBall b ε⁻¹).of_isClosed_subset hclosed
  intro x hx
  rcases hx with rfl | hx
  · exact mem_closedBall_self (inv_nonneg.mpr hε.le)
  · exact inversion_image_bounded n b S ε hε hdisj hx

/-- CS12d: `IsOpen A`, `b ∉ A` ⇒ `IsOpen (J '' A)`,
for `J := EuclideanGeometry.inversion b (1 : ℝ)`. -/
theorem isOpen_inversion_image (n : ℕ) (b : E n) (A : Set (E n))
    (hA : IsOpen A) (hb : b ∉ A) :
    IsOpen (EuclideanGeometry.inversion b (1 : ℝ) '' A) := by
  rw [(EuclideanGeometry.inversion_involutive b one_ne_zero).image_eq_preimage_symm]
  apply (continuousOn_inversion n b).isOpen_preimage isClosed_singleton.isOpen_compl
    (fun x hx => ?_) hA
  intro hxb
  have hxb' : x = b := hxb
  subst x
  exact hb (by simpa using hx)

/-- CS12e: For `b ∈ U`, `(J '' Uᶜ ∪ {b})ᶜ = J '' (U \ {b})`,
where `J := EuclideanGeometry.inversion b (1 : ℝ)`. -/
theorem inversion_image_compl (n : ℕ) (b : E n) (U : Set (E n)) (hb : b ∈ U) :
    (EuclideanGeometry.inversion b (1 : ℝ) '' Uᶜ ∪ {b})ᶜ =
      EuclideanGeometry.inversion b (1 : ℝ) '' (U \ {b}) := by
  simp only [(EuclideanGeometry.inversion_involutive b one_ne_zero).image_eq_preimage_symm]
  ext x
  by_cases hx : x = b
  · subst x
    simp [hb]
  · have hJx : EuclideanGeometry.inversion b (1 : ℝ) x ≠ b := by
      simpa using hx
    simp [hx, hJx]

/-- CS13 (restriction helper): Restrict a continuous map on a union to its left member. -/
def restrictUnionLeft {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    (Y D : Set X) (f : C(↥(Y ∪ D), Z)) : C(↥Y, Z) :=
  f.comp ⟨Set.inclusion subset_union_left, continuous_inclusion subset_union_left⟩

/-- CS13: `k + 2 ≤ n`, `Y₀ ⊆ E n` compact, `θ` a continuous injective closed
`k`-cell with `range θ ∩ Y₀` exactly its boundary image, and
`f : C(↥(Y₀ ∪ range θ), ↥(sphere (0 : E n) 1))` nullhomotopic on `Y₀` ⇒
`f.Nullhomotopic` (gluing). -/
theorem nullhomotopic_union_cell (k n : ℕ) (hkn : k + 2 ≤ n) (Y₀ : Set (E n))
    (hY₀ : IsCompact Y₀) (θ : C(↥(closedBall (0 : E k) 1), E n))
    (hθinj : Function.Injective θ)
    (hθ : range θ ∩ Y₀ = θ '' {y | ‖(y : E k)‖ = 1})
    (f : C(↥(Y₀ ∪ range θ), ↥(sphere (0 : E n) 1)))
    (hf : (restrictUnionLeft Y₀ (range θ) f).Nullhomotopic) : f.Nullhomotopic := by
  sorry

/-- CS14: Brouwer for the closed unit ball, `k + 2 ≤ n`, `U ⊆ E n` open connected,
`e` a continuous injective closed `k`-cell with its open ball in `U` and its boundary
sphere outside `U` ⇒ `IsPreconnected (U \ range e)` (Theorem T). -/
theorem isPreconnected_diff_cell (k n : ℕ)
    (hB : ∀ F : E n → E n, ContinuousOn F (closedBall 0 1) →
      MapsTo F (closedBall 0 1) (closedBall 0 1) →
      ∃ x ∈ closedBall (0 : E n) 1, F x = x)
    (hkn : k + 2 ≤ n) (U : Set (E n)) (hUo : IsOpen U) (hUc : IsConnected U)
    (e : C(↥(closedBall (0 : E k) 1), E n)) (he : Function.Injective e)
    (he₁ : ∀ x : ↥(closedBall (0 : E k) 1), ‖(x : E k)‖ < 1 → e x ∈ U)
    (he₂ : ∀ x : ↥(closedBall (0 : E k) 1), ‖(x : E k)‖ = 1 → e x ∉ U) :
    IsPreconnected (U \ range e) := by
  sorry

end CellSeparation

end

end Enforce
