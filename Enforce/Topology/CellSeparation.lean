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
  have h_closed : IsClosed (sphere (0 : E m) 1) := isClosed_sphere
  let g' : C(↥(sphere (0 : E m) 1), E n) :=
    ⟨fun x => (g x : E n), continuous_subtype_val.comp g.continuous⟩
  obtain ⟨F, hF_ext⟩ := ContinuousMap.exists_restrict_eq h_closed g'
  have hF_cont := F.continuous
  have hF_eq : ∀ x : sphere (0 : E m) 1, F x = g' x := by
    intro x
    have := congrArg (fun h => (h : C(sphere (0 : E m) 1, E n)) x) hF_ext
    exact this
  let h : E m → ℝ := fun x => max 0 (2 - ‖x‖)
  have h_cont : Continuous h := continuous_const.max (continuous_const.sub continuous_norm)
  let f : E m → E n := fun x => h x • F x
  have hf_cont : Continuous f := h_cont.smul hF_cont
  have hf_eq : ∀ x : sphere (0 : E m) 1, f x = g x := by
    intro x
    have h_hx : h x = 1 := by
      dsimp [h]
      have : ‖(x : E m)‖ = 1 := by
        have := x.2
        rwa [mem_sphere_zero_iff_norm] at this
      rw [this]
      norm_num
    change h (x : E m) • F (x : E m) = (g x : E n)
    rw [h_hx, one_smul, hF_eq x]
    rfl
  have hf_supp : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E m) 2)
    intro x hx
    contrapose hx
    simp only [Function.support, mem_setOf_eq, not_not] at hx ⊢
    have h_norm : 2 < ‖x‖ := by
      rw [mem_closedBall, dist_zero_right] at hx
      exact not_le.mp hx
    have : h x = 0 := by
      dsimp [h]
      rw [max_eq_left]
      linarith
    change h x • F x = 0
    rw [this, zero_smul]
  have hf_unif : UniformContinuous f := hf_supp.uniformContinuous_of_continuous hf_cont
  obtain ⟨G, hG_diff, hG_dist⟩ := UniformContinuous.exists_contDiff_dist_le hf_unif (by norm_num : (0 : ℝ) < 1)
  use G
  refine ⟨?_, ?_⟩
  · exact hG_diff.of_le (by simp)
  · intro y
    have h1 : dist (G y) (f y) < 1 := hG_dist y
    rw [hf_eq y] at h1
    have h2 : ‖(g y : E n) - G y‖ = dist (G y) (g y) := by
      rw [dist_eq_norm]
      exact norm_sub_rev (g y : E n) (G y)
    rwa [h2]

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

/-- The tail `(z 1, …, z k)` of a point `z` of `E (k + 1)`. -/
private def nullhomotopic_union_cell_tl (k : ℕ) (z : E (k + 1)) : E k :=
  WithLp.toLp 2 (fun i => z i.succ)

/-- The point `(s, x)` of `E (k + 1)`. -/
private def nullhomotopic_union_cell_pt (k : ℕ) (x : E k) (s : ℝ) : E (k + 1) :=
  WithLp.toLp 2 (Fin.cons s (fun i => x i))

private lemma nullhomotopic_union_cell_norm_sq (k : ℕ) (z : E (k + 1)) :
    ‖z‖ ^ 2 = z 0 ^ 2 + ‖nullhomotopic_union_cell_tl k z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp [nullhomotopic_union_cell_tl, Real.norm_eq_abs, sq_abs]

private lemma nullhomotopic_union_cell_pt_zero (k : ℕ) (x : E k) (s : ℝ) :
    nullhomotopic_union_cell_pt k x s 0 = s := by
  simp [nullhomotopic_union_cell_pt]

private lemma nullhomotopic_union_cell_tl_pt (k : ℕ) (x : E k) (s : ℝ) :
    nullhomotopic_union_cell_tl k (nullhomotopic_union_cell_pt k x s) = x := by
  ext i
  simp [nullhomotopic_union_cell_tl, nullhomotopic_union_cell_pt]

private lemma nullhomotopic_union_cell_norm_pt_sq (k : ℕ) (x : E k) (s : ℝ) :
    ‖nullhomotopic_union_cell_pt k x s‖ ^ 2 = s ^ 2 + ‖x‖ ^ 2 := by
  rw [nullhomotopic_union_cell_norm_sq, nullhomotopic_union_cell_pt_zero,
    nullhomotopic_union_cell_tl_pt]

private lemma nullhomotopic_union_cell_continuous_tl (k : ℕ) :
    Continuous (nullhomotopic_union_cell_tl k) := by
  unfold nullhomotopic_union_cell_tl
  fun_prop

private lemma nullhomotopic_union_cell_continuous_pt (k : ℕ) {X : Type*} [TopologicalSpace X]
    {x : X → E k} {s : X → ℝ} (hx : Continuous x) (hs : Continuous s) :
    Continuous fun a => nullhomotopic_union_cell_pt k (x a) (s a) := by
  unfold nullhomotopic_union_cell_pt
  exact (PiLp.continuous_toLp _ _).comp
    (hs.finCons (continuous_pi fun i => (PiLp.continuous_apply _ _ i).comp hx))

private lemma nullhomotopic_union_cell_phi_sq_le (a r : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (√(1 - a ^ 2 * r ^ 2) - 2 * a * √(1 - r ^ 2)) ^ 2 + (a * r) ^ 2 ≤ 1 := by
  have hv : 0 ≤ 1 - r ^ 2 := by nlinarith
  have hw : 0 ≤ 1 - a ^ 2 * r ^ 2 := by nlinarith
  have hsv := Real.sq_sqrt hv
  have hsw := Real.sq_sqrt hw
  have hsv0 := Real.sqrt_nonneg (1 - r ^ 2)
  have hle : a * √(1 - r ^ 2) ≤ √(1 - a ^ 2 * r ^ 2) := by
    rw [Real.le_sqrt (by positivity) hw, mul_pow, hsv]
    nlinarith
  nlinarith [mul_nonneg (mul_nonneg ha0 hsv0) (sub_nonneg.mpr hle)]

private lemma nullhomotopic_union_cell_mem_sphere {m : ℕ} (z : E m) (h : ‖z‖ ^ 2 = 1) :
    z ∈ sphere (0 : E m) 1 := by
  rw [mem_sphere_zero_iff_norm]
  nlinarith [norm_nonneg z]

/-- Step 1 of the V4 proof of `nullhomotopic_union_cell` (V4 CS13, blueprint CS13): "a
nullhomotopy `H₀` on `Y₀` and `f` on the cell prescribe a map on the boundary of the cylinder
`closedBall (0 : E k) 1 ×ˢ Icc 0 1` (bottom: `f ∘ θ`; side: `H₀ ∘ θ`; top: constant), i.e. a map
`S^k → S^{n-1}`; since `k + 1 < n` it is nullhomotopic (CS8) and so extends over the cylinder
(CS9)". Here the bottom is `g₀`, the side is `Hs`, the top is `c`. -/
private lemma nullhomotopic_union_cell_step1_cylinder (k n : ℕ) (hkn : k + 2 ≤ n)
    (g₀ : C(↥(closedBall (0 : E k) 1), ↥(sphere (0 : E n) 1))) (c : ↥(sphere (0 : E n) 1))
    (Hs : C(unitInterval × ↥(sphere (0 : E k) 1), ↥(sphere (0 : E n) 1)))
    (hs0 : ∀ u : ↥(sphere (0 : E k) 1), Hs (0, u) = g₀ ⟨u, sphere_subset_closedBall u.2⟩)
    (hs1 : ∀ u : ↥(sphere (0 : E k) 1), Hs (1, u) = c) :
    ∃ G : C(unitInterval × ↥(closedBall (0 : E k) 1), ↥(sphere (0 : E n) 1)),
      (∀ y, G (0, y) = g₀ y) ∧ (∀ y, G (1, y) = c) ∧
      ∀ (t : unitInterval) (u : ↥(sphere (0 : E k) 1)),
        G (t, ⟨u, sphere_subset_closedBall u.2⟩) = Hs (t, u) := by
  classical
  let g : C(↥(sphere (0 : E k) 1), ↥(sphere (0 : E n) 1)) :=
    g₀.comp ⟨fun u => ⟨u, sphere_subset_closedBall u.2⟩, by fun_prop⟩
  let H : g.Homotopy (ContinuousMap.const _ c) :=
    { toContinuousMap := Hs
      map_zero_left := hs0
      map_one_left := hs1 }
  -- the cone `F₁` over the side and the top of the cylinder (CS9 construction)
  obtain ⟨F₁, hF₁0, hF₁⟩ :=
    extend_sphere_to_closedBall_of_nullhomotopic_step3_continuous k g c H
  have hF₁s : ∀ p : ↥(closedBall (0 : E k) 1), ‖(p : E k)‖ = 1 → F₁ p = g₀ p := by
    intro p hp
    have hp0 : (p : E k) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hp
      norm_num at hp
    rw [hF₁ p hp0]
    change Hs _ = _
    rw [show g₀ p = Hs (0, ⟨p, mem_sphere_zero_iff_norm.mpr hp⟩) from
      (hs0 ⟨p, mem_sphere_zero_iff_norm.mpr hp⟩).symm]
    congr 1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show 1 - ‖(p : E k)‖ = 0
      rw [hp]
      norm_num
    · show ‖(p : E k)‖⁻¹ • (p : E k) = (p : E k)
      rw [hp, inv_one, one_smul]
  have hF₁side : ∀ (t : unitInterval) (u : ↥(sphere (0 : E k) 1)) (_ : (t : ℝ) < 1)
      (hm : (1 - (t : ℝ)) • (u : E k) ∈ closedBall (0 : E k) 1),
      F₁ ⟨(1 - (t : ℝ)) • (u : E k), hm⟩ = Hs (t, u) := by
    intro t u ht hm
    have hu : ‖(u : E k)‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
    have ht1 : (0 : ℝ) < 1 - t := sub_pos.mpr ht
    have hnorm : ‖(1 - (t : ℝ)) • (u : E k)‖ = 1 - t := by
      rw [norm_smul, hu, mul_one, Real.norm_of_nonneg ht1.le]
    have hp0 : (1 - (t : ℝ)) • (u : E k) ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnorm
      linarith
    rw [hF₁ ⟨(1 - (t : ℝ)) • (u : E k), hm⟩ hp0]
    change Hs _ = _
    congr 1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show 1 - ‖(1 - (t : ℝ)) • (u : E k)‖ = t
      rw [hnorm]
      ring
    · show ‖(1 - (t : ℝ)) • (u : E k)‖⁻¹ • ((1 - (t : ℝ)) • (u : E k)) = u
      rw [hnorm, smul_smul, inv_mul_cancel₀ ht1.ne', one_smul]
  -- the map `m : S^k → S^{n-1}`: `g₀` on the lower hemisphere, `F₁` on the upper one
  have htl : ∀ z : ↥(sphere (0 : E (k + 1)) 1),
      nullhomotopic_union_cell_tl k z ∈ closedBall (0 : E k) 1 := by
    intro z
    have h1 := nullhomotopic_union_cell_norm_sq k z
    have hz : ‖(z : E (k + 1))‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
    rw [hz] at h1
    rw [mem_closedBall_zero_iff]
    nlinarith [norm_nonneg (nullhomotopic_union_cell_tl k z), sq_nonneg ((z : E (k + 1)) 0)]
  let P : C(↥(sphere (0 : E (k + 1)) 1), ↥(closedBall (0 : E k) 1)) :=
    ⟨fun z => ⟨nullhomotopic_union_cell_tl k z, htl z⟩,
      ((nullhomotopic_union_cell_continuous_tl k).comp continuous_subtype_val).subtype_mk _⟩
  have hagree : ∀ z : ↥(sphere (0 : E (k + 1)) 1), (0 : ℝ) = (z : E (k + 1)) 0 →
      F₁ (P z) = g₀ (P z) := by
    intro z hz
    apply hF₁s
    have h1 := nullhomotopic_union_cell_norm_sq k z
    have hz1 : ‖(z : E (k + 1))‖ = 1 := mem_sphere_zero_iff_norm.mp z.2
    rw [hz1, ← hz] at h1
    show ‖nullhomotopic_union_cell_tl k z‖ = 1
    nlinarith [norm_nonneg (nullhomotopic_union_cell_tl k z)]
  let m : C(↥(sphere (0 : E (k + 1)) 1), ↥(sphere (0 : E n) 1)) :=
    ⟨fun z => if (0 : ℝ) ≤ (z : E (k + 1)) 0 then F₁ (P z) else g₀ (P z),
      Continuous.if_le (F₁.continuous.comp P.continuous) (g₀.continuous.comp P.continuous)
        continuous_const ((PiLp.continuous_apply _ _ 0).comp continuous_subtype_val) hagree⟩
  have hm_up : ∀ z : ↥(sphere (0 : E (k + 1)) 1), 0 ≤ (z : E (k + 1)) 0 →
      m z = F₁ (P z) := by
    intro z hz
    show (if (0 : ℝ) ≤ (z : E (k + 1)) 0 then F₁ (P z) else g₀ (P z)) = F₁ (P z)
    rw [if_pos hz]
  have hm_low : ∀ z : ↥(sphere (0 : E (k + 1)) 1), (z : E (k + 1)) 0 ≤ 0 →
      m z = g₀ (P z) := by
    intro z hz
    show (if (0 : ℝ) ≤ (z : E (k + 1)) 0 then F₁ (P z) else g₀ (P z)) = g₀ (P z)
    split_ifs with h
    · exact hagree z (le_antisymm h hz)
    · rfl
  -- `k + 1 < n`: `m` is nullhomotopic (CS8), hence extends over the ball (CS9)
  obtain ⟨M, hM⟩ := extend_sphere_to_closedBall_of_nullhomotopic (k + 1) (by omega) m
    (nullhomotopic_sphere_to_sphere (k + 1) n (by omega) (by omega) m)
  -- the cylinder mapped onto the ball of `E (k + 1)`, boundary to the sphere
  let σ : unitInterval × ↥(closedBall (0 : E k) 1) → ℝ := fun p =>
    √(1 - (1 - (p.1 : ℝ)) ^ 2 * ‖(p.2 : E k)‖ ^ 2) -
      2 * (1 - (p.1 : ℝ)) * √(1 - ‖(p.2 : E k)‖ ^ 2)
  have hσ : Continuous σ := by fun_prop
  have hΦ : ∀ p : unitInterval × ↥(closedBall (0 : E k) 1),
      nullhomotopic_union_cell_pt k ((1 - (p.1 : ℝ)) • (p.2 : E k)) (σ p) ∈
        closedBall (0 : E (k + 1)) 1 := by
    intro p
    have ht0 : 0 ≤ (p.1 : ℝ) := p.1.2.1
    have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
    have hr1 : ‖(p.2 : E k)‖ ≤ 1 := mem_closedBall_zero_iff.mp p.2.2
    have h := nullhomotopic_union_cell_phi_sq_le (1 - (p.1 : ℝ)) ‖(p.2 : E k)‖
      (by linarith) (by linarith) (norm_nonneg _) hr1
    have hn := nullhomotopic_union_cell_norm_pt_sq k ((1 - (p.1 : ℝ)) • (p.2 : E k)) (σ p)
    rw [norm_smul, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - p.1)] at hn
    have h2 : ‖nullhomotopic_union_cell_pt k ((1 - (p.1 : ℝ)) • (p.2 : E k)) (σ p)‖ ^ 2 ≤ 1 := by
      rw [hn]
      exact h
    rw [mem_closedBall_zero_iff]
    nlinarith [norm_nonneg (nullhomotopic_union_cell_pt k ((1 - (p.1 : ℝ)) • (p.2 : E k)) (σ p))]
  let Φ : C(unitInterval × ↥(closedBall (0 : E k) 1), ↥(closedBall (0 : E (k + 1)) 1)) :=
    ⟨fun p => ⟨nullhomotopic_union_cell_pt k ((1 - (p.1 : ℝ)) • (p.2 : E k)) (σ p), hΦ p⟩,
      (nullhomotopic_union_cell_continuous_pt k (by fun_prop) hσ).subtype_mk _⟩
  have hMΦ : ∀ p (hp : nullhomotopic_union_cell_pt k ((1 - (p.1 : ℝ)) • (p.2 : E k)) (σ p) ∈
      sphere (0 : E (k + 1)) 1), M (Φ p) = m ⟨_, hp⟩ := fun p hp => hM _ hp
  refine ⟨M.comp Φ, ?_, ?_, ?_⟩
  · -- bottom: the lower hemisphere, where `m = g₀`
    intro y
    have hr1 : ‖(y : E k)‖ ≤ 1 := mem_closedBall_zero_iff.mp y.2
    have hσ0 : σ (0, y) = -√(1 - ‖(y : E k)‖ ^ 2) := by
      simp only [σ, Set.Icc.coe_zero, sub_zero, one_pow, one_mul]
      ring
    have hpt : nullhomotopic_union_cell_pt k ((1 - ((0 : unitInterval) : ℝ)) • (y : E k))
        (σ (0, y)) = nullhomotopic_union_cell_pt k (y : E k) (-√(1 - ‖(y : E k)‖ ^ 2)) := by
      rw [hσ0]
      simp
    have hz : nullhomotopic_union_cell_pt k ((1 - ((0 : unitInterval) : ℝ)) • (y : E k))
        (σ (0, y)) ∈ sphere (0 : E (k + 1)) 1 := by
      apply nullhomotopic_union_cell_mem_sphere
      rw [hpt, nullhomotopic_union_cell_norm_pt_sq, neg_sq,
        Real.sq_sqrt (by nlinarith [norm_nonneg (y : E k)])]
      ring
    have hz0 : nullhomotopic_union_cell_pt k ((1 - ((0 : unitInterval) : ℝ)) • (y : E k))
        (σ (0, y)) 0 ≤ 0 := by
      rw [hpt, nullhomotopic_union_cell_pt_zero]
      exact neg_nonpos.mpr (Real.sqrt_nonneg _)
    show M (Φ (0, y)) = g₀ y
    rw [hMΦ (0, y) hz, hm_low ⟨_, hz⟩ hz0]
    congr 1
    apply Subtype.ext
    show nullhomotopic_union_cell_tl k (nullhomotopic_union_cell_pt k
      ((1 - ((0 : unitInterval) : ℝ)) • (y : E k)) (σ (0, y))) = (y : E k)
    rw [hpt, nullhomotopic_union_cell_tl_pt]
  · -- top: the north pole, where `m = F₁ 0 = c`
    intro y
    have hσ1 : σ (1, y) = 1 := by
      simp [σ]
    have hpt : nullhomotopic_union_cell_pt k ((1 - ((1 : unitInterval) : ℝ)) • (y : E k))
        (σ (1, y)) = nullhomotopic_union_cell_pt k 0 1 := by
      rw [hσ1]
      simp
    have hz : nullhomotopic_union_cell_pt k ((1 - ((1 : unitInterval) : ℝ)) • (y : E k))
        (σ (1, y)) ∈ sphere (0 : E (k + 1)) 1 := by
      apply nullhomotopic_union_cell_mem_sphere
      rw [hpt, nullhomotopic_union_cell_norm_pt_sq]
      simp
    have hz0 : 0 ≤ nullhomotopic_union_cell_pt k ((1 - ((1 : unitInterval) : ℝ)) • (y : E k))
        (σ (1, y)) 0 := by
      rw [hpt, nullhomotopic_union_cell_pt_zero]
      norm_num
    show M (Φ (1, y)) = c
    rw [hMΦ (1, y) hz, hm_up ⟨_, hz⟩ hz0, ← hF₁0]
    congr 1
    apply Subtype.ext
    show nullhomotopic_union_cell_tl k (nullhomotopic_union_cell_pt k
      ((1 - ((1 : unitInterval) : ℝ)) • (y : E k)) (σ (1, y))) = (0 : E k)
    rw [hpt, nullhomotopic_union_cell_tl_pt]
  · -- side: the upper hemisphere, where `m = F₁` is the cone of `Hs`
    intro t u
    have hu : ‖(u : E k)‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    set y : ↥(closedBall (0 : E k) 1) := ⟨u, sphere_subset_closedBall u.2⟩ with hy
    have hσt : σ (t, y) = √(1 - (1 - (t : ℝ)) ^ 2) := by
      simp [σ, hy, hu]
    have hpt : nullhomotopic_union_cell_pt k ((1 - (t : ℝ)) • (y : E k)) (σ (t, y)) =
        nullhomotopic_union_cell_pt k ((1 - (t : ℝ)) • (u : E k)) (√(1 - (1 - (t : ℝ)) ^ 2)) := by
      rw [hσt]
    have hz : nullhomotopic_union_cell_pt k ((1 - ((t, y).1 : ℝ)) • ((t, y).2 : E k))
        (σ (t, y)) ∈ sphere (0 : E (k + 1)) 1 := by
      apply nullhomotopic_union_cell_mem_sphere
      show ‖nullhomotopic_union_cell_pt k ((1 - (t : ℝ)) • (y : E k)) (σ (t, y))‖ ^ 2 = 1
      rw [hpt, nullhomotopic_union_cell_norm_pt_sq, Real.sq_sqrt (by nlinarith), norm_smul, hu,
        Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t)]
      ring
    have hz0 : 0 ≤ nullhomotopic_union_cell_pt k ((1 - ((t, y).1 : ℝ)) • ((t, y).2 : E k))
        (σ (t, y)) 0 := by
      show 0 ≤ nullhomotopic_union_cell_pt k ((1 - (t : ℝ)) • (y : E k)) (σ (t, y)) 0
      rw [hpt, nullhomotopic_union_cell_pt_zero]
      exact Real.sqrt_nonneg _
    show M (Φ (t, y)) = Hs (t, u)
    rw [hMΦ (t, y) hz, hm_up ⟨_, hz⟩ hz0]
    have hP : ((P ⟨_, hz⟩ : ↥(closedBall (0 : E k) 1)) : E k) = (1 - (t : ℝ)) • (u : E k) := by
      show nullhomotopic_union_cell_tl k
        (nullhomotopic_union_cell_pt k ((1 - (t : ℝ)) • (y : E k)) (σ (t, y))) = _
      rw [hpt, nullhomotopic_union_cell_tl_pt]
    have hmem : (1 - (t : ℝ)) • (u : E k) ∈ closedBall (0 : E k) 1 := by
      rw [← hP]
      exact (P ⟨_, hz⟩).2
    rw [show P ⟨_, hz⟩ = ⟨_, hmem⟩ from Subtype.ext hP]
    rcases lt_or_eq_of_le ht1 with ht | ht
    · exact hF₁side t u ht hmem
    · have ht' : t = 1 := Subtype.ext ht
      rw [show (⟨(1 - (t : ℝ)) • (u : E k), hmem⟩ : ↥(closedBall (0 : E k) 1)) =
        ⟨0, by simp⟩ from Subtype.ext (by
          show (1 - (t : ℝ)) • (u : E k) = 0
          rw [ht]
          simp), hF₁0, ht', hs1]

/-- Step 2 of the V4 proof of `nullhomotopic_union_cell` (V4 CS13, blueprint CS13): "Define `H`
on `(Y₀ ∪ range θ) × I`: `H₀` on `Y₀ × I`, `M̂ ∘ (θ⁻¹ × id)` on `range θ × I` (`θ` is a closed
embedding: compact to Hausdorff); overlaps agree by `hθ`; pasting on two closed sets.
`H (·, 0) = f`, `H (·, 1) = c₀`". Here `G` is the extension `M̂` over the cylinder. -/
private lemma nullhomotopic_union_cell_step2_glue (k n : ℕ) (Y₀ : Set (E n))
    (hY₀ : IsCompact Y₀) (θ : C(↥(closedBall (0 : E k) 1), E n))
    (hθinj : Function.Injective θ)
    (f : C(↥(Y₀ ∪ range θ), ↥(sphere (0 : E n) 1))) (c : ↥(sphere (0 : E n) 1))
    (H₀ : (restrictUnionLeft Y₀ (range θ) f).Homotopy (ContinuousMap.const _ c))
    (G : C(unitInterval × ↥(closedBall (0 : E k) 1), ↥(sphere (0 : E n) 1)))
    (hG0 : ∀ y, G (0, y) = f ⟨θ y, Or.inr (mem_range_self y)⟩)
    (hG1 : ∀ y, G (1, y) = c)
    (hGs : ∀ t y (hy : θ y ∈ Y₀), G (t, y) = H₀ (t, ⟨θ y, hy⟩)) : f.Nullhomotopic := by
  classical
  haveI : CompactSpace ↥(closedBall (0 : E k) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  -- `θ` is a homeomorphism onto its range
  have hecont : Continuous (Equiv.ofInjective θ hθinj) := θ.continuous.subtype_mk _
  let e : ↥(closedBall (0 : E k) 1) ≃ₜ ↥(range θ) := hecont.homeoOfEquivCompactToT2
  have he : ∀ z : ↥(range θ), θ (e.symm z) = z := fun z =>
    congrArg Subtype.val (e.apply_symm_apply z)
  have hD : ∀ z : ↥(Y₀ ∪ range θ), (z : E n) ∉ Y₀ → (z : E n) ∈ range θ :=
    fun z h => z.2.resolve_left h
  let Hf : unitInterval × ↥(Y₀ ∪ range θ) → ↥(sphere (0 : E n) 1) := fun p =>
    if h : (p.2 : E n) ∈ Y₀ then H₀ (p.1, ⟨p.2, h⟩) else G (p.1, e.symm ⟨p.2, hD p.2 h⟩)
  have hHfD : ∀ p : unitInterval × ↥(Y₀ ∪ range θ), ∀ hr : (p.2 : E n) ∈ range θ,
      Hf p = G (p.1, e.symm ⟨p.2, hr⟩) := by
    intro p hr
    by_cases h : (p.2 : E n) ∈ Y₀
    · simp only [Hf, dif_pos h]
      have hθy : θ (e.symm ⟨p.2, hr⟩) ∈ Y₀ := by rw [he]; exact h
      rw [hGs p.1 _ hθy]
      congr 2
      exact Subtype.ext (he ⟨(p.2 : E n), hr⟩).symm
    · simp only [Hf, dif_neg h]
  have hA : IsClosed {p : unitInterval × ↥(Y₀ ∪ range θ) | (p.2 : E n) ∈ Y₀} :=
    hY₀.isClosed.preimage (continuous_subtype_val.comp continuous_snd)
  have hB : IsClosed {p : unitInterval × ↥(Y₀ ∪ range θ) | (p.2 : E n) ∈ range θ} :=
    (isCompact_range θ.continuous).isClosed.preimage (continuous_subtype_val.comp continuous_snd)
  have hcont : Continuous Hf := by
    rw [← continuousOn_univ]
    have hU : (univ : Set (unitInterval × ↥(Y₀ ∪ range θ))) =
        {p | (p.2 : E n) ∈ Y₀} ∪ {p | (p.2 : E n) ∈ range θ} := by
      ext p
      simp only [mem_univ, mem_union, mem_setOf_eq, true_iff]
      exact p.2.2
    rw [hU]
    refine ContinuousOn.union_of_isClosed ?_ ?_ hA hB
    · rw [continuousOn_iff_continuous_restrict]
      have hr : restrict {p : unitInterval × ↥(Y₀ ∪ range θ) | (p.2 : E n) ∈ Y₀} Hf =
          fun p => H₀ (p.1.1, ⟨p.1.2, p.2⟩) := by
        funext p
        simp only [restrict_apply, Hf]
        exact dif_pos p.2
      rw [hr]
      exact H₀.continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _))
    · rw [continuousOn_iff_continuous_restrict]
      have hr : restrict {p : unitInterval × ↥(Y₀ ∪ range θ) | (p.2 : E n) ∈ range θ} Hf =
          fun p => G (p.1.1, e.symm ⟨p.1.2, p.2⟩) := by
        funext p
        exact hHfD p.1 p.2
      rw [hr]
      exact G.continuous.comp ((continuous_fst.comp continuous_subtype_val).prodMk
        (e.symm.continuous.comp
          ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)))
  refine ⟨c, ⟨{ toFun := Hf
                continuous_toFun := hcont
                map_zero_left := ?_
                map_one_left := ?_ }⟩⟩
  · intro z
    by_cases h : (z : E n) ∈ Y₀
    · simp only [Hf, dif_pos h]
      exact H₀.apply_zero _
    · simp only [Hf, dif_neg h]
      rw [hG0]
      congr 1
      exact Subtype.ext (he _)
  · intro z
    by_cases h : (z : E n) ∈ Y₀
    · simp only [Hf, dif_pos h]
      exact H₀.apply_one _
    · simp only [Hf, dif_neg h]
      exact hG1 _

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
  obtain ⟨c, ⟨H₀⟩⟩ := hf
  -- a point of the cell lies in `Y₀` iff it is on the boundary sphere
  have hmem : ∀ y : ↥(closedBall (0 : E k) 1), θ y ∈ Y₀ ↔ ‖(y : E k)‖ = 1 := by
    intro y
    constructor
    · intro hy
      have h : θ y ∈ θ '' {y | ‖(y : E k)‖ = 1} := hθ ▸ ⟨mem_range_self y, hy⟩
      obtain ⟨y', hy', hyy'⟩ := h
      rw [← hθinj hyy']
      exact hy'
    · intro hy
      have h : θ y ∈ range θ ∩ Y₀ := hθ ▸ mem_image_of_mem θ hy
      exact h.2
  let g₀ : C(↥(closedBall (0 : E k) 1), ↥(sphere (0 : E n) 1)) :=
    f.comp ⟨fun y => ⟨θ y, Or.inr (mem_range_self y)⟩, by fun_prop⟩
  let ι : C(unitInterval × ↥(sphere (0 : E k) 1), unitInterval × ↥(Y₀)) :=
    ⟨fun p => (p.1, ⟨θ ⟨p.2, sphere_subset_closedBall p.2.2⟩,
      (hmem _).2 (mem_sphere_zero_iff_norm.mp p.2.2)⟩), by fun_prop⟩
  let Hs : C(unitInterval × ↥(sphere (0 : E k) 1), ↥(sphere (0 : E n) 1)) :=
    H₀.toContinuousMap.comp ι
  have hs0 : ∀ u : ↥(sphere (0 : E k) 1), Hs (0, u) = g₀ ⟨u, sphere_subset_closedBall u.2⟩ := by
    intro u
    exact H₀.apply_zero _
  have hs1 : ∀ u : ↥(sphere (0 : E k) 1), Hs (1, u) = c := by
    intro u
    exact H₀.apply_one _
  obtain ⟨G, hG0, hG1, hGs⟩ :=
    nullhomotopic_union_cell_step1_cylinder k n hkn g₀ c Hs hs0 hs1
  refine nullhomotopic_union_cell_step2_glue k n Y₀ hY₀ θ hθinj f c H₀ G hG0 hG1 ?_
  intro t y hy
  have hy1 : (y : E k) ∈ sphere (0 : E k) 1 := by simpa using (hmem y).1 hy
  exact hGs t ⟨y, hy1⟩

/-- Step 1 of the V4 proof of `isPreconnected_diff_cell` (V4 CS14, step 1 / CS14b): `U` is
path connected; a path from `a` to `b` in `U`, cut just before it first reaches `b`, joins `a`
inside `U \ {b}` to points arbitrarily close to `b`. -/
private lemma isPreconnected_diff_cell_step1_path_escape (n : ℕ) (U : Set (E n))
    (hUo : IsOpen U) (hUc : IsConnected U) (a b : E n) (ha : a ∈ U) (hb : b ∈ U)
    (hab : a ≠ b) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c, JoinedIn (U \ {b}) a c ∧ dist c b < δ := by
  obtain ⟨γ, hγ⟩ := ((hUo.isConnected_iff_isPathConnected).mp hUc).joinedIn a ha b hb
  let f : ℝ → E n := γ.extend
  have hf : Continuous f := γ.continuous_extend
  let T : Set ℝ := Icc 0 1 ∩ f ⁻¹' {b}
  have hTc : IsClosed T := isClosed_Icc.inter (isClosed_singleton.preimage hf)
  have hTne : T.Nonempty := ⟨1, ⟨by norm_num, by norm_num⟩, by simp [f]⟩
  have hTbdd : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  have ht₀T : sInf T ∈ T := hTc.csInf_mem hTne hTbdd
  have hlt : ∀ t, 0 ≤ t → t < sInf T → f t ≠ b := by
    intro t ht0 htt hfb
    have : sInf T ≤ t := csInf_le hTbdd ⟨⟨ht0, by linarith [ht₀T.1.2]⟩, hfb⟩
    linarith
  have hfb : f (sInf T) = b := ht₀T.2
  have ht₀pos : 0 < sInf T := by
    rcases ht₀T.1.1.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hfb
      simp [f] at hfb
      exact hab hfb
  have htend : Filter.Tendsto f (nhdsWithin (sInf T) (Iio (sInf T))) (nhds b) := by
    rw [← hfb]; exact hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in nhdsWithin (sInf T) (Iio (sInf T)),
      f t ∈ ball b δ ∧ t ∈ Ioo 0 (sInf T) :=
    (htend.eventually (ball_mem_nhds b hδ)).and (Ioo_mem_nhdsLT ht₀pos)
  obtain ⟨t₁, hft₁, ht₁⟩ := hev.exists
  refine ⟨f t₁, ?_, hft₁⟩
  refine ⟨⟨⟨fun s => f ((s : ℝ) * t₁),
    hf.comp (continuous_subtype_val.mul continuous_const)⟩, ?_, ?_⟩, ?_⟩
  · simp [f]
  · simp [f]
  · intro s
    have hs0 : 0 ≤ (s : ℝ) * t₁ := mul_nonneg s.2.1 ht₁.1.le
    have hs1 : (s : ℝ) * t₁ ≤ t₁ := by
      have := s.2.2
      nlinarith [ht₁.1]
    have hsI : (s : ℝ) * t₁ ∈ Icc (0 : ℝ) 1 := ⟨hs0, by linarith [ht₁.2, ht₀T.1.2]⟩
    refine ⟨?_, ?_⟩
    · change f ((s : ℝ) * t₁) ∈ U
      simp only [f]
      rw [γ.extend_apply hsI]
      exact hγ _
    · exact hlt _ hs0 (by linarith [ht₁.2])

/-- Step 2 of the V4 proof of `isPreconnected_diff_cell` (V4 CS14, step 1): with
`J := inversion b 1` and `Y₀ := J '' Uᶜ ∪ {b}`, the radial map from `J a` on `Y₀` is
nullhomotopic (CS5): the path of step 1 is carried by `J` into `Y₀ᶜ` from `J a` to a point of
arbitrarily large norm. -/
private lemma isPreconnected_diff_cell_step2_Y0_nullhomotopic (n : ℕ) (hn : 1 ≤ n)
    (U : Set (E n)) (hUo : IsOpen U) (hUc : IsConnected U) (a b : E n) (ha : a ∈ U)
    (hb : b ∈ U) (hab : a ≠ b)
    (ha' : EuclideanGeometry.inversion b (1 : ℝ) a ∉
      insert b (EuclideanGeometry.inversion b (1 : ℝ) '' Uᶜ)) :
    (radialMap n (EuclideanGeometry.inversion b (1 : ℝ) a)
      (insert b (EuclideanGeometry.inversion b (1 : ℝ) '' Uᶜ)) ha').Nullhomotopic := by
  set J := EuclideanGeometry.inversion b (1 : ℝ) with hJ
  have hY₀ : IsCompact (insert b (J '' Uᶜ)) :=
    isCompact_inversion_image_insert n b Uᶜ hUo.isClosed_compl (fun h => h hb)
  obtain ⟨M, hM⟩ := hY₀.isBounded.subset_closedBall (0 : E n)
  set K : ℝ := max M 0 + ‖b‖ + 1 with hK
  have hM0 : M ≤ max M 0 := le_max_left _ _
  have hM0' : 0 ≤ max M 0 := le_max_right _ _
  have hKpos : 0 < K := by have := norm_nonneg b; linarith
  obtain ⟨c, hjoin, hcb⟩ :=
    isPreconnected_diff_cell_step1_path_escape n U hUo hUc a b ha hb hab (1 / K)
      (one_div_pos.mpr hKpos)
  have hcU : c ∈ U \ {b} := hjoin.target_mem
  have hcb0 : 0 < dist c b := dist_pos.mpr hcU.2
  refine radialMap_nullhomotopic_of_escape n hn _ M hM _ ha' ⟨J c, ?_, ?_⟩
  · have h1 : JoinedIn (J '' (U \ {b})) (J a) (J c) :=
      hjoin.map_continuousOn ((continuousOn_inversion n b).mono fun x hx => hx.2)
    have hcompl : J '' (U \ {b}) = (insert b (J '' Uᶜ))ᶜ := by
      rw [← inversion_image_compl n b U hb, union_singleton]
    exact h1.mono hcompl.subset
  · have hdist : dist (J c) b = 1 / dist c b := by
      rw [hJ, EuclideanGeometry.dist_inversion_center]; norm_num
    have hbig : K < 1 / dist c b := by
      rw [lt_div_iff₀ hcb0]
      have := (lt_div_iff₀ hKpos).mp hcb
      linarith
    have htri : dist (J c) b ≤ ‖J c‖ + ‖b‖ := by
      calc dist (J c) b ≤ dist (J c) 0 + dist 0 b := dist_triangle _ _ _
        _ = ‖J c‖ + ‖b‖ := by rw [dist_zero_right, dist_comm, dist_zero_right]
    linarith

/-- Step 3 of the V4 proof of `isPreconnected_diff_cell` (V4 CS14, step 3 / CS14c): for a
separation `U \ D ⊆ A ∪ B` by disjoint open sets with `b ∈ B` and `J := inversion b 1`,
`E n = J '' A ⊔ J '' (B \ {b}) ⊔ (J '' Uᶜ ∪ {b} ∪ J '' D)`, hence
`frontier (J '' A) ⊆ J '' Uᶜ ∪ {b} ∪ J '' D`. -/
private lemma isPreconnected_diff_cell_step3_frontier_subset (n : ℕ) (U D A B : Set (E n))
    (b : E n) (hA : IsOpen A) (hB : IsOpen B) (hAB : Disjoint A B) (hcov : U \ D ⊆ A ∪ B)
    (hbB : b ∈ B) :
    frontier (EuclideanGeometry.inversion b (1 : ℝ) '' A) ⊆
      insert b (EuclideanGeometry.inversion b (1 : ℝ) '' Uᶜ) ∪
        EuclideanGeometry.inversion b (1 : ℝ) '' D := by
  set J := EuclideanGeometry.inversion b (1 : ℝ) with hJ
  have hJinv : Function.Involutive J := EuclideanGeometry.inversion_involutive b one_ne_zero
  have hJb : J b = b := EuclideanGeometry.inversion_self b 1
  have hbA : b ∉ A := fun h => hAB.notMem_of_mem_right hbB h
  have hOA : IsOpen (J '' A) := isOpen_inversion_image n b A hA hbA
  have hOB : IsOpen (J '' (B \ {b})) :=
    isOpen_inversion_image n b (B \ {b}) (hB.sdiff isClosed_singleton) (fun h => h.2 rfl)
  intro z hz
  rw [hOA.frontier_eq] at hz
  obtain ⟨hzc, hzA⟩ := hz
  by_contra hzY
  have hzb : z ≠ b := fun h => hzY (Or.inl (Or.inl h))
  have hwz : J (J z) = z := hJinv z
  have hwU : J z ∈ U := by
    by_contra h
    exact hzY (Or.inl (Or.inr ⟨J z, h, hwz⟩))
  have hwD : J z ∉ D := fun h => hzY (Or.inr ⟨J z, h, hwz⟩)
  rcases hcov ⟨hwU, hwD⟩ with hwA | hwB
  · exact hzA ⟨J z, hwA, hwz⟩
  · have hwb : J z ≠ b := by
      intro h
      apply hzb
      rw [← hwz, h, hJb]
    have hzB : z ∈ J '' (B \ {b}) := ⟨J z, ⟨hwB, hwb⟩, hwz⟩
    obtain ⟨y, ⟨p, ⟨hpB, -⟩, rfl⟩, ⟨q, hqA, hq⟩⟩ :=
      mem_closure_iff.mp hzc _ hOB hzB
    have hpq : q = p := hJinv.injective hq
    subst hpq
    exact hAB.notMem_of_mem_right hpB hqA

/-- Step 4 of the V4 proof of `isPreconnected_diff_cell` (V4 CS14, steps 3–4 / CS14d): if `O`
is open and bounded, `a ∈ O`, and the radial map from `a` on `frontier O` is nullhomotopic, then
Borsuk's extension (CS10) over `closure O`, pasted with the radial map on `Oᶜ`, gives a
retraction of a large ball onto its boundary sphere, contradicting Brouwer (CS11). -/
private lemma isPreconnected_diff_cell_step4_retraction (n : ℕ)
    (hB : ∀ F : E n → E n, ContinuousOn F (closedBall 0 1) →
      MapsTo F (closedBall 0 1) (closedBall 0 1) →
      ∃ x ∈ closedBall (0 : E n) 1, F x = x)
    (O : Set (E n)) (hO : IsOpen O) (hbdd : Bornology.IsBounded O) (a : E n) (ha : a ∈ O)
    (hfr : a ∉ frontier O) (hnull : (radialMap n a (frontier O) hfr).Nullhomotopic) :
    False := by
  classical
  have hX : IsCompact (closure O) := hbdd.isCompact_closure
  obtain ⟨g, hg⟩ := exists_extension_of_nullhomotopic n (closure O) (frontier O) hX
    isClosed_frontier frontier_subset_closure (radialMap n a (frontier O) hfr) hnull
  obtain ⟨R₀, hR₀⟩ := hbdd.closure.subset_closedBall a
  set R : ℝ := max R₀ 0 + 1 with hR
  have hR₀' : R₀ ≤ max R₀ 0 := le_max_left _ _
  have hRpos : 0 < R := by have := le_max_right R₀ 0; linarith
  have hfar : ∀ z ∈ sphere a R, z ∉ closure O := by
    intro z hz hzO
    have h1 := hR₀ hzO
    rw [mem_closedBall] at h1
    rw [mem_sphere] at hz
    linarith
  let f₁ : E n → E n := fun z => if h : z ∈ closure O then (g ⟨z, h⟩ : E n) else 0
  let f₂ : E n → E n := fun z => ‖z - a‖⁻¹ • (z - a)
  let G : E n → E n := O.piecewise f₁ f₂
  have hf₁ : ContinuousOn f₁ (closure O) := by
    rw [continuousOn_iff_continuous_restrict]
    have : (closure O).restrict f₁ = fun z => (g z : E n) := by
      funext z
      simp [Set.restrict, f₁, z.2]
    rw [this]
    exact continuous_subtype_val.comp g.continuous
  have hne : ∀ z ∈ closure Oᶜ, z - a ≠ 0 := by
    intro z hz h
    rw [hO.isClosed_compl.closure_eq] at hz
    exact hz (sub_eq_zero.mp h ▸ ha)
  have hf₂ : ContinuousOn f₂ (closure Oᶜ) := by
    have hsub : ContinuousOn (fun z : E n => z - a) (closure Oᶜ) :=
      continuousOn_id.sub continuousOn_const
    exact (hsub.norm.inv₀ fun z hz => norm_ne_zero_iff.mpr (hne z hz)).smul hsub
  have hfr_eq : ∀ z ∈ frontier O, f₁ z = f₂ z := by
    intro z hz
    have hzc : z ∈ closure O := frontier_subset_closure hz
    simp only [f₁, f₂, dif_pos hzc]
    rw [hg z hz]
    rfl
  have hG : Continuous G := continuous_piecewise hfr_eq hf₁ hf₂
  have hGnorm : ∀ z, ‖G z‖ = 1 := by
    intro z
    by_cases hz : z ∈ O
    · have hzc : z ∈ closure O := subset_closure hz
      simp only [G, piecewise_eq_of_mem _ _ _ hz, f₁, dif_pos hzc]
      exact mem_sphere_zero_iff_norm.mp (g ⟨z, hzc⟩).2
    · simp only [G, piecewise_eq_of_notMem _ _ _ hz, f₂]
      have hza : z - a ≠ 0 := fun h => hz (sub_eq_zero.mp h ▸ ha)
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hza)]
  let ρ : E n → E n := fun z => a + R • G z
  have hρ : Continuous ρ := continuous_const.add (continuous_const.smul hG)
  refine no_retraction_of_brouwer n hB a R hRpos ρ hρ.continuousOn ?_ ?_
  · intro z _
    rw [mem_sphere, dist_eq_norm]
    simp only [ρ, add_sub_cancel_left, norm_smul, hGnorm, Real.norm_of_nonneg hRpos.le,
      mul_one]
  · intro z hz
    have hzO : z ∉ O := fun h => hfar z hz (subset_closure h)
    have hzR : ‖z - a‖ = R := by rw [← dist_eq_norm]; exact hz
    simp only [ρ, G, piecewise_eq_of_notMem _ _ _ hzO, f₂, hzR, smul_smul,
      mul_inv_cancel₀ hRpos.ne', one_smul, add_sub_cancel]

/-- Step 5 of the V4 proof of `isPreconnected_diff_cell` (V4 CS14, steps 1–4 assembled): a
separation of `U \ range e` by disjoint open sets `A ∋ a`, `B ∋ b` is impossible. Invert about
`b`; the radial map from `J a` is nullhomotopic on `Y₀` (step 2), hence on `Y₀ ∪ J '' range e`
(CS13, the only use of `k + 2 ≤ n`), hence on `frontier (J '' A)` (step 3); step 4 concludes. -/
private lemma isPreconnected_diff_cell_step5_core (k n : ℕ)
    (hB : ∀ F : E n → E n, ContinuousOn F (closedBall 0 1) →
      MapsTo F (closedBall 0 1) (closedBall 0 1) →
      ∃ x ∈ closedBall (0 : E n) 1, F x = x)
    (hkn : k + 2 ≤ n) (U : Set (E n)) (hUo : IsOpen U) (hUc : IsConnected U)
    (e : C(↥(closedBall (0 : E k) 1), E n)) (he : Function.Injective e)
    (he₁ : ∀ x : ↥(closedBall (0 : E k) 1), ‖(x : E k)‖ < 1 → e x ∈ U)
    (he₂ : ∀ x : ↥(closedBall (0 : E k) 1), ‖(x : E k)‖ = 1 → e x ∉ U)
    (A B : Set (E n)) (hA : IsOpen A) (hBo : IsOpen B) (hAB : Disjoint A B)
    (hcov : U \ range e ⊆ A ∪ B) (a b : E n) (haA : a ∈ A) (hbB : b ∈ B)
    (ha : a ∈ U \ range e) (hb : b ∈ U \ range e) : False := by
  set J := EuclideanGeometry.inversion b (1 : ℝ) with hJ
  have hJinv : Function.Involutive J := EuclideanGeometry.inversion_involutive b one_ne_zero
  have hJb : J b = b := EuclideanGeometry.inversion_self b 1
  have hab : a ≠ b := fun h => hAB.notMem_of_mem_right hbB (h ▸ haA)
  have hbA : b ∉ A := fun h => hAB.notMem_of_mem_right hbB h
  have hn : 1 ≤ n := by omega
  have heb : ∀ x, e x ≠ b := fun x h => hb.2 ⟨x, h⟩
  let θ : C(↥(closedBall (0 : E k) 1), E n) :=
    ⟨fun x => J (e x), (continuousOn_inversion n b).comp_continuous e.continuous heb⟩
  have hθrange : range θ = J '' range e := range_comp J e
  set Y₀ := insert b (J '' Uᶜ) with hY₀def
  have hY₀ : IsCompact Y₀ :=
    isCompact_inversion_image_insert n b Uᶜ hUo.isClosed_compl (fun h => h hb.1)
  have hθinj : Function.Injective θ := fun x y h => he (hJinv.injective h)
  have hθ : range θ ∩ Y₀ = θ '' {y | ‖(y : E k)‖ = 1} := by
    ext z
    constructor
    · rintro ⟨⟨y, rfl⟩, hzY⟩
      refine ⟨y, ?_, rfl⟩
      rcases hzY with h | ⟨w, hwU, hw⟩
      · exfalso
        apply heb y
        have h' : J (e y) = b := h
        rw [← hJinv (e y), h', hJb]
      · have hwy : w = e y := hJinv.injective hw
        have hle : ‖(y : E k)‖ ≤ 1 := mem_closedBall_zero_iff.mp y.2
        refine le_antisymm hle (not_lt.mp fun hlt => hwU ?_)
        rw [hwy]
        exact he₁ y hlt
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, Or.inr ⟨e y, he₂ y hy, rfl⟩⟩
  have ha'Y : J a ∉ Y₀ ∪ range θ := by
    rintro ((h | ⟨w, hwU, hw⟩) | ⟨y, hy⟩)
    · apply hab
      have h' : J a = b := h
      rw [← hJinv a, h', hJb]
    · exact hwU (hJinv.injective hw ▸ ha.1)
    · exact ha.2 ⟨y, hJinv.injective hy⟩
  have ha'Y₀ : J a ∉ Y₀ := fun h => ha'Y (Or.inl h)
  have hnull₀ : (restrictUnionLeft Y₀ (range θ)
      (radialMap n (J a) (Y₀ ∪ range θ) ha'Y)).Nullhomotopic := by
    have : restrictUnionLeft Y₀ (range θ) (radialMap n (J a) (Y₀ ∪ range θ) ha'Y) =
        radialMap n (J a) Y₀ ha'Y₀ := by
      ext y
      rfl
    rw [this]
    exact isPreconnected_diff_cell_step2_Y0_nullhomotopic n hn U hUo hUc a b ha.1 hb.1 hab
      ha'Y₀
  have hnullY := nullhomotopic_union_cell k n hkn Y₀ hY₀ θ hθinj hθ _ hnull₀
  have hOo : IsOpen (J '' A) := isOpen_inversion_image n b A hA hbA
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.mp hBo b hbB
  have hAε : A ∩ ball b ε = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hxA hxb
    exact hAB.notMem_of_mem_right (hεB hxb) hxA
  have hObdd : Bornology.IsBounded (J '' A) :=
    isBounded_closedBall.subset (inversion_image_bounded n b A ε hε hAε)
  have ha'O : J a ∈ J '' A := ⟨a, haA, rfl⟩
  have hfrY : frontier (J '' A) ⊆ Y₀ ∪ range θ := by
    rw [hθrange]
    exact isPreconnected_diff_cell_step3_frontier_subset n U (range e) A B b hA hBo hAB hcov
      hbB
  have hfr : J a ∉ frontier (J '' A) := fun h => ha'Y (hfrY h)
  have hnullF : (radialMap n (J a) (frontier (J '' A)) hfr).Nullhomotopic := by
    have : radialMap n (J a) (frontier (J '' A)) hfr =
        (radialMap n (J a) (Y₀ ∪ range θ) ha'Y).comp
          ⟨inclusion hfrY, continuous_inclusion hfrY⟩ := by
      ext y
      rfl
    rw [this]
    exact hnullY.comp_left _
  exact isPreconnected_diff_cell_step4_retraction n hB (J '' A) hOo hObdd (J a) ha'O hfr hnullF

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
  have hDc : IsClosed (range e) := (isCompact_range e.continuous).isClosed
  have hSo : IsOpen (U \ range e) := hUo.sdiff hDc
  intro u v hu hv hcov ⟨a, haS, hau⟩ ⟨b, hbS, hbv⟩
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  refine isPreconnected_diff_cell_step5_core k n hB hkn U hUo hUc e he he₁ he₂
    ((U \ range e) ∩ u) ((U \ range e) ∩ v) (hSo.inter hu) (hSo.inter hv) ?_ ?_ a b
    ⟨haS, hau⟩ ⟨hbS, hbv⟩ haS hbS
  · rw [Set.disjoint_iff_inter_eq_empty, ← hne]
    ext x
    simp only [mem_inter_iff]
    tauto
  · intro x hx
    rcases hcov hx with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩

end CellSeparation

end

end Enforce
