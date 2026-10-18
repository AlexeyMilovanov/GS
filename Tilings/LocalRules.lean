import Tilings.Alignment
import Tilings.Control.Composition
import Tilings.Control.Strict

/-!
# Local-rule transfers and the hereditary STS core (statements only)

Skeleton for `main.tex`: finite collar conversion (`lem:collar-conversion`),
dissection and glue colours (`lem:glues`), the compatible grouped hierarchy
lift (`lem:grouping-lift`) and the hereditary STS core theorems
(`thm:hereditary-substitution`, `thm:hereditary-hierarchy`).

The five principal theorems themselves are stated in `Tilings/Main.lean`.
All proofs are `sorry`.
-/

open Set Pointwise

noncomputable section

namespace Tilings

open Geometry

variable {P : Protoset}

/-! ## Finite collar conversion (`lem:collar-conversion`) -/

/-! ### Helpers for `lem:collar-conversion` -/

/-- A perpendicular vector in the plane. -/
private def ccPerp (d : Pt) : Pt := !₂[-d 1, d 0]

private lemma ccPerp_inner (d : Pt) : inner ℝ (ccPerp d) d = 0 := by
  simp [ccPerp, PiLp.inner_apply, Fin.sum_univ_two]
  ring

private lemma ccPerp_ne_zero {d : Pt} (hd : d ≠ 0) : ccPerp d ≠ 0 := by
  intro h
  apply hd
  have h0 := congrFun (congrArg (fun v : Pt => (v : Fin 2 → ℝ)) h) 0
  have h1 := congrFun (congrArg (fun v : Pt => (v : Fin 2 → ℝ)) h) 1
  simp [ccPerp] at h0 h1
  ext i
  fin_cases i <;> simp [h0, h1]

/-- A preconnected set avoiding the frontier lies inside or outside. -/
private lemma cc_preconn_sub {s H : Set Pt} (hH : IsPreconnected H) (hf : Disjoint H (frontier s)) :
    H ⊆ interior s ∨ H ⊆ (closure s)ᶜ := by
  refine hH.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl ?_ ?_
  · exact disjoint_compl_right.mono_left (interior_subset.trans subset_closure)
  · intro y hy
    by_cases h1 : y ∈ interior s
    · exact Or.inl h1
    · right
      intro h2
      exact hf.ne_of_mem hy ⟨h2, h1⟩ rfl

private lemma cc_segment_compact (x y : Pt) : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image']; exact isCompact_Icc.image (by fun_prop)

/-- Half-disk structure of a polygonal disk at a non-vertex frontier point. -/
private lemma cc_halfdisk (Q : PolygonalDisk) {x : Pt} (hx : x ∈ frontier Q.carrier)
    (hv : x ∉ Q.vertexSet) :
    ∃ (i : Fin Q.n) (ε : ℝ) (d n : Pt), 0 < ε ∧ d ≠ 0 ∧ n ≠ 0 ∧ inner ℝ n d = 0 ∧
      (∀ s : ℝ, |s| < ε → x + s • d ∈ Q.side i) ∧
      (∀ y, dist y x < ε → 0 < inner ℝ n (y - x) → y ∈ interior Q.carrier) := by
  have hx' := hx
  rw [Q.frontier_eq, mem_iUnion] at hx'
  obtain ⟨i, hxi⟩ := hx'
  set v := Q.vertex i with hvdef
  set w := Q.vertex (finRotate Q.n i) with hwdef
  have hxv : x ≠ v := fun h => hv ⟨i, h.symm⟩
  have hxw : x ≠ w := fun h => hv ⟨finRotate Q.n i, h.symm⟩
  rw [segment_eq_image'] at hxi
  obtain ⟨t, ⟨ht0, ht1⟩, hxt⟩ := hxi
  set d := w - v with hd
  have hd0 : d ≠ 0 := by
    intro h; apply hxv; rw [← hxt, h]; simp
  have ht0' : t ≠ 0 := by rintro rfl; apply hxv; rw [← hxt]; simp
  have ht1' : t ≠ 1 := by rintro rfl; apply hxw; rw [← hxt]; simp [hd]
  have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0')
  have htlt : t < 1 := lt_of_le_of_ne ht1 ht1'
  -- other sides
  set O : Set Pt := ⋃ j ∈ ({j | j ≠ i} : Set (Fin Q.n)), Q.side j with hO
  have hOc : IsClosed O := by
    apply Set.Finite.isClosed_biUnion (Set.toFinite _)
    intro j _
    exact (cc_segment_compact _ _).isClosed
  have hxO : x ∉ O := by
    simp only [hO, mem_iUnion, mem_setOf_eq, not_exists]
    intro j hj hxj
    have hxi2 : x ∈ Q.side i := by
      rw [PolygonalDisk.side, segment_eq_image']; exact ⟨t, ⟨ht0, ht1⟩, hxt⟩
    have := Q.simple i j (Ne.symm hj) ⟨hxi2, hxj⟩
    rcases this.1 with h | h
    · exact hxv h
    · exact hxw h
  obtain ⟨ε₁, hε₁, hε₁O⟩ := Metric.isOpen_iff.mp hOc.isOpen_compl x hxO
  have hfr : ∀ y, dist y x < ε₁ → y ∈ frontier Q.carrier → ∃ θ : ℝ, y = v + θ • d := by
    intro y hy hyf
    rw [Q.frontier_eq, mem_iUnion] at hyf
    obtain ⟨j, hj⟩ := hyf
    by_cases hji : j = i
    · subst hji
      rw [segment_eq_image'] at hj
      obtain ⟨θ, _, hθ⟩ := hj
      exact ⟨θ, hθ.symm⟩
    · exfalso
      have : y ∈ O := by
        simp only [hO, mem_iUnion, mem_setOf_eq]
        exact ⟨j, hji, hj⟩
      exact hε₁O (Metric.mem_ball.mpr hy) this
  set n₀ := ccPerp d with hn₀
  have hn₀d : inner ℝ n₀ d = 0 := ccPerp_inner d
  have hn₀ne : n₀ ≠ 0 := ccPerp_ne_zero hd0
  have hline : ∀ θ : ℝ, inner ℝ n₀ (v + θ • d - x) = 0 := by
    intro θ
    rw [← hxt]
    have : v + θ • d - (v + t • d) = (θ - t) • d := by
      rw [sub_smul]; abel
    rw [this, inner_smul_right, hn₀d, mul_zero]
  set ε := min ε₁ (min t (1 - t)) with hε
  have hεpos : 0 < ε := lt_min hε₁ (lt_min htpos (by linarith))
  -- interior point near x off the line
  have hxcl : x ∈ closure (interior Q.carrier) := by
    rw [Q.regular_closed]; exact Q.compact.isClosed.frontier_subset hx
  obtain ⟨z0, hz0i, hz0x⟩ := Metric.mem_closure_iff.mp hxcl (ε / 2) (by linarith)
  obtain ⟨δ0, hδ0, hδ0b⟩ := Metric.isOpen_iff.mp isOpen_interior z0 hz0i
  have hz : ∃ z ∈ interior Q.carrier, dist z x < ε ∧ inner ℝ n₀ (z - x) ≠ 0 := by
    by_cases hz0 : inner ℝ n₀ (z0 - x) = 0
    · have hnpos : 0 < ‖n₀‖ := norm_pos_iff.mpr hn₀ne
      set δ := min δ0 (ε / 2) / (2 * ‖n₀‖) with hδ
      have hmin : 0 < min δ0 (ε / 2) := lt_min hδ0 (by linarith)
      have hδpos : 0 < δ := div_pos hmin (by positivity)
      have hnorm : ‖δ • n₀‖ = min δ0 (ε / 2) / 2 := by
        rw [norm_smul, Real.norm_of_nonneg hδpos.le, hδ]; field_simp
      refine ⟨z0 + δ • n₀, hδ0b ?_, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hnorm]
        have := min_le_left δ0 (ε / 2); linarith
      · calc dist (z0 + δ • n₀) x ≤ dist (z0 + δ • n₀) z0 + dist z0 x := dist_triangle _ _ _
          _ < ε := by
            rw [dist_eq_norm, add_sub_cancel_left, hnorm, dist_comm]
            have := min_le_right δ0 (ε / 2); linarith
      · have : z0 + δ • n₀ - x = (z0 - x) + δ • n₀ := by abel
        rw [this, inner_add_right, hz0, inner_smul_right, real_inner_self_eq_norm_sq]
        positivity
    · exact ⟨z0, hz0i, by rw [dist_comm]; linarith, hz0⟩
  obtain ⟨z, hzi, hzx, hzn⟩ := hz
  have hsign : ∃ n : Pt, n ≠ 0 ∧ inner ℝ n d = 0 ∧ 0 < inner ℝ n (z - x) ∧
      ∀ θ : ℝ, inner ℝ n (v + θ • d - x) = 0 := by
    rcases lt_or_gt_of_ne hzn with h | h
    · refine ⟨-n₀, neg_ne_zero.mpr hn₀ne, by rw [inner_neg_left, hn₀d, neg_zero], ?_, ?_⟩
      · rw [inner_neg_left]; linarith
      · intro θ; rw [inner_neg_left, hline, neg_zero]
    · exact ⟨n₀, hn₀ne, hn₀d, h, hline⟩
  obtain ⟨n, hn0, hnd, hnz, hnline⟩ := hsign
  refine ⟨i, ε, d, n, hεpos, hd0, hn0, hnd, ?_, ?_⟩
  · intro s hs
    rw [PolygonalDisk.side, segment_eq_image']
    have hs1 : |s| < t := lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_left _ _))
    have hs2 : |s| < 1 - t := lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨t + s, ⟨?_, ?_⟩, ?_⟩
    · have := neg_abs_le s; linarith
    · have := le_abs_self s; linarith
    · show v + (t + s) • d = x + s • d
      rw [← hxt, add_smul]; simp only; abel
  · set H : Set Pt := Metric.ball x ε ∩ {y | 0 < inner ℝ n (y - x)} with hH
    have hHconv : Convex ℝ H := by
      apply (convex_ball x ε).inter
      intro a ha b hb α β hα hβ hαβ
      simp only [mem_setOf_eq] at ha hb ⊢
      have : α • a + β • b - x = α • (a - x) + β • (b - x) := by
        calc α • a + β • b - x = α • a + β • b - (α + β) • x := by rw [hαβ, one_smul]
          _ = α • (a - x) + β • (b - x) := by rw [add_smul, smul_sub, smul_sub]; abel
      rw [this, inner_add_right, inner_smul_right, inner_smul_right]
      rcases hα.eq_or_lt with h | h
      · subst h; simp at hαβ; subst hαβ; simpa using hb
      · have := mul_pos h ha; nlinarith
    have hHdisj : Disjoint H (frontier Q.carrier) := by
      rw [Set.disjoint_left]
      rintro y ⟨hy1, hy2⟩ hyf
      have hy1' : dist y x < ε₁ := lt_of_lt_of_le (Metric.mem_ball.mp hy1) (min_le_left _ _)
      obtain ⟨θ, rfl⟩ := hfr y hy1' hyf
      simp only [mem_setOf_eq] at hy2
      rw [hnline θ] at hy2
      exact lt_irrefl _ hy2
    rcases cc_preconn_sub hHconv.isPreconnected hHdisj with h | h
    · intro y hy hyn
      exact h ⟨Metric.mem_ball.mpr hy, hyn⟩
    · exfalso
      exact h ⟨Metric.mem_ball.mpr hzx, hnz⟩ (subset_closure (interior_subset hzi))

private lemma cc_parallel {n a b : Pt} (hn : n ≠ 0) (hb : b ≠ 0) (ha0 : inner ℝ n a = 0)
    (hb0 : inner ℝ n b = 0) : ∃ c : ℝ, a = c • b := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial] at ha0 hb0
  have hcross : a 0 * b 1 = a 1 * b 0 := by
    by_cases h0 : n 0 = 0
    · have h1 : n 1 ≠ 0 := by
        intro h1; apply hn; ext i; fin_cases i <;> simp [h0, h1]
      have e1 : a 1 = 0 := by
        rw [h0] at ha0; simp at ha0; rcases ha0 with h | h <;> simp_all
      have e2 : b 1 = 0 := by
        rw [h0] at hb0; simp at hb0; rcases hb0 with h | h <;> simp_all
      rw [e1, e2]; ring
    · have : n 0 * (a 0 * b 1 - a 1 * b 0) = 0 := by linear_combination b 1 * ha0 - a 1 * hb0
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h0
      · linarith
  by_cases hb0' : b 0 = 0
  · have hb1 : b 1 ≠ 0 := by
      intro h1; apply hb; ext i; fin_cases i <;> simp [hb0', h1]
    refine ⟨a 1 / b 1, ?_⟩
    ext i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
      rw [hb0'] at hcross ⊢
      have : a 0 = 0 := by
        have := hcross; simp at this; rcases this with h | h
        · exact h
        · exact absurd h hb1
      rw [this]; ring
    · simp only [Fin.mk_one, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
      field_simp
  · refine ⟨a 0 / b 0, ?_⟩
    ext i; fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
      field_simp
      linarith

private lemma cc_tile_carrier_closed (A : PlacedTile P) : IsClosed A.carrier := by
  unfold PlacedTile.carrier
  exact (P.disk A.form).compact.isClosed.vadd _

private lemma cc_tile_regular (A : PlacedTile P) : closure (interior A.carrier) = A.carrier := by
  unfold PlacedTile.carrier
  rw [interior_vadd, closure_vadd, (P.disk A.form).regular_closed]

private lemma cc_halfdisk_tile (A : PlacedTile P) {x : Pt} (hx : x ∈ A.carrier)
    (hint : x ∉ interior A.carrier) (hv : x ∉ A.vertexSet) :
    ∃ (i : Fin (P.disk A.form).n) (ε : ℝ) (d n : Pt), 0 < ε ∧ d ≠ 0 ∧ n ≠ 0 ∧ inner ℝ n d = 0 ∧
      (∀ s : ℝ, |s| < ε → x + s • d ∈ A.side i) ∧
      (∀ y, dist y x < ε → 0 < inner ℝ n (y - x) → y ∈ interior A.carrier) := by
  set Q := P.disk A.form
  have hx' : -A.anchor + x ∈ frontier Q.carrier := by
    unfold PlacedTile.carrier at hx hint
    rw [interior_vadd, mem_vadd_set_iff_neg_vadd_mem] at hint
    rw [mem_vadd_set_iff_neg_vadd_mem] at hx
    rw [Q.compact.isClosed.frontier_eq]
    exact ⟨hx, hint⟩
  have hv' : -A.anchor + x ∉ Q.vertexSet := by
    rintro ⟨k, hk⟩
    apply hv
    refine ⟨k, ?_⟩
    simp only [PlacedTile.vertex, vadd_eq_add]
    rw [hk]; abel
  obtain ⟨i, ε, d, n, hε, hd, hn, hnd, hs, hy⟩ := cc_halfdisk Q hx' hv'
  refine ⟨i, ε, d, n, hε, hd, hn, hnd, ?_, ?_⟩
  · intro s hs'
    have := hs s hs'
    unfold PlacedTile.side
    rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    convert this using 1; abel
  · intro y hyx hyn
    unfold PlacedTile.carrier
    rw [interior_vadd, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    apply hy
    · rw [dist_eq_norm] at hyx ⊢; convert hyx using 2; abel
    · convert hyn using 2; abel

/-- Two tiles with disjoint interiors meeting at a point which is a vertex of neither
share a side segment of positive length. -/
private lemma cc_key {A B : PlacedTile P} (hd : Disjoint (interior A.carrier) (interior B.carrier))
    {x : Pt} (hxA : x ∈ A.carrier) (hxB : x ∈ B.carrier) (hvA : x ∉ A.vertexSet)
    (hvB : x ∉ B.vertexSet) : ∃ i j, OverlapPos (A.side i) (B.side j) := by
  have hnotint : ∀ {A B : PlacedTile P}, Disjoint (interior A.carrier) (interior B.carrier) →
      x ∈ B.carrier → x ∉ interior A.carrier := by
    intro A B hd hxB hxA
    rw [← cc_tile_regular B, mem_closure_iff_nhds] at hxB
    obtain ⟨z, hz1, hz2⟩ := hxB _ (isOpen_interior.mem_nhds hxA)
    exact Set.disjoint_left.mp hd hz1 hz2
  obtain ⟨i, ε₁, d₁, n₁, hε₁, hd₁, hn₁, hnd₁, hs₁, hy₁⟩ :=
    cc_halfdisk_tile A hxA (hnotint hd hxB) hvA
  obtain ⟨j, ε₂, d₂, n₂, hε₂, hd₂, hn₂, hnd₂, hs₂, hy₂⟩ :=
    cc_halfdisk_tile B hxB (hnotint hd.symm hxA) hvB
  have key : inner ℝ n₂ d₁ = 0 := by
    by_contra hne
    obtain ⟨w, hw2, hw1⟩ : ∃ w : Pt, 0 < inner ℝ n₂ w ∧ inner ℝ n₁ w = 0 := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨-d₁, by rw [inner_neg_right]; linarith, by rw [inner_neg_right, hnd₁, neg_zero]⟩
      · exact ⟨d₁, h, hnd₁⟩
    set τ := (|inner ℝ n₂ n₁| + 1) / inner ℝ n₂ w with hτ
    set u := n₁ + τ • w with hu
    have hu2 : 0 < inner ℝ n₂ u := by
      rw [hu, inner_add_right, inner_smul_right, hτ, div_mul_cancel₀ _ hw2.ne']
      have := neg_abs_le (inner ℝ n₂ n₁); linarith
    have hu1 : 0 < inner ℝ n₁ u := by
      rw [hu, inner_add_right, inner_smul_right, hw1, mul_zero, add_zero,
        real_inner_self_eq_norm_sq]
      have := norm_pos_iff.mpr hn₁; positivity
    have hu0 : u ≠ 0 := by rintro h; rw [h, inner_zero_right] at hu1; exact lt_irrefl _ hu1
    have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    set δ := min ε₁ ε₂ / (2 * ‖u‖) with hδ
    have hδpos : 0 < δ := div_pos (lt_min hε₁ hε₂) (by positivity)
    have hdist : dist (x + δ • u) x = min ε₁ ε₂ / 2 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδpos.le, hδ]
      field_simp
    have hm1 := min_le_left ε₁ ε₂
    have hm2 := min_le_right ε₁ ε₂
    have hmpos : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
    have h1 : x + δ • u ∈ interior A.carrier := by
      apply hy₁ _ (by rw [hdist]; linarith)
      rw [add_sub_cancel_left, inner_smul_right]; positivity
    have h2 : x + δ • u ∈ interior B.carrier := by
      apply hy₂ _ (by rw [hdist]; linarith)
      rw [add_sub_cancel_left, inner_smul_right]; positivity
    exact Set.disjoint_left.mp hd h1 h2
  obtain ⟨c, hc⟩ := cc_parallel hn₂ hd₂ key hnd₂
  have hc0 : c ≠ 0 := by rintro rfl; apply hd₁; rw [hc, zero_smul]
  have hcpos : 0 < |c| := abs_pos.mpr hc0
  set s₀ := min ε₁ (ε₂ / |c|) / 2 with hs₀
  have hs₀pos : 0 < s₀ := by
    have : 0 < min ε₁ (ε₂ / |c|) := lt_min hε₁ (div_pos hε₂ hcpos)
    positivity
  refine ⟨i, j, x + (-s₀) • d₁, x + s₀ • d₁, ?_, ?_⟩
  · intro h
    have : (2 * s₀) • d₁ = 0 := by
      have h' := congrArg (fun z => z - x) h
      simp only [add_sub_cancel_left] at h'
      have e : (2 * s₀) • d₁ = s₀ • d₁ - (-s₀) • d₁ := by
        rw [neg_smul, sub_neg_eq_add, ← add_smul, two_mul]
      rw [e, h', sub_self]
    rcases smul_eq_zero.mp this with h | h
    · linarith
    · exact hd₁ h
  · rw [segment_eq_image']
    rintro _ ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    have he : x + (-s₀) • d₁ + θ • (x + s₀ • d₁ - (x + (-s₀) • d₁)) =
        x + ((2 * θ - 1) * s₀) • d₁ := by
      rw [add_sub_add_left_eq_sub, ← sub_smul]
      rw [smul_smul, add_assoc, ← add_smul]; congr 2; ring
    simp only
    rw [he]
    have hab : |(2 * θ - 1) * s₀| ≤ s₀ := by
      rw [abs_mul, abs_of_pos hs₀pos]
      have : |2 * θ - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      nlinarith [abs_nonneg (2 * θ - 1)]
    have hm1 := min_le_left ε₁ (ε₂ / |c|)
    have hm2 := min_le_right ε₁ (ε₂ / |c|)
    refine ⟨hs₁ _ (by linarith), ?_⟩
    rw [hc, smul_smul]
    apply hs₂
    rw [abs_mul]
    calc |(2 * θ - 1) * s₀| * |c| ≤ s₀ * |c| := by gcongr
      _ < ε₂ / |c| * |c| := by gcongr; linarith
      _ = ε₂ := div_mul_cancel₀ _ hcpos.ne'

private lemma cc_form_consts (P : Protoset) :
    ∃ (z : P.Form → Pt) (ρ M : ℝ), 0 < ρ ∧ 0 ≤ M ∧
      (∀ q, Metric.ball (z q) ρ ⊆ interior (P.disk q).carrier) ∧
      (∀ q, ‖z q‖ ≤ M) ∧ (∀ q, ∀ y ∈ (P.disk q).carrier, ‖y‖ ≤ M) := by
  have h1 : ∀ q : P.Form, ∃ z : Pt, ∃ r > 0, Metric.ball z r ⊆ interior (P.disk q).carrier := by
    intro q
    obtain ⟨z, hz⟩ := (P.disk q).interior_nonempty
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    exact ⟨z, r, hr, hb⟩
  choose z r hr hb using h1
  have h2 : ∀ q : P.Form, ∃ m : ℝ, 0 ≤ m ∧ ∀ y ∈ (P.disk q).carrier, ‖y‖ ≤ m := by
    intro q
    obtain ⟨m, hm⟩ := isBounded_iff_forall_norm_le.mp (P.disk q).compact.isBounded
    exact ⟨max m 0, le_max_right _ _, fun y hy => (hm y hy).trans (le_max_left _ _)⟩
  choose m hm0 hm using h2
  have hzc : ∀ q, z q ∈ (P.disk q).carrier := fun q =>
    interior_subset (hb q (Metric.mem_ball_self (hr q)))
  set ρ := 1 / (1 + ∑ q, 1 / r q) with hρ
  have hsum : 0 ≤ ∑ q, 1 / r q := Finset.sum_nonneg fun q _ => (one_div_pos.mpr (hr q)).le
  refine ⟨z, ρ, ∑ q, m q, by positivity, Finset.sum_nonneg fun q _ => hm0 q, ?_, ?_, ?_⟩
  · intro q
    refine (Metric.ball_subset_ball ?_).trans (hb q)
    have hle : 1 / r q ≤ 1 + ∑ q, 1 / r q := by
      have := Finset.single_le_sum (f := fun q => 1 / r q) (fun q _ => (one_div_pos.mpr (hr q)).le)
        (Finset.mem_univ q)
      linarith
    rw [hρ]
    calc 1 / (1 + ∑ q, 1 / r q) ≤ 1 / (1 / r q) :=
          one_div_le_one_div_of_le (one_div_pos.mpr (hr q)) hle
      _ = r q := by rw [one_div_one_div]
  · intro q
    exact (hm q _ (hzc q)).trans (Finset.single_le_sum (fun q _ => hm0 q) (Finset.mem_univ q))
  · intro q y hy
    exact (hm q y hy).trans (Finset.single_le_sum (fun q _ => hm0 q) (Finset.mem_univ q))

/-- Uniform local finiteness: a ball meets a uniformly bounded number of tiles of any
set with disjoint interiors. -/
private lemma cc_count (P : Protoset) (R : ℝ) :
    ∃ N : ℕ, ∀ S : Set (PlacedTile P), DisjointInteriors S → ∀ c : Pt,
      {X ∈ S | (X.carrier ∩ Metric.ball c R).Nonempty}.Finite ∧
      {X ∈ S | (X.carrier ∩ Metric.ball c R).Nonempty}.ncard ≤ N := by
  obtain ⟨z, ρ, M, hρ, hM, hzb, hzM, hyM⟩ := cc_form_consts P
  obtain ⟨t, -, htfin, htcov⟩ := finite_cover_balls_of_compact
    (isCompact_closedBall (0 : Pt) (R + 2 * M)) (half_pos hρ)
  refine ⟨t.ncard, fun S hS c => ?_⟩
  set Mc := {X ∈ S | (X.carrier ∩ Metric.ball c R).Nonempty} with hMc
  have hctr : ∀ X ∈ Mc, X.anchor + z X.form - c ∈ Metric.closedBall (0 : Pt) (R + 2 * M) := by
    rintro X ⟨-, y, hyX, hyc⟩
    unfold PlacedTile.carrier at hyX
    rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hyX
    have h1 := hyM _ _ hyX
    have h2 := hzM X.form
    rw [Metric.mem_ball, dist_eq_norm] at hyc
    rw [mem_closedBall_zero_iff]
    have : X.anchor + z X.form - c = (z X.form) - (-X.anchor + y) + (y - c) := by abel
    rw [this]
    calc ‖z X.form - (-X.anchor + y) + (y - c)‖ ≤ ‖z X.form‖ + ‖-X.anchor + y‖ + ‖y - c‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ R + 2 * M := by linarith
  have hf : ∀ X ∈ Mc, ∃ s ∈ t, X.anchor + z X.form - c ∈ Metric.ball s (ρ / 2) := by
    intro X hX
    have := htcov (hctr X hX)
    simpa only [mem_iUnion, exists_prop] using this
  choose! f hft hfb using hf
  have hinj : Set.InjOn f Mc := by
    intro X hX Y hY hXY
    by_contra hne
    have hd : dist (X.anchor + z X.form) (Y.anchor + z Y.form) < ρ := by
      have h1 := hfb X hX
      have h2 := hfb Y hY
      rw [hXY] at h1
      rw [Metric.mem_ball] at h1 h2
      calc dist (X.anchor + z X.form) (Y.anchor + z Y.form)
          = dist (X.anchor + z X.form - c) (Y.anchor + z Y.form - c) := by
            rw [dist_sub_right]
        _ ≤ dist (X.anchor + z X.form - c) (f Y) + dist (f Y) (Y.anchor + z Y.form - c) :=
            dist_triangle _ _ _
        _ < ρ / 2 + ρ / 2 := by rw [dist_comm (f Y)]; gcongr
        _ = ρ := by ring
    have hint : ∀ W : PlacedTile P, ∀ p, dist p (W.anchor + z W.form) < ρ →
        p ∈ interior W.carrier := by
      intro W p hp
      unfold PlacedTile.carrier
      rw [interior_vadd, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
      apply hzb W.form
      rw [dist_eq_norm] at hp
      rw [Metric.mem_ball, dist_eq_norm]
      convert hp using 2; abel
    have h1 := hint X (Y.anchor + z Y.form) (by rw [dist_comm]; exact hd)
    have h2 := hint Y (Y.anchor + z Y.form) (by simp [hρ])
    exact Set.disjoint_left.mp (hS hX.1 hY.1 hne) h1 h2
  refine ⟨Set.Finite.of_finite_image (htfin.subset ?_) hinj, ?_⟩
  · rintro _ ⟨X, hX, rfl⟩; exact hft X hX
  · exact Set.ncard_le_ncard_of_injOn f hft hinj htfin

private lemma cc_ball_diff_conn (c : Pt) {R : ℝ} (hR : 0 < R) {V : Set Pt} (hV : V.Finite) :
    IsPreconnected (Metric.ball c R \ V) := by
  set e := OpenPartialHomeomorph.univBall c R with he
  have h1 : 1 < Module.rank ℝ Pt := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num
  have hsrc : e.source = univ := OpenPartialHomeomorph.univBall_source c R
  have htgt : e.target = Metric.ball c R := OpenPartialHomeomorph.univBall_target c hR
  have hc : (e ⁻¹' V).Countable := by
    refine (hV.preimage ?_).countable
    intro a _ b _ hab
    exact e.injOn (by rw [hsrc]; trivial) (by rw [hsrc]; trivial) hab
  have hconn := hc.isConnected_compl_of_one_lt_rank h1
  have himg : e '' (e ⁻¹' V)ᶜ = Metric.ball c R \ V := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨by rw [← htgt]; exact e.map_source (by rw [hsrc]; trivial), hx⟩
    · rintro ⟨hy, hyV⟩
      rw [← htgt] at hy
      refine ⟨e.symm y, ?_, e.right_inv hy⟩
      simp only [mem_compl_iff, mem_preimage, e.right_inv hy]
      exact hyV
  rw [← himg]
  exact (hconn.image _ (e.continuousOn.mono (by rw [hsrc]; exact subset_univ _))).isPreconnected

/-- Side adjacency of placed tiles: distinct tiles with a common whole side. -/
private def ccSAdj (X Y : PlacedTile P) : Prop := X ≠ Y ∧ ∃ i j, X.side i = Y.side j

private lemma ccSAdj.symm {X Y : PlacedTile P} (h : ccSAdj X Y) : ccSAdj Y X :=
  ⟨Ne.symm h.1, let ⟨i, j, hij⟩ := h.2; ⟨j, i, hij.symm⟩⟩

/-- Chains of length `n` inside `S` for a relation `adj`. -/
private def ccChain {α : Type*} (adj : α → α → Prop) (S : Set α) (n : ℕ) (x y : α) : Prop :=
  ∃ f : ℕ → α, f 0 = x ∧ f n = y ∧ (∀ t ≤ n, f t ∈ S) ∧ ∀ t < n, adj (f t) (f (t + 1))

private lemma cc_finite_vertexSet (X : PlacedTile P) : X.vertexSet.Finite :=
  Set.finite_range _

/-- Connectivity: any two tiles of an STS plane tiling meeting an open ball are joined by an
adjacency chain inside the tiling of length at most the number of tiles meeting the ball. -/
private lemma cc_conn (T : PlaneTiling P) (hT : T.SideToSide) (c : Pt) (R : ℝ)
    (hfin : {Y ∈ T.tiles | (Y.carrier ∩ Metric.ball c R).Nonempty}.Finite)
    {A X : PlacedTile P} (hA : A ∈ {Y ∈ T.tiles | (Y.carrier ∩ Metric.ball c R).Nonempty})
    (hX : X ∈ {Y ∈ T.tiles | (Y.carrier ∩ Metric.ball c R).Nonempty}) :
    ∃ m ≤ {Y ∈ T.tiles | (Y.carrier ∩ Metric.ball c R).Nonempty}.ncard,
      ccChain ccSAdj T.tiles m A X := by
  classical
  set Mc := {Y ∈ T.tiles | (Y.carrier ∩ Metric.ball c R).Nonempty} with hMc
  let G : SimpleGraph (PlacedTile P) :=
    { Adj := fun Y Z => Y ∈ Mc ∧ Z ∈ Mc ∧ ccSAdj Y Z
      symm := fun Y Z h => ⟨h.2.1, h.1, h.2.2.symm⟩
      loopless := ⟨fun Y h => h.2.2.1 rfl⟩ }
  set C := {Y ∈ Mc | G.Reachable A Y} with hC
  have hR : 0 < R := by
    obtain ⟨y, -, hy⟩ := hA.2
    exact lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hy)
  have hXC : X ∈ C := by
    by_contra hXC
    set V := ⋃ Y ∈ Mc, Y.vertexSet with hV
    have hVfin : V.Finite := hfin.biUnion fun Y _ => cc_finite_vertexSet Y
    have hconn := cc_ball_diff_conn c hR hVfin
    rw [isPreconnected_closed_iff] at hconn
    have hcl : ∀ D ⊆ Mc, IsClosed (⋃ Y ∈ D, Y.carrier) := fun D hD =>
      Set.Finite.isClosed_biUnion (hfin.subset hD) fun Y _ => cc_tile_carrier_closed Y
    have hpt : ∀ Y ∈ Mc, ∃ y ∈ Metric.ball c R \ V, y ∈ Y.carrier := by
      intro Y hY
      obtain ⟨y, hyY, hyb⟩ := hY.2
      rw [← cc_tile_regular Y, mem_closure_iff_nhds] at hyY
      obtain ⟨w, hw1, hw2⟩ := hyY _ (Metric.isOpen_ball.mem_nhds hyb)
      have hopen : IsOpen (interior Y.carrier ∩ Metric.ball c R) :=
        isOpen_interior.inter Metric.isOpen_ball
      obtain ⟨u, hu1, hu2⟩ :=
        (hVfin.countable.dense_compl ℝ).inter_open_nonempty _ hopen ⟨w, hw2, hw1⟩
      exact ⟨u, ⟨hu1.2, hu2⟩, interior_subset hu1.1⟩
    obtain ⟨y, hyU, hy1, hy2⟩ := hconn (⋃ Y ∈ C, Y.carrier) (⋃ Y ∈ Mc \ C, Y.carrier)
      (hcl C (fun Y hY => hY.1)) (hcl (Mc \ C) diff_subset)
      (by
        rintro y ⟨hyb, -⟩
        have : y ∈ support T.tiles := by rw [T.cover]; trivial
        simp only [support, mem_iUnion, exists_prop] at this
        obtain ⟨Y, hYT, hyY⟩ := this
        have hYM : Y ∈ Mc := ⟨hYT, y, hyY, hyb⟩
        by_cases hYC : Y ∈ C
        · exact Or.inl (mem_biUnion hYC hyY)
        · exact Or.inr (mem_biUnion ⟨hYM, hYC⟩ hyY))
      (by
        obtain ⟨y, hyU, hyA⟩ := hpt A hA
        exact ⟨y, hyU, mem_biUnion (⟨hA, SimpleGraph.Reachable.refl A⟩ : A ∈ C) hyA⟩)
      (by
        obtain ⟨y, hyU, hyX⟩ := hpt X hX
        exact ⟨y, hyU, mem_biUnion (⟨hX, hXC⟩ : X ∈ Mc \ C) hyX⟩)
    simp only [mem_iUnion, exists_prop] at hy1 hy2
    obtain ⟨Y₁, hY₁, hyY₁⟩ := hy1
    obtain ⟨Y₂, hY₂, hyY₂⟩ := hy2
    have hne : Y₁ ≠ Y₂ := by rintro rfl; exact hY₂.2 hY₁
    have hnv : ∀ Y ∈ Mc, y ∉ Y.vertexSet := fun Y hY hyv =>
      hyU.2 (mem_biUnion hY hyv)
    obtain ⟨i, j, hij⟩ := cc_key (T.disjoint hY₁.1.1 hY₂.1.1 hne) hyY₁ hyY₂
      (hnv Y₁ hY₁.1) (hnv Y₂ hY₂.1)
    have hside := hT Y₁ hY₁.1.1 Y₂ hY₂.1.1 i j hij
    have hadj : G.Adj Y₁ Y₂ := ⟨hY₁.1, hY₂.1, hne, i, j, hside⟩
    exact hY₂.2 ⟨hY₂.1, hY₁.2.trans hadj.reachable⟩
  obtain ⟨p⟩ := hXC.2
  set q := p.bypass with hq
  have hqp : q.IsPath := p.bypass_isPath
  have hmem : ∀ t ≤ q.length, q.getVert t ∈ Mc := by
    intro t ht
    rcases lt_or_eq_of_le ht with h | h
    · exact (q.adj_getVert_succ h).1
    · rw [h, q.getVert_length]; exact hX
  refine ⟨q.length, ?_, q.getVert, q.getVert_zero, q.getVert_length,
    fun t ht => (hmem t ht).1, fun t ht => (q.adj_getVert_succ ht).2.2⟩
  have hsub : q.support.toFinset ⊆ hfin.toFinset := by
    intro Y hY
    rw [List.mem_toFinset, SimpleGraph.Walk.mem_support_iff_exists_getVert] at hY
    obtain ⟨t, rfl, ht⟩ := hY
    rw [Set.Finite.mem_toFinset]; exact hmem t ht
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hqp.support_nodup, SimpleGraph.Walk.length_support,
    ← Set.ncard_eq_toFinset_card _ hfin] at hcard
  omega

private lemma cc_tile_compact (A : PlacedTile P) : IsCompact A.carrier := by
  unfold PlacedTile.carrier
  rw [← image_vadd]
  exact (P.disk A.form).compact.image (continuous_const_vadd _)

private lemma cc_tile_nonempty (A : PlacedTile P) : A.carrier.Nonempty := by
  obtain ⟨y, hy⟩ := (P.disk A.form).interior_nonempty
  exact ⟨A.anchor +ᵥ y, vadd_mem_vadd_set (interior_subset hy)⟩

/-- Tiles of a bounded-diameter finite subpatch of an STS plane tiling are joined by
adjacency chains of uniformly bounded length. -/
private lemma cc_geo_bound (P : Protoset) (D : ℝ) : ∃ K : ℕ, ∀ T : PlaneTiling P, T.SideToSide →
    ∀ S ⊆ T.tiles, S.Finite → Metric.diam (support S) ≤ D →
      ∀ A ∈ S, ∀ X ∈ S, ∃ m ≤ K, ccChain ccSAdj T.tiles m A X := by
  obtain ⟨N, hN⟩ := cc_count P (max D 0 + 1)
  refine ⟨N, fun T hT S hST hS hD A hA X hX => ?_⟩
  obtain ⟨pA, hpA⟩ := cc_tile_nonempty A
  obtain ⟨pX, hpX⟩ := cc_tile_nonempty X
  have hbdd : Bornology.IsBounded (support S) :=
    (hS.isCompact_biUnion fun Y _ => cc_tile_compact Y).isBounded
  have hmemS : ∀ {Y p}, Y ∈ S → p ∈ Y.carrier → p ∈ support S := fun hY hp =>
    mem_biUnion hY hp
  have hd : dist pX pA ≤ D :=
    (Metric.dist_le_diam_of_mem hbdd (hmemS hX hpX) (hmemS hA hpA)).trans hD
  obtain ⟨hfin, hcard⟩ := hN T.tiles T.disjoint pA
  have hAM : A ∈ {Y ∈ T.tiles | (Y.carrier ∩ Metric.ball pA (max D 0 + 1)).Nonempty} :=
    ⟨hST hA, pA, hpA, Metric.mem_ball_self (by positivity)⟩
  have hXM : X ∈ {Y ∈ T.tiles | (Y.carrier ∩ Metric.ball pA (max D 0 + 1)).Nonempty} := by
    refine ⟨hST hX, pX, hpX, ?_⟩
    rw [Metric.mem_ball]
    have := le_max_left D 0
    linarith
  obtain ⟨m, hm, hch⟩ := cc_conn T hT pA _ hfin hAM hXM
  exact ⟨m, hm.trans hcard, hch⟩

/-- In an STS plane tiling every tile has a side-neighbour. -/
private lemma cc_has_neighbour (T : PlaneTiling P) (hT : T.SideToSide) {A : PlacedTile P}
    (hA : A ∈ T.tiles) : ∃ B ∈ T.tiles, ccSAdj A B := by
  obtain ⟨pA, hpA⟩ := cc_tile_nonempty A
  have hy : ∃ y, y ∉ A.carrier := by
    by_contra h
    push_neg at h
    have : Bornology.IsBounded (univ : Set Pt) :=
      (cc_tile_compact A).isBounded.subset fun y _ => h y
    exact (NormedSpace.unbounded_univ ℝ Pt) this
  obtain ⟨y, hyA⟩ := hy
  have : y ∈ support T.tiles := by rw [T.cover]; trivial
  simp only [support, mem_iUnion, exists_prop] at this
  obtain ⟨X, hXT, hyX⟩ := this
  have hXA : X ≠ A := by rintro rfl; exact hyA hyX
  set R := dist y pA + 1
  obtain ⟨N, hN⟩ := cc_count P R
  obtain ⟨hfin, -⟩ := hN T.tiles T.disjoint pA
  have hAM : A ∈ {Y ∈ T.tiles | (Y.carrier ∩ Metric.ball pA R).Nonempty} :=
    ⟨hA, pA, hpA, Metric.mem_ball_self (by positivity)⟩
  have hXM : X ∈ {Y ∈ T.tiles | (Y.carrier ∩ Metric.ball pA R).Nonempty} :=
    ⟨hXT, y, hyX, by rw [Metric.mem_ball]; linarith⟩
  obtain ⟨m, -, f, hf0, hfm, hfS, hfadj⟩ := cc_conn T hT pA R hfin hAM hXM
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; exact absurd (hf0.symm.trans hfm) (Ne.symm hXA)
  · refine ⟨f 1, hfS 1 h, ?_⟩
    have := hfadj 0 h
    rw [hf0] at this
    exact this

/-! ### Combinatorial bookkeeping -/

private lemma cc_bounded_shift {S : Set Pt} {v : Pt} (hb : Bornology.IsBounded S)
    (hne : S.Nonempty) (h : ∀ y ∈ S, y + v ∈ S) : v = 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  have hn : ∀ n : ℕ, x + (n : ℝ) • v ∈ S := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      have := h _ ih
      convert this using 1
      push_cast; rw [add_smul, one_smul, add_assoc]
  by_contra hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨n, hnlt⟩ := exists_nat_gt ((C + ‖x‖) / ‖v‖)
  have h1 := hC _ (hn n)
  have h2 : ‖(n : ℝ) • v‖ ≤ ‖x + (n : ℝ) • v‖ + ‖x‖ := by
    have := norm_sub_le (x + (n : ℝ) • v) x
    simpa using this
  rw [norm_smul, Real.norm_natCast] at h2
  rw [div_lt_iff₀ hvpos] at hnlt
  linarith

private lemma cc_side_eq_vadd (p : P.Form) (a : Pt) (i : Fin (P.disk p).n) :
    (⟨p, a⟩ : PlacedTile P).side i =
      a +ᵥ segment ℝ ((P.disk p).vertex i) ((P.disk p).vertex (finRotate _ i)) := rfl

private lemma cc_vadd_segment_compact (a x y : Pt) : IsCompact (a +ᵥ segment ℝ x y) := by
  rw [← image_vadd]; exact (cc_segment_compact x y).image (continuous_const_vadd a)

private lemma cc_side_inj {p : P.Form} {i : Fin (P.disk p).n} {a b : Pt}
    (h : (⟨p, a⟩ : PlacedTile P).side i = (⟨p, b⟩ : PlacedTile P).side i) : a = b := by
  have hS := cc_vadd_segment_compact a ((P.disk p).vertex i) ((P.disk p).vertex (finRotate _ i))
  rw [cc_side_eq_vadd, cc_side_eq_vadd] at h
  have key : b - a = 0 := by
    refine cc_bounded_shift hS.isBounded ⟨_, vadd_mem_vadd_set (left_mem_segment ℝ _ _)⟩ ?_
    intro y hy
    rw [h, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] at hy
    convert hy using 1; abel
  exact (sub_eq_zero.mp key).symm

open Classical in
/-- A canonical centre of a centrally symmetric set. -/
private def ccCtr (S : Set Pt) : Pt :=
  if h : ∃ z : Pt, ∀ y, y ∈ S ↔ (2 : ℝ) • z - y ∈ S then h.choose else 0

private lemma cc_ctr_eq {S : Set Pt} {z : Pt} (hb : Bornology.IsBounded S) (hne : S.Nonempty)
    (hz : ∀ y, y ∈ S ↔ (2 : ℝ) • z - y ∈ S) : ccCtr S = z := by
  have h : ∃ z : Pt, ∀ y, y ∈ S ↔ (2 : ℝ) • z - y ∈ S := ⟨z, hz⟩
  rw [ccCtr, dif_pos h]
  have hz' := h.choose_spec
  have : (2 : ℝ) • (z - h.choose) = 0 := by
    refine cc_bounded_shift hb hne ?_
    intro y hy
    have h1 := (hz' y).mp hy
    have h2 := (hz _).mp h1
    convert h2 using 1
    rw [smul_sub]; abel
  rw [smul_eq_zero] at this
  rcases this with h2 | h2
  · norm_num at h2
  · exact (sub_eq_zero.mp h2).symm

private lemma cc_segment_symm {u w y : Pt} (hy : y ∈ segment ℝ u w) : u + w - y ∈ segment ℝ u w := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  refine ⟨b, a, hb, ha, by linarith, ?_⟩
  have e1 : u = (a + b) • u := by rw [hab, one_smul]
  have e2 : w = (a + b) • w := by rw [hab, one_smul]
  calc b • u + a • w = (a + b) • u + (a + b) • w - (a • u + b • w) := by
        rw [add_smul, add_smul]; abel
    _ = u + w - (a • u + b • w) := by rw [← e1, ← e2]

private lemma cc_ctr_vadd_segment (c u w : Pt) :
    ccCtr (c +ᵥ segment ℝ u w) = c + (1 / 2 : ℝ) • (u + w) := by
  apply cc_ctr_eq (cc_vadd_segment_compact c u w).isBounded
    ⟨_, vadd_mem_vadd_set (left_mem_segment ℝ _ _)⟩
  intro y
  rw [mem_vadd_set_iff_neg_vadd_mem, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, vadd_eq_add]
  have e : -c + ((2 : ℝ) • (c + (1 / 2 : ℝ) • (u + w)) - y) = u + w - (-c + y) := by
    have e2 : (2 : ℝ) • (c + (1 / 2 : ℝ) • (u + w)) = (2 : ℝ) • c + (u + w) := by
      rw [smul_add, smul_smul]; norm_num
    rw [e2, two_smul]; abel
  rw [e]
  constructor
  · exact cc_segment_symm
  · intro h
    have := cc_segment_symm h
    simpa using this

private lemma cc_ctr_side (p : P.Form) (a : Pt) (i : Fin (P.disk p).n) :
    ccCtr ((⟨p, a⟩ : PlacedTile P).side i) = a + ccCtr ((⟨p, 0⟩ : PlacedTile P).side i) := by
  rw [cc_side_eq_vadd, cc_side_eq_vadd, cc_ctr_vadd_segment, cc_ctr_vadd_segment, zero_add]

/-! translations of placed tiles -/

private lemma cc_translate_translate (X : PlacedTile P) (v w : Pt) :
    (X.translate v).translate w = X.translate (w + v) :=
  PlacedTile.ext rfl (by simp [PlacedTile.translate, add_assoc])

private lemma cc_translate_zero (X : PlacedTile P) : X.translate 0 = X :=
  PlacedTile.ext rfl (by simp [PlacedTile.translate])

private lemma cc_translateSet_translateSet (S : Set (PlacedTile P)) (v w : Pt) :
    translateSet w (translateSet v S) = translateSet (w + v) S := by
  simp only [translateSet, image_image, cc_translate_translate]

private lemma cc_translateSet_zero (S : Set (PlacedTile P)) : translateSet 0 S = S := by
  simp [translateSet, cc_translate_zero]

private lemma cc_mem_translateSet {S : Set (PlacedTile P)} {v : Pt} {X : PlacedTile P} :
    X ∈ translateSet v S ↔ X.translate (-v) ∈ S := by
  constructor
  · rintro ⟨Y, hY, rfl⟩
    rwa [cc_translate_translate, neg_add_cancel, cc_translate_zero]
  · intro h
    refine ⟨_, h, ?_⟩
    show (X.translate (-v)).translate v = X
    rw [cc_translate_translate, add_neg_cancel, cc_translate_zero]

private lemma cc_translate_mem {S : Set (PlacedTile P)} {X : PlacedTile P} (v : Pt) (h : X ∈ S) :
    X.translate v ∈ translateSet v S := mem_image_of_mem _ h

private lemma cc_translateSet_mono {S S' : Set (PlacedTile P)} (v : Pt) (h : S ⊆ S') :
    translateSet v S ⊆ translateSet v S' := image_mono h

private lemma cc_side_translate (X : PlacedTile P) (v : Pt) (i : Fin (P.disk X.form).n) :
    (X.translate v).side i = v +ᵥ X.side i := by
  show (v +ᵥ X.anchor) +ᵥ _ = v +ᵥ (X.anchor +ᵥ _)
  rw [vadd_vadd]; rfl

private lemma cc_sadj_translate {X Y : PlacedTile P} (v : Pt) (h : ccSAdj X Y) :
    ccSAdj (X.translate v) (Y.translate v) := by
  obtain ⟨hne, i, j, hij⟩ := h
  refine ⟨fun h' => hne ?_, i, j, ?_⟩
  · have := congrArg (fun Z : PlacedTile P => Z.translate (-v)) h'
    simpa only [cc_translate_translate, neg_add_cancel, cc_translate_zero] using this
  · rw [cc_side_translate, cc_side_translate, hij]

private lemma cc_projTile_carrier (dec : Decoration P) (Y : PlacedTile dec.P') :
    (dec.projTile Y).carrier = Y.carrier := by
  simp only [PlacedTile.carrier, Decoration.projTile, dec.carrier_eq]

/-- Side adjacency of decorated tiles, read on their projections. -/
private def ccAdj (dec : Decoration P) (Y Z : PlacedTile dec.P') : Prop :=
  ccSAdj (dec.projTile Y) (dec.projTile Z)

/-! chains -/

private lemma cc_chain_mono {α : Type*} {adj : α → α → Prop} {S S' : Set α} {m : ℕ} {x y : α}
    (h : S ⊆ S') (hc : ccChain adj S m x y) : ccChain adj S' m x y := by
  obtain ⟨f, h0, hm, hS, ha⟩ := hc
  exact ⟨f, h0, hm, fun t ht => h (hS t ht), ha⟩

private lemma cc_chain_cons {α : Type*} {adj : α → α → Prop} {S : Set α} {m : ℕ} {x y z : α}
    (hx : x ∈ S) (hxy : adj x y) (hc : ccChain adj S m y z) : ccChain adj S (m + 1) x z := by
  obtain ⟨f, h0, hm, hS, ha⟩ := hc
  refine ⟨fun t => if t = 0 then x else f (t - 1), by simp, by simpa using hm, ?_, ?_⟩
  · intro t ht
    by_cases h : t = 0
    · simp [h, hx]
    · simp only [h, if_false]; exact hS _ (by omega)
  · intro t ht
    by_cases h : t = 0
    · subst h; simp only [if_true, add_eq_zero, one_ne_zero, and_false, if_false]
      rw [Nat.add_sub_cancel, h0]; exact hxy
    · simp only [h, if_false, add_eq_zero, one_ne_zero, and_false]
      have := ha (t - 1) (by omega)
      rwa [Nat.sub_add_cancel (by omega)] at this

private lemma cc_chain_translate (dec : Decoration P) {S : Set (PlacedTile dec.P')} {m : ℕ}
    {Y Z : PlacedTile dec.P'} (v : Pt) (hc : ccChain (ccAdj dec) S m Y Z) :
    ccChain (ccAdj dec) (translateSet v S) m (Y.translate v) (Z.translate v) := by
  obtain ⟨f, h0, hm, hS, ha⟩ := hc
  refine ⟨fun t => (f t).translate v, by simp [h0], by simp [hm],
    fun t ht => cc_translate_mem v (hS t ht), fun t ht => ?_⟩
  exact cc_sadj_translate (P := P) v (ha t ht)

/-- The part of a state seen from a side `σ`: tiles within `K` steps of a tile carrying `σ`. -/
private def ccW (dec : Decoration P) (K : ℕ) (S : Set (PlacedTile dec.P')) (σ : Set Pt) :
    Set (PlacedTile dec.P') :=
  {Y ∈ S | ∃ Z ∈ S, (∃ j, (dec.projTile Z).side j = σ) ∧ ∃ m ≤ K, ccChain (ccAdj dec) S m Z Y}

private lemma cc_W_translate_sub (dec : Decoration P) (K : ℕ) (S : Set (PlacedTile dec.P'))
    (σ : Set Pt) (v : Pt) : translateSet v (ccW dec K S σ) ⊆ ccW dec K (translateSet v S) (v +ᵥ σ) := by
  rintro _ ⟨Y, ⟨hY, Z, hZ, ⟨j, hj⟩, m, hm, hc⟩, rfl⟩
  refine ⟨cc_translate_mem v hY, Z.translate v, cc_translate_mem v hZ, ⟨j, ?_⟩, m, hm,
    cc_chain_translate dec v hc⟩
  show ((dec.projTile Z).translate v).side j = v +ᵥ σ
  rw [cc_side_translate, hj]

private lemma cc_W_translate (dec : Decoration P) (K : ℕ) (S : Set (PlacedTile dec.P'))
    (σ : Set Pt) (v : Pt) : translateSet v (ccW dec K S σ) = ccW dec K (translateSet v S) (v +ᵥ σ) := by
  refine (cc_W_translate_sub dec K S σ v).antisymm ?_
  have h := cc_translateSet_mono v (cc_W_translate_sub dec K (translateSet v S) (v +ᵥ σ) (-v))
  simpa only [cc_translateSet_translateSet, add_neg_cancel, neg_add_cancel, cc_translateSet_zero,
    vadd_vadd, zero_vadd] using h

/-! offsets and the finite universe of relative placements -/

/-- Relative anchors of side-neighbours. -/
private def ccOff (P : Protoset) : Set Pt :=
  {v | ∃ (q q' : P.Form) (i : Fin (P.disk q).n) (j : Fin (P.disk q').n),
    (⟨q, 0⟩ : PlacedTile P).side i = (⟨q', v⟩ : PlacedTile P).side j}

private lemma cc_off_finite (P : Protoset) : (ccOff P).Finite := by
  refine Set.Finite.subset (Set.finite_iUnion fun q : P.Form => Set.finite_iUnion fun q' : P.Form =>
    Set.finite_iUnion fun i : Fin (P.disk q).n => Set.finite_iUnion fun j : Fin (P.disk q').n =>
      (?_ : Set.Subsingleton {v : Pt | (⟨q, 0⟩ : PlacedTile P).side i =
        (⟨q', v⟩ : PlacedTile P).side j}).finite) ?_
  · intro v hv v' hv'
    simp only [mem_setOf_eq] at hv hv'
    exact cc_side_inj (hv.symm.trans hv')
  · rintro v ⟨q, q', i, j, h⟩
    simp only [mem_iUnion, mem_setOf_eq]
    exact ⟨q, q', i, j, h⟩

private lemma cc_sadj_off {X Y : PlacedTile P} (h : ccSAdj X Y) : Y.anchor - X.anchor ∈ ccOff P := by
  obtain ⟨-, i, j, hij⟩ := h
  refine ⟨X.form, Y.form, i, j, ?_⟩
  have := congrArg (fun s : Set Pt => -X.anchor +ᵥ s) hij
  simp only [PlacedTile.side, vadd_vadd, neg_add_cancel] at this
  simp only [PlacedTile.side]
  rw [this, sub_eq_neg_add]

/-- Relative anchors reachable in at most `k` steps. -/
private def ccLam (P : Protoset) : ℕ → Set Pt
  | 0 => {0}
  | k + 1 => ccLam P k ∪ (ccLam P k + ccOff P)

private lemma cc_lam_finite (P : Protoset) (k : ℕ) : (ccLam P k).Finite := by
  induction k with
  | zero => exact Set.finite_singleton 0
  | succ k ih => exact ih.union (ih.add (cc_off_finite P))

private lemma cc_lam_mono (P : Protoset) {k l : ℕ} (h : k ≤ l) : ccLam P k ⊆ ccLam P l := by
  induction l, h using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih => exact ih.trans subset_union_left

private lemma cc_chain_lam (dec : Decoration P) {S : Set (PlacedTile dec.P')} {m : ℕ}
    {Y Z : PlacedTile dec.P'} (hc : ccChain (ccAdj dec) S m Y Z) : Z.anchor - Y.anchor ∈ ccLam P m := by
  obtain ⟨f, h0, hm, -, ha⟩ := hc
  have key : ∀ t ≤ m, (f t).anchor - Y.anchor ∈ ccLam P t := by
    intro t
    induction t with
    | zero => intro _; rw [h0, sub_self]; exact rfl
    | succ t ih =>
      intro ht
      right
      have h1 := ih (by omega)
      have h2 := cc_sadj_off (ha t (by omega))
      have e : (f (t + 1)).anchor - Y.anchor =
          ((f t).anchor - Y.anchor) + ((f (t + 1)).anchor - (f t).anchor) := by abel
      rw [e]
      exact Set.add_mem_add h1 h2
  rw [← hm]; exact key m le_rfl

/-- The finite universe of relative decorated placements. -/
private def ccU (dec : Decoration P) (k : ℕ) : Set (PlacedTile dec.P') := {Y | Y.anchor ∈ ccLam P k}

private lemma cc_U_finite (dec : Decoration P) (k : ℕ) : (ccU dec k).Finite := by
  refine ((Set.finite_univ.prod (cc_lam_finite P k)).image
    (fun pr : dec.P'.Form × Pt => (⟨pr.1, pr.2⟩ : PlacedTile dec.P'))).subset ?_
  intro Y hY
  exact ⟨(Y.form, Y.anchor), ⟨trivial, hY⟩, rfl⟩

/-! ### The collar side decoration -/

/-- States: original form, old decoration, and a finite relative collar. -/
private def ccSt (dec : Decoration P) (k : ℕ) : Type := P.Form × dec.P'.Form × Set ↥(ccU dec k)

private def ccSet {dec : Decoration P} {k : ℕ} (x : ccSt dec k) : Set (PlacedTile dec.P') :=
  Subtype.val '' x.2.2

private def ccValid (dec : Decoration P) (R : LocalRule dec.P') {k : ℕ} (x : ccSt dec k) : Prop :=
  dec.proj x.2.1 = x.1 ∧ (⟨x.2.1, 0⟩ : PlacedTile dec.P') ∈ ccSet x ∧
    ∀ F ∈ R.forbidden, ¬ OccursIn F (ccSet x)

private def ccDom (dec : Decoration P) (k : ℕ) : Type := Σ x : ccSt dec k, Fin (P.disk x.1).n

open Classical in
private def ccCol0 (dec : Decoration P) (R : LocalRule dec.P') (K : ℕ) (x : ccSt dec (K + 1))
    (i : Fin (P.disk x.1).n) : ccDom dec (K + 1) ⊕ Set (PlacedTile dec.P') :=
  if ccValid dec R x then
    Sum.inr (translateSet (-ccCtr ((⟨x.1, 0⟩ : PlacedTile P).side i))
      (ccW dec K (ccSet x) ((⟨x.1, 0⟩ : PlacedTile P).side i)))
  else Sum.inl ⟨x, i⟩

private lemma cc_st_finite (dec : Decoration P) (k : ℕ) : Finite (ccSt dec k) := by
  haveI : Finite ↥(ccU dec k) := (cc_U_finite dec k).to_subtype
  unfold ccSt; infer_instance

private def ccProto (dec : Decoration P) (k : ℕ) : Protoset where
  Form := ccSt dec k
  fintype := by haveI := cc_st_finite dec k; exact Fintype.ofFinite _
  decEq := Classical.decEq _
  disk := fun x => P.disk x.1

private def ccSideDec (dec : Decoration P) (R : LocalRule dec.P') (K : ℕ) : SideDecoration P where
  P' := ccProto dec (K + 1)
  proj := fun x => x.1
  surj := fun p => ⟨(p, (dec.surj p).choose, ∅), rfl⟩
  carrier_eq := fun _ => rfl
  disk_eq := fun _ => rfl
  Colour := Set.range (fun y : ccDom dec (K + 1) => ccCol0 dec R K y.1 y.2)
  colourFintype := by
    haveI := cc_st_finite dec (K + 1)
    haveI : Finite (ccDom dec (K + 1)) := by unfold ccDom; infer_instance
    exact Fintype.ofFinite _
  colour := fun x i => ⟨ccCol0 dec R K x i, ⟨⟨x, i⟩, rfl⟩⟩

private lemma cc_side_zero (p : P.Form) (a : Pt) (i : Fin (P.disk p).n) :
    (⟨p, a⟩ : PlacedTile P).side i = a +ᵥ (⟨p, 0⟩ : PlacedTile P).side i := by
  rw [cc_side_eq_vadd, cc_side_eq_vadd, zero_vadd]

private lemma cc_col_abs (dec : Decoration P) (R : LocalRule dec.P') (K : ℕ) {x : ccSt dec (K + 1)}
    (hx : ccValid dec R x) (a : Pt) (i : Fin (P.disk x.1).n) :
    ccCol0 dec R K x i = Sum.inr (translateSet (-ccCtr ((⟨x.1, a⟩ : PlacedTile P).side i))
      (ccW dec K (translateSet a (ccSet x)) ((⟨x.1, a⟩ : PlacedTile P).side i))) := by
  rw [ccCol0, if_pos hx, cc_ctr_side x.1 a i, cc_side_zero x.1 a i, ← cc_W_translate,
    cc_translateSet_translateSet]
  congr 2; abel

private lemma cc_translateSet_inj {S S' : Set (PlacedTile P)} {v : Pt}
    (h : translateSet v S = translateSet v S') : S = S' := by
  have := congrArg (translateSet (-v)) h
  simpa only [cc_translateSet_translateSet, neg_add_cancel, cc_translateSet_zero] using this

private lemma cc_proj_injOn (dec : Decoration P) {S : Set (PlacedTile dec.P')}
    (hS : DisjointInteriors S) : Set.InjOn dec.projTile S := by
  intro X hX Y hY hXY
  by_contra hne
  have hc : X.carrier = Y.carrier := by
    rw [← cc_projTile_carrier dec X, ← cc_projTile_carrier dec Y, hXY]
  have hd := hS hX hY hne
  simp only [Function.onFun] at hd
  rw [hc, disjoint_self] at hd
  obtain ⟨z, hz⟩ := (P.disk (dec.projTile Y).form).interior_nonempty
  have hne' : (interior Y.carrier).Nonempty := by
    rw [← cc_projTile_carrier dec Y]
    refine ⟨(dec.projTile Y).anchor +ᵥ z, ?_⟩
    unfold PlacedTile.carrier
    rw [interior_vadd]; exact vadd_mem_vadd_set hz
  rw [hd] at hne'
  simp at hne'

private lemma cc_planeTiling_ext {T₁ T₂ : PlaneTiling P} (h : T₁.tiles = T₂.tiles) : T₁ = T₂ := by
  cases T₁; cases T₂; cases h; rfl

private lemma cc_chain_zero {α : Type*} {adj : α → α → Prop} {S : Set α} {x : α} (hx : x ∈ S) :
    ccChain adj S 0 x x :=
  ⟨fun _ => x, rfl, rfl, fun _ _ => hx, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- Completeness: every projection of a proper old tiling which is STS lifts to a proper
tiling of the collar side decoration. -/
private lemma cc_complete (dec : Decoration P) (R : LocalRule dec.P') (K : ℕ) (T : PlaneTiling P)
    (hT : T.SideToSide) (T₀ : PlaneTiling dec.P') (hR : R.Proper T₀) (hproj : dec.project T₀ = T) :
    ∃ T' : PlaneTiling (ccSideDec dec R K).P', (ccSideDec dec R K).Proper T' ∧
      (ccSideDec dec R K).toDecoration.project T' = T := by
  classical
  haveI : Nonempty (PlacedTile dec.P') := by
    have : (0 : Pt) ∈ support T₀.tiles := by rw [T₀.cover]; trivial
    simp only [support, mem_iUnion, exists_prop] at this
    obtain ⟨Y, -, -⟩ := this
    exact ⟨Y⟩
  have hinj := cc_proj_injOn dec T₀.disjoint
  have hT_eq : T.tiles = dec.projTile '' T₀.tiles := by rw [← hproj]; rfl
  set g : PlacedTile P → PlacedTile dec.P' := Function.invFunOn dec.projTile T₀.tiles with hgdef
  have hg : ∀ A ∈ T.tiles, g A ∈ T₀.tiles ∧ dec.projTile (g A) = A := by
    intro A hA
    rw [hT_eq] at hA
    exact ⟨Function.invFunOn_mem hA, Function.invFunOn_eq hA⟩
  have hganchor : ∀ A ∈ T.tiles, (g A).anchor = A.anchor := fun A hA =>
    congrArg PlacedTile.anchor (hg A hA).2
  set SA : PlacedTile P → Set (PlacedTile dec.P') := fun A =>
    {Y ∈ T₀.tiles | ∃ m ≤ K + 1, ccChain (ccAdj dec) T₀.tiles m (g A) Y} with hSA
  set st : PlacedTile P → ccSt dec (K + 1) := fun A =>
    (A.form, (g A).form, {u | u.val ∈ translateSet (-A.anchor) (SA A)}) with hst
  have hSA_U : ∀ A ∈ T.tiles, translateSet (-A.anchor) (SA A) ⊆ ccU dec (K + 1) := by
    intro A hA Y' hY'
    rw [cc_mem_translateSet, neg_neg] at hY'
    obtain ⟨-, m, hm, hc⟩ := hY'
    have h1 := cc_lam_mono P hm (cc_chain_lam dec hc)
    rw [hganchor A hA] at h1
    show Y'.anchor ∈ ccLam P (K + 1)
    convert h1 using 1
    simp only [PlacedTile.translate, vadd_eq_add]; abel
  have hset : ∀ A ∈ T.tiles, ccSet (st A) = translateSet (-A.anchor) (SA A) := by
    intro A hA
    ext Y; constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro h; exact ⟨⟨Y, hSA_U A hA h⟩, h, rfl⟩
  have hset' : ∀ A ∈ T.tiles, translateSet A.anchor (ccSet (st A)) = SA A := by
    intro A hA
    rw [hset A hA, cc_translateSet_translateSet, add_neg_cancel, cc_translateSet_zero]
  have hgSA : ∀ A ∈ T.tiles, g A ∈ SA A := fun A hA =>
    ⟨(hg A hA).1, 0, Nat.zero_le _, cc_chain_zero (hg A hA).1⟩
  have hvalid : ∀ A ∈ T.tiles, ccValid dec R (st A) := by
    intro A hA
    refine ⟨congrArg PlacedTile.form (hg A hA).2, ?_, ?_⟩
    · rw [hset A hA, cc_mem_translateSet, neg_neg]
      convert hgSA A hA using 1
      exact PlacedTile.ext rfl (by simp [PlacedTile.translate, hganchor A hA])
    · rintro F hF ⟨w, hw⟩
      apply hR F hF
      refine ⟨A.anchor + w, ?_⟩
      have := cc_translateSet_mono A.anchor hw
      rw [hset' A hA, cc_translateSet_translateSet] at this
      exact this.trans fun Y hY => hY.1
  -- the side-visible part of a state is intrinsic to the tiling
  have hW : ∀ A ∈ T.tiles, ∀ i : Fin (P.disk A.form).n,
      ccW dec K (SA A) (A.side i) = {Y ∈ T₀.tiles | ∃ Z ∈ T₀.tiles,
        (∃ j, (dec.projTile Z).side j = A.side i) ∧ ∃ m ≤ K, ccChain (ccAdj dec) T₀.tiles m Z Y} := by
    intro A hA i
    ext Y; constructor
    · rintro ⟨hY, Z, hZ, hj, m, hm, hc⟩
      exact ⟨hY.1, Z, hZ.1, hj, m, hm, cc_chain_mono (fun _ h => h.1) hc⟩
    · rintro ⟨hY, Z, hZ, ⟨k, hk⟩, m, hm, f, hf0, hfm, hfS, hfa⟩
      have hreach : ∀ t ≤ m, f t ∈ SA A := by
        intro t ht
        have hpre : ccChain (ccAdj dec) T₀.tiles t Z (f t) :=
          ⟨f, hf0, rfl, fun s hs => hfS s (by omega), fun s hs => hfa s (by omega)⟩
        refine ⟨hfS t ht, ?_⟩
        by_cases hz : dec.projTile Z = A
        · have hZg : Z = g A := hinj hZ (hg A hA).1 (hz.trans (hg A hA).2.symm)
          rw [hZg] at hpre
          exact ⟨t, by omega, hpre⟩
        · refine ⟨t + 1, by omega, cc_chain_cons (hg A hA).1 ?_ hpre⟩
          refine ⟨fun h => hz (h.symm.trans (hg A hA).2), ?_⟩
          obtain ⟨i', hi'⟩ : ∃ i', (dec.projTile (g A)).side i' = A.side i := by
            rw [(hg A hA).2]; exact ⟨i, rfl⟩
          exact ⟨i', k, hi'.trans hk.symm⟩
      refine ⟨hfm ▸ hreach m le_rfl, Z, hf0 ▸ hreach 0 (Nat.zero_le _), ⟨k, hk⟩, m, hm,
        f, hf0, hfm, hreach, hfa⟩
  set lift : PlacedTile P → PlacedTile (ccSideDec dec R K).P' := fun A => ⟨st A, A.anchor⟩
    with hlift
  have hcar : ∀ A, (lift A).carrier = A.carrier := fun A => rfl
  let T' : PlaneTiling (ccSideDec dec R K).P' :=
    { tiles := lift '' T.tiles
      cover := by
        have := T.cover
        simp only [support, biUnion_image, hcar] at this ⊢
        exact this
      disjoint := by
        rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hne
        have hAB : A ≠ B := fun h => hne (h ▸ rfl)
        exact T.disjoint hA hB hAB }
  refine ⟨T', ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ i j h
    exact hT A hA B hB i j h
  · rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hne i j hside
    have hAB : A ≠ B := fun h => hne (h ▸ rfl)
    apply Subtype.ext
    change ccCol0 dec R K (st A) i = ccCol0 dec R K (st B) j
    rw [cc_col_abs dec R K (hvalid A hA) A.anchor i, cc_col_abs dec R K (hvalid B hB) B.anchor j,
      hset' A hA, hset' B hB]
    change Sum.inr (translateSet (-ccCtr (A.side i)) (ccW dec K (SA A) (A.side i))) =
      Sum.inr (translateSet (-ccCtr (B.side j)) (ccW dec K (SA B) (B.side j)))
    have hside' : A.side i = B.side j := hside
    rw [hW A hA i, hW B hB j, hside']
  · apply cc_planeTiling_ext
    show (ccSideDec dec R K).toDecoration.projTile '' (lift '' T.tiles) = T.tiles
    rw [image_image]
    convert image_id T.tiles

private lemma cc_support_translate (S : Set (PlacedTile P)) (v : Pt) :
    support (translateSet v S) = v +ᵥ support S := by
  have hc : ∀ A : PlacedTile P, (A.translate v).carrier = v +ᵥ A.carrier := by
    intro A
    show (v +ᵥ A.anchor) +ᵥ _ = v +ᵥ (A.anchor +ᵥ _)
    rw [vadd_vadd]; rfl
  simp only [support, translateSet, biUnion_image, hc, Set.vadd_set_iUnion₂]

private lemma cc_support_proj (dec : Decoration P) (S : Set (PlacedTile dec.P')) :
    support (dec.projTile '' S) = support S := by
  simp only [support, biUnion_image, cc_projTile_carrier]

/-- Soundness: every proper tiling of the collar side decoration projects to a member of the
original sofic family. -/
private lemma cc_sound (dec : Decoration P) (R : LocalRule dec.P') (K : ℕ)
    (hK : ∀ T : PlaneTiling P, T.SideToSide → ∀ S ⊆ T.tiles, S.Finite →
      Metric.diam (support S) ≤ R.D → ∀ A ∈ S, ∀ X ∈ S, ∃ m ≤ K, ccChain ccSAdj T.tiles m A X)
    (T' : PlaneTiling (ccSideDec dec R K).P') (hT' : (ccSideDec dec R K).Proper T') :
    ∃ T₀ : PlaneTiling dec.P', R.Proper T₀ ∧
      dec.project T₀ = (ccSideDec dec R K).toDecoration.project T' := by
  classical
  set Tp := (ccSideDec dec R K).toDecoration.project T' with hTp
  have hTpSTS : Tp.SideToSide := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ i j h
    exact hT'.1 A hA B hB i j h
  have hT'ne : ∃ A, A ∈ T'.tiles := by
    have : (0 : Pt) ∈ support T'.tiles := by rw [T'.cover]; trivial
    simp only [support, mem_iUnion, exists_prop] at this
    obtain ⟨A, hA, -⟩ := this
    exact ⟨A, hA⟩
  -- every state occurring is valid
  have hvalid : ∀ A ∈ T'.tiles, ccValid dec R A.form := by
    intro A hA
    by_contra hA'
    obtain ⟨_, ⟨B, hB, rfl⟩, hne, i, j, hij⟩ := cc_has_neighbour Tp hTpSTS (mem_image_of_mem _ hA)
    have hAB : A ≠ B := fun h => hne (h ▸ rfl)
    have hc := congrArg Subtype.val (hT'.2 A hA B hB hAB i j hij)
    change ccCol0 dec R K A.form i = ccCol0 dec R K B.form j at hc
    rw [ccCol0, if_neg hA'] at hc
    by_cases hB' : ccValid dec R B.form
    · rw [ccCol0, if_pos hB'] at hc; exact Sum.inl_ne_inr hc
    · rw [ccCol0, if_neg hB'] at hc
      obtain ⟨Af, a⟩ := A
      obtain ⟨Bf, b⟩ := B
      have hc' := Sum.inl_injective hc
      obtain ⟨rfl, hij'⟩ := Sigma.mk.inj_iff.mp hc'
      have hij2 := eq_of_heq hij'
      subst hij2
      have hab : a = b := cc_side_inj (P := P) (p := Af.1) hij
      exact hAB (by rw [hab])
  set g : PlacedTile (ccSideDec dec R K).P' → PlacedTile dec.P' := fun A => ⟨A.form.2.1, A.anchor⟩ with hg
  have hgcar : ∀ A ∈ T'.tiles, (g A).carrier = A.carrier := by
    intro A hA
    show A.anchor +ᵥ (dec.P'.disk A.form.2.1).carrier = A.anchor +ᵥ (P.disk A.form.1).carrier
    rw [dec.carrier_eq, (hvalid A hA).1]
  have hgproj : ∀ A ∈ T'.tiles, dec.projTile (g A) = (ccSideDec dec R K).toDecoration.projTile A := fun A hA =>
    PlacedTile.ext (hvalid A hA).1 rfl
  let T₀ : PlaneTiling dec.P' :=
    { tiles := g '' T'.tiles
      cover := by
        apply eq_univ_of_forall; intro y
        have : y ∈ support T'.tiles := by rw [T'.cover]; trivial
        simp only [support, mem_iUnion, exists_prop] at this ⊢
        obtain ⟨A, hA, hy⟩ := this
        exact ⟨g A, mem_image_of_mem g hA, by rw [hgcar A hA]; exact hy⟩
      disjoint := by
        rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hne
        have hAB : A ≠ B := fun h => hne (h ▸ rfl)
        have := T'.disjoint hA hB hAB
        simp only [Function.onFun] at this ⊢
        rwa [hgcar A hA, hgcar B hB] }
  have hT₀ : T₀.tiles = g '' T'.tiles := rfl
  have hTp0 : Tp.tiles = dec.projTile '' T₀.tiles := by
    rw [hT₀, image_image]
    exact (Set.image_congr fun A hA => hgproj A hA).symm
  have hinj := cc_proj_injOn dec T₀.disjoint
  refine ⟨T₀, ?_, cc_planeTiling_ext hTp0.symm⟩
  -- the main propagation claim
  have hclaim : ∀ m ≤ K, ∀ A ∈ T'.tiles, ∀ X, ccChain (ccAdj dec) T₀.tiles m (g A) X →
      X ∈ translateSet A.anchor (ccSet A.form) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hm A hA X hc
    rcases m with _ | m
    · obtain ⟨f, h0, hm0, -, -⟩ := hc
      rw [← hm0, h0]
      convert cc_translate_mem A.anchor (hvalid A hA).2.1 using 1
      exact PlacedTile.ext rfl (by simp [PlacedTile.translate, hg])
    · obtain ⟨f, h0, hfm, hfS, hfa⟩ := hc
      obtain ⟨B, hB, hgB⟩ := hfS 1 (by omega)
      have hadj := hfa 0 (by omega)
      rw [h0, ← hgB] at hadj
      unfold ccAdj at hadj
      rw [hgproj A hA, hgproj B hB] at hadj
      obtain ⟨hne, i, j, hij⟩ := hadj
      have hAB : A ≠ B := fun h => hne (h ▸ rfl)
      have hc := congrArg Subtype.val (hT'.2 A hA B hB hAB i j hij)
      change ccCol0 dec R K A.form i = ccCol0 dec R K B.form j at hc
      rw [cc_col_abs dec R K (hvalid A hA) A.anchor i,
        cc_col_abs dec R K (hvalid B hB) B.anchor j] at hc
      have hc2 := Sum.inr_injective hc
      have hσ : (⟨A.form.1, A.anchor⟩ : PlacedTile P).side i =
          (⟨B.form.1, B.anchor⟩ : PlacedTile P).side j := hij
      rw [← hσ] at hc2
      have hWeq := cc_translateSet_inj hc2
      have htail : ∀ t ≤ m, f (t + 1) ∈ translateSet B.anchor (ccSet B.form) := by
        intro t ht
        refine ih t (by omega) (by omega) B hB (f (t + 1)) ⟨fun s => f (s + 1), ?_, rfl,
          fun s hs => hfS (s + 1) (by omega), fun s hs => hfa (s + 1) (by omega)⟩
        simp only [zero_add]; exact hgB.symm
      have hX : X ∈ ccW dec K (translateSet B.anchor (ccSet B.form))
          ((⟨A.form.1, A.anchor⟩ : PlacedTile P).side i) := by
        refine ⟨hfm ▸ htail m le_rfl, g B, hgB ▸ htail 0 (Nat.zero_le _), ?_, m, by omega,
          fun s => f (s + 1), by simp only [zero_add]; exact hgB.symm, hfm, htail,
          fun s hs => hfa (s + 1) (by omega)⟩
        rw [hgproj B hB]
        exact ⟨j, hij.symm⟩
      rw [← hWeq] at hX
      exact hX.1
  -- no forbidden patch occurs
  intro F hF ⟨v, hv⟩
  by_cases hFe : F = ∅
  · obtain ⟨A, hA⟩ := hT'ne
    exact (hvalid A hA).2.2 F hF ⟨0, by rw [hFe]; simp [translateSet]⟩
  obtain ⟨Y₀, hY₀⟩ := Set.nonempty_iff_ne_empty.mpr hFe
  haveI : Nonempty (PlacedTile dec.P') := ⟨Y₀⟩
  obtain ⟨A, hA, hgA⟩ := hv (mem_image_of_mem (fun Y => Y.translate v) hY₀)
  have hsub : translateSet v F ⊆ translateSet A.anchor (ccSet A.form) := by
    intro X hX
    have hXT := hv hX
    set S := dec.projTile '' translateSet v F with hS
    have hSsub : S ⊆ Tp.tiles := by rw [hTp0]; exact image_mono hv
    have hSfin : S.Finite := (((R.bounded F hF).1).image _).image _
    have hSdiam : Metric.diam (support S) ≤ R.D := by
      rw [hS, cc_support_proj, cc_support_translate, diam_vadd]
      exact (R.bounded F hF).2
    obtain ⟨m, hm, f, hf0, hfm, hfS, hfa⟩ := hK Tp hTpSTS S hSsub hSfin hSdiam
      (dec.projTile (Y₀.translate v)) (mem_image_of_mem _ (mem_image_of_mem _ hY₀))
      (dec.projTile X) (mem_image_of_mem _ hX)
    set f' := fun t => Function.invFunOn dec.projTile T₀.tiles (f t) with hf'
    have hf'mem : ∀ t ≤ m, f' t ∈ T₀.tiles ∧ dec.projTile (f' t) = f t := by
      intro t ht
      have := hfS t ht
      rw [hTp0] at this
      exact ⟨Function.invFunOn_mem this, Function.invFunOn_eq this⟩
    have hc : ccChain (ccAdj dec) T₀.tiles m (g A) X := by
      refine ⟨f', ?_, ?_, fun t ht => (hf'mem t ht).1, fun t ht => ?_⟩
      · rw [hgA]
        exact hinj (hf'mem 0 (Nat.zero_le _)).1 (hv (mem_image_of_mem _ hY₀))
          ((hf'mem 0 (Nat.zero_le _)).2.trans hf0)
      · exact hinj (hf'mem m le_rfl).1 hXT ((hf'mem m le_rfl).2.trans hfm)
      · have h1 := (hf'mem t ht.le).2
        have h2 := (hf'mem (t + 1) ht).2
        have := hfa t ht
        rw [← h1, ← h2] at this
        exact this
    exact hclaim m hm A hA X hc
  apply (hvalid A hA).2.2 F hF
  refine ⟨-A.anchor + v, ?_⟩
  have := cc_translateSet_mono (-A.anchor) hsub
  simpa only [cc_translateSet_translateSet, neg_add_cancel, cc_translateSet_zero] using this

/-- `lem:collar-conversion`: a sofic family consisting entirely of
side-to-side plane tilings is side-to-side sofic on the original listed
sides. -/
theorem LocalRule.side_presentation_of_sts_sofic {F : Set (PlaneTiling P)} (hF : IsSofic F)
    (hsts : ∀ T ∈ F, T.SideToSide) : IsSideToSideSofic F := by
  obtain ⟨dec, R, hiff⟩ := hF
  obtain ⟨K, hK⟩ := cc_geo_bound P R.D
  refine ⟨ccSideDec dec R K, fun T => ⟨fun hT => ?_, ?_⟩⟩
  · obtain ⟨T₀, hR, hp⟩ := (hiff T).mp hT
    exact cc_complete dec R K T (hsts T hT) T₀ hR hp
  · rintro ⟨T', hP, rfl⟩
    exact (hiff _).mpr (cc_sound dec R K hK T' hP)

/-! ## Dissection and glue colours (`lem:glues`) -/

/-- The family of scatterings of a family of grouped plane tilings. -/
def Geometry.GroupedFamily.scatterFamily (G : GroupedFamily P) (F' : Set (PlaneTiling G.P')) :
    Set (PlaneTiling P) :=
  {T | ∃ T' ∈ F', G.scatter T'.tiles = T.tiles}

/-! ### Finite constituent tags for `dissection_preserves_sofic` -/

private noncomputable def dissection_preserves_sofic_children (G : GroupedFamily P)
    (dec : Decoration G.P') (q : dec.P'.Form) : Finset (PlacedTile P) :=
  (G.dissect (dec.proj q)).finite.toFinset

private abbrev dissection_preserves_sofic_Active (G : GroupedFamily P)
    (dec : Decoration G.P') :=
  Σ q : dec.P'.Form, {B // B ∈ dissection_preserves_sofic_children G dec q}

private abbrev dissection_preserves_sofic_Form (G : GroupedFamily P)
    (dec : Decoration G.P') :=
  P.Form ⊕ dissection_preserves_sofic_Active G dec

/-- The active forms remember a decorated macro-form and one constituent position.
The left summand supplies inert forms, making the projection surjective. -/
private noncomputable def dissection_preserves_sofic_dec (G : GroupedFamily P)
    (dec : Decoration G.P') : Decoration P where
  P' :=
    { Form := dissection_preserves_sofic_Form G dec
      fintype := Fintype.ofFinite _
      decEq := Classical.decEq _
      disk := fun
        | .inl p => P.disk p
        | .inr a => P.disk a.2.1.form }
  proj := fun
    | .inl p => p
    | .inr a => a.2.1.form
  surj := fun p => ⟨.inl p, rfl⟩
  carrier_eq := fun
    | .inl _ => rfl
    | .inr _ => rfl

private def dissection_preserves_sofic_parent (G : GroupedFamily P)
    (dec : Decoration G.P')
    (X : PlacedTile (dissection_preserves_sofic_dec G dec).P') :
    Option (PlacedTile dec.P') :=
  match X.form with
  | .inl _ => none
  | .inr a => some ⟨a.1, X.anchor - a.2.1.anchor⟩

private def dissection_preserves_sofic_liftTile (G : GroupedFamily P)
    (dec : Decoration G.P') (A : PlacedTile dec.P')
    (B : {B // B ∈ dissection_preserves_sofic_children G dec A.form}) :
    PlacedTile (dissection_preserves_sofic_dec G dec).P' :=
  ⟨.inr ⟨A.form, B⟩, A.anchor + B.1.anchor⟩

private def dissection_preserves_sofic_liftSet (G : GroupedFamily P)
    (dec : Decoration G.P') (S : Set (PlacedTile dec.P')) :
    Set (PlacedTile (dissection_preserves_sofic_dec G dec).P') :=
  ⋃ A ∈ S, range (dissection_preserves_sofic_liftTile G dec A)

private def dissection_preserves_sofic_parentSet (G : GroupedFamily P)
    (dec : Decoration G.P')
    (S : Set (PlacedTile (dissection_preserves_sofic_dec G dec).P')) :
    Set (PlacedTile dec.P') :=
  {A | ∃ X ∈ S, dissection_preserves_sofic_parent G dec X = some A}

private def dissection_preserves_sofic_size (G : GroupedFamily P) : ℝ :=
  (∑ p : P.Form, max 0 (Metric.diam (P.disk p).carrier)) +
    ∑ q : G.P'.Form, max 0 (Metric.diam (G.P'.disk q).carrier)

private def dissection_preserves_sofic_badPair (G : GroupedFamily P)
    (dec : Decoration G.P')
    (S : Set (PlacedTile (dissection_preserves_sofic_dec G dec).P')) : Prop :=
  ∃ X ∈ S, ∃ Y ∈ S, ∃ A B,
    dissection_preserves_sofic_parent G dec X = some A ∧
      dissection_preserves_sofic_parent G dec Y = some B ∧ A ≠ B ∧
      (interior A.carrier ∩ B.carrier).Nonempty ∧ S = {X, Y}

private def dissection_preserves_sofic_forbidden (G : GroupedFamily P)
    (dec : Decoration G.P') (R : LocalRule dec.P') :
    Set (Set (PlacedTile (dissection_preserves_sofic_dec G dec).P')) :=
  {S | dissection_preserves_sofic_badPair G dec S ∨
    (∃ X, X.form.isLeft ∧ S = {X}) ∨
    (∃ F ∈ R.forbidden, S.Finite ∧
      (∀ X ∈ S, ∃ A, dissection_preserves_sofic_parent G dec X = some A) ∧
      dissection_preserves_sofic_parentSet G dec S = F)}

private lemma dissection_preserves_sofic_children_mem (G : GroupedFamily P)
    (dec : Decoration G.P') (q : dec.P'.Form) (B : PlacedTile P) :
    B ∈ dissection_preserves_sofic_children G dec q ↔
      B ∈ (G.dissect (dec.proj q)).tiles := by
  simp [dissection_preserves_sofic_children]

private lemma dissection_preserves_sofic_parent_liftTile (G : GroupedFamily P)
    (dec : Decoration G.P') (A : PlacedTile dec.P')
    (B : {B // B ∈ dissection_preserves_sofic_children G dec A.form}) :
    dissection_preserves_sofic_parent G dec
      (dissection_preserves_sofic_liftTile G dec A B) = some A := by
  simp [dissection_preserves_sofic_parent, dissection_preserves_sofic_liftTile]

private lemma dissection_preserves_sofic_parent_translate (G : GroupedFamily P)
    (dec : Decoration G.P')
    (X : PlacedTile (dissection_preserves_sofic_dec G dec).P') (v : Pt) :
    dissection_preserves_sofic_parent G dec (X.translate v) =
      (dissection_preserves_sofic_parent G dec X).map fun A => A.translate v := by
  rcases X with ⟨q, x⟩
  rcases q with p | a
  · rfl
  · simp only [dissection_preserves_sofic_parent, PlacedTile.translate, Option.map_some]
    apply congrArg some
    apply PlacedTile.ext
    · rfl
    · simp only [vadd_eq_add]
      abel

private lemma dissection_preserves_sofic_carrier_translate {Q : Protoset}
    (A : PlacedTile Q) (v : Pt) : (A.translate v).carrier = v +ᵥ A.carrier := by
  simp only [PlacedTile.translate, PlacedTile.carrier, Set.ext_iff,
    mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  intro y
  constructor <;> intro hy
  · convert hy using 1
    all_goals abel
  · convert hy using 1
    all_goals abel

private lemma dissection_preserves_sofic_child_carrier_subset (G : GroupedFamily P)
    (dec : Decoration G.P')
    {X : PlacedTile (dissection_preserves_sofic_dec G dec).P'} {A : PlacedTile dec.P'}
    (hXA : dissection_preserves_sofic_parent G dec X = some A) :
    X.carrier ⊆ A.carrier := by
  rcases X with ⟨q, x⟩
  rcases q with p | a
  · simp [dissection_preserves_sofic_parent] at hXA
  · rcases a with ⟨q, B, hB⟩
    simp only [dissection_preserves_sofic_parent, Option.some.injEq] at hXA
    subst A
    intro y hy
    have hBc : B.carrier ⊆ (G.P'.disk (dec.proj q)).carrier := by
      rw [← G.support_eq]
      exact fun z hz => Set.mem_biUnion
        ((dissection_preserves_sofic_children_mem G dec q B).mp hB) hz
    change y ∈ x +ᵥ (P.disk B.form).carrier at hy
    rw [mem_vadd_set_iff_neg_vadd_mem] at hy
    have hz := hBc (show B.anchor +ᵥ (-x +ᵥ y) ∈ B.carrier by
      exact vadd_mem_vadd_set hy)
    rw [PlacedTile.carrier, dec.carrier_eq]
    rw [mem_vadd_set_iff_neg_vadd_mem]
    convert hz using 1
    all_goals simp only [vadd_eq_add]
    all_goals abel

private lemma dissection_preserves_sofic_parent_diam_le (G : GroupedFamily P)
    (dec : Decoration G.P') (A : PlacedTile dec.P') :
    Metric.diam A.carrier ≤ dissection_preserves_sofic_size G := by
  have hq : Metric.diam (G.P'.disk (dec.proj A.form)).carrier ≤
      dissection_preserves_sofic_size G := by
    apply le_trans (le_max_right 0 _)
    unfold dissection_preserves_sofic_size
    apply le_trans (Finset.single_le_sum (s := Finset.univ)
      (f := fun q : G.P'.Form => max 0 (Metric.diam (G.P'.disk q).carrier))
      (fun q _ => le_max_left 0 _) (Finset.mem_univ _))
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun p _ => le_max_left 0 _)
  rw [PlacedTile.carrier, dec.carrier_eq, diam_vadd]
  exact hq

private lemma dissection_preserves_sofic_badPair_bounded (G : GroupedFamily P)
    (dec : Decoration G.P')
    {S : Set (PlacedTile (dissection_preserves_sofic_dec G dec).P')}
    (hS : dissection_preserves_sofic_badPair G dec S) :
    Metric.diam (support S) ≤ 2 * dissection_preserves_sofic_size G := by
  obtain ⟨X, hX, Y, hY, A, B, hXA, hYB, -, hAB, rfl⟩ := hS
  have hsub : support ({X, Y} : Set _) ⊆ A.carrier ∪ B.carrier := by
    intro z hz
    simp only [support, Set.mem_iUnion, exists_prop, mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with ⟨Z, hZ, hz⟩
    rcases hZ with rfl | rfl
    · exact Or.inl (dissection_preserves_sofic_child_carrier_subset G dec hXA hz)
    · exact Or.inr (dissection_preserves_sofic_child_carrier_subset G dec hYB hz)
  have hAc : IsCompact A.carrier := cc_tile_compact A
  have hBc : IsCompact B.carrier := cc_tile_compact B
  obtain ⟨z, hzA, hzB⟩ := hAB
  calc
    Metric.diam (support ({X, Y} : Set _)) ≤ Metric.diam (A.carrier ∪ B.carrier) :=
      Metric.diam_mono hsub (hAc.union hBc).isBounded
    _ ≤ Metric.diam A.carrier + Metric.diam B.carrier :=
      Metric.diam_union' ⟨z, interior_subset hzA, hzB⟩
    _ ≤ 2 * dissection_preserves_sofic_size G := by
      have hA := dissection_preserves_sofic_parent_diam_le G dec A
      have hB := dissection_preserves_sofic_parent_diam_le G dec B
      linarith

private lemma dissection_preserves_sofic_inert_bounded (G : GroupedFamily P)
    (dec : Decoration G.P')
    (X : PlacedTile (dissection_preserves_sofic_dec G dec).P')
    (hX : X.form.isLeft) :
    Metric.diam (support ({X} : Set _)) ≤ dissection_preserves_sofic_size G := by
  rcases X with ⟨q, x⟩
  rcases q with p | a
  · have hp : Metric.diam (P.disk p).carrier ≤ dissection_preserves_sofic_size G := by
      apply le_trans (le_max_right 0 _)
      unfold dissection_preserves_sofic_size
      apply le_add_of_le_of_nonneg
      · apply Finset.single_le_sum (s := Finset.univ)
          (f := fun p : P.Form => max 0 (Metric.diam (P.disk p).carrier))
        · intro p _
          exact le_max_left 0 _
        · exact Finset.mem_univ _
      · exact Finset.sum_nonneg fun q _ => le_max_left 0 _
    simpa only [support, biUnion_singleton, PlacedTile.carrier,
      dissection_preserves_sofic_dec, diam_vadd] using hp
  · simp at hX

private lemma dissection_preserves_sofic_active_support_subset (G : GroupedFamily P)
    (dec : Decoration G.P')
    {S : Set (PlacedTile (dissection_preserves_sofic_dec G dec).P')}
    (hactive : ∀ X ∈ S, ∃ A, dissection_preserves_sofic_parent G dec X = some A) :
    support S ⊆ support (dissection_preserves_sofic_parentSet G dec S) := by
  intro z hz
  simp only [support, Set.mem_iUnion, exists_prop] at hz ⊢
  obtain ⟨X, hXS, hzX⟩ := hz
  obtain ⟨A, hXA⟩ := hactive X hXS
  exact ⟨A, ⟨X, hXS, hXA⟩,
    dissection_preserves_sofic_child_carrier_subset G dec hXA hzX⟩

private noncomputable def dissection_preserves_sofic_rule (G : GroupedFamily P)
    (dec : Decoration G.P') (R : LocalRule dec.P') :
    LocalRule (dissection_preserves_sofic_dec G dec).P' where
  forbidden := dissection_preserves_sofic_forbidden G dec R
  D := max R.D (2 * dissection_preserves_sofic_size G)
  bounded := by
    intro S hS
    simp only [dissection_preserves_sofic_forbidden, mem_setOf_eq] at hS
    rcases hS with hbad | hinert | hpull
    · exact ⟨by
        obtain ⟨X, -, Y, -, A, B, -, -, -, -, rfl⟩ := hbad
        exact Set.toFinite _,
        (dissection_preserves_sofic_badPair_bounded G dec hbad).trans
          (le_max_right _ _)⟩
    · obtain ⟨X, hX, rfl⟩ := hinert
      have hsize : 0 ≤ dissection_preserves_sofic_size G := by
        unfold dissection_preserves_sofic_size
        positivity
      exact ⟨Set.finite_singleton X,
        (dissection_preserves_sofic_inert_bounded G dec X hX).trans
          ((show dissection_preserves_sofic_size G ≤
            2 * dissection_preserves_sofic_size G by linarith).trans (le_max_right _ _))⟩
    · obtain ⟨F, hFR, hSfin, hactive, hparent⟩ := hpull
      refine ⟨hSfin, ?_⟩
      apply (Metric.diam_mono
        (dissection_preserves_sofic_active_support_subset G dec hactive) ?_).trans
      · rw [hparent]
        exact (R.bounded F hFR).2.trans (le_max_left _ _)
      · rw [hparent]
        exact ((R.bounded F hFR).1.isCompact_biUnion fun A _ => cc_tile_compact A).isBounded

private lemma dissection_preserves_sofic_mem_liftSet (G : GroupedFamily P)
    (dec : Decoration G.P') (S : Set (PlacedTile dec.P'))
    (X : PlacedTile (dissection_preserves_sofic_dec G dec).P') :
    X ∈ dissection_preserves_sofic_liftSet G dec S ↔
      ∃ A ∈ S, ∃ B, X = dissection_preserves_sofic_liftTile G dec A B := by
  simp only [dissection_preserves_sofic_liftSet, Set.mem_iUnion, mem_range]
  aesop

private lemma dissection_preserves_sofic_liftTile_carrier (G : GroupedFamily P)
    (dec : Decoration G.P') (A : PlacedTile dec.P')
    (B : {B // B ∈ dissection_preserves_sofic_children G dec A.form}) :
    (dissection_preserves_sofic_liftTile G dec A B).carrier = A.anchor +ᵥ B.1.carrier := by
  simp only [dissection_preserves_sofic_liftTile, PlacedTile.carrier,
    dissection_preserves_sofic_dec, vadd_eq_add, Set.ext_iff, mem_vadd_set_iff_neg_vadd_mem]
  intro y
  constructor <;> intro hy
  · convert hy using 1
    all_goals abel
  · convert hy using 1
    all_goals abel

private lemma dissection_preserves_sofic_support_liftSet (G : GroupedFamily P)
    (dec : Decoration G.P') (S : Set (PlacedTile dec.P')) :
    support (dissection_preserves_sofic_liftSet G dec S) = support S := by
  ext y
  simp only [support, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨X, hX, hyX⟩
    obtain ⟨A, hAS, B, rfl⟩ :=
      (dissection_preserves_sofic_mem_liftSet G dec S X).mp hX
    exact ⟨A, hAS, dissection_preserves_sofic_child_carrier_subset G dec
      (dissection_preserves_sofic_parent_liftTile G dec A B) hyX⟩
  · rintro ⟨A, hAS, hyA⟩
    rw [PlacedTile.carrier, dec.carrier_eq, ← G.support_eq,
      mem_vadd_set_iff_neg_vadd_mem] at hyA
    simp only [support, Set.mem_iUnion, exists_prop] at hyA
    obtain ⟨B, hB, hyB⟩ := hyA
    let B' : {B // B ∈ dissection_preserves_sofic_children G dec A.form} :=
      ⟨B, (dissection_preserves_sofic_children_mem G dec A.form B).mpr hB⟩
    refine ⟨dissection_preserves_sofic_liftTile G dec A B',
      (dissection_preserves_sofic_mem_liftSet G dec S _).mpr ⟨A, hAS, B', rfl⟩, ?_⟩
    rw [dissection_preserves_sofic_liftTile_carrier]
    rw [mem_vadd_set_iff_neg_vadd_mem]
    exact hyB

private lemma dissection_preserves_sofic_liftTile_injective (G : GroupedFamily P)
    (dec : Decoration G.P') {A C : PlacedTile dec.P'}
    {B : {B // B ∈ dissection_preserves_sofic_children G dec A.form}}
    {D : {B // B ∈ dissection_preserves_sofic_children G dec C.form}}
    (h : dissection_preserves_sofic_liftTile G dec A B =
      dissection_preserves_sofic_liftTile G dec C D) : A = C ∧ B.1 = D.1 := by
  have hp := congrArg (dissection_preserves_sofic_parent G dec) h
  rw [dissection_preserves_sofic_parent_liftTile,
    dissection_preserves_sofic_parent_liftTile] at hp
  have hAC := Option.some.inj hp
  subst C
  have hf := congrArg PlacedTile.form h
  have hs : (⟨A.form, B⟩ : dissection_preserves_sofic_Active G dec) = ⟨A.form, D⟩ :=
    Sum.inr.inj hf
  exact ⟨rfl, congrArg (fun a => a.2.1) hs⟩

private noncomputable def dissection_preserves_sofic_lift (G : GroupedFamily P)
    (dec : Decoration G.P') (T : PlaneTiling dec.P') :
    PlaneTiling (dissection_preserves_sofic_dec G dec).P' where
  tiles := dissection_preserves_sofic_liftSet G dec T.tiles
  cover := by rw [dissection_preserves_sofic_support_liftSet, T.cover]
  disjoint := by
    intro X hX Y hY hXY
    obtain ⟨A, hAT, B, rfl⟩ :=
      (dissection_preserves_sofic_mem_liftSet G dec T.tiles X).mp hX
    obtain ⟨C, hCT, D, rfl⟩ :=
      (dissection_preserves_sofic_mem_liftSet G dec T.tiles Y).mp hY
    by_cases hAC : A = C
    · subst C
      have hBD : B.1 ≠ D.1 := fun h => hXY (by
        have h' : B = D := Subtype.ext h
        subst D
        rfl)
      have hd := (G.dissect (dec.proj A.form)).disjoint
        ((dissection_preserves_sofic_children_mem G dec A.form B).mp B.2)
        ((dissection_preserves_sofic_children_mem G dec A.form D).mp D.2) hBD
      unfold Function.onFun at hd ⊢
      change Disjoint (interior B.1.carrier) (interior D.1.carrier) at hd
      change Disjoint
        (interior (dissection_preserves_sofic_liftTile G dec A B).carrier)
        (interior (dissection_preserves_sofic_liftTile G dec A D).carrier)
      rw [dissection_preserves_sofic_liftTile_carrier,
        dissection_preserves_sofic_liftTile_carrier, interior_vadd, interior_vadd]
      rw [Set.disjoint_left]
      intro z hzB hzD
      rw [mem_vadd_set_iff_neg_vadd_mem] at hzB hzD
      exact Set.disjoint_left.mp hd hzB hzD
    · have hd := T.disjoint hAT hCT hAC
      exact hd.mono
        (interior_mono (dissection_preserves_sofic_child_carrier_subset G dec
          (dissection_preserves_sofic_parent_liftTile G dec A B)))
        (interior_mono (dissection_preserves_sofic_child_carrier_subset G dec
          (dissection_preserves_sofic_parent_liftTile G dec C D)))

private lemma dissection_preserves_sofic_parent_of_mem_liftSet (G : GroupedFamily P)
    (dec : Decoration G.P') {S : Set (PlacedTile dec.P')}
    {X : PlacedTile (dissection_preserves_sofic_dec G dec).P'} {A : PlacedTile dec.P'}
    (hX : X ∈ dissection_preserves_sofic_liftSet G dec S)
    (hXA : dissection_preserves_sofic_parent G dec X = some A) : A ∈ S := by
  obtain ⟨C, hCS, B, rfl⟩ :=
    (dissection_preserves_sofic_mem_liftSet G dec S X).mp hX
  rw [dissection_preserves_sofic_parent_liftTile] at hXA
  exact Option.some.inj hXA ▸ hCS

private lemma dissection_preserves_sofic_no_cross {Q : Protoset}
    (T : PlaneTiling Q) {A B : PlacedTile Q} (hA : A ∈ T.tiles) (hB : B ∈ T.tiles)
    (hne : A ≠ B) : Disjoint (interior A.carrier) B.carrier := by
  rw [Set.disjoint_left]
  intro z hzA hzB
  rw [← cc_tile_regular B, mem_closure_iff_nhds] at hzB
  obtain ⟨y, hyB, hyA⟩ := hzB _ (isOpen_interior.mem_nhds hzA)
  exact Set.disjoint_left.mp (T.disjoint hA hB hne) hyB hyA

private lemma dissection_preserves_sofic_lift_proper (G : GroupedFamily P)
    (dec : Decoration G.P') (R : LocalRule dec.P') (T : PlaneTiling dec.P')
    (hT : R.Proper T) :
    (dissection_preserves_sofic_rule G dec R).Proper
      (dissection_preserves_sofic_lift G dec T) := by
  intro S hS hocc
  simp only [dissection_preserves_sofic_rule, dissection_preserves_sofic_forbidden,
    mem_setOf_eq] at hS
  obtain ⟨v, hv⟩ := hocc
  rcases hS with hbad | hinert | hpull
  · obtain ⟨X, hXS, Y, hYS, A, B, hXA, hYB, hAB, hinter, -⟩ := hbad
    have hXt := hv (cc_translate_mem v hXS)
    have hYt := hv (cc_translate_mem v hYS)
    have hpat := dissection_preserves_sofic_parent_translate G dec X v
    have hpbt := dissection_preserves_sofic_parent_translate G dec Y v
    rw [hXA] at hpat
    rw [hYB] at hpbt
    have hAt : A.translate v ∈ T.tiles :=
      dissection_preserves_sofic_parent_of_mem_liftSet G dec hXt hpat
    have hBt : B.translate v ∈ T.tiles :=
      dissection_preserves_sofic_parent_of_mem_liftSet G dec hYt hpbt
    have hne : A.translate v ≠ B.translate v := by
      intro heq
      have := congrArg (fun Z : PlacedTile dec.P' => Z.translate (-v)) heq
      apply hAB
      simpa only [cc_translate_translate, neg_add_cancel, cc_translate_zero] using this
    have hdisj := dissection_preserves_sofic_no_cross T hAt hBt hne
    obtain ⟨z, hzA, hzB⟩ := hinter
    have hzAt : v +ᵥ z ∈ interior (A.translate v).carrier := by
      rw [dissection_preserves_sofic_carrier_translate, interior_vadd]
      exact vadd_mem_vadd_set hzA
    have hzBt : v +ᵥ z ∈ (B.translate v).carrier := by
      rw [dissection_preserves_sofic_carrier_translate]
      exact vadd_mem_vadd_set hzB
    exact Set.disjoint_left.mp hdisj hzAt hzBt
  · obtain ⟨X, hleft, rfl⟩ := hinert
    have hmem := hv (cc_translate_mem v (Set.mem_singleton X))
    obtain ⟨A, -, B, heq⟩ :=
      (dissection_preserves_sofic_mem_liftSet G dec T.tiles (X.translate v)).mp hmem
    have hf := congrArg PlacedTile.form heq
    rcases X with ⟨q, x⟩
    rcases q with p | a
    · simp [PlacedTile.translate, dissection_preserves_sofic_liftTile] at hf
    · simp at hleft
  · obtain ⟨F, hFR, -, -, hparent⟩ := hpull
    apply hT F hFR
    refine ⟨v, ?_⟩
    intro A hA
    rw [cc_mem_translateSet] at hA
    have hAF : A.translate (-v) ∈ F := hA
    rw [← hparent] at hAF
    obtain ⟨X, hXS, hXA⟩ := hAF
    have hXt := hv (cc_translate_mem v hXS)
    have hp := dissection_preserves_sofic_parent_translate G dec X v
    rw [hXA] at hp
    have hmem := dissection_preserves_sofic_parent_of_mem_liftSet G dec hXt hp
    simpa only [cc_translate_translate, add_neg_cancel, cc_translate_zero] using hmem

private lemma dissection_preserves_sofic_proper_active (G : GroupedFamily P)
    (dec : Decoration G.P') (R : LocalRule dec.P')
    (T : PlaneTiling (dissection_preserves_sofic_dec G dec).P')
    (hT : (dissection_preserves_sofic_rule G dec R).Proper T) {X} (hX : X ∈ T.tiles) :
    ∃ A, dissection_preserves_sofic_parent G dec X = some A := by
  rcases X with ⟨q, x⟩
  rcases q with p | a
  · exfalso
    apply hT ({⟨.inl p, x⟩} : Set _) (by
      simp only [dissection_preserves_sofic_rule, dissection_preserves_sofic_forbidden,
        mem_setOf_eq]
      exact Or.inr (Or.inl ⟨⟨.inl p, x⟩, rfl, rfl⟩))
    exact ⟨0, by simpa [cc_translateSet_zero] using hX⟩
  · exact ⟨⟨a.1, x - a.2.1.anchor⟩, rfl⟩

private lemma dissection_preserves_sofic_proper_parents_disjoint (G : GroupedFamily P)
    (dec : Decoration G.P') (R : LocalRule dec.P')
    (T : PlaneTiling (dissection_preserves_sofic_dec G dec).P')
    (hT : (dissection_preserves_sofic_rule G dec R).Proper T) :
    DisjointInteriors (dissection_preserves_sofic_parentSet G dec T.tiles) := by
  intro A hA B hB hAB
  obtain ⟨X, hXT, hXA⟩ := hA
  obtain ⟨Y, hYT, hYB⟩ := hB
  unfold Function.onFun
  rw [Set.disjoint_left]
  intro z hzA hzB
  apply hT ({X, Y} : Set _) (by
    simp only [dissection_preserves_sofic_rule, dissection_preserves_sofic_forbidden,
      mem_setOf_eq]
    left
    exact ⟨X, mem_insert X {Y}, Y, mem_insert_of_mem X (mem_singleton Y),
      A, B, hXA, hYB, hAB, ⟨z, hzA, interior_subset hzB⟩, rfl⟩)
  exact ⟨0, by
    rw [cc_translateSet_zero]
    exact insert_subset hXT (singleton_subset_iff.mpr hYT)⟩

private noncomputable def dissection_preserves_sofic_parentTiling (G : GroupedFamily P)
    (dec : Decoration G.P') (R : LocalRule dec.P')
    (T : PlaneTiling (dissection_preserves_sofic_dec G dec).P')
    (hT : (dissection_preserves_sofic_rule G dec R).Proper T) : PlaneTiling dec.P' where
  tiles := dissection_preserves_sofic_parentSet G dec T.tiles
  cover := by
    apply Set.Subset.antisymm (subset_univ _)
    rw [← T.cover]
    exact dissection_preserves_sofic_active_support_subset G dec
      (fun X hX => dissection_preserves_sofic_proper_active G dec R T hT hX)
  disjoint := dissection_preserves_sofic_proper_parents_disjoint G dec R T hT

private lemma dissection_preserves_sofic_parentTiling_proper (G : GroupedFamily P)
    (dec : Decoration G.P') (R : LocalRule dec.P')
    (T : PlaneTiling (dissection_preserves_sofic_dec G dec).P')
    (hT : (dissection_preserves_sofic_rule G dec R).Proper T) :
    R.Proper (dissection_preserves_sofic_parentTiling G dec R T hT) := by
  intro F hFR hocc
  obtain ⟨v, hv⟩ := hocc
  have hpick : ∀ A ∈ F, ∃ X ∈ T.tiles,
      dissection_preserves_sofic_parent G dec X = some (A.translate v) := by
    intro A hAF
    have hAv := hv (cc_translate_mem v hAF)
    exact hAv
  let pick : ↥F → PlacedTile (dissection_preserves_sofic_dec G dec).P' :=
    fun A => Classical.choose (hpick A.1 A.2)
  have hpickT : ∀ A : ↥F, pick A ∈ T.tiles :=
    fun A => (Classical.choose_spec (hpick A.1 A.2)).1
  have hpickParent : ∀ A : ↥F,
      dissection_preserves_sofic_parent G dec (pick A) = some (A.1.translate v) :=
    fun A => (Classical.choose_spec (hpick A.1 A.2)).2
  letI : Fintype ↥F := (R.bounded F hFR).1.fintype
  let S : Set (PlacedTile (dissection_preserves_sofic_dec G dec).P') :=
    (fun A : ↥F => (pick A).translate (-v)) '' univ
  have hSfin : S.Finite := Set.finite_univ.image _
  have hSactive : ∀ X ∈ S,
      ∃ A, dissection_preserves_sofic_parent G dec X = some A := by
    rintro X ⟨A, -, rfl⟩
    refine ⟨A.1, ?_⟩
    rw [dissection_preserves_sofic_parent_translate, hpickParent A]
    simp only [Option.map_some, Option.some.injEq]
    rw [cc_translate_translate, neg_add_cancel, cc_translate_zero]
  have hSparent : dissection_preserves_sofic_parentSet G dec S = F := by
    ext A
    constructor
    · rintro ⟨X, ⟨C, -, rfl⟩, hpar⟩
      rw [dissection_preserves_sofic_parent_translate, hpickParent C] at hpar
      have heq : C.1 = A := by
        simpa only [cc_translate_translate, neg_add_cancel, cc_translate_zero] using
          Option.some.inj hpar
      exact heq ▸ C.2
    · intro hAF
      let A' : ↥F := ⟨A, hAF⟩
      refine ⟨(pick A').translate (-v), ⟨A', mem_univ _, rfl⟩, ?_⟩
      rw [dissection_preserves_sofic_parent_translate, hpickParent A']
      simp only [Option.map_some, Option.some.injEq]
      rw [cc_translate_translate, neg_add_cancel, cc_translate_zero]
  apply hT S (by
    simp only [dissection_preserves_sofic_rule, dissection_preserves_sofic_forbidden,
      mem_setOf_eq]
    exact Or.inr (Or.inr ⟨F, hFR, hSfin, hSactive, hSparent⟩))
  refine ⟨v, ?_⟩
  rintro X ⟨Y, ⟨A, -, rfl⟩, rfl⟩
  simpa only [cc_translate_translate, add_neg_cancel, cc_translate_zero] using hpickT A

private lemma dissection_preserves_sofic_active_eq_liftTile (G : GroupedFamily P)
    (dec : Decoration G.P')
    {X : PlacedTile (dissection_preserves_sofic_dec G dec).P'} {A : PlacedTile dec.P'}
    (hXA : dissection_preserves_sofic_parent G dec X = some A) :
    ∃ B, X = dissection_preserves_sofic_liftTile G dec A B := by
  rcases X with ⟨q, x⟩
  rcases q with p | a
  · simp [dissection_preserves_sofic_parent] at hXA
  · rcases a with ⟨q, B, hB⟩
    simp only [dissection_preserves_sofic_parent, Option.some.injEq] at hXA
    subst A
    let B' : {B // B ∈ dissection_preserves_sofic_children G dec q} := ⟨B, hB⟩
    refine ⟨B', ?_⟩
    apply PlacedTile.ext
    · rfl
    · simp only [dissection_preserves_sofic_liftTile]
      abel

private lemma dissection_preserves_sofic_tiles_subset_lift (G : GroupedFamily P)
    (dec : Decoration G.P') (R : LocalRule dec.P')
    (T : PlaneTiling (dissection_preserves_sofic_dec G dec).P')
    (hT : (dissection_preserves_sofic_rule G dec R).Proper T) :
    T.tiles ⊆ dissection_preserves_sofic_liftSet G dec
      (dissection_preserves_sofic_parentSet G dec T.tiles) := by
  intro X hXT
  obtain ⟨A, hXA⟩ := dissection_preserves_sofic_proper_active G dec R T hT hXT
  obtain ⟨B, rfl⟩ := dissection_preserves_sofic_active_eq_liftTile G dec hXA
  apply (dissection_preserves_sofic_mem_liftSet G dec _ _).mpr
  exact ⟨A, ⟨_, hXT, hXA⟩, B, rfl⟩

private lemma dissection_preserves_sofic_tiling_maximal {Q : Protoset}
    (T₁ T₂ : PlaneTiling Q) (hsub : T₁.tiles ⊆ T₂.tiles) : T₁.tiles = T₂.tiles := by
  apply Set.Subset.antisymm hsub
  intro Y hY
  obtain ⟨y, hy⟩ := (Q.disk Y.form).interior_nonempty
  have hyY : Y.anchor +ᵥ y ∈ interior Y.carrier := by
    rw [PlacedTile.carrier, interior_vadd]
    exact vadd_mem_vadd_set hy
  have hcov : Y.anchor +ᵥ y ∈ support T₁.tiles := by rw [T₁.cover]; trivial
  simp only [support, Set.mem_iUnion, exists_prop] at hcov
  obtain ⟨X, hX, hyX⟩ := hcov
  by_cases hXY : X = Y
  · exact hXY ▸ hX
  · have hd := dissection_preserves_sofic_no_cross T₂ hY (hsub hX) (Ne.symm hXY)
    exact (Set.disjoint_left.mp hd hyY hyX).elim

private lemma dissection_preserves_sofic_PlaneTiling_ext {Q : Protoset}
    {T₁ T₂ : PlaneTiling Q} (h : T₁.tiles = T₂.tiles) : T₁ = T₂ := by
  cases T₁
  cases T₂
  congr

private lemma dissection_preserves_sofic_tiling_eq_lift (G : GroupedFamily P)
    (dec : Decoration G.P') (R : LocalRule dec.P')
    (T : PlaneTiling (dissection_preserves_sofic_dec G dec).P')
    (hT : (dissection_preserves_sofic_rule G dec R).Proper T) :
    T = dissection_preserves_sofic_lift G dec
      (dissection_preserves_sofic_parentTiling G dec R T hT) := by
  apply dissection_preserves_sofic_PlaneTiling_ext
  exact dissection_preserves_sofic_tiling_maximal
    T _ (dissection_preserves_sofic_tiles_subset_lift G dec R T hT)

private lemma dissection_preserves_sofic_project_liftTile (G : GroupedFamily P)
    (dec : Decoration G.P') (A : PlacedTile dec.P')
    (B : {B // B ∈ dissection_preserves_sofic_children G dec A.form}) :
    (dissection_preserves_sofic_dec G dec).projTile
      (dissection_preserves_sofic_liftTile G dec A B) = B.1.translate A.anchor := by
  apply PlacedTile.ext
  · rfl
  · rfl

private lemma dissection_preserves_sofic_project_lift (G : GroupedFamily P)
    (dec : Decoration G.P') (T : PlaneTiling dec.P') :
    ((dissection_preserves_sofic_dec G dec).project
      (dissection_preserves_sofic_lift G dec T)).tiles =
      G.scatter (dec.project T).tiles := by
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩
    obtain ⟨A, hAT, B, rfl⟩ :=
      (dissection_preserves_sofic_mem_liftSet G dec T.tiles Y).mp hY
    rw [dissection_preserves_sofic_project_liftTile]
    simp only [GroupedFamily.scatter, GroupedFamily.scatterTile, Set.mem_iUnion]
    refine ⟨dec.projTile A, ⟨A, hAT, rfl⟩, ?_⟩
    exact cc_translate_mem A.anchor
      ((dissection_preserves_sofic_children_mem G dec A.form B).mp B.2)
  · simp only [GroupedFamily.scatter, GroupedFamily.scatterTile, Set.mem_iUnion]
    rintro ⟨A, ⟨C, hCT, rfl⟩, B, hB, rfl⟩
    let B' : {B // B ∈ dissection_preserves_sofic_children G dec C.form} :=
      ⟨B, (dissection_preserves_sofic_children_mem G dec C.form B).mpr hB⟩
    refine ⟨dissection_preserves_sofic_liftTile G dec C B', ?_, ?_⟩
    · exact (dissection_preserves_sofic_mem_liftSet G dec T.tiles _).mpr
        ⟨C, hCT, B', rfl⟩
    · rw [dissection_preserves_sofic_project_liftTile]
      rfl

/-- `lem:glues` (generic presentations): the grouped forms are finite
connected unions of original tiles with connected dual graphs (fields of
`GroupedFamily`).  A sofic presentation of a family of grouped plane tilings
transfers, via unique glue colours on internal constituent sides and inert
decorations for surjectivity, to a sofic presentation of its scattering. -/
theorem Decoration.dissection_preserves_sofic (G : GroupedFamily P)
    {F' : Set (PlaneTiling G.P')} (h : IsSofic F') : IsSofic (G.scatterFamily F') := by
  obtain ⟨dec, R, hF⟩ := h
  refine ⟨dissection_preserves_sofic_dec G dec,
    dissection_preserves_sofic_rule G dec R, fun T => ?_⟩
  constructor
  · rintro ⟨T', hT'F, hscatter⟩
    obtain ⟨T'', hproper, hproject⟩ := (hF T').mp hT'F
    refine ⟨dissection_preserves_sofic_lift G dec T'',
      dissection_preserves_sofic_lift_proper G dec R T'' hproper, ?_⟩
    apply dissection_preserves_sofic_PlaneTiling_ext
    rw [dissection_preserves_sofic_project_lift, hproject, hscatter]
  · rintro ⟨Tdec, hproper, hproject⟩
    let T'' := dissection_preserves_sofic_parentTiling G dec R Tdec hproper
    have hT''proper : R.Proper T'' :=
      dissection_preserves_sofic_parentTiling_proper G dec R Tdec hproper
    refine ⟨dec.project T'', (hF _).mpr ⟨T'', hT''proper, rfl⟩, ?_⟩
    rw [← dissection_preserves_sofic_project_lift G dec T'']
    have heq := dissection_preserves_sofic_tiling_eq_lift G dec R Tdec hproper
    rw [← heq, hproject]

/-- Step 1 helper: every listed side of a placed tile lies in its carrier. -/
private lemma dissection_preserves_sts_sofic_step1_local_rule_tile_side_subset
    (A : PlacedTile P) (i : Fin (P.disk A.form).n) : A.side i ⊆ A.carrier := by
  exact image_mono (by
    apply (show (P.disk A.form).side i ⊆ frontier (P.disk A.form).carrier from ?_).trans
      (P.disk A.form).compact.isClosed.frontier_subset
    rw [(P.disk A.form).frontier_eq]
    exact Set.subset_iUnion (fun j =>
      segment ℝ ((P.disk A.form).vertex j)
        ((P.disk A.form).vertex (finRotate _ j))) i)

private lemma dissection_preserves_sts_sofic_step1_local_rule_tile_side_nonempty
    (A : PlacedTile P) (i : Fin (P.disk A.form).n) : (A.side i).Nonempty := by
  refine ⟨A.vertex i, ?_⟩
  exact ⟨(P.disk A.form).vertex i, left_mem_segment ℝ _ _, rfl⟩

private def dissection_preserves_sts_sofic_step1_local_rule_side_rule_bad
    (dec : SideDecoration P) (A B : PlacedTile dec.P') : Prop :=
  ∃ (i : Fin (dec.P'.disk A.form).n) (j : Fin (dec.P'.disk B.form).n),
    (OverlapPos (A.side i) (B.side j) ∧ A.side i ≠ B.side j) ∨
      (A ≠ B ∧ A.side i = B.side j ∧
        dec.colour A.form i ≠ dec.colour B.form j)

private lemma dissection_preserves_sts_sofic_step1_local_rule_bad_carriers_meet
    (dec : SideDecoration P) (A B : PlacedTile dec.P')
    (h : dissection_preserves_sts_sofic_step1_local_rule_side_rule_bad dec A B) :
    (A.carrier ∩ B.carrier).Nonempty := by
  obtain ⟨i, j, hbad | hbad⟩ := h
  · obtain ⟨⟨x, y, hxy, hseg⟩, hne⟩ := hbad
    have hx := hseg (left_mem_segment ℝ x y)
    exact ⟨x,
      dissection_preserves_sts_sofic_step1_local_rule_tile_side_subset A i hx.1,
      dissection_preserves_sts_sofic_step1_local_rule_tile_side_subset B j hx.2⟩
  · obtain ⟨hne, heq, hcol⟩ := hbad
    obtain ⟨x, hx⟩ :=
      dissection_preserves_sts_sofic_step1_local_rule_tile_side_nonempty A i
    exact ⟨x,
      dissection_preserves_sts_sofic_step1_local_rule_tile_side_subset A i hx,
      dissection_preserves_sts_sofic_step1_local_rule_tile_side_subset B j (heq ▸ hx)⟩

private def dissection_preserves_sts_sofic_step1_local_rule_local_rule
    (dec : SideDecoration P) : LocalRule dec.P' where
  forbidden := {F | ∃ A B, F = {A, B} ∧
    dissection_preserves_sts_sofic_step1_local_rule_side_rule_bad dec A B}
  D := 2 * ∑ q : dec.P'.Form, Metric.diam (dec.P'.disk q).carrier
  bounded := by
    rintro F ⟨A, B, rfl, hbad⟩
    refine ⟨Set.toFinite {A, B}, ?_⟩
    have hmeet :=
      dissection_preserves_sts_sofic_step1_local_rule_bad_carriers_meet dec A B hbad
    have hA : Metric.diam A.carrier ≤
        ∑ q : dec.P'.Form, Metric.diam (dec.P'.disk q).carrier := by
      rw [PlacedTile.carrier, diam_vadd]
      exact Finset.single_le_sum
        (f := fun q : dec.P'.Form => Metric.diam (dec.P'.disk q).carrier)
        (fun _ _ => Metric.diam_nonneg) (Finset.mem_univ A.form)
    have hB : Metric.diam B.carrier ≤
        ∑ q : dec.P'.Form, Metric.diam (dec.P'.disk q).carrier := by
      rw [PlacedTile.carrier, diam_vadd]
      exact Finset.single_le_sum
        (f := fun q : dec.P'.Form => Metric.diam (dec.P'.disk q).carrier)
        (fun _ _ => Metric.diam_nonneg) (Finset.mem_univ B.form)
    have hu := Metric.diam_union' hmeet
    rw [show support ({A, B} : Set (PlacedTile dec.P')) = A.carrier ∪ B.carrier by
      simp [support]]
    calc
      Metric.diam (A.carrier ∪ B.carrier) ≤ Metric.diam A.carrier + Metric.diam B.carrier := hu
      _ ≤ _ := by linarith

private lemma dissection_preserves_sts_sofic_step1_local_rule_translate_tile_zero
    (A : PlacedTile P) : A.translate 0 = A := by
  apply PlacedTile.ext <;> simp [PlacedTile.translate]

private lemma dissection_preserves_sts_sofic_step1_local_rule_translate_tile_injective
    (v : Pt) : Function.Injective (fun A : PlacedTile P => A.translate v) := by
  intro A B h
  have h' := congrArg (fun X : PlacedTile P => X.translate (-v)) h
  have hp : A.form = B.form ∧ A.anchor = B.anchor := by
    simpa [PlacedTile.translate] using h'
  exact PlacedTile.ext hp.1 hp.2

private lemma dissection_preserves_sts_sofic_step1_local_rule_side_translate
    (A : PlacedTile P) (v : Pt) (i : Fin (P.disk A.form).n) :
    (A.translate v).side i = v +ᵥ A.side i := by
  show (v +ᵥ A.anchor) +ᵥ _ = v +ᵥ (A.anchor +ᵥ _)
  rw [vadd_vadd]
  rfl

private lemma dissection_preserves_sts_sofic_step1_local_rule_vadd_set_injective
    (v : Pt) : Function.Injective (fun s : Set Pt => v +ᵥ s) := by
  intro s t h
  ext x
  have hx := Set.ext_iff.mp h (v +ᵥ x)
  rwa [vadd_mem_vadd_set_iff, vadd_mem_vadd_set_iff] at hx

private lemma dissection_preserves_sts_sofic_step1_local_rule_overlap_vadd
    (v : Pt) {s t : Set Pt} (h : OverlapPos s t) :
    OverlapPos (v +ᵥ s) (v +ᵥ t) := by
  obtain ⟨x, y, hxy, hseg⟩ := h
  refine ⟨v +ᵥ x, v +ᵥ y, fun h => hxy (add_left_cancel h), ?_⟩
  rw [← vadd_segment]
  rintro z ⟨w, hw, rfl⟩
  exact ⟨⟨w, (hseg hw).1, rfl⟩, ⟨w, (hseg hw).2, rfl⟩⟩

private lemma dissection_preserves_sts_sofic_step1_local_rule_side_rule_bad_translate
    (dec : SideDecoration P) (A B : PlacedTile dec.P') (v : Pt)
    (h : dissection_preserves_sts_sofic_step1_local_rule_side_rule_bad dec A B) :
    dissection_preserves_sts_sofic_step1_local_rule_side_rule_bad dec
      (A.translate v) (B.translate v) := by
  obtain ⟨i, j, hbad | hbad⟩ := h
  · refine ⟨i, j, Or.inl ⟨?_, ?_⟩⟩
    · rw [dissection_preserves_sts_sofic_step1_local_rule_side_translate,
        dissection_preserves_sts_sofic_step1_local_rule_side_translate]
      exact dissection_preserves_sts_sofic_step1_local_rule_overlap_vadd v hbad.1
    · rw [dissection_preserves_sts_sofic_step1_local_rule_side_translate,
        dissection_preserves_sts_sofic_step1_local_rule_side_translate]
      exact fun heq => hbad.2
        (dissection_preserves_sts_sofic_step1_local_rule_vadd_set_injective v heq)
  · refine ⟨i, j, Or.inr ⟨?_, ?_, hbad.2.2⟩⟩
    · intro heq
      exact hbad.1
        (dissection_preserves_sts_sofic_step1_local_rule_translate_tile_injective v heq)
    rw [dissection_preserves_sts_sofic_step1_local_rule_side_translate,
      dissection_preserves_sts_sofic_step1_local_rule_side_translate, hbad.2.1]

private lemma dissection_preserves_sts_sofic_step1_local_rule_translate_set_zero
    (S : Set (PlacedTile P)) : translateSet 0 S = S := by
  ext A
  constructor
  · rintro ⟨B, hB, rfl⟩
    simpa [dissection_preserves_sts_sofic_step1_local_rule_translate_tile_zero] using hB
  · intro hA
    exact ⟨A, hA, dissection_preserves_sts_sofic_step1_local_rule_translate_tile_zero A⟩

private lemma dissection_preserves_sts_sofic_step1_local_rule_proper_iff
    (dec : SideDecoration P) (T : PlaneTiling dec.P') :
    (dissection_preserves_sts_sofic_step1_local_rule_local_rule dec).Proper T ↔
      dec.Proper T := by
  constructor
  · intro h
    constructor
    · intro A hA B hB i j hover
      by_contra hne
      apply h {A, B} ⟨A, B, rfl, i, j, Or.inl ⟨hover, hne⟩⟩
      refine ⟨0, ?_⟩
      rw [dissection_preserves_sts_sofic_step1_local_rule_translate_set_zero]
      intro X hX
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl
      · exact hA
      · exact hB
    · intro A hA B hB hAB i j hsides
      by_contra hcol
      apply h {A, B} ⟨A, B, rfl, i, j, Or.inr ⟨hAB, hsides, hcol⟩⟩
      refine ⟨0, ?_⟩
      rw [dissection_preserves_sts_sofic_step1_local_rule_translate_set_zero]
      intro X hX
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
      rcases hX with rfl | rfl
      · exact hA
      · exact hB
  · rintro ⟨hsts, hcol⟩ F ⟨A, B, rfl, hbad⟩ ⟨v, hv⟩
    have hAv : A.translate v ∈ T.tiles := hv (by simp [translateSet])
    have hBv : B.translate v ∈ T.tiles := hv (by simp [translateSet])
    obtain ⟨i, j, hbad | hbad⟩ :=
      dissection_preserves_sts_sofic_step1_local_rule_side_rule_bad_translate dec A B v hbad
    · exact hbad.2 (hsts _ hAv _ hBv i j hbad.1)
    · exact hbad.2.2 (hcol _ hAv _ hBv hbad.1 i j hbad.2.1)

/-- Step 1 of the blueprint proof of `dissection_preserves_sts_sofic`: encode
    the finite side-matching conditions of a side decoration by a bounded local
    rule, so its proper tilings are exactly its side-proper tilings. -/
private theorem dissection_preserves_sts_sofic_step1_local_rule
    (dec : SideDecoration P) :
    ∃ R : LocalRule dec.P', ∀ T, R.Proper T ↔ dec.Proper T := by
  exact ⟨dissection_preserves_sts_sofic_step1_local_rule_local_rule dec,
    fun T => dissection_preserves_sts_sofic_step1_local_rule_proper_iff dec T⟩

/-- Step 1 of the blueprint proof of `dissection_preserves_sts_sofic_step2_scatter_sts`: within-group case using the grouped family's STS field. -/
private lemma dissection_preserves_sts_sofic_step2_scatter_sts_step1_same_group
    {P : Protoset}
    (G : GroupedFamily P) (dec : SideDecoration G.P')
    (T : PlaneTiling dec.P') (hT : dec.Proper T)
    (A B : PlacedTile P) (A' : PlacedTile G.P')
    (hA' : A' ∈ (dec.toDecoration.project T).tiles)
    (hA : A ∈ G.scatterTile A')
    (hB : B ∈ G.scatterTile A')
    (i : Fin (P.disk A.form).n) (j : Fin (P.disk B.form).n)
    (h_overlap : OverlapPos (A.side i) (B.side j)) :
    A.side i = B.side j := by
  have _ := hT; have _ := hA'
  rcases hA with ⟨A₀, hA₀, rfl⟩
  rcases hB with ⟨B₀, hB₀, rfl⟩
  have h_overlap₀ : OverlapPos (A₀.side i) (B₀.side j) := by
    rw [dissection_preserves_sts_sofic_step1_local_rule_side_translate,
      dissection_preserves_sts_sofic_step1_local_rule_side_translate] at h_overlap
    simpa [vadd_vadd] using
      (dissection_preserves_sts_sofic_step1_local_rule_overlap_vadd
        (-A'.anchor) h_overlap)
  have hEq := G.sts A'.form A₀ hA₀ B₀ hB₀ i j h_overlap₀
  rw [dissection_preserves_sts_sofic_step1_local_rule_side_translate,
    dissection_preserves_sts_sofic_step1_local_rule_side_translate]
  exact congrArg (fun s : Set Pt => A'.anchor +ᵥ s) hEq

/-- Step 2 of the blueprint proof of `dissection_preserves_sts_sofic_step2_scatter_sts`:
    cross-group case using complete grouped sides and the STS property of the projected
    decorated tiling. -/
private lemma dissection_preserves_sts_sofic_step2_scatter_sts_step2_diff_group
    {P : Protoset}
    (G : GroupedFamily P) (dec : SideDecoration G.P')
    (T : PlaneTiling dec.P') (hT : dec.Proper T)
    (A B : PlacedTile P) (A' B' : PlacedTile G.P')
    (hA' : A' ∈ (dec.toDecoration.project T).tiles)
    (hB' : B' ∈ (dec.toDecoration.project T).tiles)
    (h_neq : A' ≠ B')
    (hA : A ∈ G.scatterTile A')
    (hB : B ∈ G.scatterTile B')
    (i : Fin (P.disk A.form).n) (j : Fin (P.disk B.form).n)
    (h_overlap : OverlapPos (A.side i) (B.side j)) :
    A.side i = B.side j :=
  Alignment.dissect_cross_group_sideToSide G dec T hT A' hA' B' hB' h_neq A hA B hB i j h_overlap

/-- Step 2 of the blueprint proof of `dissection_preserves_sts_sofic`: scattering
    a proper side-decoration tiling preserves the side-to-side property.  The
    within-group case uses the grouped family's STS field; the cross-group case
    uses complete grouped sides and the side-to-side property of the projected
    decorated tiling. -/
private theorem dissection_preserves_sts_sofic_step2_scatter_sts
    (G : GroupedFamily P) (dec : SideDecoration G.P')
    (T : PlaneTiling dec.P') (hT : dec.Proper T) :
    SideToSideSet (G.scatter (dec.toDecoration.project T).tiles) := by
  intro A hA B hB i j hoverlap
  simp only [GroupedFamily.scatter, Set.mem_iUnion] at hA hB
  rcases hA with ⟨A', hA', hA⟩
  rcases hB with ⟨B', hB', hB⟩
  by_cases hAB : A' = B'
  · rcases hAB with rfl
    exact dissection_preserves_sts_sofic_step2_scatter_sts_step1_same_group G dec T hT A B A' hA' hA hB i j hoverlap
  · exact dissection_preserves_sts_sofic_step2_scatter_sts_step2_diff_group G dec T hT A B A' B' hA' hB' hAB hA hB i j hoverlap

/-- `lem:glues` (strict presentations): the same transfer for side-to-side
sofic presentations; grouped sides are complete original sides, so exposed
colours stay on whole original sides. -/
theorem Decoration.dissection_preserves_sts_sofic (G : GroupedFamily P)
    {F' : Set (PlaneTiling G.P')} (h : IsSideToSideSofic F') :
    IsSideToSideSofic (G.scatterFamily F') := by
  obtain ⟨dec, hdec⟩ := h
  obtain ⟨R, hR⟩ := dissection_preserves_sts_sofic_step1_local_rule dec
  have hsofic : IsSofic F' :=
    ⟨dec.toDecoration, R, fun T' => by
      constructor
      · intro hT'
        obtain ⟨T, hproper, hproject⟩ := (hdec T').mp hT'
        exact ⟨T, (hR T).mpr hproper, hproject⟩
      · rintro ⟨T, hproper, hproject⟩
        exact (hdec T').mpr ⟨T, (hR T).mp hproper, hproject⟩⟩
  apply LocalRule.side_presentation_of_sts_sofic
    (Decoration.dissection_preserves_sofic G hsofic)
  intro T hT
  obtain ⟨T', hT'F, hscatter⟩ := hT
  obtain ⟨Tdec, hproper, hproject⟩ := (hdec T').mp hT'F
  change SideToSideSet T.tiles
  rw [← hscatter, ← hproject]
  exact dissection_preserves_sts_sofic_step2_scatter_sts G dec Tdec hproper

/-! ## Compatible grouped hierarchy lift (`lem:grouping-lift`) -/

/-- `T` is the bottom of a `τ^k`-hierarchy of plane tilings. -/
def Grouping.IsPowerHierarchy (τ : Substitution P) (k : ℕ) (T : PlaneTiling P) : Prop :=
  ∃ seq : ℕ → PlaneTiling P, seq 0 = T ∧ ∀ n, τ.decomposeIter k (seq (n + 1)).tiles = (seq n).tiles

/-! ### Compactness helpers for `hierarchy_lift_iff` -/

private lemma hierarchy_lift_iff_decomposeTile_carrier (τ : Substitution P)
    (A : PlacedTile P) :
    support (τ.decomposeTile A) = τ.θ • A.carrier := by
  dsimp [Substitution.decomposeTile]
  rw [cc_support_translate, τ.support_eq, PlacedTile.carrier]
  ext x
  simp only [mem_vadd_set_iff_neg_vadd_mem, mem_smul_set]
  constructor
  · rintro ⟨y, hy, hx⟩
    refine ⟨A.anchor + y, ?_, ?_⟩
    · simpa
    · rw [smul_add]
      calc
        τ.θ • A.anchor + τ.θ • y = τ.θ • A.anchor + (-(τ.θ • A.anchor) + x) := by
          congr 1
        _ = x := by abel
  · rintro ⟨y, hy, rfl⟩
    refine ⟨-A.anchor + y, ?_, ?_⟩
    · simpa
    · simp [smul_add]

private lemma hierarchy_lift_iff_decompose_support (τ : Substitution P)
    (S : Set (PlacedTile P)) :
    support (τ.decompose S) = τ.θ • support S := by
  dsimp [Substitution.decompose, support]
  rw [smul_set_iUnion₂]
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨C, ⟨A, hAS, hCA⟩, hx⟩
    refine ⟨A, hAS, ?_⟩
    have h : x ∈ support (τ.decomposeTile A) := by
      simp only [support, Set.mem_iUnion]
      exact ⟨C, hCA, hx⟩
    rw [hierarchy_lift_iff_decomposeTile_carrier] at h
    exact h
  · rintro ⟨A, hAS, hx⟩
    have h : x ∈ support (τ.decomposeTile A) := by
      rw [hierarchy_lift_iff_decomposeTile_carrier]
      exact hx
    simp only [support, Set.mem_iUnion] at h
    rcases h with ⟨C, hC, hx'⟩
    exact ⟨C, ⟨A, hAS, hC⟩, hx'⟩

private noncomputable def hierarchy_lift_iff_decomposeTiling (τ : Substitution P)
    (T : PlaneTiling P) : PlaneTiling P where
  tiles := τ.decompose T.tiles
  cover := by
    rw [hierarchy_lift_iff_decompose_support, T.cover]
    have hθ : τ.θ ≠ 0 := by linarith [τ.one_lt]
    ext x
    constructor
    · intro
      trivial
    · intro
      exact ⟨τ.θ⁻¹ • x, trivial, by simp [hθ]⟩
  disjoint := by
    intro C hC D hD hCD
    simp only [Substitution.decompose, Set.mem_iUnion] at hC hD
    obtain ⟨A, hAT, hCA⟩ := hC
    obtain ⟨B, hBT, hDB⟩ := hD
    by_cases hAB : A = B
    · subst B
      simp only [Substitution.decomposeTile, translateSet, Set.mem_image] at hCA hDB
      obtain ⟨C₀, hC₀, rfl⟩ := hCA
      obtain ⟨D₀, hD₀, hDeq⟩ := hDB
      subst D
      have hC₀D₀ : C₀ ≠ D₀ := by
        intro h
        apply hCD
        rw [h]
      have hd := (τ.rule A.form).disjoint hC₀ hD₀ hC₀D₀
      dsimp [Function.onFun] at hd ⊢
      rw [dissection_preserves_sofic_carrier_translate,
        dissection_preserves_sofic_carrier_translate, interior_vadd, interior_vadd]
      exact disjoint_image_of_injective (add_right_injective (τ.θ • A.anchor)) hd
    · have hθ : τ.θ ≠ 0 := by linarith [τ.one_lt]
      have hCsub : interior C.carrier ⊆ interior (τ.θ • A.carrier) := by
        apply interior_maximal
        · have hsub : C.carrier ⊆ support (τ.decomposeTile A) := by
            intro x hx
            simp only [support, Set.mem_iUnion]
            exact ⟨C, hCA, hx⟩
          rw [hierarchy_lift_iff_decomposeTile_carrier] at hsub
          exact interior_subset.trans hsub
        · exact isOpen_interior
      have hDsub : interior D.carrier ⊆ interior (τ.θ • B.carrier) := by
        apply interior_maximal
        · have hsub : D.carrier ⊆ support (τ.decomposeTile B) := by
            intro x hx
            simp only [support, Set.mem_iUnion]
            exact ⟨D, hDB, hx⟩
          rw [hierarchy_lift_iff_decomposeTile_carrier] at hsub
          exact interior_subset.trans hsub
        · exact isOpen_interior
      apply (disjoint_image_of_injective (smul_right_injective Pt hθ)
        (T.disjoint hAT hBT hAB)).mono
      · simpa only [interior_smul₀ hθ] using hCsub
      · simpa only [interior_smul₀ hθ] using hDsub

private def hierarchy_lift_iff_decomposeIterTiling (τ : Substitution P) :
    ℕ → PlaneTiling P → PlaneTiling P
  | 0, T => T
  | n + 1, T => hierarchy_lift_iff_decomposeTiling τ
      (hierarchy_lift_iff_decomposeIterTiling τ n T)

private lemma hierarchy_lift_iff_decomposeIterTiling_tiles (τ : Substitution P)
    (n : ℕ) (T : PlaneTiling P) :
    (hierarchy_lift_iff_decomposeIterTiling τ n T).tiles =
      τ.decomposeIter n T.tiles := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change τ.decompose (hierarchy_lift_iff_decomposeIterTiling τ n T).tiles = _
      rw [ih]
      rfl

private lemma hierarchy_lift_iff_scatterTile_support (G : GroupedFamily P)
    (A : PlacedTile G.P') : support (G.scatterTile A) = A.carrier := by
  rw [GroupedFamily.scatterTile, cc_support_translate, G.support_eq]
  rfl

private lemma hierarchy_lift_iff_scatter_support (G : GroupedFamily P)
    (S : Set (PlacedTile G.P')) : support (G.scatter S) = support S := by
  ext x
  simp only [GroupedFamily.scatter, support, Set.mem_iUnion]
  constructor
  · rintro ⟨B, ⟨A, hAS, hBA⟩, hxB⟩
    refine ⟨A, hAS, ?_⟩
    rw [← hierarchy_lift_iff_scatterTile_support G A]
    simp only [support, Set.mem_iUnion]
    exact ⟨B, hBA, hxB⟩
  · rintro ⟨A, hAS, hxA⟩
    rw [← hierarchy_lift_iff_scatterTile_support G A] at hxA
    simp only [support, Set.mem_iUnion] at hxA
    rcases hxA with ⟨B, hBA, hxB⟩
    exact ⟨B, ⟨A, hAS, hBA⟩, hxB⟩

private lemma hierarchy_lift_iff_scatter_translate (G : GroupedFamily P)
    (v : Pt) (S : Set (PlacedTile G.P')) :
    G.scatter (translateSet v S) = translateSet v (G.scatter S) := by
  ext B
  simp only [GroupedFamily.scatter, GroupedFamily.scatterTile, translateSet,
    Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨A, ⟨A₀, hA₀, rfl⟩, C, hC, rfl⟩
    refine ⟨C.translate A₀.anchor, ⟨A₀, hA₀, C, hC, rfl⟩, ?_⟩
    simp [PlacedTile.translate, add_assoc]
  · rintro ⟨B₀, ⟨A, hAS, C, hC, rfl⟩, rfl⟩
    refine ⟨A.translate v, ⟨A, hAS, rfl⟩, C, hC, ?_⟩
    simp [PlacedTile.translate, add_assoc]

private lemma hierarchy_lift_iff_decompose_translate (τ : Substitution P)
    (v : Pt) (S : Set (PlacedTile P)) :
    τ.decompose (translateSet v S) = translateSet (τ.θ • v) (τ.decompose S) := by
  ext C
  simp only [Substitution.decompose, Substitution.decomposeTile, translateSet,
    Set.mem_iUnion, Set.mem_image]
  constructor
  · rintro ⟨A, ⟨A₀, hA₀, rfl⟩, B, hB, rfl⟩
    refine ⟨B.translate (τ.θ • A₀.anchor), ⟨A₀, hA₀, B, hB, rfl⟩, ?_⟩
    apply PlacedTile.ext
    · rfl
    · simp only [PlacedTile.translate, vadd_eq_add, smul_add]
      abel
  · rintro ⟨C₀, ⟨A, hAS, B, hB, rfl⟩, rfl⟩
    refine ⟨A.translate v, ⟨A, hAS, rfl⟩, B, hB, ?_⟩
    apply PlacedTile.ext
    · rfl
    · simp only [PlacedTile.translate, vadd_eq_add, smul_add]
      abel

private lemma hierarchy_lift_iff_decomposeIter_translate (τ : Substitution P)
    (n : ℕ) (v : Pt) (S : Set (PlacedTile P)) :
    τ.decomposeIter n (translateSet v S) =
      translateSet (τ.θ ^ n • v) (τ.decomposeIter n S) := by
  induction n with
  | zero => simp [Substitution.decomposeIter]
  | succ n ih =>
      change τ.decompose (τ.decomposeIter n (translateSet v S)) = _
      rw [ih, hierarchy_lift_iff_decompose_translate]
      rw [pow_succ', mul_smul]
      rfl

private lemma hierarchy_lift_iff_decomposeIter_iUnion₂ (τ : Substitution P)
    {ι : Type*} (n : ℕ) (s : Set ι) (f : ι → Set (PlacedTile P)) :
    τ.decomposeIter n (⋃ i ∈ s, f i) = ⋃ i ∈ s, τ.decomposeIter n (f i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change τ.decompose (τ.decomposeIter n (⋃ i ∈ s, f i)) = _
      rw [ih]
      ext C
      simp only [Substitution.decompose, Set.mem_iUnion]
      constructor
      · rintro ⟨B, ⟨i, hi, hB⟩, hCB⟩
        refine ⟨i, hi, ?_⟩
        change C ∈ τ.decompose (τ.decomposeIter n (f i))
        simp only [Substitution.decompose, Set.mem_iUnion]
        exact ⟨B, hB, hCB⟩
      · rintro ⟨i, hi, hC⟩
        change C ∈ τ.decompose (τ.decomposeIter n (f i)) at hC
        simp only [Substitution.decompose, Set.mem_iUnion] at hC
        rcases hC with ⟨B, hB, hCB⟩
        exact ⟨B, ⟨i, hi, hB⟩, hCB⟩

private lemma hierarchy_lift_iff_scatter_decomposeTile (τ : Substitution P)
    (GS : GroupedSubstitution τ) (A : PlacedTile GS.G.P') :
    GS.G.scatter (GS.σ.decomposeTile A) =
      τ.decomposeIter GS.k (GS.G.scatterTile A) := by
  rw [Substitution.decomposeTile, hierarchy_lift_iff_scatter_translate,
    GS.θ_eq, GS.compat, GroupedFamily.scatterTile,
    hierarchy_lift_iff_decomposeIter_translate]

private lemma hierarchy_lift_iff_scatter_decompose (τ : Substitution P)
    (GS : GroupedSubstitution τ) (S : Set (PlacedTile GS.G.P')) :
    GS.G.scatter (GS.σ.decompose S) =
      τ.decomposeIter GS.k (GS.G.scatter S) := by
  change GS.G.scatter (GS.σ.decompose S) =
    τ.decomposeIter GS.k (⋃ A ∈ S, GS.G.scatterTile A)
  rw [hierarchy_lift_iff_decomposeIter_iUnion₂]
  ext B
  simp only [Substitution.decompose, GroupedFamily.scatter, Set.mem_iUnion]
  constructor
  · rintro ⟨C, ⟨A, hAS, hCA⟩, hBC⟩
    refine ⟨A, hAS, ?_⟩
    rw [← hierarchy_lift_iff_scatter_decomposeTile τ GS A]
    simp only [GroupedFamily.scatter, Set.mem_iUnion]
    exact ⟨C, hCA, hBC⟩
  · rintro ⟨A, hAS, hBA⟩
    rw [← hierarchy_lift_iff_scatter_decomposeTile τ GS A] at hBA
    simp only [GroupedFamily.scatter, Set.mem_iUnion] at hBA
    rcases hBA with ⟨C, hC, hBC⟩
    exact ⟨C, ⟨A, hAS, hC⟩, hBC⟩

private noncomputable def hierarchy_lift_iff_singleForm {τ : Substitution P}
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩}) :
    P.Form → GS.G.P'.Form := fun p => (hsingle p).choose

private lemma hierarchy_lift_iff_singleForm_spec {τ : Substitution P}
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩}) (p : P.Form) :
    (GS.G.dissect (hierarchy_lift_iff_singleForm GS hsingle p)).tiles = {⟨p, 0⟩} :=
  (hsingle p).choose_spec

private noncomputable def hierarchy_lift_iff_singleTile {τ : Substitution P}
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (A : PlacedTile P) : PlacedTile GS.G.P' :=
  ⟨hierarchy_lift_iff_singleForm GS hsingle A.form, A.anchor⟩

private lemma hierarchy_lift_iff_singleTile_scatter {τ : Substitution P}
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (A : PlacedTile P) :
    GS.G.scatterTile (hierarchy_lift_iff_singleTile GS hsingle A) = {A} := by
  simp only [GroupedFamily.scatterTile, hierarchy_lift_iff_singleTile,
    hierarchy_lift_iff_singleForm_spec, translateSet, Set.image_singleton]
  congr 1
  apply PlacedTile.ext
  · rfl
  · simp [PlacedTile.translate]

private lemma hierarchy_lift_iff_singleTile_injective {τ : Substitution P}
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩}) :
    Function.Injective (hierarchy_lift_iff_singleTile GS hsingle) := by
  intro A B hAB
  have h := congrArg GS.G.scatterTile hAB
  rw [hierarchy_lift_iff_singleTile_scatter, hierarchy_lift_iff_singleTile_scatter] at h
  exact Set.singleton_eq_singleton_iff.mp h

private lemma hierarchy_lift_iff_singleTile_carrier {τ : Substitution P}
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (A : PlacedTile P) :
    (hierarchy_lift_iff_singleTile GS hsingle A).carrier = A.carrier := by
  rw [← hierarchy_lift_iff_scatterTile_support,
    hierarchy_lift_iff_singleTile_scatter]
  simp [support]

private noncomputable def hierarchy_lift_iff_singleTiling {τ : Substitution P}
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (T : PlaneTiling P) : PlaneTiling GS.G.P' where
  tiles := hierarchy_lift_iff_singleTile GS hsingle '' T.tiles
  cover := by
    calc
      support (hierarchy_lift_iff_singleTile GS hsingle '' T.tiles) = support T.tiles := by
        ext x
        simp only [support, Set.mem_iUnion, Set.mem_image]
        constructor
        · rintro ⟨B, ⟨A, hAT, rfl⟩, hxB⟩
          exact ⟨A, hAT, by rwa [hierarchy_lift_iff_singleTile_carrier] at hxB⟩
        · rintro ⟨A, hAT, hxA⟩
          exact ⟨hierarchy_lift_iff_singleTile GS hsingle A, ⟨A, hAT, rfl⟩, by
            rwa [hierarchy_lift_iff_singleTile_carrier]⟩
      _ = Set.univ := T.cover
  disjoint := by
    rintro A ⟨A₀, hA₀, rfl⟩ B ⟨B₀, hB₀, rfl⟩ hAB
    have hA₀B₀ : A₀ ≠ B₀ := fun h => hAB (congrArg _ h)
    dsimp [Function.onFun]
    rw [hierarchy_lift_iff_singleTile_carrier, hierarchy_lift_iff_singleTile_carrier]
    exact T.disjoint hA₀ hB₀ hA₀B₀

private lemma hierarchy_lift_iff_singleTiling_scatter {τ : Substitution P}
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (T : PlaneTiling P) :
    GS.G.scatter (hierarchy_lift_iff_singleTiling GS hsingle T).tiles = T.tiles := by
  ext A
  simp only [hierarchy_lift_iff_singleTiling, GroupedFamily.scatter, Set.mem_iUnion,
    Set.mem_image]
  constructor
  · rintro ⟨B, ⟨C, hCT, rfl⟩, hAB⟩
    rw [hierarchy_lift_iff_singleTile_scatter] at hAB
    rw [Set.mem_singleton_iff] at hAB
    simpa [hAB] using hCT
  · intro hAT
    exact ⟨hierarchy_lift_iff_singleTile GS hsingle A, ⟨A, hAT, rfl⟩, by
      rw [hierarchy_lift_iff_singleTile_scatter]
      rfl⟩

private lemma hierarchy_lift_iff_finiteHeight_scatter (τ : Substitution P)
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (n d : ℕ) :
    GS.G.scatter
        (hierarchy_lift_iff_decomposeIterTiling GS.σ d
          (hierarchy_lift_iff_singleTiling GS hsingle (seq (n + d)))).tiles =
      (seq n).tiles := by
  induction d generalizing n with
  | zero =>
      simpa using hierarchy_lift_iff_singleTiling_scatter GS hsingle (seq n)
  | succ d ih =>
      change GS.G.scatter
          (GS.σ.decompose
            (hierarchy_lift_iff_decomposeIterTiling GS.σ d
              (hierarchy_lift_iff_singleTiling GS hsingle (seq (n + (d + 1))))).tiles) = _
      rw [hierarchy_lift_iff_scatter_decompose]
      have hind := ih (n + 1)
      have htop : n + (d + 1) = n + 1 + d := by omega
      rw [htop, hind]
      exact hseq n

private noncomputable def hierarchy_lift_iff_approx {τ : Substitution P}
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P) (H n : ℕ) : PlaneTiling GS.G.P' :=
  if n ≤ H then
    hierarchy_lift_iff_decomposeIterTiling GS.σ (H - n)
      (hierarchy_lift_iff_singleTiling GS hsingle (seq H))
  else
    hierarchy_lift_iff_singleTiling GS hsingle (seq n)

private lemma hierarchy_lift_iff_approx_scatter (τ : Substitution P)
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (H n : ℕ) :
    GS.G.scatter (hierarchy_lift_iff_approx GS hsingle seq H n).tiles = (seq n).tiles := by
  by_cases hnH : n ≤ H
  · rw [hierarchy_lift_iff_approx, if_pos hnH]
    have hH : H = n + (H - n) := by omega
    conv_lhs =>
      congr
      rw [hH]
    simpa only [Nat.add_sub_cancel_left] using
      hierarchy_lift_iff_finiteHeight_scatter τ GS hsingle seq hseq n (H - n)
  · rw [hierarchy_lift_iff_approx, if_neg hnH]
    exact hierarchy_lift_iff_singleTiling_scatter GS hsingle (seq n)

private lemma hierarchy_lift_iff_approx_comp {τ : Substitution P}
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P) (H n : ℕ) (hnH : n + 1 ≤ H) :
    GS.σ.decompose (hierarchy_lift_iff_approx GS hsingle seq H (n + 1)).tiles =
      (hierarchy_lift_iff_approx GS hsingle seq H n).tiles := by
  have hnH' : n ≤ H := by omega
  rw [hierarchy_lift_iff_approx, if_pos hnH, hierarchy_lift_iff_approx, if_pos hnH']
  rw [hierarchy_lift_iff_decomposeIterTiling_tiles,
    hierarchy_lift_iff_decomposeIterTiling_tiles]
  have hsub : H - n = (H - (n + 1)) + 1 := by omega
  rw [hsub]
  rfl

private lemma hierarchy_lift_iff_scatter_owner_unique (G : GroupedFamily P)
    (T : PlaneTiling G.P') {B : PlacedTile P} {A C : PlacedTile G.P'}
    (hAT : A ∈ T.tiles) (hCT : C ∈ T.tiles)
    (hBA : B ∈ G.scatterTile A) (hBC : B ∈ G.scatterTile C) : A = C := by
  by_contra hAC
  have hBAsub : B.carrier ⊆ A.carrier := by
    rw [← hierarchy_lift_iff_scatterTile_support G A]
    intro x hx
    simp only [support, Set.mem_iUnion]
    exact ⟨B, hBA, hx⟩
  have hBCsub : B.carrier ⊆ C.carrier := by
    rw [← hierarchy_lift_iff_scatterTile_support G C]
    intro x hx
    simp only [support, Set.mem_iUnion]
    exact ⟨B, hBC, hx⟩
  have hiA : interior B.carrier ⊆ interior A.carrier :=
    interior_maximal (interior_subset.trans hBAsub) isOpen_interior
  have hiC : interior B.carrier ⊆ interior C.carrier :=
    interior_maximal (interior_subset.trans hBCsub) isOpen_interior
  obtain ⟨x, hx⟩ := (P.disk B.form).interior_nonempty
  have hxB : B.anchor +ᵥ x ∈ interior B.carrier := by
    rw [PlacedTile.carrier, interior_vadd]
    exact vadd_mem_vadd_set hx
  exact Set.disjoint_left.mp (T.disjoint hAT hCT hAC) (hiA hxB) (hiC hxB)

private lemma hierarchy_lift_iff_scatter_parents_finite (G : GroupedFamily P)
    (B : PlacedTile P) : {A : PlacedTile G.P' | B ∈ G.scatterTile A}.Finite := by
  let choices : Set (PlacedTile G.P') :=
    ⋃ α : G.P'.Form, ⋃ C ∈ (G.dissect α).tiles,
      ({⟨α, B.anchor - C.anchor⟩} : Set (PlacedTile G.P'))
  have hchoices : choices.Finite := by
    apply Set.finite_iUnion
    intro α
    apply Set.Finite.biUnion (G.dissect α).finite
    intro C hC
    exact Set.finite_singleton _
  apply hchoices.subset
  intro A hBA
  simp only [GroupedFamily.scatterTile, translateSet, Set.mem_image] at hBA
  obtain ⟨C, hC, hCB⟩ := hBA
  simp only [choices, Set.mem_iUnion, Set.mem_singleton_iff]
  refine ⟨A.form, C, hC, ?_⟩
  have hanchor : A.anchor = B.anchor - C.anchor := by
    have h := congrArg PlacedTile.anchor hCB
    simp only [PlacedTile.translate, vadd_eq_add] at h
    rw [← h]
    abel
  exact PlacedTile.ext rfl hanchor

private noncomputable def hierarchy_lift_iff_owner (τ : Substitution P)
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (H n : ℕ) (B : (seq n).tiles) : PlacedTile GS.G.P' :=
  (show ∃ A ∈ (hierarchy_lift_iff_approx GS hsingle seq H n).tiles,
      B.1 ∈ GS.G.scatterTile A by
    have hB : B.1 ∈ GS.G.scatter (hierarchy_lift_iff_approx GS hsingle seq H n).tiles := by
      rw [hierarchy_lift_iff_approx_scatter τ GS hsingle seq hseq H n]
      exact B.2
    simp only [GroupedFamily.scatter, Set.mem_iUnion] at hB
    rcases hB with ⟨A, hA, hBA⟩
    exact ⟨A, hA, hBA⟩).choose

private lemma hierarchy_lift_iff_owner_mem (τ : Substitution P)
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (H n : ℕ) (B : (seq n).tiles) :
    hierarchy_lift_iff_owner τ GS hsingle seq hseq H n B ∈
      (hierarchy_lift_iff_approx GS hsingle seq H n).tiles :=
  (show ∃ A ∈ (hierarchy_lift_iff_approx GS hsingle seq H n).tiles,
      B.1 ∈ GS.G.scatterTile A by
    have hB : B.1 ∈ GS.G.scatter (hierarchy_lift_iff_approx GS hsingle seq H n).tiles := by
      rw [hierarchy_lift_iff_approx_scatter τ GS hsingle seq hseq H n]
      exact B.2
    simp only [GroupedFamily.scatter, Set.mem_iUnion] at hB
    rcases hB with ⟨A, hA, hBA⟩
    exact ⟨A, hA, hBA⟩).choose_spec.1

private lemma hierarchy_lift_iff_owner_scatter (τ : Substitution P)
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (H n : ℕ) (B : (seq n).tiles) :
    B.1 ∈ GS.G.scatterTile (hierarchy_lift_iff_owner τ GS hsingle seq hseq H n B) :=
  (show ∃ A ∈ (hierarchy_lift_iff_approx GS hsingle seq H n).tiles,
      B.1 ∈ GS.G.scatterTile A by
    have hB : B.1 ∈ GS.G.scatter (hierarchy_lift_iff_approx GS hsingle seq H n).tiles := by
      rw [hierarchy_lift_iff_approx_scatter τ GS hsingle seq hseq H n]
      exact B.2
    simp only [GroupedFamily.scatter, Set.mem_iUnion] at hB
    rcases hB with ⟨A, hA, hBA⟩
    exact ⟨A, hA, hBA⟩).choose_spec.2

private noncomputable def hierarchy_lift_iff_heightFilter : Ultrafilter ℕ :=
  Ultrafilter.of Filter.atTop

private lemma hierarchy_lift_iff_owner_eventually_constant (τ : Substitution P)
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (n : ℕ) (B : (seq n).tiles) :
    ∃ A : PlacedTile GS.G.P',
      ∀ᶠ H in hierarchy_lift_iff_heightFilter,
        hierarchy_lift_iff_owner τ GS hsingle seq hseq H n B = A := by
  let candidates := {A : PlacedTile GS.G.P' | B.1 ∈ GS.G.scatterTile A}
  letI : Finite candidates := (hierarchy_lift_iff_scatter_parents_finite GS.G B.1).to_subtype
  let owner : ℕ → candidates := fun H =>
    ⟨hierarchy_lift_iff_owner τ GS hsingle seq hseq H n B,
      hierarchy_lift_iff_owner_scatter τ GS hsingle seq hseq H n B⟩
  have hconst : ∃ A : candidates,
      ∀ᶠ H in hierarchy_lift_iff_heightFilter, owner H = A := by
    apply (Ultrafilter.eventually_exists_iff (f := hierarchy_lift_iff_heightFilter)).mp
    exact Filter.Eventually.of_forall fun H => ⟨owner H, rfl⟩
  obtain ⟨A, hA⟩ := hconst
  exact ⟨A.1, hA.mono fun H h => congrArg Subtype.val h⟩

private noncomputable def hierarchy_lift_iff_selectedOwner (τ : Substitution P)
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (n : ℕ) (B : (seq n).tiles) : PlacedTile GS.G.P' :=
  (hierarchy_lift_iff_owner_eventually_constant τ GS hsingle seq hseq n B).choose

private lemma hierarchy_lift_iff_selectedOwner_eventually (τ : Substitution P)
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (n : ℕ) (B : (seq n).tiles) :
    ∀ᶠ H in hierarchy_lift_iff_heightFilter,
      hierarchy_lift_iff_owner τ GS hsingle seq hseq H n B =
        hierarchy_lift_iff_selectedOwner τ GS hsingle seq hseq n B :=
  (hierarchy_lift_iff_owner_eventually_constant τ GS hsingle seq hseq n B).choose_spec

private lemma hierarchy_lift_iff_selectedOwner_scatter (τ : Substitution P)
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (n : ℕ) (B : (seq n).tiles) :
    B.1 ∈ GS.G.scatterTile
      (hierarchy_lift_iff_selectedOwner τ GS hsingle seq hseq n B) := by
  obtain ⟨H, hH⟩ :=
    (hierarchy_lift_iff_selectedOwner_eventually τ GS hsingle seq hseq n B).exists
  rw [← hH]
  exact hierarchy_lift_iff_owner_scatter τ GS hsingle seq hseq H n B

private noncomputable def hierarchy_lift_iff_selectedTiles (τ : Substitution P)
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (n : ℕ) : Set (PlacedTile GS.G.P') :=
  Set.range (hierarchy_lift_iff_selectedOwner τ GS hsingle seq hseq n)

private lemma hierarchy_lift_iff_selected_scatter (τ : Substitution P)
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (n : ℕ) :
    GS.G.scatter (hierarchy_lift_iff_selectedTiles τ GS hsingle seq hseq n) =
      (seq n).tiles := by
  ext B
  simp only [GroupedFamily.scatter, hierarchy_lift_iff_selectedTiles,
    Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro ⟨A, ⟨C, rfl⟩, hBA⟩
    obtain ⟨H, hH⟩ :=
      (hierarchy_lift_iff_selectedOwner_eventually τ GS hsingle seq hseq n C).exists
    have hAmem := hierarchy_lift_iff_owner_mem τ GS hsingle seq hseq H n C
    rw [hH] at hAmem
    have hB : B ∈ GS.G.scatter (hierarchy_lift_iff_approx GS hsingle seq H n).tiles := by
      simp only [GroupedFamily.scatter, Set.mem_iUnion]
      exact ⟨_, hAmem, hBA⟩
    rw [hierarchy_lift_iff_approx_scatter τ GS hsingle seq hseq H n] at hB
    exact hB
  · intro hB
    let B' : (seq n).tiles := ⟨B, hB⟩
    exact ⟨hierarchy_lift_iff_selectedOwner τ GS hsingle seq hseq n B',
      ⟨B', rfl⟩,
      hierarchy_lift_iff_selectedOwner_scatter τ GS hsingle seq hseq n B'⟩

private noncomputable def hierarchy_lift_iff_selectedTiling (τ : Substitution P)
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (n : ℕ) : PlaneTiling GS.G.P' where
  tiles := hierarchy_lift_iff_selectedTiles τ GS hsingle seq hseq n
  cover := by
    rw [← hierarchy_lift_iff_scatter_support,
      hierarchy_lift_iff_selected_scatter τ GS hsingle seq hseq n, (seq n).cover]
  disjoint := by
    rintro A ⟨B, rfl⟩ C ⟨D, rfl⟩ hAC
    have hB := hierarchy_lift_iff_selectedOwner_eventually τ GS hsingle seq hseq n B
    have hD := hierarchy_lift_iff_selectedOwner_eventually τ GS hsingle seq hseq n D
    obtain ⟨H, hHB, hHD⟩ := (hB.and hD).exists
    have hBm := hierarchy_lift_iff_owner_mem τ GS hsingle seq hseq H n B
    have hDm := hierarchy_lift_iff_owner_mem τ GS hsingle seq hseq H n D
    have hne : hierarchy_lift_iff_owner τ GS hsingle seq hseq H n B ≠
        hierarchy_lift_iff_owner τ GS hsingle seq hseq H n D := by
      intro h
      apply hAC
      rw [← hHB, ← hHD, h]
    have hd := (hierarchy_lift_iff_approx GS hsingle seq H n).disjoint hBm hDm hne
    rwa [hHB, hHD] at hd

private lemma hierarchy_lift_iff_scatterTile_nonempty (G : GroupedFamily P)
    (A : PlacedTile G.P') : (G.scatterTile A).Nonempty := by
  obtain ⟨x, hx⟩ := (G.P'.disk A.form).interior_nonempty
  have hxA : A.anchor +ᵥ x ∈ A.carrier := by
    exact vadd_mem_vadd_set (interior_subset hx)
  rw [← hierarchy_lift_iff_scatterTile_support G A] at hxA
  simp only [support, Set.mem_iUnion] at hxA
  rcases hxA with ⟨B, hBA, _⟩
  exact ⟨B, hBA⟩

private lemma hierarchy_lift_iff_eventually_height (m : ℕ) :
    ∀ᶠ H : ℕ in hierarchy_lift_iff_heightFilter, m ≤ H := by
  have h : ∀ᶠ H : ℕ in Filter.atTop, m ≤ H := by
    apply Filter.eventually_atTop.2
    exact ⟨m, fun H hH => hH⟩
  exact h.filter_mono (Ultrafilter.of_le Filter.atTop)

private lemma hierarchy_lift_iff_selected_comp_subset (τ : Substitution P)
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (n : ℕ) :
    GS.σ.decompose (hierarchy_lift_iff_selectedTiling τ GS hsingle seq hseq (n + 1)).tiles ⊆
      (hierarchy_lift_iff_selectedTiling τ GS hsingle seq hseq n).tiles := by
  intro C hC
  simp only [hierarchy_lift_iff_selectedTiling, Substitution.decompose,
    Set.mem_iUnion] at hC
  obtain ⟨A, hA, hCA⟩ := hC
  simp only [hierarchy_lift_iff_selectedTiles, Set.mem_range] at hA
  obtain ⟨E, rfl⟩ := hA
  obtain ⟨B, hBC⟩ := hierarchy_lift_iff_scatterTile_nonempty GS.G C
  have hBseq : B ∈ (seq n).tiles := by
    have hB : B ∈ GS.G.scatter
        (GS.σ.decompose
          (hierarchy_lift_iff_selectedTiling τ GS hsingle seq hseq (n + 1)).tiles) := by
      simp only [GroupedFamily.scatter, Set.mem_iUnion]
      exact ⟨C, by
        simp only [Substitution.decompose, Set.mem_iUnion]
        exact ⟨hierarchy_lift_iff_selectedOwner τ GS hsingle seq hseq (n + 1) E,
          ⟨E, rfl⟩, hCA⟩, hBC⟩
    rw [hierarchy_lift_iff_scatter_decompose] at hB
    change B ∈ τ.decomposeIter GS.k
      (GS.G.scatter (hierarchy_lift_iff_selectedTiles τ GS hsingle seq hseq (n + 1))) at hB
    rw [hierarchy_lift_iff_selected_scatter τ GS hsingle seq hseq (n + 1), hseq n] at hB
    exact hB
  let B' : (seq n).tiles := ⟨B, hBseq⟩
  have hEA := hierarchy_lift_iff_selectedOwner_eventually τ GS hsingle seq hseq (n + 1) E
  have hEB := hierarchy_lift_iff_selectedOwner_eventually τ GS hsingle seq hseq n B'
  have hEH := hierarchy_lift_iff_eventually_height (n + 1)
  obtain ⟨H, hHA, hHB, hnH⟩ := (hEA.and (hEB.and hEH)).exists
  have hAmem := hierarchy_lift_iff_owner_mem τ GS hsingle seq hseq H (n + 1) E
  rw [hHA] at hAmem
  have hCmem : C ∈ (hierarchy_lift_iff_approx GS hsingle seq H n).tiles := by
    rw [← hierarchy_lift_iff_approx_comp GS hsingle seq H n hnH]
    simp only [Substitution.decompose, Set.mem_iUnion]
    exact ⟨hierarchy_lift_iff_selectedOwner τ GS hsingle seq hseq (n + 1) E,
      hAmem, hCA⟩
  have hBmem := hierarchy_lift_iff_owner_mem τ GS hsingle seq hseq H n B'
  have hBscat := hierarchy_lift_iff_owner_scatter τ GS hsingle seq hseq H n B'
  have hownC := hierarchy_lift_iff_scatter_owner_unique GS.G
    (hierarchy_lift_iff_approx GS hsingle seq H n) hBmem hCmem hBscat hBC
  simp only [hierarchy_lift_iff_selectedTiling, hierarchy_lift_iff_selectedTiles,
    Set.mem_range]
  exact ⟨B', hHB.symm.trans hownC⟩

private lemma hierarchy_lift_iff_selected_comp (τ : Substitution P)
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (n : ℕ) :
    GS.σ.IsComposition
      (hierarchy_lift_iff_selectedTiling τ GS hsingle seq hseq (n + 1))
      (hierarchy_lift_iff_selectedTiling τ GS hsingle seq hseq n) := by
  exact dissection_preserves_sofic_tiling_maximal
    (hierarchy_lift_iff_decomposeTiling GS.σ
      (hierarchy_lift_iff_selectedTiling τ GS hsingle seq hseq (n + 1)))
    (hierarchy_lift_iff_selectedTiling τ GS hsingle seq hseq n)
    (hierarchy_lift_iff_selected_comp_subset τ GS hsingle seq hseq n)

private lemma hierarchy_lift_iff_liftSequence (τ : Substitution P)
    (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles) :
    ∃ seq' : ℕ → PlaneTiling GS.G.P',
      (∀ n, GS.σ.IsComposition (seq' (n + 1)) (seq' n)) ∧
      ∀ n, GS.G.scatter (seq' n).tiles = (seq n).tiles := by
  exact ⟨hierarchy_lift_iff_selectedTiling τ GS hsingle seq hseq,
    hierarchy_lift_iff_selected_comp τ GS hsingle seq hseq,
    hierarchy_lift_iff_selected_scatter τ GS hsingle seq hseq⟩

private noncomputable def hierarchy_lift_iff_scatterTiling (G : GroupedFamily P)
    (T : PlaneTiling G.P') : PlaneTiling P where
  tiles := G.scatter T.tiles
  cover := by
    rw [hierarchy_lift_iff_scatter_support, T.cover]
  disjoint := by
    intro B hB C hC hBC
    simp only [GroupedFamily.scatter, Set.mem_iUnion] at hB hC
    obtain ⟨A, hAT, hBA⟩ := hB
    obtain ⟨D, hDT, hCD⟩ := hC
    by_cases hAD : A = D
    · subst D
      simp only [GroupedFamily.scatterTile, translateSet, Set.mem_image] at hBA hCD
      obtain ⟨B₀, hB₀, rfl⟩ := hBA
      obtain ⟨C₀, hC₀, hCeq⟩ := hCD
      subst C
      have hB₀C₀ : B₀ ≠ C₀ := by
        intro h
        apply hBC
        rw [h]
      have hd := (G.dissect A.form).disjoint hB₀ hC₀ hB₀C₀
      dsimp [Function.onFun] at hd ⊢
      rw [dissection_preserves_sofic_carrier_translate,
        dissection_preserves_sofic_carrier_translate, interior_vadd, interior_vadd]
      exact disjoint_image_of_injective (add_right_injective A.anchor) hd
    · have hBsub : interior B.carrier ⊆ interior A.carrier := by
        apply interior_maximal
        · apply interior_subset.trans
          rw [← hierarchy_lift_iff_scatterTile_support G A]
          intro x hx
          simp only [support, Set.mem_iUnion]
          exact ⟨B, hBA, hx⟩
        · exact isOpen_interior
      have hCsub : interior C.carrier ⊆ interior D.carrier := by
        apply interior_maximal
        · apply interior_subset.trans
          rw [← hierarchy_lift_iff_scatterTile_support G D]
          intro x hx
          simp only [support, Set.mem_iUnion]
          exact ⟨C, hCD, hx⟩
        · exact isOpen_interior
      exact (T.disjoint hAT hDT hAD).mono hBsub hCsub

/-- `lem:grouping-lift`: when every original form is available as a
singleton group, original `τ^k`-hierarchies are exactly the scatterings of
grouped `σ`-hierarchies. -/
theorem Grouping.hierarchy_lift_iff (τ : Substitution P) (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩}) (T : PlaneTiling P) :
    Grouping.IsPowerHierarchy τ GS.k T ↔
      ∃ seq' : ℕ → PlaneTiling GS.G.P', (∀ n, GS.σ.IsComposition (seq' (n + 1)) (seq' n)) ∧
        GS.G.scatter (seq' 0).tiles = T.tiles := by
  constructor
  · rintro ⟨seq, hseq0, hseq⟩
    obtain ⟨seq', hcomp, hscatter⟩ :=
      hierarchy_lift_iff_liftSequence τ GS hsingle seq hseq
    refine ⟨seq', hcomp, ?_⟩
    rw [hscatter 0, hseq0]
  · rintro ⟨seq', hcomp, hscatter⟩
    let seq : ℕ → PlaneTiling P := fun n => hierarchy_lift_iff_scatterTiling GS.G (seq' n)
    refine ⟨seq, ?_, ?_⟩
    · apply dissection_preserves_sofic_PlaneTiling_ext
      exact hscatter
    · intro n
      change τ.decomposeIter GS.k (GS.G.scatter (seq' (n + 1)).tiles) =
        GS.G.scatter (seq' n).tiles
      rw [← hierarchy_lift_iff_scatter_decompose τ GS, hcomp n]

/-- Step 1 of the blueprint proof of `hierarchy_lift_sts`: lift the sequence. -/
private lemma hierarchy_lift_sts_step1_lift (τ : Substitution P) (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩}) (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles) :
    ∃ seq' : ℕ → PlaneTiling GS.G.P', (∀ n, GS.σ.IsComposition (seq' (n + 1)) (seq' n)) ∧
      (∀ n, GS.G.scatter (seq' n).tiles = (seq n).tiles) := by
  exact hierarchy_lift_iff_liftSequence τ GS hsingle seq hseq

/-- Step 1 of the blueprint proof of `hierarchy_lift_sts_step2_sts`: Overlapping grouped sides
contain an overlapping pair of original sides. -/
private lemma hierarchy_lift_sts_step2_sts_step1_overlap
    (τ : Substitution P) (GS : GroupedSubstitution τ)
    (A B : PlacedTile GS.G.P')
    (i : Fin (GS.G.P'.disk A.form).n) (j : Fin (GS.G.P'.disk B.form).n)
    (hover : OverlapPos (A.side i) (B.side j)) :
    ∃ (a : PlacedTile P) (_ : a ∈ GS.G.scatterTile A)
      (b : PlacedTile P) (_ : b ∈ GS.G.scatterTile B)
      (k : Fin (P.disk a.form).n) (l : Fin (P.disk b.form).n),
      OverlapPos (a.side k) (b.side l) ∧ a.side k ⊆ A.side i ∧ b.side l ⊆ B.side j := by
  have _ := τ
  obtain ⟨a₀, ha₀, hk⟩ := GS.G.side_whole A.form i
  obtain ⟨b₀, hb₀, hl⟩ := GS.G.side_whole B.form j
  obtain ⟨k, hk⟩ := hk
  obtain ⟨l, hl⟩ := hl
  let a : PlacedTile P := ⟨a₀.form, A.anchor + a₀.anchor⟩
  let b : PlacedTile P := ⟨b₀.form, B.anchor + b₀.anchor⟩
  have ha : a ∈ GS.G.scatterTile A := by
    simp [GroupedFamily.scatterTile, translateSet, Set.mem_image]
    exact ⟨a₀, ha₀, rfl⟩
  have hb : b ∈ GS.G.scatterTile B := by
    simp [GroupedFamily.scatterTile, translateSet, Set.mem_image]
    exact ⟨b₀, hb₀, rfl⟩
  use a, ha, b, hb, k, l
  have hk' : a.side k = A.side i := by
    dsimp [a, PlacedTile.side]
    rw [add_vadd]
    have h1 : a₀.anchor +ᵥ (P.disk a₀.form).side k = a₀.side k := rfl
    rw [h1, hk]
  have hl' : b.side l = B.side j := by
    dsimp [b, PlacedTile.side]
    rw [add_vadd]
    have h1 : b₀.anchor +ᵥ (P.disk b₀.form).side l = b₀.side l := rfl
    rw [h1, hl]
  refine ⟨?_, ?_, ?_⟩
  · rw [hk', hl']
    exact hover
  · rw [hk']
  · rw [hl']

/-- Step 1 of the blueprint proof of `hierarchy_lift_sts_step2_sts_step2_match`: If an original
side in a grouped tile's scatter is a subset of the grouped side, they are equal. -/
private lemma hierarchy_lift_sts_step2_sts_step2_match_step1_eq
    (τ : Substitution P) (GS : GroupedSubstitution τ)
    (A : PlacedTile GS.G.P') (i : Fin (GS.G.P'.disk A.form).n)
    (a : PlacedTile P) (ha : a ∈ GS.G.scatterTile A) (k : Fin (P.disk a.form).n)
    (h_sub : a.side k ⊆ A.side i) :
    A.side i = a.side k := by
  have _ := τ
  obtain ⟨c, hc, l, hcl⟩ := GS.G.side_whole A.form i
  simp only [GroupedFamily.scatterTile, translateSet, Set.mem_image] at ha
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  change Fin (P.disk a₀.form).n at k
  have rotate_ne : ∀ {n : ℕ}, 2 ≤ n → ∀ k : Fin n, finRotate n k ≠ k := by
    intro n hn k
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [finRotate_succ_apply]
    intro h
    have h1 : (1 : Fin (m + 1)) = 0 := by
      have := congrArg (fun x => x - k) h
      simpa using this
    have : NeZero (m + 1) := ⟨by omega⟩
    rw [Fin.one_eq_zero_iff] at h1
    omega
  have hnext : finRotate (P.disk a₀.form).n k ≠ k :=
    rotate_ne (by have := (P.disk a₀.form).three_le; omega) k
  have hab : a₀.vertex k ≠ a₀.vertex (finRotate _ k) := by
    intro h
    have h' : (P.disk a₀.form).vertex k =
        (P.disk a₀.form).vertex (finRotate _ k) := by
      simpa [PlacedTile.vertex] using h
    exact hnext ((P.disk a₀.form).vertex_injective h'.symm)
  have h_sub0 : a₀.side k ⊆ (GS.G.P'.disk A.form).side i := by
    intro x hx
    have hx'' : A.anchor +ᵥ x ∈ A.anchor +ᵥ a₀.side k := vadd_mem_vadd_set hx
    have hx' : (A.anchor +ᵥ x) ∈ (a₀.translate A.anchor).side k := by
      simpa [PlacedTile.translate, PlacedTile.side, add_vadd] using hx''
    have hx_sub := h_sub hx'
    change A.anchor +ᵥ x ∈ A.anchor +ᵥ (GS.G.P'.disk A.form).side i at hx_sub
    rw [mem_vadd_set_iff_neg_vadd_mem] at hx_sub
    simpa using hx_sub
  have hover : OverlapPos (a₀.side k) (c.side l) := by
    refine ⟨a₀.vertex k, a₀.vertex (finRotate _ k), hab, ?_⟩
    rw [hcl]
    intro x hx
    have hx' : x ∈ a₀.side k := by
      simpa [PlacedTile.side, PolygonalDisk.side, PlacedTile.vertex, vadd_segment]
        using hx
    exact ⟨hx', h_sub0 hx'⟩
  have heq : a₀.side k = c.side l := GS.G.sts A.form a₀ ha₀ c hc k l hover
  have hwhole : a₀.side k = (GS.G.P'.disk A.form).side i := heq.trans hcl
  have hwhole' := congrArg (fun s : Set Pt => A.anchor +ᵥ s) hwhole
  simpa [PlacedTile.side, PlacedTile.translate, add_vadd] using hwhole'.symm

/-- Step 2 of the blueprint proof of `hierarchy_lift_sts_step2_sts`: Matching original sides
on grouped sides force the grouped sides to be identical. -/
private lemma hierarchy_lift_sts_step2_sts_step2_match
    (τ : Substitution P) (GS : GroupedSubstitution τ)
    (A B : PlacedTile GS.G.P')
    (i : Fin (GS.G.P'.disk A.form).n) (j : Fin (GS.G.P'.disk B.form).n)
    (hover : OverlapPos (A.side i) (B.side j))
    (a : PlacedTile P) (ha : a ∈ GS.G.scatterTile A)
    (b : PlacedTile P) (hb : b ∈ GS.G.scatterTile B)
    (k : Fin (P.disk a.form).n) (l : Fin (P.disk b.form).n)
    (h_sts : a.side k = b.side l)
    (h_sub_a : a.side k ⊆ A.side i) (h_sub_b : b.side l ⊆ B.side j) :
    A.side i = B.side j := by
  have _ := hover
  have eq_A : A.side i = a.side k := hierarchy_lift_sts_step2_sts_step2_match_step1_eq τ GS A i a ha k h_sub_a
  have eq_B : B.side j = b.side l := hierarchy_lift_sts_step2_sts_step2_match_step1_eq τ GS B j b hb l h_sub_b
  rw [eq_A, eq_B, h_sts]

/-- Step 2 of the blueprint proof of `hierarchy_lift_sts`: STS property is inherited. -/
private lemma hierarchy_lift_sts_step2_sts (τ : Substitution P) (GS : GroupedSubstitution τ)
    (seq : ℕ → PlaneTiling P) (seq' : ℕ → PlaneTiling GS.G.P')
    (hscatter : ∀ n, GS.G.scatter (seq' n).tiles = (seq n).tiles)
    (hsts : ∀ n, (seq n).SideToSide) :
    ∀ n, (seq' n).SideToSide := by
  intro n A hA B hB i j hover
  obtain ⟨a, ha, b, hb, k, l, hover', hsuba, hsubb⟩ :=
    hierarchy_lift_sts_step2_sts_step1_overlap τ GS A B i j hover
  have ha' : a ∈ (seq n).tiles := by
    rw [← hscatter n]
    exact Set.mem_iUnion₂.mpr ⟨A, hA, ha⟩
  have hb' : b ∈ (seq n).tiles := by
    rw [← hscatter n]
    exact Set.mem_iUnion₂.mpr ⟨B, hB, hb⟩
  have h_eq : a.side k = b.side l := hsts n a ha' b hb' k l hover'
  exact hierarchy_lift_sts_step2_sts_step2_match τ GS A B i j hover a ha b hb k l h_eq hsuba hsubb

/-- `lem:grouping-lift` (STS levels): a `τ^k`-hierarchy all of whose levels
are STS lifts to a grouped `σ`-hierarchy scattering level by level onto it,
all of whose levels are STS. -/
theorem Grouping.hierarchy_lift_sts (τ : Substitution P) (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩})
    (seq : ℕ → PlaneTiling P) (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles)
    (hsts : ∀ n, (seq n).SideToSide) :
    ∃ seq' : ℕ → PlaneTiling GS.G.P', (∀ n, GS.σ.IsComposition (seq' (n + 1)) (seq' n)) ∧
      (∀ n, GS.G.scatter (seq' n).tiles = (seq n).tiles) ∧ ∀ n, (seq' n).SideToSide := by
  obtain ⟨seq', hcomp, hscat⟩ := hierarchy_lift_sts_step1_lift τ GS hsingle seq hseq
  exact ⟨seq', hcomp, hscat, hierarchy_lift_sts_step2_sts τ GS seq seq' hscat hsts⟩

/-! ## The hereditary STS core -/

/-! ### The finite crown control used by `thm:hereditary-substitution`

The ordinary strict control alphabet remembers a hierarchy, but it deliberately
does not remember which crowns occur across a persistent hierarchy boundary.
The following data are the extra, physical crown channel from the reviewed
proof.  In particular, the catalogue uses one *jointly allowed collar*, rather
than choosing its crowns independently. -/

open Classical

/-- The finite list of allowed crowns which cover a neighbourhood of their
centre.  The neighbourhood condition removes incomplete crowns occurring on
the boundary of a finite supertile. -/
private noncomputable def hereditary_sts_substitution_sofic_fullCrowns
    (τ : Substitution P) (hsts : τ.STS) : Finset (Set (PlacedTile P)) :=
  (Substitution.STS.finite_crowns τ hsts).toFinset.filter
    (fun K => 0 ∈ interior (support K))

/-- A full allowed crown, represented by its entry in the finite list above. -/
private abbrev hereditary_sts_substitution_sofic_FullCrown
    (τ : Substitution P) (hsts : τ.STS) :=
  ↥(hereditary_sts_substitution_sofic_fullCrowns τ hsts)

/-- Step 1 of the reviewed proof: the marked vertices in a finite grouped
dissection form a finite set.  This is only the elementary finite-union
statement; no control rule or tiling is involved. -/
private lemma hereditary_sts_substitution_sofic_step1_macro_vertices_finite
    (C : Geometry.MacroCertificate P) (q : C.Q.Form) :
    {v : Pt | Substitution.IsVertexOf (C.Δ q).tiles v}.Finite := by
  have hset : {v : Pt | Substitution.IsVertexOf (C.Δ q).tiles v} =
      ⋃ A ∈ (C.Δ q).tiles, A.vertexSet := by
    ext v
    simp [Substitution.IsVertexOf]
  rw [hset]
  exact (C.Δ q).finite.biUnion fun A _ => Set.finite_range A.vertex

/-- The actual finite set of original marked vertices in a grouped tile. -/
private noncomputable def hereditary_sts_substitution_sofic_macroVertices
    (C : Geometry.MacroCertificate P) (q : C.Q.Form) : Finset Pt :=
  (hereditary_sts_substitution_sofic_step1_macro_vertices_finite C q).toFinset

/-- A vector of full crowns, one at every original marked vertex of a grouped
tile. -/
private abbrev hereditary_sts_substitution_sofic_CrownVector
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (q : C.Q.Form) :=
  (v : ↥(hereditary_sts_substitution_sofic_macroVertices C q)) →
    hereditary_sts_substitution_sofic_FullCrown τ hsts

/-- The collar obtained by adjoining every translated crown in a crown
vector to the grouped dissection. -/
private def hereditary_sts_substitution_sofic_collar
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (q : C.Q.Form)
    (γ : hereditary_sts_substitution_sofic_CrownVector τ hsts C q) :
    Set (PlacedTile P) :=
  (C.Δ q).tiles ∪ ⋃ v, translateSet v.1 (γ v).1

/-- Joint occurrence of the entire collar in one supertile.  This is the
condition that prevents independently chosen, mutually incompatible crowns. -/
private def hereditary_sts_substitution_sofic_JointAllowed
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (q : C.Q.Form)
    (γ : hereditary_sts_substitution_sofic_CrownVector τ hsts C q) : Prop :=
  ∃ (n : ℕ) (p : P.Form) (a : Pt),
    translateSet a (hereditary_sts_substitution_sofic_collar τ hsts C q γ) ⊆
      τ.supertile n p

/-- The jointly allowed catalogue `Γ(q)`: disjoint and STS collars, exact
stars at every recorded vertex, and one common supertile witness. -/
private def hereditary_sts_substitution_sofic_Catalog
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (q : C.Q.Form) :=
  {γ : hereditary_sts_substitution_sofic_CrownVector τ hsts C q //
    DisjointInteriors
        (hereditary_sts_substitution_sofic_collar τ hsts C q γ) ∧
    SideToSideSet
        (hereditary_sts_substitution_sofic_collar τ hsts C q γ) ∧
    (∀ v,
      Substitution.crown (hereditary_sts_substitution_sofic_collar τ hsts C q γ) v.1 =
        translateSet v.1 (γ v).1) ∧
    hereditary_sts_substitution_sofic_JointAllowed τ hsts C q γ}

/-- The raw child crown at a marked vertex, obtained by decomposing the whole
parent collar and taking the physical star at the positioned child vertex. -/
private def hereditary_sts_substitution_sofic_rawChildCrown
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (t : C.Typ)
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.owner t))
    (v : ↥(hereditary_sts_substitution_sofic_macroVertices C (C.form t))) :
    Set (PlacedTile P) :=
  let x := C.anchor t + v.1
  translateSet (-x)
    (Substitution.crown
      (τ.decomposeIter m
        (hereditary_sts_substitution_sofic_collar τ hsts C (C.owner t) γ.1)) x)

/-! #### Helpers for `hereditary_sts_substitution_sofic_step2_raw_child_is_full` -/

/-- Translating a placed tile translates its carrier. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_carrier_translate
    (X : PlacedTile P) (u : Pt) : (X.translate u).carrier = u +ᵥ X.carrier := by
  show (u +ᵥ X.anchor) +ᵥ _ = u +ᵥ (X.anchor +ᵥ _)
  rw [vadd_vadd]; rfl

/-- Translating a placed tile translates its listed vertices. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_vertex_translate
    (X : PlacedTile P) (u : Pt) (k : Fin (P.disk X.form).n) :
    (X.translate u).vertex k = u + X.vertex k := by
  show (u +ᵥ X.anchor) +ᵥ (P.disk X.form).vertex k =
    u + (X.anchor +ᵥ (P.disk X.form).vertex k)
  simp only [vadd_eq_add, add_assoc]

/-- A listed vertex of a placed tile lies in its carrier. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_vertex_mem_carrier
    (X : PlacedTile P) (i : Fin (P.disk X.form).n) : X.vertex i ∈ X.carrier := by
  refine ⟨(P.disk X.form).vertex i, ?_, rfl⟩
  apply (P.disk X.form).compact.isClosed.frontier_subset
  rw [(P.disk X.form).frontier_eq]
  exact Set.mem_iUnion.mpr ⟨i, left_mem_segment ℝ _ _⟩

/-- Supertiles have pairwise disjoint interiors. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_supertile_disjoint
    (τ : Substitution P) (n : ℕ) (p : P.Form) : DisjointInteriors (τ.supertile n p) := by
  cases n with
  | zero =>
    change DisjointInteriors ({⟨p, 0⟩} : Set (PlacedTile P))
    exact Set.pairwiseDisjoint_singleton _ _
  | succ n => exact ((τ.pow (n + 1) (Nat.succ_pos n)).rule p).disjoint

/-- A tile of an interior-disjoint family containing an interior point of the support of a
finite subfamily belongs to that subfamily. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_mem_of_interior
    {D F : Set (PlacedTile P)} (hD : DisjointInteriors D) (hFD : F ⊆ D)
    (hF : F.Finite) {w : Pt} (hw : w ∈ interior (support F)) {Y : PlacedTile P} (hY : Y ∈ D)
    (hwY : w ∈ Y.carrier) : Y ∈ F := by
  by_contra hYF
  rw [← cc_tile_regular Y] at hwY
  obtain ⟨z, hzV, hzY⟩ := mem_closure_iff.mp hwY _ isOpen_interior hw
  have hsupp : support F = closure (⋃ Z ∈ F, interior Z.carrier) := by
    rw [hF.closure_biUnion]
    apply iUnion₂_congr
    intro Z _
    exact (cc_tile_regular Z).symm
  have hz : z ∈ closure (⋃ Z ∈ F, interior Z.carrier) := hsupp ▸ interior_subset hzV
  obtain ⟨y, ⟨hyV, hyY⟩, hyU⟩ :=
    mem_closure_iff.mp hz _ (isOpen_interior.inter isOpen_interior) ⟨hzV, hzY⟩
  simp only [mem_iUnion] at hyU
  obtain ⟨Z, hZ, hyZ⟩ := hyU
  have hne : Y ≠ Z := fun h => hYF (h ▸ hZ)
  exact Set.disjoint_left.mp (hD hY (hFD hZ) hne) hyY hyZ

/-- Iterated decomposition is monotone. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_decomposeIter_mono
    (τ : Substitution P) (k : ℕ) {S S' : Set (PlacedTile P)} (h : S ⊆ S') :
    τ.decomposeIter k S ⊆ τ.decomposeIter k S' := by
  induction k with
  | zero => exact h
  | succ k ih =>
    intro A hA
    change A ∈ τ.decompose (τ.decomposeIter k S) at hA
    change A ∈ τ.decompose (τ.decomposeIter k S')
    simp only [Substitution.decompose, Set.mem_iUnion] at hA ⊢
    obtain ⟨B, hB, hAB⟩ := hA
    exact ⟨B, ih hB, hAB⟩

/-- Iterated decompositions compose additively. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_decomposeIter_add
    (τ : Substitution P) (n k : ℕ) (S : Set (PlacedTile P)) :
    τ.decomposeIter k (τ.decomposeIter n S) = τ.decomposeIter (n + k) S := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change τ.decompose (τ.decomposeIter k (τ.decomposeIter n S)) =
      τ.decompose (τ.decomposeIter (n + k) S)
    rw [ih]

/-- Iterated decomposition preserves finiteness. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_decomposeIter_finite
    (τ : Substitution P) (k : ℕ) {S : Set (PlacedTile P)} (hS : S.Finite) :
    (τ.decomposeIter k S).Finite := by
  induction k with
  | zero => exact hS
  | succ k ih =>
    change (τ.decompose (τ.decomposeIter k S)).Finite
    exact ih.biUnion fun A _ => (τ.rule A.form).finite.image _

/-- The support of an iterated decomposition is the scaled support. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_support_decomposeIter
    (τ : Substitution P) (k : ℕ) (S : Set (PlacedTile P)) :
    support (τ.decomposeIter k S) = (τ.θ ^ k) • support S := by
  induction k with
  | zero =>
    show support S = (τ.θ ^ 0) • support S
    rw [pow_zero, one_smul]
  | succ k ih =>
    change support (τ.decompose (τ.decomposeIter k S)) = _
    rw [hierarchy_lift_iff_decompose_support, ih, smul_smul, ← pow_succ']

/-- Equal segments have the same endpoints. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_segment_endpoints
    {a b c d : Pt} (h : segment ℝ a b = segment ℝ c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  by_cases hab : a = b
  · subst hab
    rw [segment_same] at h
    have hc : c ∈ ({a} : Set Pt) := h ▸ left_mem_segment ℝ c d
    have hd : d ∈ ({a} : Set Pt) := h ▸ right_mem_segment ℝ c d
    rw [Set.mem_singleton_iff] at hc hd
    exact Or.inl ⟨hc.symm, hd.symm⟩
  · have hc : c ∈ segment ℝ a b := h ▸ left_mem_segment ℝ c d
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
      have h' : a + s • (b - a) + u • (a + t • (b - a) -
          (a + s • (b - a))) - a = (s + u * (t - s)) • (b - a) := by
        module
      rw [← h', hu, sub_self]
    have e2 : (s + w * (t - s) - 1) • (b - a) = 0 := by
      have h' : a + s • (b - a) + w • (a + t • (b - a) -
          (a + s • (b - a))) - b = (s + w * (t - s) - 1) • (b - a) := by
        module
      rw [← h', hw, sub_self]
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

/-- A listed side of a placed tile is the segment between its endpoints. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_side_eq_segment
    (X : PlacedTile P) (i : Fin (P.disk X.form).n) :
    X.side i = segment ℝ (X.vertex i) (X.vertex (finRotate _ i)) := by
  simp only [PlacedTile.side, PlacedTile.vertex, PolygonalDisk.side]
  exact vadd_segment ℝ _ _ _

/-- A listed side of a placed tile lies in its carrier. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_side_subset_carrier
    (X : PlacedTile P) (i : Fin (P.disk X.form).n) : X.side i ⊆ X.carrier := by
  simp only [PlacedTile.side, PlacedTile.carrier]
  refine vadd_set_mono ?_
  have h1 : (P.disk X.form).side i ⊆ frontier (P.disk X.form).carrier := by
    rw [(P.disk X.form).frontier_eq]
    exact subset_iUnion (fun i => segment ℝ ((P.disk X.form).vertex i)
      ((P.disk X.form).vertex (finRotate (P.disk X.form).n i))) i
  refine h1.trans ?_
  rw [((P.disk X.form).compact.isClosed).frontier_eq]
  exact diff_subset

/-- A listed vertex of a placed tile lies on the listed side starting there. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_vertex_mem_side
    (X : PlacedTile P) (k : Fin (P.disk X.form).n) : X.vertex k ∈ X.side k := by
  rw [hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_side_eq_segment]
  exact left_mem_segment ℝ _ _

/-- Two distinct listed sides of a placed tile meet only in listed endpoints. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_side_inter
    (X : PlacedTile P) {k i : Fin (P.disk X.form).n} (hki : k ≠ i) {z : Pt}
    (hzk : z ∈ X.side k) (hzi : z ∈ X.side i) :
    z = X.vertex i ∨ z = X.vertex (finRotate _ i) := by
  rw [PlacedTile.side, mem_vadd_set_iff_neg_vadd_mem] at hzk hzi
  have h := ((P.disk X.form).simple k i hki ⟨hzk, hzi⟩).2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h
  · left
    rw [PlacedTile.vertex, ← h, vadd_neg_vadd]
  · right
    rw [PlacedTile.vertex, ← h, vadd_neg_vadd]

/-- A point of one tile is not an interior point of a second tile with disjoint interior. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_not_interior
    {A B : PlacedTile P} (hd : Disjoint (interior A.carrier) (interior B.carrier)) {x : Pt}
    (hxB : x ∈ B.carrier) : x ∉ interior A.carrier := by
  intro hxA
  rw [← cc_tile_regular B, mem_closure_iff_nhds] at hxB
  obtain ⟨z, hz1, hz2⟩ := hxB _ (isOpen_interior.mem_nhds hxA)
  exact Set.disjoint_left.mp hd hz1 hz2

/-- A point of a listed side is not an interior point of the tile. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_side_not_interior
    (X : PlacedTile P) (i : Fin (P.disk X.form).n) {z : Pt} (hz : z ∈ X.side i) :
    z ∉ interior X.carrier := by
  rw [PlacedTile.side, mem_vadd_set_iff_neg_vadd_mem] at hz
  rw [PlacedTile.carrier, interior_vadd, mem_vadd_set_iff_neg_vadd_mem]
  have h1 : (P.disk X.form).side i ⊆ frontier (P.disk X.form).carrier := by
    rw [(P.disk X.form).frontier_eq]
    exact subset_iUnion (fun i => segment ℝ ((P.disk X.form).vertex i)
      ((P.disk X.form).vertex (finRotate (P.disk X.form).n i))) i
  exact (h1 hz).2

/-- `finRotate` has no fixed point on `Fin n` for `2 ≤ n`. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_finRotate_ne
    {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [finRotate_succ_apply]
  intro h
  have h1 : (1 : Fin (m + 1)) = 0 := by
    have := congrArg (fun x => x - i) h
    simpa using this
  have : NeZero (m + 1) := ⟨by omega⟩
  rw [Fin.one_eq_zero_iff] at h1
  omega

/-- The two endpoints of a listed side are distinct. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_vertex_ne
    (X : PlacedTile P) (i : Fin (P.disk X.form).n) :
    X.vertex i ≠ X.vertex (finRotate _ i) := by
  intro h
  simp only [PlacedTile.vertex, vadd_eq_add, add_right_inj] at h
  exact hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_finRotate_ne
    (by have := (P.disk X.form).three_le; omega) i ((P.disk X.form).vertex_injective h).symm

/-- Two tiles with disjoint interiors meeting at a point of the side `A.side i` which is a
listed vertex of neither tile share a segment of positive length of `A.side i` with a listed
side of `B`. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_key
    {A B : PlacedTile P} (hd : Disjoint (interior A.carrier) (interior B.carrier)) {x : Pt}
    {i : Fin (P.disk A.form).n} (hxi : x ∈ A.side i) (hxB : x ∈ B.carrier)
    (hvA : x ∉ A.vertexSet) (hvB : x ∉ B.vertexSet) :
    ∃ j, OverlapPos (A.side i) (B.side j) := by
  have hxA : x ∈ A.carrier :=
    hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_side_subset_carrier A i hxi
  obtain ⟨i₁, ε₁, d₁, n₁, hε₁, hd₁, hn₁, hnd₁, hs₁, hy₁⟩ := cc_halfdisk_tile A hxA
    (hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_not_interior hd hxB) hvA
  obtain ⟨j, ε₂, d₂, n₂, hε₂, hd₂, hn₂, hnd₂, hs₂, hy₂⟩ := cc_halfdisk_tile B hxB
    (hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_not_interior hd.symm hxA) hvB
  have hi₁ : i₁ = i := by
    by_contra hne
    have hx₁ : x ∈ A.side i₁ := by simpa using hs₁ 0 (by simpa using hε₁)
    rcases hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_side_inter A hne
        hx₁ hxi with h | h
    · exact hvA ⟨i, h.symm⟩
    · exact hvA ⟨_, h.symm⟩
  subst hi₁
  have key : inner ℝ n₂ d₁ = 0 := by
    by_contra hne
    obtain ⟨w, hw2, hw1⟩ : ∃ w : Pt, 0 < inner ℝ n₂ w ∧ inner ℝ n₁ w = 0 := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨-d₁, by rw [inner_neg_right]; linarith, by rw [inner_neg_right, hnd₁, neg_zero]⟩
      · exact ⟨d₁, h, hnd₁⟩
    set c := (|inner ℝ n₂ n₁| + 1) / inner ℝ n₂ w with hc
    set u := n₁ + c • w with hu
    have hu2 : 0 < inner ℝ n₂ u := by
      rw [hu, inner_add_right, inner_smul_right, hc, div_mul_cancel₀ _ hw2.ne']
      have := neg_abs_le (inner ℝ n₂ n₁); linarith
    have hu1 : 0 < inner ℝ n₁ u := by
      rw [hu, inner_add_right, inner_smul_right, hw1, mul_zero, add_zero,
        real_inner_self_eq_norm_sq]
      have := norm_pos_iff.mpr hn₁; positivity
    have hu0 : u ≠ 0 := by rintro h; rw [h, inner_zero_right] at hu1; exact lt_irrefl _ hu1
    have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    set δ := min ε₁ ε₂ / (2 * ‖u‖) with hδ
    have hδpos : 0 < δ := div_pos (lt_min hε₁ hε₂) (by positivity)
    have hdist : dist (x + δ • u) x = min ε₁ ε₂ / 2 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδpos.le, hδ]
      field_simp
    have hm1 := min_le_left ε₁ ε₂
    have hm2 := min_le_right ε₁ ε₂
    have hmpos : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
    have h1 : x + δ • u ∈ interior A.carrier := by
      apply hy₁ _ (by rw [hdist]; linarith)
      rw [add_sub_cancel_left, inner_smul_right]; positivity
    have h2 : x + δ • u ∈ interior B.carrier := by
      apply hy₂ _ (by rw [hdist]; linarith)
      rw [add_sub_cancel_left, inner_smul_right]; positivity
    exact Set.disjoint_left.mp hd h1 h2
  obtain ⟨c, hc⟩ := cc_parallel hn₂ hd₂ key hnd₂
  have hc0 : c ≠ 0 := by rintro rfl; apply hd₁; rw [hc, zero_smul]
  have hcpos : 0 < |c| := abs_pos.mpr hc0
  set s₀ := min ε₁ (ε₂ / |c|) / 2 with hs₀
  have hs₀pos : 0 < s₀ := by
    have : 0 < min ε₁ (ε₂ / |c|) := lt_min hε₁ (div_pos hε₂ hcpos)
    positivity
  refine ⟨j, x + (-s₀) • d₁, x + s₀ • d₁, ?_, ?_⟩
  · intro h
    have : (2 * s₀) • d₁ = 0 := by
      have h' := congrArg (fun z => z - x) h
      simp only [add_sub_cancel_left] at h'
      have e : (2 * s₀) • d₁ = s₀ • d₁ - (-s₀) • d₁ := by
        rw [neg_smul, sub_neg_eq_add, ← add_smul, two_mul]
      rw [e, h', sub_self]
    rcases smul_eq_zero.mp this with h | h
    · linarith
    · exact hd₁ h
  · rw [segment_eq_image']
    rintro _ ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩
    have he : x + (-s₀) • d₁ + θ • (x + s₀ • d₁ - (x + (-s₀) • d₁)) =
        x + ((2 * θ - 1) * s₀) • d₁ := by
      rw [add_sub_add_left_eq_sub, ← sub_smul]
      rw [smul_smul, add_assoc, ← add_smul]; congr 2; ring
    simp only
    rw [he]
    have hab : |(2 * θ - 1) * s₀| ≤ s₀ := by
      rw [abs_mul, abs_of_pos hs₀pos]
      have : |2 * θ - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      nlinarith [abs_nonneg (2 * θ - 1)]
    have hm1 := min_le_left ε₁ (ε₂ / |c|)
    have hm2 := min_le_right ε₁ (ε₂ / |c|)
    refine ⟨hs₁ _ (by linarith), ?_⟩
    rw [hc, smul_smul]
    apply hs₂
    rw [abs_mul]
    calc |(2 * θ - 1) * s₀| * |c| ≤ s₀ * |c| := by gcongr
      _ < ε₂ / |c| * |c| := by gcongr; linarith
      _ = ε₂ := div_mul_cancel₀ _ hcpos.ne'

/-- A collar is a finite set of placed tiles: full crowns are finite. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_collar_finite
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P) (q : C.Q.Form)
    (γ : hereditary_sts_substitution_sofic_CrownVector τ hsts C q) :
    (hereditary_sts_substitution_sofic_collar τ hsts C q γ).Finite := by
  unfold hereditary_sts_substitution_sofic_collar
  refine (C.Δ q).finite.union (Set.finite_iUnion fun v => ?_)
  have hK := (γ v).2
  simp only [hereditary_sts_substitution_sofic_fullCrowns, Finset.mem_filter,
    Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hK
  obtain ⟨⟨n, p, w, -, hw⟩, -⟩ := hK
  rw [hw]
  have hsup : (τ.supertile n p).Finite :=
    hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_decomposeIter_finite τ n
      (Set.finite_singleton _)
  exact ((hsup.subset (sep_subset _ _)).image _).image _

/-- Step 1 of the blueprint proof of `hereditary_sts_substitution_sofic_step2_raw_child_is_full`:
side saturation of a catalogue collar.  Let `γ ∈ Γ(q)`.  Every listed side `A.side i` of every
original tile `A` of the grouped dissection `Δ q` is also a listed side of a second, different
tile `B` of the collar of `γ`.  (The exact full star `translateSet a (γ a)` of the collar at the
endpoint `a = A.vertex i ∈ V(q)` covers a neighbourhood of `a`, so a tile `B ≠ A` of this star
shares with `A.side i` a segment of positive length near `a`; side-to-side matching inside the
collar then makes the two listed sides equal.) -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_step1_side_partner
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P) (q : C.Q.Form)
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C q)
    (A : PlacedTile P) (hA : A ∈ (C.Δ q).tiles) (i : Fin (P.disk A.form).n) :
    ∃ B ∈ hereditary_sts_substitution_sofic_collar τ hsts C q γ.1, B ≠ A ∧
      ∃ j : Fin (P.disk B.form).n, B.side j = A.side i := by
  set Col := hereditary_sts_substitution_sofic_collar τ hsts C q γ.1 with hCol
  have hAcol : A ∈ Col := Or.inl hA
  have hab : A.vertex i ≠ A.vertex (finRotate _ i) :=
    hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_vertex_ne A i
  set a := A.vertex i with ha_def
  set b := A.vertex (finRotate _ i) with hb_def
  have haV : a ∈ hereditary_sts_substitution_sofic_macroVertices C q := by
    simp only [hereditary_sts_substitution_sofic_macroVertices, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq]
    exact ⟨A, hA, i, rfl⟩
  -- the exact full star at `a` covers a ball around `a`
  have hcr : Substitution.crown Col a = translateSet a (γ.1 ⟨a, haV⟩).1 := γ.2.2.2.1 ⟨a, haV⟩
  have hfull := (γ.1 ⟨a, haV⟩).2
  simp only [hereditary_sts_substitution_sofic_fullCrowns, Finset.mem_filter] at hfull
  have hint : a ∈ interior (support (Substitution.crown Col a)) := by
    rw [hcr, cc_support_translate, interior_vadd]
    have h := vadd_mem_vadd_set (a := a) hfull.2
    simpa only [vadd_eq_add, add_zero] using h
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hint)
  have hKfin : (Substitution.crown Col a).Finite :=
    (hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_collar_finite
      τ hsts C q γ.1).subset (sep_subset _ _)
  -- a point `z` of the side near `a`, avoiding all listed vertices of the star
  have hVfin : (⋃ B ∈ Substitution.crown Col a, B.vertexSet).Finite :=
    hKfin.biUnion fun B _ => Set.finite_range B.vertex
  have hba0 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hba : 0 < ‖b - a‖ := norm_pos_iff.mpr hba0
  have hs₀pos : 0 < min 1 (r / ‖b - a‖) := lt_min one_pos (div_pos hr hba)
  have hinj : Function.Injective fun s : ℝ => a + s • (b - a) := by
    intro s s' h
    have h' : s • (b - a) = s' • (b - a) := add_left_cancel h
    exact smul_left_injective ℝ hba0 h'
  have hbad : ((fun s : ℝ => a + s • (b - a)) ⁻¹'
      (⋃ B ∈ Substitution.crown Col a, B.vertexSet)).Finite :=
    hVfin.preimage hinj.injOn
  obtain ⟨s, ⟨hs0, hs1⟩, hsV⟩ := ((Set.Ioo_infinite hs₀pos).diff hbad).nonempty
  have hs1' : s < 1 := lt_of_lt_of_le hs1 (min_le_left _ _)
  have hsr : s < r / ‖b - a‖ := lt_of_lt_of_le hs1 (min_le_right _ _)
  have hzside : a + s • (b - a) ∈ A.side i := by
    rw [hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_side_eq_segment,
      segment_eq_image']
    exact ⟨s, ⟨hs0.le, hs1'.le⟩, rfl⟩
  have hzball : a + s • (b - a) ∈ Metric.ball a r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hs0.le]
    exact (lt_div_iff₀ hba).mp hsr
  have hzA : a + s • (b - a) ∉ interior A.carrier :=
    hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_side_not_interior A i hzside
  have hzvert : ∀ B ∈ Substitution.crown Col a, a + s • (b - a) ∉ B.vertexSet := by
    intro B hB hzB
    apply hsV
    show a + s • (b - a) ∈ ⋃ B ∈ Substitution.crown Col a, B.vertexSet
    exact mem_biUnion hB hzB
  have hAK : A ∈ Substitution.crown Col a :=
    ⟨hAcol, hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_vertex_mem_carrier A i⟩
  -- a second tile of the star contains `z`
  have hexB : ∃ B ∈ Substitution.crown Col a, B ≠ A ∧ a + s • (b - a) ∈ B.carrier := by
    by_contra hno
    push_neg at hno
    have hFfin : {B ∈ Substitution.crown Col a | B ≠ A}.Finite := hKfin.subset (sep_subset _ _)
    have hFcl : IsClosed (⋃ B ∈ {B ∈ Substitution.crown Col a | B ≠ A}, B.carrier) :=
      hFfin.isClosed_biUnion fun B _ => cc_tile_carrier_closed B
    have hzF : a + s • (b - a) ∉ ⋃ B ∈ {B ∈ Substitution.crown Col a | B ≠ A}, B.carrier := by
      simp only [mem_iUnion, not_exists]
      intro B hB hzB
      exact hno B hB.1 hB.2 hzB
    apply hzA
    rw [mem_interior_iff_mem_nhds]
    have hU : Metric.ball a r ∩ (⋃ B ∈ {B ∈ Substitution.crown Col a | B ≠ A}, B.carrier)ᶜ ∈
        nhds (a + s • (b - a)) :=
      (Metric.isOpen_ball.inter hFcl.isOpen_compl).mem_nhds ⟨hzball, hzF⟩
    refine Filter.mem_of_superset hU ?_
    rintro w ⟨hw1, hw2⟩
    have hwK := hball hw1
    simp only [support, mem_iUnion] at hwK
    obtain ⟨B, hB, hwB⟩ := hwK
    by_cases hBA : B = A
    · rw [← hBA]
      exact hwB
    · exfalso
      apply hw2
      simp only [mem_iUnion]
      exact ⟨B, ⟨hB, hBA⟩, hwB⟩
  obtain ⟨B, hBK, hBA, hzB⟩ := hexB
  have hBcol : B ∈ Col := hBK.1
  have hdisj : Disjoint (interior A.carrier) (interior B.carrier) :=
    γ.2.1 hAcol hBcol (Ne.symm hBA)
  obtain ⟨j, hj⟩ := hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_key hdisj
    hzside hzB (hzvert A hAK) (hzvert B hBK)
  exact ⟨B, hBcol, hBA, j, (γ.2.2.1 A hAcol B hBcol i j hj).symm⟩

/-- Step 2 of the blueprint proof of `hereditary_sts_substitution_sofic_step2_raw_child_is_full`:
two placed tiles with disjoint interiors and a common listed side cover a neighbourhood of every
point of that side other than its two endpoints (near such a point the two tiles lie on the two
opposite sides of the common segment). -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_step2_common_side_nhds
    {A B : PlacedTile P} (hAB : Disjoint (interior A.carrier) (interior B.carrier))
    {i : Fin (P.disk A.form).n} {j : Fin (P.disk B.form).n} (hside : A.side i = B.side j)
    {y : Pt} (hy : y ∈ A.side i) (hya : y ≠ A.vertex i)
    (hyb : y ≠ A.vertex (finRotate (P.disk A.form).n i)) :
    y ∈ interior (A.carrier ∪ B.carrier) := by
  have hyA : y ∈ A.carrier :=
    hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_side_subset_carrier A i hy
  have hyBj : y ∈ B.side j := hside ▸ hy
  have hyB : y ∈ B.carrier :=
    hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_side_subset_carrier B j hyBj
  have hnA : y ∉ interior A.carrier :=
    hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_not_interior hAB hyB
  have hnB : y ∉ interior B.carrier :=
    hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_not_interior hAB.symm hyA
  have hvA : y ∉ A.vertexSet := by
    rintro ⟨k, hk⟩
    by_cases hki : k = i
    · rw [hki] at hk
      exact hya hk.symm
    · have hyk : y ∈ A.side k := by
        rw [← hk]
        exact hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_vertex_mem_side A k
      rcases hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_side_inter A hki
          hyk hy with h | h
      · exact hya h
      · exact hyb h
  have hvB : y ∉ B.vertexSet := by
    rintro ⟨k, hk⟩
    have hend : y = B.vertex j ∨ y = B.vertex (finRotate _ j) := by
      by_cases hkj : k = j
      · rw [hkj] at hk
        exact Or.inl hk.symm
      · have hyk : y ∈ B.side k := by
          rw [← hk]
          exact hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_vertex_mem_side B k
        exact hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_side_inter B hkj
          hyk hyBj
    have hseg := hside
    rw [hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_side_eq_segment,
      hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_side_eq_segment] at hseg
    rcases hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_segment_endpoints hseg
      with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hend with h | h
      · exact hya (h.trans h1.symm)
      · exact hyb (h.trans h2.symm)
    · rcases hend with h | h
      · exact hyb (h.trans h2.symm)
      · exact hya (h.trans h1.symm)
  obtain ⟨_, ε₁, d₁, n₁, hε₁, hd₁, hn₁, hnd₁, _, hy₁⟩ := cc_halfdisk_tile A hyA hnA hvA
  obtain ⟨_, ε₂, _, n₂, hε₂, _, hn₂, _, _, hy₂⟩ := cc_halfdisk_tile B hyB hnB hvB
  have hm1 := min_le_left ε₁ ε₂
  have hm2 := min_le_right ε₁ ε₂
  have hmpos : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have key : inner ℝ n₂ d₁ = 0 := by
    by_contra hne
    obtain ⟨w, hw2, hw1⟩ : ∃ w : Pt, 0 < inner ℝ n₂ w ∧ inner ℝ n₁ w = 0 := by
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨-d₁, by rw [inner_neg_right]; linarith, by rw [inner_neg_right, hnd₁, neg_zero]⟩
      · exact ⟨d₁, h, hnd₁⟩
    set c := (|inner ℝ n₂ n₁| + 1) / inner ℝ n₂ w with hc
    set u := n₁ + c • w with hu
    have hu2 : 0 < inner ℝ n₂ u := by
      rw [hu, inner_add_right, inner_smul_right, hc, div_mul_cancel₀ _ hw2.ne']
      have := neg_abs_le (inner ℝ n₂ n₁); linarith
    have hu1 : 0 < inner ℝ n₁ u := by
      rw [hu, inner_add_right, inner_smul_right, hw1, mul_zero, add_zero,
        real_inner_self_eq_norm_sq]
      have := norm_pos_iff.mpr hn₁; positivity
    have hu0 : u ≠ 0 := by rintro h; rw [h, inner_zero_right] at hu1; exact lt_irrefl _ hu1
    have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    set δ := min ε₁ ε₂ / (2 * ‖u‖) with hδ
    have hδpos : 0 < δ := div_pos (lt_min hε₁ hε₂) (by positivity)
    have hdist : dist (y + δ • u) y = min ε₁ ε₂ / 2 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδpos.le, hδ]
      field_simp
    have h1 : y + δ • u ∈ interior A.carrier := by
      apply hy₁ _ (by rw [hdist]; linarith)
      rw [add_sub_cancel_left, inner_smul_right]; positivity
    have h2 : y + δ • u ∈ interior B.carrier := by
      apply hy₂ _ (by rw [hdist]; linarith)
      rw [add_sub_cancel_left, inner_smul_right]; positivity
    exact Set.disjoint_left.mp hAB h1 h2
  have hpar1 : inner ℝ d₁ n₂ = 0 := by rw [real_inner_comm]; exact key
  have hpar2 : inner ℝ d₁ n₁ = 0 := by rw [real_inner_comm]; exact hnd₁
  obtain ⟨c, hc⟩ := cc_parallel (n := d₁) (a := n₂) (b := n₁) hd₁ hn₁ hpar1 hpar2
  have hn1 : 0 < inner ℝ n₁ n₁ := by
    rw [real_inner_self_eq_norm_sq]
    have := norm_pos_iff.mpr hn₁
    positivity
  have hc0 : c < 0 := by
    by_contra hcn
    push_neg at hcn
    have hcpos : 0 < c := by
      rcases hcn.lt_or_eq with h | h
      · exact h
      · exfalso
        apply hn₂
        rw [hc, ← h, zero_smul]
    have hnorm : 0 < ‖n₁‖ := norm_pos_iff.mpr hn₁
    set δ := min ε₁ ε₂ / (2 * ‖n₁‖) with hδ
    have hδpos : 0 < δ := div_pos (lt_min hε₁ hε₂) (by positivity)
    have hdist : dist (y + δ • n₁) y = min ε₁ ε₂ / 2 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδpos.le, hδ]
      field_simp
    have h1 : y + δ • n₁ ∈ interior A.carrier := by
      apply hy₁ _ (by rw [hdist]; linarith)
      rw [add_sub_cancel_left, real_inner_smul_right]
      positivity
    have h2 : y + δ • n₁ ∈ interior B.carrier := by
      apply hy₂ _ (by rw [hdist]; linarith)
      rw [add_sub_cancel_left, real_inner_smul_right, hc, real_inner_smul_left]
      positivity
    exact Set.disjoint_left.mp hAB h1 h2
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  refine ⟨min ε₁ ε₂, hmpos, fun z hz => ?_⟩
  have hzy : dist z y < min ε₁ ε₂ := Metric.mem_ball.mp hz
  have hz1 : dist z y < ε₁ := lt_of_lt_of_le hzy hm1
  have hz2 : dist z y < ε₂ := lt_of_lt_of_le hzy hm2
  rcases lt_trichotomy (inner ℝ n₁ (z - y)) 0 with hneg | hzero | hpos
  · apply Set.mem_union_right
    apply interior_subset
    apply hy₂ z hz2
    rw [hc, real_inner_smul_left]
    exact mul_pos_of_neg_of_neg hc0 hneg
  · apply Set.mem_union_left
    rw [← cc_tile_regular A, Metric.mem_closure_iff]
    intro e he
    have hnorm : 0 < ‖n₁‖ := norm_pos_iff.mpr hn₁
    have hgap : 0 < ε₁ - dist z y := by linarith
    have hmin : 0 < min e (ε₁ - dist z y) := lt_min he hgap
    set δ := min e (ε₁ - dist z y) / (2 * ‖n₁‖) with hδ
    have hδpos : 0 < δ := div_pos hmin (by positivity)
    have hdz : dist (z + δ • n₁) z = min e (ε₁ - dist z y) / 2 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδpos.le, hδ]
      field_simp
    have hme1 := min_le_left e (ε₁ - dist z y)
    have hme2 := min_le_right e (ε₁ - dist z y)
    refine ⟨z + δ • n₁, ?_, ?_⟩
    · apply hy₁
      · calc dist (z + δ • n₁) y ≤ dist (z + δ • n₁) z + dist z y := dist_triangle _ _ _
          _ < ε₁ := by rw [hdz]; linarith
      · have hsplit : z + δ • n₁ - y = (z - y) + δ • n₁ := by abel
        rw [hsplit, inner_add_right, hzero, zero_add, real_inner_smul_right]
        positivity
    · rw [dist_comm, hdz]
      linarith
  · exact Set.mem_union_left _ (interior_subset (hy₁ z hz1 hpos))

/-- Step 3 of the blueprint proof of `hereditary_sts_substitution_sofic_step2_raw_child_is_full`:
collar neighbourhood saturation.  For `γ ∈ Γ(q)` the collar covers an open neighbourhood of the
support of `Δ q`: interior points of tiles are trivial, marked vertices are covered by their
exact full stars, and the remaining frontier points lie in the relative interior of a side which
is shared with a second collar tile (Steps 1 and 2). -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_step3_collar_nhds
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P) (q : C.Q.Form)
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C q) :
    support (C.Δ q).tiles ⊆
      interior (support (hereditary_sts_substitution_sofic_collar τ hsts C q γ.1)) := by
  intro y hy
  simp only [support, mem_iUnion] at hy
  obtain ⟨A, hA, hyA⟩ := hy
  have hAcol : A ∈ hereditary_sts_substitution_sofic_collar τ hsts C q γ.1 := Or.inl hA
  have hsub : ∀ X ∈ hereditary_sts_substitution_sofic_collar τ hsts C q γ.1,
      X.carrier ⊆ support (hereditary_sts_substitution_sofic_collar τ hsts C q γ.1) := by
    intro X hX z hz
    simp only [support, mem_iUnion]
    exact ⟨X, hX, hz⟩
  by_cases hint : y ∈ interior A.carrier
  · exact interior_mono (hsub A hAcol) hint
  by_cases hv : y ∈ A.vertexSet
  · have hyV : y ∈ hereditary_sts_substitution_sofic_macroVertices C q := by
      simp only [hereditary_sts_substitution_sofic_macroVertices, Set.Finite.mem_toFinset,
        Set.mem_setOf_eq]
      exact ⟨A, hA, hv⟩
    have hcr : Substitution.crown (hereditary_sts_substitution_sofic_collar τ hsts C q γ.1) y =
        translateSet y (γ.1 ⟨y, hyV⟩).1 := γ.2.2.2.1 ⟨y, hyV⟩
    have hfull := (γ.1 ⟨y, hyV⟩).2
    simp only [hereditary_sts_substitution_sofic_fullCrowns, Finset.mem_filter] at hfull
    have hy' : y ∈ interior (support (Substitution.crown
        (hereditary_sts_substitution_sofic_collar τ hsts C q γ.1) y)) := by
      rw [hcr, cc_support_translate, interior_vadd]
      have h := vadd_mem_vadd_set (a := y) hfull.2
      simpa only [vadd_eq_add, add_zero] using h
    refine interior_mono ?_ hy'
    intro z hz
    simp only [support, mem_iUnion] at hz ⊢
    obtain ⟨B, hB, hzB⟩ := hz
    exact ⟨B, hB.1, hzB⟩
  · obtain ⟨i, ε, d, n, hε, -, -, -, hs, -⟩ := cc_halfdisk_tile A hyA hint hv
    have hyi : y ∈ A.side i := by simpa using hs 0 (by simpa using hε)
    obtain ⟨B, hB, hBA, j, hBj⟩ :=
      hereditary_sts_substitution_sofic_step2_raw_child_is_full_step1_side_partner
        τ hsts C q γ A hA i
    have hdisj : Disjoint (interior A.carrier) (interior B.carrier) :=
      γ.2.1 hAcol hB (Ne.symm hBA)
    have hy1 : y ≠ A.vertex i := fun h => hv ⟨i, h.symm⟩
    have hy2 : y ≠ A.vertex (finRotate _ i) := fun h => hv ⟨_, h.symm⟩
    have h := hereditary_sts_substitution_sofic_step2_raw_child_is_full_step2_common_side_nhds
      hdisj hBj.symm hyi hy1 hy2
    exact interior_mono (union_subset (hsub A hAcol) (hsub B hB)) h

/-- Step 4 of the blueprint proof of `hereditary_sts_substitution_sofic_step2_raw_child_is_full`:
certificate compatibility.  The positioned child vertex `a_t + v` is a listed vertex of the
decomposition `τ^m (Δ (owner t))`, since `Δ σ' = τ^m Δ` and the child `t` belongs to the
template `σ' (owner t)`. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_step4_child_vertex
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m) (t : C.Typ)
    (v : ↥(hereditary_sts_substitution_sofic_macroVertices C (C.form t))) :
    ∃ X ∈ τ.decomposeIter m (C.Δ (C.owner t)).tiles, ∃ k, X.vertex k = C.anchor t + v.1 := by
  have _ := hsts
  have hv := v.2
  simp only [hereditary_sts_substitution_sofic_macroVertices, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq] at hv
  obtain ⟨A, hA, k, hk⟩ := hv
  refine ⟨A.translate (C.anchor t), ?_, k, ?_⟩
  · rw [← hC.compat (C.owner t)]
    simp only [Set.mem_iUnion]
    refine ⟨⟨C.form t, C.anchor t⟩, ?_, A, hA, rfl⟩
    rw [C.rule_eq]
    exact ⟨t, rfl, rfl⟩
  · rw [hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_vertex_translate, hk]

/-- Step 5 of the blueprint proof of `hereditary_sts_substitution_sofic_step2_raw_child_is_full`:
the decomposed collar `τ^m coll(γ)` covers a neighbourhood of the positioned child vertex
`a_t + v` (Steps 3 and 4, scaled by `θ^m`). -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_step5_child_nhds
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m) (t : C.Typ)
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.owner t))
    (v : ↥(hereditary_sts_substitution_sofic_macroVertices C (C.form t))) :
    C.anchor t + v.1 ∈ interior (support (τ.decomposeIter m
      (hereditary_sts_substitution_sofic_collar τ hsts C (C.owner t) γ.1))) := by
  obtain ⟨X, hX, k, hk⟩ :=
    hereditary_sts_substitution_sofic_step2_raw_child_is_full_step4_child_vertex
      τ hsts C m hC t v
  have hθ : τ.θ ^ m ≠ 0 := pow_ne_zero _ (by linarith [τ.one_lt])
  have hxD : C.anchor t + v.1 ∈ support (τ.decomposeIter m (C.Δ (C.owner t)).tiles) := by
    simp only [support, mem_iUnion]
    refine ⟨X, hX, ?_⟩
    rw [← hk]
    exact hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_vertex_mem_carrier X k
  rw [hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_support_decomposeIter]
    at hxD ⊢
  rw [interior_smul₀ hθ]
  exact smul_set_mono
    (hereditary_sts_substitution_sofic_step2_raw_child_is_full_step3_collar_nhds
      τ hsts C (C.owner t) γ) hxD

/-- Step 6 of the blueprint proof of `hereditary_sts_substitution_sofic_step2_raw_child_is_full`:
joint allowedness is inherited by the decomposed collar: if a translate of `coll(γ)` lies in
`τ^n p`, then a translate of `τ^m coll(γ)` lies in `τ^(n+m) p`. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_step6_supertile
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (q : C.Q.Form) (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C q) :
    ∃ (n : ℕ) (p : P.Form) (u : Pt),
      translateSet u (τ.decomposeIter m (hereditary_sts_substitution_sofic_collar τ hsts C q γ.1))
        ⊆ τ.supertile n p := by
  obtain ⟨n, p, a, ha⟩ := γ.2.2.2.2
  refine ⟨n + m, p, τ.θ ^ m • a, ?_⟩
  rw [← hierarchy_lift_iff_decomposeIter_translate]
  calc τ.decomposeIter m (translateSet a
        (hereditary_sts_substitution_sofic_collar τ hsts C q γ.1))
      ⊆ τ.decomposeIter m (τ.supertile n p) :=
        hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_decomposeIter_mono τ m ha
    _ = τ.supertile (n + m) p :=
        hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_decomposeIter_add τ n m _

/-- Step 7 of the blueprint proof of `hereditary_sts_substitution_sofic_step2_raw_child_is_full`:
allowedness of the star.  If a translate of a family `D` lies in a supertile and `x` is a listed
vertex of `D` and an interior point of its support, then the star of `D` at `x`, translated to the
origin, is the star of the supertile at the translated vertex, hence an allowed crown. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_step7_allowed
    {τ : Substitution P} {D : Set (PlacedTile P)} {x u : Pt} {n : ℕ} {p : P.Form}
    (hD : translateSet u D ⊆ τ.supertile n p) (hv : Substitution.IsVertexOf D x)
    (hx : x ∈ interior (support D)) :
    τ.IsAllowedCrown (translateSet (-x) (Substitution.crown D x)) := by
  obtain ⟨X, hX, k, hk⟩ := hv
  have hfin : (translateSet u D).Finite :=
    (hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_decomposeIter_finite τ n
      (Set.finite_singleton (⟨p, 0⟩ : PlacedTile P))).subset hD
  have hcrown : Substitution.crown (τ.supertile n p) (u + x) =
      translateSet u (Substitution.crown D x) := by
    ext Y
    constructor
    · rintro ⟨hY, hxY⟩
      have hint : u + x ∈ interior (support (translateSet u D)) := by
        rw [cc_support_translate, interior_vadd]
        exact vadd_mem_vadd_set hx
      have hYD := hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_mem_of_interior
        (hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_supertile_disjoint τ n p)
        hD hfin hint hY hxY
      obtain ⟨Z, hZ, rfl⟩ := hYD
      refine ⟨Z, ⟨hZ, ?_⟩, rfl⟩
      rw [hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_carrier_translate,
        ← vadd_eq_add, vadd_mem_vadd_set_iff] at hxY
      exact hxY
    · rintro ⟨Z, ⟨hZ, hxZ⟩, rfl⟩
      refine ⟨hD ⟨Z, hZ, rfl⟩, ?_⟩
      rw [hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_carrier_translate]
      exact vadd_mem_vadd_set hxZ
  refine ⟨n, p, u + x, ⟨X.translate u, hD ⟨X, hX, rfl⟩, k, ?_⟩, ?_⟩
  · rw [hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_vertex_translate, hk]
  · rw [hcrown, cc_translateSet_translateSet]
    congr 1
    abel

/-- Step 8 of the blueprint proof of `hereditary_sts_substitution_sofic_step2_raw_child_is_full`:
fullness of the star.  If `x` is an interior point of the support of a finite family `D`, then
the star of `D` at `x` covers a neighbourhood of `x`, so its translate to the origin covers a
neighbourhood of `0`. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full_step8_full
    {D : Set (PlacedTile P)} (hD : D.Finite) {x : Pt} (hx : x ∈ interior (support D)) :
    (0 : Pt) ∈ interior (support (translateSet (-x) (Substitution.crown D x))) := by
  have hE : {Y ∈ D | x ∉ Y.carrier}.Finite := hD.subset (sep_subset _ _)
  have hclosed : IsClosed (⋃ Y ∈ {Y ∈ D | x ∉ Y.carrier}, Y.carrier) :=
    hE.isClosed_biUnion fun Y _ => cc_tile_carrier_closed Y
  have hxint : x ∈ interior (support (Substitution.crown D x)) := by
    rw [mem_interior]
    refine ⟨interior (support D) \ ⋃ Y ∈ {Y ∈ D | x ∉ Y.carrier}, Y.carrier, ?_,
      isOpen_interior.sdiff hclosed, ?_⟩
    · rintro z ⟨hz, hzE⟩
      have hzD := interior_subset hz
      simp only [support, mem_iUnion] at hzD ⊢
      obtain ⟨Y, hY, hzY⟩ := hzD
      by_cases hxY : x ∈ Y.carrier
      · exact ⟨Y, ⟨hY, hxY⟩, hzY⟩
      · exfalso
        apply hzE
        simp only [mem_iUnion]
        exact ⟨Y, ⟨hY, hxY⟩, hzY⟩
    · refine ⟨hx, ?_⟩
      simp only [mem_iUnion, not_exists]
      intro Y hY hxY
      exact hY.2 hxY
  rw [cc_support_translate, interior_vadd]
  have h := vadd_mem_vadd_set (a := -x) hxint
  simpa only [vadd_eq_add, neg_add_cancel] using h

/-- Step 2a of the reviewed proof: each raw child star is again a full allowed
crown.  The proof uses joint allowedness, collar neighbourhood saturation and
the certificate compatibility equation. -/
private lemma hereditary_sts_substitution_sofic_step2_raw_child_is_full
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m) (t : C.Typ)
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.owner t))
    (v : ↥(hereditary_sts_substitution_sofic_macroVertices C (C.form t))) :
    hereditary_sts_substitution_sofic_rawChildCrown τ hsts C m t γ v ∈
      hereditary_sts_substitution_sofic_fullCrowns τ hsts := by
  obtain ⟨X, hX, k, hk⟩ :=
    hereditary_sts_substitution_sofic_step2_raw_child_is_full_step4_child_vertex
      τ hsts C m hC t v
  have hx := hereditary_sts_substitution_sofic_step2_raw_child_is_full_step5_child_nhds
    τ hsts C m hC t γ v
  obtain ⟨n, p, u, hu⟩ :=
    hereditary_sts_substitution_sofic_step2_raw_child_is_full_step6_supertile
      τ hsts C m (C.owner t) γ
  have hvert : Substitution.IsVertexOf (τ.decomposeIter m
      (hereditary_sts_substitution_sofic_collar τ hsts C (C.owner t) γ.1)) (C.anchor t + v.1) :=
    ⟨X, hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_decomposeIter_mono τ m
      subset_union_left hX, k, hk⟩
  have hfin : (τ.decomposeIter m
      (hereditary_sts_substitution_sofic_collar τ hsts C (C.owner t) γ.1)).Finite :=
    hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_decomposeIter_finite τ m
      (hereditary_sts_substitution_sofic_step2_raw_child_is_full_aux_collar_finite
        τ hsts C (C.owner t) γ.1)
  simp only [hereditary_sts_substitution_sofic_fullCrowns, Finset.mem_filter,
    Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  exact ⟨hereditary_sts_substitution_sofic_step2_raw_child_is_full_step7_allowed hu hvert hx,
    hereditary_sts_substitution_sofic_step2_raw_child_is_full_step8_full hfin hx⟩

/-- The child crown vector `F_t(γ)`. -/
private noncomputable def hereditary_sts_substitution_sofic_childVector
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m) (t : C.Typ)
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.owner t)) :
    hereditary_sts_substitution_sofic_CrownVector τ hsts C (C.form t) :=
  fun v => ⟨hereditary_sts_substitution_sofic_rawChildCrown τ hsts C m t γ v,
    hereditary_sts_substitution_sofic_step2_raw_child_is_full τ hsts C m hC t γ v⟩

/-- Iterated decomposition is monotone in the decomposed set (helper for Step 2b). -/
private lemma hereditary_sts_substitution_sofic_step2_child_catalog_closed_mono
    (τ : Substitution P) (j : ℕ) {S S' : Set (PlacedTile P)} (h : S ⊆ S') :
    τ.decomposeIter j S ⊆ τ.decomposeIter j S' := by
  induction j with
  | zero => exact h
  | succ j ih => exact Set.biUnion_subset_biUnion_left ih

/-- Iterated decompositions add up (helper for Step 2b). -/
private lemma hereditary_sts_substitution_sofic_step2_child_catalog_closed_add
    (τ : Substitution P) (j n : ℕ) (S : Set (PlacedTile P)) :
    τ.decomposeIter j (τ.decomposeIter n S) = τ.decomposeIter (n + j) S := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show τ.decompose (τ.decomposeIter j (τ.decomposeIter n S)) =
      τ.decompose (τ.decomposeIter (n + j) S)
    rw [ih]

/-- A set of placed tiles whose translate has pairwise disjoint interiors has pairwise disjoint
interiors itself (helper for Step 2b). -/
private lemma hereditary_sts_substitution_sofic_step2_child_catalog_closed_disjoint
    {S : Set (PlacedTile P)} {v : Pt} (h : DisjointInteriors (translateSet v S)) :
    DisjointInteriors S := by
  intro A hA B hB hne
  have hne' : A.translate v ≠ B.translate v := by
    intro heq
    apply hne
    have := congrArg (fun Z : PlacedTile P => Z.translate (-v)) heq
    simpa only [cc_translate_translate, neg_add_cancel, cc_translate_zero] using this
  have hd := h (cc_translate_mem v hA) (cc_translate_mem v hB) hne'
  simp only [Function.onFun, dissection_preserves_sofic_carrier_translate, interior_vadd] at hd
  exact (Set.disjoint_image_iff (add_right_injective v)).mp hd

/-- Witness transport (helper for Step 2b): if the translate of `K` by `b` lies in the
decomposed collar `τ^m Col`, and a translate of `Col` lies in the supertile `τ^n p`, then a
translate of `K` lies in the supertile `τ^(n+m) p`. -/
private lemma hereditary_sts_substitution_sofic_step2_child_catalog_closed_transport
    (τ : Substitution P) (m n : ℕ) (p : P.Form) (a b : Pt) {Col K : Set (PlacedTile P)}
    (hKD : translateSet b K ⊆ τ.decomposeIter m Col)
    (hCol : translateSet a Col ⊆ τ.supertile n p) :
    translateSet (τ.θ ^ m • a + b) K ⊆ τ.supertile (n + m) p := by
  calc translateSet (τ.θ ^ m • a + b) K
      = translateSet (τ.θ ^ m • a) (translateSet b K) :=
        (cc_translateSet_translateSet K b (τ.θ ^ m • a)).symm
    _ ⊆ translateSet (τ.θ ^ m • a) (τ.decomposeIter m Col) := cc_translateSet_mono _ hKD
    _ = τ.decomposeIter m (translateSet a Col) :=
        (hierarchy_lift_iff_decomposeIter_translate τ m a Col).symm
    _ ⊆ τ.decomposeIter m (τ.supertile n p) :=
        hereditary_sts_substitution_sofic_step2_child_catalog_closed_mono τ m hCol
    _ = τ.supertile (n + m) p := by
        change τ.decomposeIter m (τ.decomposeIter n {⟨p, 0⟩}) =
          τ.decomposeIter (n + m) {⟨p, 0⟩}
        exact hereditary_sts_substitution_sofic_step2_child_catalog_closed_add τ m n _

/-- Membership in a raw child crown (helper for Step 2b): a tile `Z` lies in the raw child crown
at the marked vertex `v` iff its translate by the positioned vertex `a_t + v` lies in the physical
star of the decomposed parent collar at that vertex. -/
private lemma hereditary_sts_substitution_sofic_step2_child_catalog_closed_mem_raw
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (t : C.Typ)
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.owner t))
    (v : ↥(hereditary_sts_substitution_sofic_macroVertices C (C.form t)))
    (Z : PlacedTile P) :
    Z ∈ hereditary_sts_substitution_sofic_rawChildCrown τ hsts C m t γ v ↔
      Z.translate (C.anchor t + v.1) ∈ Substitution.crown
        (τ.decomposeIter m
          (hereditary_sts_substitution_sofic_collar τ hsts C (C.owner t) γ.1))
        (C.anchor t + v.1) := by
  show Z ∈ translateSet (-(C.anchor t + v.1)) _ ↔ _
  rw [cc_mem_translateSet, neg_neg]

/-- The key inclusion of Step 2b: the child collar `coll(F_t(γ))`, translated by the anchor
`a_t`, is a subpatch of the decomposed parent collar `τ^m coll(γ)`.  The scattered group of
`form t` is covered by the compatibility equation `Δσ' = τ^m Δ` and the recorded child crowns
are, by definition, stars of the decomposed collar. -/
private lemma hereditary_sts_substitution_sofic_step2_child_catalog_closed_collar_subset
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m) (t : C.Typ)
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.owner t)) :
    translateSet (C.anchor t)
      (hereditary_sts_substitution_sofic_collar τ hsts C (C.form t)
        (hereditary_sts_substitution_sofic_childVector τ hsts C m hC t γ)) ⊆
      τ.decomposeIter m
        (hereditary_sts_substitution_sofic_collar τ hsts C (C.owner t) γ.1) := by
  rintro X ⟨Y, hY, rfl⟩
  rcases hY with hY | hY
  · have hmem : Y.translate (C.anchor t) ∈ ⋃ A ∈ (C.σ.rule (C.owner t)).tiles,
        translateSet A.anchor (C.Δ A.form).tiles := by
      rw [Set.mem_iUnion₂]
      refine ⟨⟨C.form t, C.anchor t⟩, ?_, Y, hY, rfl⟩
      rw [C.rule_eq]
      exact ⟨t, rfl, rfl⟩
    rw [hC.compat] at hmem
    exact hereditary_sts_substitution_sofic_step2_child_catalog_closed_mono τ m
      Set.subset_union_left hmem
  · obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hY
    have h1 := cc_mem_translateSet.mp hv
    have h2 := (hereditary_sts_substitution_sofic_step2_child_catalog_closed_mem_raw
      τ hsts C m t γ v _).mp h1
    rw [cc_translate_translate, show C.anchor t + v.1 + -v.1 = C.anchor t by abel] at h2
    exact h2.1

/-- The crown condition of Step 2b: in the child collar, the physical crown at each marked vertex
`v` of `form t` is exactly the recorded child crown translated to `v`. -/
private lemma hereditary_sts_substitution_sofic_step2_child_catalog_closed_crown_eq
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m) (t : C.Typ)
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.owner t))
    (v : ↥(hereditary_sts_substitution_sofic_macroVertices C (C.form t))) :
    Substitution.crown
        (hereditary_sts_substitution_sofic_collar τ hsts C (C.form t)
          (hereditary_sts_substitution_sofic_childVector τ hsts C m hC t γ)) v.1 =
      translateSet v.1
        ((hereditary_sts_substitution_sofic_childVector τ hsts C m hC t γ) v).1 := by
  ext X
  have hraw := hereditary_sts_substitution_sofic_step2_child_catalog_closed_mem_raw
    τ hsts C m t γ v (X.translate (-v.1))
  rw [cc_translate_translate, show C.anchor t + v.1 + -v.1 = C.anchor t by abel] at hraw
  have hcar : ∀ y : Pt, y ∈ (X.translate (C.anchor t)).carrier ↔
      -C.anchor t + y ∈ X.carrier := by
    intro y
    rw [dissection_preserves_sofic_carrier_translate, Set.mem_vadd_set_iff_neg_vadd_mem]
    rfl
  constructor
  · rintro ⟨hXK, hXv⟩
    rw [cc_mem_translateSet]
    refine hraw.mpr ⟨?_, ?_⟩
    · exact hereditary_sts_substitution_sofic_step2_child_catalog_closed_collar_subset
        τ hsts C m hC t γ ⟨X, hXK, rfl⟩
    · rw [hcar, show -C.anchor t + (C.anchor t + v.1) = v.1 by abel]
      exact hXv
  · intro hX
    have hX' := cc_mem_translateSet.mp hX
    have h := (hraw.mp hX').2
    rw [hcar, show -C.anchor t + (C.anchor t + v.1) = v.1 by abel] at h
    exact ⟨Or.inr (Set.mem_iUnion.mpr ⟨v, hX⟩), h⟩

/-- Step 2b of the reviewed proof: `F_t(γ)` satisfies all four catalogue
conditions, including a single joint supertile witness. -/
private lemma hereditary_sts_substitution_sofic_step2_child_catalog_closed
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m) (t : C.Typ)
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.owner t)) :
    DisjointInteriors
        (hereditary_sts_substitution_sofic_collar τ hsts C (C.form t)
          (hereditary_sts_substitution_sofic_childVector τ hsts C m hC t γ)) ∧
    SideToSideSet
        (hereditary_sts_substitution_sofic_collar τ hsts C (C.form t)
          (hereditary_sts_substitution_sofic_childVector τ hsts C m hC t γ)) ∧
    (∀ v,
      Substitution.crown
          (hereditary_sts_substitution_sofic_collar τ hsts C (C.form t)
            (hereditary_sts_substitution_sofic_childVector τ hsts C m hC t γ)) v.1 =
        translateSet v.1
          ((hereditary_sts_substitution_sofic_childVector τ hsts C m hC t γ) v).1) ∧
    hereditary_sts_substitution_sofic_JointAllowed τ hsts C (C.form t)
      (hereditary_sts_substitution_sofic_childVector τ hsts C m hC t γ) := by
  obtain ⟨n, p, a, ha⟩ := γ.2.2.2.2
  have hsub := hereditary_sts_substitution_sofic_step2_child_catalog_closed_transport
    τ m n p a (C.anchor t)
    (hereditary_sts_substitution_sofic_step2_child_catalog_closed_collar_subset
      τ hsts C m hC t γ) ha
  refine ⟨?_, ?_, fun v =>
    hereditary_sts_substitution_sofic_step2_child_catalog_closed_crown_eq
      τ hsts C m hC t γ v, ⟨n + m, p, _, hsub⟩⟩
  · exact hereditary_sts_substitution_sofic_step2_child_catalog_closed_disjoint
      (Set.PairwiseDisjoint.subset (Crowns.supertile_disjoint τ (n + m) p) hsub)
  · exact Substitution.STS.decomposeIter_sts_of_subset_supertile hsts hsub 0

/-- The catalogue-valued child operator. -/
private noncomputable def hereditary_sts_substitution_sofic_childCatalog
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m) (t : C.Typ)
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.owner t)) :
    hereditary_sts_substitution_sofic_Catalog τ hsts C (C.form t) :=
  ⟨hereditary_sts_substitution_sofic_childVector τ hsts C m hC t γ,
    hereditary_sts_substitution_sofic_step2_child_catalog_closed
      τ hsts C m hC t γ⟩

/-- A physical endpoint packet.  `none` is the absent endpoint marker; a
nonempty entry contains an actual member of the full-crown list. -/
private abbrev hereditary_sts_substitution_sofic_CrownPacket
    (τ : Substitution P) (hsts : τ.STS) :=
  Option (hereditary_sts_substitution_sofic_FullCrown τ hsts) ×
    Option (hereditary_sts_substitution_sofic_FullCrown τ hsts)

/-- The nonrecursive header: old positioned type, zero-mode bits, and the
catalogue value decoded from physical endpoint packets. -/
private abbrev hereditary_sts_substitution_sofic_CrownHeader
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P) :=
  Σ t : C.Typ,
    (C.Side t → Bool) ×
      Option (hereditary_sts_substitution_sofic_Catalog τ hsts C (C.form t))

/-- The extended finite symbol alphabet.  Old strict symbols remain a
separate summand, so crown packets cannot be confused with identities,
schedules, zero, bottom, or headers. -/
private abbrev hereditary_sts_substitution_sofic_ExtSymbol
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    {m : ℕ} (hC : C.Represents τ m) :=
  Planned.Strict.SU C hC ⊕
    (hereditary_sts_substitution_sofic_CrownPacket τ hsts ⊕
      hereditary_sts_substitution_sofic_CrownHeader τ hsts C)

/-- Extended tiles retain the old positioned type and five cells per listed
side; only the finite cell alphabet is enlarged. -/
private abbrev hereditary_sts_substitution_sofic_ExtTile
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    {m : ℕ} (hC : C.Represents τ m) :=
  Σ t : C.Typ,
    C.Side t → Fin 5 →
      hereditary_sts_substitution_sofic_ExtSymbol τ hsts C hC

/-- A global, translation-invariant strict order of two distinct endpoints. -/
private def hereditary_sts_substitution_sofic_pointLT (x y : Pt) : Prop :=
  x 0 < y 0 ∨ (x 0 = y 0 ∧ x 1 < y 1)

/-- Look up the crown recorded at a physical marked vertex. -/
private noncomputable def hereditary_sts_substitution_sofic_lookupCrown
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (q : C.Q.Form)
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C q) (v : Pt) :
    Option (hereditary_sts_substitution_sofic_FullCrown τ hsts) :=
  if hv : v ∈ hereditary_sts_substitution_sofic_macroVertices C q then
    some (γ.1 ⟨v, hv⟩)
  else none

/-- The canonically ordered packet at the two endpoints of a grouped side. -/
private noncomputable def hereditary_sts_substitution_sofic_packetOf
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (t : C.Typ)
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.form t))
    (i : C.Side t) :
    hereditary_sts_substitution_sofic_CrownPacket τ hsts :=
  let x := (C.Q.disk (C.form t)).vertex i
  let y := (C.Q.disk (C.form t)).vertex
    (finRotate (C.Q.disk (C.form t)).n i)
  let atOwnerBoundary := fun v : Pt =>
    C.anchor t + v ∈ frontier (C.σ.θ • (C.Q.disk (C.owner t)).carrier)
  let read := fun v : Pt =>
    if atOwnerBoundary v then
      hereditary_sts_substitution_sofic_lookupCrown τ hsts C (C.form t) γ v
    else none
  if hereditary_sts_substitution_sofic_pointLT x y then
    (read x, read y)
  else
    (read y, read x)

/-- Encode an endpoint packet in the extended alphabet.  The doubly absent
packet is literally the old zero symbol; this is the convention needed on
ordinary internal non-print sides and along cyclic central chains. -/
private def hereditary_sts_substitution_sofic_encodePacket
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    {m : ℕ} (hC : C.Represents τ m)
    (p : hereditary_sts_substitution_sofic_CrownPacket τ hsts) :
    hereditary_sts_substitution_sofic_ExtSymbol τ hsts C hC :=
  match p with
  | (none, none) => Sum.inl 0
  | _ => Sum.inr (Sum.inl p)

/-- A tile physically decodes a catalogue value when every non-print second
cell is exactly the endpoint packet of that value.  Print second cells are
deliberately ignored: they are transit channels, not physical crown records. -/
private def hereditary_sts_substitution_sofic_Decodes
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    {m : ℕ} (hC : C.Represents τ m)
  (A : hereditary_sts_substitution_sofic_ExtTile τ hsts C hC)
  (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.form A.1)) : Prop :=
  (∀ i : C.Side A.1, ¬ C.IsPrint (C.occ A.1 i) →
    A.2 i 1 = hereditary_sts_substitution_sofic_encodePacket τ hsts C hC
      (hereditary_sts_substitution_sofic_packetOf τ hsts C A.1 γ i)) ∧
  ∀ v : ↥(hereditary_sts_substitution_sofic_macroVertices C (C.form A.1)),
    C.anchor A.1 + v.1 ∉ frontier
        (C.σ.θ • (C.Q.disk (C.owner A.1)).carrier) →
      (γ.1 v).1 =
        translateSet (-(C.anchor A.1 + v.1))
          (Substitution.crown
            (τ.decomposeIter m (C.Δ (C.owner A.1)).tiles)
            (C.anchor A.1 + v.1))

/-- The total decoder used by the header.  Ambiguous or malformed arrays
decode to `none`, which the incidence colours below reject. -/
private noncomputable def hereditary_sts_substitution_sofic_decode
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    {m : ℕ} (hC : C.Represents τ m)
    (A : hereditary_sts_substitution_sofic_ExtTile τ hsts C hC) :
    Option (hereditary_sts_substitution_sofic_Catalog τ hsts C (C.form A.1)) :=
  if h : ∃! γ, hereditary_sts_substitution_sofic_Decodes τ hsts C hC A γ then
    some h.exists.choose
  else none

/-- The nonrecursive header computed from the old type, actual fourth cells,
and the physical packet decoder. -/
private noncomputable def hereditary_sts_substitution_sofic_header
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    {m : ℕ} (hC : C.Represents τ m)
    (A : hereditary_sts_substitution_sofic_ExtTile τ hsts C hC) :
    hereditary_sts_substitution_sofic_CrownHeader τ hsts C :=
  ⟨A.1,
    (fun d => C.outerB A.1 d && decide (A.2 d 3 = Sum.inl 0)),
    hereditary_sts_substitution_sofic_decode τ hsts C hC A⟩

/-- Generated children use the reviewed packet channel in cell two, the
extended header in cell four, and the old strict copying graph everywhere. -/
private noncomputable def hereditary_sts_substitution_sofic_generate
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m)
    (A : hereditary_sts_substitution_sofic_ExtTile τ hsts C hC)
    (t : C.Typ) : hereditary_sts_substitution_sofic_ExtTile τ hsts C hC :=
  ⟨t, fun i k =>
    if hs : (Planned.copySource C (C.form A.1) (C.occ t i) k).Nonempty then
      A.2 hs.some.1 hs.some.2
    else if _hp : C.IsPrint (C.occ t i) then
      if k = 4 then
        Sum.inl (Planned.Strict.identSU C hC (C.edge (C.occ t i)))
      else Sum.inl 0
    else if k = 0 then
      if C.IsInner (C.occ t i) then
        Sum.inl (Planned.Strict.identSU C hC (C.edge (C.occ t i)))
      else Sum.inl 0
    else if k = 1 then
      match hereditary_sts_substitution_sofic_decode τ hsts C hC A with
      | none => Sum.inl 0
      | some γ =>
          if ht : C.owner t = C.form A.1 then
            hereditary_sts_substitution_sofic_encodePacket τ hsts C hC
              (hereditary_sts_substitution_sofic_packetOf τ hsts C t
                (hereditary_sts_substitution_sofic_childCatalog τ hsts C m hC t
                  (ht ▸ γ)) i)
          else Sum.inl 0
    else if k = 3 then
      if C.IsOuter (C.occ t i) then
        Sum.inl (Planned.Strict.schedU C hC (C.occ t i))
      else if C.IsBoundary (C.occ t i) then
        Sum.inr (Sum.inr
          (hereditary_sts_substitution_sofic_header τ hsts C hC A))
      else Sum.inl (Planned.Strict.botSU C hC)
    else Sum.inl 0⟩

/-- Step 3 of the reviewed proof: generation preserves packet consistency and
the physical decoder returns exactly `F_t(γ)`. -/
private lemma hereditary_sts_substitution_sofic_step3_generate_decodes_child
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m)
    (A : hereditary_sts_substitution_sofic_ExtTile τ hsts C hC)
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.form A.1))
    (hγ : hereditary_sts_substitution_sofic_Decodes τ hsts C hC A γ)
    (t : C.Typ) (ht : C.owner t = C.form A.1) :
    hereditary_sts_substitution_sofic_Decodes τ hsts C hC
      (hereditary_sts_substitution_sofic_generate τ hsts C m hC A t)
      (hereditary_sts_substitution_sofic_childCatalog τ hsts C m hC t (ht ▸ γ)) := by
  sorry

/-- The child relation for the extended arrays. -/
private def hereditary_sts_substitution_sofic_IsExtChild
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m)
    (A B : hereditary_sts_substitution_sofic_ExtTile τ hsts C hC) : Prop :=
  C.owner B.1 = C.form A.1 ∧
    B = hereditary_sts_substitution_sofic_generate τ hsts C m hC A B.1

/-- A copied cell reaches a generated source in finitely many ancestor
steps.  This is the reflexive-transitive closure of the old `copySource`
graph on the new finite alphabet. -/
private def hereditary_sts_substitution_sofic_ExtHasOrigin
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    {m : ℕ} (hC : C.Represents τ m)
    (ch : ℕ → hereditary_sts_substitution_sofic_ExtTile τ hsts C hC)
    (n : ℕ) (i : C.Side (ch n).1) (k : Fin 5) : Prop :=
  let State := Σ r : ℕ, C.Side (ch r).1 × Fin 5
  let step : State → State → Prop := fun a b =>
    ∃ (d : C.Side (ch (a.1 + 1)).1) (k' : Fin 5),
      (d, k') ∈ Planned.copySource C (C.form (ch (a.1 + 1)).1)
        (C.occ (ch a.1).1 a.2.1) a.2.2 ∧
      b = ⟨a.1 + 1, d, k'⟩
  ∃ s : State,
    Relation.ReflTransGen step ⟨n, i, k⟩ s ∧
    Planned.copySource C (C.form (ch (s.1 + 1)).1)
      (C.occ (ch s.1).1 s.2.1) s.2.2 = ∅

/-- Founded legality: every level decodes, every level is the generated child
of the next one, and a copied value on an infinite source-free chain is zero. -/
private def hereditary_sts_substitution_sofic_ExtLegal
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m)
    (A : hereditary_sts_substitution_sofic_ExtTile τ hsts C hC) : Prop :=
  ∃ ch : ℕ → hereditary_sts_substitution_sofic_ExtTile τ hsts C hC,
    ch 0 = A ∧
    (∀ n, hereditary_sts_substitution_sofic_IsExtChild
      τ hsts C m hC (ch (n + 1)) (ch n)) ∧
    (∀ n, (hereditary_sts_substitution_sofic_decode τ hsts C hC (ch n)).isSome) ∧
    ∀ (n : ℕ) (i : C.Side (ch n).1) (k : Fin 5),
      (Planned.copySource C (C.form (ch (n + 1)).1)
        (C.occ (ch n).1 i) k).Nonempty →
      ¬ hereditary_sts_substitution_sofic_ExtHasOrigin τ hsts C hC ch n i k →
      (ch n).2 i k = Sum.inl 0

/-- A typed side index and a decorated-form side index denote the same
geometric incidence.  `HEq` performs only the transport forced by the
presentation's exact disk/projection equations. -/
private def hereditary_sts_substitution_sofic_CoincidentTypedSides
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    {m : ℕ} (hC : C.Represents τ m) (dec : SideDecoration C.Q)
    (X Y : PlacedTile dec.P')
    (A B : hereditary_sts_substitution_sofic_ExtTile τ hsts C hC)
    (i : C.Side A.1) (j : C.Side B.1) : Prop :=
  ∃ (i' : Fin (dec.P'.disk X.form).n) (j' : Fin (dec.P'.disk Y.form).n),
    HEq i i' ∧ HEq j j' ∧ X.side i' = Y.side j'

/-- A crown-control presentation packages the finite side decoration together
with the exact contracts supplied by its illegal-incidence colours.  These
fields prevent the constant-colour degeneracy rejected in the earlier attempt. -/
private structure hereditary_sts_substitution_sofic_CrownPresentation
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m) where
  dec : SideDecoration C.Q
  formEquiv : dec.P'.Form ≃
    hereditary_sts_substitution_sofic_ExtTile τ hsts C hC ⊕ C.Q.Form
  proj_typed : ∀ A, dec.proj (formEquiv.symm (Sum.inl A)) = C.form A.1
  proper_typed_legal : ∀ (T : PlaneTiling dec.P'), dec.Proper T →
    ∀ X ∈ T.tiles, ∃ A,
      formEquiv X.form = Sum.inl A ∧
      hereditary_sts_substitution_sofic_ExtLegal τ hsts C m hC A
  proper_cells_match : ∀ (T : PlaneTiling dec.P'), dec.Proper T →
    ∀ X ∈ T.tiles, ∀ Y ∈ T.tiles, X ≠ Y →
      ∀ A B, formEquiv X.form = Sum.inl A → formEquiv Y.form = Sum.inl B →
      ∀ (i : C.Side A.1) (j : C.Side B.1),
        hereditary_sts_substitution_sofic_CoincidentTypedSides
          τ hsts C hC dec X Y A B i j →
        A.2 i = B.2 j
  proper_of_typed_legal : ∀ (T : PlaneTiling dec.P'), T.SideToSide →
    (∀ X ∈ T.tiles, ∃ A, formEquiv X.form = Sum.inl A ∧
      hereditary_sts_substitution_sofic_ExtLegal τ hsts C m hC A) →
    (∀ X ∈ T.tiles, ∀ Y ∈ T.tiles, X ≠ Y →
      ∀ A B, formEquiv X.form = Sum.inl A → formEquiv Y.form = Sum.inl B →
      ∀ (i : C.Side A.1) (j : C.Side B.1),
        hereditary_sts_substitution_sofic_CoincidentTypedSides
          τ hsts C hC dec X Y A B i j → A.2 i = B.2 j) →
    dec.Proper T

/-- Step 4 of the reviewed proof: compile the implemented packet decoder,
generator, founded legality predicate and illegal-incidence colours into a
finite side decoration.  This step is only the finite encoding; it asserts no
completeness or reconstruction theorem. -/
private lemma hereditary_sts_substitution_sofic_step4_finite_side_encoding
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m) :
    Nonempty (hereditary_sts_substitution_sofic_CrownPresentation
      τ hsts C m hC) := by
  sorry

/-- The grouped tilings presented by the concrete crown side decoration. -/
private def hereditary_sts_substitution_sofic_controlFamily
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    {m : ℕ} {hC : C.Represents τ m}
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC) :
    Set (PlaneTiling C.Q) :=
  {T | ∃ T' : PlaneTiling X.dec.P', X.dec.Proper T' ∧
    X.dec.toDecoration.project T' = T}

/-- The family presented by any concrete crown presentation is immediately
side-to-side sofic; this is just the defining witness, not a soundness claim. -/
private lemma hereditary_sts_substitution_sofic_step4_control_family_sofic
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    {m : ℕ} {hC : C.Represents τ m}
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC) :
    IsSideToSideSofic
      (hereditary_sts_substitution_sofic_controlFamily τ hsts C X) := by
  exact ⟨X.dec, fun T => Iff.rfl⟩

/-- The exact pre-legal one-level reconstruction contract.  `fine` is the
proper input colouring; `coarse` already has decoded and matched extended
arrays, but founded legality is intentionally not assumed here. -/
private structure hereditary_sts_substitution_sofic_Reconstruction
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (T T' : PlaneTiling C.Q) where
  fine : PlaneTiling X.dec.P'
  fine_proper : X.dec.Proper fine
  fine_project : X.dec.toDecoration.project fine = T
  coarse : PlaneTiling X.dec.P'
  coarse_project : X.dec.toDecoration.project coarse = T'
  composition : C.σ.IsComposition T' T
  coarse_sideToSide : coarse.SideToSide
  coarse_typed : ∀ Y ∈ coarse.tiles, ∃ A,
    X.formEquiv Y.form = Sum.inl A ∧
      (hereditary_sts_substitution_sofic_decode τ hsts C hC A).isSome
  coarse_cells_match : ∀ Y ∈ coarse.tiles, ∀ Z ∈ coarse.tiles, Y ≠ Z →
    ∀ A B, X.formEquiv Y.form = Sum.inl A → X.formEquiv Z.form = Sum.inl B →
    ∀ (i : C.Side A.1) (j : C.Side B.1),
      hereditary_sts_substitution_sofic_CoincidentTypedSides
        τ hsts C hC X.dec Y Z A B i j → A.2 i = B.2 j
  coarse_parents : ∀ Y ∈ coarse.tiles, ∃ A,
    X.formEquiv Y.form = Sum.inl A ∧
    ∀ t, C.owner t = C.form A.1 →
      ∃ Z ∈ fine.tiles,
        X.formEquiv Z.form = Sum.inl
          (hereditary_sts_substitution_sofic_generate τ hsts C m hC A t) ∧
        Z.anchor = C.σ.θ • Y.anchor + C.anchor t

/-- Step 5 of the reviewed proof (one level only): a proper crown-controlled
tiling has a proper reconstructed parent, exact generated children, and a
grouped composition.  No iteration and no substitution conclusion occur in
this statement. -/
private lemma hereditary_sts_substitution_sofic_step5_one_level_reconstruction
    (τ : Substitution P) (hsts : τ.STS) (hher : τ.HereditarySides)
    (C : Geometry.MacroCertificate P) (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (T : PlaneTiling C.Q)
    (hT : T ∈ hereditary_sts_substitution_sofic_controlFamily τ hsts C X) :
    ∃ T' : PlaneTiling C.Q,
      Nonempty (hereditary_sts_substitution_sofic_Reconstruction
        τ hsts C m hC X T T') := by
  sorry

/-- Step 6 of the reviewed proof: legality of every reconstructed parent is
proved before reconstruction is iterated, by the cyclic, noncentral and
central-acyclic cases.  This isolates exactly that non-circular argument. -/
private lemma hereditary_sts_substitution_sofic_step6_reconstructed_parent_legal
    (τ : Substitution P) (hsts : τ.STS) (hher : τ.HereditarySides)
    (C : Geometry.MacroCertificate P) (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (T T' : PlaneTiling C.Q)
    (hrec : hereditary_sts_substitution_sofic_Reconstruction
      τ hsts C m hC X T T') :
    T' ∈ hereditary_sts_substitution_sofic_controlFamily τ hsts C X := by
  sorry

/-- A hierarchy whose adjacent coloured levels are related by the exact
pre-legal reconstruction contract.  Keeping these witnesses prevents the
levels from silently choosing unrelated proper colourings. -/
private structure hereditary_sts_substitution_sofic_CrownHierarchy
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (T : PlaneTiling C.Q) where
  seq : ℕ → PlaneTiling C.Q
  zero : seq 0 = T
  mem : ∀ n, seq n ∈ hereditary_sts_substitution_sofic_controlFamily τ hsts C X
  step : ∀ n, Nonempty (hereditary_sts_substitution_sofic_Reconstruction
    τ hsts C m hC X (seq n) (seq (n + 1)))

/-- Step 7 of the reviewed proof: iterating the now-legal one-level
reconstruction gives a grouped hierarchy. -/
private lemma hereditary_sts_substitution_sofic_step7_iterated_reconstruction
    (τ : Substitution P) (hsts : τ.STS) (hher : τ.HereditarySides)
    (C : Geometry.MacroCertificate P) (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (T : PlaneTiling C.Q)
    (hT : T ∈ hereditary_sts_substitution_sofic_controlFamily τ hsts C X) :
    Nonempty (hereditary_sts_substitution_sofic_CrownHierarchy
      τ hsts C m hC X T) := by
  let Good := {U : PlaneTiling C.Q //
    U ∈ hereditary_sts_substitution_sofic_controlFamily τ hsts C X}
  let parent : Good → PlaneTiling C.Q := fun U => Classical.choose
    (hereditary_sts_substitution_sofic_step5_one_level_reconstruction
      τ hsts hher C m hC X U.1 U.2)
  let reconstruction : (U : Good) →
      hereditary_sts_substitution_sofic_Reconstruction
        τ hsts C m hC X U.1 (parent U) := fun U => Classical.choice
    (Classical.choose_spec
      (hereditary_sts_substitution_sofic_step5_one_level_reconstruction
        τ hsts hher C m hC X U.1 U.2))
  let advance : Good → Good := fun U =>
    ⟨parent U,
      hereditary_sts_substitution_sofic_step6_reconstructed_parent_legal
        τ hsts hher C m hC X U.1 (parent U) (reconstruction U)⟩
  let levels : ℕ → Good := fun n => (advance^[n]) ⟨T, hT⟩
  refine ⟨{
    seq := fun n => (levels n).1
    zero := by rfl
    mem := fun n => (levels n).2
    step := fun n => ?_ }⟩
  have hrec := reconstruction (levels n)
  refine ⟨?_⟩
  simpa only [levels, Function.iterate_succ_apply'] using hrec

/-- Step 8 of the reviewed proof: recorded catalogue crowns equal the actual
full crowns at every reconstructed level (including vertices on interfaces).
This is the finite cyclic-fan and saturation argument, stated independently
of the final allowed-hierarchy theorem. -/
private lemma hereditary_sts_substitution_sofic_step8_all_level_crowns_allowed
    (τ : Substitution P) (hsts : τ.STS) (hher : τ.HereditarySides)
    (C : Geometry.MacroCertificate P) (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    {T : PlaneTiling C.Q}
    (H : hereditary_sts_substitution_sofic_CrownHierarchy
      τ hsts C m hC X T) :
    ∀ n (w : Pt), Substitution.IsVertexOf
        (hC.groupedFamily.scatter (H.seq n).tiles) w →
      τ.IsAllowedCrown
        (translateSet (-w)
          (Substitution.crown (hC.groupedFamily.scatter (H.seq n).tiles) w)) := by
  sorry

/-- One decomposition by the positive power substitution is the corresponding
finite iterate of the original decomposition. -/
private lemma hereditary_sts_substitution_sofic_step9a_power_decompose
    (τ : Substitution P) (m : ℕ) (hm : 0 < m)
    (S : Set (PlacedTile P)) :
    (τ.pow m hm).decompose S = τ.decomposeIter m S := by
  have hS : S = ⋃ A ∈ S, ({A} : Set (PlacedTile P)) := by ext; simp
  conv_rhs => rw [hS]
  rw [hierarchy_lift_iff_decomposeIter_iUnion₂]
  simp only [Substitution.decompose]
  apply Set.iUnion₂_congr
  intro A _
  have hA : ({A} : Set (PlacedTile P)) =
      translateSet A.anchor {⟨A.form, 0⟩} := by
    ext B
    simp [translateSet, PlacedTile.translate, PlacedTile.ext_iff]
  rw [hA, hierarchy_lift_iff_decomposeIter_translate]
  rfl

/-- Step 9a: certificate compatibility transports each exact grouped
composition in the witnessed coloured hierarchy to a `τ^m` composition after
scattering. -/
private lemma hereditary_sts_substitution_sofic_step9a_scatter_compositions
    (τ : Substitution P) (hsts : τ.STS)
    (C : Geometry.MacroCertificate P) (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    {T : PlaneTiling C.Q}
    (H : hereditary_sts_substitution_sofic_CrownHierarchy
      τ hsts C m hC X T) :
    ∀ n, (τ.pow m hC.m_pos).IsComposition
      (hierarchy_lift_iff_scatterTiling hC.groupedFamily (H.seq (n + 1)))
      (hierarchy_lift_iff_scatterTiling hC.groupedFamily (H.seq n)) := by
  intro n
  let R := Classical.choice (H.step n)
  change (τ.pow m hC.m_pos).decompose
      (hC.groupedFamily.scatter (H.seq (n + 1)).tiles) =
    hC.groupedFamily.scatter (H.seq n).tiles
  rw [hereditary_sts_substitution_sofic_step9a_power_decompose]
  have hs := hierarchy_lift_iff_scatter_decompose τ hC.groupedSubstitution
    (H.seq (n + 1)).tiles
  change hC.groupedFamily.scatter (C.σ.decompose (H.seq (n + 1)).tiles) =
    τ.decomposeIter m (hC.groupedFamily.scatter (H.seq (n + 1)).tiles) at hs
  rw [← hs]
  exact congrArg hC.groupedFamily.scatter R.composition

/-- Step 9 of the reviewed proof (soundness): scatter a reconstructed grouped
hierarchy, use compatibility to obtain a `τ^m` hierarchy, use Step 8 at every
level, and only then apply `allowed_crowns_hierarchy_is_substitutive`. -/
private lemma hereditary_sts_substitution_sofic_step9_soundness
    (τ : Substitution P) (hsts : τ.STS) (hher : τ.HereditarySides)
    (C : Geometry.MacroCertificate P) (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (T : PlaneTiling C.Q)
    (hT : T ∈ hereditary_sts_substitution_sofic_controlFamily τ hsts C X)
    (S : PlaneTiling P) (hscatter : hC.groupedFamily.scatter T.tiles = S.tiles) :
    τ.IsSubstitutionTiling S := by
  let H := Classical.choice
    (hereditary_sts_substitution_sofic_step7_iterated_reconstruction
      τ hsts hher C m hC X T hT)
  let seq : ℕ → PlaneTiling P := fun n =>
    hierarchy_lift_iff_scatterTiling hC.groupedFamily (H.seq n)
  have hseq : ∀ n, (τ.pow m hC.m_pos).IsComposition (seq (n + 1)) (seq n) :=
    hereditary_sts_substitution_sofic_step9a_scatter_compositions
      τ hsts C m hC X H
  have hcrown : ∀ n (w : Pt), Substitution.IsVertexOf (seq n).tiles w →
      τ.IsAllowedCrown
        (translateSet (-w) (Substitution.crown (seq n).tiles w)) := by
    intro n w hw
    exact hereditary_sts_substitution_sofic_step8_all_level_crowns_allowed
      τ hsts hher C m hC X H n w hw
  have hsub := allowed_crowns_hierarchy_is_substitutive
    τ (Substitution.STS.finite_crowns τ hsts) m hC.m_pos seq hseq hcrown
  have hzero : seq 0 = S := by
    apply dissection_preserves_sofic_PlaneTiling_ext
    change hC.groupedFamily.scatter (H.seq 0).tiles = S.tiles
    rw [H.zero]
    exact hscatter
  rwa [hzero] at hsub

/-- Genuine crown data on a grouped lift of a substitution hierarchy.  The
catalogue value is fixed before any control cell is assigned and is required
to equal the actual full crown in the scattered tiling. -/
private structure hereditary_sts_substitution_sofic_GenuineCrownHierarchy
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m) (T : PlaneTiling P) where
  seq : ℕ → PlaneTiling C.Q
  composition : ∀ n, C.σ.IsComposition (seq (n + 1)) (seq n)
  sts : ∀ n, (seq n).SideToSide
  bottom : hC.groupedFamily.scatter (seq 0).tiles = T.tiles
  gamma : ∀ n (A : PlacedTile C.Q), A ∈ (seq n).tiles →
    hereditary_sts_substitution_sofic_Catalog τ hsts C A.form
  gamma_actual : ∀ n (A : PlacedTile C.Q) (hA : A ∈ (seq n).tiles)
      (v : ↥(hereditary_sts_substitution_sofic_macroVertices C A.form)),
    ((gamma n A hA).1 v).1 =
      translateSet (-(A.anchor + v.1))
        (Substitution.crown (hC.groupedFamily.scatter (seq n).tiles)
          (A.anchor + v.1))

/-- Step 1 of the blueprint proof of `hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy`:
repeatedly compose the substitution tiling (`exists_composition`) to obtain an `m`-spaced hierarchy
of substitution tilings. -/
private lemma hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step1_power_hierarchy
    (τ : Substitution P) (m : ℕ) (T : PlaneTiling P) (hT : τ.IsSubstitutionTiling T) :
    ∃ seq : ℕ → PlaneTiling P, seq 0 = T ∧
      (∀ n, τ.decomposeIter m (seq (n + 1)).tiles = (seq n).tiles) ∧
      ∀ n, τ.IsSubstitutionTiling (seq n) := by
  classical
  let comp : {S : PlaneTiling P // τ.IsSubstitutionTiling S} →
      {S : PlaneTiling P // τ.IsSubstitutionTiling S} := fun S =>
    ⟨Classical.choose (SubstitutionTiling.exists_composition τ S.2),
      (Classical.choose_spec (SubstitutionTiling.exists_composition τ S.2)).2⟩
  have hcomp : ∀ S, τ.decompose (comp S).1.tiles = S.1.tiles := fun S =>
    (Classical.choose_spec (SubstitutionTiling.exists_composition τ S.2)).1
  let c : ℕ → {S : PlaneTiling P // τ.IsSubstitutionTiling S} := fun k => comp^[k] ⟨T, hT⟩
  have hc : ∀ k, τ.decompose (c (k + 1)).1.tiles = (c k).1.tiles := by
    intro k
    simp only [c, Function.iterate_succ_apply']
    exact hcomp _
  have hiter : ∀ j k, τ.decomposeIter j (c (k + j)).1.tiles = (c k).1.tiles := by
    intro j
    induction j with
    | zero => intro k; rfl
    | succ j ih =>
      intro k
      change τ.decompose (τ.decomposeIter j (c (k + (j + 1))).1.tiles) = _
      rw [show k + (j + 1) = (k + 1) + j by omega, ih, hc]
  refine ⟨fun n => (c (m * n)).1, rfl, ?_, fun n => (c (m * n)).2⟩
  intro n
  have := hiter m (m * n)
  rwa [show m * n + m = m * (n + 1) by ring] at this

/-- Step 2 of the blueprint proof of `hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy`:
every substitution tiling of an STS substitution is side-to-side. -/
private lemma hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step2_levels_sts (τ : Substitution P) (hsts : τ.STS) (S : PlaneTiling P)
    (hS : τ.IsSubstitutionTiling S) : S.SideToSide := by
  intro A hA B hB i j hover
  obtain ⟨n, p, u, hu⟩ := hS {A, B} (by simp [insert_subset_iff, hA, hB]) (by simp)
  have hA' : A.translate u ∈ τ.supertile n p := hu ⟨A, by simp, rfl⟩
  have hB' : B.translate u ∈ τ.supertile n p := hu ⟨B, by simp, rfl⟩
  have hside : ∀ (X : PlacedTile P) (k : Fin (P.disk X.form).n), (X.translate u).side k = u +ᵥ X.side k := by
    intro X k
    show (u +ᵥ X.anchor) +ᵥ _ = u +ᵥ (X.anchor +ᵥ _)
    rw [vadd_vadd]; rfl
  have hov : OverlapPos ((A.translate u).side i) ((B.translate u).side j) := by
    rw [hside, hside]
    obtain ⟨x, y, hxy, hseg⟩ := hover
    refine ⟨u +ᵥ x, u +ᵥ y, fun h => hxy (add_left_cancel h), ?_⟩
    rw [← vadd_segment]
    rintro z ⟨w, hw, rfl⟩
    exact ⟨⟨w, (hseg hw).1, rfl⟩, ⟨w, (hseg hw).2, rfl⟩⟩
  have h := hsts n p _ hA' _ hB' i j hov
  rw [hside, hside] at h
  ext x
  have hx := Set.ext_iff.mp h (u +ᵥ x)
  rwa [vadd_mem_vadd_set_iff, vadd_mem_vadd_set_iff] at hx

/-- Step 3 of the blueprint proof of `hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy`:
the full crown at a point of a plane tiling is finite (local finiteness). -/
private lemma hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step3_crown_finite
    (S : PlaneTiling P) (w : Pt) : (Substitution.crown S.tiles w).Finite := by
  apply (PlaneTiling.locallyFinite S (isCompact_singleton (x := w))).subset
  rintro A ⟨hA, hw⟩
  exact ⟨hA, w, hw, rfl⟩

/-- Step 3 of the blueprint proof of `hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy`:
the full crown at a point of a plane tiling covers a neighbourhood of that point. -/
private lemma hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step3_crown_nhds (S : PlaneTiling P) (w : Pt) :
    w ∈ interior (support (Substitution.crown S.tiles w)) := by
  have hB := PlaneTiling.locallyFinite S (isCompact_closedBall w 1)
  let E := {A ∈ S.tiles | (A.carrier ∩ Metric.closedBall w 1).Nonempty} \ Substitution.crown S.tiles w
  have hE : E.Finite := hB.subset diff_subset
  have hclosed : IsClosed (⋃ A ∈ E, A.carrier) :=
    hE.isClosed_biUnion fun A _ => (P.disk A.form).compact.isClosed.vadd A.anchor
  rw [mem_interior]
  refine ⟨Metric.ball w 1 \ ⋃ A ∈ E, A.carrier, ?_, Metric.isOpen_ball.sdiff hclosed, ?_⟩
  · rintro x ⟨hx, hxE⟩
    have hcov : x ∈ support S.tiles := by rw [S.cover]; trivial
    simp only [support, mem_iUnion] at hcov
    obtain ⟨A, hA, hxA⟩ := hcov
    by_cases hc : A ∈ Substitution.crown S.tiles w
    · simp only [support, mem_iUnion]; exact ⟨A, hc, hxA⟩
    · exfalso; apply hxE
      simp only [mem_iUnion]
      exact ⟨A, ⟨⟨hA, x, hxA, Metric.ball_subset_closedBall hx⟩, hc⟩, hxA⟩
  · refine ⟨Metric.mem_ball_self one_pos, ?_⟩
    simp only [mem_iUnion, not_exists]
    intro A hA hwA
    exact hA.2 ⟨hA.1.1, hwA⟩

/-- Step 4 of the blueprint proof of `hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy`:
translating a placed tile translates its carrier. -/
private lemma hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_tile_carrier_translate (X : PlacedTile P) (u : Pt) :
    (X.translate u).carrier = u +ᵥ X.carrier := by
  show (u +ᵥ X.anchor) +ᵥ _ = u +ᵥ (X.anchor +ᵥ _)
  rw [vadd_vadd]; rfl

/-- Step 4 of the blueprint proof of `hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy`:
a tile of an interior-disjoint set containing an interior point of the support of a finite subfamily
belongs to that subfamily. -/
private lemma hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_mem_of_interior
    {D F : Set (PlacedTile P)} (hD : DisjointInteriors D) (hFD : F ⊆ D)
    (hF : F.Finite) {w : Pt} (hw : w ∈ interior (support F)) {Y : PlacedTile P} (hY : Y ∈ D)
    (hwY : w ∈ Y.carrier) : Y ∈ F := by
  by_contra hYF
  have hreg : closure (interior Y.carrier) = Y.carrier := by
    show closure (interior (Y.anchor +ᵥ (P.disk Y.form).carrier)) = Y.anchor +ᵥ (P.disk Y.form).carrier
    rw [interior_vadd, closure_vadd, (P.disk Y.form).regular_closed]
  rw [← hreg] at hwY
  obtain ⟨z, hzV, hzY⟩ := mem_closure_iff.mp hwY _ isOpen_interior hw
  have hsupp : support F = closure (⋃ Z ∈ F, interior Z.carrier) := by
    rw [hF.closure_biUnion]
    apply iUnion₂_congr
    intro Z _
    show Z.anchor +ᵥ (P.disk Z.form).carrier = closure (interior (Z.anchor +ᵥ (P.disk Z.form).carrier))
    rw [interior_vadd, closure_vadd, (P.disk Z.form).regular_closed]
  have hz : z ∈ closure (⋃ Z ∈ F, interior Z.carrier) := hsupp ▸ interior_subset hzV
  obtain ⟨y, ⟨hyV, hyY⟩, hyU⟩ := mem_closure_iff.mp hz _ (isOpen_interior.inter isOpen_interior) ⟨hzV, hzY⟩
  simp only [mem_iUnion] at hyU
  obtain ⟨Z, hZ, hyZ⟩ := hyU
  have hne : Y ≠ Z := fun h => hYF (h ▸ hZ)
  exact Set.disjoint_left.mp (hD hY (hFD hZ) hne) hyY hyZ

/-- Step 4 of the blueprint proof of `hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy`:
supertiles have disjoint interiors. -/
private lemma hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_supertile_disjoint (τ : Substitution P) (n : ℕ) (p : P.Form) :
    DisjointInteriors (τ.supertile n p) := by
  cases n with
  | zero =>
    change DisjointInteriors ({⟨p, 0⟩} : Set (PlacedTile P))
    exact Set.pairwiseDisjoint_singleton _ _
  | succ n => exact ((τ.pow (n + 1) (Nat.succ_pos n)).rule p).disjoint

/-- Step 4 of the blueprint proof of `hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy`:
a listed vertex lies in the carrier. -/
private lemma hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_vertex_mem_carrier (X : PlacedTile P) (i : Fin (P.disk X.form).n) :
    X.vertex i ∈ X.carrier := by
  refine ⟨(P.disk X.form).vertex i, ?_, rfl⟩
  apply (P.disk X.form).compact.isClosed.frontier_subset
  rw [(P.disk X.form).frontier_eq]
  exact Set.mem_iUnion.mpr ⟨i, left_mem_segment ℝ _ _⟩

/-- Step 4 of the blueprint proof of `hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy`:
the support of a translated set is the translated support. -/
private lemma hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_support_translate (S : Set (PlacedTile P)) (v : Pt) :
    support (translateSet v S) = v +ᵥ support S := by
  simp only [support, translateSet, biUnion_image, Set.vadd_set_iUnion₂,
    hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_tile_carrier_translate]

/-- Step 4 of the blueprint proof of `hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy`:
composition of translations of tile sets. -/
private lemma hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_translateSet_translateSet (S : Set (PlacedTile P)) (v w : Pt) :
    translateSet w (translateSet v S) = translateSet (w + v) S := by
  simp only [translateSet, image_image]
  congr 1
  funext X
  exact PlacedTile.ext rfl (by simp [PlacedTile.translate, add_assoc])

/-- Step 4 of the blueprint proof of `hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy`:
a full crown of a tiling which occurs in a supertile is an allowed crown. -/
private lemma hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_allowed_crown (τ : Substitution P) (S : PlaneTiling P) (w : Pt)
    (hv : Substitution.IsVertexOf S.tiles w) {n : ℕ} {p : P.Form} {u : Pt}
    (hu : translateSet u (Substitution.crown S.tiles w) ⊆ τ.supertile n p) :
    τ.IsAllowedCrown (translateSet (-w) (Substitution.crown S.tiles w)) := by
  obtain ⟨X, hX, i, rfl⟩ := hv
  set w := X.vertex i with hw
  have hXc : X ∈ Substitution.crown S.tiles w := ⟨hX, hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_vertex_mem_carrier X i⟩
  have hcrown : Substitution.crown (τ.supertile n p) (u + w) =
      translateSet u (Substitution.crown S.tiles w) := by
    ext Y
    constructor
    · rintro ⟨hY, hwY⟩
      have hint : u + w ∈ interior (support (translateSet u (Substitution.crown S.tiles w))) := by
        rw [hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_support_translate, interior_vadd]
        exact vadd_mem_vadd_set (hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step3_crown_nhds S w)
      exact hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_mem_of_interior
        (hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_supertile_disjoint τ n p) hu
        ((hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step3_crown_finite S w).image _) hint hY hwY
    · rintro hY
      refine ⟨hu hY, ?_⟩
      obtain ⟨Z, hZ, rfl⟩ := hY
      rw [hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_tile_carrier_translate]
      exact vadd_mem_vadd_set hZ.2
  refine ⟨n, p, u + w, ⟨X.translate u, hu ⟨X, hXc, rfl⟩, i, ?_⟩, ?_⟩
  · show (u +ᵥ X.anchor) +ᵥ (P.disk X.form).vertex i = u + (X.anchor +ᵥ (P.disk X.form).vertex i)
    simp only [vadd_eq_add, add_assoc]
  · rw [hcrown, hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_translateSet_translateSet]
    congr 1
    abel

/-- Step 5 of the blueprint proof of `hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy`:
a translate of a subfamily of an interior-disjoint side-to-side family is again interior-disjoint
and side-to-side. -/
private lemma hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step5_translate_subset
    {D F : Set (PlacedTile P)} (hD : DisjointInteriors D) (hDs : SideToSideSet D) (hFD : F ⊆ D) (u : Pt) :
    DisjointInteriors (translateSet u F) ∧ SideToSideSet (translateSet u F) := by
  constructor
  · rintro _ ⟨X, hX, rfl⟩ _ ⟨Y, hY, rfl⟩ hne
    have hXY : X ≠ Y := fun h => hne (h ▸ rfl)
    have hd := hD (hFD hX) (hFD hY) hXY
    dsimp [Function.onFun] at hd ⊢
    rw [hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_tile_carrier_translate,
      hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_tile_carrier_translate,
      interior_vadd, interior_vadd]
    exact (Set.disjoint_vadd_set).mpr hd
  · rintro _ ⟨X, hX, rfl⟩ _ ⟨Y, hY, rfl⟩ i j hover
    rw [dissection_preserves_sts_sofic_step1_local_rule_side_translate,
      dissection_preserves_sts_sofic_step1_local_rule_side_translate] at hover ⊢
    have hover' := dissection_preserves_sts_sofic_step1_local_rule_overlap_vadd (-u) hover
    rw [neg_vadd_vadd, neg_vadd_vadd] at hover'
    rw [hDs X (hFD hX) Y (hFD hY) i j hover']

/-- Step 5 of the blueprint proof of `hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy`:
choosing the record of the actual crowns. For a grouped tile whose scattering lies in a substitution
tiling `S` of an STS substitution, the vector of actual full crowns of `S` at its marked vertices is
a jointly allowed catalogue entry. -/
private lemma hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step5_actual_catalog
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P) (m : ℕ)
    (hC : C.Represents τ m) (S : PlaneTiling P) (hS : τ.IsSubstitutionTiling S)
    (A : PlacedTile C.Q) (hA : hC.groupedFamily.scatterTile A ⊆ S.tiles) :
    ∃ γ : hereditary_sts_substitution_sofic_Catalog τ hsts C A.form,
      ∀ v : ↥(hereditary_sts_substitution_sofic_macroVertices C A.form),
        (γ.1 v).1 = translateSet (-(A.anchor + v.1)) (Substitution.crown S.tiles (A.anchor + v.1)) := by
  set a := A.anchor with ha
  set q := A.form with hq
  have hvert : ∀ v : ↥(hereditary_sts_substitution_sofic_macroVertices C q),
      Substitution.IsVertexOf S.tiles (a + v.1) := by
    intro v
    have hv := v.2
    simp only [hereditary_sts_substitution_sofic_macroVertices, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq] at hv
    obtain ⟨B, hB, i, hi⟩ := hv
    refine ⟨B.translate a, hA ⟨B, hB, rfl⟩, i, ?_⟩
    rw [← hi]
    show (a +ᵥ B.anchor) +ᵥ (P.disk B.form).vertex i = a + (B.anchor +ᵥ (P.disk B.form).vertex i)
    simp only [vadd_eq_add, add_assoc]
  let F : Set (PlacedTile P) := hC.groupedFamily.scatterTile A ∪
    ⋃ v : ↥(hereditary_sts_substitution_sofic_macroVertices C q), Substitution.crown S.tiles (a + v.1)
  have hFS : F ⊆ S.tiles := by
    refine union_subset hA (iUnion_subset fun v => fun X hX => hX.1)
  have hFfin : F.Finite := by
    refine Set.Finite.union ?_ (Set.finite_iUnion fun v =>
      hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step3_crown_finite S _)
    exact (C.Δ q).finite.image _
  obtain ⟨n, p, u, hu⟩ := hS F hFS hFfin
  have hcrownF : ∀ v : ↥(hereditary_sts_substitution_sofic_macroVertices C q),
      Substitution.crown S.tiles (a + v.1) ⊆ F := fun v =>
    subset_union_right.trans' (subset_iUnion (fun v : ↥(hereditary_sts_substitution_sofic_macroVertices C q) =>
      Substitution.crown S.tiles (a + v.1)) v)
  have hK : ∀ v : ↥(hereditary_sts_substitution_sofic_macroVertices C q),
      translateSet (-(a + v.1)) (Substitution.crown S.tiles (a + v.1)) ∈
        hereditary_sts_substitution_sofic_fullCrowns τ hsts := by
    intro v
    simp only [hereditary_sts_substitution_sofic_fullCrowns, Finset.mem_filter, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq]
    refine ⟨hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_allowed_crown τ S _
      (hvert v) ((image_mono (hcrownF v)).trans hu), ?_⟩
    rw [hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_support_translate,
      interior_vadd]
    have h := vadd_mem_vadd_set (a := -(a + v.1))
      (hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step3_crown_nhds S (a + v.1))
    simpa only [vadd_eq_add, neg_add_cancel] using h
  let γ : hereditary_sts_substitution_sofic_CrownVector τ hsts C q := fun v => ⟨_, hK v⟩
  have htr : ∀ v : ↥(hereditary_sts_substitution_sofic_macroVertices C q),
      translateSet v.1 (γ v).1 = translateSet (-a) (Substitution.crown S.tiles (a + v.1)) := by
    intro v
    show translateSet v.1 (translateSet (-(a + v.1)) _) = _
    rw [hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_translateSet_translateSet]
    congr 1
    abel
  have hcollar : hereditary_sts_substitution_sofic_collar τ hsts C q γ = translateSet (-a) F := by
    have hF' : translateSet (-a) F = translateSet (-a) (hC.groupedFamily.scatterTile A) ∪
        ⋃ v : ↥(hereditary_sts_substitution_sofic_macroVertices C q),
          translateSet (-a) (Substitution.crown S.tiles (a + v.1)) := by
      simp only [F, translateSet, image_union, image_iUnion]
    rw [hF', hereditary_sts_substitution_sofic_collar]
    congr 1
    swap
    · exact iUnion_congr htr
    show (C.Δ q).tiles = translateSet (-a) (translateSet a (C.Δ q).tiles)
    rw [hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_translateSet_translateSet,
      neg_add_cancel, cc_translateSet_zero]
  have hDS := hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step5_translate_subset
    S.disjoint (hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step2_levels_sts τ hsts S hS)
    hFS (-a)
  refine ⟨⟨γ, ?_, ?_, ?_, ?_⟩, fun v => rfl⟩
  · rw [hcollar]; exact hDS.1
  · rw [hcollar]; exact hDS.2
  · intro v
    rw [hcollar, htr]
    ext Y
    simp only [Substitution.crown, Set.mem_setOf_eq, cc_mem_translateSet, neg_neg]
    rw [hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_tile_carrier_translate]
    constructor
    · rintro ⟨hYF, hvY⟩
      exact ⟨hFS hYF, by simpa using vadd_mem_vadd_set (a := a) hvY⟩
    · rintro ⟨hYS, hvY⟩
      refine ⟨hcrownF v ⟨hYS, by
        rw [hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_tile_carrier_translate]
        exact hvY⟩, ?_⟩
      have h := vadd_mem_vadd_set (a := -a) hvY
      simpa using h
  · refine ⟨n, p, u + a, ?_⟩
    rw [hcollar, hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step4_translateSet_translateSet,
      add_neg_cancel_right]
    exact hu

/-- Step 10a of the reviewed proof: repeatedly compose the substitution
tiling, lift the `m`-spaced levels through grouping, and assign their genuine
jointly allowed full crown vectors. -/
private lemma hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy
    (τ : Substitution P) (hsts : τ.STS) (hher : τ.HereditarySides)
    (C : Geometry.MacroCertificate P) (m : ℕ) (hC : C.Represents τ m)
    (T : PlaneTiling P) (hT : τ.IsSubstitutionTiling T) :
    Nonempty (hereditary_sts_substitution_sofic_GenuineCrownHierarchy
      τ hsts C m hC T) := by
  have _ := hher
  obtain ⟨seqP, hseq0, hseq, hsub⟩ :=
    hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step1_power_hierarchy τ m T hT
  obtain ⟨seq', hcomp, hscat, hsts'⟩ := Grouping.hierarchy_lift_sts τ hC.groupedSubstitution hC.singleton
    seqP hseq (fun n => hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step2_levels_sts
      τ hsts (seqP n) (hsub n))
  have hcat : ∀ n (A : PlacedTile C.Q), A ∈ (seq' n).tiles →
      ∃ γ : hereditary_sts_substitution_sofic_Catalog τ hsts C A.form,
        ∀ v : ↥(hereditary_sts_substitution_sofic_macroVertices C A.form),
          (γ.1 v).1 = translateSet (-(A.anchor + v.1))
            (Substitution.crown (hC.groupedFamily.scatter (seq' n).tiles) (A.anchor + v.1)) := by
    intro n A hA
    have hscat' : hC.groupedFamily.scatter (seq' n).tiles = (seqP n).tiles := hscat n
    rw [hscat']
    refine hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy_step5_actual_catalog
      τ hsts C m hC (seqP n) (hsub n) A ?_
    rw [← hscat']
    exact fun X hX => Set.mem_iUnion₂.mpr ⟨A, hA, hX⟩
  exact ⟨{
    seq := seq'
    composition := hcomp
    sts := hsts'
    bottom := by
      have h0 : hC.groupedFamily.scatter (seq' 0).tiles = (seqP 0).tiles := hscat 0
      rw [h0, hseq0]
    gamma := fun n A hA => Classical.choose (hcat n A hA)
    gamma_actual := fun n A hA => Classical.choose_spec (hcat n A hA) }⟩

/-- Exact provenance of one extended tile through the chosen genuine grouped
hierarchy.  Besides generation and positions, it records at every ancestor
that the physical decoder returns the preassigned catalogue value `H.gamma`.
The final clause is origin-or-zero for this actual ancestor chain, rather than
for an unrelated legality witness. -/
private def hereditary_sts_substitution_sofic_FollowsHierarchyBy
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (T : PlaneTiling P)
    (H : hereditary_sts_substitution_sofic_GenuineCrownHierarchy
      τ hsts C m hC T)
    (coloured : ℕ → PlaneTiling X.dec.P') (n : ℕ)
    (Y : PlacedTile X.dec.P')
    (A : hereditary_sts_substitution_sofic_ExtTile τ hsts C hC)
    (placed : ℕ → PlacedTile X.dec.P')
    (ch : ℕ → hereditary_sts_substitution_sofic_ExtTile τ hsts C hC) : Prop :=
  placed 0 = Y ∧ ch 0 = A ∧
  (∀ r,
    placed r ∈ (coloured (n + r)).tiles ∧
    X.formEquiv (placed r).form = Sum.inl (ch r) ∧
    hereditary_sts_substitution_sofic_IsExtChild
      τ hsts C m hC (ch (r + 1)) (ch r) ∧
    (placed r).anchor = C.σ.θ • (placed (r + 1)).anchor + C.anchor (ch r).1 ∧
    ∃ (G : PlacedTile C.Q) (hG : G ∈ (H.seq (n + r)).tiles)
        (hform : G.form = C.form (ch r).1),
      G.anchor = (placed r).anchor ∧
      hereditary_sts_substitution_sofic_decode τ hsts C hC (ch r) =
        some (hform ▸ H.gamma (n + r) G hG)) ∧
  ∀ (r : ℕ) (i : C.Side (ch r).1) (k : Fin 5),
    (Planned.copySource C (C.form (ch (r + 1)).1)
      (C.occ (ch r).1 i) k).Nonempty →
    ¬ hereditary_sts_substitution_sofic_ExtHasOrigin τ hsts C hC ch r i k →
    (ch r).2 i k = Sum.inl 0

/-- The founded lift is tied to one `GenuineCrownHierarchy`.  It colours every
level, projects levelwise to `H.seq`, and gives every tile an actual ancestor
chain satisfying `FollowsHierarchyBy`.  Thus different sides cannot silently
choose unrelated legal chains or unrelated crown vectors. -/
private structure hereditary_sts_substitution_sofic_FoundedLift
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (T : PlaneTiling P)
    (H : hereditary_sts_substitution_sofic_GenuineCrownHierarchy
      τ hsts C m hC T) where
  coloured : ℕ → PlaneTiling X.dec.P'
  project : ∀ n, X.dec.toDecoration.project (coloured n) = H.seq n
  sideToSide : ∀ n, (coloured n).SideToSide
  follows : ∀ n (Y : PlacedTile X.dec.P'), Y ∈ (coloured n).tiles →
    ∃ A, X.formEquiv Y.form = Sum.inl A ∧
      hereditary_sts_substitution_sofic_ExtLegal τ hsts C m hC A ∧
      ∃ placed ch,
        hereditary_sts_substitution_sofic_FollowsHierarchyBy
          τ hsts C m hC X T H coloured n Y A placed ch

/-- Step 1 of the blueprint proof of
`hereditary_sts_substitution_sofic_step10b_founded_cell_lift`: every tile of a level of a
grouped composition is the positioned child, of some type owned by the parent form, of a
tile of the next level. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_step1_parent
    (C : Geometry.MacroCertificate P) {T' T : PlaneTiling C.Q}
    (h : C.σ.IsComposition T' T) {Z : PlacedTile C.Q} (hZ : Z ∈ T.tiles) :
    ∃ Y ∈ T'.tiles, ∃ t, C.owner t = Y.form ∧
      Z = ⟨C.form t, C.σ.θ • Y.anchor +ᵥ C.anchor t⟩ := by
  rw [← h] at hZ
  simp only [Substitution.decompose, Substitution.decomposeTile, translateSet, C.rule_eq,
    Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq] at hZ
  obtain ⟨Y, hY, _, ⟨t, ht, rfl⟩, rfl⟩ := hZ
  exact ⟨Y, hY, t, ht, rfl⟩

/-- The `r`-th ancestor of a tile of level `n` along a parent function. -/
private def hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc
    {Q : Protoset} {seq : ℕ → PlaneTiling Q}
    (par : ∀ n, (seq n).tiles → (seq (n + 1)).tiles) (n : ℕ) (Z : (seq n).tiles) :
    (r : ℕ) → (seq (n + r)).tiles
  | 0 => Z
  | r + 1 => par (n + r)
      (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z r)

/-- A lifted tile has the carrier of the grouped tile it lifts. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_lt_carrier
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (A : hereditary_sts_substitution_sofic_ExtTile τ hsts C hC) (F : PlacedTile C.Q)
    (hF : C.form A.1 = F.form) :
    (⟨X.formEquiv.symm (Sum.inl A), F.anchor⟩ : PlacedTile X.dec.P').carrier = F.carrier := by
  simp only [PlacedTile.carrier]
  rw [X.dec.carrier_eq, X.proj_typed, hF]

/-- The plane tiling obtained by lifting every tile `Z` of a grouped tiling `S` to the
decorated tile `f Z`. -/
private def hereditary_sts_substitution_sofic_step10b_founded_cell_lift_liftTiling
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (S : PlaneTiling C.Q) (f : S.tiles → hereditary_sts_substitution_sofic_ExtTile τ hsts C hC)
    (hf : ∀ Z, C.form (f Z).1 = Z.1.form) : PlaneTiling X.dec.P' where
  tiles := Set.range fun Z : S.tiles =>
    (⟨X.formEquiv.symm (Sum.inl (f Z)), Z.1.anchor⟩ : PlacedTile X.dec.P')
  cover := by
    rw [Set.eq_univ_iff_forall]
    intro z
    have hz : z ∈ support S.tiles := by rw [S.cover]; exact Set.mem_univ z
    simp only [support, Set.mem_iUnion] at hz ⊢
    obtain ⟨Z, hZ, hz⟩ := hz
    refine ⟨_, ⟨⟨Z, hZ⟩, rfl⟩, ?_⟩
    rw [hereditary_sts_substitution_sofic_step10b_founded_cell_lift_lt_carrier τ hsts C m hC X
      (f ⟨Z, hZ⟩) Z (hf ⟨Z, hZ⟩)]
    exact hz
  disjoint := by
    rintro _ ⟨Z, rfl⟩ _ ⟨Z', rfl⟩ hne
    simp only [Function.onFun]
    rw [hereditary_sts_substitution_sofic_step10b_founded_cell_lift_lt_carrier τ hsts C m hC X
        (f Z) Z.1 (hf Z),
      hereditary_sts_substitution_sofic_step10b_founded_cell_lift_lt_carrier τ hsts C m hC X
        (f Z') Z'.1 (hf Z')]
    apply S.disjoint Z.2 Z'.2
    intro he
    apply hne
    rw [Subtype.ext he]

/-- Two plane tilings with the same tiles are equal. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_ext
    {Q : Protoset} {T U : PlaneTiling Q} (h : T.tiles = U.tiles) : T = U := by
  cases T
  cases U
  congr

/-- The lifted tiling projects back to the grouped tiling it lifts. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_project
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (S : PlaneTiling C.Q) (f : S.tiles → hereditary_sts_substitution_sofic_ExtTile τ hsts C hC)
    (hf : ∀ Z, C.form (f Z).1 = Z.1.form) :
    X.dec.toDecoration.project
      (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_liftTiling
        τ hsts C m hC X S f hf) = S := by
  apply hereditary_sts_substitution_sofic_step10b_founded_cell_lift_ext
  ext W
  constructor
  · rintro ⟨_, ⟨Z, rfl⟩, rfl⟩
    convert Z.2 using 1
    exact PlacedTile.ext (by simp only [Decoration.projTile, X.proj_typed]; exact hf Z) rfl
  · intro hW
    refine ⟨_, ⟨⟨W, hW⟩, rfl⟩, ?_⟩
    exact PlacedTile.ext (by simp only [Decoration.projTile, X.proj_typed]; exact hf ⟨W, hW⟩) rfl

/-- Listed sides of equal polygonal disks correspond under the index cast. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_side_cast
    {D D' : PolygonalDisk} (e : D = D') (i : Fin D.n) :
    D.side i = D'.side (Fin.cast (congrArg PolygonalDisk.n e) i) := by
  subst e
  rfl

/-- A tiling of a side decoration is side-to-side as soon as its projection is. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_sideToSide
    {Q : Protoset} (dec : SideDecoration Q) (T : PlaneTiling dec.P')
    (h : (dec.toDecoration.project T).SideToSide) : T.SideToSide := by
  have key : ∀ (E : PlacedTile dec.P') (i : Fin (dec.P'.disk E.form).n),
      E.side i = (dec.toDecoration.projTile E).side
        (Fin.cast (congrArg PolygonalDisk.n (dec.disk_eq E.form)) i) := by
    intro E i
    simp only [PlacedTile.side, Decoration.projTile]
    rw [hereditary_sts_substitution_sofic_step10b_founded_cell_lift_side_cast
      (dec.disk_eq E.form) i]
  intro A hA B hB i j hov
  have := h _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    (Fin.cast (congrArg PolygonalDisk.n (dec.disk_eq A.form)) i)
    (Fin.cast (congrArg PolygonalDisk.n (dec.disk_eq B.form)) j)
    (by rw [← key, ← key]; exact hov)
  rw [key A i, key B j]
  exact this

/-- Step 5.1 of the blueprint proof of
`hereditary_sts_substitution_sofic_step10b_founded_cell_lift`: along a deterministic partial
copy chain `next`, one can assign a value to every state that is constant along copy steps,
equals the prescribed origin value at a state without successor, and is `zero` on states
whose chain never terminates. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_fv
    {α V : Type} (next : α → Option α) (zero : V) (origin : α → V) :
    ∃ value : α → V,
      (∀ s s', next s = some s' → value s = value s') ∧
      (∀ s, next s = none → value s = origin s) ∧
      (∀ s, (¬ ∃ a, Relation.ReflTransGen (fun x y => next x = some y) s a ∧ next a = none) →
        value s = zero) := by
  classical
  have hR : Relator.RightUnique (fun x y => next x = some y) := by
    intro x y z hy hz
    rw [hy] at hz
    exact Option.some.inj hz
  have huniq : ∀ {s a b : α}, Relation.ReflTransGen (fun x y => next x = some y) s a →
      next a = none → Relation.ReflTransGen (fun x y => next x = some y) s b →
      next b = none → a = b := by
    intro s a b ha hna hb hnb
    rcases Relation.ReflTransGen.total_of_right_unique hR ha hb with h | h
    · rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, _⟩
      · exact h
      · rw [hna] at hc
        cases hc
    · rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hc, _⟩
      · exact h.symm
      · rw [hnb] at hc
        cases hc
  refine ⟨fun s => if h : ∃ a, Relation.ReflTransGen (fun x y => next x = some y) s a ∧
      next a = none then origin h.choose else zero, ?_, ?_, ?_⟩
  · intro s s' hs
    have hiff : (∃ a, Relation.ReflTransGen (fun x y => next x = some y) s a ∧ next a = none) ↔
        (∃ a, Relation.ReflTransGen (fun x y => next x = some y) s' a ∧ next a = none) := by
      constructor
      · rintro ⟨a, ha, hna⟩
        rcases Relation.ReflTransGen.cases_head ha with rfl | ⟨c, hc, hca⟩
        · rw [hs] at hna
          cases hna
        · have : c = s' := by
            rw [hs] at hc
            exact (Option.some.inj hc).symm
          subst this
          exact ⟨a, hca, hna⟩
      · rintro ⟨a, ha, hna⟩
        exact ⟨a, Relation.ReflTransGen.head hs ha, hna⟩
    by_cases h : ∃ a, Relation.ReflTransGen (fun x y => next x = some y) s a ∧ next a = none
    · have h' := hiff.1 h
      simp only [dif_pos h, dif_pos h']
      congr 1
      exact huniq h.choose_spec.1 h.choose_spec.2
        (Relation.ReflTransGen.head hs h'.choose_spec.1) h'.choose_spec.2
    · have h' : ¬ ∃ a, Relation.ReflTransGen (fun x y => next x = some y) s' a ∧
          next a = none := fun h'' => h (hiff.2 h'')
      simp only [dif_neg h, dif_neg h']
  · intro s hs
    have h : ∃ a, Relation.ReflTransGen (fun x y => next x = some y) s a ∧ next a = none :=
      ⟨s, Relation.ReflTransGen.refl, hs⟩
    simp only [dif_pos h]
    congr 1
    exact huniq h.choose_spec.1 h.choose_spec.2 Relation.ReflTransGen.refl hs
  · intro s hs
    simp only [dif_neg hs]

/-- Transport of a catalogue value along two composable equalities of forms. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_cast_comp
    {α : Type} (F : α → Type) {a b c : α} (e : c = a) (hf : a = b) (hown : c = b) (u : F a) :
    (hown ▸ (hf ▸ u : F b) : F c) = (e ▸ u : F c) := by
  subst e
  subst hf
  rfl

/-- A nonprint side of a child of the form `α` has no copy source in a cell other than the
third. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_src_empty_nonprint
    (C : Geometry.MacroCertificate P) (t : C.Typ) (α : C.Q.Form) (hα : C.owner t = α)
    (i : C.Side t) (k : Fin 5) (hk : k ≠ 2) (hnp : ¬ C.IsPrint (C.occ t i)) :
    ¬ (Planned.copySource C α (C.occ t i) k).Nonempty := by
  subst hα
  rintro ⟨⟨d, k'⟩, hmem | hmem⟩
  · exact hnp ⟨d, hmem.1⟩
  · exact hk hmem.2.1

/-- A side occurrence that is a print of a marked parent side is inner. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_inner_of_print
    (C : Geometry.MacroCertificate P) {α : C.Q.Form} {d : Fin (C.Q.disk α).n}
    {o : C.SideOcc} (h : C.IsPrintOf α d o) : C.IsInner o := by
  have hpartner : ∀ {o : C.SideOcc}, C.IsInner o → C.IsInner (C.partner o) := by
    intro o ho
    have hp := C.g1_partner _ ho
    unfold MacroData.IsInner MacroData.IsOuter at ho ⊢
    rw [hp.2.2, hp.2.1]
    exact ho
  rcases h with ⟨hm, rfl | rfl⟩
  · exact C.g4_print_inner α d hm
  · exact hpartner (C.g4_print_inner α d hm)

/-- An outer side occurrence has no copy source in a cell other than the third. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_src_empty_outer
    (C : Geometry.MacroCertificate P) (α : C.Q.Form) (o : C.SideOcc) (k : Fin 5) (hk : k ≠ 2)
    (ho : C.IsOuter o) : ¬ (Planned.copySource C α o k).Nonempty := by
  rintro ⟨⟨d, k'⟩, hmem | hmem⟩
  · exact hereditary_sts_substitution_sofic_step10b_founded_cell_lift_inner_of_print C hmem.1 ho
  · exact hk hmem.2.1

/-- The states of the copy chains along a hierarchy: a level, a tile of it, a side of the type
of the tile and a cell position. -/
private abbrev hereditary_sts_substitution_sofic_step10b_founded_cell_lift_State
    {τ : Substitution P} {hsts : τ.STS} {C : Geometry.MacroCertificate P}
    {m : ℕ} {hC : C.Represents τ m} {T : PlaneTiling P}
    (H : hereditary_sts_substitution_sofic_GenuineCrownHierarchy τ hsts C m hC T)
    (typ : ∀ n, (H.seq n).tiles → C.Typ) : Type :=
  Σ n : ℕ, Σ x : (H.seq n).tiles, C.Side (typ n x) × Fin 5

/-- The deterministic copy step: a cell with a copy source follows the chosen source in the
parent. -/
private noncomputable def hereditary_sts_substitution_sofic_step10b_founded_cell_lift_next
    {τ : Substitution P} {hsts : τ.STS} {C : Geometry.MacroCertificate P}
    {m : ℕ} {hC : C.Represents τ m} {T : PlaneTiling P}
    (H : hereditary_sts_substitution_sofic_GenuineCrownHierarchy τ hsts C m hC T)
    (par : ∀ n, (H.seq n).tiles → (H.seq (n + 1)).tiles)
    (typ : ∀ n, (H.seq n).tiles → C.Typ) :
    hereditary_sts_substitution_sofic_step10b_founded_cell_lift_State H typ →
      Option (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_State H typ)
  | ⟨n, x, i, k⟩ =>
    if h : (Planned.copySource C (C.form (typ (n + 1) (par n x)))
        (C.occ (typ n x) i) k).Nonempty then
      some ⟨n + 1, par n x, h.some.1, h.some.2⟩
    else none

/-- The generated (origin) value of a cell without copy source, read off from the
preassigned crown vectors `gam`: this is the non-copy part of `generate`. -/
private noncomputable def hereditary_sts_substitution_sofic_step10b_founded_cell_lift_origin
    {τ : Substitution P} {hsts : τ.STS} {C : Geometry.MacroCertificate P}
    {m : ℕ} {hC : C.Represents τ m} {T : PlaneTiling P}
    (H : hereditary_sts_substitution_sofic_GenuineCrownHierarchy τ hsts C m hC T)
    (par : ∀ n, (H.seq n).tiles → (H.seq (n + 1)).tiles)
    (typ : ∀ n, (H.seq n).tiles → C.Typ)
    (gam : ∀ n (x : (H.seq n).tiles),
      hereditary_sts_substitution_sofic_Catalog τ hsts C (C.form (typ n x))) :
    hereditary_sts_substitution_sofic_step10b_founded_cell_lift_State H typ →
      hereditary_sts_substitution_sofic_ExtSymbol τ hsts C hC
  | ⟨n, x, i, k⟩ =>
    if C.IsPrint (C.occ (typ n x) i) then
      (if k = 4 then
        Sum.inl (Planned.Strict.identSU C hC (C.edge (C.occ (typ n x) i)))
      else Sum.inl 0)
    else if k = 0 then
      (if C.IsInner (C.occ (typ n x) i) then
        Sum.inl (Planned.Strict.identSU C hC (C.edge (C.occ (typ n x) i)))
      else Sum.inl 0)
    else if k = 1 then
      hereditary_sts_substitution_sofic_encodePacket τ hsts C hC
        (hereditary_sts_substitution_sofic_packetOf τ hsts C (typ n x) (gam n x) i)
    else if k = 3 then
      (if C.IsOuter (C.occ (typ n x) i) then
        Sum.inl (Planned.Strict.schedU C hC (C.occ (typ n x) i))
      else if C.IsBoundary (C.occ (typ n x) i) then
        Sum.inr (Sum.inr ⟨typ (n + 1) (par n x), fun _ => false,
          some (gam (n + 1) (par n x))⟩)
      else Sum.inl (Planned.Strict.botSU C hC))
    else Sum.inl 0

/-- A tile of the decomposition of a single tile lies in the scaled tile. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_decompose_carrier
    (σ : Substitution P) (u B : PlacedTile P) (hB : B ∈ σ.decompose {u}) :
    B.carrier ⊆ σ.θ • u.carrier := by
  simp only [Substitution.decompose, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop,
    exists_eq_left] at hB
  simp only [Substitution.decomposeTile, translateSet, Set.mem_image] at hB
  obtain ⟨B', hB', rfl⟩ := hB
  have hsub : B'.carrier ⊆ σ.θ • (P.disk u.form).carrier := by
    rw [← σ.support_eq]
    exact Set.subset_biUnion_of_mem (u := fun X => X.carrier) hB'
  intro z hz
  simp only [PlacedTile.carrier, PlacedTile.translate, Set.mem_vadd_set] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hw' : B'.anchor +ᵥ w ∈ σ.θ • (P.disk u.form).carrier :=
    hsub (Set.vadd_mem_vadd_set hw)
  obtain ⟨y, hy, hy'⟩ := Set.mem_smul_set.1 hw'
  refine Set.mem_smul_set.2 ⟨u.anchor +ᵥ y, Set.vadd_mem_vadd_set hy, ?_⟩
  simp only [vadd_eq_add, smul_add] at hy' ⊢
  rw [hy']
  abel

/-- Membership in an iterated decomposition splits over the tiles of the decomposed set. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_decomposeIter_mem
    (τ : Substitution P) (n : ℕ) (S : Set (PlacedTile P)) (B : PlacedTile P) :
    B ∈ τ.decomposeIter n S ↔ ∃ u ∈ S, B ∈ τ.decomposeIter n {u} := by
  have hS : S = ⋃ u ∈ S, ({u} : Set (PlacedTile P)) := by ext; simp
  conv_lhs => rw [hS]
  rw [hierarchy_lift_iff_decomposeIter_iUnion₂]
  simp

/-- Step 3 of the blueprint proof of
`hereditary_sts_substitution_sofic_step10b_founded_cell_lift` (interior vertices of a child
vector): for any catalogue value `γ` of the owner form, the child vector `F_t(γ)` records,
at every marked vertex of the child that is not on the boundary of the scaled owner, the star
computed in the `τ^m`-decomposition of the owner's dissection alone.  (The tiles of the
collar other than those of the dissection have interiors disjoint from the interior of the
owner, by `DisjointInteriors` of the collar, so their decompositions miss such a vertex.) -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_step3_child_interior
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P) (m : ℕ)
    (hC : C.Represents τ m) (t : C.Typ)
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.owner t))
    (v : ↥(hereditary_sts_substitution_sofic_macroVertices C (C.form t)))
    (hv : C.anchor t + v.1 ∉ frontier (C.σ.θ • (C.Q.disk (C.owner t)).carrier)) :
    ((hereditary_sts_substitution_sofic_childCatalog τ hsts C m hC t γ).1 v).1 =
      translateSet (-(C.anchor t + v.1))
        (Substitution.crown (τ.decomposeIter m (C.Δ (C.owner t)).tiles)
          (C.anchor t + v.1)) := by
  have hθne : τ.θ ^ m ≠ 0 := pow_ne_zero _ (by have := τ.one_lt; positivity)
  have hvc : ∀ (D : PolygonalDisk) (i : Fin D.n), D.vertex i ∈ D.carrier := by
    intro D i
    apply D.compact.isClosed.frontier_subset
    rw [D.frontier_eq]
    exact Set.mem_iUnion.2 ⟨i, left_mem_segment ℝ _ _⟩
  have hvmem : Substitution.IsVertexOf (C.Δ (C.form t)).tiles v.1 := by
    have hv0 := v.2
    unfold hereditary_sts_substitution_sofic_macroVertices at hv0
    rw [Set.Finite.mem_toFinset] at hv0
    exact hv0
  have hcar : v.1 ∈ (C.Q.disk (C.form t)).carrier := by
    obtain ⟨B, hB, hvB⟩ := hvmem
    obtain ⟨i, hi⟩ := hvB
    have hBc : B.carrier ⊆ (C.Q.disk (C.form t)).carrier := by
      rw [← C.scatter_support]
      exact Set.subset_biUnion_of_mem (u := fun B => B.carrier) hB
    apply hBc
    rw [← hi]
    exact Set.vadd_mem_vadd_set (hvc _ i)
  have hchild : C.anchor t +ᵥ (C.Q.disk (C.form t)).carrier ⊆
      C.σ.θ • (C.Q.disk (C.owner t)).carrier := by
    have hmem : (⟨C.form t, C.anchor t⟩ : PlacedTile C.Q) ∈ (C.σ.rule (C.owner t)).tiles := by
      rw [C.rule_eq]
      exact ⟨t, rfl, rfl⟩
    rw [← C.σ.support_eq]
    exact Set.subset_biUnion_of_mem (u := fun B => B.carrier) hmem
  have hxmem : C.anchor t + v.1 ∈ C.σ.θ • (C.Q.disk (C.owner t)).carrier :=
    hchild (Set.vadd_mem_vadd_set hcar)
  have hxint : C.anchor t + v.1 ∈ interior (C.σ.θ • (C.Q.disk (C.owner t)).carrier) := by
    by_contra hni
    exact hv ⟨subset_closure hxmem, hni⟩
  have hint : C.anchor t + v.1 ∈ τ.θ ^ m • interior (C.Q.disk (C.owner t)).carrier := by
    rw [← interior_smul₀ hθne, ← hC.θ_eq]
    exact hxint
  show translateSet (-(C.anchor t + v.1)) (Substitution.crown (τ.decomposeIter m
      (hereditary_sts_substitution_sofic_collar τ hsts C (C.owner t) γ.1)) (C.anchor t + v.1)) = _
  congr 1
  ext B
  simp only [Substitution.crown, Set.mem_setOf_eq]
  rw [hereditary_sts_substitution_sofic_step10b_founded_cell_lift_decomposeIter_mem,
    hereditary_sts_substitution_sofic_step10b_founded_cell_lift_decomposeIter_mem]
  constructor
  · rintro ⟨⟨u, hu, hBu⟩, hxB⟩
    refine ⟨⟨u, ?_, hBu⟩, hxB⟩
    by_contra hnu
    -- the carrier of `B` lies in the scaled carrier of `u`
    have hBu' : B ∈ (τ.pow m hC.m_pos).decompose {u} := by
      rw [hereditary_sts_substitution_sofic_step9a_power_decompose]
      exact hBu
    have hsubB := hereditary_sts_substitution_sofic_step10b_founded_cell_lift_decompose_carrier
      (τ.pow m hC.m_pos) u B hBu' hxB
    obtain ⟨p, hpu, hpx⟩ := Set.mem_smul_set.1 hsubB
    obtain ⟨p', hp', hp'x⟩ := Set.mem_smul_set.1 hint
    have hpp : p = p' := smul_right_injective _ hθne (hpx.trans hp'x.symm)
    subst hpp
    have hDisj := γ.2.1
    have hz : (interior (C.Q.disk (C.owner t)).carrier ∩ interior u.carrier).Nonempty := by
      have hcl : p ∈ closure (interior u.carrier) := by
        rw [cc_tile_regular u]
        exact hpu
      exact mem_closure_iff.1 hcl _ isOpen_interior hp'
    obtain ⟨z, hz1, hz2⟩ := hz
    have hsup : (C.Q.disk (C.owner t)).carrier = ⋃ w ∈ (C.Δ (C.owner t)).tiles, w.carrier :=
      (C.scatter_support _).symm
    have hzcl : z ∈ closure (⋃ w ∈ (C.Δ (C.owner t)).tiles, interior w.carrier) := by
      rw [(C.Δ (C.owner t)).finite.closure_biUnion]
      have hzc : z ∈ (C.Q.disk (C.owner t)).carrier := interior_subset hz1
      rw [hsup] at hzc
      simp only [Set.mem_iUnion] at hzc ⊢
      obtain ⟨w, hw, hzw⟩ := hzc
      exact ⟨w, hw, by rw [cc_tile_regular w]; exact hzw⟩
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hzcl
      (interior (C.Q.disk (C.owner t)).carrier ∩ interior u.carrier)
      (isOpen_interior.inter isOpen_interior) ⟨hz1, hz2⟩
    simp only [Set.mem_iUnion] at hy2
    obtain ⟨w, hw, hyw⟩ := hy2
    have hne : u ≠ w := fun h => hnu (h ▸ hw)
    exact Set.disjoint_left.1 (hDisj hu (Or.inl hw) hne) hy1.2 hyw
  · rintro ⟨⟨u, hu, hBu⟩, hxB⟩
    exact ⟨⟨u, Or.inl hu, hBu⟩, hxB⟩

/-- A segment determines its endpoints up to order. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_seg_endpoints
    {a b c d : Pt} (h : segment ℝ a b = segment ℝ c d) :
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

/-- The listed side of a side occurrence is the segment between its endpoints. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_occSide_eq
    (C : Geometry.MacroCertificate P) (o : C.SideOcc) :
    C.occSide o = segment ℝ (C.occStart o) (C.occEnd o) := by
  have hv : ∀ (w a b : Pt), w +ᵥ segment ℝ a b = segment ℝ (w + a) (w + b) := by
    intro w a b
    rw [← segment_translate_image]
    rfl
  simp only [MacroData.occSide, MacroData.childTile, PlacedTile.side, PolygonalDisk.side, hv,
    MacroData.occStart, MacroData.occEnd]

/-- Neither endpoint of a print lies on the boundary of its owner template: the central
child has no boundary side, and the partner of its print has the same segment. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_print_endpoints
    (C : Geometry.MacroCertificate P) {α : C.Q.Form} {d : Fin (C.Q.disk α).n}
    {o : C.SideOcc} (h : C.IsPrintOf α d o) :
    C.occStart o ∉ C.macroBoundary α ∧ C.occEnd o ∉ C.macroBoundary α := by
  obtain ⟨hm, h⟩ := h
  have hin := C.g4_print_inner α d hm
  have hpo : C.occStart (C.printOcc α d) ∉ C.macroBoundary α ∧
      C.occEnd (C.printOcc α d) ∉ C.macroBoundary α := by
    have h0 := (C.g2_central α (C.print α d)).2
    have e : C.owner (C.central α) = α := C.g5_central_owner α
    unfold MacroData.IsBoundary at h0
    have hnb : ¬ (C.IsInner (C.printOcc α d) ∧ (C.occStart (C.printOcc α d) ∈ C.macroBoundary α ∨
        C.occEnd (C.printOcc α d) ∈ C.macroBoundary α)) := by
      simpa only [e] using h0
    exact ⟨fun hs => hnb ⟨hin, Or.inl hs⟩, fun he => hnb ⟨hin, Or.inr he⟩⟩
  rcases h with rfl | rfl
  · exact hpo
  · have hp := C.g1_partner _ hin
    have hseg : segment ℝ (C.occStart (C.partner (C.printOcc α d)))
        (C.occEnd (C.partner (C.printOcc α d))) =
        segment ℝ (C.occStart (C.printOcc α d)) (C.occEnd (C.printOcc α d)) := by
      rw [← hereditary_sts_substitution_sofic_step10b_founded_cell_lift_occSide_eq,
        ← hereditary_sts_substitution_sofic_step10b_founded_cell_lift_occSide_eq]
      exact hp.2.2
    rcases hereditary_sts_substitution_sofic_step10b_founded_cell_lift_seg_endpoints hseg with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact hpo
    · rw [h1, h2]
      exact ⟨hpo.2, hpo.1⟩

/-- The encoding of endpoint packets is injective. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_encode_inj
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    {m : ℕ} (hC : C.Represents τ m)
    (p q : hereditary_sts_substitution_sofic_CrownPacket τ hsts)
    (h : hereditary_sts_substitution_sofic_encodePacket τ hsts C hC p =
      hereditary_sts_substitution_sofic_encodePacket τ hsts C hC q) : p = q := by
  have e1 : ∀ p : hereditary_sts_substitution_sofic_CrownPacket τ hsts, p ≠ (none, none) →
      hereditary_sts_substitution_sofic_encodePacket τ hsts C hC p = Sum.inr (Sum.inl p) := by
    rintro ⟨_ | a, _ | b⟩ hp
    · exact absurd rfl hp
    all_goals rfl
  by_cases hp : p = (none, none)
  · by_cases hq : q = (none, none)
    · exact hp.trans hq.symm
    · subst hp
      rw [e1 q hq] at h
      exact absurd h (by simp [hereditary_sts_substitution_sofic_encodePacket])
  · by_cases hq : q = (none, none)
    · subst hq
      rw [e1 p hp] at h
      exact absurd h (by simp [hereditary_sts_substitution_sofic_encodePacket])
    · rw [e1 p hp, e1 q hq] at h
      exact Sum.inl.inj (Sum.inr.inj h)

/-- Step 4 of the blueprint proof of
`hereditary_sts_substitution_sofic_step10b_founded_cell_lift` (the physical decoder is
well defined): an extended tile decodes at most one catalogue value.  A marked vertex off the
scaled owner boundary is determined by the second clause of `Decodes`; a marked vertex on it
is a listed vertex of the form (`hC.vertex_retained`), hence an endpoint of a non-print side
(prints and their partners are inner sides of or next to the central child, which has no
boundary side, by `g2_central`, `g4_print_inner`, `g1_partner`), and the packet of that side
records the crown at the vertex. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_step4_decode_unique
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P) (m : ℕ)
    (hC : C.Represents τ m)
    (A : hereditary_sts_substitution_sofic_ExtTile τ hsts C hC)
    (γ₁ γ₂ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.form A.1))
    (h₁ : hereditary_sts_substitution_sofic_Decodes τ hsts C hC A γ₁)
    (h₂ : hereditary_sts_substitution_sofic_Decodes τ hsts C hC A γ₂) : γ₁ = γ₂ := by
  apply Subtype.ext
  funext v
  apply Subtype.ext
  by_cases hfr : C.anchor A.1 + v.1 ∈ frontier (C.σ.θ • (C.Q.disk (C.owner A.1)).carrier)
  swap
  · rw [h₁.2 v hfr, h₂.2 v hfr]
  have hvmem : Substitution.IsVertexOf (C.Δ (C.form A.1)).tiles v.1 := by
    have hv := v.2
    unfold hereditary_sts_substitution_sofic_macroVertices at hv
    rw [Set.Finite.mem_toFinset] at hv
    exact hv
  have hvc : ∀ (D : PolygonalDisk) (i : Fin D.n), D.vertex i ∈ D.carrier := by
    intro D i
    apply D.compact.isClosed.frontier_subset
    rw [D.frontier_eq]
    exact Set.mem_iUnion.2 ⟨i, left_mem_segment ℝ _ _⟩
  have hcar : v.1 ∈ (C.Q.disk (C.form A.1)).carrier := by
    obtain ⟨B, hB, hvB⟩ := hvmem
    obtain ⟨i, hi⟩ := hvB
    have hBc : B.carrier ⊆ (C.Q.disk (C.form A.1)).carrier := by
      rw [← C.scatter_support]
      exact Set.subset_biUnion_of_mem (u := fun B => B.carrier) hB
    apply hBc
    rw [← hi]
    exact Set.vadd_mem_vadd_set (hvc _ i)
  have hchild : C.anchor A.1 +ᵥ (C.Q.disk (C.form A.1)).carrier ⊆
      C.σ.θ • (C.Q.disk (C.owner A.1)).carrier := by
    have hmem : (⟨C.form A.1, C.anchor A.1⟩ : PlacedTile C.Q) ∈
        (C.σ.rule (C.owner A.1)).tiles := by
      rw [C.rule_eq]
      exact ⟨A.1, rfl, rfl⟩
    rw [← C.σ.support_eq]
    exact Set.subset_biUnion_of_mem (u := fun B => B.carrier) hmem
  have hfront : v.1 ∈ frontier (C.Q.disk (C.form A.1)).carrier := by
    refine ⟨subset_closure hcar, fun hint => ?_⟩
    have hin : C.anchor A.1 + v.1 ∈ interior (C.anchor A.1 +ᵥ (C.Q.disk (C.form A.1)).carrier) := by
      rw [interior_vadd]
      exact Set.vadd_mem_vadd_set hint
    exact hfr.2 (interior_mono hchild hin)
  obtain ⟨j, hj⟩ := hC.vertex_retained (C.form A.1) v.1 hvmem hfront
  have hnp : ¬ C.IsPrint (C.occ A.1 j) := by
    rintro ⟨d, hd⟩
    apply (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_print_endpoints C hd).1
    show C.anchor A.1 + (C.Q.disk (C.form A.1)).vertex j ∈
      frontier (C.σ.θ • (C.Q.disk (C.owner A.1)).carrier)
    rw [hj]
    exact hfr
  have hpk := hereditary_sts_substitution_sofic_step10b_founded_cell_lift_encode_inj τ hsts C hC
    _ _ ((h₁.1 j hnp).symm.trans (h₂.1 j hnp))
  simp only [hereditary_sts_substitution_sofic_packetOf] at hpk
  rw [hj] at hpk
  have hx : hereditary_sts_substitution_sofic_lookupCrown τ hsts C (C.form A.1) γ₁ v.1 =
      hereditary_sts_substitution_sofic_lookupCrown τ hsts C (C.form A.1) γ₂ v.1 := by
    by_cases hlt : hereditary_sts_substitution_sofic_pointLT v.1
        ((C.Q.disk (C.form A.1)).vertex (finRotate (C.Q.disk (C.form A.1)).n j))
    · rw [if_pos hlt, if_pos hlt] at hpk
      have h3 := congrArg Prod.fst hpk
      simpa only [if_pos hfr] using h3
    · rw [if_neg hlt, if_neg hlt] at hpk
      have h3 := congrArg Prod.snd hpk
      simpa only [if_pos hfr] using h3
  unfold hereditary_sts_substitution_sofic_lookupCrown at hx
  rw [dif_pos v.2, dif_pos v.2] at hx
  exact congrArg Subtype.val (Option.some.inj hx)

/-- A listed vertex of a grouped tile is a vertex of an original tile of its scattering: the
listed side starting there is a complete side of an original tile (`hC.side_whole`). -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_listed_vertex
    (τ : Substitution P) (C : Geometry.MacroCertificate P) (m : ℕ) (hC : C.Represents τ m)
    (Y : PlacedTile C.Q) (p : Pt) (hp : p ∈ Y.vertexSet) :
    Substitution.IsVertexOf (hC.groupedFamily.scatterTile Y) p := by
  obtain ⟨j, rfl⟩ := hp
  obtain ⟨A, hA, k, hk⟩ := hC.side_whole Y.form j
  have hv : ∀ (w a b : Pt), w +ᵥ segment ℝ a b = segment ℝ (w + a) (w + b) := by
    intro w a b
    rw [← segment_translate_image]
    rfl
  simp only [PlacedTile.side, PolygonalDisk.side, hv] at hk
  refine ⟨A.translate Y.anchor, ⟨A, hA, rfl⟩, ?_⟩
  rcases hereditary_sts_substitution_sofic_step10b_founded_cell_lift_seg_endpoints hk with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨k, ?_⟩
    simp only [PlacedTile.vertex, PlacedTile.translate, vadd_eq_add] at h1 ⊢
    rw [add_assoc, h1]
  · refine ⟨finRotate _ k, ?_⟩
    simp only [PlacedTile.vertex, PlacedTile.translate, vadd_eq_add] at h2 ⊢
    rw [add_assoc, h2]

/-- Step 2a of the blueprint proof of
`hereditary_sts_substitution_sofic_step10b_founded_cell_lift` (planar geometry of a
side-to-side grouped level): let `Y` be a tile of a side-to-side grouped tiling `S`, let `u`
be an original tile of the scattering of `S` and let `p` be a common point of the carriers of
`Y` and `u` which is not a listed vertex of `Y`.  Then `u` belongs to the scattering of `Y`
itself, or `u` contains a vertex of an original tile of the scattering of `Y`.  (If `u` is in
the scattering of `Y` there is nothing to prove.  Otherwise `u` lies in another tile `Y'` of
`S`, whose interior is disjoint from that of `Y`, so `p` lies on the frontier of both and, not
being a listed vertex of `Y`, is interior to a listed side `e` of `Y`.  Since the grouped
level is side-to-side and covers the plane, the tile across `e` is `Y'` and `e` is a complete
listed side of `Y'` too (a listed vertex of `Y'` inside a listed side of `Y` would violate
side-to-sideness); `u` is then the original tile of `Y'` carrying `e` (`hC.side_whole`,
disjointness of interiors inside a group, `hC.sts`), and the endpoints of `e` are vertices of
`u` and of the original tile of `Y` carrying `e`.  The half-disk lemmas `cc_halfdisk_tile`
and `cc_key` of this file are available for the local structure at `p`.) -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_step2a_touching_tile
    (τ : Substitution P) (C : Geometry.MacroCertificate P) (m : ℕ) (hC : C.Represents τ m)
    (S : PlaneTiling C.Q) (hS : S.SideToSide) (Y : PlacedTile C.Q) (hY : Y ∈ S.tiles)
    (u : PlacedTile P) (hu : u ∈ hC.groupedFamily.scatter S.tiles) (p : Pt)
    (hpY : p ∈ Y.carrier) (hpu : p ∈ u.carrier) (hpv : p ∉ Y.vertexSet) :
    u ∈ hC.groupedFamily.scatterTile Y ∨
      ∃ w, Substitution.IsVertexOf (hC.groupedFamily.scatterTile Y) w ∧ w ∈ u.carrier := by
  sorry

/-- The carrier of a translated tile. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_translate_carrier
    {Q : Protoset} (X : PlacedTile Q) (v : Pt) : (X.translate v).carrier = v +ᵥ X.carrier := by
  ext x
  simp only [PlacedTile.carrier, PlacedTile.translate, mem_vadd_set_iff_neg_vadd_mem,
    vadd_eq_add, neg_add_rev]
  rw [← add_assoc]

/-- Crowns commute with translations. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_crown_translate
    (V : Set (PlacedTile P)) (b x : Pt) :
    Substitution.crown (translateSet b V) (b + x) = translateSet b (Substitution.crown V x) := by
  ext X
  simp only [Substitution.crown, Set.mem_setOf_eq, cc_mem_translateSet,
    hereditary_sts_substitution_sofic_step10b_founded_cell_lift_translate_carrier,
    mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg]

/-- A vertex of a translated set of tiles is a translate of a vertex. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_vertex_translate
    {S : Set (PlacedTile P)} {a w : Pt} (h : Substitution.IsVertexOf (translateSet a S) w) :
    Substitution.IsVertexOf S (w - a) := by
  obtain ⟨A, ⟨B, hB, rfl⟩, i, hi⟩ := h
  refine ⟨B, hB, i, ?_⟩
  rw [← hi]
  simp only [PlacedTile.vertex, PlacedTile.translate, vadd_eq_add]
  abel

/-- A child tile lies in the scaled carrier of its parent. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_child_carrier
    (C : Geometry.MacroCertificate P) (t : C.Typ) (Y : PlacedTile C.Q)
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

/-- The coordinates of a transported catalogue vector. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_cast_vec
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P)
    {q q' : C.Q.Form} (e : q = q')
    (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C q')
    (w : ↥(hereditary_sts_substitution_sofic_macroVertices C q)) :
    ((e ▸ γ : hereditary_sts_substitution_sofic_Catalog τ hsts C q).1 w).1 =
      (γ.1 ⟨w.1, e ▸ w.2⟩).1 := by
  subst e
  rfl

/-- One level of the scattered hierarchy is the `τ^m`-decomposition of the next. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_scatter_level
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P) (m : ℕ)
    (hC : C.Represents τ m) (T : PlaneTiling P)
    (H : hereditary_sts_substitution_sofic_GenuineCrownHierarchy τ hsts C m hC T) (n : ℕ) :
    hC.groupedFamily.scatter (H.seq n).tiles =
      τ.decomposeIter m (hC.groupedFamily.scatter (H.seq (n + 1)).tiles) := by
  have hs := hierarchy_lift_iff_scatter_decompose τ hC.groupedSubstitution
    (H.seq (n + 1)).tiles
  change hC.groupedFamily.scatter (C.σ.decompose (H.seq (n + 1)).tiles) =
    τ.decomposeIter m (hC.groupedFamily.scatter (H.seq (n + 1)).tiles) at hs
  rw [← hs]
  exact congrArg hC.groupedFamily.scatter (H.composition n).symm

/-- A marked vertex of a grouped form lies in its carrier. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_vertex_mem
    (C : Geometry.MacroCertificate P) (q : C.Q.Form)
    (v : ↥(hereditary_sts_substitution_sofic_macroVertices C q)) :
    v.1 ∈ (C.Q.disk q).carrier := by
  have hvc : ∀ (D : PolygonalDisk) (i : Fin D.n), D.vertex i ∈ D.carrier := by
    intro D i
    apply D.compact.isClosed.frontier_subset
    rw [D.frontier_eq]
    exact Set.mem_iUnion.2 ⟨i, left_mem_segment ℝ _ _⟩
  have hvmem : Substitution.IsVertexOf (C.Δ q).tiles v.1 := by
    have hv0 := v.2
    unfold hereditary_sts_substitution_sofic_macroVertices at hv0
    rw [Set.Finite.mem_toFinset] at hv0
    exact hv0
  obtain ⟨B, hB, i, hi⟩ := hvmem
  have hBc : B.carrier ⊆ (C.Q.disk q).carrier := by
    rw [← C.scatter_support]
    exact Set.subset_biUnion_of_mem (u := fun B => B.carrier) hB
  apply hBc
  rw [← hi]
  exact Set.vadd_mem_vadd_set (hvc _ i)

/-- Step 2 of the blueprint proof of
`hereditary_sts_substitution_sofic_step10b_founded_cell_lift` (coherence of the preassigned
crown vectors along the hierarchy): if `Z` is the child of type `t` of the tile `Y` of the
next level, then the genuine crown vector of `Z` is the child vector `F_t(γ_Y)` of the genuine
crown vector of `Y`.  Both are full crown vectors of the scattered levels (`H.gamma_actual`);
the scattered level `n` is the `τ^m`-decomposition of the scattered level `n + 1`
(`hC.compat`), and the collar of `Y` contains every tile of the scattered level `n + 1`
meeting `Y` (Step 2a), so the star of the decomposed collar at a vertex of `Z` is the actual
star there. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_step2_gamma_child
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P) (m : ℕ)
    (hC : C.Represents τ m) (T : PlaneTiling P)
    (H : hereditary_sts_substitution_sofic_GenuineCrownHierarchy τ hsts C m hC T)
    (n : ℕ) (Z : PlacedTile C.Q) (hZ : Z ∈ (H.seq n).tiles)
    (Y : PlacedTile C.Q) (hY : Y ∈ (H.seq (n + 1)).tiles) (t : C.Typ)
    (ht : C.owner t = Y.form)
    (hZeq : Z = ⟨C.form t, C.σ.θ • Y.anchor +ᵥ C.anchor t⟩) (hform : Z.form = C.form t) :
    hform ▸ H.gamma n Z hZ =
      hereditary_sts_substitution_sofic_childCatalog τ hsts C m hC t
        (ht ▸ H.gamma (n + 1) Y hY) := by
  subst hZeq
  have hθ : C.σ.θ = τ.θ ^ m := hC.θ_eq
  have hθne : τ.θ ^ m ≠ 0 := pow_ne_zero _ (by have := τ.one_lt; positivity)
  have hcast : ∀ w : ↥(hereditary_sts_substitution_sofic_macroVertices C (C.owner t)),
      ((ht ▸ H.gamma (n + 1) Y hY :
        hereditary_sts_substitution_sofic_Catalog τ hsts C (C.owner t)).1 w).1 =
        translateSet (-(Y.anchor + w.1))
          (Substitution.crown (hC.groupedFamily.scatter (H.seq (n + 1)).tiles)
            (Y.anchor + w.1)) := by
    intro w
    rw [hereditary_sts_substitution_sofic_step10b_founded_cell_lift_cast_vec τ hsts C ht
      (H.gamma (n + 1) Y hY) w]
    exact H.gamma_actual (n + 1) Y hY ⟨w.1, ht ▸ w.2⟩
  have hK1 : translateSet Y.anchor (hereditary_sts_substitution_sofic_collar τ hsts C
        (C.owner t) (ht ▸ H.gamma (n + 1) Y hY :
          hereditary_sts_substitution_sofic_Catalog τ hsts C (C.owner t)).1) =
      hC.groupedFamily.scatterTile Y ∪
        ⋃ w : ↥(hereditary_sts_substitution_sofic_macroVertices C (C.owner t)),
          Substitution.crown (hC.groupedFamily.scatter (H.seq (n + 1)).tiles)
            (Y.anchor + w.1) := by
    unfold hereditary_sts_substitution_sofic_collar
    have tu : ∀ (A B : Set (PlacedTile P)),
        translateSet Y.anchor (A ∪ B) = translateSet Y.anchor A ∪ translateSet Y.anchor B :=
      fun A B => Set.image_union _ A B
    have ti : ∀ (f : ↥(hereditary_sts_substitution_sofic_macroVertices C (C.owner t)) →
        Set (PlacedTile P)), translateSet Y.anchor (⋃ i, f i) =
          ⋃ i, translateSet Y.anchor (f i) := fun f => Set.image_iUnion
    rw [tu, ti]
    congr 1
    · rw [show C.Δ (C.owner t) = C.Δ Y.form from congrArg C.Δ ht]
      rfl
    · apply Set.iUnion_congr
      intro w
      rw [hcast w, cc_translateSet_translateSet, cc_translateSet_translateSet]
      have h0 : Y.anchor + w.1 + -(Y.anchor + w.1) = 0 := by abel
      rw [h0, cc_translateSet_zero]
  obtain ⟨U, hUdef⟩ : ∃ U : Set (PlacedTile P), U = hC.groupedFamily.scatterTile Y ∪
      ⋃ w : ↥(hereditary_sts_substitution_sofic_macroVertices C (C.owner t)),
        Substitution.crown (hC.groupedFamily.scatter (H.seq (n + 1)).tiles)
          (Y.anchor + w.1) := ⟨_, rfl⟩
  rw [← hUdef] at hK1
  have hUsub : U ⊆ hC.groupedFamily.scatter (H.seq (n + 1)).tiles := by
    rw [hUdef]
    intro u hu
    rcases hu with hu | hu
    · exact Set.mem_iUnion₂.2 ⟨Y, hY, hu⟩
    · obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hu
      exact hw.1
  have hcov : ∀ P' ∈ (⟨C.form t, C.σ.θ • Y.anchor +ᵥ C.anchor t⟩ : PlacedTile C.Q).carrier,
      Substitution.crown (τ.decomposeIter m U) P' =
        Substitution.crown (hC.groupedFamily.scatter (H.seq n).tiles) P' := by
    intro P' hP'
    rw [hereditary_sts_substitution_sofic_step10b_founded_cell_lift_scatter_level
      τ hsts C m hC T H n]
    ext B
    simp only [Substitution.crown, Set.mem_setOf_eq]
    rw [hereditary_sts_substitution_sofic_step10b_founded_cell_lift_decomposeIter_mem,
      hereditary_sts_substitution_sofic_step10b_founded_cell_lift_decomposeIter_mem]
    constructor
    · rintro ⟨⟨u, hu, hBu⟩, hxB⟩
      exact ⟨⟨u, hUsub hu, hBu⟩, hxB⟩
    · rintro ⟨⟨u, hu, hBu⟩, hxB⟩
      refine ⟨⟨u, ?_, hBu⟩, hxB⟩
      have hBu' : B ∈ (τ.pow m hC.m_pos).decompose {u} := by
        rw [hereditary_sts_substitution_sofic_step9a_power_decompose]
        exact hBu
      have hsubB :=
        hereditary_sts_substitution_sofic_step10b_founded_cell_lift_decompose_carrier
          (τ.pow m hC.m_pos) u B hBu' hxB
      obtain ⟨p, hpu, hpx⟩ := Set.mem_smul_set.1 hsubB
      have hZY := hereditary_sts_substitution_sofic_step10b_founded_cell_lift_child_carrier
        C t Y ht hP'
      rw [hθ] at hZY
      obtain ⟨p', hp', hp'x⟩ := Set.mem_smul_set.1 hZY
      have hpp : p = p' := smul_right_injective _ hθne (hpx.trans hp'x.symm)
      subst hpp
      have hres : u ∈ hC.groupedFamily.scatterTile Y ∨ ∃ w,
          Substitution.IsVertexOf (hC.groupedFamily.scatterTile Y) w ∧ w ∈ u.carrier := by
        by_cases hpv : p ∈ Y.vertexSet
        · exact Or.inr ⟨p, hereditary_sts_substitution_sofic_step10b_founded_cell_lift_listed_vertex
            τ C m hC Y p hpv, hpu⟩
        · exact hereditary_sts_substitution_sofic_step10b_founded_cell_lift_step2a_touching_tile
            τ C m hC (H.seq (n + 1)) (H.sts (n + 1)) Y hY u hu p hp' hpu hpv
      rcases hres with h | ⟨w, hw, hwu⟩
      · rw [hUdef]
        exact Or.inl h
      · rw [hUdef]
        right
        have hmv : w - Y.anchor ∈
            hereditary_sts_substitution_sofic_macroVertices C (C.owner t) := by
          unfold hereditary_sts_substitution_sofic_macroVertices
          rw [Set.Finite.mem_toFinset]
          show Substitution.IsVertexOf (C.Δ (C.owner t)).tiles (w - Y.anchor)
          rw [ht]
          exact hereditary_sts_substitution_sofic_step10b_founded_cell_lift_vertex_translate hw
        refine Set.mem_iUnion.2 ⟨⟨w - Y.anchor, hmv⟩, hu, ?_⟩
        show Y.anchor + (w - Y.anchor) ∈ u.carrier
        rw [show Y.anchor + (w - Y.anchor) = w by abel]
        exact hwu
  apply Subtype.ext
  funext v
  apply Subtype.ext
  have hPcar : (⟨C.form t, C.σ.θ • Y.anchor +ᵥ C.anchor t⟩ : PlacedTile C.Q).anchor + v.1 ∈
      (⟨C.form t, C.σ.θ • Y.anchor +ᵥ C.anchor t⟩ : PlacedTile C.Q).carrier :=
    Set.vadd_mem_vadd_set
      (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_vertex_mem C (C.form t) v)
  have hPeq : (⟨C.form t, C.σ.θ • Y.anchor +ᵥ C.anchor t⟩ : PlacedTile C.Q).anchor + v.1 =
      τ.θ ^ m • Y.anchor + (C.anchor t + v.1) := by
    show (C.σ.θ • Y.anchor +ᵥ C.anchor t) + v.1 = _
    rw [hθ, vadd_eq_add]
    abel
  show ((H.gamma n _ hZ).1 v).1 = translateSet (-(C.anchor t + v.1))
    (Substitution.crown (τ.decomposeIter m (hereditary_sts_substitution_sofic_collar τ hsts C
      (C.owner t) (ht ▸ H.gamma (n + 1) Y hY :
        hereditary_sts_substitution_sofic_Catalog τ hsts C (C.owner t)).1)) (C.anchor t + v.1))
  rw [H.gamma_actual n _ hZ v]
  have hkey : Substitution.crown (hC.groupedFamily.scatter (H.seq n).tiles)
      ((⟨C.form t, C.σ.θ • Y.anchor +ᵥ C.anchor t⟩ : PlacedTile C.Q).anchor + v.1) =
      translateSet (τ.θ ^ m • Y.anchor)
        (Substitution.crown (τ.decomposeIter m (hereditary_sts_substitution_sofic_collar
          τ hsts C (C.owner t) (ht ▸ H.gamma (n + 1) Y hY :
            hereditary_sts_substitution_sofic_Catalog τ hsts C (C.owner t)).1))
          (C.anchor t + v.1)) := by
    rw [← hcov _ hPcar, ← hK1, hierarchy_lift_iff_decomposeIter_translate, hPeq,
      hereditary_sts_substitution_sofic_step10b_founded_cell_lift_crown_translate]
  rw [hkey, cc_translateSet_translateSet]
  congr 1
  rw [hPeq]
  abel

/-- Step 5 of the blueprint proof of
`hereditary_sts_substitution_sofic_step10b_founded_cell_lift` (the founded cell assignment):
given the parent and type functions of the genuine hierarchy and the three geometric facts of
Steps 2-4, there are extended tiles `cell n Z`, one for each tile `Z` of each level, of the
type `typ n Z`, each the generated child (`generate`) of the extended tile of its parent,
physically decoding to the preassigned genuine crown vector `H.gamma n Z`, and such that along
the ancestor chain of every tile every copied cell without a finite origin is zero.  (Every
cell is the value at the end of its copy chain, where the generated value is read off from
`H.gamma`; and `0` on an infinite chain.) -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift_step5_cells
    (τ : Substitution P) (hsts : τ.STS) (C : Geometry.MacroCertificate P) (m : ℕ)
    (hC : C.Represents τ m) (T : PlaneTiling P)
    (H : hereditary_sts_substitution_sofic_GenuineCrownHierarchy τ hsts C m hC T)
    (par : ∀ n, (H.seq n).tiles → (H.seq (n + 1)).tiles)
    (typ : ∀ n, (H.seq n).tiles → C.Typ)
    (hspec : ∀ n Z, C.owner (typ n Z) = (par n Z).1.form ∧
      Z.1 = ⟨C.form (typ n Z), C.σ.θ • (par n Z).1.anchor +ᵥ C.anchor (typ n Z)⟩)
    (hgamma : ∀ (n : ℕ) (Z : PlacedTile C.Q) (hZ : Z ∈ (H.seq n).tiles)
      (Y : PlacedTile C.Q) (hY : Y ∈ (H.seq (n + 1)).tiles) (t : C.Typ)
      (ht : C.owner t = Y.form)
      (_hZeq : Z = ⟨C.form t, C.σ.θ • Y.anchor +ᵥ C.anchor t⟩) (hform : Z.form = C.form t),
      hform ▸ H.gamma n Z hZ =
        hereditary_sts_substitution_sofic_childCatalog τ hsts C m hC t
          (ht ▸ H.gamma (n + 1) Y hY))
    (hinterior : ∀ (t : C.Typ)
      (γ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.owner t))
      (v : ↥(hereditary_sts_substitution_sofic_macroVertices C (C.form t))),
      C.anchor t + v.1 ∉ frontier (C.σ.θ • (C.Q.disk (C.owner t)).carrier) →
      ((hereditary_sts_substitution_sofic_childCatalog τ hsts C m hC t γ).1 v).1 =
        translateSet (-(C.anchor t + v.1))
          (Substitution.crown (τ.decomposeIter m (C.Δ (C.owner t)).tiles)
            (C.anchor t + v.1)))
    (hunique : ∀ (A : hereditary_sts_substitution_sofic_ExtTile τ hsts C hC)
      (γ₁ γ₂ : hereditary_sts_substitution_sofic_Catalog τ hsts C (C.form A.1)),
      hereditary_sts_substitution_sofic_Decodes τ hsts C hC A γ₁ →
      hereditary_sts_substitution_sofic_Decodes τ hsts C hC A γ₂ → γ₁ = γ₂) :
    ∃ cell : ∀ n, (H.seq n).tiles → hereditary_sts_substitution_sofic_ExtTile τ hsts C hC,
      (∀ n Z, (cell n Z).1 = typ n Z) ∧
      (∀ n Z, cell n Z = hereditary_sts_substitution_sofic_generate τ hsts C m hC
        (cell (n + 1) (par n Z)) (cell n Z).1) ∧
      (∀ n Z (hf : Z.1.form = C.form (cell n Z).1),
        hereditary_sts_substitution_sofic_decode τ hsts C hC (cell n Z) =
          some (hf ▸ H.gamma n Z.1 Z.2)) ∧
      ∀ (n : ℕ) (Z : (H.seq n).tiles) (r : ℕ)
        (i : C.Side (cell (n + r)
          (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z r)).1)
        (k : Fin 5),
        (Planned.copySource C (C.form (cell (n + (r + 1))
            (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z
              (r + 1))).1)
          (C.occ (cell (n + r)
            (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z r)).1 i)
          k).Nonempty →
        ¬ hereditary_sts_substitution_sofic_ExtHasOrigin τ hsts C hC
          (fun r => cell (n + r)
            (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z r))
          r i k →
        (cell (n + r)
          (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z r)).2 i k =
          Sum.inl 0 := by
  have hform0 : ∀ n (x : (H.seq n).tiles), x.1.form = C.form (typ n x) := fun n x =>
    congrArg PlacedTile.form (hspec n x).2
  have hown : ∀ n (x : (H.seq n).tiles),
      C.owner (typ n x) = C.form (typ (n + 1) (par n x)) := fun n x =>
    (hspec n x).1.trans (hform0 (n + 1) (par n x))
  obtain ⟨gam, hgam⟩ : ∃ gam : ∀ n (x : (H.seq n).tiles),
      hereditary_sts_substitution_sofic_Catalog τ hsts C (C.form (typ n x)),
      ∀ n x, gam n x = hform0 n x ▸ H.gamma n x.1 x.2 :=
    ⟨fun n x => hform0 n x ▸ H.gamma n x.1 x.2, fun _ _ => rfl⟩
  have hK : ∀ n (x : (H.seq n).tiles), gam n x =
      hereditary_sts_substitution_sofic_childCatalog τ hsts C m hC (typ n x)
        (hown n x ▸ gam (n + 1) (par n x)) := by
    intro n x
    have h := hgamma n x.1 x.2 (par n x).1 (par n x).2 (typ n x) (hspec n x).1
      (hspec n x).2 (hform0 n x)
    rw [hgam n x, h]
    congr 1
    rw [hgam (n + 1) (par n x)]
    exact (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_cast_comp
      (hereditary_sts_substitution_sofic_Catalog τ hsts C) (hspec n x).1
      (hform0 (n + 1) (par n x)) (hown n x) _).symm
  obtain ⟨value, hstep, hstop, hzero⟩ :=
    hereditary_sts_substitution_sofic_step10b_founded_cell_lift_fv
      (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_next H par typ)
      (Sum.inl 0 : hereditary_sts_substitution_sofic_ExtSymbol τ hsts C hC)
      (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_origin H par typ gam)
  have hnext_some : ∀ n (x : (H.seq n).tiles) (i : C.Side (typ n x)) (k : Fin 5)
      (hs : (Planned.copySource C (C.form (typ (n + 1) (par n x)))
        (C.occ (typ n x) i) k).Nonempty),
      hereditary_sts_substitution_sofic_step10b_founded_cell_lift_next H par typ ⟨n, x, i, k⟩ =
        some ⟨n + 1, par n x, hs.some.1, hs.some.2⟩ := by
    intro n x i k hs
    simp only [hereditary_sts_substitution_sofic_step10b_founded_cell_lift_next, dif_pos hs]
  have hnext_none : ∀ n (x : (H.seq n).tiles) (i : C.Side (typ n x)) (k : Fin 5),
      ¬ (Planned.copySource C (C.form (typ (n + 1) (par n x)))
        (C.occ (typ n x) i) k).Nonempty →
      hereditary_sts_substitution_sofic_step10b_founded_cell_lift_next H par typ
        ⟨n, x, i, k⟩ = none := by
    intro n x i k hs
    simp only [hereditary_sts_substitution_sofic_step10b_founded_cell_lift_next, dif_neg hs]
  have hdecode : ∀ n (x : (H.seq n).tiles),
      hereditary_sts_substitution_sofic_decode τ hsts C hC
        (⟨typ n x, fun i k => value ⟨n, x, i, k⟩⟩ :
          hereditary_sts_substitution_sofic_ExtTile τ hsts C hC) = some (gam n x) := by
    intro n x
    have hD : hereditary_sts_substitution_sofic_Decodes τ hsts C hC
        (⟨typ n x, fun i k => value ⟨n, x, i, k⟩⟩ :
          hereditary_sts_substitution_sofic_ExtTile τ hsts C hC) (gam n x) := by
      refine ⟨?_, ?_⟩
      · intro i hnp
        show value ⟨n, x, i, 1⟩ = hereditary_sts_substitution_sofic_encodePacket τ hsts C hC
          (hereditary_sts_substitution_sofic_packetOf τ hsts C (typ n x) (gam n x) i)
        rw [hstop _ (hnext_none n x i 1
          (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_src_empty_nonprint
            C (typ n x) _ (hown n x) i 1 (by decide) hnp))]
        simp only [hereditary_sts_substitution_sofic_step10b_founded_cell_lift_origin]
        rw [if_neg hnp, if_neg (by decide : ¬ ((1 : Fin 5) = 0))]
        exact if_true _ _
      · intro v hv
        show ((gam n x).1 v).1 = _
        rw [hK n x]
        exact hinterior (typ n x) _ v hv
    have hex : ∃! γ, hereditary_sts_substitution_sofic_Decodes τ hsts C hC
        (⟨typ n x, fun i k => value ⟨n, x, i, k⟩⟩ :
          hereditary_sts_substitution_sofic_ExtTile τ hsts C hC) γ :=
      ⟨gam n x, hD, fun γ hγ => hunique _ γ (gam n x) hγ hD⟩
    unfold hereditary_sts_substitution_sofic_decode
    rw [dif_pos hex]
    congr 1
    exact hunique _ _ _ hex.exists.choose_spec hD
  have hout3 : ∀ n (x : (H.seq n).tiles) (d : C.Side (typ n x)),
      C.IsOuter (C.occ (typ n x) d) →
      value ⟨n, x, d, 3⟩ = Sum.inl (Planned.Strict.schedU C hC (C.occ (typ n x) d)) := by
    intro n x d ho
    have hnp : ¬ C.IsPrint (C.occ (typ n x) d) := fun ⟨_, hd⟩ =>
      hereditary_sts_substitution_sofic_step10b_founded_cell_lift_inner_of_print C hd ho
    rw [hstop _ (hnext_none n x d 3
      (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_src_empty_outer
        C _ _ 3 (by decide) ho))]
    simp only [hereditary_sts_substitution_sofic_step10b_founded_cell_lift_origin]
    rw [if_neg hnp, if_neg (by decide : ¬ ((3 : Fin 5) = 0)),
      if_neg (by decide : ¬ ((3 : Fin 5) = 1))]
    rw [if_pos ho]
    exact if_true _ _
  have key : ∀ (n : ℕ) (Z : (H.seq n).tiles)
      (s a : hereditary_sts_substitution_sofic_step10b_founded_cell_lift_State H typ),
      Relation.ReflTransGen (fun x y =>
        hereditary_sts_substitution_sofic_step10b_founded_cell_lift_next H par typ x = some y)
        s a →
      hereditary_sts_substitution_sofic_step10b_founded_cell_lift_next H par typ a = none →
      ∀ (r : ℕ) (i : C.Side (typ (n + r)
          (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z r)))
        (k : Fin 5),
        s = ⟨n + r, hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z r,
          i, k⟩ →
        hereditary_sts_substitution_sofic_ExtHasOrigin τ hsts C hC
          (fun r => (⟨typ (n + r)
              (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z r),
            fun i k => value ⟨n + r,
              hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z r, i, k⟩⟩ :
            hereditary_sts_substitution_sofic_ExtTile τ hsts C hC)) r i k := by
    intro n Z s a hsa
    induction hsa using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro hna r i k hs
      subst hs
      have hne : ¬ (Planned.copySource C (C.form (typ (n + r + 1)
          (par (n + r) (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc
            par n Z r)))) (C.occ (typ (n + r)
          (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z r)) i)
          k).Nonempty := by
        intro hne
        rw [hnext_some _ _ i k hne] at hna
        cases hna
      exact ⟨⟨r, i, k⟩, Relation.ReflTransGen.refl, Set.not_nonempty_iff_eq_empty.mp hne⟩
    | @head s s' hss' hrest ih =>
      intro hna r i k hs
      subst hs
      have hs' : (Planned.copySource C (C.form (typ (n + r + 1)
          (par (n + r) (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc
            par n Z r)))) (C.occ (typ (n + r)
          (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z r)) i)
          k).Nonempty := by
        by_contra hne
        have hss'' : hereditary_sts_substitution_sofic_step10b_founded_cell_lift_next H par typ
            ⟨n + r, hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z r,
              i, k⟩ = some s' := hss'
        rw [hnext_none _ _ i k hne] at hss''
        cases hss''
      have hs'eq : s' = ⟨n + r + 1, par (n + r)
          (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z r),
          hs'.some.1, hs'.some.2⟩ := by
        have hss'' : hereditary_sts_substitution_sofic_step10b_founded_cell_lift_next H par typ
            ⟨n + r, hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z r,
              i, k⟩ = some s' := hss'
        rw [hnext_some _ _ i k hs'] at hss''
        exact (Option.some.inj hss'').symm
      obtain ⟨s0, hs0, hemp⟩ := ih hna (r + 1) hs'.some.1 hs'.some.2 hs'eq
      exact ⟨s0, Relation.ReflTransGen.head ⟨hs'.some.1, hs'.some.2, hs'.some_mem, rfl⟩ hs0,
        hemp⟩
  refine ⟨fun n x => ⟨typ n x, fun i k => value ⟨n, x, i, k⟩⟩, fun n x => rfl, ?_, ?_, ?_⟩
  · intro n x
    show (⟨typ n x, fun i k => value ⟨n, x, i, k⟩⟩ :
        hereditary_sts_substitution_sofic_ExtTile τ hsts C hC) =
      hereditary_sts_substitution_sofic_generate τ hsts C m hC
        ⟨typ (n + 1) (par n x), fun i k => value ⟨n + 1, par n x, i, k⟩⟩ (typ n x)
    refine Sigma.ext rfl (heq_of_eq ?_)
    funext i k
    show value ⟨n, x, i, k⟩ = (hereditary_sts_substitution_sofic_generate τ hsts C m hC
      ⟨typ (n + 1) (par n x), fun i k => value ⟨n + 1, par n x, i, k⟩⟩ (typ n x)).2 i k
    unfold hereditary_sts_substitution_sofic_generate
    dsimp only
    by_cases hs : (Planned.copySource C (C.form (typ (n + 1) (par n x)))
        (C.occ (typ n x) i) k).Nonempty
    · rw [dif_pos hs, hstep _ _ (hnext_some n x i k hs)]
    · rw [dif_neg hs, hstop _ (hnext_none n x i k hs)]
      simp only [hereditary_sts_substitution_sofic_step10b_founded_cell_lift_origin]
      by_cases hp : C.IsPrint (C.occ (typ n x) i)
      · rw [dif_pos hp, if_pos hp]
      · rw [dif_neg hp, if_neg hp]
        by_cases hk0 : k = 0
        · rw [if_pos hk0, if_pos hk0]
        · rw [if_neg hk0, if_neg hk0]
          by_cases hk1 : k = 1
          · rw [if_pos hk1, if_pos hk1, hdecode (n + 1) (par n x)]
            dsimp only
            rw [dif_pos (hown n x), ← hK n x]
          · rw [if_neg hk1, if_neg hk1]
            by_cases hk3 : k = 3
            · rw [if_pos hk3, if_pos hk3]
              by_cases hout : C.IsOuter (C.occ (typ n x) i)
              · rw [if_pos hout, if_pos hout]
              · rw [if_neg hout, if_neg hout]
                by_cases hb : C.IsBoundary (C.occ (typ n x) i)
                · rw [if_pos hb, if_pos hb]
                  unfold hereditary_sts_substitution_sofic_header
                  rw [hdecode (n + 1) (par n x)]
                  dsimp only
                  have hbits : (fun _ => false) = (fun d => C.outerB (typ (n + 1) (par n x)) d &&
                      decide (value ⟨n + 1, par n x, d, 3⟩ = Sum.inl 0)) := by
                    funext d
                    by_cases ho : C.IsOuter (C.occ (typ (n + 1) (par n x)) d)
                    · rw [hout3 (n + 1) (par n x) d ho]
                      have hne : (Planned.Strict.schedU C hC
                          (C.occ (typ (n + 1) (par n x)) d) : Planned.Strict.SU C hC) ≠ 0 := by
                        intro h
                        cases h
                      have hne' : ¬ ((Sum.inl (Planned.Strict.schedU C hC
                          (C.occ (typ (n + 1) (par n x)) d)) :
                          hereditary_sts_substitution_sofic_ExtSymbol τ hsts C hC) =
                            Sum.inl 0) := fun h => hne (Sum.inl.inj h)
                      simp [hne']
                    · simp [MacroData.outerB, ho]
                  rw [← hbits]
                · rw [if_neg hb, if_neg hb]
            · rw [if_neg hk3, if_neg hk3]
  · intro n Z hf
    show hereditary_sts_substitution_sofic_decode τ hsts C hC
      (⟨typ n Z, fun i k => value ⟨n, Z, i, k⟩⟩ :
        hereditary_sts_substitution_sofic_ExtTile τ hsts C hC) = _
    rw [hdecode n Z, hgam n Z]
  · intro n Z r i k _ hno
    show value ⟨n + r,
      hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z r, i, k⟩ =
        Sum.inl 0
    apply hzero
    rintro ⟨a, ha, hna⟩
    apply hno
    exact key n Z _ a ha hna r i k rfl

/-- Step 10b of the reviewed proof: assign every cell by finite origin or
zero along the genuine hierarchy and prove the decoder returns the previously
chosen physical crown vector. -/
private lemma hereditary_sts_substitution_sofic_step10b_founded_cell_lift
    (τ : Substitution P) (hsts : τ.STS) (hher : τ.HereditarySides)
    (C : Geometry.MacroCertificate P) (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (T : PlaneTiling P)
    (H : hereditary_sts_substitution_sofic_GenuineCrownHierarchy
      τ hsts C m hC T) :
    Nonempty (hereditary_sts_substitution_sofic_FoundedLift
      τ hsts C m hC X T H) := by
  have _ := hher
  have hpar : ∀ n (Z : (H.seq n).tiles), ∃ Y : (H.seq (n + 1)).tiles, ∃ t,
      C.owner t = Y.1.form ∧ Z.1 = ⟨C.form t, C.σ.θ • Y.1.anchor +ᵥ C.anchor t⟩ := by
    intro n Z
    obtain ⟨Y, hY, t, ht, he⟩ :=
      hereditary_sts_substitution_sofic_step10b_founded_cell_lift_step1_parent C
        (H.composition n) Z.2
    exact ⟨⟨Y, hY⟩, t, ht, he⟩
  choose par typ hspec using hpar
  obtain ⟨cell, ha, hb, hc, hd⟩ :=
    hereditary_sts_substitution_sofic_step10b_founded_cell_lift_step5_cells τ hsts C m hC T H
      par typ hspec
      (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_step2_gamma_child
        τ hsts C m hC T H)
      (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_step3_child_interior
        τ hsts C m hC)
      (hereditary_sts_substitution_sofic_step10b_founded_cell_lift_step4_decode_unique
        τ hsts C m hC)
  have hform : ∀ n (Z : (H.seq n).tiles), C.form (cell n Z).1 = Z.1.form := by
    intro n Z
    rw [ha]
    exact (congrArg PlacedTile.form (hspec n Z).2).symm
  let col : ℕ → PlaneTiling X.dec.P' := fun n =>
    hereditary_sts_substitution_sofic_step10b_founded_cell_lift_liftTiling τ hsts C m hC X
      (H.seq n) (cell n) (hform n)
  have hproj : ∀ n, X.dec.toDecoration.project (col n) = H.seq n := fun n =>
    hereditary_sts_substitution_sofic_step10b_founded_cell_lift_project τ hsts C m hC X
      (H.seq n) (cell n) (hform n)
  refine ⟨{
    coloured := col
    project := hproj
    sideToSide := fun n =>
      hereditary_sts_substitution_sofic_step10b_founded_cell_lift_sideToSide X.dec (col n)
        (by rw [hproj n]; exact H.sts n)
    follows := ?_ }⟩
  intro n Y hY
  obtain ⟨Z, rfl⟩ := hY
  let anc := hereditary_sts_substitution_sofic_step10b_founded_cell_lift_anc par n Z
  let ch : ℕ → hereditary_sts_substitution_sofic_ExtTile τ hsts C hC :=
    fun r => cell (n + r) (anc r)
  let placed : ℕ → PlacedTile X.dec.P' := fun r =>
    ⟨X.formEquiv.symm (Sum.inl (ch r)), (anc r).1.anchor⟩
  have hext : ∀ r, hereditary_sts_substitution_sofic_IsExtChild τ hsts C m hC
      (ch (r + 1)) (ch r) := by
    intro r
    refine ⟨?_, hb (n + r) (anc r)⟩
    have h1 := (hspec (n + r) (anc r)).1
    have h2 := congrArg PlacedTile.form (hspec (n + r + 1) (par (n + r) (anc r))).2
    change C.owner (cell (n + r) (anc r)).1 = C.form (cell (n + (r + 1)) (par (n + r) (anc r))).1
    rw [ha, ha]
    exact h1.trans h2
  have hdec : ∀ r (hf : (anc r).1.form = C.form (ch r).1),
      hereditary_sts_substitution_sofic_decode τ hsts C hC (ch r) =
        some (hf ▸ H.gamma (n + r) (anc r).1 (anc r).2) := fun r hf =>
    hc (n + r) (anc r) hf
  have hformr : ∀ r, (anc r).1.form = C.form (ch r).1 := fun r =>
    (hform (n + r) (anc r)).symm
  have hfollow : hereditary_sts_substitution_sofic_FollowsHierarchyBy τ hsts C m hC X T H
      col n ⟨X.formEquiv.symm (Sum.inl (cell n Z)), Z.1.anchor⟩ (cell n Z) placed ch := by
    refine ⟨rfl, rfl, fun r => ⟨⟨anc r, rfl⟩, X.formEquiv.apply_symm_apply _, hext r, ?_,
      (anc r).1, (anc r).2, hformr r, rfl, hdec r (hformr r)⟩, hd n Z⟩
    have h := congrArg PlacedTile.anchor (hspec (n + r) (anc r)).2
    change (anc r).1.anchor =
      C.σ.θ • (par (n + r) (anc r)).1.anchor + C.anchor (cell (n + r) (anc r)).1
    rw [ha]
    exact h
  refine ⟨cell n Z, X.formEquiv.apply_symm_apply _, ?_, placed, ch, hfollow⟩
  refine ⟨ch, rfl, hext, fun r => ?_, hd n Z⟩
  rw [hdec r (hformr r)]
  rfl

/-- Step 10c of the reviewed proof: the geometric five-coordinate argument.
For two coincident sides following the fixed hierarchy, a finite source on
either actual ancestor chain forces equality of the initial cell values.  Its
cases are sibling prints, sibling non-prints, external packets and schedules,
and the aligned port of a copied third cell. -/
private lemma hereditary_sts_substitution_sofic_step10c_source_pair_geometry
    (τ : Substitution P) (hsts : τ.STS) (hher : τ.HereditarySides)
    (C : Geometry.MacroCertificate P) (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (T : PlaneTiling P)
    (H : hereditary_sts_substitution_sofic_GenuineCrownHierarchy
      τ hsts C m hC T)
    (L : hereditary_sts_substitution_sofic_FoundedLift
      τ hsts C m hC X T H) :
    ∀ n (Y : PlacedTile X.dec.P') (_hY : Y ∈ (L.coloured n).tiles)
      (Z : PlacedTile X.dec.P') (_hZ : Z ∈ (L.coloured n).tiles), Y ≠ Z →
      ∀ A B, X.formEquiv Y.form = Sum.inl A →
      X.formEquiv Z.form = Sum.inl B →
      ∀ (placedA placedB : ℕ → PlacedTile X.dec.P')
        (chA chB : ℕ → hereditary_sts_substitution_sofic_ExtTile τ hsts C hC),
      hereditary_sts_substitution_sofic_FollowsHierarchyBy
          τ hsts C m hC X T H L.coloured n Y A placedA chA →
      hereditary_sts_substitution_sofic_FollowsHierarchyBy
          τ hsts C m hC X T H L.coloured n Z B placedB chB →
      ∀ (i : C.Side A.1) (j : C.Side B.1),
      hereditary_sts_substitution_sofic_CoincidentTypedSides
          τ hsts C hC X.dec Y Z A B i j →
      ∀ k : Fin 5,
      ((∃ iA : C.Side (chA 0).1, HEq i iA ∧
          hereditary_sts_substitution_sofic_ExtHasOrigin
            τ hsts C hC chA 0 iA k) ∨
        (∃ jB : C.Side (chB 0).1, HEq j jB ∧
          hereditary_sts_substitution_sofic_ExtHasOrigin
            τ hsts C hC chB 0 jB k)) →
      A.2 i k = B.2 j k := by
  sorry

/-- Step 10d: combine finite-source matching with the origin-or-zero clauses
of the two actual hierarchy chains.  If either side has a finite source use
Step 10c; if neither does, both copied values are literally zero. -/
private lemma hereditary_sts_substitution_sofic_step10d_all_cells_match
    (τ : Substitution P) (hsts : τ.STS) (hher : τ.HereditarySides)
    (C : Geometry.MacroCertificate P) (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (T : PlaneTiling P)
    (H : hereditary_sts_substitution_sofic_GenuineCrownHierarchy
      τ hsts C m hC T)
    (L : hereditary_sts_substitution_sofic_FoundedLift
      τ hsts C m hC X T H) :
    ∀ n (Y : PlacedTile X.dec.P') (_hY : Y ∈ (L.coloured n).tiles)
      (Z : PlacedTile X.dec.P') (_hZ : Z ∈ (L.coloured n).tiles), Y ≠ Z →
      ∀ A B, X.formEquiv Y.form = Sum.inl A →
      X.formEquiv Z.form = Sum.inl B →
      ∀ (i : C.Side A.1) (j : C.Side B.1),
      hereditary_sts_substitution_sofic_CoincidentTypedSides
          τ hsts C hC X.dec Y Z A B i j →
      A.2 i = B.2 j := by
  intro n Y hY Z hZ hYZ A B hA hB i j hij
  obtain ⟨A', hA', _, placedA, chA, hfollowA⟩ := L.follows n Y hY
  obtain ⟨B', hB', _, placedB, chB, hfollowB⟩ := L.follows n Z hZ
  have hAA' : A = A' := Sum.inl.inj (hA.symm.trans hA')
  have hBB' : B = B' := Sum.inl.inj (hB.symm.trans hB')
  subst A'
  subst B'
  rcases hfollowA with ⟨hplacedA, hchA, hlevelsA, hzeroA⟩
  rcases hfollowB with ⟨hplacedB, hchB, hlevelsB, hzeroB⟩
  subst A
  subst B
  funext k
  by_cases horiginA :
      hereditary_sts_substitution_sofic_ExtHasOrigin τ hsts C hC chA 0 i k
  · exact hereditary_sts_substitution_sofic_step10c_source_pair_geometry
      τ hsts hher C m hC X T H L n Y hY Z hZ hYZ (chA 0) (chB 0)
      hA hB placedA placedB chA chB
      ⟨hplacedA, rfl, hlevelsA, hzeroA⟩
      ⟨hplacedB, rfl, hlevelsB, hzeroB⟩ i j hij k
      (Or.inl ⟨i, HEq.rfl, horiginA⟩)
  · by_cases horiginB :
        hereditary_sts_substitution_sofic_ExtHasOrigin τ hsts C hC chB 0 j k
    · exact hereditary_sts_substitution_sofic_step10c_source_pair_geometry
        τ hsts hher C m hC X T H L n Y hY Z hZ hYZ (chA 0) (chB 0)
        hA hB placedA placedB chA chB
        ⟨hplacedA, rfl, hlevelsA, hzeroA⟩
        ⟨hplacedB, rfl, hlevelsB, hzeroB⟩ i j hij k
        (Or.inr ⟨j, HEq.rfl, horiginB⟩)
    · have hsourceA :
          (Planned.copySource C (C.form (chA 1).1)
            (C.occ (chA 0).1 i) k).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro hempty
        apply horiginA
        exact ⟨⟨0, i, k⟩, Relation.ReflTransGen.refl, by simpa using hempty⟩
      have hsourceB :
          (Planned.copySource C (C.form (chB 1).1)
            (C.occ (chB 0).1 j) k).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro hempty
        apply horiginB
        exact ⟨⟨0, j, k⟩, Relation.ReflTransGen.refl, by simpa using hempty⟩
      rw [hzeroA 0 i k hsourceA horiginA, hzeroB 0 j k hsourceB horiginB]

/-- Step 10e: the presentation's illegal-incidence contract turns founded
legality and the now-proved equality of all coincident five-cell arrays into
properness of the bottom colouring. -/
private lemma hereditary_sts_substitution_sofic_step10e_bottom_proper
    (τ : Substitution P) (hsts : τ.STS) (hher : τ.HereditarySides)
    (C : Geometry.MacroCertificate P) (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (T : PlaneTiling P)
    (H : hereditary_sts_substitution_sofic_GenuineCrownHierarchy
      τ hsts C m hC T)
    (L : hereditary_sts_substitution_sofic_FoundedLift
      τ hsts C m hC X T H) :
    X.dec.Proper (L.coloured 0) := by
  apply X.proper_of_typed_legal (L.coloured 0) (L.sideToSide 0)
  · intro Y hY
    obtain ⟨A, hA, hlegal, _⟩ := L.follows 0 Y hY
    exact ⟨A, hA, hlegal⟩
  · intro Y hY Z hZ hYZ A B hA hB i j hij
    exact hereditary_sts_substitution_sofic_step10d_all_cells_match
      τ hsts hher C m hC X T H L 0 Y hY Z hZ hYZ A B hA hB i j hij

/-- Step 10: assemble the two independent completeness obligations. -/
private lemma hereditary_sts_substitution_sofic_step10_completeness
    (τ : Substitution P) (hsts : τ.STS) (hher : τ.HereditarySides)
    (C : Geometry.MacroCertificate P) (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC)
    (T : PlaneTiling P) (hT : τ.IsSubstitutionTiling T) :
    ∃ U : PlaneTiling C.Q,
      U ∈ hereditary_sts_substitution_sofic_controlFamily τ hsts C X ∧
      hC.groupedFamily.scatter U.tiles = T.tiles := by
  let H := Classical.choice
    (hereditary_sts_substitution_sofic_step10a_genuine_crown_hierarchy
      τ hsts hher C m hC T hT)
  let L := Classical.choice
    (hereditary_sts_substitution_sofic_step10b_founded_cell_lift
      τ hsts hher C m hC X T H)
  refine ⟨H.seq 0, ?_, H.bottom⟩
  exact ⟨L.coloured 0,
    hereditary_sts_substitution_sofic_step10e_bottom_proper
      τ hsts hher C m hC X T H L,
    L.project 0⟩

/-- Step 11: the two separately proved inclusions give the exact scattered
family. -/
private lemma hereditary_sts_substitution_sofic_step11_exact_family
    (τ : Substitution P) (hsts : τ.STS) (hher : τ.HereditarySides)
    (C : Geometry.MacroCertificate P) (m : ℕ) (hC : C.Represents τ m)
    (X : hereditary_sts_substitution_sofic_CrownPresentation τ hsts C m hC) :
    hC.groupedFamily.scatterFamily
        (hereditary_sts_substitution_sofic_controlFamily τ hsts C X) =
      {T | τ.IsSubstitutionTiling T} := by
  ext T
  constructor
  · rintro ⟨U, hU, hscatter⟩
    exact hereditary_sts_substitution_sofic_step9_soundness
      τ hsts hher C m hC X U hU T hscatter
  · intro hT
    obtain ⟨U, hU, hscatter⟩ :=
      hereditary_sts_substitution_sofic_step10_completeness
        τ hsts hher C m hC X T hT
    exact ⟨U, hU, hscatter⟩

/-- `thm:hereditary-substitution`: an STS substitution with hereditary
listed sides has a side-to-side sofic substitution family. -/
theorem Core.hereditary_sts_substitution_sofic (τ : Substitution P) (hsts : τ.STS)
    (hher : τ.HereditarySides) : IsSideToSideSofic {T | τ.IsSubstitutionTiling T} := by
  obtain ⟨C, m, hC⟩ := Geometry.existsMacroCertificate τ hsts
  let X := Classical.choice
    (hereditary_sts_substitution_sofic_step4_finite_side_encoding
      τ hsts C m hC)
  have hcontrol :=
    hereditary_sts_substitution_sofic_step4_control_family_sofic
      τ hsts C X
  have hscatter := Decoration.dissection_preserves_sts_sofic
    hC.groupedFamily hcontrol
  rw [hereditary_sts_substitution_sofic_step11_exact_family
    τ hsts hher C m hC X] at hscatter
  exact hscatter

/-! ### The hereditary STS hierarchy assembly steps -/

private noncomputable def hereditary_sts_hierarchy_sofic_step1_control_decoration
    (C : Geometry.MacroCertificate P) : Decoration C.Q where
  P' :=
    { Form := C.Q.Form ⊕ Planned.DecTile C
      disk := fun
        | Sum.inl α => C.Q.disk α
        | Sum.inr A => C.Q.disk (C.form A.typ) }
  proj := fun
    | Sum.inl α => α
    | Sum.inr A => C.form A.typ
  surj α := ⟨Sum.inl α, rfl⟩
  carrier_eq := fun
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl

/-! The control rule is separated into its finite encoding and its two decoding
directions.  The intermediate predicate mentions only the decorated alphabet;
in particular, it does not choose a witness tiling or erase any tiles. -/

private def hereditary_sts_hierarchy_sofic_step1_control_control_rule_locallyCompatible
    (C : Geometry.MacroCertificate P)
    (T' : PlaneTiling (hereditary_sts_hierarchy_sofic_step1_control_decoration C).P') : Prop :=
  (∀ X ∈ T'.tiles, ∃ A : Planned.DecTile C,
    X.form = Sum.inr A ∧ Planned.headerLegal C A) ∧
  (∀ X ∈ T'.tiles, ∀ A : Planned.DecTile C, X.form = Sum.inr A →
    ∀ i : C.Side A.typ, Planned.IsNontrivial C A i →
      ∃ Y ∈ T'.tiles, Y ≠ X ∧ ∃ B : Planned.DecTile C,
        ∃ j : C.Side B.typ, Y.form = Sum.inr B ∧
          Planned.sideOf C ⟨B, Y.anchor⟩ j = Planned.sideOf C ⟨A, X.anchor⟩ i ∧
          (∀ k : Fin 5, B.cell j k = A.cell i k))

private abbrev controlEncodingProtoset (C : Geometry.MacroCertificate P) : Protoset :=
  (hereditary_sts_hierarchy_sofic_step1_control_decoration C).P'

private def controlEncodingValid (C : Geometry.MacroCertificate P)
    (X : PlacedTile (controlEncodingProtoset C)) : Prop :=
  ∃ A : Planned.DecTile C, X.form = Sum.inr A ∧ Planned.headerLegal C A

private def controlEncodingMatch (C : Geometry.MacroCertificate P)
    (X : PlacedTile (controlEncodingProtoset C)) (A : Planned.DecTile C)
    (i : C.Side A.typ) (Y : PlacedTile (controlEncodingProtoset C)) : Prop :=
  Y ≠ X ∧ ∃ B : Planned.DecTile C, ∃ j : C.Side B.typ,
    Y.form = Sum.inr B ∧
      Planned.sideOf C ⟨B, Y.anchor⟩ j = Planned.sideOf C ⟨A, X.anchor⟩ i ∧
      ∀ k : Fin 5, B.cell j k = A.cell i k

private def controlEncodingFailure (C : Geometry.MacroCertificate P)
    (F : Set (PlacedTile (controlEncodingProtoset C)))
    (X : PlacedTile (controlEncodingProtoset C)) : Prop :=
  ¬ controlEncodingValid C X ∨
    ∃ (A : Planned.DecTile C) (_hA : X.form = Sum.inr A) (i : C.Side A.typ),
      Planned.IsNontrivial C A i ∧ ∀ Y ∈ F, ¬ controlEncodingMatch C X A i Y

private def controlEncodingSize (Q : Protoset) : ℝ :=
  ∑ q : Q.Form, Metric.diam (Q.disk q).carrier

private def controlEncodingRadius (Q : Protoset) : ℝ :=
  1 + 2 * controlEncodingSize Q

private lemma controlEncodingSize_nonneg (Q : Protoset) : 0 ≤ controlEncodingSize Q := by
  exact Finset.sum_nonneg fun _ _ => Metric.diam_nonneg

private lemma controlEncodingRadius_pos (Q : Protoset) : 0 < controlEncodingRadius Q := by
  unfold controlEncodingRadius
  linarith [controlEncodingSize_nonneg Q]

private lemma controlEncoding_tile_diam_le (Q : Protoset) (X : PlacedTile Q) :
    Metric.diam X.carrier ≤ controlEncodingSize Q := by
  rw [PlacedTile.carrier, diam_vadd]
  exact Finset.single_le_sum
    (f := fun q : Q.Form => Metric.diam (Q.disk q).carrier)
    (fun _ _ => Metric.diam_nonneg) (Finset.mem_univ X.form)

private def controlEncodingForbidden (C : Geometry.MacroCertificate P)
    (F : Set (PlacedTile (controlEncodingProtoset C))) : Prop :=
  F.Finite ∧ ∃ X ∈ F, ∃ c ∈ X.carrier,
    Metric.ball c (controlEncodingRadius (controlEncodingProtoset C)) ⊆ support F ∧
      (∀ Y ∈ F,
        (Y.carrier ∩ Metric.ball c (controlEncodingRadius (controlEncodingProtoset C))).Nonempty) ∧
      controlEncodingFailure C F X

private def controlEncodingRule (C : Geometry.MacroCertificate P) :
    LocalRule (controlEncodingProtoset C) where
  forbidden := {F | controlEncodingForbidden C F}
  D := 2 * (controlEncodingRadius (controlEncodingProtoset C) +
    controlEncodingSize (controlEncodingProtoset C))
  bounded := by
    rintro F ⟨hF, X, hXF, c, hcX, hcover, hmeet, hfail⟩
    refine ⟨hF, ?_⟩
    apply Metric.diam_le_of_forall_dist_le
    · have hs := controlEncodingSize_nonneg (controlEncodingProtoset C)
      have hr := (controlEncodingRadius_pos (controlEncodingProtoset C)).le
      positivity
    · intro x hx y hy
      simp only [support, Set.mem_iUnion] at hx hy
      obtain ⟨A, hAF, hxA⟩ := hx
      obtain ⟨B, hBF, hyB⟩ := hy
      obtain ⟨a, haA, hac⟩ := hmeet A hAF
      obtain ⟨b, hbB, hbc⟩ := hmeet B hBF
      have hxa : dist x a ≤ controlEncodingSize (controlEncodingProtoset C) :=
        (Metric.dist_le_diam_of_mem (cc_tile_compact A).isBounded hxA haA).trans
          (controlEncoding_tile_diam_le _ A)
      have hyb : dist b y ≤ controlEncodingSize (controlEncodingProtoset C) :=
        (Metric.dist_le_diam_of_mem (cc_tile_compact B).isBounded hbB hyB).trans
          (controlEncoding_tile_diam_le _ B)
      have hac' : dist a c < controlEncodingRadius (controlEncodingProtoset C) :=
        Metric.mem_ball.mp hac
      have hcb' : dist c b < controlEncodingRadius (controlEncodingProtoset C) := by
        rw [dist_comm]
        exact Metric.mem_ball.mp hbc
      calc
        dist x y ≤ dist x a + dist a y := dist_triangle _ _ _
        _ ≤ dist x a + (dist a c + dist c y) := by gcongr; exact dist_triangle _ _ _
        _ ≤ dist x a + (dist a c + (dist c b + dist b y)) := by
          gcongr
          exact dist_triangle _ _ _
        _ ≤ 2 * (controlEncodingRadius (controlEncodingProtoset C) +
            controlEncodingSize (controlEncodingProtoset C)) := by linarith

private lemma controlEncoding_vertex_mem_carrier (Q : Protoset) (X : PlacedTile Q)
    (i : Fin (Q.disk X.form).n) : X.vertex i ∈ X.carrier := by
  apply dissection_preserves_sts_sofic_step1_local_rule_tile_side_subset X i
  exact ⟨(Q.disk X.form).vertex i, left_mem_segment ℝ _ _, rfl⟩

private lemma controlEncoding_failure_occurs (C : Geometry.MacroCertificate P)
    (T : PlaneTiling (controlEncodingProtoset C)) (X : PlacedTile (controlEncodingProtoset C))
    (hXT : X ∈ T.tiles) (hfail : controlEncodingFailure C T.tiles X) :
    ∃ F ∈ (controlEncodingRule C).forbidden, OccursIn F T.tiles := by
  let i0 : Fin ((controlEncodingProtoset C).disk X.form).n :=
    ⟨0, by have := ((controlEncodingProtoset C).disk X.form).three_le; omega⟩
  let c : Pt := X.vertex i0
  let r : ℝ := controlEncodingRadius (controlEncodingProtoset C)
  let F : Set (PlacedTile (controlEncodingProtoset C)) :=
    {Y ∈ T.tiles | (Y.carrier ∩ Metric.ball c r).Nonempty}
  obtain ⟨N, hN⟩ := cc_count (controlEncodingProtoset C) r
  have hFfin : F.Finite := (hN T.tiles T.disjoint c).1
  have hcX : c ∈ X.carrier := controlEncoding_vertex_mem_carrier _ X i0
  have hXF : X ∈ F := by
    exact ⟨hXT, c, hcX, Metric.mem_ball_self (controlEncodingRadius_pos _)⟩
  have hFsub : F ⊆ T.tiles := fun _ hY => hY.1
  have hcover : Metric.ball c r ⊆ support F := by
    intro x hx
    have hxT : x ∈ support T.tiles := by rw [T.cover]; trivial
    simp only [support, Set.mem_iUnion] at hxT ⊢
    obtain ⟨Y, hYT, hxY⟩ := hxT
    exact ⟨Y, ⟨hYT, x, hxY, hx⟩, hxY⟩
  have hfailF : controlEncodingFailure C F X := by
    rcases hfail with hbad | ⟨A, hA, i, hi, hnone⟩
    · exact Or.inl hbad
    · exact Or.inr ⟨A, hA, i, hi, fun Y hY hmatch => hnone Y (hFsub hY) hmatch⟩
  refine ⟨F, ⟨hFfin, X, hXF, c, hcX, hcover, ?_, hfailF⟩, ?_⟩
  · exact fun Y hY => hY.2
  · refine ⟨0, ?_⟩
    simpa [translateSet, PlacedTile.translate] using hFsub

private lemma controlEncodingMatch_of_translate (C : Geometry.MacroCertificate P)
    (X : PlacedTile (controlEncodingProtoset C)) (A : Planned.DecTile C)
    (i : C.Side A.typ) (Y : PlacedTile (controlEncodingProtoset C)) (v : Pt)
    (h : controlEncodingMatch C (X.translate v) A i (Y.translate v)) :
    controlEncodingMatch C X A i Y := by
  obtain ⟨hne, B, j, hform, hside, hcell⟩ := h
  refine ⟨?_, B, j, ?_, ?_, hcell⟩
  · intro hXY
    exact hne (congrArg (fun Z : PlacedTile (controlEncodingProtoset C) => Z.translate v) hXY)
  · simpa [PlacedTile.translate] using hform
  · have hside' := congrArg (fun s : Set Pt => (-v) +ᵥ s) hside
    simpa [Planned.sideOf, PlacedTile.translate, vadd_vadd] using hside'

/-- Step 1 of the blueprint proof of
`hereditary_sts_hierarchy_sofic_step1_control_control_rule`: encode the finite
local compatibility conditions of the decorated alphabet by a bounded rule. -/
private theorem hereditary_sts_hierarchy_sofic_step1_control_control_rule_step1_local_encoding
    (C : Geometry.MacroCertificate P) :
    ∃ R : LocalRule (hereditary_sts_hierarchy_sofic_step1_control_decoration C).P',
      ∀ T' : PlaneTiling (hereditary_sts_hierarchy_sofic_step1_control_decoration C).P',
        R.Proper T' ↔
          hereditary_sts_hierarchy_sofic_step1_control_control_rule_locallyCompatible C T' := by
  refine ⟨controlEncodingRule C, fun T => ?_⟩
  constructor
  · intro hproper
    have hnofail : ∀ X ∈ T.tiles, ¬ controlEncodingFailure C T.tiles X := by
      intro X hXT hfail
      obtain ⟨F, hFR, hocc⟩ := controlEncoding_failure_occurs C T X hXT hfail
      exact hproper F hFR hocc
    constructor
    · intro X hXT
      by_contra hbad
      exact hnofail X hXT (Or.inl hbad)
    · intro X hXT A hXA i hi
      by_contra hnone
      apply hnofail X hXT
      refine Or.inr ⟨A, hXA, i, hi, ?_⟩
      intro Y hYT hmatch
      apply hnone
      obtain ⟨hYX, B, j, hYB, hside, hcell⟩ := hmatch
      exact ⟨Y, hYT, hYX, B, j, hYB, hside, hcell⟩
  · rintro ⟨hvalid, hmatched⟩ F hforbidden ⟨v, hv⟩
    obtain ⟨hFfin, X, hXF, c, hcX, hcover, hmeet, hfail⟩ := hforbidden
    have hXvT : X.translate v ∈ T.tiles := hv ⟨X, hXF, rfl⟩
    rcases hfail with hbad | ⟨A, hXA, i, hi, hnone⟩
    · apply hbad
      obtain ⟨A, hform, hlegal⟩ := hvalid (X.translate v) hXvT
      exact ⟨A, by simpa [PlacedTile.translate] using hform, hlegal⟩
    · have hXAv : (X.translate v).form = Sum.inr A := by
        simpa [PlacedTile.translate] using hXA
      obtain ⟨Y, hYT, hYX, B, j, hYB, hside, hcell⟩ :=
        hmatched (X.translate v) hXvT A hXAv i hi
      have hmatchv : controlEncodingMatch C (X.translate v) A i Y :=
        ⟨hYX, B, j, hYB, hside, hcell⟩
      let Ft : Set (PlacedTile (controlEncodingProtoset C)) := translateSet v F
      have hFtfin : Ft.Finite := by
        dsimp [Ft, translateSet]
        exact hFfin.image (fun Z => Z.translate v)
      have hFtdisj : DisjointInteriors Ft := by
        intro Z hZ W hW hZW
        exact T.disjoint (hv hZ) (hv hW) hZW
      let Fpatch : Patch (controlEncodingProtoset C) := ⟨Ft, hFtfin, hFtdisj⟩
      have hYsub : Y.carrier ⊆ support Ft := by
        intro y hyY
        let p : Pt :=
          (X.translate v).anchor +ᵥ (C.Q.disk (C.form A.typ)).vertex i
        have hpXside : p ∈ Planned.sideOf C ⟨A, (X.translate v).anchor⟩ i := by
          exact ⟨(C.Q.disk (C.form A.typ)).vertex i, left_mem_segment ℝ _ _, rfl⟩
        have hpX : p ∈ (X.translate v).carrier := by
          have hp := dissection_preserves_sts_sofic_step1_local_rule_tile_side_subset
            (⟨A, (X.translate v).anchor⟩ : PlacedTile (Planned.typedDecoration C)) i hpXside
          simpa [PlacedTile.carrier, hXAv] using hp
        have hpYside : p ∈ Planned.sideOf C ⟨B, Y.anchor⟩ j := by
          rw [hside]
          exact hpXside
        have hpY : p ∈ Y.carrier := by
          have hp := dissection_preserves_sts_sofic_step1_local_rule_tile_side_subset
            (⟨B, Y.anchor⟩ : PlacedTile (Planned.typedDecoration C)) j hpYside
          simpa [PlacedTile.carrier, hYB] using hp
        have hcvX : v +ᵥ c ∈ (X.translate v).carrier := by
          simpa [PlacedTile.carrier, PlacedTile.translate, vadd_vadd] using
            (show v +ᵥ c ∈ v +ᵥ X.carrier from vadd_mem_vadd_set hcX)
        have hyp : dist y p ≤ controlEncodingSize (controlEncodingProtoset C) :=
          (Metric.dist_le_diam_of_mem (cc_tile_compact Y).isBounded hyY hpY).trans
            (controlEncoding_tile_diam_le _ Y)
        have hpc : dist p (v +ᵥ c) ≤ controlEncodingSize (controlEncodingProtoset C) :=
          (Metric.dist_le_diam_of_mem (cc_tile_compact (X.translate v)).isBounded hpX hcvX).trans
            (controlEncoding_tile_diam_le _ (X.translate v))
        have hyball : y ∈ Metric.ball (v +ᵥ c)
            (controlEncodingRadius (controlEncodingProtoset C)) := by
          rw [Metric.mem_ball]
          calc
            dist y (v +ᵥ c) ≤ dist y p + dist p (v +ᵥ c) := dist_triangle _ _ _
            _ < controlEncodingRadius (controlEncodingProtoset C) := by
              unfold controlEncodingRadius
              linarith
        change y ∈ support (translateSet v F)
        rw [cc_support_translate]
        let y0 : Pt := -v +ᵥ y
        have hy0 : y0 ∈ Metric.ball c (controlEncodingRadius (controlEncodingProtoset C)) := by
          rw [Metric.mem_ball]
          rw [Metric.mem_ball] at hyball
          have heq : dist y0 c = dist y (v +ᵥ c) := by
            rw [dist_eq_norm, dist_eq_norm]
            congr 1
            simp only [y0, vadd_eq_add]
            abel
          rwa [heq]
        exact ⟨y0, hcover hy0, by simp [y0]⟩
      have hYFt : Y ∈ Ft := by
        apply Patch.mem_of_carrier_subset_union Fpatch Y
        · intro Z hZ hZY
          exact T.disjoint hYT (hv hZ) hZY.symm
        · exact hYsub
      rcases hYFt with ⟨Z, hZF, hZY⟩
      apply hnone Z hZF
      apply controlEncodingMatch_of_translate C X A i Z v
      rw [← hZY] at hmatchv
      exact hmatchv

/-- Step 2 of the blueprint proof of
`hereditary_sts_hierarchy_sofic_step1_control_control_rule`: decode a locally
compatible decorated tiling into a proper legal typed tiling. -/
private theorem hereditary_sts_hierarchy_sofic_step1_control_control_rule_step2_soundness
    (C : Geometry.MacroCertificate P) :
    ∀ T' : PlaneTiling (hereditary_sts_hierarchy_sofic_step1_control_decoration C).P',
      hereditary_sts_hierarchy_sofic_step1_control_control_rule_locallyCompatible C T' →
      ∃ U : PlaneTiling (Planned.typedDecoration C),
        Planned.IsProper C U ∧
        (∀ X ∈ U.tiles, Planned.headerLegal C (Planned.tileDec X)) ∧
        ((hereditary_sts_hierarchy_sofic_step1_control_decoration C).project T').tiles =
          Planned.eraseSet C U.tiles := by
  rintro T' ⟨hvalid, hmatch⟩
  let f : PlacedTile (Planned.typedDecoration C) →
      PlacedTile (hereditary_sts_hierarchy_sofic_step1_control_decoration C).P' :=
    fun X => ⟨Sum.inr X.form, X.anchor⟩
  have hf_carrier : ∀ X, (f X).carrier = X.carrier := fun _ => rfl
  have hf_inj : Function.Injective f := by
    intro X Y h
    have hform := congrArg (fun W => W.form) h
    have hanchor := congrArg (fun W => W.anchor) h
    change (Sum.inr X.form : C.Q.Form ⊕ Planned.DecTile C) = Sum.inr Y.form at hform
    exact PlacedTile.ext (Sum.inr.inj hform) hanchor
  have hf_mk : ∀ Z ∈ T'.tiles, ∀ A : Planned.DecTile C, Z.form = Sum.inr A →
      f ⟨A, Z.anchor⟩ = Z := by
    intro Z _ A hZA
    cases Z with
    | mk zform zanchor =>
      change zform = Sum.inr A at hZA
      subst hZA
      rfl
  have himage : f '' {X | f X ∈ T'.tiles} = T'.tiles := by
    apply Set.Subset.antisymm
    · rintro _ ⟨X, hX, rfl⟩
      exact hX
    · intro Z hZ
      obtain ⟨A, hZA, _⟩ := hvalid Z hZ
      exact ⟨⟨A, Z.anchor⟩, by simpa [hf_mk Z hZ A hZA] using hZ, hf_mk Z hZ A hZA⟩
  have hcover : support {X | f X ∈ T'.tiles} = Set.univ := by
    have hcov := T'.cover
    rw [← himage, support, Set.biUnion_image] at hcov
    simp only [hf_carrier] at hcov
    exact hcov
  have hdisj : DisjointInteriors {X | f X ∈ T'.tiles} := by
    intro X hX Y hY hXY
    have h := T'.disjoint hX hY (hf_inj.ne hXY)
    simpa only [Function.onFun, hf_carrier] using h
  obtain ⟨U, hU⟩ : ∃ U : PlaneTiling (Planned.typedDecoration C), U.tiles = {X | f X ∈ T'.tiles} :=
    ⟨⟨_, hcover, hdisj⟩, rfl⟩
  refine ⟨U, ?_, ?_, ?_⟩
  · intro X hX i hi
    rw [hU] at hX
    obtain ⟨Y, hYT, hYX, B, j, hYB, hside, hcell⟩ := hmatch (f X) hX X.form rfl i hi
    let Y' : PlacedTile (Planned.typedDecoration C) := ⟨B, Y.anchor⟩
    have hY' : f Y' = Y := hf_mk Y hYT B hYB
    refine ⟨Y', ?_, ?_, j, hside, hcell⟩
    · rw [hU]
      change f Y' ∈ T'.tiles
      rw [hY']
      exact hYT
    · intro h
      apply hYX
      rw [← hY', h]
  · intro X hX
    rw [hU] at hX
    obtain ⟨A, hXA, hleg⟩ := hvalid (f X) hX
    have hA : X.form = A := Sum.inr.inj hXA
    change Planned.headerLegal C X.form
    rw [hA]
    exact hleg
  · change (hereditary_sts_hierarchy_sofic_step1_control_decoration C).projTile '' T'.tiles =
      Planned.erase C '' U.tiles
    rw [hU]
    conv_lhs => rw [← himage, Set.image_image]
    rfl

/-- Step 3 of the blueprint proof of
`hereditary_sts_hierarchy_sofic_step1_control_control_rule`: realize every
proper legal typed tiling in the decorated alphabet with the same projection. -/
private theorem hereditary_sts_hierarchy_sofic_step1_control_control_rule_step3_completeness
    (C : Geometry.MacroCertificate P) :
    ∀ U : PlaneTiling (Planned.typedDecoration C),
      Planned.IsProper C U →
      (∀ X ∈ U.tiles, Planned.headerLegal C (Planned.tileDec X)) →
      ∃ T' : PlaneTiling (hereditary_sts_hierarchy_sofic_step1_control_decoration C).P',
        hereditary_sts_hierarchy_sofic_step1_control_control_rule_locallyCompatible C T' ∧
        ((hereditary_sts_hierarchy_sofic_step1_control_decoration C).project T').tiles =
          Planned.eraseSet C U.tiles := by
  intro U hU hleg
  let f : PlacedTile (Planned.typedDecoration C) →
      PlacedTile (hereditary_sts_hierarchy_sofic_step1_control_decoration C).P' :=
    fun X => ⟨Sum.inr X.form, X.anchor⟩
  let T' : PlaneTiling (hereditary_sts_hierarchy_sofic_step1_control_decoration C).P' :=
    { tiles := f '' U.tiles
      cover := by
        simpa [support, f, PlacedTile.carrier] using U.cover
      disjoint := by
        intro A hA B hB hAB
        rcases hA with ⟨X, hX, rfl⟩
        rcases hB with ⟨Y, hY, rfl⟩
        have hXY : X ≠ Y := by
          intro h
          apply hAB
          subst h
          rfl
        simpa [f, PlacedTile.carrier] using U.disjoint hX hY hXY }
  refine ⟨T', ?_, ?_⟩
  · constructor
    · intro X hX
      rcases hX with ⟨Y, hY, rfl⟩
      exact ⟨Y.form, rfl, hleg Y hY⟩
    · intro X hX A hXA i hi
      rcases hX with ⟨Y, hY, rfl⟩
      have hA : A = Y.form := by
        change (Sum.inr Y.form : C.Q.Form ⊕ Planned.DecTile C) = Sum.inr A at hXA
        exact (Sum.inr.inj hXA).symm
      subst A
      obtain ⟨Z, hZ, hYZ, j, hside, hcell⟩ := hU Y hY i hi
      refine ⟨f Z, ⟨Z, hZ, rfl⟩, ?_, Z.form, j, rfl, ?_, ?_⟩
      · intro h
        apply hYZ
        cases Z with
        | mk zform zanchor =>
          cases Y with
          | mk yform yanchor =>
            have hform := congrArg (fun W => W.form) h
            change (Sum.inr zform : C.Q.Form ⊕ Planned.DecTile C) = Sum.inr yform at hform
            apply PlacedTile.ext
            · exact Sum.inr.inj hform
            · exact congrArg (fun W => W.anchor) h
      · simpa [f, Planned.sideOf] using hside
      · exact hcell
  · ext X
    simp [T', f, hereditary_sts_hierarchy_sofic_step1_control_decoration,
      Decoration.project, Decoration.projTile, Planned.tileDec, Planned.eraseSet,
      Planned.erase]

/-- Step 1 of the blueprint proof of `hereditary_sts_hierarchy_sofic_step1_control`: the control rule. -/
private theorem hereditary_sts_hierarchy_sofic_step1_control_control_rule
    (C : Geometry.MacroCertificate P) :
    ∃ R : LocalRule (hereditary_sts_hierarchy_sofic_step1_control_decoration C).P',
      (∀ T' : PlaneTiling (hereditary_sts_hierarchy_sofic_step1_control_decoration C).P',
        R.Proper T' → ∃ U : PlaneTiling (Planned.typedDecoration C),
          Planned.IsProper C U ∧
          (∀ X ∈ U.tiles, Planned.headerLegal C (Planned.tileDec X)) ∧
          ((hereditary_sts_hierarchy_sofic_step1_control_decoration C).project T').tiles = Planned.eraseSet C U.tiles) ∧
      (∀ U : PlaneTiling (Planned.typedDecoration C),
        Planned.IsProper C U →
        (∀ X ∈ U.tiles, Planned.headerLegal C (Planned.tileDec X)) →
        ∃ T' : PlaneTiling (hereditary_sts_hierarchy_sofic_step1_control_decoration C).P',
          R.Proper T' ∧
          ((hereditary_sts_hierarchy_sofic_step1_control_decoration C).project T').tiles = Planned.eraseSet C U.tiles) := by
  obtain ⟨R, hR⟩ :=
    hereditary_sts_hierarchy_sofic_step1_control_control_rule_step1_local_encoding C
  refine ⟨R, ?_, ?_⟩
  · intro T' hT'
    exact hereditary_sts_hierarchy_sofic_step1_control_control_rule_step2_soundness C T'
      ((hR T').mp hT')
  · intro U hU hleg
    obtain ⟨T', hcompat, hproj⟩ :=
      hereditary_sts_hierarchy_sofic_step1_control_control_rule_step3_completeness C U hU hleg
    exact ⟨T', (hR T').mpr hcompat, hproj⟩

/-- Step 1 of the blueprint proof of `hereditary_sts_hierarchy_sofic`: the repaired
control presentation makes the grouped hierarchical family sofic once every grouped
hierarchy has side-to-side finite supertiles. -/
private theorem hereditary_sts_hierarchy_sofic_step1_control
    (C : Geometry.MacroCertificate P) (hH : C.Hereditary)
    (hsts : ∀ T : PlaneTiling C.Q, C.σ.IsHierarchical T →
      ∃ seq : ℕ → PlaneTiling C.Q, seq 0 = T ∧
        (∀ n, C.σ.IsComposition (seq (n + 1)) (seq n)) ∧
        Planned.HierarchySupertilesSTS C seq) :
    IsSofic {T : PlaneTiling C.Q | C.σ.IsHierarchical T} := by
  obtain ⟨R, hR1, hR2⟩ := hereditary_sts_hierarchy_sofic_step1_control_control_rule C
  use hereditary_sts_hierarchy_sofic_step1_control_decoration C, R
  intro T
  constructor
  · intro hT
    obtain ⟨seq, hseq0, hcomp, hSTS⟩ := hsts T hT
    have h_proj := Planned.projects_to_hierarchy C hH
    obtain ⟨U, hU, hleg, herase⟩ := h_proj.2.1 T ⟨seq, hseq0, hcomp, hSTS⟩
    obtain ⟨T', hProp, herase_proj⟩ := hR2 U hU hleg
    use T'
    constructor
    · exact hProp
    · have hT'_tiles : ((hereditary_sts_hierarchy_sofic_step1_control_decoration C).project T').tiles = T.tiles := by
        rw [herase_proj, herase]
      have h_cases : ∀ T₁ T₂ : PlaneTiling C.Q, T₁.tiles = T₂.tiles → T₁ = T₂ := by
        intro T₁ T₂ h
        cases T₁; cases T₂; congr
      exact h_cases _ _ hT'_tiles
  · rintro ⟨T', hProp, rfl⟩
    obtain ⟨U, hU, hleg, herase_proj⟩ := hR1 T' hProp
    have h_proj := Planned.projects_to_hierarchy C hH
    obtain ⟨T₀, herase0, hhier⟩ := h_proj.1 U hU hleg
    have hT0 : T₀.tiles = ((hereditary_sts_hierarchy_sofic_step1_control_decoration C).project T').tiles := by
      rw [herase0, ← herase_proj]
    have h_cases : ∀ T₁ T₂ : PlaneTiling C.Q, T₁.tiles = T₂.tiles → T₁ = T₂ := by
      intro T₁ T₂ h
      cases T₁; cases T₂; congr
    have h_eq : T₀ = (hereditary_sts_hierarchy_sofic_step1_control_decoration C).project T' := by
      exact h_cases _ _ hT0
    rwa [← h_eq]

/-- Step 1 of the blueprint proof of
`hereditary_sts_hierarchy_sofic_step2_certificate_sts_step1_certificate_sts`: use the
representing certificate's supertile containment to obtain side-to-side fine iterates. -/
private lemma hereditary_sts_hierarchy_sofic_step2_certificate_sts_step1_certificate_sts_aux1
    (τ : Substitution P) (hτ : τ.STS) (C : Geometry.MacroCertificate P) (m : ℕ)
    (hC : C.Represents τ m) :
    ∀ α j, SideToSideSet (τ.decomposeIter j (C.Δ α).tiles) := by
  have hmono : ∀ r {S T : Set (PlacedTile P)}, S ⊆ T →
      τ.decomposeIter r S ⊆ τ.decomposeIter r T := by
    intro r
    induction r with
    | zero => intro S T hST; exact hST
    | succ r ihr =>
      intro S T hST B hB
      change B ∈ τ.decompose (τ.decomposeIter r S) at hB
      change B ∈ τ.decompose (τ.decomposeIter r T)
      simp only [Substitution.decompose, Set.mem_iUnion] at hB ⊢
      obtain ⟨A, hA, hBA⟩ := hB
      exact ⟨A, ihr hST hA, hBA⟩
  have hadd : ∀ r n (S : Set (PlacedTile P)),
      τ.decomposeIter r (τ.decomposeIter n S) = τ.decomposeIter (n + r) S := by
    intro r
    induction r with
    | zero => intro n S; rfl
    | succ r ihr =>
      intro n S
      change τ.decompose (τ.decomposeIter r (τ.decomposeIter n S)) = _
      rw [ihr]
      rw [show n + (r + 1) = (n + r) + 1 by omega]
      rfl
  intro α j
  obtain ⟨n, p, v, hsub⟩ := hC.inside_supertile α
  have hsub' : τ.decomposeIter j (translateSet v (C.Δ α).tiles) ⊆
      τ.supertile (n + j) p := by
    calc
      τ.decomposeIter j (translateSet v (C.Δ α).tiles) ⊆
          τ.decomposeIter j (τ.supertile n p) := hmono j hsub
      _ = τ.supertile (n + j) p := by
        change τ.decomposeIter j (τ.decomposeIter n {⟨p, 0⟩}) =
          τ.decomposeIter (n + j) {⟨p, 0⟩}
        exact hadd j n {⟨p, 0⟩}
  have hsts : SideToSideSet (τ.decomposeIter j (translateSet v (C.Δ α).tiles)) := by
    intro A hA B hB i l hover
    exact hτ (n + j) p A (hsub' hA) B (hsub' hB) i l hover
  rw [hierarchy_lift_iff_decomposeIter_translate] at hsts
  set w : Pt := (τ.θ ^ j) • v
  intro A hA B hB i l hover
  have hover' : OverlapPos ((A.translate w).side i) ((B.translate w).side l) := by
    obtain ⟨x, y, hxy, hseg⟩ := hover
    refine ⟨w + x, w + y, ?_, ?_⟩
    · intro heq
      apply hxy
      exact add_left_cancel heq
    · intro z hz
      rw [← segment_translate_image] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      refine ⟨?_, ?_⟩
      · simpa [PlacedTile.side, PlacedTile.translate, add_vadd] using
          (show w +ᵥ u ∈ w +ᵥ A.side i from vadd_mem_vadd_set (hseg hu).1)
      · simpa [PlacedTile.side, PlacedTile.translate, add_vadd] using
          (show w +ᵥ u ∈ w +ᵥ B.side l from vadd_mem_vadd_set (hseg hu).2)
  have heq := hsts (A.translate w) ⟨A, hA, rfl⟩ (B.translate w) ⟨B, hB, rfl⟩ i l hover'
  have heq' := congrArg (fun s : Set Pt => (-w) +ᵥ s) heq
  simpa [PlacedTile.side, PlacedTile.translate, vadd_eq_add, vadd_vadd] using heq'

/-- Step 2 of the blueprint proof of
`hereditary_sts_hierarchy_sofic_step2_certificate_sts_step1_certificate_sts`: transfer
side-to-side fine iterates through the grouped substitution to every grouped supertile. -/
private theorem hereditary_sts_hierarchy_sofic_step2_certificate_sts_step1_certificate_sts_aux2
    (τ : Substitution P) (C : Geometry.MacroCertificate P) (m : ℕ)
    (hC : C.Represents τ m)
    (hfine : ∀ α j, SideToSideSet (τ.decomposeIter j (C.Δ α).tiles)) :
    ∀ (X : PlacedTile C.Q) (k : ℕ),
      SideToSideSet (C.σ.decomposeIter k {X}) := by
  intro X k
  let GS := hC.groupedSubstitution
  have hadd : ∀ r n (S : Set (PlacedTile P)),
      τ.decomposeIter r (τ.decomposeIter n S) = τ.decomposeIter (n + r) S := by
    intro r
    induction r with
    | zero => intro n S; rfl
    | succ r ihr =>
      intro n S
      change τ.decompose (τ.decomposeIter r (τ.decomposeIter n S)) = _
      rw [ihr]
      rw [show n + (r + 1) = (n + r) + 1 by omega]
      rfl
  have hiter : ∀ (k : ℕ) (S : Set (PlacedTile C.Q)),
      GS.G.scatter (C.σ.decomposeIter k S) = τ.decomposeIter (m * k) (GS.G.scatter S) := by
    intro k
    induction k with
    | zero => intro S; rfl
    | succ k ih =>
      intro S
      change GS.G.scatter (GS.σ.decompose (C.σ.decomposeIter k S)) = _
      rw [hierarchy_lift_iff_scatter_decompose τ GS, ih, hadd, Nat.mul_succ]
      rfl
  have hover_tr : ∀ (w : Pt) (s t : Set Pt), OverlapPos s t → OverlapPos (w +ᵥ s) (w +ᵥ t) := by
    intro w s t hover
    obtain ⟨x, y, hxy, hseg⟩ := hover
    refine ⟨w + x, w + y, ?_, ?_⟩
    · intro heq
      exact hxy (add_left_cancel heq)
    · intro z hz
      rw [← segment_translate_image] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      exact ⟨vadd_mem_vadd_set (hseg hu).1, vadd_mem_vadd_set (hseg hu).2⟩
  have hside_tr : ∀ (v : Pt) (A : PlacedTile P) (i : Fin (P.disk A.form).n),
      (A.translate v).side i = v +ᵥ A.side i := by
    intro v A i
    simp only [PlacedTile.side, PlacedTile.translate, vadd_vadd, vadd_eq_add]
  have hsts_tr : ∀ (v : Pt) (S : Set (PlacedTile P)), SideToSideSet S →
      SideToSideSet (translateSet v S) := by
    intro v S hS A hA B hB i l hover
    obtain ⟨A₀, hA₀, rfl⟩ := hA
    obtain ⟨B₀, hB₀, rfl⟩ := hB
    rw [hside_tr, hside_tr] at hover ⊢
    have h := hover_tr (-v) _ _ hover
    rw [neg_vadd_vadd, neg_vadd_vadd] at h
    rw [hS A₀ hA₀ B₀ hB₀ i l h]
  have hF : SideToSideSet (τ.decomposeIter (m * k) (GS.G.scatter {X})) := by
    have hs : GS.G.scatter {X} = translateSet X.anchor (C.Δ X.form).tiles := by
      simp only [GroupedFamily.scatter, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]
      rfl
    rw [hs, hierarchy_lift_iff_decomposeIter_translate]
    exact hsts_tr _ _ (hfine X.form (m * k))
  have hmem : ∀ Y ∈ C.σ.decomposeIter k {X}, ∀ A ∈ (C.Δ Y.form).tiles,
      A.translate Y.anchor ∈ τ.decomposeIter (m * k) (GS.G.scatter {X}) := by
    intro Y hY A hA
    rw [← hiter]
    simp only [GroupedFamily.scatter, Set.mem_iUnion]
    exact ⟨Y, hY, A, hA, rfl⟩
  have hside : ∀ (Y : PlacedTile C.Q) (A : PlacedTile P) (i : Fin (C.Q.disk Y.form).n)
      (j : Fin (P.disk A.form).n), A.side j = (C.Q.disk Y.form).side i →
      (A.translate Y.anchor).side j = Y.side i := by
    intro Y A i j h
    rw [hside_tr, h]
    rfl
  intro Y₁ hY₁ Y₂ hY₂ i₁ i₂ hover
  obtain ⟨A₁, hA₁, j₁, hj₁⟩ := hC.side_whole Y₁.form i₁
  obtain ⟨A₂, hA₂, j₂, hj₂⟩ := hC.side_whole Y₂.form i₂
  rw [← hside Y₁ A₁ i₁ j₁ hj₁, ← hside Y₂ A₂ i₂ j₂ hj₂] at hover ⊢
  exact hF _ (hmem Y₁ hY₁ A₁ hA₁) _ (hmem Y₂ hY₂ A₂ hA₂) j₁ j₂ hover

/-- Step 2 of the blueprint proof of `hereditary_sts_hierarchy_sofic_step2_certificate_sts`:
construct an STS macrocertificate whose every grouped supertile iterate is side-to-side. -/
private theorem hereditary_sts_hierarchy_sofic_step2_certificate_sts_step1_certificate_sts
    (τ : Substitution P) (hτ : τ.STS) :
    ∃ (C : Geometry.MacroCertificate P) (m : ℕ), C.Represents τ m ∧
      ∀ (X : PlacedTile C.Q) (k : ℕ),
        SideToSideSet (C.σ.decomposeIter k {X}) := by
  obtain ⟨C, m, hC⟩ := Geometry.existsMacroCertificate τ hτ
  refine ⟨C, m, hC, ?_⟩
  exact hereditary_sts_hierarchy_sofic_step2_certificate_sts_step1_certificate_sts_aux2
    τ C m hC
    (hereditary_sts_hierarchy_sofic_step2_certificate_sts_step1_certificate_sts_aux1
      τ hτ C m hC)

/-- Step 2 of the blueprint proof of `hereditary_sts_hierarchy_sofic`: the STS
certificate supplies the side-to-side-supertiling instantiation needed by the
repaired hierarchy lift for every grouped hierarchy. -/
private theorem hereditary_sts_hierarchy_sofic_step2_certificate_sts
    (τ : Substitution P) (hτ : τ.STS) :
    ∃ (C : Geometry.MacroCertificate P) (m : ℕ), C.Represents τ m ∧
      ∀ T : PlaneTiling C.Q, C.σ.IsHierarchical T →
        ∃ seq : ℕ → PlaneTiling C.Q, seq 0 = T ∧
          (∀ n, C.σ.IsComposition (seq (n + 1)) (seq n)) ∧
          Planned.HierarchySupertilesSTS C seq := by
  obtain ⟨C, m, hC, hlocal⟩ :=
    hereditary_sts_hierarchy_sofic_step2_certificate_sts_step1_certificate_sts τ hτ
  refine ⟨C, m, hC, ?_⟩
  rintro T ⟨seq, hzero, hcomp⟩
  refine ⟨seq, hzero, hcomp, ?_⟩
  change ∀ n k, k ≤ n → ∀ X ∈ (seq n).tiles, SideToSideSet (C.σ.decomposeIter k {X})
  intro n k hk X hX
  exact hlocal X k

/-- Step 1 of the blueprint proof of `hereditary_sts_hierarchy_sofic_step3_power_scatter`:
one decomposition by the power substitution `τ^m` is the `m`-fold decomposition by `τ`. -/
private lemma hereditary_sts_hierarchy_sofic_step3_power_scatter_step1_pow_decompose
    (τ : Substitution P) (m : ℕ) (hm : 0 < m) (S : Set (PlacedTile P)) :
    (τ.pow m hm).decompose S = τ.decomposeIter m S := by
  have hS : S = ⋃ A ∈ S, ({A} : Set (PlacedTile P)) := by ext; simp
  conv_rhs => rw [hS]
  rw [hierarchy_lift_iff_decomposeIter_iUnion₂]
  simp only [Substitution.decompose]
  apply Set.iUnion₂_congr
  intro A _
  have hA : ({A} : Set (PlacedTile P)) = translateSet A.anchor {⟨A.form, 0⟩} := by
    ext B
    simp [translateSet, PlacedTile.translate, PlacedTile.ext_iff]
  rw [hA, hierarchy_lift_iff_decomposeIter_translate]
  rfl

/-- Step 2 of the blueprint proof of `hereditary_sts_hierarchy_sofic_step3_power_scatter`:
the positive-power hierarchy equivalence (`τ`-hierarchies are exactly `τ^m`-hierarchies). -/
private lemma hereditary_sts_hierarchy_sofic_step3_power_scatter_step2_power_hierarchy
    (τ : Substitution P) (m : ℕ) (hm : 0 < m) (T : PlaneTiling P) :
    Grouping.IsPowerHierarchy τ m T ↔ τ.IsHierarchical T := by
  rw [hierarchical_power_iff τ m hm T]
  simp only [Grouping.IsPowerHierarchy, Substitution.IsHierarchical, Substitution.IsComposition,
    hereditary_sts_hierarchy_sofic_step3_power_scatter_step1_pow_decompose]

/-- Step 3 of the blueprint proof of `hereditary_sts_hierarchy_sofic`: grouping,
scattering, and the positive-power hierarchy equivalence identify the scattered
grouped family with the original hierarchical family. -/
private theorem hereditary_sts_hierarchy_sofic_step3_power_scatter
    (τ : Substitution P) (C : Geometry.MacroCertificate P) (m : ℕ)
    (hC : C.Represents τ m) :
    Geometry.GroupedFamily.scatterFamily
        (Geometry.MacroCertificate.Represents.groupedFamily hC)
        {T : PlaneTiling C.Q | C.σ.IsHierarchical T} =
      {T : PlaneTiling P | τ.IsHierarchical T} := by
  ext T
  simp only [Geometry.GroupedFamily.scatterFamily, Set.mem_setOf_eq]
  rw [← hereditary_sts_hierarchy_sofic_step3_power_scatter_step2_power_hierarchy τ m hC.m_pos T]
  have hlift := Grouping.hierarchy_lift_iff τ hC.groupedSubstitution hC.singleton T
  refine Iff.trans ?_ hlift.symm
  constructor
  · rintro ⟨T', ⟨seq', h0, hc⟩, hs⟩
    exact ⟨seq', hc, by rw [h0]; exact hs⟩
  · rintro ⟨seq', hc, hs⟩
    exact ⟨seq' 0, ⟨seq', rfl, hc⟩, hs⟩

/-- `thm:hereditary-hierarchy`: an STS substitution with hereditary listed
sides has a sofic family of hierarchical plane tilings. -/
theorem Core.hereditary_sts_hierarchy_sofic (τ : Substitution P) (hsts : τ.STS)
    (hher : τ.HereditarySides) : IsSofic {T | τ.IsHierarchical T} := by
  obtain ⟨C, m, hC, hstsC⟩ :=
    hereditary_sts_hierarchy_sofic_step2_certificate_sts τ hsts
  have hH : C.Hereditary := hC.hereditary hher
  have hF := hereditary_sts_hierarchy_sofic_step1_control C hH hstsC
  have hscatter := Decoration.dissection_preserves_sofic
    (Geometry.MacroCertificate.Represents.groupedFamily hC) hF
  rw [hereditary_sts_hierarchy_sofic_step3_power_scatter τ C m hC] at hscatter
  exact hscatter

end Tilings

end
