import Tilings.Alignment

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

/-- `lem:glues` (generic presentations): the grouped forms are finite
connected unions of original tiles with connected dual graphs (fields of
`GroupedFamily`).  A sofic presentation of a family of grouped plane tilings
transfers, via unique glue colours on internal constituent sides and inert
decorations for surjectivity, to a sofic presentation of its scattering. -/
theorem Decoration.dissection_preserves_sofic (G : GroupedFamily P)
    {F' : Set (PlaneTiling G.P')} (h : IsSofic F') : IsSofic (G.scatterFamily F') := by
  sorry

/-- `lem:glues` (strict presentations): the same transfer for side-to-side
sofic presentations; grouped sides are complete original sides, so exposed
colours stay on whole original sides. -/
theorem Decoration.dissection_preserves_sts_sofic (G : GroupedFamily P)
    {F' : Set (PlaneTiling G.P')} (h : IsSideToSideSofic F') :
    IsSideToSideSofic (G.scatterFamily F') := by
  sorry

/-! ## Compatible grouped hierarchy lift (`lem:grouping-lift`) -/

/-- `T` is the bottom of a `τ^k`-hierarchy of plane tilings. -/
def Grouping.IsPowerHierarchy (τ : Substitution P) (k : ℕ) (T : PlaneTiling P) : Prop :=
  ∃ seq : ℕ → PlaneTiling P, seq 0 = T ∧ ∀ n, τ.decomposeIter k (seq (n + 1)).tiles = (seq n).tiles

/-- `lem:grouping-lift`: when every original form is available as a
singleton group, original `τ^k`-hierarchies are exactly the scatterings of
grouped `σ`-hierarchies. -/
theorem Grouping.hierarchy_lift_iff (τ : Substitution P) (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩}) (T : PlaneTiling P) :
    Grouping.IsPowerHierarchy τ GS.k T ↔
      ∃ seq' : ℕ → PlaneTiling GS.G.P', (∀ n, GS.σ.IsComposition (seq' (n + 1)) (seq' n)) ∧
        GS.G.scatter (seq' 0).tiles = T.tiles := by
  sorry

/-- Step 1 of the blueprint proof of `hierarchy_lift_sts`: lift the sequence. -/
private lemma hierarchy_lift_sts_step1_lift (τ : Substitution P) (GS : GroupedSubstitution τ)
    (hsingle : ∀ p : P.Form, ∃ α, (GS.G.dissect α).tiles = {⟨p, 0⟩}) (seq : ℕ → PlaneTiling P)
    (hseq : ∀ n, τ.decomposeIter GS.k (seq (n + 1)).tiles = (seq n).tiles) :
    ∃ seq' : ℕ → PlaneTiling GS.G.P', (∀ n, GS.σ.IsComposition (seq' (n + 1)) (seq' n)) ∧
      (∀ n, GS.G.scatter (seq' n).tiles = (seq n).tiles) := by
  sorry

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
  sorry

/-- Step 1 of the blueprint proof of `hierarchy_lift_sts_step2_sts_step2_match`: If an original
side in a grouped tile's scatter is a subset of the grouped side, they are equal. -/
private lemma hierarchy_lift_sts_step2_sts_step2_match_step1_eq
    (τ : Substitution P) (GS : GroupedSubstitution τ)
    (A : PlacedTile GS.G.P') (i : Fin (GS.G.P'.disk A.form).n)
    (a : PlacedTile P) (ha : a ∈ GS.G.scatterTile A) (k : Fin (P.disk a.form).n)
    (h_sub : a.side k ⊆ A.side i) :
    A.side i = a.side k := by
  sorry

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

/-- `thm:hereditary-substitution`: an STS substitution with hereditary
listed sides has a side-to-side sofic substitution family. -/
theorem Core.hereditary_sts_substitution_sofic (τ : Substitution P) (hsts : τ.STS)
    (hher : τ.HereditarySides) : IsSideToSideSofic {T | τ.IsSubstitutionTiling T} := by
  sorry

/-- `thm:hereditary-hierarchy`: an STS substitution with hereditary listed
sides has a sofic family of hierarchical plane tilings. -/
theorem Core.hereditary_sts_hierarchy_sofic (τ : Substitution P) (hsts : τ.STS)
    (hher : τ.HereditarySides) : IsSofic {T | τ.IsHierarchical T} := by
  sorry

end Tilings

end
