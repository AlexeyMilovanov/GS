import Tilings.Alignment
import Tilings.Control.Composition

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

/-- `thm:hereditary-substitution`: an STS substitution with hereditary
listed sides has a side-to-side sofic substitution family. -/
theorem Core.hereditary_sts_substitution_sofic (τ : Substitution P) (hsts : τ.STS)
    (hher : τ.HereditarySides) : IsSideToSideSofic {T | τ.IsSubstitutionTiling T} := by
  sorry

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
  sorry

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

/-- Step 2 of the blueprint proof of `hereditary_sts_hierarchy_sofic_step2_certificate_sts`:
construct an STS macrocertificate whose every grouped supertile iterate is side-to-side. -/
private theorem hereditary_sts_hierarchy_sofic_step2_certificate_sts_step1_certificate_sts
    (τ : Substitution P) (hτ : τ.STS) :
    ∃ (C : Geometry.MacroCertificate P) (m : ℕ), C.Represents τ m ∧
      ∀ (X : PlacedTile C.Q) (k : ℕ),
        SideToSideSet (C.σ.decomposeIter k {X}) := by
  sorry

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
  sorry

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
