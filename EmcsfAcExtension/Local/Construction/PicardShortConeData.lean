module

public import EmcsfAcExtension.Local.Construction.PicardOriginalBall

/-! # Uniform short-cone domain of the Picard map

The cone radius and a preliminary length cap depend only on the first-order
data bound, positive expansion bound, and coupling. The entire ball then has
a positive expansion and inverse-gap bound, without a variation premise.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- Choose the uniform short-cone radius and preliminary length cap before
the cone position, actual length and data. Only `B,ell,|e|` enter; all displayed
numerical margins are universal. -/
theorem picardShortCone_exists_cap (B ell e : ℝ) (hB : 1 ≤ B) (he : 0 < ell) :
    ∃ ρ > 0, ρ ≤ 1 / 128 ∧ ρ ≤ ell / 4 ∧
      ∃ L₀ > 0, L₀ ≤ 1 ∧ B * L₀ + 2 * ρ ≤ 1 / 8 ∧
        |e| * (B + 1) ^ 2 * L₀ ≤ 1 := by
  let ρ := min (1 / 128) (ell / 4)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρsmall : ρ ≤ 1 / 128 := min_le_left _ _
  have hρell : ρ ≤ ell / 4 := min_le_right _ _
  let X := |e| * (B + 1) ^ 2
  have hX : 0 ≤ X := by dsimp [X]; positivity
  let L₀ := min 1 (min (1 / (32 * (B + 1))) (1 / (1 + X)))
  have hL₀ : 0 < L₀ := by dsimp [L₀]; positivity
  have hLone : L₀ ≤ 1 := min_le_left _ _
  have hLrest : L₀ ≤ min (1 / (32 * (B + 1))) (1 / (1 + X)) := min_le_right _ _
  have hLB := (le_div_iff₀ (by linarith : (0 : ℝ) < 32 * (B + 1))).mp
    (hLrest.trans (min_le_left _ _))
  have hLX := (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + X)).mp
    (hLrest.trans (min_le_right _ _))
  have hBcap : B * L₀ ≤ 1 / 32 := by
    have hnonneg := hL₀.le
    ring_nf at hLB
    linarith only [hLB, hnonneg]
  have hXcap : X * L₀ ≤ 1 := by
    have hh : X * L₀ ≤ L₀ * (1 + X) := by
      have hnonneg := hL₀.le
      linarith only [hnonneg]
    exact hh.trans hLX
  exact ⟨ρ, hρ, hρsmall, hρell, L₀, hL₀, hLone,
    by linarith only [hBcap, hρsmall], hXcap⟩

/-- A bounded C1 cone datum gives a center of size at most `B`, uniformly
in the incoming width. The coefficient one is universal in cone position,
length, datum and target space. -/
theorem picardConeCenter_size_le {c a L B : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (datum : ℝ → E) (hL : 0 < L) (hc : ContDiffOn ℝ 1 datum (Icc c (c + L)))
    (hB : 0 ≤ B) (hb : ∀ v ∈ Icc c (c + L),
      ‖datum v‖ ≤ B ∧ ‖derivWithin datum (Icc c (c + L)) v‖ ≤ B) :
    picardCarrierSize (picardConeCenterOfContDiff (a := a) datum hL hc) ≤ B := by
  apply picardCarrierSize_le_of_pointwise B hB
    (picardConeCenterOfContDiff datum hL hc)
  · intro p
    exact (hb p.1.2 ⟨p.2.1.1.trans p.2.1.2.1, p.2.1.2.2⟩).1
  · intro p
    exact (hb p.1.2 ⟨p.2.1.1.trans p.2.1.2.1, p.2.1.2.2⟩).2

/-- A derivative bound gives cone oscillation at most `B*L`, uniformly in
the cone position and datum. No second derivative or variation premise is used. -/
theorem picardConeDatum_oscillation_le {c L B : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {datum : ℝ → E} (hc : ContDiffOn ℝ 1 datum (Icc c (c + L))) (hB : 0 ≤ B)
    (hb : ∀ v ∈ Icc c (c + L), ‖derivWithin datum (Icc c (c + L)) v‖ ≤ B)
    {s t : ℝ} (hs : s ∈ Icc c (c + L)) (ht : t ∈ Icc c (c + L)) :
    dist (datum s) (datum t) ≤ B * L := by
  have hm := (convex_Icc c (c + L)).norm_image_sub_le_of_norm_derivWithin_le
    (hc.differentiableOn (by norm_num)) hb ht hs
  have hst : ‖s - t‖ ≤ L := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith only [hs.1, hs.2, ht.1, ht.2]
  simpa only [dist_eq_norm] using hm.trans (mul_le_mul_of_nonneg_left hst hB)

/-- Every candidate in the short-cone ball has positive expansion. The
constant `ell/2` is uniform in the cone, data and candidates. -/
theorem picardShortConeBall_lam_lower {c a L ell ρ : ℝ}
    (datum : ℝ → ℝ × ℂ) (hL : 0 < L)
    (hc : ContDiffOn ℝ 1 datum (Icc c (c + L))) (hρ : ρ ≤ ell / 4) (he : 0 < ell)
    (hl : ∀ v ∈ Icc c (c + L), ell ≤ (datum v).1)
    (z : PicardBall datum (picardConeCenterOfContDiff (a := a) datum hL hc) ρ)
    (p : PicardDomain c a L) : ell / 2 ≤ (z.1.1.1 p).1 := by
  have hp := picardBall_lam_lower_of_center_lower z p
    (hl p.1.2 ⟨p.2.1.1.trans p.2.1.2.1, p.2.1.2.2⟩)
  linarith only [hp, hρ, he]

/-- The short-cone ball has S1 gap at least `3/4`, derived from the first
derivative and charged-length bounds. All thresholds are universal and no gap
or higher-derivative bound is assumed. Parameters precede cone and candidates. -/
theorem picardShortConeBall_gap (B ell ρ L₀ e : ℝ) (hB : 1 ≤ B) (he : 0 < ell)
    (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 128) (hρell : ρ ≤ ell / 4)
    (hosc : B * L₀ + 2 * ρ ≤ 1 / 8) (hscale : |e| * (B + 1) ^ 2 * L₀ ≤ 1)
    {c a L : ℝ} (ha : 0 ≤ a) (haL : a ≤ L) (hL : 0 < L) (hLL : L ≤ L₀)
    (datum : ℝ → ℝ × ℂ) (hc : ContDiffOn ℝ 1 datum (Icc c (c + L)))
    (hb : ∀ v ∈ Icc c (c + L),
      ‖datum v‖ ≤ B ∧ ‖derivWithin datum (Icc c (c + L)) v‖ ≤ B)
    (hl : ∀ v ∈ Icc c (c + L), ell ≤ (datum v).1)
    (z : PicardBall datum (picardConeCenterOfContDiff (a := a) datum hL hc) ρ)
    (p : PicardDomain c a L) :
    3 / 4 ≤ 1 - Recon.mu e (picardCandidateLam ha haL z.1)
      (picardCandidateH ha haL z.1) p.1.1 p.1.2 := by
  have hB0 : 0 ≤ B := by linarith only [hB]
  have hU : 0 ≤ B + 1 := by linarith only [hB]
  have hcenter := picardConeCenter_size_le (a := a) datum hL hc hB0 hb
  have hzsize : picardCarrierSize z.1 ≤ B + 1 :=
    (picardBall_size_le hcenter z).trans (by linarith only [hρsmall])
  have hnorm (q : PicardDomain c a L) : ‖z.1.1.1 q‖ ≤ B + 1 :=
    (z.1.1.1.norm_coe_le_norm q).trans ((picardCarrierSize_values_le z.1).trans hzsize)
  have hlow (q : PicardDomain c a L) : ell / 2 ≤ (z.1.1.1 q).1 :=
    picardShortConeBall_lam_lower datum hL hc hρell he hl z q
  have hupp (q : PicardDomain c a L) : (z.1.1.1 q).1 ≤ B + 1 :=
    (le_abs_self _).trans ((norm_fst_le _).trans (hnorm q))
  have hbound (q : PicardDomain c a L) : ‖(z.1.1.1 q).2‖ ≤ B + 1 :=
    (norm_snd_le _).trans (hnorm q)
  have hdist (q r : PicardDomain c a L) :
      ‖(z.1.1.1 q).2 - (z.1.1.1 r).2‖ ≤ B * L + 2 * ρ := by
    have hcent : dist ((picardConeCenterOfContDiff datum hL hc).1.1 q)
        ((picardConeCenterOfContDiff datum hL hc).1.1 r) ≤ B * L :=
      picardConeDatum_oscillation_le hc hB0 (fun v hv => (hb v hv).2)
        ⟨q.2.1.1.trans q.2.1.2.1, q.2.1.2.2⟩
        ⟨r.2.1.1.trans r.2.1.2.1, r.2.1.2.2⟩
    have hh := picardBall_dist_le_of_center_dist_le z q r hcent
    rw [Prod.dist_eq, max_le_iff] at hh
    simpa only [dist_eq_norm] using hh.2
  have hLam (s : ℝ) (hs : s ∈ Icc p.1.1 (c + L)) :
      picardCandidateLam ha haL z.1 p.1.1 s = (z.1.1.1 (picardSectionPoint p s)).1 := by
    simpa only [picardSectionPoint_of_mem p hs] using
      picardCandidateLam_coe ha haL z.1 (picardSectionPoint p s)
  have hH (s : ℝ) (hs : s ∈ Icc p.1.1 (c + L)) :
      picardCandidateH ha haL z.1 p.1.1 s = (z.1.1.1 (picardSectionPoint p s)).2 := by
    simpa only [picardSectionPoint_of_mem p hs] using
      picardCandidateH_coe ha haL z.1 (picardSectionPoint p s)
  rcases lt_or_eq_of_le p.2.1.2.1 with hp | hp
  · have hsTop {s : ℝ} (hs : s ∈ Icc p.1.1 p.1.2) : s ∈ Icc p.1.1 (c + L) :=
      ⟨hs.1, hs.2.trans p.2.1.2.2⟩
    have hcont : Continuous (picardCandidateLam ha haL z.1 p.1.1) :=
      (continuous_picardCandidateLam ha haL z.1).comp (continuous_const.prodMk continuous_id)
    have hcontH : Continuous (picardCandidateH ha haL z.1 p.1.1) :=
      (continuous_picardCandidateH ha haL z.1).comp (continuous_const.prodMk continuous_id)
    have hr : Recon.r (picardCandidateLam ha haL z.1) p.1.1 p.1.2 ≤ (B + 1) * L := by
      have hint := intervalIntegral.integral_mono_on hp.le
        (hcont.intervalIntegrable (μ := volume) _ _)
        (intervalIntegrable_const (μ := volume) (c := B + 1))
        (fun s hs => by rw [hLam s (hsTop hs)]; exact hupp _)
      have hint' : Recon.r (picardCandidateLam ha haL z.1) p.1.1 p.1.2 ≤
          (p.1.2 - p.1.1) * (B + 1) := by
        simpa only [Recon.r_def, intervalIntegral.integral_const, smul_eq_mul] using hint
      have hw : p.1.2 - p.1.1 ≤ L := by linarith only [p.2.1.1, p.2.1.2.2]
      exact hint'.trans ((mul_le_mul_of_nonneg_right hw hU).trans_eq (by ring))
    have hosmall : B * L + 2 * ρ ≤ 1 / 8 :=
      (add_le_add (mul_le_mul_of_nonneg_left hLL hB0) (le_refl (2 * ρ))).trans hosc
    apply Recon.picard_gap_of_oscillation (ℓ := ell / 2) (H := B + 1)
      (ω := B * L + 2 * ρ) hp (by linarith only [he]) hU (by positivity) hosmall
      hcont hcontH
    · intro s hs
      rw [hLam s (hsTop hs)]
      exact hlow _
    · intro s hs
      rw [hH s (hsTop hs)]
      exact hbound _
    · intro s hs t ht
      rw [hH s (hsTop hs), hH t (hsTop ht)]
      exact hdist _ _
    · calc
        _ ≤ (|e| * (B + 1)) * ((B + 1) * L) :=
          mul_le_mul_of_nonneg_left hr (mul_nonneg (abs_nonneg _) hU)
        _ = (|e| * (B + 1) ^ 2) * L := by ring
        _ ≤ (|e| * (B + 1) ^ 2) * L₀ :=
          mul_le_mul_of_nonneg_left hLL (by positivity)
        _ ≤ 1 := hscale
  · norm_num [hp, Recon.mu_def, Recon.m_def, Recon.r_def]

end EmcsfAcExtension.Local
