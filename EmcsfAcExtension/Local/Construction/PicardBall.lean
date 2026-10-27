module

public import EmcsfAcExtension.Local.Construction.PicardGap

/-! # Closed affine balls for incoming Picard iteration

The initial cone is fixed by evaluation equalities. Intersecting this affine
set with a closed ball gives the complete metric space required by Banach's
theorem. Center bounds give positivity and oscillation control; the canonical
small-data assumptions then give the Hawking gap. Invariance under the concrete
radial map remains a separate analytic obligation.

This module supplies function space infrastructure; it closes no graph node.
-/

public section

open Set Metric MeasureTheory

namespace EmcsfAcExtension.Local

variable {c a L : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Candidates agreeing with the prescribed values on the initial cone `u=c`.
No value is prescribed on any later part of the axis. -/
def picardInitialSet (datum : ℝ → E) : Set (PicardCarrier c a L E) :=
  {z | ∀ p : PicardDomain c a L, p.1.1 = c → z.1.1 p = datum p.1.2}

/-- Membership in the initial affine set is exactly equality with the prescribed
cone values; the criterion exposes no condition on future axis values. -/
theorem mem_picardInitialSet_iff (datum : ℝ → E) (z : PicardCarrier c a L E) :
    z ∈ picardInitialSet datum ↔
      ∀ p : PicardDomain c a L, p.1.1 = c → z.1.1 p = datum p.1.2 := Iff.rfl

/-- Fixing cone data is a closed condition in the carrier metric. -/
theorem isClosed_picardInitialSet (datum : ℝ → E) :
    IsClosed (picardInitialSet (c := c) (a := a) (L := L) datum) := by
  simp only [picardInitialSet, ofPred_forall]
  apply isClosed_iInter
  intro p
  apply isClosed_iInter
  intro _
  exact isClosed_eq
    ((continuous_eval_const p).comp (continuous_fst.comp continuous_subtype_val))
    continuous_const

/-- A closed ball in the affine space of candidates with fixed cone data.
The metric uses the maximum of the four sup norms when `E = ℝ × ℂ`. -/
def picardBallSet (datum : ℝ → E) (center : PicardCarrier c a L E) (ρ : ℝ) :
    Set (PicardCarrier c a L E) :=
  picardInitialSet datum ∩ closedBall center ρ

/-- Membership in the closed affine ball is exactly the initial-value
condition and the displayed metric radius. -/
theorem mem_picardBallSet_iff (datum : ℝ → E) (center : PicardCarrier c a L E) (ρ : ℝ)
    (z : PicardCarrier c a L E) :
    z ∈ picardBallSet datum center ρ ↔ z ∈ picardInitialSet datum ∧ dist z center ≤ ρ :=
  Iff.rfl

/-- The candidate ball is closed, for every radius and every prescribed datum. -/
theorem isClosed_picardBallSet (datum : ℝ → E) (center : PicardCarrier c a L E)
    (ρ : ℝ) : IsClosed (picardBallSet datum center ρ) :=
  (isClosed_picardInitialSet datum).inter isClosed_closedBall

/-- The closed affine ball on which a Picard self-map can be restricted. -/
abbrev PicardBall (datum : ℝ → E) (center : PicardCarrier c a L E) (ρ : ℝ) :=
  ↥(picardBallSet datum center ρ)

/-- The affine ball is a complete metric space, without any compactness
assumption on the range. -/
instance picardBallCompleteSpace [CompleteSpace E] (datum : ℝ → E)
    (center : PicardCarrier c a L E) (ρ : ℝ) : CompleteSpace (PicardBall datum center ρ) :=
  (isClosed_picardBallSet datum center ρ).isComplete.completeSpace_coe

/-- A center with the prescribed initial values belongs to every nonnegative
radius ball about itself. -/
theorem picardBall_center_mem {datum : ℝ → E} {center : PicardCarrier c a L E}
    {ρ : ℝ} (hc : center ∈ picardInitialSet datum) (hρ : 0 ≤ ρ) :
    center ∈ picardBallSet datum center ρ :=
  ⟨hc, by simpa using hρ⟩

/-- The affine ball is nonempty once its center has the cone data and the
radius is nonnegative. This is the nonemptiness needed by the fixed point API. -/
theorem picardBall_nonempty {datum : ℝ → E} {center : PicardCarrier c a L E}
    {ρ : ℝ} (hc : center ∈ picardInitialSet datum) (hρ : 0 ≤ ρ) :
    Nonempty (PicardBall datum center ρ) :=
  ⟨⟨center, picardBall_center_mem hc hρ⟩⟩

/-- The constant-in-`u` extension of cone data, with its prescribed outgoing
jet. The derivative assumptions concern only the closed initial interval. -/
@[expose] noncomputable def picardConeCenter [CompleteSpace E] (datum datumV : ℝ → E)
    (hd : ContinuousOn datum (Icc c (c + L)))
    (hdV : ContinuousOn datumV (Icc c (c + L)))
    (hderiv : ∀ v ∈ Ioo c (c + L), HasDerivAt datum (datumV v) v) :
    PicardCarrier c a L E := by
  let values : C(PicardDomain c a L, E) :=
    ⟨fun p => datum p.1.2, hd.comp_continuous
      (continuous_snd.comp continuous_subtype_val)
      (fun p => ⟨p.2.1.1.trans p.2.1.2.1, p.2.1.2.2⟩)⟩
  let jets : C(PicardDomain c a L, E) :=
    ⟨fun p => datumV p.1.2, hdV.comp_continuous
      (continuous_snd.comp continuous_subtype_val)
      (fun p => ⟨p.2.1.1.trans p.2.1.2.1, p.2.1.2.2⟩)⟩
  refine ⟨(values, jets), ?_⟩
  intro p
  have hs : Icc p.1.1 p.1.2 ⊆ Icc c (c + L) :=
    Icc_subset_Icc p.2.1.1 p.2.1.2.2
  have hcV : ContinuousOn datumV (uIcc p.1.1 p.1.2) := by
    simpa only [uIcc_of_le p.2.1.2.1] using hdV.mono hs
  have hi : (∫ s in p.1.1..p.1.2, datumV s) = datum p.1.2 - datum p.1.1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le p.2.1.2.1 (hd.mono hs)
      (fun s hs' => hderiv s
        ⟨p.2.1.1.trans_lt hs'.1, hs'.2.trans_le p.2.1.2.2⟩)
      hcV.intervalIntegrable
  have heq : (∫ s in p.1.1..p.1.2, jets (picardSectionPoint p s)) =
      ∫ s in p.1.1..p.1.2, datumV s := by
    apply intervalIntegral.integral_congr
    intro s hs'
    rw [uIcc_of_le p.2.1.2.1] at hs'
    change datumV (picardSectionPoint p s).1.2 = datumV s
    rw [picardSectionPoint_of_mem p ⟨hs'.1, hs'.2.trans p.2.1.2.2⟩]
  change datum p.1.2 = datum (picardSectionPoint p p.1.1).1.2 +
    ∫ s in p.1.1..p.1.2, jets (picardSectionPoint p s)
  rw [heq, hi, picardSectionPoint_of_mem p
    ⟨le_rfl, p.2.1.2.1.trans p.2.1.2.2⟩]
  simp

/-- The cone center has exactly the prescribed values at every domain point. -/
@[simp] theorem picardConeCenter_value [CompleteSpace E] (datum datumV : ℝ → E)
    (hd : ContinuousOn datum (Icc c (c + L)))
    (hdV : ContinuousOn datumV (Icc c (c + L)))
    (hderiv : ∀ v ∈ Ioo c (c + L), HasDerivAt datum (datumV v) v)
    (p : PicardDomain c a L) :
    (picardConeCenter datum datumV hd hdV hderiv).1.1 p = datum p.1.2 := rfl

/-- The center's outgoing jet is the prescribed cone derivative. -/
@[simp] theorem picardConeCenter_jet [CompleteSpace E] (datum datumV : ℝ → E)
    (hd : ContinuousOn datum (Icc c (c + L)))
    (hdV : ContinuousOn datumV (Icc c (c + L)))
    (hderiv : ∀ v ∈ Ioo c (c + L), HasDerivAt datum (datumV v) v)
    (p : PicardDomain c a L) :
    (picardConeCenter datum datumV hd hdV hderiv).1.2 p = datumV p.1.2 := rfl

/-- Every value in the candidate ball is within `ρ` of the center value.
The numerical evaluation constant one is universal. -/
theorem picardBall_dist_value_le {datum : ℝ → E} {center : PicardCarrier c a L E}
    {ρ : ℝ} (z : PicardBall datum center ρ) (p : PicardDomain c a L) :
    dist (z.1.1.1 p) (center.1.1 p) ≤ ρ :=
  (picardCarrier_dist_value_le z.1 center p).trans z.2.2

/-- A lower expansion bound `ℓ` on the center loses at most the ball radius.
This estimate is uniform in the datum and candidate, with numerical constant one. -/
theorem picardBall_lam_lower_of_center_lower
    {datum : ℝ → ℝ × ℂ} {center : PicardCarrier c a L (ℝ × ℂ)} {ρ ℓ : ℝ}
    (z : PicardBall datum center ρ) (p : PicardDomain c a L)
    (hc : ℓ ≤ (center.1.1 p).1) : ℓ - ρ ≤ (z.1.1.1 p).1 := by
  have h := picardBall_dist_value_le z p
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq] at h
  have hab := (abs_le.mp h.1).1
  linarith

/-- An upper expansion bound `U` on the center increases by at most the radius.
The numerical constant one is universal. -/
theorem picardBall_lam_upper_of_center_upper
    {datum : ℝ → ℝ × ℂ} {center : PicardCarrier c a L (ℝ × ℂ)} {ρ U : ℝ}
    (z : PicardBall datum center ρ) (p : PicardDomain c a L)
    (hc : (center.1.1 p).1 ≤ U) : (z.1.1.1 p).1 ≤ U + ρ := by
  have h := picardBall_dist_value_le z p
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq] at h
  have hab := (abs_le.mp h.1).2
  linarith

/-- An oscillation bound `ω` for the center loses at most twice the radius.
The numerical constant two is universal, uniformly in all domain points. -/
theorem picardBall_dist_le_of_center_dist_le
    {datum : ℝ → E} {center : PicardCarrier c a L E} {ρ ω : ℝ}
    (z : PicardBall datum center ρ) (p q : PicardDomain c a L)
    (hc : dist (center.1.1 p) (center.1.1 q) ≤ ω) :
    dist (z.1.1.1 p) (z.1.1.1 q) ≤ ω + 2 * ρ := by
  have hp := picardBall_dist_value_le z p
  have hq := picardBall_dist_value_le z q
  have ht₁ := dist_triangle (z.1.1.1 p) (center.1.1 p) (z.1.1.1 q)
  have ht₂ := dist_triangle (center.1.1 p) (center.1.1 q) (z.1.1.1 q)
  rw [dist_comm (center.1.1 q) (z.1.1.1 q)] at ht₂
  linarith

/-- A center value bound `B` increases by at most the ball radius.
The numerical constant one is universal. -/
theorem picardBall_norm_value_le_of_center_bound
    {datum : ℝ → E} {center : PicardCarrier c a L E} {ρ B : ℝ}
    (z : PicardBall datum center ρ) (p : PicardDomain c a L)
    (hc : ‖center.1.1 p‖ ≤ B) : ‖z.1.1.1 p‖ ≤ B + ρ := by
  have h := norm_add_le (z.1.1.1 p - center.1.1 p) (center.1.1 p)
  rw [sub_add_cancel, ← dist_eq_norm] at h
  linarith [picardBall_dist_value_le z p]



/-- Every member of the radius-`1/128` ball around the prescribed initial cone
has `1-μ ≥ 3/4`, under the displayed small oscillation and charged-length bounds.
The background parameter is exactly the canonical `M = 1 + ‖h(0)‖ + 10ε` (S2).
All numerical thresholds are universal. The center-value and datum-oscillation
hypotheses must be discharged when constructing the concrete invariant ball. -/
theorem picardBall_gap_of_center_values {a L ε e : ℝ} (ha : 0 ≤ a) (haL : a ≤ L)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 64)
    (h : ℝ → ℂ) (center : PicardCarrier 0 a L (ℝ × ℂ))
    (hcenter : ∀ q : PicardDomain 0 a L, center.1.1 q = (1 / 2, h q.1.2))
    (hosc : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, ‖h s - h t‖ ≤ ε)
    (hscale : |e| * (1 + ‖h 0‖ + 10 * ε) * L ≤ 1 / 16)
    (z : PicardBall (fun v => ((1 / 2 : ℝ), h v)) center (1 / 128))
    (p : PicardDomain 0 a L) :
    3 / 4 ≤ 1 - Recon.mu e (picardCandidateLam ha haL z.1)
      (picardCandidateH ha haL z.1) p.1.1 p.1.2 := by
  let M : ℝ := 1 + ‖h 0‖ + 10 * ε
  have hM : 1 ≤ M := by dsimp [M]; linarith [norm_nonneg (h 0)]
  have hL : 0 ≤ L := ha.trans haL
  have rangeV (q : PicardDomain 0 a L) : q.1.2 ∈ Icc 0 L := by
    constructor <;> linarith [q.2.1.1, q.2.1.2.1, q.2.1.2.2]
  have hd (v : ℝ) (hv : v ∈ Icc 0 L) : ‖h v‖ ≤ M := by
    have ht := norm_add_le (h v - h 0) (h 0)
    rw [sub_add_cancel] at ht
    have ho := hosc v hv 0 ⟨le_rfl, hL⟩
    dsimp [M]
    linarith
  have hc (q : PicardDomain 0 a L) : ‖center.1.1 q‖ ≤ M := by
    rw [hcenter q, Prod.norm_def, max_le_iff]
    exact ⟨by norm_num; linarith, hd q.1.2 (rangeV q)⟩
  have hlow (q : PicardDomain 0 a L) : (1 / 4 : ℝ) ≤ (z.1.1.1 q).1 := by
    have hz := picardBall_lam_lower_of_center_lower (ℓ := 1 / 2) z q (by rw [hcenter q])
    norm_num at hz
    linarith
  have hupp (q : PicardDomain 0 a L) : (z.1.1.1 q).1 ≤ (1 : ℝ) := by
    have hz := picardBall_lam_upper_of_center_upper (U := 1 / 2) z q (by rw [hcenter q])
    norm_num at hz
    linarith
  have hbound (q : PicardDomain 0 a L) : ‖(z.1.1.1 q).2‖ ≤ 2 * M := by
    have hz := picardBall_norm_value_le_of_center_bound z q (hc q)
    exact (norm_snd_le _).trans (hz.trans (by linarith))
  have hdist (q r : PicardDomain 0 a L) :
      ‖(z.1.1.1 q).2 - (z.1.1.1 r).2‖ ≤ ε + 2 * (1 / 128) := by
    have hcent : dist (center.1.1 q) (center.1.1 r) ≤ ε := by
      rw [hcenter q, hcenter r, Prod.dist_eq, dist_self,
        max_eq_right (dist_nonneg : 0 ≤ dist (h q.1.2) (h r.1.2)), dist_eq_norm]
      exact hosc q.1.2 (rangeV q) r.1.2 (rangeV r)
    have hz := picardBall_dist_le_of_center_dist_le z q r hcent
    rw [Prod.dist_eq, max_le_iff] at hz
    simpa only [dist_eq_norm] using hz.2
  have hLam (s : ℝ) (hs : s ∈ Icc p.1.1 (0 + L)) :
      picardCandidateLam ha haL z.1 p.1.1 s = (z.1.1.1 (picardSectionPoint p s)).1 := by
    simpa only [picardSectionPoint_of_mem p hs] using
      picardCandidateLam_coe ha haL z.1 (picardSectionPoint p s)
  have hH (s : ℝ) (hs : s ∈ Icc p.1.1 (0 + L)) :
      picardCandidateH ha haL z.1 p.1.1 s = (z.1.1.1 (picardSectionPoint p s)).2 := by
    simpa only [picardSectionPoint_of_mem p hs] using
      picardCandidateH_coe ha haL z.1 (picardSectionPoint p s)
  rcases lt_or_eq_of_le p.2.1.2.1 with hp | hp
  · have hsTop {s : ℝ} (hs : s ∈ Icc p.1.1 p.1.2) : s ∈ Icc p.1.1 (0 + L) :=
      ⟨hs.1, hs.2.trans p.2.1.2.2⟩
    have hl : ∀ s ∈ Icc p.1.1 p.1.2,
        (1 / 4 : ℝ) ≤ picardCandidateLam ha haL z.1 p.1.1 s := by
      intro s hs
      rw [hLam s (hsTop hs)]
      exact hlow _
    have hh : ∀ s ∈ Icc p.1.1 p.1.2,
        ‖picardCandidateH ha haL z.1 p.1.1 s‖ ≤ 2 * M := by
      intro s hs
      rw [hH s (hsTop hs)]
      exact hbound _
    have ho : ∀ s ∈ Icc p.1.1 p.1.2, ∀ t ∈ Icc p.1.1 p.1.2,
        ‖picardCandidateH ha haL z.1 p.1.1 s - picardCandidateH ha haL z.1 p.1.1 t‖ ≤
          ε + 2 * (1 / 128) := by
      intro s hs t ht
      rw [hH s (hsTop hs), hH t (hsTop ht)]
      exact hdist _ _
    have hcont : Continuous (picardCandidateLam ha haL z.1 p.1.1) :=
      (continuous_picardCandidateLam ha haL z.1).comp (continuous_const.prodMk continuous_id)
    have hcontH : Continuous (picardCandidateH ha haL z.1 p.1.1) :=
      (continuous_picardCandidateH ha haL z.1).comp (continuous_const.prodMk continuous_id)
    have hi : IntervalIntegrable (picardCandidateLam ha haL z.1 p.1.1) volume p.1.1 p.1.2 :=
      hcont.intervalIntegrable _ _
    have hr : Recon.r (picardCandidateLam ha haL z.1) p.1.1 p.1.2 ≤ L := by
      have hi₁ : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume p.1.1 p.1.2 :=
        intervalIntegrable_const
      have hint := intervalIntegral.integral_mono_on hp.le hi hi₁ (fun s hs => by
          rw [hLam s (hsTop hs)]
          exact hupp _)
      have hint' : Recon.r (picardCandidateLam ha haL z.1) p.1.1 p.1.2 ≤ p.1.2 - p.1.1 := by
        simpa [Recon.r_def] using hint
      linarith [p.2.1.1, p.2.1.2.2]
    have hcharged : |e| * (2 * M) * Recon.r (picardCandidateLam ha haL z.1) p.1.1 p.1.2 ≤ 1 := by
      have hmul := mul_le_mul_of_nonneg_left hr (show 0 ≤ |e| * (2 * M) by positivity)
      have heq : |e| * (2 * M) * L = 2 * (|e| * M * L) := by ring
      rw [heq] at hmul
      change |e| * M * L ≤ 1 / 16 at hscale
      linarith
    exact Recon.picard_gap_of_oscillation hp (by norm_num) (by linarith) (by positivity)
      (by linarith) hcont hcontH hl hh ho hcharged
  · norm_num [hp, Recon.mu_def, Recon.m_def, Recon.r_def]

end EmcsfAcExtension.Local
