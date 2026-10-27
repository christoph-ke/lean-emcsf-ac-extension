module

public import EmcsfAcExtension.Local.Construction.PicardBallMap
public import EmcsfAcExtension.Local.Construction.PicardCarrierEstimates
public import EmcsfAcExtension.Local.Defs.Params

/-! # The ball derived from the original datum

The center is the original constant-in-incoming-time datum, with its first
outgoing derivative. All size bounds are chosen after the datum, independently
of the incoming width. The background is exactly `datumM`, as required by S2.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- Total variation is nonnegative, including its frozen real-valued convention. -/
theorem picardDatumVar_nonneg (h : ℝ → ℂ) (T : ℝ) : 0 ≤ datumVar h T :=
  ENNReal.toReal_nonneg

/-- The canonical S2 background dominates one, uniformly in the datum and length. -/
theorem picardDatumM_one_le (h : ℝ → ℂ) (T : ℝ) : 1 ≤ datumM h T := by
  unfold datumM
  linarith only [norm_nonneg (h 0), picardDatumVar_nonneg h T]

/-- The canonical charged scale threshold gives exactly the scale used by
the radius-`1/128` ball. Both numerical constants are universal. -/
theorem picardDatum_scale {T e : ℝ} {h : ℝ → ℂ}
    (hs : chargedScale e h T ≤ 1 / 32) :
    |e| * (1 + ‖h 0‖ + 10 * datumVar h T) * T ≤ 1 / 16 := by
  have heq : |e| * (1 + ‖h 0‖ + 10 * datumVar h T) * T =
      2 * chargedScale e h T := by unfold chargedScale datumM; ring
  rw [heq]
  linarith only [hs]

/-- A C1 datum is bounded by its canonical S2 background. The coefficient
one is universal and the background is never replaced by an adjustable bound. -/
theorem picardDatum_norm_le_M {T : ℝ} {h : ℝ → ℂ} (hT : 0 < T)
    (hc : ContDiffOn ℝ 1 h (Icc 0 T)) {v : ℝ} (hv : v ∈ Icc 0 T) :
    ‖h v‖ ≤ datumM h T := by
  have ho := picardDatum_oscillation_le_of_contDiffOn hc (le_refl (datumVar h T))
    hv (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT.le⟩)
  have hn : ‖h v‖ ≤ ‖h v - h 0‖ + ‖h 0‖ := norm_le_norm_sub_add _ _
  have hε := picardDatumVar_nonneg h T
  unfold datumM
  linarith only [ho, hn, hε]

/-- A finite positive bound for the first derivative is chosen after the C1
datum and interval, uniformly in the outgoing point. No higher derivative enters. -/
theorem picardDatum_exists_jet_bound {T : ℝ} {h : ℝ → ℂ} (hT : 0 < T)
    (hc : ContDiffOn ℝ 1 h (Icc 0 T)) :
    ∃ D > 0, ∀ v ∈ Icc 0 T, ‖derivWithin h (Icc 0 T) v‖ ≤ D := by
  have hd := hc.continuousOn_derivWithin (uniqueDiffOn_Icc hT) (by norm_num)
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hd
  refine ⟨1 + |D|, by positivity, ?_⟩
  intro v hv
  exact (hD v hv).trans (by linarith only [le_abs_self D])

/-- The original center has expansion `1/2` and carries the datum with its
actual first outgoing derivative. It is constant in incoming time. -/
@[expose] noncomputable def picardOriginalCenter {a T : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (h : ℝ → ℂ) (hT : 0 < T) (hc : ContDiffOn ℝ 1 h (Icc 0 T)) :
    PicardCarrier 0 a T (ℝ × ℂ) :=
  picardCarrierPair ha haT (picardCarrierConst (1 / 2 : ℝ))
    (picardConeCenterOfContDiff h hT (by simpa only [zero_add] using hc))

/-- The original center has exactly the prescribed constant-in-time values. -/
@[simp] theorem picardOriginalCenter_value {a T : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (h : ℝ → ℂ) (hT : 0 < T) (hc : ContDiffOn ℝ 1 h (Icc 0 T))
    (p : PicardDomain 0 a T) :
    (picardOriginalCenter ha haT h hT hc).1.1 p = (1 / 2, h p.1.2) := rfl

/-- The original center has zero expansion jet and the actual scalar jet. -/
@[simp] theorem picardOriginalCenter_jet {a T : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (h : ℝ → ℂ) (hT : 0 < T) (hc : ContDiffOn ℝ 1 h (Icc 0 T))
    (p : PicardDomain 0 a T) :
    (picardOriginalCenter ha haT h hT hc).1.2 p =
      (0, derivWithin h (Icc 0 T) p.1.2) := by
  change (0, derivWithin h (Icc 0 (0 + T)) p.1.2) = _
  simp only [zero_add]

/-- The original center lies in the initial affine set, without a condition
on its future axis trace. -/
theorem picardOriginalCenter_mem_initialSet {a T : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (h : ℝ → ℂ) (hT : 0 < T) (hc : ContDiffOn ℝ 1 h (Icc 0 T)) :
    picardOriginalCenter ha haT h hT hc ∈ picardInitialSet (fun v => ((1 / 2 : ℝ), h v)) := by
  apply (mem_picardInitialSet_iff _ _).mpr
  intro p _
  exact picardOriginalCenter_value ha haT h hT hc p

/-- A bound on the canonical background and the first datum derivative
bounds every original center by `H+D`, uniformly in the incoming width.
The parameter `H` only bounds the actual S2 background `datumM h T`. -/
theorem picardOriginalCenter_size_le {a T H D : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (h : ℝ → ℂ) (hT : 0 < T) (hc : ContDiffOn ℝ 1 h (Icc 0 T))
    (hH : 1 ≤ H) (hD : 0 ≤ D) (hM : datumM h T ≤ H)
    (hd : ∀ v ∈ Icc 0 T, ‖derivWithin h (Icc 0 T) v‖ ≤ D) :
    picardCarrierSize (picardOriginalCenter ha haT h hT hc) ≤ H + D := by
  have hHD : 0 ≤ H + D := by linarith only [hH, hD]
  apply picardCarrierSize_le_of_pointwise (H + D) hHD
    (picardOriginalCenter ha haT h hT hc)
  · intro p
    rw [picardOriginalCenter_value, Prod.norm_def]
    apply max_le
    · norm_num
      linarith only [hH, hD]
    · exact ((picardDatum_norm_le_M hT hc
        ⟨p.2.1.1.trans p.2.1.2.1, by simpa only [zero_add] using p.2.1.2.2⟩).trans hM).trans
          (by linarith only [hD])
  · intro p
    rw [picardOriginalCenter_jet, Prod.norm_def, norm_zero]
    apply max_le hHD
    exact (hd p.1.2
      ⟨p.2.1.1.trans p.2.1.2.1, by simpa only [zero_add] using p.2.1.2.2⟩).trans
        (by linarith only [hH])

/-- A C1 datum determines a positive center-size bound before the incoming
width is chosen. It depends only on the datum and `T`, using `datumM` and one
bound for its first derivative; it is uniform in every `0 ≤ a ≤ T`. -/
theorem picardOriginalCenter_uniform_size {T : ℝ} {h : ℝ → ℂ} (hT : 0 < T)
    (hc : ContDiffOn ℝ 1 h (Icc 0 T)) :
    ∃ B > 0, ∀ (a : ℝ) (ha : 0 ≤ a) (haT : a ≤ T),
      picardCarrierSize (picardOriginalCenter ha haT h hT hc) ≤ B := by
  obtain ⟨D, hD, hd⟩ := picardDatum_exists_jet_bound hT hc
  let B := datumM h T + D
  have hM := picardDatumM_one_le h T
  have hB : 0 < B := by dsimp [B]; linarith
  refine ⟨B, hB, ?_⟩
  intro a ha haT
  apply picardCarrierSize_le_of_pointwise B hB.le
    (picardOriginalCenter ha haT h hT hc)
  · intro p
    rw [picardOriginalCenter_value, Prod.norm_def]
    apply max_le
    · norm_num
      dsimp [B]
      linarith
    · exact (picardDatum_norm_le_M hT hc
        ⟨p.2.1.1.trans p.2.1.2.1, by simpa only [zero_add] using p.2.1.2.2⟩).trans
          (by dsimp [B]; linarith)
  · intro p
    rw [picardOriginalCenter_jet, Prod.norm_def, norm_zero]
    exact max_le hB.le ((hd p.1.2
      ⟨p.2.1.1.trans p.2.1.2.1, by simpa only [zero_add] using p.2.1.2.2⟩).trans
        (by dsimp [B]; linarith))

/-- A closed affine ball inherits its center's size bound plus its radius.
The numerical constant one is universal in the datum, range and geometry. -/
theorem picardBall_size_le {c a L ρ B : ℝ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {datum : ℝ → E} {center : PicardCarrier c a L E}
    (hc : picardCarrierSize center ≤ B) (z : PicardBall datum center ρ) :
    picardCarrierSize z.1 ≤ B + ρ := by
  exact (picardCarrierSize_le_dist_add z.1 center).trans (by
    have hz : dist z.1 center ≤ ρ :=
      ((mem_picardBallSet_iff datum center ρ z.1).mp z.2).2
    linarith only [hz, hc])

end EmcsfAcExtension.Local
