module

public import EmcsfAcExtension.Local.Construction.Defects
import EmcsfAcExtension.Infra.Calculus.DiagonalChain
import EmcsfAcExtension.Local.Calculus.AxisLimits
import EmcsfAcExtension.Local.Calculus.Partials

public import EmcsfAcExtension.Local.Construction.WaveSystemMixed

/-! # Diagonal evaluation of incoming constraint defects

The boundary derivative calculation of internal project record `#defect-axis-values`,
`charged_SF_new_version.tex:L6183–6197`. The incoming constraints are not hypotheses.
The diagonal calculation evaluates the domain derivatives at the axis.
Radial quotient limits then identify the off-axis defect limits as zero.
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Local.Null

private theorem incoming_partial_axis_eq_zero {a b t : ℝ} {f : ℝ → ℝ → ℝ}
    (hab : a < b) (hc : ContDiffOn ℝ 1 (Function.uncurry f) (triangle a b))
    (haxis : ∀ s ∈ Icc a b, f s s = 0)
    (hv : pdV (triangle a b) f t t = 0) (ht : t ∈ Icc a b) :
    pdU (triangle a b) f t t = 0 := by
  have hd := hasDerivWithinAt_diagonal hc ht
  have hz : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ))
      (pdU (triangle a b) f t t + pdV (triangle a b) f t t) (Icc a b) t :=
    hd.congr (fun s hs => (haxis s hs).symm) (haxis t ht).symm
  have heq := hz.derivWithin (uniqueDiffOn_Icc hab t ht)
  have hc0 := (hasDerivWithinAt_const t (Icc a b) (0 : ℝ)).derivWithin
    (uniqueDiffOn_Icc hab t ht)
  rw [hc0] at heq
  simpa only [hv, add_zero] using heq.symm

/-- [node restart-sec-independent-null-construction#defect-axis-values]
The incoming defects tend to zero from off the axis of a nondegenerate
closed triangle (`charged_SF_new_version.tex:L6183–6197`). The hypotheses are first
regularity, regular-axis traces, zero outgoing mass and charge derivatives,
and nonzero outgoing radius derivative and incoming expansion at the axis.
These are supplied by smooth reconstruction and the outgoing constraints.
Neither incoming constraint is used and there are no estimate constants. -/
theorem tendsto_defects_axis_of_outgoing_axis {a b e t : ℝ} {S : Fields}
    (hab : a < b)
    (cr : ContDiffOn ℝ 1 (Function.uncurry S.r) (triangle a b))
    (cQ : ContDiffOn ℝ 1 (Function.uncurry S.Q) (triangle a b))
    (cm : ContDiffOn ℝ 1 (Function.uncurry S.m) (triangle a b))
    (cnu : ContinuousOn (Function.uncurry S.nu) (triangle a b))
    (cphi : ContinuousOn (Function.uncurry S.phi) (triangle a b))
    (cxi : ContinuousOn (Function.uncurry S.xi) (triangle a b))
    (hr : ∀ s ∈ Icc a b, S.r s s = 0)
    (hQ : ∀ s ∈ Icc a b, S.Q s s = 0)
    (hm : ∀ s ∈ Icc a b, S.m s s = 0)
    (hQv : ∀ s ∈ Icc a b, pdV (triangle a b) S.Q s s = 0)
    (hmv : ∀ s ∈ Icc a b, pdV (triangle a b) S.m s s = 0)
    (ht : t ∈ Icc a b) (hrv : pdV (triangle a b) S.r t t ≠ 0)
    (hnu : S.nu t t ≠ 0) (hxi : S.xi t t = 0) :
    Tendsto (Function.uncurry (defectQ e (triangle a b) S))
      (𝓝[triangle a b ∩ {p | p.1 < p.2}] (t, t)) (𝓝 0) ∧
    Tendsto (Function.uncurry (defectM (triangle a b) S))
      (𝓝[triangle a b ∩ {p | p.1 < p.2}] (t, t)) (𝓝 0) := by
  let F := 𝓝[triangle a b ∩ {p : ℝ × ℝ | p.1 < p.2}] (t, t)
  have hp : (t, t) ∈ triangle a b := ⟨ht.1, le_rfl, ht.2⟩
  have hQR : Tendsto (fun p : ℝ × ℝ => S.Q p.1 p.2 / S.r p.1 p.2) F (𝓝 0) := by
    simpa only [hQv t ht, zero_div] using
      tendsto_axis_quotient hab cQ cr hQ hr ht hrv
  have hmR : Tendsto (fun p : ℝ × ℝ => S.m p.1 p.2 / S.r p.1 p.2) F (𝓝 0) := by
    simpa only [hmv t ht, zero_div] using
      tendsto_axis_quotient hab cm cr hm hr ht hrv
  have hmu : Tendsto (Function.uncurry S.mu) F (𝓝 0) := by
    change Tendsto (fun p : ℝ × ℝ => 2 * S.m p.1 p.2 / S.r p.1 p.2) F (𝓝 0)
    simpa only [mul_div_assoc, mul_zero] using hmR.const_mul 2
  have hN : Tendsto (Function.uncurry S.nu) F (𝓝 (S.nu t t)) :=
    (cnu (t, t) hp).mono inter_subset_left
  have hPhi : Tendsto (Function.uncurry S.phi) F (𝓝 (S.phi t t)) :=
    (cphi (t, t) hp).mono inter_subset_left
  have hXi : Tendsto (Function.uncurry S.xi) F (𝓝 0) := by
    have h : Tendsto (Function.uncurry S.xi) F (𝓝 (S.xi t t)) :=
      (cxi (t, t) hp).mono inter_subset_left
    rwa [hxi] at h
  have hR : Tendsto (Function.uncurry S.r) F (𝓝 0) := by
    have h : Tendsto (Function.uncurry S.r) F (𝓝 (S.r t t)) :=
      (cr.continuousOn (t, t) hp).mono inter_subset_left
    rwa [hr t ht] at h
  have hQu : Tendsto (Function.uncurry (pdU (triangle a b) S.Q)) F (𝓝 0) := by
    have h : Tendsto (Function.uncurry (pdU (triangle a b) S.Q)) F
        (𝓝 (pdU (triangle a b) S.Q t t)) :=
      (continuousOn_pdU cQ (uniqueDiffOn_triangle hab) (t, t) hp).mono inter_subset_left
    rwa [incoming_partial_axis_eq_zero hab cQ hQ (hQv t ht) ht] at h
  have hmu' : Tendsto (Function.uncurry (pdU (triangle a b) S.m)) F (𝓝 0) := by
    have h : Tendsto (Function.uncurry (pdU (triangle a b) S.m)) F
        (𝓝 (pdU (triangle a b) S.m t t)) :=
      (continuousOn_pdU cm (uniqueDiffOn_triangle hab) (t, t) hp).mono inter_subset_left
    rwa [incoming_partial_axis_eq_zero hab cm hm (hmv t ht) ht] at h
  have hCurrent := Complex.continuous_im.continuousAt.tendsto.comp
    ((Complex.continuous_conj.continuousAt.tendsto.comp hPhi).mul hXi)
  have hQU : Tendsto (Function.uncurry (S.QU e)) F (𝓝 0) := by
    change Tendsto (fun p : ℝ × ℝ =>
      e * S.r p.1 p.2 * (starRingEnd ℂ (S.phi p.1 p.2) * S.xi p.1 p.2).im) F (𝓝 0)
    simpa only [Function.comp_apply, Function.uncurry, mul_zero, map_zero,
      Complex.zero_im] using (hR.const_mul e).mul hCurrent
  have hD : Tendsto (fun p : ℝ × ℝ => 1 - S.mu p.1 p.2) F (𝓝 1) := by
    simpa only [Function.uncurry, sub_zero] using! tendsto_const_nhds.sub hmu
  have hScalar : Tendsto (fun p : ℝ × ℝ =>
      (1 - S.mu p.1 p.2) * ‖S.xi p.1 p.2‖ ^ 2 / (2 * S.nu p.1 p.2)) F (𝓝 0) := by
    simpa only [Function.uncurry, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      zero_div, Pi.div_apply] using! (hD.mul (hXi.norm.pow 2)).div
        (hN.const_mul 2) (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hnu)
  have hCharge : Tendsto (fun p : ℝ × ℝ =>
      (S.Q p.1 p.2 / S.r p.1 p.2) ^ 2 * S.nu p.1 p.2 / 2) F (𝓝 0) := by
    simpa only [Function.uncurry, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_div]
      using ((hQR.pow 2).mul hN).div_const 2
  have hMU : Tendsto (Function.uncurry S.mU) F (𝓝 0) := by
    have hsum := hScalar.add hCharge
    simp only [add_zero] at hsum
    convert hsum using 1
    · ext p
      dsimp only [Function.uncurry, Fields.mU]
      congr 1
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
  exact ⟨by simpa only [defectQ, Function.uncurry, sub_zero] using! hQu.sub hQU,
    by simpa only [defectM, Function.uncurry, sub_zero] using! hmu'.sub hMU⟩

/-- Zero outgoing axis derivatives and the diagonal chain rule evaluate the
actual incoming defects on every axis point of the construction wedge.
No incoming constraint or second derivative is assumed. -/
theorem defects_axis_values_on_wedge_of_outgoing_axis {a b c e : ℝ} {S : Fields}
    (hac : a < c) (hcb : c ≤ b)
    (cQ : ContDiffOn ℝ 1 (Function.uncurry S.Q) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cm : ContDiffOn ℝ 1 (Function.uncurry S.m) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hQ : ∀ t ∈ Icc a c, S.Q t t = 0) (hm : ∀ t ∈ Icc a c, S.m t t = 0)
    (hQv : ∀ t ∈ Icc a c, pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.Q t t = 0)
    (hmv : ∀ t ∈ Icc a c, pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.m t t = 0)
    (hr : ∀ t ∈ Icc a c, S.r t t = 0) (hxi : ∀ t ∈ Icc a c, S.xi t t = 0) :
    ∀ t ∈ Icc a c,
      defectQ e (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S t t = 0 ∧
        defectM (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S t t = 0 := by
  have hpartial {f : ℝ → ℝ → ℝ}
      (cf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
      (hzero : ∀ t ∈ Icc a c, f t t = 0)
      (hv : ∀ t ∈ Icc a c, pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) f t t = 0)
      (t : ℝ) (ht : t ∈ Icc a c) :
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) f t t = 0 := by
    have hd := hasDerivWithinAt_diagonal_wedge cf hcb ht
    have hz := hd.congr (fun s hs => (hzero s hs).symm) (hzero t ht).symm
    have heq := hz.derivWithin (uniqueDiffOn_Icc hac t ht)
    rw [(hasDerivWithinAt_const t (Icc a c) (0 : ℝ)).derivWithin
      (uniqueDiffOn_Icc hac t ht), hv t ht, add_zero] at heq
    exact heq.symm
  intro t ht
  simp [defectQ, defectM, hpartial cQ hQ hQv t ht, hpartial cm hm hmv t ht,
    Fields.QU, Fields.mU, hr t ht, hxi t ht]


end EmcsfAcExtension.Local.Null
