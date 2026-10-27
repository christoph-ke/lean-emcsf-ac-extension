module

public import EmcsfAcExtension.Local.Construction.PicardOriginalBall
public import EmcsfAcExtension.Local.Construction.PicardBallFixedPoint

/-! # Original-data invariant ball and Banach construction

This is the original-cone part of the invariant-ball node. The later-cone
part is proved separately before the combined node is exported. The datum
has the construction regularity specified by internal project record; no coefficient or ball
estimate is assumed.
-/

public section

open Set
open scoped ENNReal ContDiff

namespace EmcsfAcExtension.Local

/-- The original C¹ datum yields a concrete invariant complete ball,
the exact Picard self-map, a universal contraction factor `1/2`, and its unique
fixed point. The time is chosen after `(T,e,h)` and uses only `T,|e|,datumM h T`
and a first-derivative bound. Thresholds and ball radius are universal. -/
theorem picardOriginalBall_contraction {T e : ℝ} {h : ℝ → ℂ} (hT : 0 < T)
    (hc : ContDiffOn ℝ 1 h (Icc 0 T)) (hv : datumVar h T ≤ 1 / 64)
    (hs : chargedScale e h T ≤ 1 / 32) :
    ∃ (a : ℝ) (ha : 0 < a) (haT : a ≤ T), a ≤ 1 ∧
      let center := picardOriginalCenter ha.le haT h hT hc
      ∃ F : PicardBall (fun v => ((1 / 2 : ℝ), h v)) center (1 / 128) →
          PicardBall (fun v => ((1 / 2 : ℝ), h v)) center (1 / 128),
        (∀ z p, (F z).1.1.1 p =
          picardUpdate ha.le haT e (fun _ => 1 / 2) h z.1 p.1.1 p.1.2) ∧
        (∀ z w, dist (F z) (F w) ≤ (1 / 2 : ℝ) * dist z w) ∧
        (∃! z, F z = z) ∧
        (∀ (z : PicardBall (fun v => ((1 / 2 : ℝ), h v)) center (1 / 128)) p,
          (1 / 4 : ℝ) ≤ (z.1.1.1 p).1 ∧
          (3 / 4 : ℝ) ≤ 1 - Recon.mu e (picardCandidateLam ha.le haT z.1)
            (picardCandidateH ha.le haT z.1) p.1.1 p.1.2) := by
  have hc1 : ContDiffOn ℝ 1 h (Icc 0 T) := hc
  obtain ⟨D, hD, hd⟩ := picardOriginalCenter_uniform_size hT hc1
  let B := D + 1 / 128
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨K, hK, C, hC, hest⟩ := picardCarrierUpdate_uniform
    (1 / 4) B T (3 / 4) e (by norm_num) (by norm_num) hB hT.le
  obtain ⟨a, ha, haT, ha1, haK, haC⟩ :=
    picard_exists_pos_time T (1 / 128) K C hT (by norm_num) hK.le hC.le
  let center := picardOriginalCenter ha.le haT h hT hc1
  have hcenter (p : PicardDomain 0 a T) : center.1.1 p = (1 / 2, h p.1.2) := rfl
  have hcenterSize : picardCarrierSize center ≤ B :=
    (hd a ha.le haT).trans (by dsimp [B]; linarith)
  have hzSize (z : PicardBall (fun v => ((1 / 2 : ℝ), h v)) center (1 / 128)) :
      picardCarrierSize z.1 ≤ B := picardBall_size_le (hd a ha.le haT) z
  let hl : ∀ z : PicardBall (fun v => ((1 / 2 : ℝ), h v)) center (1 / 128),
      ∀ p, (1 / 4 : ℝ) ≤ (z.1.1.1 p).1 :=
    fun z => picardBall_lam_ge_quarter_of_half_center h center hcenter z
  have hscale := picardDatum_scale hs
  have hraw (z : PicardBall (fun v => ((1 / 2 : ℝ), h v)) center (1 / 128))
      (p : PicardDomain 0 a T) :
      (3 / 4 : ℝ) ≤ 1 - Recon.mu e (picardCandidateLam ha.le haT z.1)
        (picardCandidateH ha.le haT z.1) p.1.1 p.1.2 :=
    picardBall_gap_of_datumVar ha.le haT (picardDatumVar_nonneg h T) hv
      h hc1 (le_refl _) center hcenter hscale z p
  let hg : ∀ z : PicardBall (fun v => ((1 / 2 : ℝ), h v)) center (1 / 128),
      ∀ p, (3 / 4 : ℝ) ≤ 1 - picardMuValues e (1 / 4) (by norm_num) z.1 (hl z) p := by
    intro z p
    rw [picardMuValues_eq_recon ha.le haT]
    exact hraw z p
  have hbounds (z w : PicardBall (fun v => ((1 / 2 : ℝ), h v)) center (1 / 128)) :=
    hest 0 a T ha.le haT le_rfl ha1 center z.1 w.1 (hl z) (hl w)
      (hg z) (hg w) hcenterSize (hzSize z) (hzSize w)
  obtain ⟨F, hF, hcon, hfixed⟩ := picardBall_exists_fixedPoint_of_update_bounds
    ha.le haT (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (0 : ℝ) < 3 / 4)
    center (picardOriginalCenter_mem_initialSet ha.le haT h hT hc1)
    (by norm_num : (0 : ℝ) ≤ 1 / 128) hl hg
    (fun z => (hbounds z z).1.trans (by linarith only [haK]))
    (fun z w => (hbounds z w).2.trans
      (mul_le_mul_of_nonneg_right haC dist_nonneg))
  refine ⟨a, ha, haT, ha1, F, ?_, hcon, hfixed, fun z p => ⟨hl z p, hraw z p⟩⟩
  intro z p
  rw [hF z]
  exact picardCarrierUpdate_value_of_center_values ha.le haT e (1 / 4) (3 / 4)
    (by norm_num) (by norm_num) center z.1 (hl z) (hg z)
    (fun _ => 1 / 2) h hcenter p

end EmcsfAcExtension.Local
