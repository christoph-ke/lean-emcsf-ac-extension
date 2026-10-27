module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
import EmcsfAcExtension.Local.Construction.WireBall
import EmcsfAcExtension.Local.Construction.WireUniform
import EmcsfAcExtension.Local.Construction.PicardOriginalBall
import EmcsfAcExtension.Local.Construction.PicardContraction

/-! # Discharging the original-cone Picard input

The canonical complete ball is retained in full. The two-sided E3 estimate
chooses its coefficient and incoming width from the bounded first-jet class
before the signed coupling and datum. Smallness uses the actual `datumM`.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- Discharge the original Picard input from the landed canonical carrier
and E3 estimates. The common coefficient and time depend only on `T,E,M,D`,
uniformly over signed couplings with `|e|=E` and the displayed C¹ datum class.
The radius `1/128`, expansion `1/2-1/128` and gap `3/4` are numerical. -/
theorem continuation_original_picard_input : ContinuationOriginalPicardInput := by
  intro T E M D hT _hE hM hD
  let B := M + D + 1 / 128
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨K, hK, C, hC, hest⟩ := picardCarrierUpdate_uniform_abs
    (1 / 4) B T (3 / 4) E (by norm_num) (by norm_num) hB hT.le
  obtain ⟨a, ha, haT, ha1, haK, haC⟩ :=
    picard_exists_pos_time T (1 / 128) K C hT (by norm_num) hK.le hC.le
  have haC' : a * C < 1 := haC.trans_lt (by norm_num)
  refine ⟨C, a, hC, ha, haT, haC', ?_⟩
  intro e h he hdatum hc hd hv hs
  let center := picardOriginalCenter ha.le haT h hT hc
  let Ball := PicardBall (fun v => ((1 / 2 : ℝ), h v)) center (1 / 128)
  have hcval (p : PicardDomain 0 a T) : center.1.1 p = (1 / 2, h p.1.2) := rfl
  have hcjet (p : PicardDomain 0 a T) : center.1.2 p =
      (derivWithin (fun _ : ℝ => (1 / 2 : ℝ)) (Icc 0 (0 + T)) p.1.2,
        derivWithin h (Icc 0 (0 + T)) p.1.2) := by
    simp only [center, picardOriginalCenter_jet, derivWithin_fun_const, Pi.zero_apply, zero_add]
  have hsize : picardCarrierSize center ≤ M + D :=
    picardOriginalCenter_size_le ha.le haT h hT hc hM hD hdatum.le hd
  have hcenterB : picardCarrierSize center ≤ B := hsize.trans (by dsimp only [B]; linarith)
  have hzsize (z : Ball) : picardCarrierSize z.1 ≤ B := picardBall_size_le hsize z
  let hl : ∀ z : Ball, ∀ q, (1 / 4 : ℝ) ≤ (z.1.1.1 q).1 :=
    fun z => picardBall_lam_ge_quarter_of_half_center h center hcval z
  have hraw (z : Ball) (p : PicardDomain 0 a T) :
      (3 / 4 : ℝ) ≤ 1 - Recon.mu e (picardCandidateLam ha.le haT z.1)
        (picardCandidateH ha.le haT z.1) p.1.1 p.1.2 :=
    picardBall_gap_of_datumVar ha.le haT (picardDatumVar_nonneg h T) hv h hc
      le_rfl center hcval hs z p
  let hg : ∀ z : Ball, ∀ q,
      (3 / 4 : ℝ) ≤ 1 - picardMuValues e (1 / 4) (by norm_num) z.1 (hl z) q := by
    intro z q
    rw [picardMuValues_eq_recon ha.le haT]
    exact hraw z q
  have hbounds (z w : Ball) := hest e he 0 a T ha.le haT le_rfl ha1
    center z.1 w.1 (hl z) (hl w) (hg z) (hg w) hcenterB (hzsize z) (hzsize w)
  let F : Ball → Ball := fun z =>
    ⟨picardCarrierUpdate ha.le haT e (1 / 4) (3 / 4) (by norm_num) (by norm_num)
      center z.1 (hl z) (hg z),
      (mem_picardBallSet_iff _ _ _ _).mpr ⟨
      picardCarrierUpdate_mem_initialSet ha.le haT e (1 / 4) (3 / 4)
        (by norm_num) (by norm_num) (picardOriginalCenter_mem_initialSet ha.le haT h hT hc)
        z.1 (hl z) (hg z),
      (hbounds z z).1.trans (by linarith only [haK])⟩⟩
  have hF (z : Ball) (p : PicardDomain 0 a T) : (F z).1.1.1 p =
      (Recon.picardLam e (picardCandidateLam ha.le haT z.1)
        (picardCandidateH ha.le haT z.1) 0 (fun _ => 1 / 2) p.1.1 p.1.2,
       Recon.picardH e (picardCandidateLam ha.le haT z.1)
        (picardCandidateH ha.le haT z.1) 0 h p.1.1 p.1.2) :=
    picardCarrierUpdate_value_of_center_values ha.le haT e (1 / 4) (3 / 4)
      (by norm_num) (by norm_num) center z.1 (hl z) (hg z) (fun _ => 1 / 2) h hcval p
  have hb (z : Ball) (p : PicardDomain 0 a T) :
      (1 / 2 - 1 / 128 : ℝ) ≤ (z.1.1.1 p).1 ∧
        (3 / 4 : ℝ) ≤ 1 - Recon.mu e (picardCandidateLam ha.le haT z.1)
          (picardCandidateH ha.le haT z.1) p.1.1 p.1.2 :=
    ⟨picardBall_lam_lower_of_center_lower z p (by rw [hcval p]), hraw z p⟩
  exact ⟨continuationPicardBall_of_update ha.le haT e (1 / 128)
    (1 / 2 - 1 / 128) (3 / 4) C (fun _ => 1 / 2) h center (by norm_num)
    hcval hcjet F hF hC haC' (fun z w => (hbounds z w).2) hb, le_rfl⟩

end EmcsfAcExtension.Local
