module

public import EmcsfAcExtension.Local.Construction.PicardShortConeData
public import EmcsfAcExtension.Local.Construction.PicardBallFixedPoint

/-! # Uniform full-triangle Banach construction E5

The radius and time are chosen before the cone position, length and datum.
Only the first-order data bounds enter, so no higher derivative controls the
continuation time. The map is the literal audited incoming Picard map.
-/

public section

open Set
open scoped ENNReal ContDiff

namespace EmcsfAcExtension.Local

/-- The uniform short-cone construction E5. The positive radius and time
depend only on `B,ell,|e|`, before every cone position, positive actual length
and C¹ datum. All estimates use only the displayed C1 bounds. Every ball
member has `lambda ≥ ell/2` and `1-mu ≥ 3/4`; the exact Picard map contracts
with universal factor `1/2` and has a unique fixed point on the full triangle. -/
theorem picardShortCone_contraction (B ell e : ℝ) (hB : 1 ≤ B) (he : 0 < ell) :
    ∃ ρ > 0, ρ ≤ 1 / 128 ∧ ρ ≤ ell / 4 ∧ ∃ τ > 0, τ ≤ 1 ∧
      ∀ (c L : ℝ) (hL : 0 < L), L ≤ τ →
      ∀ (datum : ℝ → ℝ × ℂ) (hc : ContDiffOn ℝ 1 datum (Icc c (c + L))),
      (∀ v ∈ Icc c (c + L),
        ‖datum v‖ ≤ B ∧ ‖derivWithin datum (Icc c (c + L)) v‖ ≤ B) →
      (∀ v ∈ Icc c (c + L), ell ≤ (datum v).1) →
      let center := picardConeCenterOfContDiff (a := L) datum hL hc
      ∃ F : PicardBall datum center ρ → PicardBall datum center ρ,
        (∀ z p, (F z).1.1.1 p = picardUpdate hL.le le_rfl e
          (fun v => (datum v).1) (fun v => (datum v).2) z.1 p.1.1 p.1.2) ∧
        (∀ z w, dist (F z) (F w) ≤ (1 / 2 : ℝ) * dist z w) ∧
        (∃! z, F z = z) ∧
        (∀ (z : PicardBall datum center ρ) p, ell / 2 ≤ (z.1.1.1 p).1 ∧
          (3 / 4 : ℝ) ≤ 1 - Recon.mu e (picardCandidateLam hL.le le_rfl z.1)
            (picardCandidateH hL.le le_rfl z.1) p.1.1 p.1.2) := by
  obtain ⟨ρ, hρ, hρsmall, hρell, L₀, hL₀, hLone, hosc, hscale⟩ :=
    picardShortCone_exists_cap B ell e hB he
  have hB0 : 0 ≤ B := by linarith only [hB]
  have hU : 0 ≤ B + 1 := by linarith only [hB]
  have hell : 0 < ell / 2 := by linarith only [he]
  obtain ⟨K, hK, C, hC, hest⟩ := picardCarrierUpdate_uniform
    (ell / 2) (B + 1) L₀ (3 / 4) e hell (by norm_num) hU hL₀.le
  obtain ⟨τ, hτ, hτL, hτone, hτK, hτC⟩ :=
    picard_exists_pos_time L₀ ρ K C hL₀ hρ hK.le hC.le
  refine ⟨ρ, hρ, hρsmall, hρell, τ, hτ, hτone, ?_⟩
  intro c L hL hLτ datum hc hb hldatum
  have hc1 : ContDiffOn ℝ 1 datum (Icc c (c + L)) := hc
  let center := picardConeCenterOfContDiff (a := L) datum hL hc1
  have hcenter (p : PicardDomain c L L) :
      center.1.1 p = ((datum p.1.2).1, (datum p.1.2).2) := rfl
  have hcenterB : picardCarrierSize center ≤ B := picardConeCenter_size_le datum hL hc1 hB0 hb
  have hcenterU : picardCarrierSize center ≤ B + 1 := hcenterB.trans (by linarith)
  have hzSize (z : PicardBall datum center ρ) : picardCarrierSize z.1 ≤ B + 1 :=
    (picardBall_size_le hcenterB z).trans (by linarith only [hρsmall])
  let hl : ∀ z : PicardBall datum center ρ, ∀ p, ell / 2 ≤ (z.1.1.1 p).1 :=
    fun z => picardShortConeBall_lam_lower datum hL hc1 hρell he hldatum z
  have hraw (z : PicardBall datum center ρ) (p : PicardDomain c L L) :
      (3 / 4 : ℝ) ≤ 1 - Recon.mu e (picardCandidateLam hL.le le_rfl z.1)
        (picardCandidateH hL.le le_rfl z.1) p.1.1 p.1.2 :=
    picardShortConeBall_gap B ell ρ L₀ e hB he hρ.le hρsmall hρell hosc hscale
      hL.le le_rfl hL (hLτ.trans hτL) datum hc1 hb hldatum z p
  let hg : ∀ z : PicardBall datum center ρ, ∀ p,
      (3 / 4 : ℝ) ≤ 1 - picardMuValues e (ell / 2) hell z.1 (hl z) p := by
    intro z p
    rw [picardMuValues_eq_recon hL.le le_rfl]
    exact hraw z p
  have hbounds (z w : PicardBall datum center ρ) :=
    hest c L L hL.le le_rfl (hLτ.trans hτL) (hLτ.trans hτone)
      center z.1 w.1 (hl z) (hl w) (hg z) (hg w) hcenterU (hzSize z) (hzSize w)
  have hLK : L * K ≤ ρ :=
    ((mul_le_mul_of_nonneg_right hLτ hK.le).trans hτK).trans (by linarith only [hρ])
  have hLC : L * C ≤ 1 / 2 := (mul_le_mul_of_nonneg_right hLτ hC.le).trans hτC
  obtain ⟨F, hF, hcon, hfixed⟩ := picardBall_exists_fixedPoint_of_update_bounds
    hL.le le_rfl hell (by norm_num : (0 : ℝ) < 3 / 4)
    center (picardConeCenterOfContDiff_mem_initialSet datum hL hc1) hρ.le hl hg
    (fun z => (hbounds z z).1.trans hLK)
    (fun z w => (hbounds z w).2.trans (mul_le_mul_of_nonneg_right hLC dist_nonneg))
  refine ⟨F, ?_, hcon, hfixed, fun z p => ⟨hl z p, hraw z p⟩⟩
  intro z p
  rw [hF z]
  exact picardCarrierUpdate_value_of_center_values hL.le le_rfl e (ell / 2) (3 / 4)
    hell (by norm_num) center z.1 (hl z) (hg z)
    (fun v => (datum v).1) (fun v => (datum v).2) hcenter p

end EmcsfAcExtension.Local
