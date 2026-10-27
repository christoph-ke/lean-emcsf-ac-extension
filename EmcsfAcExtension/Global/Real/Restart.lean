module

public import EmcsfAcExtension.Global.Defs.LocalStatement
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Relabel
import EmcsfAcExtension.Global.Restart.Relabel
import EmcsfAcExtension.Global.Restart.Prolongation
import EmcsfAcExtension.Global.Restart.Smallness
import EmcsfAcExtension.Global.Restart.Placement
import EmcsfAcExtension.Global.Restart.Pullback
import EmcsfAcExtension.Global.Restart.Overlap
import EmcsfAcExtension.Global.Glue.IsSolutionUnion
import EmcsfAcExtension.Local.Api.EqOn

/-! # Joint restart and gluing with the clauses needed for reality

internal project record R4, R6 and Assembly require the normalization, data, full uniqueness
clause and glued-triangle identification for the same restart witness.
The construction below retains those clauses from the existing restart and
gluing proofs (`charged_SF_new_version.tex:L4174`–L4210).
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Real

/-- [internal]
Apply the local theorem once and glue its pullback to the original solution.
Keep the normalization, initial datum, full closed-endpoint uniqueness and
identification of the glued field on the new triangle, all for that witness.
This is the joint construction required by internal project record R4, R6 and Assembly. -/
theorem restart_and_glue_of_cone (hlocal : LocalTheoremStatement)
    (ui e : ℝ) (S : Fields) (hold : OriginalData ui e S)
    (hcone : ∀ η : ℝ, 0 < η → ∃ us ∈ Ioo ui 0,
      AbsolutelyContinuousOnInterval (S.a us) us 0 ∧
      eVariationOn (S.a us) (Icc us 0) ≤ ENNReal.ofReal η ∧
      |e| * (2 * S.r us 0) *
        (1 + ‖S.phi us us‖ + 10 * (eVariationOn (S.a us) (Icc us 0)).toReal) ≤ η) :
    ∃ us ∈ Ioo ui 0, ∃ F : ℝ ≃o ℝ, IsNullRelabel F ∧ F us = 0 ∧ 0 < F 0 ∧
      let old := nullPullback S F.symm F.symm
      let h := extendDatum (old.a 0) (F 0)
      (∀ v ∈ Icc 0 (F 0), old.r 0 v = v / 2 ∧ old.a 0 v = S.a us (F.symm v)) ∧
      ∃ N : Fields, IsSolution e N (triangle 0 (2 * F 0)) ∧
        (∀ t ∈ Icc 0 (2 * F 0), N.A t t = 0) ∧
        (∀ v ∈ Icc 0 (2 * F 0), N.r 0 v = v / 2 ∧ N.a 0 v = h v) ∧
        (∀ T' ∈ Ioc 0 (2 * F 0), ∀ S' : Fields,
          IsSolution e S' (triangle 0 T') →
          (∀ v ∈ Icc 0 T', S'.r 0 v = v / 2 ∧ S'.a 0 v = h v) →
          (∀ t ∈ Icc 0 T', S'.A t t = 0) → S'.EqOn N (triangle 0 T')) ∧
        ∃ vp > 0, F vp = 2 * F 0 ∧ ∃ G : Fields,
          IsSolution e G (origDomain ui ∪ triangle us vp) ∧
          (∀ t ∈ Icc us vp, G.A t t = 0) ∧ G.EqOn S (origDomain ui) ∧
          G.EqOn (nullPullback N F F) (triangle us vp) := by
  obtain ⟨εB, δB, CB, hε, hδ, hC, htheory⟩ := hlocal
  obtain ⟨us, hus, _hac, hv, hscale⟩ := hcone (min εB δB) (lt_min hε hδ)
  obtain ⟨F, hF, hz, hL, hm, _hr, hac, hvar, hd, hg, hc⟩ :=
    Restart.null_normalization ui e us S hold hus
  let old := nullPullback S F.symm F.symm
  have hvertex : old.a 0 0 = S.phi us us := by
    rw [(hd 0 ⟨le_rfl, hL.le⟩).2]
    have hi : F.symm 0 = us := by rw [← hz, F.symm_apply_apply]
    rw [hi]
    exact (hold.solution.axis us ⟨hus.1.le, hus.2, le_rfl, hus.2.le⟩).2.2.2.2.1
  have hlabel : F 0 = 2 * S.r us 0 := hm 0 ⟨hus.2.le, le_rfl⟩
  have hsmall := Restart.restart_smallness_of_cone e εB δB (F 0) (old.a 0) hε hL hac
    (by rw [hvar]; exact hv.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    (by rw [hvertex, hvar, hlabel]; exact hscale.trans (min_le_right _ _))
  have hT : 0 < 2 * F 0 := mul_pos (by norm_num) hL
  obtain ⟨N, hN, hdN, hgN, _haN, _hbN, _haxisN, _hvN, _hpointN,
      _hvoN, _hviN, _hacoN, _haciN, _hregN, _hbvN, huniq⟩ :=
    (htheory (2 * F 0) e hT).1 (extendDatum (old.a 0) (F 0))
      hsmall.1 hsmall.2.1 hsmall.2.2
  have heN : ∀ T' ∈ Ioo 0 (F 0), old.EqOn N (triangle 0 T') := by
    intro T' hT'
    apply huniq T' ⟨hT'.1, by linarith only [hT'.2, hL]⟩ old (hc T' hT')
    · intro v hv'
      have hvL : v ∈ Icc 0 (F 0) := ⟨hv'.1, hv'.2.trans hT'.2.le⟩
      exact ⟨(hd v hvL).1,
        (Restart.extendDatum_eq_of_le (old.a 0) hvL.2).symm⟩
    · intro t ht
      exact hg t ⟨ht.1, ht.2.trans_lt hT'.2⟩
  obtain ⟨vp, hvp, hFvp⟩ := Restart.pullback_endpoint F hL
  have husvp : us < vp := hus.2.trans hvp
  obtain ⟨hP, hgP⟩ := Restart.pullback_restart hF hz hFvp husvp hN hgN
  have he := Restart.overlap_uniqueness_of_restart hvp hold.solution hF hz hL hP heN
  obtain ⟨G, hG, hGo, hGp⟩ := Closure.glue_original_triangle ui e us vp S
    (nullPullback N F F) hold.ui_neg hus hvp hold.solution hP he
  refine ⟨us, hus, F, hF, hz, hL, hd, N, hN, hgN, hdN, huniq,
    vp, hvp, hFvp, G, hG, ?_, hGo, hGp⟩
  intro t ht
  rw [hGp.A (show (t, t) ∈ triangle us vp from ⟨ht.1, le_rfl, ht.2⟩)]
  exact hgP t ht

/-- [internal]
The joint construction retains the entire conclusion of
`Closure.regular_center_continuation_of_cone`. -/
theorem regular_center_continuation_of_joint_restart (hlocal : LocalTheoremStatement)
    (ui e : ℝ) (S : Fields) (hold : OriginalData ui e S)
    (hcone : ∀ η : ℝ, 0 < η → ∃ us ∈ Ioo ui 0,
      AbsolutelyContinuousOnInterval (S.a us) us 0 ∧
      eVariationOn (S.a us) (Icc us 0) ≤ ENNReal.ofReal η ∧
      |e| * (2 * S.r us 0) *
        (1 + ‖S.phi us us‖ + 10 * (eVariationOn (S.a us) (Icc us 0)).toReal) ≤ η) :
    ∃ us vp : ℝ, ∃ S' : Fields, ui < us ∧ us < 0 ∧ 0 < vp ∧
      IsSolution e S' (origDomain ui ∪ triangle us vp) ∧
      (∀ t ∈ Icc us vp, S'.A t t = 0) ∧ S'.EqOn S (origDomain ui) := by
  obtain ⟨us, hus, F, _hF, _hz, _hL, _hd, N, _hN, _hgN, _hdN, _huniq,
      vp, hvp, _hFvp, G, hG, hgG, hGo, _hGp⟩ :=
    restart_and_glue_of_cone hlocal ui e S hold hcone
  exact ⟨us, vp, G, hus.1, hus.2, hvp, hG, hgG, hGo⟩

end EmcsfAcExtension.Global.Real
