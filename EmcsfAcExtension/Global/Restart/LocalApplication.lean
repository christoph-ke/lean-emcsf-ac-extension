module

public import EmcsfAcExtension.Global.Defs.LocalStatement
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Relabel
import EmcsfAcExtension.Global.Restart.Relabel
import EmcsfAcExtension.Global.Restart.Prolongation
import EmcsfAcExtension.Global.Restart.Smallness
import EmcsfAcExtension.Global.Api.Definitions
import EmcsfAcExtension.Global.Restart.ClassInvariance

/-! # Restart using the exact frozen local proposition

The complete-cone conclusions are explicit pending inputs from internal project record. The local
constants are extracted before that cone is selected. Existence and broad
competitor uniqueness are used from the same witness; no provider is imported.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Restart

/-- [internal]
Apply the entire local proposition after selecting a cone smaller than both
local thresholds. The explicit cone hypothesis is exactly internal project record's
`complete_cone_smallness` conclusion (internal project record AC route). The common label is affine
above zero. Equality here is only on proper triangles, before the missing point.
The three universal constants come from `hlocal`, before cone selection. -/
theorem local_restart_of_cone (hlocal : LocalTheoremStatement)
    (ui e : ℝ) (S : Fields) (hold : OriginalData ui e S)
    (hcone : ∀ η : ℝ, 0 < η → ∃ us ∈ Ioo ui 0,
      AbsolutelyContinuousOnInterval (S.a us) us 0 ∧
      eVariationOn (S.a us) (Icc us 0) ≤ ENNReal.ofReal η ∧
      |e| * (2 * S.r us 0) *
        (1 + ‖S.phi us us‖ + 10 * (eVariationOn (S.a us) (Icc us 0)).toReal) ≤ η) :
    ∃ us ∈ Ioo ui 0, ∃ F : ℝ ≃o ℝ, IsNullRelabel F ∧ F us = 0 ∧ 0 < F 0 ∧
      (∀ t ∈ Ici 0, F t = selectedRelabel S us 0 + 2 * S.lam us 0 * t) ∧
      ∃ N : Fields, IsSolution e N (triangle 0 (2 * F 0)) ∧
        (∀ t ∈ Icc 0 (2 * F 0), N.A t t = 0) ∧
        (∀ T' ∈ Ioo 0 (F 0),
          (nullPullback S F.symm F.symm).EqOn N (triangle 0 T')) := by
  obtain ⟨εB, δB, CB, hε, hδ, hC, htheory⟩ := hlocal
  obtain ⟨us, hus, _hac, hv, hscale⟩ := hcone (min εB δB) (lt_min hε hδ)
  obtain ⟨F, hF, hz, hL, hm, hr, hac, hvar, hd, hg, hc⟩ :=
    null_normalization ui e us S hold hus
  let old := nullPullback S F.symm F.symm
  have hvertex : old.a 0 0 = S.phi us us := by
    rw [(hd 0 ⟨le_rfl, hL.le⟩).2]
    have hi : F.symm 0 = us := by rw [← hz, F.symm_apply_apply]
    rw [hi]
    exact (hold.solution.axis us ⟨hus.1.le, hus.2, le_rfl, hus.2.le⟩).2.2.2.2.1
  have hlabel : F 0 = 2 * S.r us 0 := hm 0 ⟨hus.2.le, le_rfl⟩
  have hsmall := restart_smallness_of_cone e εB δB (F 0) (old.a 0) hε hL hac
    (by rw [hvar]; exact hv.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    (by rw [hvertex, hvar, hlabel]; exact hscale.trans (min_le_right _ _))
  have hT : 0 < 2 * F 0 := mul_pos (by norm_num) hL
  obtain ⟨N, hN, _hdN, hgN, _haN, _hbN, _haxisN, _hvN, _hpointN,
      _hvoN, _hviN, _hacoN, _haciN, _hregN, _hbvN, huniq⟩ :=
    (htheory (2 * F 0) e hT).1 (extendDatum (old.a 0) (F 0))
      hsmall.1 hsmall.2.1 hsmall.2.2
  refine ⟨us, hus, F, hF, hz, hL, hr, N, hN, hgN, ?_⟩
  intro T' hT'
  apply huniq T' ⟨hT'.1, by linarith only [hT'.2, hL]⟩ old (hc T' hT')
  · intro v hv'
    have hvL : v ∈ Icc 0 (F 0) := ⟨hv'.1, hv'.2.trans hT'.2.le⟩
    exact ⟨(hd v hvL).1,
      (extendDatum_eq_of_le (old.a 0) hvL.2).symm⟩
  · intro t ht
    exact hg t ⟨ht.1, ht.2.trans_lt hT'.2⟩

end EmcsfAcExtension.Global.Restart
