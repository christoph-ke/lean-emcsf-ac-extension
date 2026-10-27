module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Relabel
public import EmcsfAcExtension.Frozen.DatumVar
public import EmcsfAcExtension.Local.Defs.Params
import EmcsfAcExtension.Global.Closure.Final
import EmcsfAcExtension.Global.Closure.WireRestart
import EmcsfAcExtension.Global.Restart.Relabel
import EmcsfAcExtension.Global.Restart.Smallness

/-! # Restart smallness for prescribed thresholds

The complete-cone estimate supplies both bounds for any prescribed positive
threshold pair, in particular the witnesses of the sealed local theorem.
The common null normalization and constant prolongation use enlargement Δ = L.
Source: `charged_SF_new_version.tex:L3954–L4168`, `charged_SF_new_version.tex:L4400–L4415`.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Closure

/-- [node sec:charged-closure#restart-smallness]
Every prescribed positive pair of thresholds precedes all original data.
A late complete cone, with its common null normalization retained explicitly,
has an AC constant prolongation meeting both bounds. The charged scale uses
the canonical coefficient 10 and enlarged radius `F 0`. No estimate constant
is introduced; the cone and coordinate may depend on the thresholds and data.
Thus the positive witnesses of `EmcsfAcExtension.restart_charged_local_BV`
can be substituted directly. Source: `charged_SF_new_version.tex:L4166–L4168`, L4407–L4415. -/
theorem restart_smallness_for_any_thresholds (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ (ui e : ℝ) (S : Fields), OriginalData ui e S → SignedTerminalBound ui S →
      ∃ us ∈ Ioo ui 0, ∃ F : ℝ ≃o ℝ, IsNullRelabel F ∧ F us = 0 ∧ 0 < F 0 ∧
        (∀ t ∈ Icc us 0, F t = selectedRelabel S us t) ∧
        (∀ v ∈ Icc 0 (F 0), (nullPullback S F.symm F.symm).r 0 v = v / 2) ∧
        (∀ t ∈ Ici 0, F t = selectedRelabel S us 0 + 2 * S.lam us 0 * t) ∧
        AbsolutelyContinuousOnInterval
          (extendDatum ((nullPullback S F.symm F.symm).a 0) (F 0))
          0 (2 * F 0) ∧
        datumVar (extendDatum ((nullPullback S F.symm F.symm).a 0) (F 0))
          (2 * F 0) ≤ ε ∧
        Local.chargedScale e
          (extendDatum ((nullPullback S F.symm F.symm).a 0) (F 0))
          (2 * F 0) ≤ δ := by
  intro ui e S hold hs
  obtain ⟨us, hus, _hac, hv, hscale⟩ :=
    complete_cone_smallness_of_closure closure_obligations ui e S hold hs
      (min ε δ) (lt_min hε hδ)
  obtain ⟨F, hF, hz, hL, hm, hr, hac, hvar, hd, _hg, _hc⟩ :=
    Restart.null_normalization ui e us S hold hus
  have hvertex : (nullPullback S F.symm F.symm).a 0 0 = S.phi us us := by
    rw [(hd 0 ⟨le_rfl, hL.le⟩).2]
    have hi : F.symm 0 = us := by rw [← hz, F.symm_apply_apply]
    rw [hi]
    exact (hold.solution.axis us ⟨hus.1.le, hus.2, le_rfl, hus.2.le⟩).2.2.2.2.1
  have hlabel : F 0 = 2 * S.r us 0 := hm 0 ⟨hus.2.le, le_rfl⟩
  refine ⟨us, hus, F, hF, hz, hL, hm, (fun v hv => (hd v hv).1), hr, ?_⟩
  exact Restart.restart_smallness_of_cone e ε δ (F 0)
    ((nullPullback S F.symm F.symm).a 0) hε hL hac
    (by rw [hvar]; exact hv.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    (by rw [hvertex, hvar, hlabel]; exact hscale.trans (min_le_right _ _))

end EmcsfAcExtension.Global.Closure
