module

public import EmcsfAcExtension.Frozen.Fields.EqOn
public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.OrigDomain
public import EmcsfAcExtension.Global.Defs.Relabel
import EmcsfAcExtension.Global.Restart.Pullback
import EmcsfAcExtension.Global.Restart.LastCone
import EmcsfAcExtension.Local.Api.EqOn

/-! # Exhaustion of the proper overlap

The local application's equalities come from the broad uniqueness conjunct of
its very same existence witness. Exhaustion covers `v < L`; the last cone is a
separate continuity argument. The missing apex is outside this statement.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Restart

/-- [internal]
Equalities from uniqueness on each proper triangle identify all nine fields
below the old last cone (`charged_SF_new_version.tex:L4181`–L4205). This helper is consumed
after the local application's frozen broad uniqueness clause. -/
theorem overlap_uniqueness_of_proper {L : ℝ} {S N : Fields} (hL : 0 < L)
    (he : ∀ T' ∈ Ioo 0 L, S.EqOn N (triangle 0 T')) :
    S.EqOn N (triangle 0 L ∩ {p : ℝ × ℝ | p.2 < L}) := by
  intro p hp
  have hv : 0 ≤ p.2 := hp.1.1.trans hp.1.2.1
  have hvL : p.2 < L := hp.2
  have ht : (p.2 + L) / 2 ∈ Ioo 0 L :=
    ⟨by linarith only [hv, hL], by linarith only [hvL]⟩
  exact he _ ht p ⟨hp.1.1, hp.1.2.1, by linarith only [hvL]⟩

/-- [internal]
Proper-triangle uniqueness from the restarted witness identifies every old
point of the overlap, including the old last cone by continuity. The missing
point is never a competitor point (`charged_SF_new_version.tex:L4181`–L4205). -/
theorem overlap_uniqueness_of_restart {ui e us vp : ℝ} {S N : Fields}
    {F : ℝ ≃o ℝ} (hvp : 0 < vp) (hold : IsSolution e S (origDomain ui))
    (hF : IsNullRelabel F) (hz : F us = 0) (hL : 0 < F 0)
    (hP : IsSolution e (nullPullback N F F) (triangle us vp))
    (heN : ∀ T' ∈ Ioo 0 (F 0),
      (nullPullback S F.symm F.symm).EqOn N (triangle 0 T')) :
    (nullPullback N F F).EqOn S (origDomain ui ∩ triangle us vp) := by
  have heproper := overlap_uniqueness_of_proper hL heN
  have hepull := nullPullback_eqOn heproper F
  rw [nullPullback_symm_cancel S F hF] at hepull
  apply eqOn_last_cone_of_lt hvp hold hP
  apply hepull.symm.mono
  intro p hp
  change (F p.1, F p.2) ∈ triangle 0 (F 0) ∩ {q : ℝ × ℝ | q.2 < F 0}
  have hv : F p.2 < F 0 := F.strictMono hp.2
  exact ⟨⟨by simpa only [hz] using F.monotone hp.1.2.1,
    F.monotone hp.1.1.2.2.1, hv.le⟩, hv⟩

end EmcsfAcExtension.Global.Restart
