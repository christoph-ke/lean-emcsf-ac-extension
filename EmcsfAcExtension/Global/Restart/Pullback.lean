module

public import EmcsfAcExtension.Global.Defs.Relabel
public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.Fields.EqOn
import EmcsfAcExtension.Global.Restart.ClassInvariance
import EmcsfAcExtension.Global.Api.Definitions
import EmcsfAcExtension.Global.Restart.Relabel
import EmcsfAcExtension.Local.Api.EqOn

/-! # Pullback and identification in the original gauge

Common labels multiply the three incoming and two outgoing weighted fields by
positive Jacobians. The canonical inverse cancels those factors everywhere.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Restart

/-- [internal] Equality of all primary fields is preserved by common pullback. -/
theorem nullPullback_eqOn {S N : Fields} {D : Set (ℝ × ℝ)}
    (he : S.EqOn N D) (F : ℝ ≃o ℝ) :
    (nullPullback S F F).EqOn (nullPullback N F F)
      {p : ℝ × ℝ | (F p.1, F p.2) ∈ D} := by
  intro p hp
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := he _ hp
  simp only [nullPullback, h1, h2, h3, h4, h5, h6, h7, h8, h9, and_self]

/-- [internal] Pulling back by the canonical inverse and then by the label recovers
all nine original fields, including both expansions and the potential. -/
theorem nullPullback_symm_cancel (S : Fields) (F : ℝ ≃o ℝ) (hF : IsNullRelabel F) :
    nullPullback (nullPullback S F.symm F.symm) F F = S := by
  have hd (t : ℝ) : deriv (F : ℝ → ℝ) t ≠ 0 := ne_of_gt (hF.2.1 t)
  cases S
  dsimp only [nullPullback]
  congr 1 <;> funext u v <;>
    simp [hF.deriv_symm, F.symm_apply_apply, hd]

/-- [internal] Pull back a normalized restart to its exact original-label triangle,
including the zero axis gauge. -/
theorem pullback_restart {e us vp : ℝ} {F : ℝ ≃o ℝ} {N : Fields}
    (hF : IsNullRelabel F) (hz : F us = 0) (hvp : F vp = 2 * F 0)
    (hus : us < vp) (hN : IsSolution e N (triangle 0 (2 * F 0)))
    (hg : ∀ t ∈ Icc 0 (2 * F 0), N.A t t = 0) :
    IsSolution e (nullPullback N F F) (triangle us vp) ∧
      (∀ t ∈ Icc us vp, (nullPullback N F F).A t t = 0) := by
  refine ⟨relabel_class e us vp N F hF hus (by simpa only [hz, hvp] using hN), ?_⟩
  intro t ht
  apply nullPullback_axis_gauge
  apply hg
  exact ⟨by simpa only [hz] using F.monotone ht.1,
    by simpa only [hvp] using F.monotone ht.2⟩

end EmcsfAcExtension.Global.Restart
