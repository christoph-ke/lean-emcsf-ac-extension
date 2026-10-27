module

public import EmcsfAcExtension.Global.Defs.Relabel
public import EmcsfAcExtension.Frozen.OrigDomain
public import EmcsfAcExtension.Frozen.Fields.NormalizedOut

/-! # Reality of the prolonged restart datum

internal project record R4: normalization identifies the pulled-back datum with the old
normalized scalar on a proper cone. The constant extension samples only that
cone, where reality of the scalar and outgoing derivative makes the datum real.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Real

/-- [internal]
The restart datum is real when the original scalar and outgoing weighted
derivative are real. Every sampled point belongs to `origDomain ui`, including
the axis endpoint. The denominator in `Fields.a` is the real-valued field
`S.lam`, so no nonvanishing or solution-class assumption is required (internal project record R4).
-/
theorem restart_datum_im_zero {ui us : ℝ} {S : Fields} {F : ℝ ≃o ℝ}
    (hus : us ∈ Ioo ui 0) (hz : F us = 0) (hL : 0 < F 0)
    (hnorm : ∀ v ∈ Icc 0 (F 0),
      (nullPullback S F.symm F.symm).r 0 v = v / 2 ∧
      (nullPullback S F.symm F.symm).a 0 v = S.a us (F.symm v))
    (hphi : ∀ p ∈ origDomain ui, (S.phi p.1 p.2).im = 0)
    (htheta : ∀ p ∈ origDomain ui, (S.theta p.1 p.2).im = 0) :
    ∀ t ∈ Icc 0 (2 * F 0),
      (extendDatum ((nullPullback S F.symm F.symm).a 0) (F 0) t).im = 0 := by
  intro t ht
  have ht' : min t (F 0) ∈ Icc 0 (F 0) :=
    ⟨le_min ht.1 hL.le, min_le_right _ _⟩
  have hzero : F.symm 0 = us := by rw [← hz, F.symm_apply_apply]
  have hs : F.symm (min t (F 0)) ∈ Icc us 0 := by
    constructor
    · rw [← hzero]
      exact F.symm.monotone ht'.1
    · simpa only [F.symm_apply_apply] using F.symm.monotone ht'.2
  have hp : (us, F.symm (min t (F 0))) ∈ origDomain ui :=
    ⟨hus.1.le, hus.2, hs.1, hs.2⟩
  change ((nullPullback S F.symm F.symm).a 0 (min t (F 0))).im = 0
  rw [(hnorm _ ht').2]
  simp only [Fields.a, Complex.add_im, Complex.div_ofReal_im,
    hphi _ hp, htheta _ hp, zero_div, add_zero]

end EmcsfAcExtension.Global.Real
