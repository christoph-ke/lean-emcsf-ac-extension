module

public import EmcsfAcExtension.Local.Construction.PicardData
public import EmcsfAcExtension.Local.Construction.PicardMap

/-! # The actual Picard map on the canonical complete ball

The small datum assumptions imply positive expansion and the S1 gap for every
ball member, so the exact carrier map is defined on the entire ball. Its output
lies in the initial affine set. Preservation of the metric ball and contraction
are proved in `PicardOriginalContraction`, using the uniform estimates E3.
This module supplies the canonical map and its domain, without closing a node.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- Every member of the canonical ball has expansion at least `1/4`, with
universal constants and no a priori coefficient-domain assumption. -/
theorem picardBall_lam_ge_quarter_of_half_center {a L : ℝ} (h : ℝ → ℂ)
    (center : PicardCarrier 0 a L (ℝ × ℂ))
    (hc : ∀ q : PicardDomain 0 a L, center.1.1 q = (1 / 2, h q.1.2))
    (z : PicardBall (fun v => ((1 / 2 : ℝ), h v)) center (1 / 128)) (p : PicardDomain 0 a L) :
    (1 / 4 : ℝ) ≤ (z.1.1.1 p).1 := by
  have hz := picardBall_lam_lower_of_center_lower (ℓ := 1 / 2) z p (by rw [hc p])
  norm_num at hz
  linarith

end EmcsfAcExtension.Local
