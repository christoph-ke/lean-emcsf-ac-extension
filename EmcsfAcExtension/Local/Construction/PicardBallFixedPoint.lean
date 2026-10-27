module

public import EmcsfAcExtension.Local.Construction.PicardUpdateBounds
public import EmcsfAcExtension.Local.Construction.PicardContraction

/-! # Restricting the exact update to an invariant ball

This conditional helper isolates the final metric argument. The concrete
original-data and short-cone constructions discharge every displayed bound.
-/

public section

open scoped NNReal

namespace EmcsfAcExtension.Local

/-- Restrict the exact update to the complete affine ball and apply Banach.
This `_of_` helper has explicit quantitative premises; concrete nodes must
derive them. The contraction factor `1/2` is universal. -/
theorem picardBall_exists_fixedPoint_of_update_bounds {c a L e ell κ ρ : ℝ}
    (ha : 0 ≤ a) (haL : a ≤ L) (he : 0 < ell) (hκ : 0 < κ)
    {datum : ℝ → ℝ × ℂ} (center : PicardCarrier c a L (ℝ × ℂ))
    (hc : center ∈ picardInitialSet datum) (hρ : 0 ≤ ρ)
    (hl : ∀ z : PicardBall datum center ρ, ∀ q, ell ≤ (z.1.1.1 q).1)
    (hg : ∀ z : PicardBall datum center ρ, ∀ q,
      κ ≤ 1 - picardMuValues e ell he z.1 (hl z) q)
    (hdisp : ∀ z : PicardBall datum center ρ,
      dist (picardCarrierUpdate ha haL e ell κ he hκ center z.1 (hl z) (hg z)) center ≤ ρ)
    (hlip : ∀ z w : PicardBall datum center ρ,
      dist (picardCarrierUpdate ha haL e ell κ he hκ center z.1 (hl z) (hg z))
        (picardCarrierUpdate ha haL e ell κ he hκ center w.1 (hl w) (hg w)) ≤
          (1 / 2 : ℝ) * dist z w) :
    ∃ F : PicardBall datum center ρ → PicardBall datum center ρ,
      (∀ z, (F z).1 = picardCarrierUpdate ha haL e ell κ he hκ center z.1 (hl z) (hg z)) ∧
      (∀ z w, dist (F z) (F w) ≤ (1 / 2 : ℝ) * dist z w) ∧
      ∃! z, F z = z := by
  let F : PicardBall datum center ρ → PicardBall datum center ρ := fun z =>
    ⟨picardCarrierUpdate ha haL e ell κ he hκ center z.1 (hl z) (hg z), by
      apply (mem_picardBallSet_iff datum center ρ _).mpr
      exact ⟨picardCarrierUpdate_mem_initialSet ha haL e ell κ he hκ hc z.1 (hl z) (hg z),
        hdisp z⟩⟩
  refine ⟨F, fun _ => rfl, hlip, ?_⟩
  exact picard_existsUnique_fixedPoint_of_contracting (q := (1 / 2 : ℝ≥0))
    (by norm_num) hc hρ F hlip

end EmcsfAcExtension.Local
