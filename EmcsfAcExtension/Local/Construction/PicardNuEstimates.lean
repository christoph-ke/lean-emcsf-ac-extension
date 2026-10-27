module

public import EmcsfAcExtension.Local.Construction.PicardGapEstimates
public import EmcsfAcExtension.Local.Construction.PicardOutgoingEstimates
public import EmcsfAcExtension.Local.Construction.PicardIncomingEstimates

/-! # Uniform null-expansion estimates

Axis evaluation and the outgoing exponential give bounds and comparison
for the reconstructed incoming expansion, using only the outgoing first jet.
-/

public section

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- A reconstructed null expansion has the explicit size and comparison
bounds from a size/comparison bound `B` on its outgoing coefficient. Constants
depend only on `U,B,L`, uniformly in cone position and incoming width. -/
theorem picardNuRecon_bounds_of_BValues (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell κ U B : ℝ) (he : 0 < ell) (hκ : 0 < κ) (hU : 0 ≤ U) (hB : 0 ≤ B)
    (z w : PicardCarrier c a L (ℝ × ℂ))
    (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1)
    (hgz : ∀ q, κ ≤ 1 - picardMuValues e ell he z hlz q)
    (hgw : ∀ q, κ ≤ 1 - picardMuValues e ell he w hlw q)
    (hz : ∀ q, |(z.1.1 q).1| ≤ U) (hw : ∀ q, |(w.1.1 q).1| ≤ U)
    (hBz : ‖picardBValues e ell κ he hκ z hlz hgz‖ ≤ B)
    (hBw : ‖picardBValues e ell κ he hκ w hlw hgw‖ ≤ B)
    (hBd : dist (picardBValues e ell κ he hκ z hlz hgz)
      (picardBValues e ell κ he hκ w hlw hgw) ≤ B * dist z w) :
    let S := (1 + L) * B
    let R := Real.exp S * (1 + S)
    picardCarrierSize (picardNuRecon ha haL e ell κ he hκ z hlz hgz) ≤ 2 * U * R ∧
      dist (picardNuRecon ha haL e ell κ he hκ z hlz hgz)
        (picardNuRecon ha haL e ell κ he hκ w hlw hgw) ≤
          2 * (U * R * S + R) * dist z w := by
  let S := (1 + L) * B
  let R := Real.exp S * (1 + S)
  have hL : 0 ≤ L := ha.trans haL
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let F := picardCarrierNeg ha haL (picardAxisLam ha haL z)
  let G := picardCarrierNeg ha haL (picardAxisLam ha haL w)
  let I := picardOutgoing ha haL (picardBValues e ell κ he hκ z hlz hgz)
  let J := picardOutgoing ha haL (picardBValues e ell κ he hκ w hlw hgw)
  have hF : picardCarrierSize F ≤ U := by
    rw [picardCarrierSize_neg]
    exact picardAxisLam_size_le ha haL U hU z hz
  have hG : picardCarrierSize G ≤ U := by
    rw [picardCarrierSize_neg]
    exact picardAxisLam_size_le ha haL U hU w hw
  have hFG : dist F G ≤ dist z w := by
    have heq : dist F G = dist (picardAxisLam ha haL z) (picardAxisLam ha haL w) := by
      change max (dist (-(picardAxisLam ha haL z).1.1) (-(picardAxisLam ha haL w).1.1))
        (dist (-(picardAxisLam ha haL z).1.2) (-(picardAxisLam ha haL w).1.2)) = _
      simp only [dist_neg_neg]
      rfl
    rw [heq]
    exact picardAxisLam_dist_le ha haL z w
  have hI : picardCarrierSize I ≤ S := (picardOutgoing_size_le ha haL _).trans
    (mul_le_mul_of_nonneg_left hBz (by positivity))
  have hJ : picardCarrierSize J ≤ S := (picardOutgoing_size_le ha haL _).trans
    (mul_le_mul_of_nonneg_left hBw (by positivity))
  have hIJ : dist I J ≤ S * dist z w := by
    exact ((picardOutgoing_dist_le ha haL _ _).trans
      (mul_le_mul_of_nonneg_left hBd (by positivity))).trans_eq (by dsimp [S]; ring)
  have hEI : picardCarrierSize (picardCarrierExp ha haL I) ≤ R :=
    picardCarrierExp_size_le_of_size ha haL S hS I hI
  have hEJ : picardCarrierSize (picardCarrierExp ha haL J) ≤ R :=
    picardCarrierExp_size_le_of_size ha haL S hS J hJ
  have hEIJ : dist (picardCarrierExp ha haL I) (picardCarrierExp ha haL J) ≤ R * S * dist z w :=
    ((picardCarrierExp_dist_le_of_size ha haL S hS I J hI hJ).trans
      (mul_le_mul_of_nonneg_left hIJ hR)).trans_eq (by ring)
  refine ⟨?_, ?_⟩
  · exact (picardCarrierSize_mul_le ha haL F (picardCarrierExp ha haL I)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hF (by norm_num)) hEI
        (picardCarrierSize_nonneg _) (by positivity))
  · calc
      _ ≤ 2 * (picardCarrierSize F * dist (picardCarrierExp ha haL I) (picardCarrierExp ha haL J) +
          dist F G * picardCarrierSize (picardCarrierExp ha haL J)) :=
        picardCarrierMul_dist_le ha haL F G _ _
      _ ≤ 2 * (U * (R * S * dist z w) + dist z w * R) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul hF hEIJ dist_nonneg hU)
          (mul_le_mul hFG hEJ (picardCarrierSize_nonneg _) dist_nonneg)) (by norm_num)
      _ = _ := by ring

end EmcsfAcExtension.Local
