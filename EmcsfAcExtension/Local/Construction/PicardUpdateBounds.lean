module

public import EmcsfAcExtension.Local.Construction.PicardMap
public import EmcsfAcExtension.Local.Construction.PicardCarrierBounds
import EmcsfAcExtension.Local.Construction.PicardUniformCoefficients
import EmcsfAcExtension.Local.Construction.PicardIncomingEstimates

/-! # The discharged incoming estimates E3

The radial estimates supply every coefficient bound needed by incoming
integration. Both constants are chosen before the actual cone, strip width,
center or candidates; only a fixed upper bound for the cone length is used.
-/

public section

namespace EmcsfAcExtension.Local

/-- The two concrete estimates E3. Positive constants depend only on
`ell,B,R,kappa,|e|`, uniformly in the cone position, actual `L ≤ R`, incoming
width `a ≤ 1`, center and candidates. All radial coefficient bounds are proved
internally. The lower expansion and S1 gap describe their explicit domain. -/
theorem picardCarrierUpdate_uniform (ell B R κ e : ℝ) (he : 0 < ell)
    (hκ : 0 < κ) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ K > 0, ∃ C > 0, ∀ (c a L : ℝ) (ha : 0 ≤ a) (haL : a ≤ L),
      L ≤ R → a ≤ 1 → ∀ (center z w : PicardCarrier c a L (ℝ × ℂ))
        (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1)
        (hgz : ∀ q, κ ≤ 1 - picardMuValues e ell he z hlz q)
        (hgw : ∀ q, κ ≤ 1 - picardMuValues e ell he w hlw q),
      picardCarrierSize center ≤ B → picardCarrierSize z ≤ B → picardCarrierSize w ≤ B →
      dist (picardCarrierUpdate ha haL e ell κ he hκ center z hlz hgz) center ≤ a * K ∧
      dist (picardCarrierUpdate ha haL e ell κ he hκ center z hlz hgz)
        (picardCarrierUpdate ha haL e ell κ he hκ center w hlw hgw) ≤ a * C * dist z w := by
  obtain ⟨S, hS, hs⟩ := picardSourceCarriers_uniform ell B R κ e he hκ hB hR
  obtain ⟨A, hA, hAest⟩ := picardARecon_uniform ell B R κ e he hκ hB hR
  let M := 1 + B + S + A
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hBM : B ≤ M := by dsimp [M]; linarith
  have hSM : S ≤ M := by dsimp [M]; linarith
  have hAM : A ≤ M := by dsimp [M]; linarith
  obtain ⟨K, hK, hdisp⟩ := picardIncomingCarrierUpdate_displacement_of_size e M hM
  obtain ⟨J, hJ, hdist⟩ := picardIncomingCarrierUpdate_lipschitz_of_size e M hM
  refine ⟨K, hK, J * (2 * S + A), by positivity, ?_⟩
  intro c a L ha haL hLR ha1 center z w hlz hlw hgz hgw hc hz hw
  have hsz := hs c a L ha haL hLR z w hlz hlw hgz hgw hz hw
  have hsw := hs c a L ha haL hLR w z hlw hlz hgw hgz hw hz
  have hAz := hAest c a L ha haL hLR z w hlz hlw hgz hgw hz hw
  have hAw := hAest c a L ha haL hLR w z hlw hlz hgw hgz hw hz
  have hGz : picardCarrierSize (picardGRecon ha haL e ell κ he hκ z hlz hgz) ≤ S := by
    simpa [picardRealSourceCarriers] using (hsz 0).1
  have hGw : picardCarrierSize (picardGRecon ha haL e ell κ he hκ w hlw hgw) ≤ S := by
    simpa [picardRealSourceCarriers] using (hsw 0).1
  have hPz : picardCarrierSize (picardPRecon ha haL e ell κ he hκ z hlz hgz) ≤ S := by
    simpa [picardComplexSourceCarriers] using (hsz 1).2.2.1
  have hPw : picardCarrierSize (picardPRecon ha haL e ell κ he hκ w hlw hgw) ≤ S := by
    simpa [picardComplexSourceCarriers] using (hsw 1).2.2.1
  have hdG : dist (picardGRecon ha haL e ell κ he hκ z hlz hgz)
      (picardGRecon ha haL e ell κ he hκ w hlw hgw) ≤ S * dist z w := by
    simpa [picardRealSourceCarriers] using (hsz 0).2.1
  have hdP : dist (picardPRecon ha haL e ell κ he hκ z hlz hgz)
      (picardPRecon ha haL e ell κ he hκ w hlw hgw) ≤ S * dist z w := by
    simpa [picardComplexSourceCarriers] using (hsz 1).2.2.2
  have hsum : dist (picardGRecon ha haL e ell κ he hκ z hlz hgz)
        (picardGRecon ha haL e ell κ he hκ w hlw hgw) +
      dist (picardARecon ha haL e ell κ he hκ z hlz hgz)
        (picardARecon ha haL e ell κ he hκ w hlw hgw) +
      dist (picardPRecon ha haL e ell κ he hκ z hlz hgz)
        (picardPRecon ha haL e ell κ he hκ w hlw hgw) ≤ (2 * S + A) * dist z w := by
    linarith only [hdG, hAz.2, hdP]
  constructor
  · exact hdisp c a L ha haL ha1 center _ _ _ (hc.trans hBM)
      (hGz.trans hSM) (hAz.1.trans hAM) (hPz.trans hSM)
  · exact (hdist c a L ha haL ha1 center _ _ _ _ _ _ (hc.trans hBM)
      (hGz.trans hSM) (hGw.trans hSM) (hAz.1.trans hAM) (hAw.1.trans hAM)
      (hPz.trans hSM) (hPw.trans hSM)).trans
        ((mul_le_mul_of_nonneg_left hsum (mul_nonneg ha hJ.le)).trans_eq (by ring))

end EmcsfAcExtension.Local
