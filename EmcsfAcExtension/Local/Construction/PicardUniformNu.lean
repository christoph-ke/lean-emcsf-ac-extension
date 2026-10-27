module

public import EmcsfAcExtension.Local.Construction.PicardUniformGap
public import EmcsfAcExtension.Local.Construction.PicardNuEstimates

/-! # Null-expansion estimates uniform in cone length

The outgoing primitive and exponential bounds are evaluated at a fixed
upper length before the actual cone and both candidates.
-/

public section

namespace EmcsfAcExtension.Local

/-- The reconstructed incoming expansion has a common positive C1 size and
comparison constant depending only on `ell,B,R,κ,|e|`, uniformly in every
cone position, incoming width and actual cone length at most `R`. -/
theorem picardNuRecon_uniform (ell B R κ e : ℝ) (he : 0 < ell)
    (hκ : 0 < κ) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ (c a L : ℝ) (ha : 0 ≤ a) (haL : a ≤ L), L ≤ R →
      ∀ (z w : PicardCarrier c a L (ℝ × ℂ))
        (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1)
        (hgz : ∀ q, κ ≤ 1 - picardMuValues e ell he z hlz q)
        (hgw : ∀ q, κ ≤ 1 - picardMuValues e ell he w hlw q),
      picardCarrierSize z ≤ B → picardCarrierSize w ≤ B →
      picardCarrierSize (picardNuRecon ha haL e ell κ he hκ z hlz hgz) ≤ C ∧
      dist (picardNuRecon ha haL e ell κ he hκ z hlz hgz)
        (picardNuRecon ha haL e ell κ he hκ w hlw hgw) ≤ C * dist z w := by
  obtain ⟨Q, hQ, hq⟩ := picardGapProfiles_uniform ell B R κ e he hκ hB hR
  let S := (1 + R) * Q
  let T := Real.exp S * (1 + S)
  let N := 2 * B * T
  let K := 2 * (B * T * S + T)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨1 + N + K, by positivity, ?_⟩
  intro c a L ha haL hLR z w hlz hlw hgz hgw hz hw
  have hL : 0 ≤ L := ha.trans haL
  have hnz := (hq c a L ha haL hLR z z hlz hlz hgz hgz hz hz).1
  have hnw := (hq c a L ha haL hLR w w hlw hlw hgw hgw hw hw).1
  have hnd := (hq c a L ha haL hLR z w hlz hlw hgz hgw hz hw).2
  have hBz : ‖picardBValues e ell κ he hκ z hlz hgz‖ ≤ Q :=
    (picardProfileCoordinate_norm_le (picardGapProfiles ha haL e ell κ he hκ z hlz hgz) 2).trans hnz
  have hBw : ‖picardBValues e ell κ he hκ w hlw hgw‖ ≤ Q :=
    (picardProfileCoordinate_norm_le (picardGapProfiles ha haL e ell κ he hκ w hlw hgw) 2).trans hnw
  have hBd : dist (picardBValues e ell κ he hκ z hlz hgz)
      (picardBValues e ell κ he hκ w hlw hgw) ≤ Q * dist z w :=
    (picardProfileCoordinate_dist_le (picardGapProfiles ha haL e ell κ he hκ z hlz hgz)
      (picardGapProfiles ha haL e ell κ he hκ w hlw hgw) 2).trans hnd
  have hzl := (picardCarrier_pointwise_bounds_of_size B z hz).1
  have hwl := (picardCarrier_pointwise_bounds_of_size B w hw).1
  obtain ⟨hn, hd⟩ := picardNuRecon_bounds_of_BValues ha haL e ell κ B Q he hκ hB hQ.le
    z w hlz hlw hgz hgw hzl hwl hBz hBw hBd
  have hSL : (1 + L) * Q ≤ S := by dsimp [S]; gcongr
  have hTL : Real.exp ((1 + L) * Q) * (1 + (1 + L) * Q) ≤ T := by
    dsimp [T]
    exact mul_le_mul (Real.exp_le_exp.mpr hSL) (add_le_add (le_refl (1 : ℝ)) hSL)
      (by positivity) (Real.exp_pos S).le
  have hn' : picardCarrierSize (picardNuRecon ha haL e ell κ he hκ z hlz hgz) ≤ N :=
    hn.trans (by dsimp [N]; gcongr)
  have hd' : dist (picardNuRecon ha haL e ell κ he hκ z hlz hgz)
      (picardNuRecon ha haL e ell κ he hκ w hlw hgw) ≤ K * dist z w :=
    hd.trans (mul_le_mul_of_nonneg_right (by dsimp [K]; gcongr) dist_nonneg)
  exact ⟨hn'.trans (by linarith only [hK]),
    hd'.trans (mul_le_mul_of_nonneg_right (by linarith only [hN]) dist_nonneg)⟩

end EmcsfAcExtension.Local
