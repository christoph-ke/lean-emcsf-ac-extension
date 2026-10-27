module

public import EmcsfAcExtension.Local.Construction.PicardUniformRatios
public import EmcsfAcExtension.Local.Construction.PicardCarrierEstimates

/-! # Complete uniform mass-aspect and charge-square carriers

The normalized ratio profiles retain the linear and cubic outgoing-jet
orders when assembled into complete value and first-jet carriers.
-/

public section

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- The complete mass-aspect and charge-square/radius-square carriers,
in that order. This finite family changes no reconstruction definition. -/
@[expose] noncomputable def picardMuQCarriers (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell : ℝ) (he : 0 < ell) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) : Fin 2 → PicardCarrier c a L ℝ :=
  ![picardMuRecon ha haL e ell he z hl, picardQSquareRecon ha haL e ell he z hl]

private theorem picard_ratio_coordinates_aux (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) :
    picardProfileCoordinate (picardRatioProfiles e ell he z hl) 1 = picardMuValues e ell he z hl ∧
    picardProfileCoordinate (picardRatioProfiles e ell he z hl) 2 = picardMuJetRemainder e ell he z
        hl ∧
    picardProfileCoordinate (picardRatioProfiles e ell he z hl) 4 = picardQSquareValues e ell he z
        hl ∧
    picardProfileCoordinate (picardRatioProfiles e ell he z hl) 5 = picardQSquareJetRemainder e ell
        he z hl := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext p <;>
    simp [picardProfileCoordinate, picardRatioProfiles_apply]

/-- Both complete quotient carriers have a positive uniform C1 size and
comparison constant depending only on `ell,B,R,|e|`, before cone position,
incoming width and every actual cone length at most `R`. -/
theorem picardMuQRecon_uniform (ell B R e : ℝ) (he : 0 < ell) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ (c a L : ℝ) (ha : 0 ≤ a) (haL : a ≤ L), L ≤ R →
      ∀ (z w : PicardCarrier c a L (ℝ × ℂ))
        (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1),
      picardCarrierSize z ≤ B → picardCarrierSize w ≤ B → ∀ i : Fin 2,
      picardCarrierSize (picardMuQCarriers ha haL e ell he z hlz i) ≤ C ∧
      dist (picardMuQCarriers ha haL e ell he z hlz i)
        (picardMuQCarriers ha haL e ell he w hlw i) ≤ C * dist z w := by
  obtain ⟨Q, hQ, hq⟩ := picardRatioProfiles_uniform ell B R e he hB hR
  let C := 1 + Q + R * Q + R ^ 3 * Q
  have hC : 0 < C := by dsimp [C]; positivity
  have hMuC : (R ^ 0 + R ^ 1) * Q ≤ C := by
    have h0 : 0 ≤ R ^ 3 * Q := by positivity
    simp only [pow_zero, pow_one]
    dsimp [C]
    linarith only [h0]
  have hQC : (R ^ 0 + R ^ 3) * Q ≤ C := by
    have h0 : 0 ≤ R * Q := by positivity
    simp only [pow_zero]
    dsimp [C]
    linarith only [h0]
  refine ⟨C, hC, ?_⟩
  intro c a L ha haL hLR z w hlz hlw hz hw i
  obtain ⟨hcoordz1, hcoordz2, hcoordz4, hcoordz5⟩ := picard_ratio_coordinates_aux e ell he z hlz
  obtain ⟨hcoordw1, hcoordw2, hcoordw4, hcoordw5⟩ := picard_ratio_coordinates_aux e ell he w hlw
  obtain ⟨hn, hd⟩ := hq c a L (ha.trans haL) hLR z w hlz hlw hz hw
  have hnMu : ‖picardMuValues e ell he z hlz‖ ≤ Q := by
    rw [←hcoordz1]
    exact (picardProfileCoordinate_norm_le _ 1).trans hn
  have hnMuJ : ‖picardMuJetRemainder e ell he z hlz‖ ≤ Q := by
    rw [←hcoordz2]
    exact (picardProfileCoordinate_norm_le _ 2).trans hn
  have hnQ : ‖picardQSquareValues e ell he z hlz‖ ≤ Q := by
    rw [←hcoordz4]
    exact (picardProfileCoordinate_norm_le _ 4).trans hn
  have hnQJ : ‖picardQSquareJetRemainder e ell he z hlz‖ ≤ Q := by
    rw [←hcoordz5]
    exact (picardProfileCoordinate_norm_le _ 5).trans hn
  have hdMu : dist (picardMuValues e ell he z hlz) (picardMuValues e ell he w hlw) ≤ Q * dist z w :=
      by
    rw [←hcoordz1, ←hcoordw1]
    exact (picardProfileCoordinate_dist_le _ _ 1).trans hd
  have hdMuJ : dist (picardMuJetRemainder e ell he z hlz) (picardMuJetRemainder e ell he w hlw) ≤ Q
      * dist z w := by
    rw [←hcoordz2, ←hcoordw2]
    exact (picardProfileCoordinate_dist_le _ _ 2).trans hd
  have hdQ : dist (picardQSquareValues e ell he z hlz) (picardQSquareValues e ell he w hlw) ≤ Q *
      dist z w := by
    rw [←hcoordz4, ←hcoordw4]
    exact (picardProfileCoordinate_dist_le _ _ 4).trans hd
  have hdQJ : dist (picardQSquareJetRemainder e ell he z hlz) (picardQSquareJetRemainder e ell he w
      hlw) ≤ Q * dist z w := by
    rw [←hcoordz5, ←hcoordw5]
    exact (picardProfileCoordinate_dist_le _ _ 5).trans hd
  fin_cases i <;> simp only [picardMuQCarriers, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · obtain ⟨hn', hd'⟩ := picardCarrier_bounds_of_weighted_profiles R Q (dist z w)
      hR hQ.le dist_nonneg hLR 0 1
      (picardMuRecon ha haL e ell he z hlz) (picardMuRecon ha haL e ell he w hlw)
      (picardMuValues e ell he z hlz) (picardMuValues e ell he w hlw)
      (picardMuJetRemainder e ell he z hlz) (picardMuJetRemainder e ell he w hlw)
      (fun p => by simp only [pow_zero, one_smul]; rfl)
      (fun p => by simp only [pow_zero, one_smul]; rfl)
      (fun p => by simp [picardMuRecon, picardCarrierOfRawDeriv, picardMuJets, smul_eq_mul])
      (fun p => by simp [picardMuRecon, picardCarrierOfRawDeriv, picardMuJets, smul_eq_mul])
      hnMu hnMuJ hdMu hdMuJ
    exact ⟨hn'.trans hMuC, hd'.trans (mul_le_mul_of_nonneg_right hMuC dist_nonneg)⟩
  · obtain ⟨hn', hd'⟩ := picardCarrier_bounds_of_weighted_profiles R Q (dist z w)
      hR hQ.le dist_nonneg hLR 0 3
      (picardQSquareRecon ha haL e ell he z hlz) (picardQSquareRecon ha haL e ell he w hlw)
      (picardQSquareValues e ell he z hlz) (picardQSquareValues e ell he w hlw)
      (picardQSquareJetRemainder e ell he z hlz) (picardQSquareJetRemainder e ell he w hlw)
      (fun p => by simp only [pow_zero, one_smul]; rfl)
      (fun p => by simp only [pow_zero, one_smul]; rfl)
      (fun p =>
          by simp [picardQSquareRecon, picardCarrierOfRawDeriv, picardQSquareJets, smul_eq_mul])
      (fun p =>
          by simp [picardQSquareRecon, picardCarrierOfRawDeriv, picardQSquareJets, smul_eq_mul])
      hnQ hnQJ hdQ hdQJ
    exact ⟨hn'.trans hQC, hd'.trans (mul_le_mul_of_nonneg_right hQC dist_nonneg)⟩

end EmcsfAcExtension.Local
