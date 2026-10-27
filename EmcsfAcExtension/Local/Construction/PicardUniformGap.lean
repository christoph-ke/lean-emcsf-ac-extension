module

public import EmcsfAcExtension.Local.Construction.PicardUniformRatios
public import EmcsfAcExtension.Local.Construction.PicardGapEstimates

/-! # Positive-gap coefficient bounds uniform in cone length

The inverse-gap and z/B estimates use a fixed upper cone length before
the actual domain and candidates.
-/

public section

namespace EmcsfAcExtension.Local

/-- The normalized z, B and inverse-gap profiles have a common positive
size and comparison constant depending only on `ell,B,R,κ,|e|`, uniformly
in cone position, incoming width and every actual length at most `R`. -/
theorem picardGapProfiles_uniform (ell B R κ e : ℝ) (he : 0 < ell)
    (hκ : 0 < κ) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ (c a L : ℝ) (ha : 0 ≤ a) (haL : a ≤ L), L ≤ R →
      ∀ (z w : PicardCarrier c a L (ℝ × ℂ))
        (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1)
        (hgz : ∀ q, κ ≤ 1 - picardMuValues e ell he z hlz q)
        (hgw : ∀ q, κ ≤ 1 - picardMuValues e ell he w hlw q),
      picardCarrierSize z ≤ B → picardCarrierSize w ≤ B →
      ‖picardGapProfiles ha haL e ell κ he hκ z hlz hgz‖ ≤ C ∧
      dist (picardGapProfiles ha haL e ell κ he hκ z hlz hgz)
        (picardGapProfiles ha haL e ell κ he hκ w hlw hgw) ≤ C * dist z w := by
  obtain ⟨Q, hQ, hq⟩ := picardRatioProfiles_uniform ell B R e he hB hR
  let V := 1 + R + B + ell⁻¹ + Q
  let W := 1 + ell⁻¹ ^ 2 + Q
  have hi : 0 ≤ ell⁻¹ := by positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hRV : R ≤ V := by dsimp [V]; linarith only [hB, hi, hQ]
  have hBV : B ≤ V := by dsimp [V]; linarith only [hR, hi, hQ]
  have hiV : ell⁻¹ ≤ V := by dsimp [V]; linarith only [hR, hB, hQ]
  have hQV : Q ≤ V := by dsimp [V]; linarith only [hR, hB, hi]
  have h1W : 1 ≤ W := by dsimp [W]; linarith only [sq_nonneg ell⁻¹, hQ]
  have hiW : ell⁻¹ ^ 2 ≤ W := by dsimp [W]; linarith only [hQ]
  have hQW : Q ≤ W := by dsimp [W]; linarith only [sq_nonneg ell⁻¹]
  obtain ⟨K, hK, hn, hd⟩ := picard_finite_profile_pos_bound_aux
    picardGapPolynomial κ V 10 (contDiffOn_picardGapPolynomial κ hκ)
  refine ⟨1 + K + K * W, by positivity, ?_⟩
  intro c a L ha haL hLR z w hlz hlw hgz hgw hz hw
  have hL : 0 ≤ L := ha.trans haL
  have hinput (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
      (hz : picardCarrierSize z ≤ B) (p : PicardDomain c a L) :
      ‖picardGapInput e ell he z hl p‖ ≤ V := by
    have hcoord (i : Fin 7) : |picardRatioProfiles e ell he z hl p i| ≤ Q :=
      (norm_le_pi_norm _ i).trans (((picardRatioProfiles e ell he z hl).norm_coe_le_norm p).trans
        (hq c a L hL hLR z z hl hl hz hz).1)
    have hx : |p.1.2 - p.1.1| ≤ R := by
      rw [abs_of_nonneg (sub_nonneg.mpr p.2.1.2.1)]
      exact (by linarith [p.2.1.1, p.2.1.2.2] : p.1.2 - p.1.1 ≤ L).trans hLR
    have hpR := he.trans_le (picardRadialAverage_lower (picardLamValues z) hl p)
    have hRi : |(picardRadialAverage (picardLamValues z) p)⁻¹| ≤ ell⁻¹ := by
      rw [abs_of_pos (inv_pos.mpr hpR)]
      exact (inv_le_inv₀ hpR he).mpr (picardRadialAverage_lower _ hl p)
    have hbounds := picardCarrier_pointwise_bounds_of_size B z hz
    apply (pi_norm_le_iff_of_nonneg hV).mpr
    intro i
    fin_cases i <;> simp only [picardGapInput, ContinuousMap.pi_eval,
      Matrix.cons_val_zero', Matrix.cons_val_succ', picardWidth,
      picardLamValues, picardProfileCoordinate, picardRatioInput,
      ContinuousMap.coe_mk, Real.norm_eq_abs]
    · exact hx.trans hRV
    · exact (hbounds.1 p).trans hBV
    · exact (hbounds.2.2.1 p).trans hBV
    · exact hRi.trans hiV
    all_goals exact (hcoord _).trans hQV
  have hinputdist (p : PicardDomain c a L) :
      dist (picardGapInput e ell he z hlz p) (picardGapInput e ell he w hlw p) ≤ W * dist z w := by
    have hlam : |(z.1.1 p).1 - (w.1.1 p).1| ≤ dist z w :=
      (le_max_left _ _).trans (picardCarrier_dist_value_le z w p)
    have hljet : |(z.1.2 p).1 - (w.1.2 p).1| ≤ dist z w :=
      (le_max_left _ _).trans (picardCarrier_dist_jet_le z w p)
    have hRS : |picardRadialAverage (picardLamValues z) p - picardRadialAverage (picardLamValues w)
        p| ≤ dist z w :=
      (ContinuousMap.dist_apply_le_dist p).trans
        ((picardRadialAverage_dist_le _ _).trans (picardLamValues_dist_le z w))
    have hRi : |(picardRadialAverage (picardLamValues z) p)⁻¹ -
        (picardRadialAverage (picardLamValues w) p)⁻¹| ≤ ell⁻¹ ^ 2 * dist z w :=
      (picard_inv_sub_le_aux he (picardRadialAverage_lower _ hlz p)
        (picardRadialAverage_lower _ hlw p)).trans
          (mul_le_mul_of_nonneg_left hRS (sq_nonneg _))
    have hdR (i : Fin 7) : |picardRatioProfiles e ell he z hlz p i -
        picardRatioProfiles e ell he w hlw p i| ≤ Q * dist z w := by
      have h : ‖picardRatioProfiles e ell he z hlz p -
          picardRatioProfiles e ell he w hlw p‖ ≤ Q * dist z w := by
        simpa only [dist_eq_norm] using (ContinuousMap.dist_apply_le_dist p).trans
          (hq c a L hL hLR z w hlz hlw hz hw).2
      exact (norm_le_pi_norm _ i).trans h
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hW dist_nonneg)).mpr
    intro i
    fin_cases i <;> simp only [Pi.sub_apply, picardGapInput, ContinuousMap.pi_eval,
      Matrix.cons_val_zero', Matrix.cons_val_succ', picardWidth, picardLamValues,
      picardProfileCoordinate, picardRatioInput, ContinuousMap.coe_mk,
      Real.norm_eq_abs, sub_self, abs_zero]
    · positivity
    · exact hlam.trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h1W (dist_nonneg : 0 ≤ dist z w))
    · exact hljet.trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h1W (dist_nonneg : 0 ≤ dist z w))
    · exact hRi.trans (mul_le_mul_of_nonneg_right hiW dist_nonneg)
    all_goals exact (hdR _).trans (mul_le_mul_of_nonneg_right hQW dist_nonneg)
  have hginput (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
      (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q) (p : PicardDomain c a L) :
      κ ≤ picardGapInput e ell he z hl p 10 := by
    simpa [picardGapInput, picardProfileCoordinate, picardRatioProfiles_apply] using hg p
  refine ⟨?_, ?_⟩
  · apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro p
    rw [picardGapProfiles_apply]
    exact (hn _ (hinput z hlz hz p) (hginput z hlz hgz p)).trans
      (by have hKW := mul_nonneg hK.le hW; linarith only [hKW])
  · apply (ContinuousMap.dist_le (by positivity)).mpr
    intro p
    rw [picardGapProfiles_apply, picardGapProfiles_apply]
    calc
      _ ≤ K * dist (picardGapInput e ell he z hlz p) (picardGapInput e ell he w hlw p) :=
        hd _ _ (hinput z hlz hz p) (hginput z hlz hgz p)
          (hinput w hlw hw p) (hginput w hlw hgw p)
      _ ≤ K * (W * dist z w) := mul_le_mul_of_nonneg_left (hinputdist p) hK.le
      _ ≤ (1 + K + K * W) * dist z w := by
        have h0 : 0 ≤ (1 + K) * dist z w := by positivity
        nlinarith only [h0]

end EmcsfAcExtension.Local
