module

public import EmcsfAcExtension.Local.Construction.PicardUniformMass
public import EmcsfAcExtension.Local.Construction.PicardRatioEstimates

/-! # Ratio profiles uniform in the actual cone length

One fixed input ball bounds the normalized rational reconstruction for every
actual length below its prescribed upper length.
-/

public section

namespace EmcsfAcExtension.Local

/-- The normalized mass and charge ratio profiles have a common positive
size and comparison constant depending only on `ell,B,R,|e|`, uniformly in
cone position, incoming width, and all actual lengths `0 ≤ L ≤ R`. -/
theorem picardRatioProfiles_uniform (ell B R e : ℝ) (he : 0 < ell)
    (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ (c a L : ℝ), 0 ≤ L → L ≤ R →
      ∀ (z w : PicardCarrier c a L (ℝ × ℂ))
        (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1),
      picardCarrierSize z ≤ B → picardCarrierSize w ≤ B →
      ‖picardRatioProfiles e ell he z hlz‖ ≤ C ∧
      dist (picardRatioProfiles e ell he z hlz) (picardRatioProfiles e ell he w hlw) ≤ C * dist z w
          := by
  obtain ⟨S, hS, hs⟩ := picardScalarCharge_uniform ell B R e he hB hR
  obtain ⟨M, hM, hm⟩ := picardMass_uniform ell B R e he hB hR
  let P := 1 + R + B + ell⁻¹ + S + M
  have hi : 0 ≤ ell⁻¹ := by positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hRP : R ≤ P := by dsimp [P]; linarith only [hB, hi, hS, hM]
  have hBP : B ≤ P := by dsimp [P]; linarith only [hR, hi, hS, hM]
  have hiP : ell⁻¹ ≤ P := by dsimp [P]; linarith only [hR, hB, hS, hM]
  have hSP : S ≤ P := by dsimp [P]; linarith only [hR, hB, hi, hM]
  have hMP : M ≤ P := by dsimp [P]; linarith only [hR, hB, hi, hS]
  let V := 1 + P + P ^ 2
  let W := 1 + 2 * P ^ 2 + P
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hPV : P ≤ V := by dsimp [V]; linarith only [sq_nonneg P]
  have hP2V : P ^ 2 ≤ V := by dsimp [V]; linarith only [hP]
  have h1W : 1 ≤ W := by dsimp [W]; linarith only [sq_nonneg P, hP]
  have hPW : P ≤ W := by dsimp [W]; linarith only [sq_nonneg P]
  have hP2W : P ^ 2 ≤ W := by dsimp [W]; linarith only [sq_nonneg P, hP]
  have h2P2W : 2 * P ^ 2 ≤ W := by dsimp [W]; linarith only [hP]
  obtain ⟨K, hK, hn, hd⟩ := picard_finite_profile_bound_aux
    picardRatioPolynomial contDiff_picardRatioPolynomial V
  refine ⟨1 + K + K * W, by positivity, ?_⟩
  intro c a L hL hLR z w hlz hlw hz hw
  have hinput (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
      (hz : picardCarrierSize z ≤ B) (p : PicardDomain c a L) :
      ‖picardRatioInput e ell he z hl p‖ ≤ V := by
    obtain ⟨hfn, _, _, _, _, _, hkn, _, hqn, _⟩ := hs c a L hL hLR z z hl hl hz hz
    have hmn := (hm c a L hL hLR z z hl hl hz hz).2.2.1
    have hf : ‖picardScalarRemainder ell he z hl p‖ ≤ P :=
      ((picardScalarRemainder ell he z hl).norm_coe_le_norm p).trans (hfn.trans hSP)
    have hk : |picardChargeKernel e ell he z hl p| ≤ P :=
      ((picardChargeKernel e ell he z hl).norm_coe_le_norm p).trans (hkn.trans hSP)
    have hq : |picardChargeRemainder e ell he z hl p| ≤ P :=
      ((picardChargeRemainder e ell he z hl).norm_coe_le_norm p).trans (hqn.trans hSP)
    have hmass : |picardMassRemainder e ell he z hl p| ≤ P :=
      ((picardMassRemainder e ell he z hl).norm_coe_le_norm p).trans (hmn.trans hMP)
    have hlam : |(z.1.1 p).1| ≤ P :=
      ((picardCarrier_pointwise_bounds_of_size B z hz).1 p).trans hBP
    have hpR := he.trans_le (picardRadialAverage_lower (picardLamValues z) hl p)
    have hRi : |(picardRadialAverage (picardLamValues z) p)⁻¹| ≤ P := by
      rw [abs_of_pos (inv_pos.mpr hpR)]
      exact ((inv_le_inv₀ hpR he).mpr (picardRadialAverage_lower _ hl p)).trans hiP
    have hx : |p.1.2 - p.1.1| ≤ P := by
      rw [abs_of_nonneg (sub_nonneg.mpr p.2.1.2.1)]
      exact (by linarith [p.2.1.1, p.2.1.2.2] : p.1.2 - p.1.1 ≤ L).trans (hLR.trans hRP)
    apply (pi_norm_le_iff_of_nonneg hV).mpr
    intro i
    fin_cases i <;> simp only [picardRatioInput, ContinuousMap.coe_mk,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Real.norm_eq_abs]
    · exact hx.trans hPV
    · exact hlam.trans hPV
    · exact hRi.trans hPV
    · rw [abs_of_nonneg (sq_nonneg _)]
      exact ((sq_le_sq₀ (norm_nonneg _) hP).mpr hf).trans hP2V
    · exact hq.trans hPV
    · exact hk.trans hPV
    · exact hmass.trans hPV
  have hinputdist (p : PicardDomain c a L) :
      dist (picardRatioInput e ell he z hlz p) (picardRatioInput e ell he w hlw p) ≤ W * dist z w :=
          by
    obtain ⟨hfnz, hdf, _, _, _, _, _, hdk, _, hdq⟩ := hs c a L hL hLR z w hlz hlw hz hw
    have hfnw := (hs c a L hL hLR w z hlw hlz hw hz).1
    have hdm := (hm c a L hL hLR z w hlz hlw hz hw).2.2.2.2.2
    have hfz : ‖picardScalarRemainder ell he z hlz p‖ ≤ P :=
      ((picardScalarRemainder ell he z hlz).norm_coe_le_norm p).trans (hfnz.trans hSP)
    have hfw : ‖picardScalarRemainder ell he w hlw p‖ ≤ P :=
      ((picardScalarRemainder ell he w hlw).norm_coe_le_norm p).trans (hfnw.trans hSP)
    have hdfp : ‖picardScalarRemainder ell he z hlz p - picardScalarRemainder ell he w hlw p‖ ≤ P *
        dist z w := by
      simpa only [dist_eq_norm] using (ContinuousMap.dist_apply_le_dist p).trans
        (hdf.trans (mul_le_mul_of_nonneg_right hSP dist_nonneg))
    have hf2 : |‖picardScalarRemainder ell he z hlz p‖ ^ 2 -
        ‖picardScalarRemainder ell he w hlw p‖ ^ 2| ≤ (2 * P ^ 2) * dist z w :=
      ((picard_norm_sq_sub_le_aux P _ _ hfz hfw).trans
        (mul_le_mul_of_nonneg_left hdfp (by positivity))).trans_eq (by ring)
    have hk : |picardChargeKernel e ell he z hlz p - picardChargeKernel e ell he w hlw p| ≤ P * dist
        z w :=
      (ContinuousMap.dist_apply_le_dist p).trans (hdk.trans (mul_le_mul_of_nonneg_right hSP
          dist_nonneg))
    have hq : |picardChargeRemainder e ell he z hlz p - picardChargeRemainder e ell he w hlw p| ≤ P
        * dist z w :=
      (ContinuousMap.dist_apply_le_dist p).trans (hdq.trans (mul_le_mul_of_nonneg_right hSP
          dist_nonneg))
    have hmass : |picardMassRemainder e ell he z hlz p - picardMassRemainder e ell he w hlw p| ≤ P *
        dist z w :=
      (ContinuousMap.dist_apply_le_dist p).trans (hdm.trans (mul_le_mul_of_nonneg_right hMP
          dist_nonneg))
    have hlam : |(z.1.1 p).1 - (w.1.1 p).1| ≤ dist z w :=
      (le_max_left _ _).trans (picardCarrier_dist_value_le z w p)
    have hRS : |picardRadialAverage (picardLamValues z) p - picardRadialAverage (picardLamValues w)
        p| ≤ dist z w :=
      (ContinuousMap.dist_apply_le_dist p).trans
        ((picardRadialAverage_dist_le _ _).trans (picardLamValues_dist_le z w))
    have hRi : |(picardRadialAverage (picardLamValues z) p)⁻¹ -
        (picardRadialAverage (picardLamValues w) p)⁻¹| ≤ P ^ 2 * dist z w :=
      ((picard_inv_sub_le_aux he (picardRadialAverage_lower _ hlz p)
        (picardRadialAverage_lower _ hlw p)).trans (mul_le_mul_of_nonneg_left hRS (sq_nonneg
            _))).trans
          (mul_le_mul_of_nonneg_right ((sq_le_sq₀ hi hP).mpr hiP) dist_nonneg)
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hW dist_nonneg)).mpr
    intro i
    fin_cases i <;> simp only [Pi.sub_apply, picardRatioInput, ContinuousMap.coe_mk,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Real.norm_eq_abs, sub_self, abs_zero]
    · positivity
    · exact hlam.trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h1W (dist_nonneg : 0 ≤ dist z w))
    · exact hRi.trans (mul_le_mul_of_nonneg_right hP2W dist_nonneg)
    · exact hf2.trans (mul_le_mul_of_nonneg_right h2P2W dist_nonneg)
    · exact hq.trans (mul_le_mul_of_nonneg_right hPW dist_nonneg)
    · exact hk.trans (mul_le_mul_of_nonneg_right hPW dist_nonneg)
    · exact hmass.trans (mul_le_mul_of_nonneg_right hPW dist_nonneg)
  refine ⟨?_, ?_⟩
  · apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro p
    exact (hn _ (hinput z hlz hz p)).trans
      (by have hKW := mul_nonneg hK.le hW; linarith only [hKW])
  · apply (ContinuousMap.dist_le (by positivity)).mpr
    intro p
    calc
      _ ≤ K * dist (picardRatioInput e ell he z hlz p) (picardRatioInput e ell he w hlw p) :=
        hd _ _ (hinput z hlz hz p) (hinput w hlw hw p)
      _ ≤ K * (W * dist z w) := mul_le_mul_of_nonneg_left (hinputdist p) hK.le
      _ ≤ (1 + K + K * W) * dist z w := by
        have h0 : 0 ≤ (1 + K) * dist z w := by positivity
        nlinarith only [h0]

end EmcsfAcExtension.Local
