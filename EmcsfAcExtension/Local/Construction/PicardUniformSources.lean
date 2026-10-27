module

public import EmcsfAcExtension.Local.Construction.PicardUniformNu
public import EmcsfAcExtension.Local.Construction.PicardSourceProfiles
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Incoming-source estimates uniform in cone length

The exact weighted source formulas act on a fixed finite dimensional input
ball for every cone below the prescribed upper length.
-/

public section

namespace EmcsfAcExtension.Local

/-- The values and outgoing first jets of `G,C_A,W,P` have a common positive
size and comparison constant depending only on `ell,B,R,κ,|e|`, uniformly
in cone position, incoming width and every actual length at most `R`. -/
theorem picardSourceProfiles_uniform (ell B R κ e : ℝ) (he : 0 < ell)
    (hκ : 0 < κ) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ (c a L : ℝ) (ha : 0 ≤ a) (haL : a ≤ L), L ≤ R →
      ∀ (z w : PicardCarrier c a L (ℝ × ℂ))
        (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1)
        (hgz : ∀ q, κ ≤ 1 - picardMuValues e ell he z hlz q)
        (hgw : ∀ q, κ ≤ 1 - picardMuValues e ell he w hlw q),
      picardCarrierSize z ≤ B → picardCarrierSize w ≤ B →
      ‖picardSourceProfiles ha haL e ell κ he hκ z hlz hgz‖ ≤ C ∧
      dist (picardSourceProfiles ha haL e ell κ he hκ z hlz hgz)
        (picardSourceProfiles ha haL e ell κ he hκ w hlw hgw) ≤ C * dist z w := by
  obtain ⟨S, hS, hs⟩ := picardScalarCharge_uniform ell B R e he hB hR
  obtain ⟨Q, hQ, hq⟩ := picardGapProfiles_uniform ell B R κ e he hκ hB hR
  obtain ⟨N, hN, hn⟩ := picardNuRecon_uniform ell B R κ e he hκ hB hR
  let V := 1 + R + B + ell⁻¹ + S + Q + N
  let W := 1 + ell⁻¹ ^ 2 + S + Q + N
  have hi : 0 ≤ ell⁻¹ := by positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hRV : R ≤ V := by dsimp [V]; linarith only [hB, hi, hS, hQ, hN]
  have hBV : B ≤ V := by dsimp [V]; linarith only [hR, hi, hS, hQ, hN]
  have hiV : ell⁻¹ ≤ V := by dsimp [V]; linarith only [hR, hB, hS, hQ, hN]
  have hSV : S ≤ V := by dsimp [V]; linarith only [hR, hB, hi, hQ, hN]
  have hQV : Q ≤ V := by dsimp [V]; linarith only [hR, hB, hi, hS, hN]
  have hNV : N ≤ V := by dsimp [V]; linarith only [hR, hB, hi, hS, hQ]
  have h1W : 1 ≤ W := by dsimp [W]; linarith only [sq_nonneg ell⁻¹, hS, hQ, hN]
  have hiW : ell⁻¹ ^ 2 ≤ W := by dsimp [W]; linarith only [hS, hQ, hN]
  have hSW : S ≤ W := by dsimp [W]; linarith only [sq_nonneg ell⁻¹, hQ, hN]
  have hQW : Q ≤ W := by dsimp [W]; linarith only [sq_nonneg ell⁻¹, hS, hN]
  have hNW : N ≤ W := by dsimp [W]; linarith only [sq_nonneg ell⁻¹, hS, hQ]
  obtain ⟨K, hK, hpolyN, hpolyD⟩ := picard_finite_profile_bound_aux
    picardUniversalSourcePolynomial contDiff_picardUniversalSourcePolynomial (|e| + V)
  refine ⟨1 + K + K * W, by positivity, ?_⟩
  intro c a L ha haL hLR z w hlz hlw hgz hgw hz hw
  have hL : 0 ≤ L := ha.trans haL
  have hinput (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
      (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q)
      (hz : picardCarrierSize z ≤ B) (p : PicardDomain c a L) :
      ‖picardSourceInput ha haL e ell κ he hκ z hl hg p‖ ≤ V := by
    obtain ⟨hfn, _, hvn, _, hjn, _, hkn, _, hqn, _⟩ := hs c a L hL hLR z z hl hl hz hz
    have hf := ((picardScalarRemainder ell he z hl).norm_coe_le_norm p).trans hfn
    have hphi := ((picardPhiValues ell he z hl).norm_coe_le_norm p).trans hvn
    have hphij := ((picardPhiJets ell he z hl).norm_coe_le_norm p).trans hjn
    have hk := ((picardChargeKernel e ell he z hl).norm_coe_le_norm p).trans hkn
    have hcharge := ((picardChargeRemainder e ell he z hl).norm_coe_le_norm p).trans hqn
    have hgap (i : Fin 9) : |picardGapProfiles ha haL e ell κ he hκ z hl hg p i| ≤ Q :=
      (norm_le_pi_norm _ i).trans (((picardGapProfiles ha haL e ell κ he hκ z hl
          hg).norm_coe_le_norm p).trans
        (hq c a L ha haL hLR z z hl hl hg hg hz hz).1)
    have hnu := (hn c a L ha haL hLR z z hl hl hg hg hz hz).1
    have hnuv := ((picardNuRecon ha haL e ell κ he hκ z hl hg).1.1.norm_coe_le_norm p).trans
      ((picardCarrierSize_values_le _).trans hnu)
    have hnuj := ((picardNuRecon ha haL e ell κ he hκ z hl hg).1.2.norm_coe_le_norm p).trans
      ((picardCarrierSize_jets_le _).trans hnu)
    have hb := picardCarrier_pointwise_bounds_of_size B z hz
    have hx : |p.1.2 - p.1.1| ≤ R := by
      rw [abs_of_nonneg (sub_nonneg.mpr p.2.1.2.1)]
      exact (by linarith [p.2.1.1, p.2.1.2.2] : p.1.2 - p.1.1 ≤ L).trans hLR
    have hpR := he.trans_le (picardRadialAverage_lower (picardLamValues z) hl p)
    have hRi : |(picardRadialAverage (picardLamValues z) p)⁻¹| ≤ ell⁻¹ := by
      rw [abs_of_pos (inv_pos.mpr hpR)]
      exact (inv_le_inv₀ hpR he).mpr (picardRadialAverage_lower _ hl p)
    change max ‖(picardSourceInput ha haL e ell κ he hκ z hl hg p).1‖
      ‖(picardSourceInput ha haL e ell κ he hκ z hl hg p).2‖ ≤ V
    apply max_le
    · apply (pi_norm_le_iff_of_nonneg hV).mpr
      intro i
      fin_cases i <;> simp only [picardSourceInput, ContinuousMap.prod_eval,
        ContinuousMap.pi_eval, Matrix.cons_val_zero', Matrix.cons_val_succ',
        picardProfileCoordinate, picardRatioInput, picardWidth, picardLamValues,
        ContinuousMap.coe_mk, Real.norm_eq_abs]
      · exact hx.trans hRV
      · exact (hb.1 p).trans hBV
      · exact (hb.2.2.1 p).trans hBV
      · exact hRi.trans hiV
      · exact (hgap 4).trans hQV
      · exact (hgap 5).trans hQV
      · exact (hgap 0).trans hQV
      · exact (hgap 1).trans hQV
      · exact hcharge.trans hSV
      · exact hk.trans hSV
      · exact hnuv.trans hNV
      · exact hnuj.trans hNV
    · apply (pi_norm_le_iff_of_nonneg hV).mpr
      intro i
      fin_cases i <;> simp only [picardSourceInput, ContinuousMap.prod_eval,
        ContinuousMap.pi_eval, Matrix.cons_val_zero', Matrix.cons_val_succ',
        picardHJets, ContinuousMap.coe_mk]
      · exact hf.trans hSV
      · exact (hb.2.2.2 p).trans hBV
      · exact hphi.trans hSV
      · exact hphij.trans hSV
  have hinputdist (p : PicardDomain c a L) :
      dist (picardSourceInput ha haL e ell κ he hκ z hlz hgz p)
        (picardSourceInput ha haL e ell κ he hκ w hlw hgw p) ≤ W * dist z w := by
    obtain ⟨_, hfd, _, hvd, _, hjd, _, hkd, _, hqd⟩ := hs c a L hL hLR z w hlz hlw hz hw
    have hf : ‖picardScalarRemainder ell he z hlz p - picardScalarRemainder ell he w hlw p‖ ≤ S *
        dist z w := by
      simpa only [dist_eq_norm] using (ContinuousMap.dist_apply_le_dist p).trans hfd
    have hphi : ‖picardPhiValues ell he z hlz p - picardPhiValues ell he w hlw p‖ ≤ S * dist z w :=
        by
      simpa only [dist_eq_norm] using (ContinuousMap.dist_apply_le_dist p).trans hvd
    have hphij : ‖picardPhiJets ell he z hlz p - picardPhiJets ell he w hlw p‖ ≤ S * dist z w := by
      simpa only [dist_eq_norm] using (ContinuousMap.dist_apply_le_dist p).trans hjd
    have hk : |picardChargeKernel e ell he z hlz p - picardChargeKernel e ell he w hlw p| ≤ S * dist
        z w :=
      (ContinuousMap.dist_apply_le_dist p).trans hkd
    have hcharge : |picardChargeRemainder e ell he z hlz p - picardChargeRemainder e ell he w hlw p|
        ≤ S * dist z w :=
      (ContinuousMap.dist_apply_le_dist p).trans hqd
    have hgap (i : Fin 9) : |picardGapProfiles ha haL e ell κ he hκ z hlz hgz p i -
        picardGapProfiles ha haL e ell κ he hκ w hlw hgw p i| ≤ Q * dist z w := by
      have h : ‖picardGapProfiles ha haL e ell κ he hκ z hlz hgz p -
          picardGapProfiles ha haL e ell κ he hκ w hlw hgw p‖ ≤ Q * dist z w := by
        simpa only [dist_eq_norm] using (ContinuousMap.dist_apply_le_dist p).trans
          (hq c a L ha haL hLR z w hlz hlw hgz hgw hz hw).2
      exact (norm_le_pi_norm _ i).trans h
    have hnu := (hn c a L ha haL hLR z w hlz hlw hgz hgw hz hw).2
    have hnuv := (picardCarrier_dist_value_le
      (picardNuRecon ha haL e ell κ he hκ z hlz hgz)
      (picardNuRecon ha haL e ell κ he hκ w hlw hgw) p).trans hnu
    have hnuj := (picardCarrier_dist_jet_le
      (picardNuRecon ha haL e ell κ he hκ z hlz hgz)
      (picardNuRecon ha haL e ell κ he hκ w hlw hgw) p).trans hnu
    have hlam : |(z.1.1 p).1 - (w.1.1 p).1| ≤ dist z w :=
      (le_max_left _ _).trans (picardCarrier_dist_value_le z w p)
    have hljet : |(z.1.2 p).1 - (w.1.2 p).1| ≤ dist z w :=
      (le_max_left _ _).trans (picardCarrier_dist_jet_le z w p)
    have hhjet : ‖(z.1.2 p).2 - (w.1.2 p).2‖ ≤ dist z w := by
      simpa only [dist_eq_norm] using (le_max_right _ _).trans (picardCarrier_dist_jet_le z w p)
    have hRS : |picardRadialAverage (picardLamValues z) p - picardRadialAverage (picardLamValues w)
        p| ≤ dist z w :=
      (ContinuousMap.dist_apply_le_dist p).trans
        ((picardRadialAverage_dist_le _ _).trans (picardLamValues_dist_le z w))
    have hRi : |(picardRadialAverage (picardLamValues z) p)⁻¹ -
        (picardRadialAverage (picardLamValues w) p)⁻¹| ≤ ell⁻¹ ^ 2 * dist z w :=
      (picard_inv_sub_le_aux he (picardRadialAverage_lower _ hlz p)
        (picardRadialAverage_lower _ hlw p)).trans
          (mul_le_mul_of_nonneg_left hRS (sq_nonneg _))
    rw [dist_eq_norm]
    change max ‖(picardSourceInput ha haL e ell κ he hκ z hlz hgz p).1 -
        (picardSourceInput ha haL e ell κ he hκ w hlw hgw p).1‖
      ‖(picardSourceInput ha haL e ell κ he hκ z hlz hgz p).2 -
        (picardSourceInput ha haL e ell κ he hκ w hlw hgw p).2‖ ≤ W * dist z w
    apply max_le
    · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hW dist_nonneg)).mpr
      intro i
      fin_cases i <;> simp only [Pi.sub_apply, picardSourceInput, ContinuousMap.prod_eval,
        ContinuousMap.pi_eval, Matrix.cons_val_zero', Matrix.cons_val_succ',
        picardProfileCoordinate, picardRatioInput, picardWidth, picardLamValues,
        ContinuousMap.coe_mk, Real.norm_eq_abs, sub_self, abs_zero]
      · positivity
      · exact hlam.trans
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h1W (dist_nonneg : 0 ≤ dist z
                w))
      · exact hljet.trans
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h1W (dist_nonneg : 0 ≤ dist z
                w))
      · exact hRi.trans (mul_le_mul_of_nonneg_right hiW dist_nonneg)
      · exact (hgap 4).trans (mul_le_mul_of_nonneg_right hQW dist_nonneg)
      · exact (hgap 5).trans (mul_le_mul_of_nonneg_right hQW dist_nonneg)
      · exact (hgap 0).trans (mul_le_mul_of_nonneg_right hQW dist_nonneg)
      · exact (hgap 1).trans (mul_le_mul_of_nonneg_right hQW dist_nonneg)
      · exact hcharge.trans (mul_le_mul_of_nonneg_right hSW dist_nonneg)
      · exact hk.trans (mul_le_mul_of_nonneg_right hSW dist_nonneg)
      · exact hnuv.trans (mul_le_mul_of_nonneg_right hNW dist_nonneg)
      · exact hnuj.trans (mul_le_mul_of_nonneg_right hNW dist_nonneg)
    · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hW dist_nonneg)).mpr
      intro i
      fin_cases i <;> simp only [Pi.sub_apply, picardSourceInput, ContinuousMap.prod_eval,
        ContinuousMap.pi_eval, Matrix.cons_val_zero', Matrix.cons_val_succ',
        picardHJets, ContinuousMap.coe_mk]
      · exact hf.trans (mul_le_mul_of_nonneg_right hSW dist_nonneg)
      · exact hhjet.trans
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h1W (dist_nonneg : 0 ≤ dist z
                w))
      · exact hphi.trans (mul_le_mul_of_nonneg_right hSW dist_nonneg)
      · exact hphij.trans (mul_le_mul_of_nonneg_right hSW dist_nonneg)
  have hinputfull (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
      (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q)
      (hz : picardCarrierSize z ≤ B) (p : PicardDomain c a L) :
      ‖(e, picardSourceInput ha haL e ell κ he hκ z hl hg p)‖ ≤ |e| + V := by
    apply max_le
    · simpa only [Real.norm_eq_abs] using
        (show |e| ≤ |e| + V from le_add_of_nonneg_right hV)
    · exact (hinput z hl hg hz p).trans (le_add_of_nonneg_left (abs_nonneg e))
  refine ⟨?_, ?_⟩
  · apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro p
    rw [picardSourceProfiles_apply]
    exact (hpolyN _ (hinputfull z hlz hgz hz p)).trans
      (by have hKW := mul_nonneg hK.le hW; linarith only [hKW])
  · apply (ContinuousMap.dist_le (by positivity)).mpr
    intro p
    rw [picardSourceProfiles_apply, picardSourceProfiles_apply]
    calc
      _ ≤ K * dist (picardSourceInput ha haL e ell κ he hκ z hlz hgz p)
          (picardSourceInput ha haL e ell κ he hκ w hlw hgw p) := by
        have h := hpolyD _ _ (hinputfull z hlz hgz hz p) (hinputfull w hlw hgw hw p)
        have heq : dist (e, picardSourceInput ha haL e ell κ he hκ z hlz hgz p)
            (e, picardSourceInput ha haL e ell κ he hκ w hlw hgw p) =
            dist (picardSourceInput ha haL e ell κ he hκ z hlz hgz p)
              (picardSourceInput ha haL e ell κ he hκ w hlw hgw p) := by
          rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
        simpa only [picardUniversalSourcePolynomial] using
          h.trans_eq (congrArg (fun r : ℝ => K * r) heq)
      _ ≤ K * (W * dist z w) := mul_le_mul_of_nonneg_left (hinputdist p) hK.le
      _ ≤ (1 + K + K * W) * dist z w := by
        have h0 : 0 ≤ (1 + K) * dist z w := by positivity
        nlinarith only [h0]

end EmcsfAcExtension.Local
