module

public import EmcsfAcExtension.Local.Construction.PicardUniformScalar
public import EmcsfAcExtension.Local.Construction.PicardMassLipschitz

/-! # Mass bounds uniform in the actual cone length

The scalar and charge bounds use a fixed upper length. The normalized mass
coefficients and nonnegative damping preserve this quantifier order.
-/

public section

namespace EmcsfAcExtension.Local

/-- Both mass coefficients and the normalized cubic mass have a common
positive size and comparison constant depending only on `ell,B,R,|e|`,
uniformly in all cone positions, incoming widths and lengths `0 ≤ L ≤ R`.
No inverse-gap assumption or higher candidate derivative is used. -/
theorem picardMass_uniform (ell B R e : ℝ) (he : 0 < ell) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ (c a L : ℝ), 0 ≤ L → L ≤ R →
      ∀ (z w : PicardCarrier c a L (ℝ × ℂ))
        (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1),
      picardCarrierSize z ≤ B → picardCarrierSize w ≤ B →
      ‖picardMassAm ell he z hlz‖ ≤ C ∧
      ‖picardMassKernel e ell he z hlz‖ ≤ C ∧
      ‖picardMassRemainder e ell he z hlz‖ ≤ C ∧
      dist (picardMassAm ell he z hlz) (picardMassAm ell he w hlw) ≤ C * dist z w ∧
      dist (picardMassKernel e ell he z hlz) (picardMassKernel e ell he w hlw) ≤ C * dist z w ∧
      dist (picardMassRemainder e ell he z hlz) (picardMassRemainder e ell he w hlw) ≤ C * dist z w
          := by
  obtain ⟨S, hS, hs⟩ := picardScalarCharge_uniform ell B R e he hB hR
  let A := R * B * S ^ 2 / ell
  let K := B / 2 * (S ^ 2 + R ^ 2 * S ^ 2 / ell ^ 2)
  let Ca := R * (ell⁻¹ * (B * (2 * S * S) + S ^ 2) + B * S ^ 2 * ell⁻¹ ^ 2)
  let Ck := B / 2 * (2 * S * S + R ^ 2 * (2 * (S / ell) * (ell⁻¹ * S + S * ell⁻¹ ^ 2))) +
    (S ^ 2 + R ^ 2 * (S / ell) ^ 2) / 2
  let Cm := Ck + R * K * Ca
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hCa : 0 ≤ Ca := by dsimp [Ca]; positivity
  have hCk : 0 ≤ Ck := by dsimp [Ck]; positivity
  have hCm : 0 ≤ Cm := by dsimp [Cm]; positivity
  let C := 1 + A + K + Ca + Ck + Cm
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ C := by dsimp [C]; linarith only [hK, hCa, hCk, hCm]
  have hKC : K ≤ C := by dsimp [C]; linarith only [hA, hCa, hCk, hCm]
  have hCaC : Ca ≤ C := by dsimp [C]; linarith only [hA, hK, hCk, hCm]
  have hCkC : Ck ≤ C := by dsimp [C]; linarith only [hA, hK, hCa, hCm]
  have hCmC : Cm ≤ C := by dsimp [C]; linarith only [hA, hK, hCa, hCk]
  refine ⟨C, hC, ?_⟩
  intro c a L hL hLR z w hlz hlw hz hw
  obtain ⟨hfz, hdf, _, _, _, _, _, _, hqz, hdq⟩ := hs c a L hL hLR z w hlz hlw hz hw
  obtain ⟨hfw, _, _, _, _, _, _, _, hqw, _⟩ := hs c a L hL hLR w z hlw hlz hw hz
  have hzl : ∀ q, (z.1.1 q).1 ≤ B := fun q => (le_abs_self _).trans
    ((picardCarrier_pointwise_bounds_of_size B z hz).1 q)
  have hwl : ∀ q, (w.1.1 q).1 ≤ B := fun q => (le_abs_self _).trans
    ((picardCarrier_pointwise_bounds_of_size B w hw).1 q)
  have han : ‖picardMassAm ell he z hlz‖ ≤ A :=
    (picardMassAm_norm_le ell B S he hB hS.le hL z hlz hzl hfz).trans
      (by dsimp [A]; gcongr)
  have hkn (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
      (hzl : ∀ q, (z.1.1 q).1 ≤ B)
      (hf : ‖picardScalarRemainder ell he z hl‖ ≤ S)
      (hq : ‖picardChargeRemainder e ell he z hl‖ ≤ S) :
      ‖picardMassKernel e ell he z hl‖ ≤ K :=
    (picardMassKernel_norm_le ell B S S e he hB hS.le hS.le hL z hl hzl hf hq).trans
      (by dsimp [K]; gcongr)
  have hknz := hkn z hlz hzl hfz hqz
  have hknw := hkn w hlw hwl hfw hqw
  have hmn : ‖picardMassRemainder e ell he z hlz‖ ≤ K :=
    (picardMassRemainder_norm_le_kernel e ell he z hlz).trans hknz
  have had : dist (picardMassAm ell he z hlz) (picardMassAm ell he w hlw) ≤ Ca * dist z w :=
    (picardMassAm_dist_le_of_remainders ell B S S he hB hS.le hS.le hL z w hlz hlw
      (picardCarrier_pointwise_bounds_of_size B z hz).1
      (picardCarrier_pointwise_bounds_of_size B w hw).1 hfz hfw hdf).trans
        (mul_le_mul_of_nonneg_right (by dsimp [Ca]; gcongr) dist_nonneg)
  have hkd : dist (picardMassKernel e ell he z hlz) (picardMassKernel e ell he w hlw) ≤ Ck * dist z
      w :=
    (picardMassKernel_dist_le_of_remainders ell B S S S S e he hB hS.le hS.le hS.le hS.le hL
      z w hlz hlw (picardCarrier_pointwise_bounds_of_size B z hz).1
      hfz hfw hqz hqw hdf hdq).trans
        (mul_le_mul_of_nonneg_right (by dsimp [Ck]; gcongr) dist_nonneg)
  have hmd : dist (picardMassRemainder e ell he z hlz) (picardMassRemainder e ell he w hlw) ≤ Cm *
      dist z w := by
    calc
      _ ≤ dist (picardMassKernel e ell he z hlz) (picardMassKernel e ell he w hlw) +
          L * ‖picardMassKernel e ell he w hlw‖ * dist (picardMassAm ell he z hlz) (picardMassAm ell
              he w hlw) :=
        picardMassRemainder_dist_le_coefficients hL e ell he z w hlz hlw
      _ ≤ Ck * dist z w + R * K * (Ca * dist z w) := add_le_add hkd
        (mul_le_mul (mul_le_mul hLR hknw (norm_nonneg _) hR) had dist_nonneg (by positivity))
      _ = Cm * dist z w := by dsimp [Cm]; ring
  exact ⟨han.trans hAC, hknz.trans hKC, hmn.trans hKC,
    had.trans (mul_le_mul_of_nonneg_right hCaC dist_nonneg),
    hkd.trans (mul_le_mul_of_nonneg_right hCkC dist_nonneg),
    hmd.trans (mul_le_mul_of_nonneg_right hCmC dist_nonneg)⟩

end EmcsfAcExtension.Local
