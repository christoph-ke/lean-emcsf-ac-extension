module

public import EmcsfAcExtension.Local.Construction.PicardCharge
public import EmcsfAcExtension.Local.Construction.PicardScalarEstimates

/-! # Uniform normalized charge bounds and differences

The scalar estimates and the charge polynomial give bounds independent of cone
position and strip width. Radial moments preserve those uniform Lipschitz bounds.
This module proves the charge component of the radial node, not the full node.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

private theorem picard_charge_average_norm_aux (f : C(PicardDomain c a L, ℝ)) :
    ‖picardRadialAverage f‖ ≤ ‖f‖ := by
  have hz : picardRadialAverage (0 : C(PicardDomain c a L, ℝ)) = 0 := by
    ext p
    simp [picardRadialAverage]
  simpa only [hz, dist_zero_right] using picardRadialAverage_dist_le f 0
private theorem picard_charge_moment_norm_aux (f : C(PicardDomain c a L, ℝ)) :
    ‖picardRadialMoment 2 f‖ ≤ ‖f‖ := by
  have hz : picardRadialMoment 2 (0 : C(PicardDomain c a L, ℝ)) = 0 := by
    ext p
    simp [picardRadialMoment]
  simpa only [hz, dist_zero_right] using picardRadialMoment_dist_le 2 f 0

/-- The quadratic charge-source coefficient is bounded by the displayed
constant depending only on `ell,U,D,H,L,|e|`, uniformly in `c,a` and the candidate. -/
theorem picardChargeKernel_norm_le (ell U D H e : ℝ) (he : 0 < ell)
    (hU : 0 ≤ U) (hD : 0 ≤ D) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hz : ∀ q, |(z.1.1 q).1| ≤ U) (hj : ∀ q, ‖(z.1.2 q).2‖ ≤ D)
    (hh : ∀ q, ‖(z.1.1 q).2‖ ≤ H) :
    ‖picardChargeKernel e ell he z hl‖ ≤
      |e| * U * U * (H + L * (ell⁻¹ * (U * D / 2))) * (ell⁻¹ * (U * D / 2)) := by
  let F := ell⁻¹ * (U * D / 2)
  let V := H + L * F
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hnF := picardScalarRemainder_norm_le ell U D he hU hD z hl hz hj
  have hnV := picardPhiValues_norm_le ell U D H he hU hD hH hL z hl hz hj hh
  have hnlam : ‖picardLamValues z‖ ≤ U := (ContinuousMap.norm_le _ hU).mpr (by
    intro q
    simpa only [picardLamValues, ContinuousMap.coe_mk, Real.norm_eq_abs] using hz q)
  have hnR : ‖picardRadialAverage (picardLamValues z)‖ ≤ U := (picard_charge_average_norm_aux
      _).trans hnlam
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro p
  have hR : |picardRadialAverage (picardLamValues z) p| ≤ U := by
    simpa only [Real.norm_eq_abs] using
      ((picardRadialAverage (picardLamValues z)).norm_coe_le_norm p).trans hnR
  have hpF : ‖picardScalarRemainder ell he z hl p‖ ≤ F :=
    ((picardScalarRemainder ell he z hl).norm_coe_le_norm p).trans hnF
  have hpV : ‖picardPhiValues ell he z hl p‖ ≤ V :=
    ((picardPhiValues ell he z hl).norm_coe_le_norm p).trans hnV
  have hA : |-e * picardRadialAverage (picardLamValues z) p * (z.1.1 p).1| ≤ |e| * U * U := by
    rw [abs_mul, abs_mul, abs_neg]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hR (abs_nonneg _)) (hz p)
      (abs_nonneg _) (mul_nonneg (abs_nonneg _) hU)
  have hB : |(starRingEnd ℂ (picardPhiValues ell he z hl p) * picardScalarRemainder ell he z hl
      p).im| ≤ V * F := by
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hpV hpF (norm_nonneg _) hV
  rw [Real.norm_eq_abs]
  change |-e * picardRadialAverage (picardLamValues z) p * (z.1.1 p).1 *
    (starRingEnd ℂ (picardPhiValues ell he z hl p) * picardScalarRemainder ell he z hl p).im| ≤ _
  rw [abs_mul]
  calc
    _ ≤ (|e| * U * U) * (V * F) := mul_le_mul hA hB (abs_nonneg _) (by positivity)
    _ = _ := by dsimp only [V, F]; ring

private theorem picard_charge_mul_diff_aux {F : Type*} [NormedRing F] (x x' y y' : F) :
    ‖x * y - x' * y'‖ ≤ ‖x‖ * ‖y - y'‖ + ‖x - x'‖ * ‖y'‖ := by
  have heq : x * y - x' * y' = x * (y - y') + (x - x') * y' := by
    rw [mul_sub, sub_mul]; abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

private theorem picard_charge_polynomial_dist_aux (e R S l k : ℝ) (phi psi f g : ℂ)
    {U V F Cv Cf Δ : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (_hF : 0 ≤ F)
    (hCv : 0 ≤ Cv) (_hCf : 0 ≤ Cf) (hΔ : 0 ≤ Δ)
    (hR : |R| ≤ U) (_hS : |S| ≤ U) (hl : |l| ≤ U) (hk : |k| ≤ U)
    (hphi : ‖phi‖ ≤ V) (hpsi : ‖psi‖ ≤ V) (_hf : ‖f‖ ≤ F) (hg : ‖g‖ ≤ F)
    (hRS : |R - S| ≤ Δ) (hlk : |l - k| ≤ Δ)
    (hp : ‖phi - psi‖ ≤ Cv * Δ) (hfg : ‖f - g‖ ≤ Cf * Δ) :
    |-e * R * l * (starRingEnd ℂ phi * f).im - (-e * S * k * (starRingEnd ℂ psi * g).im)| ≤
      |e| * (U * U * (V * Cf + Cv * F) + (2 * U) * (V * F)) * Δ := by
  have hA : |R * l - S * k| ≤ (2 * U) * Δ := by
    have h := picard_charge_mul_diff_aux R S l k
    simp only [Real.norm_eq_abs] at h
    calc
      _ ≤ U * Δ + Δ * U := h.trans (add_le_add
        (mul_le_mul hR hlk (abs_nonneg _) hU)
        (mul_le_mul hRS hk (abs_nonneg _) hΔ))
      _ = _ := by ring
  have hAn : |R * l| ≤ U * U := by rw [abs_mul]; exact mul_le_mul hR hl (abs_nonneg _) hU
  have hB : |(starRingEnd ℂ psi * g).im| ≤ V * F := by
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul hpsi hg (norm_nonneg _) hV
  have hBd : |(starRingEnd ℂ phi * f).im - (starRingEnd ℂ psi * g).im| ≤ (V * Cf + Cv * F) * Δ := by
    rw [←Complex.sub_im]
    refine (Complex.abs_im_le_norm _).trans ?_
    have h := picard_charge_mul_diff_aux (starRingEnd ℂ phi) (starRingEnd ℂ psi) f g
    rw [←map_sub, Complex.norm_conj, Complex.norm_conj] at h
    calc
      _ ≤ V * (Cf * Δ) + (Cv * Δ) * F := h.trans (add_le_add
        (mul_le_mul hphi hfg (norm_nonneg _) hV)
        (mul_le_mul hp hg (norm_nonneg _) (mul_nonneg hCv hΔ)))
      _ = _ := by ring
  have h := picard_charge_mul_diff_aux (R * l) (S * k) (starRingEnd ℂ phi * f).im (starRingEnd ℂ psi
      * g).im
  simp only [Real.norm_eq_abs] at h
  have hprod : |R * l * (starRingEnd ℂ phi * f).im - S * k * (starRingEnd ℂ psi * g).im| ≤
      (U * U * (V * Cf + Cv * F) + (2 * U) * (V * F)) * Δ := by
    calc
      _ ≤ (U * U) * ((V * Cf + Cv * F) * Δ) + ((2 * U) * Δ) * (V * F) := h.trans (add_le_add
        (mul_le_mul hAn hBd (abs_nonneg _) (mul_nonneg hU hU))
        (mul_le_mul hA hB (abs_nonneg _) (by positivity)))
      _ = _ := by ring
  have heq : -e * R * l * (starRingEnd ℂ phi * f).im - (-e * S * k * (starRingEnd ℂ psi * g).im) =
      -e * (R * l * (starRingEnd ℂ phi * f).im - S * k * (starRingEnd ℂ psi * g).im) := by ring
  rw [heq, abs_mul, abs_neg]
  exact (mul_le_mul_of_nonneg_left hprod (abs_nonneg _)).trans_eq (by ring)

/-- The quadratic charge-source coefficient has the displayed Lipschitz
constant, depending only on `ell,U,D,H,L,|e|`, uniformly in `c,a` and both candidates. -/
theorem picardChargeKernel_dist_le (ell U D H e : ℝ) (he : 0 < ell)
    (hU : 0 ≤ U) (hD : 0 ≤ D) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (z w : PicardCarrier c a L (ℝ × ℂ))
    (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1)
    (hz : ∀ q, |(z.1.1 q).1| ≤ U) (hw : ∀ q, |(w.1.1 q).1| ≤ U)
    (hjz : ∀ q, ‖(z.1.2 q).2‖ ≤ D) (hjw : ∀ q, ‖(w.1.2 q).2‖ ≤ D)
    (hhz : ∀ q, ‖(z.1.1 q).2‖ ≤ H) (hhw : ∀ q, ‖(w.1.1 q).2‖ ≤ H) :
    dist (picardChargeKernel e ell he z hlz) (picardChargeKernel e ell he w hlw) ≤
      |e| * (U * U * ((H + L * (ell⁻¹ * (U * D / 2))) * (ell⁻¹ * ((D + U) / 2) + ell⁻¹ ^ 2 * (U * D
          / 2)) +
        (1 + L * (ell⁻¹ * ((D + U) / 2) + ell⁻¹ ^ 2 * (U * D / 2))) * (ell⁻¹ * (U * D / 2))) +
        (2 * U) * ((H + L * (ell⁻¹ * (U * D / 2))) * (ell⁻¹ * (U * D / 2)))) * dist z w := by
  let F := ell⁻¹ * (U * D / 2)
  let V := H + L * F
  let Cf := ell⁻¹ * ((D + U) / 2) + ell⁻¹ ^ 2 * (U * D / 2)
  let Cv := 1 + L * Cf
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hCf : 0 ≤ Cf := by dsimp [Cf]; positivity
  have hCv : 0 ≤ Cv := by dsimp [Cv]; positivity
  have hRn (k : PicardCarrier c a L (ℝ × ℂ)) (hk : ∀ q, |(k.1.1 q).1| ≤ U) :
      ‖picardRadialAverage (picardLamValues k)‖ ≤ U := by
    refine (picard_charge_average_norm_aux _).trans ((ContinuousMap.norm_le _ hU).mpr ?_)
    intro q
    simpa only [picardLamValues, ContinuousMap.coe_mk, Real.norm_eq_abs] using hk q
  have hnFz := picardScalarRemainder_norm_le ell U D he hU hD z hlz hz hjz
  have hnFw := picardScalarRemainder_norm_le ell U D he hU hD w hlw hw hjw
  have hnVz := picardPhiValues_norm_le ell U D H he hU hD hH hL z hlz hz hjz hhz
  have hnVw := picardPhiValues_norm_le ell U D H he hU hD hH hL w hlw hw hjw hhw
  have hdF := picardScalarRemainder_dist_le ell U D he hU hD z w hlz hlw hz hw hjz hjw
  have hdV := picardPhiValues_dist_le ell U D he hU hD z w hlz hlw hz hw hjz hjw hL
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro p
  have hRz : |picardRadialAverage (picardLamValues z) p| ≤ U := by
    simpa only [Real.norm_eq_abs] using
      ((picardRadialAverage (picardLamValues z)).norm_coe_le_norm p).trans (hRn z hz)
  have hRw : |picardRadialAverage (picardLamValues w) p| ≤ U := by
    simpa only [Real.norm_eq_abs] using
      ((picardRadialAverage (picardLamValues w)).norm_coe_le_norm p).trans (hRn w hw)
  have hRS : |picardRadialAverage (picardLamValues z) p -
      picardRadialAverage (picardLamValues w) p| ≤ dist z w :=
    (ContinuousMap.dist_apply_le_dist p).trans
      ((picardRadialAverage_dist_le _ _).trans (picardLamValues_dist_le z w))
  have hlk : |(z.1.1 p).1 - (w.1.1 p).1| ≤ dist z w :=
    (ContinuousMap.dist_apply_le_dist p).trans (picardLamValues_dist_le z w)
  have hVp : ‖picardPhiValues ell he z hlz p - picardPhiValues ell he w hlw p‖ ≤ Cv * dist z w := by
    simpa only [dist_eq_norm, Cv, Cf] using (ContinuousMap.dist_apply_le_dist p).trans hdV
  have hFp : ‖picardScalarRemainder ell he z hlz p - picardScalarRemainder ell he w hlw p‖ ≤ Cf *
      dist z w := by
    simpa only [dist_eq_norm, Cf] using (ContinuousMap.dist_apply_le_dist p).trans hdF
  rw [Real.dist_eq]
  change |-e * picardRadialAverage (picardLamValues z) p * (z.1.1 p).1 *
    (starRingEnd ℂ (picardPhiValues ell he z hlz p) * picardScalarRemainder ell he z hlz p).im -
      (-e * picardRadialAverage (picardLamValues w) p * (w.1.1 p).1 *
        (starRingEnd ℂ (picardPhiValues ell he w hlw p) * picardScalarRemainder ell he w hlw p).im)|
            ≤ _
  exact picard_charge_polynomial_dist_aux _ _ _ _ _ _ _ _ _ hU hV hF hCv hCf dist_nonneg
    hRz hRw (hz p) (hw p)
    (((picardPhiValues ell he z hlz).norm_coe_le_norm p).trans hnVz)
    (((picardPhiValues ell he w hlw).norm_coe_le_norm p).trans hnVw)
    (((picardScalarRemainder ell he z hlz).norm_coe_le_norm p).trans hnFz)
    (((picardScalarRemainder ell he w hlw).norm_coe_le_norm p).trans hnFw)
    hRS hlk hVp hFp

/-- The normalized cubic charge is bounded by the displayed constant
depending only on `ell,U,D,H,L,|e|`, uniformly in `c,a` and the candidate. -/
theorem picardChargeRemainder_norm_le (ell U D H e : ℝ) (he : 0 < ell)
    (hU : 0 ≤ U) (hD : 0 ≤ D) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hz : ∀ q, |(z.1.1 q).1| ≤ U) (hj : ∀ q, ‖(z.1.2 q).2‖ ≤ D)
    (hh : ∀ q, ‖(z.1.1 q).2‖ ≤ H) :
    ‖picardChargeRemainder e ell he z hl‖ ≤
      |e| * U * U * (H + L * (ell⁻¹ * (U * D / 2))) * (ell⁻¹ * (U * D / 2)) := by
  exact (picard_charge_moment_norm_aux _).trans (picardChargeKernel_norm_le ell U D H e he hU hD hH
      hL z hl hz hj hh)

/-- The normalized cubic charge has the displayed Lipschitz constant
depending only on `ell,U,D,H,L,|e|`, uniformly in `c,a` and both candidates. -/
theorem picardChargeRemainder_dist_le (ell U D H e : ℝ) (he : 0 < ell)
    (hU : 0 ≤ U) (hD : 0 ≤ D) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (z w : PicardCarrier c a L (ℝ × ℂ))
    (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1)
    (hz : ∀ q, |(z.1.1 q).1| ≤ U) (hw : ∀ q, |(w.1.1 q).1| ≤ U)
    (hjz : ∀ q, ‖(z.1.2 q).2‖ ≤ D) (hjw : ∀ q, ‖(w.1.2 q).2‖ ≤ D)
    (hhz : ∀ q, ‖(z.1.1 q).2‖ ≤ H) (hhw : ∀ q, ‖(w.1.1 q).2‖ ≤ H) :
    dist (picardChargeRemainder e ell he z hlz) (picardChargeRemainder e ell he w hlw) ≤
      |e| * (U * U * ((H + L * (ell⁻¹ * (U * D / 2))) * (ell⁻¹ * ((D + U) / 2) + ell⁻¹ ^ 2 * (U * D
          / 2)) +
        (1 + L * (ell⁻¹ * ((D + U) / 2) + ell⁻¹ ^ 2 * (U * D / 2))) * (ell⁻¹ * (U * D / 2))) +
        (2 * U) * ((H + L * (ell⁻¹ * (U * D / 2))) * (ell⁻¹ * (U * D / 2)))) * dist z w := by
  exact (picardRadialMoment_dist_le 2 _ _).trans
    (picardChargeKernel_dist_le ell U D H e he hU hD hH hL z w hlz hlw hz hw hjz hjw hhz hhw)

end EmcsfAcExtension.Local
