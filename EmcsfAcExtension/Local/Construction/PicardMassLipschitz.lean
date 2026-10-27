module

public import EmcsfAcExtension.Local.Construction.PicardMassEstimates
public import EmcsfAcExtension.Local.Construction.PicardChargeEstimates
public import EmcsfAcExtension.Local.Construction.PicardPolynomial

/-! # Uniform Lipschitz estimates for the mass coefficients

The normalized scalar and charge estimates control the damping and forcing
polynomials. All constants precede the candidates and are uniform in cone
position and incoming width. No second candidate derivative or Hawking gap
is used in these estimates.
-/

public section

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- The mass damping polynomial has the displayed Lipschitz bound from
normalized scalar size `F` and comparison constant `Cf`. The constant depends
only on `ell,U,F,Cf,L`, uniformly in cone position and incoming width. -/
theorem picardMassAm_dist_le_of_remainders (ell U F Cf : ℝ) (he : 0 < ell)
    (hU : 0 ≤ U) (hF : 0 ≤ F) (hCf : 0 ≤ Cf) (hL : 0 ≤ L)
    (z w : PicardCarrier c a L (ℝ × ℂ))
    (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1)
    (hz : ∀ q, |(z.1.1 q).1| ≤ U) (hw : ∀ q, |(w.1.1 q).1| ≤ U)
    (hfz : ‖picardScalarRemainder ell he z hlz‖ ≤ F)
    (hfw : ‖picardScalarRemainder ell he w hlw‖ ≤ F)
    (hdf : dist (picardScalarRemainder ell he z hlz)
      (picardScalarRemainder ell he w hlw) ≤ Cf * dist z w) :
    dist (picardMassAm ell he z hlz) (picardMassAm ell he w hlw) ≤
      L * (ell⁻¹ * (U * (2 * F * Cf) + F ^ 2) + U * F ^ 2 * ell⁻¹ ^ 2) * dist z w := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro p
  let f := picardScalarRemainder ell he z hlz p
  let g := picardScalarRemainder ell he w hlw p
  let R := picardRadialAverage (picardLamValues z) p
  let S := picardRadialAverage (picardLamValues w) p
  have hfn : ‖f‖ ≤ F := ((picardScalarRemainder ell he z hlz).norm_coe_le_norm p).trans hfz
  have hgn : ‖g‖ ≤ F := ((picardScalarRemainder ell he w hlw).norm_coe_le_norm p).trans hfw
  have hfg : ‖f - g‖ ≤ Cf * dist z w :=
    by simpa only [dist_eq_norm, f, g] using (ContinuousMap.dist_apply_le_dist p).trans hdf
  have hf2 : |‖f‖ ^ 2 - ‖g‖ ^ 2| ≤ (2 * F * Cf) * dist z w := by
    calc
      _ ≤ (2 * F) * (Cf * dist z w) := (picard_norm_sq_sub_le_aux F f g hfn hgn).trans
        (mul_le_mul_of_nonneg_left hfg (by positivity))
      _ = _ := by ring
  have hgn2 : |‖g‖ ^ 2| ≤ F ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) hF).mpr hgn
  have hla : |(z.1.1 p).1 - (w.1.1 p).1| ≤ dist z w :=
    (le_max_left _ _).trans (picardCarrier_dist_value_le z w p)
  have hN : |(z.1.1 p).1 * ‖f‖ ^ 2 - (w.1.1 p).1 * ‖g‖ ^ 2| ≤
      (U * (2 * F * Cf) + F ^ 2) * dist z w := by
    have h := picard_mul_sub_le_aux (z.1.1 p).1 (w.1.1 p).1 (‖f‖ ^ 2) (‖g‖ ^ 2)
    simp only [Real.norm_eq_abs] at h
    calc
      _ ≤ U * ((2 * F * Cf) * dist z w) + dist z w * F ^ 2 := h.trans
        (add_le_add (mul_le_mul (hz p) hf2 (abs_nonneg _) hU)
          (mul_le_mul hla hgn2 (abs_nonneg _) dist_nonneg))
      _ = _ := by ring
  have hNy : |(w.1.1 p).1 * ‖g‖ ^ 2| ≤ U * F ^ 2 := by
    rw [abs_mul]
    exact mul_le_mul (hw p) hgn2 (abs_nonneg _) hU
  have hRS : |R - S| ≤ dist z w :=
    (ContinuousMap.dist_apply_le_dist p).trans
      ((picardRadialAverage_dist_le _ _).trans (picardLamValues_dist_le z w))
  have hQ := picard_div_sub_le_aux ell (U * F ^ 2) (U * (2 * F * Cf) + F ^ 2)
    (dist z w) ((z.1.1 p).1 * ‖f‖ ^ 2) ((w.1.1 p).1 * ‖g‖ ^ 2) R S
    he (by positivity) (by positivity) dist_nonneg
    (picardRadialAverage_lower _ hlz p) (picardRadialAverage_lower _ hlw p) hNy hN hRS
  have hx : 0 ≤ p.1.2 - p.1.1 := sub_nonneg.mpr p.2.1.2.1
  have hxL : p.1.2 - p.1.1 ≤ L := by linarith [p.2.1.1, p.2.1.2.2]
  rw [Real.dist_eq]
  change |(p.1.2 - p.1.1) * (z.1.1 p).1 * ‖f‖ ^ 2 / R -
    (p.1.2 - p.1.1) * (w.1.1 p).1 * ‖g‖ ^ 2 / S| ≤ _
  have heq : (p.1.2 - p.1.1) * (z.1.1 p).1 * ‖f‖ ^ 2 / R -
      (p.1.2 - p.1.1) * (w.1.1 p).1 * ‖g‖ ^ 2 / S =
      (p.1.2 - p.1.1) * ((z.1.1 p).1 * ‖f‖ ^ 2 / R - (w.1.1 p).1 * ‖g‖ ^ 2 / S) := by ring
  rw [heq, abs_mul, abs_of_nonneg hx]
  exact (mul_le_mul hxL hQ (abs_nonneg _) hL).trans_eq (by ring)

/-- The normalized mass forcing polynomial has the displayed Lipschitz
bound from scalar and charge remainder sizes and comparison constants.
It depends only on `ell,U,F,Q,Cf,Cq,L`, uniformly in both candidates. -/
theorem picardMassKernel_dist_le_of_remainders (ell U F Q Cf Cq e : ℝ) (he : 0 < ell)
    (hU : 0 ≤ U) (hF : 0 ≤ F) (hQ : 0 ≤ Q) (hCf : 0 ≤ Cf) (hCq : 0 ≤ Cq) (hL : 0 ≤ L)
    (z w : PicardCarrier c a L (ℝ × ℂ))
    (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1)
    (hz : ∀ q, |(z.1.1 q).1| ≤ U)
    (hfz : ‖picardScalarRemainder ell he z hlz‖ ≤ F)
    (hfw : ‖picardScalarRemainder ell he w hlw‖ ≤ F)
    (hqz : ‖picardChargeRemainder e ell he z hlz‖ ≤ Q)
    (hqw : ‖picardChargeRemainder e ell he w hlw‖ ≤ Q)
    (hdf : dist (picardScalarRemainder ell he z hlz)
      (picardScalarRemainder ell he w hlw) ≤ Cf * dist z w)
    (hdq : dist (picardChargeRemainder e ell he z hlz)
      (picardChargeRemainder e ell he w hlw) ≤ Cq * dist z w) :
    dist (picardMassKernel e ell he z hlz) (picardMassKernel e ell he w hlw) ≤
      (U / 2 * (2 * F * Cf + L ^ 2 * (2 * (Q / ell) * (ell⁻¹ * Cq + Q * ell⁻¹ ^ 2))) +
        (F ^ 2 + L ^ 2 * (Q / ell) ^ 2) / 2) * dist z w := by
  let J := Q / ell
  let Cj := ell⁻¹ * Cq + Q * ell⁻¹ ^ 2
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hCj : 0 ≤ Cj := by dsimp [Cj]; positivity
  apply (ContinuousMap.dist_le (by dsimp [J, Cj] at *; positivity)).mpr
  intro p
  let f := picardScalarRemainder ell he z hlz p
  let g := picardScalarRemainder ell he w hlw p
  let q := picardChargeRemainder e ell he z hlz p
  let s := picardChargeRemainder e ell he w hlw p
  let R := picardRadialAverage (picardLamValues z) p
  let S := picardRadialAverage (picardLamValues w) p
  have hR : ell ≤ R := picardRadialAverage_lower _ hlz p
  have hS : ell ≤ S := picardRadialAverage_lower _ hlw p
  have hfn : ‖f‖ ≤ F := ((picardScalarRemainder ell he z hlz).norm_coe_le_norm p).trans hfz
  have hgn : ‖g‖ ≤ F := ((picardScalarRemainder ell he w hlw).norm_coe_le_norm p).trans hfw
  have hqn : |q| ≤ Q := ((picardChargeRemainder e ell he z hlz).norm_coe_le_norm p).trans hqz
  have hsn : |s| ≤ Q := ((picardChargeRemainder e ell he w hlw).norm_coe_le_norm p).trans hqw
  have hfg : ‖f - g‖ ≤ Cf * dist z w := by
    simpa only [dist_eq_norm, f, g] using (ContinuousMap.dist_apply_le_dist p).trans hdf
  have hqs : |q - s| ≤ Cq * dist z w := (ContinuousMap.dist_apply_le_dist p).trans hdq
  have hRS : |R - S| ≤ dist z w :=
    (ContinuousMap.dist_apply_le_dist p).trans
      ((picardRadialAverage_dist_le _ _).trans (picardLamValues_dist_le z w))
  have hJn (q R : ℝ) (hq : |q| ≤ Q) (hR : ell ≤ R) : |q / R| ≤ J := by
    rw [abs_div, abs_of_pos (he.trans_le hR)]
    exact (div_le_div_of_nonneg_left (abs_nonneg _) he hR).trans
      (div_le_div_of_nonneg_right hq he.le)
  have hJd : |q / R - s / S| ≤ Cj * dist z w :=
    picard_div_sub_le_aux ell Q Cq (dist z w) q s R S he hQ hCq dist_nonneg hR hS hsn hqs hRS
  have hJ2 : |(q / R) ^ 2 - (s / S) ^ 2| ≤ (2 * J * Cj) * dist z w := by
    have h := picard_norm_sq_sub_le_aux J (q / R) (s / S) (hJn q R hqn hR) (hJn s S hsn hS)
    simp only [Real.norm_eq_abs, sq_abs] at h
    exact (h.trans (mul_le_mul_of_nonneg_left hJd (by positivity))).trans_eq (by ring)
  have hF2 : |‖f‖ ^ 2 - ‖g‖ ^ 2| ≤ (2 * F * Cf) * dist z w :=
    ((picard_norm_sq_sub_le_aux F f g hfn hgn).trans
      (mul_le_mul_of_nonneg_left hfg (by positivity))).trans_eq (by ring)
  have hx : 0 ≤ p.1.2 - p.1.1 := sub_nonneg.mpr p.2.1.2.1
  have hxL : p.1.2 - p.1.1 ≤ L := by linarith [p.2.1.1, p.2.1.2.2]
  let T := ‖f‖ ^ 2 + (p.1.2 - p.1.1) ^ 2 * (q / R) ^ 2
  let V := ‖g‖ ^ 2 + (p.1.2 - p.1.1) ^ 2 * (s / S) ^ 2
  have hV : |V| ≤ F ^ 2 + L ^ 2 * J ^ 2 := by
    rw [abs_of_nonneg (by dsimp [V]; positivity)]
    exact add_le_add ((sq_le_sq₀ (norm_nonneg _) hF).mpr hgn)
      (mul_le_mul ((sq_le_sq₀ hx hL).mpr hxL)
        (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hJ).mpr (hJn s S hsn hS))
        (sq_nonneg _) (sq_nonneg _))
  have hTV : |T - V| ≤ (2 * F * Cf + L ^ 2 * (2 * J * Cj)) * dist z w := by
    have heq : T - V = (‖f‖ ^ 2 - ‖g‖ ^ 2) + (p.1.2 - p.1.1) ^ 2 *
        ((q / R) ^ 2 - (s / S) ^ 2) := by dsimp [T, V]; ring
    rw [heq]
    calc
      _ ≤ |‖f‖ ^ 2 - ‖g‖ ^ 2| + |(p.1.2 - p.1.1) ^ 2 * ((q / R) ^ 2 - (s / S) ^ 2)| := abs_add_le _
          _
      _ ≤ (2 * F * Cf) * dist z w + L ^ 2 * ((2 * J * Cj) * dist z w) := by
        rw [abs_mul, abs_of_nonneg (sq_nonneg (p.1.2 - p.1.1))]
        exact add_le_add hF2 (mul_le_mul ((sq_le_sq₀ hx hL).mpr hxL) hJ2 (abs_nonneg _) (sq_nonneg
            _))
      _ = _ := by ring
  have hla : |(z.1.1 p).1 / 2| ≤ U / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (hz p) (by norm_num : (0 : ℝ) ≤ 2)
  have hld : |(z.1.1 p).1 / 2 - (w.1.1 p).1 / 2| ≤ dist z w / 2 := by
    rw [←sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right
      ((le_max_left _ _).trans (picardCarrier_dist_value_le z w p)) (by norm_num)
  rw [Real.dist_eq]
  change |(z.1.1 p).1 / 2 * (‖f‖ ^ 2 + (p.1.2 - p.1.1) ^ 2 * q ^ 2 / R ^ 2) -
    (w.1.1 p).1 / 2 * (‖g‖ ^ 2 + (p.1.2 - p.1.1) ^ 2 * s ^ 2 / S ^ 2)| ≤ _
  have heq : (p.1.2 - p.1.1) ^ 2 * q ^ 2 / R ^ 2 = (p.1.2 - p.1.1) ^ 2 * (q / R) ^ 2 :=
      by rw [div_pow, mul_div_assoc]
  have heq' : (p.1.2 - p.1.1) ^ 2 * s ^ 2 / S ^ 2 = (p.1.2 - p.1.1) ^ 2 * (s / S) ^ 2 :=
      by rw [div_pow, mul_div_assoc]
  rw [heq, heq']
  have hm := picard_mul_sub_le_aux ((z.1.1 p).1 / 2) ((w.1.1 p).1 / 2) T V
  simp only [Real.norm_eq_abs] at hm
  calc
    _ ≤ (U / 2) * ((2 * F * Cf + L ^ 2 * (2 * J * Cj)) * dist z w) +
        (dist z w / 2) * (F ^ 2 + L ^ 2 * J ^ 2) := hm.trans (add_le_add
      (mul_le_mul hla hTV (abs_nonneg _) (by positivity))
      (mul_le_mul hld hV (abs_nonneg _) (by positivity)))
    _ = _ := by dsimp [J, Cj]; ring

end EmcsfAcExtension.Local
