module

public import EmcsfAcExtension.Local.Construction.PicardRadial

/-! # Bounds and Lipschitz estimates for the scalar radial reconstruction

All displayed constants are uniform in the candidate. The scalar construction
uses the first outgoing jet and the positive lambda average, including the axis.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- Projection to lambda values has universal Lipschitz constant one. -/
theorem picardLamValues_dist_le (z w : PicardCarrier c a L (ℝ × ℂ)) :
    dist (picardLamValues z) (picardLamValues w) ≤ dist z w := by
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro p
  exact (le_max_left _ _).trans (picardCarrier_dist_value_le z w p)

/-- Projection to the outgoing scalar jet has universal Lipschitz constant one. -/
theorem picardHJets_dist_le (z w : PicardCarrier c a L (ℝ × ℂ)) :
    dist (picardHJets z) (picardHJets w) ≤ dist z w := by
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro p
  exact (le_max_right _ _).trans (picardCarrier_dist_jet_le z w p)

private theorem picard_inv_sub_le_aux {ell R S : ℝ} (he : 0 < ell) (hR : ell ≤ R) (hS : ell ≤ S) :
    |R⁻¹ - S⁻¹| ≤ ell⁻¹ ^ 2 * |R - S| := by
  have hRp : 0 < R := he.trans_le hR
  have hSp : 0 < S := he.trans_le hS
  have hRi : R⁻¹ ≤ ell⁻¹ := (inv_le_inv₀ hRp he).mpr hR
  have hSi : S⁻¹ ≤ ell⁻¹ := (inv_le_inv₀ hSp he).mpr hS
  have heq : R⁻¹ - S⁻¹ = (S - R) * (R⁻¹ * S⁻¹) := by field_simp
  rw [heq, abs_mul,
    abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hRp.le) (inv_nonneg.mpr hSp.le)), abs_sub_comm S R]
  calc
    _ ≤ |R - S| * (ell⁻¹ * ell⁻¹) := mul_le_mul_of_nonneg_left
      (mul_le_mul hRi hSi (inv_nonneg.mpr hSp.le) (inv_nonneg.mpr he.le)) (abs_nonneg _)
    _ = ell⁻¹ ^ 2 * |R - S| := by ring

/-- The normalized scalar remainder is bounded uniformly by the displayed
arithmetic expression. It depends only on `ell,U,D`, independently of `c,a,L`
and the candidate; no second derivative is used. -/
theorem picardScalarRemainder_norm_le (ell U D : ℝ) (he : 0 < ell) (hU : 0 ≤ U) (hD : 0 ≤ D)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hbound : ∀ q, |(z.1.1 q).1| ≤ U) (hj : ∀ q, ‖(z.1.2 q).2‖ ≤ D) :
    ‖picardScalarRemainder ell he z hl‖ ≤ ell⁻¹ * (U * D / 2) := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro p
  have hR := picardRadialAverage_lower (picardLamValues z) hl p
  have hRp : 0 < picardRadialAverage (picardLamValues z) p := he.trans_le hR
  have hRi : (picardRadialAverage (picardLamValues z) p)⁻¹ ≤ ell⁻¹ :=
    (inv_le_inv₀ hRp he).mpr hR
  change ‖(picardRadialAverage (picardLamValues z) p)⁻¹ •
    picardRadialBilinear (picardLamValues z) (picardHJets z) p‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hRp.le)]
  exact mul_le_mul hRi (picardRadialBilinear_norm_le _ _ hU hD hbound hj p)
    (norm_nonneg _) (inv_nonneg.mpr he.le)

/-- The normalized remainder has the displayed uniform Lipschitz constant,
depending only on `ell,U,D`, independently of the wedge and the candidates. -/
theorem picardScalarRemainder_dist_le (ell U D : ℝ) (he : 0 < ell) (hU : 0 ≤ U) (hD : 0 ≤ D)
    (z w : PicardCarrier c a L (ℝ × ℂ))
    (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1)
    (_hz : ∀ q, |(z.1.1 q).1| ≤ U) (hw : ∀ q, |(w.1.1 q).1| ≤ U)
    (hjz : ∀ q, ‖(z.1.2 q).2‖ ≤ D) (hjw : ∀ q, ‖(w.1.2 q).2‖ ≤ D) :
    dist (picardScalarRemainder ell he z hlz) (picardScalarRemainder ell he w hlw) ≤
      (ell⁻¹ * ((D + U) / 2) + ell⁻¹ ^ 2 * (U * D / 2)) * dist z w := by
  have hFn (f : PicardCarrier c a L (ℝ × ℂ)) (hf : ∀ q, |(f.1.1 q).1| ≤ U) :
      ‖picardLamValues f‖ ≤ U := (ContinuousMap.norm_le _ hU).mpr (by
      intro q
      simpa only [picardLamValues, ContinuousMap.coe_mk, Real.norm_eq_abs] using hf q)
  have hGn (f : PicardCarrier c a L (ℝ × ℂ)) (hf : ∀ q, ‖(f.1.2 q).2‖ ≤ D) :
      ‖picardHJets f‖ ≤ D := (ContinuousMap.norm_le _ hD).mpr hf
  have hJ := picardRadialBilinear_dist_le (picardLamValues z) (picardLamValues w)
    (picardHJets z) (picardHJets w)
  have hJb : dist (picardRadialBilinear (picardLamValues z) (picardHJets z))
      (picardRadialBilinear (picardLamValues w) (picardHJets w)) ≤ ((D + U) / 2) * dist z w := by
    calc
      _ ≤ (dist z w * D + U * dist z w) / 2 := hJ.trans (by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact add_le_add
          (mul_le_mul (picardLamValues_dist_le z w) (hGn z hjz) (norm_nonneg _) dist_nonneg)
          (mul_le_mul (hFn w hw) (picardHJets_dist_le z w) dist_nonneg hU))
      _ = _ := by ring
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro p
  let R := picardRadialAverage (picardLamValues z) p
  let S := picardRadialAverage (picardLamValues w) p
  let J := picardRadialBilinear (picardLamValues z) (picardHJets z) p
  let K := picardRadialBilinear (picardLamValues w) (picardHJets w) p
  have hR : ell ≤ R := picardRadialAverage_lower _ hlz p
  have hS : ell ≤ S := picardRadialAverage_lower _ hlw p
  have hRp : 0 < R := he.trans_le hR
  have hRi : |R⁻¹| ≤ ell⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr hRp)]
    exact (inv_le_inv₀ hRp he).mpr hR
  have hRS : |R - S| ≤ dist z w :=
    (ContinuousMap.dist_apply_le_dist p).trans
      ((picardRadialAverage_dist_le _ _).trans (picardLamValues_dist_le z w))
  have hI : |R⁻¹ - S⁻¹| ≤ ell⁻¹ ^ 2 * dist z w :=
    (picard_inv_sub_le_aux he hR hS).trans (mul_le_mul_of_nonneg_left hRS (sq_nonneg _))
  have hK : ‖K‖ ≤ U * D / 2 := picardRadialBilinear_norm_le _ _ hU hD hw hjw p
  have hJK : ‖J - K‖ ≤ ((D + U) / 2) * dist z w :=
    by simpa only [dist_eq_norm, J, K] using (ContinuousMap.dist_apply_le_dist p).trans hJb
  have heq : R⁻¹ • J - S⁻¹ • K = R⁻¹ • (J - K) + (R⁻¹ - S⁻¹) • K := by
    rw [smul_sub, sub_smul]; abel
  rw [dist_eq_norm]
  change ‖R⁻¹ • J - S⁻¹ • K‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖R⁻¹ • (J - K)‖ + ‖(R⁻¹ - S⁻¹) • K‖ := norm_add_le _ _
    _ ≤ ell⁻¹ * (((D + U) / 2) * dist z w) + (ell⁻¹ ^ 2 * dist z w) * (U * D / 2) := by
      simp only [norm_smul, Real.norm_eq_abs]
      exact add_le_add
        (mul_le_mul hRi hJK (norm_nonneg _) (inv_nonneg.mpr he.le))
        (mul_le_mul hI hK (norm_nonneg _) (mul_nonneg (sq_nonneg _) dist_nonneg))
    _ = _ := by ring

private theorem picard_smul_sub_le_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r s : ℝ) (x y : E) :
    ‖r • x - s • y‖ ≤ |r| * ‖x - y‖ + |r - s| * ‖y‖ := by
  have heq : r • x - s • y = r • (x - y) + (r - s) • y := by
    rw [smul_sub, sub_smul]; abel
  rw [heq]
  simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le (r • (x - y)) ((r - s) • y)

/-- Scalar values have the displayed uniform Lipschitz bound, depending only
on `ell,U,D,L`, independently of `c,a` and both candidates. -/
theorem picardPhiValues_dist_le (ell U D : ℝ) (he : 0 < ell) (hU : 0 ≤ U) (hD : 0 ≤ D)
    (z w : PicardCarrier c a L (ℝ × ℂ))
    (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1)
    (hz : ∀ q, |(z.1.1 q).1| ≤ U) (hw : ∀ q, |(w.1.1 q).1| ≤ U)
    (hjz : ∀ q, ‖(z.1.2 q).2‖ ≤ D) (hjw : ∀ q, ‖(w.1.2 q).2‖ ≤ D) (hL : 0 ≤ L) :
    dist (picardPhiValues ell he z hlz) (picardPhiValues ell he w hlw) ≤
      (1 + L * (ell⁻¹ * ((D + U) / 2) + ell⁻¹ ^ 2 * (U * D / 2))) * dist z w := by
  let C := ell⁻¹ * ((D + U) / 2) + ell⁻¹ ^ 2 * (U * D / 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hF := picardScalarRemainder_dist_le ell U D he hU hD z w hlz hlw hz hw hjz hjw
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro p
  have hx : 0 ≤ p.1.2 - p.1.1 := sub_nonneg.mpr p.2.1.2.1
  have hxL : p.1.2 - p.1.1 ≤ L := by linarith [p.2.1.1, p.2.1.2.2]
  have hV : ‖(z.1.1 p).2 - (w.1.1 p).2‖ ≤ dist z w :=
    by
      have hv := picardCarrier_dist_value_le z w p
      rw [Prod.dist_eq, max_le_iff, Real.dist_eq, dist_eq_norm] at hv
      exact hv.2
  have hFp : ‖picardScalarRemainder ell he z hlz p - picardScalarRemainder ell he w hlw p‖ ≤
      C * dist z w := by
    simpa only [dist_eq_norm, C] using (ContinuousMap.dist_apply_le_dist p).trans hF
  rw [dist_eq_norm]
  change ‖((z.1.1 p).2 - (p.1.2 - p.1.1) • picardScalarRemainder ell he z hlz p) -
    ((w.1.1 p).2 - (p.1.2 - p.1.1) • picardScalarRemainder ell he w hlw p)‖ ≤ _
  have hEq : ((z.1.1 p).2 - (p.1.2 - p.1.1) • picardScalarRemainder ell he z hlz p) -
      ((w.1.1 p).2 - (p.1.2 - p.1.1) • picardScalarRemainder ell he w hlw p) =
      ((z.1.1 p).2 - (w.1.1 p).2) - (p.1.2 - p.1.1) •
        (picardScalarRemainder ell he z hlz p - picardScalarRemainder ell he w hlw p) := by
    rw [smul_sub]; abel
  rw [hEq]
  calc
    _ ≤ ‖(z.1.1 p).2 - (w.1.1 p).2‖ +
      ‖(p.1.2 - p.1.1) • (picardScalarRemainder ell he z hlz p -
        picardScalarRemainder ell he w hlw p)‖ := norm_sub_le _ _
    _ ≤ dist z w + L * (C * dist z w) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx]
      exact add_le_add hV (mul_le_mul hxL hFp (norm_nonneg _) hL)
    _ = _ := by dsimp only [C]; ring

/-- Scalar outgoing jets have the displayed uniform Lipschitz bound,
depending only on `ell,U,D`, independently of the wedge and both candidates. -/
theorem picardPhiJets_dist_le (ell U D : ℝ) (he : 0 < ell) (hU : 0 ≤ U) (hD : 0 ≤ D)
    (z w : PicardCarrier c a L (ℝ × ℂ))
    (hlz : ∀ q, ell ≤ (z.1.1 q).1) (hlw : ∀ q, ell ≤ (w.1.1 q).1)
    (hz : ∀ q, |(z.1.1 q).1| ≤ U) (hw : ∀ q, |(w.1.1 q).1| ≤ U)
    (hjz : ∀ q, ‖(z.1.2 q).2‖ ≤ D) (hjw : ∀ q, ‖(w.1.2 q).2‖ ≤ D) :
    dist (picardPhiJets ell he z hlz) (picardPhiJets ell he w hlw) ≤
      (U * ell⁻¹ * (ell⁻¹ * ((D + U) / 2) + ell⁻¹ ^ 2 * (U * D / 2)) +
        (ell⁻¹ + U * ell⁻¹ ^ 2) * (ell⁻¹ * (U * D / 2))) * dist z w := by
  let C := ell⁻¹ * ((D + U) / 2) + ell⁻¹ ^ 2 * (U * D / 2)
  let B := ell⁻¹ * (U * D / 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF := picardScalarRemainder_dist_le ell U D he hU hD z w hlz hlw hz hw hjz hjw
  have hFn := picardScalarRemainder_norm_le ell U D he hU hD w hlw hw hjw
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro p
  let R := picardRadialAverage (picardLamValues z) p
  let S := picardRadialAverage (picardLamValues w) p
  have hR : ell ≤ R := picardRadialAverage_lower _ hlz p
  have hS : ell ≤ S := picardRadialAverage_lower _ hlw p
  have hRp : 0 < R := he.trans_le hR
  have hSp : 0 < S := he.trans_le hS
  have hRi : |R⁻¹| ≤ ell⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr hRp)]
    exact (inv_le_inv₀ hRp he).mpr hR
  have hSi : |S⁻¹| ≤ ell⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr hSp)]
    exact (inv_le_inv₀ hSp he).mpr hS
  have hRS : |R - S| ≤ dist z w :=
    (ContinuousMap.dist_apply_le_dist p).trans
      ((picardRadialAverage_dist_le _ _).trans (picardLamValues_dist_le z w))
  have hI : |R⁻¹ - S⁻¹| ≤ ell⁻¹ ^ 2 * dist z w :=
    (picard_inv_sub_le_aux he hR hS).trans (mul_le_mul_of_nonneg_left hRS (sq_nonneg _))
  have hV : |(z.1.1 p).1 - (w.1.1 p).1| ≤ dist z w :=
    (le_max_left _ _).trans (picardCarrier_dist_value_le z w p)
  have hFac : |(z.1.1 p).1 / R| ≤ U * ell⁻¹ := by
    rw [div_eq_mul_inv, abs_mul]
    exact mul_le_mul (hz p) hRi (abs_nonneg _) hU
  have hFacD : |(z.1.1 p).1 / R - (w.1.1 p).1 / S| ≤
      (ell⁻¹ + U * ell⁻¹ ^ 2) * dist z w := by
    have heq : (z.1.1 p).1 / R - (w.1.1 p).1 / S =
        R⁻¹ * ((z.1.1 p).1 - (w.1.1 p).1) + (R⁻¹ - S⁻¹) * (w.1.1 p).1 :=
            by simp only [div_eq_mul_inv]; ring
    rw [heq]
    calc
      _ ≤ |R⁻¹ * ((z.1.1 p).1 - (w.1.1 p).1)| + |(R⁻¹ - S⁻¹) * (w.1.1 p).1| := abs_add_le _ _
      _ ≤ ell⁻¹ * dist z w + (ell⁻¹ ^ 2 * dist z w) * U := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul hRi hV (abs_nonneg _) (inv_nonneg.mpr he.le))
          (mul_le_mul hI (hw p) (abs_nonneg _) (by positivity))
      _ = _ := by ring
  have hFp : ‖picardScalarRemainder ell he z hlz p - picardScalarRemainder ell he w hlw p‖ ≤
      C * dist z w := by
    simpa only [dist_eq_norm, C] using (ContinuousMap.dist_apply_le_dist p).trans hF
  have hFnp : ‖picardScalarRemainder ell he w hlw p‖ ≤ B :=
    ((picardScalarRemainder ell he w hlw).norm_coe_le_norm p).trans hFn
  rw [dist_eq_norm]
  change ‖((z.1.1 p).1 / R) • picardScalarRemainder ell he z hlz p -
      ((w.1.1 p).1 / S) • picardScalarRemainder ell he w hlw p‖ ≤ _
  calc
    _ ≤ |(z.1.1 p).1 / R| * ‖picardScalarRemainder ell he z hlz p -
        picardScalarRemainder ell he w hlw p‖ +
        |(z.1.1 p).1 / R - (w.1.1 p).1 / S| * ‖picardScalarRemainder ell he w hlw p‖ :=
      picard_smul_sub_le_aux _ _ _ _
    _ ≤ (U * ell⁻¹) * (C * dist z w) + ((ell⁻¹ + U * ell⁻¹ ^ 2) * dist z w) * B :=
      add_le_add (mul_le_mul hFac hFp (norm_nonneg _) (by positivity))
        (mul_le_mul hFacD hFnp (norm_nonneg _) (by positivity))
    _ = _ := by dsimp only [B, C]; ring

/-- Scalar values are bounded by a constant depending only on `ell,U,D,H,L`,
uniformly in `c,a` and the candidate. The estimate includes the axis. -/
theorem picardPhiValues_norm_le (ell U D H : ℝ) (he : 0 < ell) (hU : 0 ≤ U)
    (hD : 0 ≤ D) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hz : ∀ q, |(z.1.1 q).1| ≤ U) (hj : ∀ q, ‖(z.1.2 q).2‖ ≤ D)
    (hh : ∀ q, ‖(z.1.1 q).2‖ ≤ H) :
    ‖picardPhiValues ell he z hl‖ ≤ H + L * (ell⁻¹ * (U * D / 2)) := by
  have hn := picardScalarRemainder_norm_le ell U D he hU hD z hl hz hj
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro p
  have hx : 0 ≤ p.1.2 - p.1.1 := sub_nonneg.mpr p.2.1.2.1
  have hxL : p.1.2 - p.1.1 ≤ L := by linarith [p.2.1.1, p.2.1.2.2]
  change ‖(z.1.1 p).2 - (p.1.2 - p.1.1) • picardScalarRemainder ell he z hl p‖ ≤ _
  refine (norm_sub_le _ _).trans (add_le_add (hh p) ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx]
  exact mul_le_mul hxL (((picardScalarRemainder ell he z hl).norm_coe_le_norm p).trans hn)
    (norm_nonneg _) hL

/-- Scalar outgoing jets are bounded by a constant depending only on
`ell,U,D`, uniformly in the wedge and the candidate, including the axis. -/
theorem picardPhiJets_norm_le (ell U D : ℝ) (he : 0 < ell) (hU : 0 ≤ U) (hD : 0 ≤ D)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hz : ∀ q, |(z.1.1 q).1| ≤ U) (hj : ∀ q, ‖(z.1.2 q).2‖ ≤ D) :
    ‖picardPhiJets ell he z hl‖ ≤ (U * ell⁻¹) * (ell⁻¹ * (U * D / 2)) := by
  have hn := picardScalarRemainder_norm_le ell U D he hU hD z hl hz hj
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro p
  have hR := picardRadialAverage_lower (picardLamValues z) hl p
  have hRp : 0 < picardRadialAverage (picardLamValues z) p := he.trans_le hR
  have hRi : (picardRadialAverage (picardLamValues z) p)⁻¹ ≤ ell⁻¹ :=
    (inv_le_inv₀ hRp he).mpr hR
  change ‖((z.1.1 p).1 / picardRadialAverage (picardLamValues z) p) •
    picardScalarRemainder ell he z hl p‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, div_eq_mul_inv, abs_mul, abs_of_pos (inv_pos.mpr hRp)]
  exact mul_le_mul (mul_le_mul (hz p) hRi (inv_nonneg.mpr hRp.le) hU)
    (((picardScalarRemainder ell he z hl).norm_coe_le_norm p).trans hn)
    (norm_nonneg _) (by positivity)

end EmcsfAcExtension.Local
