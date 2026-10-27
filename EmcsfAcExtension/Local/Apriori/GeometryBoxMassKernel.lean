module

public import Mathlib
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Infra.Triangle
import EmcsfAcExtension.Infra.AC.Primitive

/-! # A positive radial mass average with a matching quadratic budget

The weighted mass estimate is a one-dimensional consequence of the radial
average kernel. The incoming application reverses its null parameter before
using this lemma, preserving the axis endpoint of the mass constraint.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- A radius reconstructed as the primitive of a continuous characteristic
weight is continuous through its axis endpoint. -/
private theorem mass_radius_continuous_aux {a b : ℝ} {w r : ℝ → ℝ}
    (hab : a ≤ b) (hw : ContinuousOn w (Icc a b))
    (hr : ∀ x ∈ Icc a b, r x = ∫ y in a..x, w y) : ContinuousOn r (Icc a b) := by
  have hi := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hw
  have hp := hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc |>.continuousOn
  rw [uIcc_of_le hab] at hp
  exact hp.congr hr

private theorem mass_inverse_square_kernel_aux {a b y : ℝ} {w r : ℝ → ℝ}
    (hab : a ≤ b) (hw : ContinuousOn w (Icc a b))
    (hr : ∀ x ∈ Icc a b, r x = ∫ z in a..x, w z)
    (hrpos : ∀ x ∈ Ioc a b, 0 < r x) (hy : y ∈ Ioc a b) :
    IntervalIntegrable (fun x => w x / r x ^ 2) volume y b ∧
      (∫ x in y..b, w x / r x ^ 2) ≤ 1 / r y := by
  have iw := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab hw
  have cr := mass_radius_continuous_aux hab hw hr
  have hd x (hx : x ∈ Ioo a b) : HasDerivAt r (w x) x := by
    apply hasDerivAt_of_integralForm_interior hx (hw.mono Ioo_subset_Icc_self)
    intro c d hc hcd hd
    have hc' : c ∈ Icc a b := ⟨hc.le, hcd.trans hd.le⟩
    have hd' : d ∈ Icc a b := ⟨hc.le.trans hcd, hd.le⟩
    refine ⟨iw.mono_set (uIcc_subset_uIcc (Icc_subset_uIcc hc') (Icc_subset_uIcc hd')), ?_⟩
    rw [hr d hd', hr c hc']
    exact intervalIntegral.integral_interval_sub_left
      (iw.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hd')))
      (iw.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hc')))
  have hsub : Icc y b ⊆ Icc a b := Icc_subset_Icc hy.1.le le_rfl
  have hpos x (hx : x ∈ Icc y b) : 0 < r x := hrpos x ⟨hy.1.trans_le hx.1, hx.2⟩
  have ci : ContinuousOn (fun x => w x / r x ^ 2) (Icc y b) :=
    (hw.mono hsub).div ((cr.mono hsub).pow 2) (fun x hx => pow_ne_zero 2 (hpos x hx).ne')
  have ii := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hy.2 ci
  have cf : ContinuousOn (fun x => -(r x)⁻¹) (Icc y b) :=
    ((cr.mono hsub).inv₀ (fun x hx => (hpos x hx).ne')).neg
  have df x (hx : x ∈ Ioo y b) : HasDerivAt (fun x => -(r x)⁻¹) (w x / r x ^ 2) x := by
    have hd' := ((hd x ⟨hy.1.trans hx.1, hx.2⟩).inv
      (hpos x ⟨hx.1.le, hx.2.le⟩).ne').neg
    simpa only [neg_div, neg_neg] using! hd'
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hy.2 cf df ii
  refine ⟨ii, ?_⟩
  rw [hi]
  have hbpos := hpos b (right_mem_Icc.mpr hy.2)
  calc
    _ = (r y)⁻¹ - (r b)⁻¹ := by ring
    _ ≤ (r y)⁻¹ := sub_le_self _ (inv_nonneg.mpr hbpos.le)
    _ = _ := by rw [one_div]

private theorem mass_interval_extension_measurable_aux {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) : Measurable ((Icc a b).indicator f) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact hf.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) measurableSet_Icc

/-- The mass-average Hardy inequality with the exact universal coefficient one,
written in the original increasing characteristic label. Both sides may be
infinite. The weight and continuous nonnegative trace require no derivative
envelope; the radius is their actual primitive. -/
private theorem mass_average_lintegral_aux {a b : ℝ} {w r F : ℝ → ℝ}
    (hab : a ≤ b) (hw : ContinuousOn w (Icc a b))
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hr : ∀ x ∈ Icc a b, r x = ∫ y in a..x, w y)
    (hrpos : ∀ x ∈ Ioc a b, 0 < r x)
    (hF : ContinuousOn F (Icc a b)) (hF0 : ∀ x ∈ Icc a b, 0 ≤ F x) :
    (∫⁻ x in Icc a b, ENNReal.ofReal
      (w x / r x ^ 2 * ∫ y in a..x, w y * F y)) ≤
      ∫⁻ x in Icc a b, ENNReal.ofReal (w x / r x * F x) := by
  classical
  let W := (Icc a b).indicator w
  let R := (Icc a b).indicator r
  let G := (Icc a b).indicator F
  let K := fun p : ℝ × ℝ => ENNReal.ofReal (W p.1 * G p.1) *
    ENNReal.ofReal (W p.2 / R p.2 ^ 2)
  have cr := mass_radius_continuous_aux hab hw hr
  have hW := mass_interval_extension_measurable_aux hw
  have hR := mass_interval_extension_measurable_aux cr
  have hG := mass_interval_extension_measurable_aux hF
  have hK : Measurable K := by dsimp [K, W, R, G] at *; fun_prop
  have iWF := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab (hw.mul hF)
  have hswap := lintegral_lintegral_swap_triangle (a := a) (b := b) hK
  calc
    _ = ∫⁻ x in Icc a b, ∫⁻ y in Icc a x, K (y, x) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro x hx
      have hxsub := uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hx)
      have iy := (intervalIntegrable_iff_integrableOn_Icc_of_le hx.1).mp (iWF.mono_set hxsub)
      change IntegrableOn (fun y => w y * F y) (Icc a x) at iy
      have hy0 : 0 ≤ᵐ[volume.restrict (Icc a x)] fun y => w y * F y := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        exact mul_nonneg (hw0 y ⟨hy.1, hy.2.trans hx.2⟩) (hF0 y ⟨hy.1, hy.2.trans hx.2⟩)
      symm
      calc
        _ = ∫⁻ y in Icc a x, ENNReal.ofReal (w x / r x ^ 2) * ENNReal.ofReal (w y * F y) := by
          apply setLIntegral_congr_fun measurableSet_Icc
          intro y hy
          have hy' : y ∈ Icc a b := ⟨hy.1, hy.2.trans hx.2⟩
          simp only [K, W, R, G, indicator_of_mem hx, indicator_of_mem hy', mul_comm]
        _ = ENNReal.ofReal (w x / r x ^ 2) * ∫⁻ y in Icc a x, ENNReal.ofReal (w y * F y) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal (w x / r x ^ 2) * ENNReal.ofReal (∫ y in a..x, w y * F y) := by
          rw [← ofReal_integral_eq_lintegral_ofReal iy hy0,
            integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hx.1]
        _ = _ := (ENNReal.ofReal_mul (div_nonneg (hw0 x hx) (sq_nonneg _))).symm
    _ = ∫⁻ y in Icc a b, ∫⁻ x in Icc y b, K (y, x) := hswap.symm
    _ ≤ _ := by
      apply lintegral_mono_ae
      have hne : ∀ᵐ y : ℝ, y ≠ a := by simp [ae_iff]
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with y hy hya
      have hy' : y ∈ Ioc a b := ⟨lt_of_le_of_ne hy.1 (Ne.symm hya), hy.2⟩
      obtain ⟨ii, hkernel⟩ := mass_inverse_square_kernel_aux hab hw hr hrpos hy'
      have iicc := (intervalIntegrable_iff_integrableOn_Icc_of_le hy.2).mp ii
      have hn : 0 ≤ᵐ[volume.restrict (Icc y b)] fun x => w x / r x ^ 2 := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact div_nonneg (hw0 x ⟨hy.1.trans hx.1, hx.2⟩) (sq_nonneg _)
      have hinner : (∫⁻ x in Icc y b, ENNReal.ofReal (w x / r x ^ 2)) ≤
          ENNReal.ofReal (1 / r y) := by
        rw [← ofReal_integral_eq_lintegral_ofReal iicc hn,
          integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hy.2]
        exact ENNReal.ofReal_le_ofReal hkernel
      calc
        _ = ∫⁻ x in Icc y b, ENNReal.ofReal (w y * F y) * ENNReal.ofReal (w x / r x ^ 2) := by
          apply setLIntegral_congr_fun measurableSet_Icc
          intro x hx
          have hx' : x ∈ Icc a b := ⟨hy.1.trans hx.1, hx.2⟩
          simp only [K, W, R, G, indicator_of_mem hy, indicator_of_mem hx']
        _ = ENNReal.ofReal (w y * F y) * ∫⁻ x in Icc y b, ENNReal.ofReal (w x / r x ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (w y * F y) * ENNReal.ofReal (1 / r y) := by gcongr
        _ = ENNReal.ofReal (w y / r y * F y) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg (hw0 y hy) (hF0 y hy))]
          congr 1
          ring

/-- The real mass-average Hardy inequality, with exact universal coefficient
one. Integrability at the axis is proved from the matching Hardy integral. -/
private theorem mass_average_integral_aux {a b : ℝ} {w r F : ℝ → ℝ}
    (hab : a ≤ b) (hw : ContinuousOn w (Icc a b))
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hr : ∀ x ∈ Icc a b, r x = ∫ y in a..x, w y)
    (hrpos : ∀ x ∈ Ioc a b, 0 < r x)
    (hF : ContinuousOn F (Icc a b)) (hF0 : ∀ x ∈ Icc a b, 0 ≤ F x)
    (hHardy : IntervalIntegrable (fun x => w x / r x * F x) volume a b) :
    IntervalIntegrable (fun x => w x / r x ^ 2 * ∫ y in a..x, w y * F y) volume a b ∧
      (∫ x in a..b, w x / r x ^ 2 * ∫ y in a..x, w y * F y) ≤ ∫ x in a..b, w x / r x * F x := by
  let N := fun x => w x / r x ^ 2 * ∫ y in a..x, w y * F y
  have cr := mass_radius_continuous_aux hab hw hr
  have hr0 x (hx : x ∈ Icc a b) : 0 ≤ r x := by
    rw [hr x hx]
    exact intervalIntegral.integral_nonneg hx.1 (fun y hy => hw0 y ⟨hy.1, hy.2.trans hx.2⟩)
  have hN0 x (hx : x ∈ Icc a b) : 0 ≤ N x :=
    mul_nonneg (div_nonneg (hw0 x hx) (sq_nonneg _))
      (intervalIntegral.integral_nonneg hx.1 (fun y hy =>
        mul_nonneg (hw0 y ⟨hy.1, hy.2.trans hx.2⟩) (hF0 y ⟨hy.1, hy.2.trans hx.2⟩)))
  have hNae : 0 ≤ᵐ[volume.restrict (Icc a b)] N :=
    (ae_restrict_mem measurableSet_Icc).mono fun x hx => hN0 x hx
  have hHae : 0 ≤ᵐ[volume.restrict (Icc a b)] fun x => w x / r x * F x :=
    (ae_restrict_mem measurableSet_Icc).mono fun x hx => mul_nonneg
      (div_nonneg (hw0 x hx) (hr0 x hx)) (hF0 x hx)
  have iH := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hHardy
  have hbound := mass_average_lintegral_aux hab hw hw0 hr hrpos hF hF0
  rw [← ofReal_integral_eq_lintegral_ofReal iH hHae] at hbound
  have iWF := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hab (hw.mul hF)
  have cp := iWF.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc |>.continuousOn
  rw [uIcc_of_le hab] at cp
  have hNmeas : AEStronglyMeasurable N (volume.restrict (Icc a b)) :=
    ((hw.aestronglyMeasurable (μ := volume) measurableSet_Icc).div₀
      ((cr.pow 2).aestronglyMeasurable (μ := volume) measurableSet_Icc)).mul
        (cp.aestronglyMeasurable (μ := volume) measurableSet_Icc)
  have hn : (∫⁻ x in Icc a b, ‖N x‖ₑ) = ∫⁻ x in Icc a b, ENNReal.ofReal (N x) := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro x hx
    exact Real.enorm_of_nonneg (hN0 x hx)
  have iN : IntegrableOn N (Icc a b) := by
    refine ⟨hNmeas, ?_⟩
    change (∫⁻ x in Icc a b, ‖N x‖ₑ) < ⊤
    rw [hn]
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  rw [← ofReal_integral_eq_lintegral_ofReal iN hNae] at hbound
  have hreal := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hHae)).mp hbound
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab] at hreal
  exact ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr iN, hreal⟩


/-- A positive radial constraint density dominated by `‖z‖² + B r²`
has weighted mass budget at most its matching scalar quadratic budget plus
`B r(b)²/2`. The exact coefficients one and one half are universal in all
functions and interval parameters. Integrability is proved before using
either real integral; the radial average is the literal constraint premise. -/
theorem weighted_mass_of_constraint_density {a b B : ℝ}
    {w r F μ : ℝ → ℝ} {z : ℝ → ℂ}
    (hab : a ≤ b) (_hB : 0 ≤ B) (cw : ContinuousOn w (Icc a b))
    (cr : ContinuousOn r (Icc a b)) (cF : ContinuousOn F (Icc a b))
    (hw : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hr0 : ∀ x ∈ Icc a b, 0 ≤ r x)
    (hr : ∀ x ∈ Icc a b, r x = ∫ y in a..x, w y)
    (hrpos : ∀ x ∈ Ioc a b, 0 < r x)
    (hF0 : ∀ x ∈ Icc a b, 0 ≤ F x)
    (hF : ∀ x ∈ Icc a b, F x ≤ ‖z x‖ ^ 2 + B * r x ^ 2)
    (hμ : ∀ x ∈ Icc a b, μ x = (r x)⁻¹ * ∫ y in a..x, w y * F y)
    (hz : IntervalIntegrable (fun x => w x / r x * ‖z x‖ ^ 2) volume a b)
    (hmoment : (∫ x in a..b, w x * r x) = r b ^ 2 / 2) :
    IntervalIntegrable (fun x => w x / r x * μ x) volume a b ∧
      (∫ x in a..b, w x / r x * μ x) ≤
        (∫ x in a..b, w x / r x * ‖z x‖ ^ 2) + B * r b ^ 2 / 2 := by
  let P := fun x => w x / r x * F x
  let Q := fun x => w x / r x * ‖z x‖ ^ 2 + B * (w x * r x)
  have iw : IntervalIntegrable (fun x => w x * r x) volume a b :=
    (cw.mul cr).intervalIntegrable_of_Icc hab
  have iQ : IntervalIntegrable Q volume a b := hz.add (iw.const_mul B)
  have hW (x : ℝ) (hx : x ∈ Icc a b) : 0 ≤ w x / r x :=
    div_nonneg (hw x hx) (hr0 x hx)
  have hP0 (x : ℝ) (hx : x ∈ Icc a b) : 0 ≤ P x := mul_nonneg (hW x hx) (hF0 x hx)
  have hPQ (x : ℝ) (hx : x ∈ Icc a b) : P x ≤ Q x := by
    apply (mul_le_mul_of_nonneg_left (hF x hx) (hW x hx)).trans_eq
    dsimp only [Q]
    by_cases hx0 : r x = 0
    · simp only [hx0, div_zero, zero_mul, mul_zero, add_zero]
    · field_simp [hx0]
  have iP : IntegrableOn P (Icc a b) := by
    apply ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp iQ).mono'
      ((((cw.aestronglyMeasurable (μ := volume) measurableSet_Icc).div₀
        (cr.aestronglyMeasurable (μ := volume) measurableSet_Icc)).mul
          (cF.aestronglyMeasurable (μ := volume) measurableSet_Icc)))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    change ‖P x‖ ≤ Q x
    rw [Real.norm_eq_abs, abs_of_nonneg (hP0 x hx)]
    exact hPQ x hx
  have iP' := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr iP
  have hk := mass_average_integral_aux hab cw hw hr hrpos cF hF0 iP'
  have heq (x : ℝ) (hx : x ∈ Icc a b) :
      w x / r x * μ x = w x / r x ^ 2 * ∫ y in a..x, w y * F y := by
    rw [hμ x hx]
    by_cases hx0 : r x = 0
    · simp [hx0]
    · field_simp [hx0]
  have iμ : IntervalIntegrable (fun x => w x / r x * μ x) volume a b := by
    apply hk.1.congr
    intro x hx
    exact (heq x (by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hx)).symm
  refine ⟨iμ, ?_⟩
  have hi : (∫ x in a..b, w x / r x * μ x) =
      ∫ x in a..b, w x / r x ^ 2 * ∫ y in a..x, w y * F y := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact heq x (by simpa only [uIcc_of_le hab] using hx)
  rw [hi]
  apply hk.2.trans
  apply le_trans (b := ∫ x in a..b, Q x)
  · exact intervalIntegral.integral_mono_on hab iP' iQ hPQ
  · rw [intervalIntegral.integral_add hz (iw.const_mul B),
      intervalIntegral.integral_const_mul, hmoment]
    exact le_of_eq (by ring)

end EmcsfAcExtension.Local
