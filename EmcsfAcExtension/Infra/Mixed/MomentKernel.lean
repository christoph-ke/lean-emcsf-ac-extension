module

public import EmcsfAcExtension.Infra.RadialKernel
public import EmcsfAcExtension.Infra.Triangle
public import EmcsfAcExtension.Infra.AC.Rpow

/-!
# Radial moment kernels

Auxiliary analysis A4, display (A4), of internal project record.
The exact constant is `1 / p` for every positive real exponent, independent
of the radius, weight, section, or forcing. Forcings may have infinite mass.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Mixed

/-- The radial power density is integrable above a positive initial radius.
Its exact primitive has coefficient `1 / p`, depending only on the exponent. -/
theorem integral_radial_rpow_eq {r w : ℝ → ℝ} {a b p : ℝ}
    (hab : a ≤ b) (hp : 0 < p) (hr : AbsolutelyContinuousOnInterval r a b)
    (hra : 0 < r a) (hm : MonotoneOn r (Icc a b))
    (hd : ∀ᵐ x ∂volume.restrict (Icc a b), deriv r x = w x) :
    IntervalIntegrable (fun x => w x / (r x) ^ (1 + p)) volume a b ∧
      (∫ x in a..b, w x / (r x) ^ (1 + p)) =
        (((r a) ^ p)⁻¹ - ((r b) ^ p)⁻¹) / p := by
  have hlo : ∀ x ∈ uIcc a b, r a ≤ r x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact hm ⟨le_rfl, hab⟩ hx hx.1
  have hpow := hr.rpow_of_monotoneOn (by simpa only [uIcc_of_le hab] using hm) hp
  have hi := hpow.inv_of_le_norm (Real.rpow_pos_of_pos hra p) (fun x hx =>
    (Real.rpow_le_rpow hra.le (hlo x hx) hp.le).trans (le_abs_self _))
  have hH : AbsolutelyContinuousOnInterval (fun x => (-1 / p) * ((r x) ^ p)⁻¹) a b := by
    simpa only [smul_eq_mul] using! hi.const_smul (-1 / p : ℝ)
  have hder : ∀ᵐ x, x ∈ uIcc a b →
      HasDerivAt (fun y => (-1 / p) * ((r y) ^ p)⁻¹) (w x / (r x) ^ (1 + p)) x := by
    have hd' := (ae_restrict_iff' measurableSet_Icc).mp hd
    filter_upwards [hr.ae_differentiableAt, hd'] with x hx hdx hmem
    have hrx : 0 < r x := hra.trans_le (hlo x hmem)
    have hpx : (r x) ^ p ≠ 0 := (Real.rpow_pos_of_pos hrx p).ne'
    have hdx' := hdx (by simpa only [uIcc_of_le hab] using hmem)
    have hdH := ((((hx hmem).hasDerivAt.rpow_const (Or.inl hrx.ne')).inv hpx).const_mul
      (-1 / p : ℝ))
    have hdH' : HasDerivAt (fun y => (-1 / p) * ((r y) ^ p)⁻¹)
        ((-1 / p) * (-(deriv r x * p * (r x) ^ (p - 1)) / ((r x) ^ p) ^ 2)) x := by
      simpa only [Pi.inv_apply] using! hdH
    convert hdH' using 1
    rw [hdx', Real.rpow_sub_one hrx.ne', Real.rpow_add hrx 1 p, Real.rpow_one]
    field_simp
  constructor
  · apply hH.intervalIntegrable_deriv.congr_ae
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    filter_upwards [hder] with x hx hmem
    exact (hx (uIoc_subset_uIcc hmem)).deriv
  · rw [hH.integral_eq_sub_of_ae_hasDerivAt_real hder]
    ring

/-- A4 radial moment kernels have mass at most `1 / p` above each positive
initial radius. The bound is uniform in all section endpoints and radial weights. -/
theorem lintegral_radial_moment_mass_le {r w : ℝ → ℝ} {a b p : ℝ}
    (hab : a ≤ b) (hp : 0 < p) (hr : AbsolutelyContinuousOnInterval r a b)
    (hra : 0 < r a) (hm : MonotoneOn r (Icc a b))
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hd : ∀ᵐ x ∂volume.restrict (Icc a b), deriv r x = w x) :
    (∫⁻ t in Icc a b, ENNReal.ofReal (w t / r t) *
      ENNReal.ofReal ((r a / r t) ^ p)) ≤ ENNReal.ofReal (1 / p) := by
  obtain ⟨hi, heq⟩ := integral_radial_rpow_eq hab hp hr hra hm hd
  have hpos x (hx : x ∈ Icc a b) : 0 < r x :=
    hra.trans_le (hm ⟨le_rfl, hab⟩ hx hx.1)
  have heqfun : ∀ x ∈ Icc a b,
      w x / r x * (r a / r x) ^ p = (r a) ^ p * (w x / (r x) ^ (1 + p)) := by
    intro x hx
    rw [Real.div_rpow hra.le (hpos x hx).le, Real.rpow_add (hpos x hx) 1 p,
      Real.rpow_one]
    ring
  have hk : IntervalIntegrable (fun x => w x / r x * (r a / r x) ^ p) volume a b := by
    apply (hi.const_mul ((r a) ^ p)).congr
    intro x hx
    exact (heqfun x (by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hx)).symm
  have hk0 : 0 ≤ᵐ[volume.restrict (Icc a b)]
      (fun x => w x / r x * (r a / r x) ^ p) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact mul_nonneg (div_nonneg (hw0 x hx) (hpos x hx).le)
      (Real.rpow_nonneg (div_nonneg hra.le (hpos x hx).le) _)
  have hbound : (∫ x in a..b, w x / r x * (r a / r x) ^ p) ≤ 1 / p := by
    calc
      _ = (r a) ^ p * ∫ x in a..b, w x / (r x) ^ (1 + p) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x hx
        exact heqfun x (by simpa only [uIcc_of_le hab] using hx)
      _ = (1 - (r a) ^ p * ((r b) ^ p)⁻¹) / p := by
        rw [heq, ← mul_div_assoc, mul_sub, mul_inv_cancel₀ (Real.rpow_pos_of_pos hra p).ne']
      _ ≤ _ := div_le_div_of_nonneg_right (sub_le_self _ (mul_nonneg (Real.rpow_nonneg hra.le _)
        (inv_nonneg.mpr (Real.rpow_nonneg (hpos b ⟨hab, le_rfl⟩).le _)))) hp.le
  calc
    _ = ∫⁻ x in Icc a b, ENNReal.ofReal (w x / r x * (r a / r x) ^ p) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [ENNReal.ofReal_mul (div_nonneg (hw0 x hx) (hpos x hx).le)]
    _ = ENNReal.ofReal (∫ x in a..b, w x / r x * (r a / r x) ^ p) := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hk) hk0,
        integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

/-- A4: the radial moment operator has L¹ mass at most `1 / p` times the forcing
mass. The density is nonnegative and measurable, with no integrability assumption.
This exact bound is uniform in all radii, weights, intervals, and shorter sections. -/
theorem lintegral_radial_moment_le {r w : ℝ → ℝ} {F : ℝ → ℝ≥0∞} {a b p : ℝ}
    (hab : a ≤ b) (hp : 0 < p) (hr : AbsolutelyContinuousOnInterval r a b)
    (hm : MonotoneOn r (Icc a b)) (hrpos : ∀ x ∈ Ioc a b, 0 < r x)
    (hw : Measurable w) (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hF : Measurable F)
    (hd : ∀ᵐ x ∂volume.restrict (Icc a b), deriv r x = w x) :
    (∫⁻ t in Icc a b, ENNReal.ofReal (w t / r t) *
      ∫⁻ s in Icc a t, ENNReal.ofReal ((r s / r t) ^ p) * F s) ≤
      ENNReal.ofReal (1 / p) * ∫⁻ s in Icc a b, F s := by
  classical
  let R := (Icc a b).indicator r
  have hR : Measurable R := by
    dsimp only [R]
    rw [← Set.piecewise_eq_indicator]
    apply ContinuousOn.measurable_piecewise _ continuousOn_const measurableSet_Icc
    simpa only [uIcc_of_le hab] using hr.continuousOn
  let K : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (w z.2 / R z.2) *
    ENNReal.ofReal ((R z.1 / R z.2) ^ p) * F z.1
  have hK : Measurable K := by dsimp only [K]; fun_prop
  have hRa : ∀ x ∈ Icc a b, R x = r x := fun x hx => indicator_of_mem hx r
  calc
    _ = ∫⁻ t in Icc a b, ∫⁻ s in Icc a t, K (s, t) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      dsimp only [K]
      rw [hRa t ht, hRa s ⟨hs.1, hs.2.trans ht.2⟩, mul_assoc]
    _ = ∫⁻ s in Icc a b, ∫⁻ t in Icc s b, K (s, t) :=
      (lintegral_lintegral_swap_triangle hK).symm
    _ ≤ ∫⁻ s in Icc a b, ENNReal.ofReal (1 / p) * F s := by
      apply lintegral_mono_ae
      have hna : ∀ᵐ s : ℝ, s ≠ a := by simp [ae_iff, measure_singleton]
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hna] with s hs hsa
      have hspos := hrpos s ⟨lt_of_le_of_ne hs.1 hsa.symm, hs.2⟩
      have hsub : uIcc s b ⊆ uIcc a b := by
        rw [uIcc_of_le hs.2, uIcc_of_le hab]
        exact Icc_subset_Icc hs.1 le_rfl
      have hds : ∀ᵐ x ∂volume.restrict (Icc s b), deriv r x = w x :=
        ae_mono (Measure.restrict_mono (Icc_subset_Icc hs.1 le_rfl) le_rfl) hd
      calc
        _ = (∫⁻ t in Icc s b, ENNReal.ofReal (w t / R t) *
            ENNReal.ofReal ((R s / R t) ^ p)) * F s := by
          rw [← lintegral_mul_const _ (show Measurable (fun t =>
            ENNReal.ofReal (w t / R t) * ENNReal.ofReal ((R s / R t) ^ p)) by fun_prop)]
        _ = (∫⁻ t in Icc s b, ENNReal.ofReal (w t / r t) *
            ENNReal.ofReal ((r s / r t) ^ p)) * F s := by
          congr 1
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          rw [hRa s hs, hRa t ⟨hs.1.trans ht.1, ht.2⟩]
        _ ≤ _ := mul_le_mul_left (lintegral_radial_moment_mass_le hs.2 hp
          (hr.mono hsub) hspos (hm.mono (Icc_subset_Icc hs.1 le_rfl))
          (fun x hx => hw0 x ⟨hs.1.trans hx.1, hx.2⟩) hds) _
    _ = _ := lintegral_const_mul _ hF

/-- A4 for a field bounded by a radial moment. The exact coefficient is `C / p`;
`C` is the displayed pointwise moment bound and `p` the exponent. There is no
additional dependence on the radius, section length, or density. -/
theorem lintegral_weighted_le_of_radial_moment {r w : ℝ → ℝ}
    {F Z : ℝ → ℝ≥0∞} {a b p C : ℝ}
    (hab : a ≤ b) (hp : 0 < p) (hC : 0 ≤ C)
    (hr : AbsolutelyContinuousOnInterval r a b)
    (hm : MonotoneOn r (Icc a b)) (hrpos : ∀ x ∈ Ioc a b, 0 < r x)
    (hw : Measurable w) (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x) (hF : Measurable F)
    (hd : ∀ᵐ x ∂volume.restrict (Icc a b), deriv r x = w x)
    (hZ : ∀ t ∈ Icc a b, Z t ≤ ENNReal.ofReal C *
      ∫⁻ s in Icc a t, ENNReal.ofReal ((r s / r t) ^ p) * F s) :
    (∫⁻ t in Icc a b, ENNReal.ofReal (w t / r t) * Z t) ≤
      ENNReal.ofReal (C / p) * ∫⁻ s in Icc a b, F s := by
  calc
    _ ≤ ∫⁻ t in Icc a b, ENNReal.ofReal C * (ENNReal.ofReal (w t / r t) *
        ∫⁻ s in Icc a t, ENNReal.ofReal ((r s / r t) ^ p) * F s) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      calc
        _ ≤ ENNReal.ofReal (w t / r t) * (ENNReal.ofReal C *
            ∫⁻ s in Icc a t, ENNReal.ofReal ((r s / r t) ^ p) * F s) := by
          gcongr
          exact hZ t ht
        _ = _ := by ac_rfl
    _ = ENNReal.ofReal C * (∫⁻ t in Icc a b, ENNReal.ofReal (w t / r t) *
        ∫⁻ s in Icc a t, ENNReal.ofReal ((r s / r t) ^ p) * F s) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (1 / p) * ∫⁻ s in Icc a b, F s) := by
      gcongr
      exact lintegral_radial_moment_le hab hp hr hm hrpos hw hw0 hF hd
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hC]
      congr 2
      ring

end EmcsfAcExtension.Mixed
