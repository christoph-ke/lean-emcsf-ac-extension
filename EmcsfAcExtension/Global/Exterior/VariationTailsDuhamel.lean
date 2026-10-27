module

public import EmcsfAcExtension.Global.Exterior.VariationTailsHistory
public import EmcsfAcExtension.Global.Exterior.OpticsCoefficients

/-! # The fixed-row incoming Duhamel bound

The only rough term is the fixed initial outgoing derivative. The gauge
phase has norm one. All multiplier bounds are fixed before both later
rows vary. This is the characteristic step of internal project record (D2),
`charged_SF_new_version.tex:L1381–L1391` and L1404–L1412.
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal] The electromagnetic transport phase is unitary for every
real coupling and every real potential integral. -/
theorem density_phase_norm (e x : ℝ) : ‖Complex.exp (-I * e * x)‖ = 1 := by
  simp [Complex.norm_exp, mul_re]

/-- [internal]
Pointwise Duhamel bound for the actual prescribed density. The real
multiplier bound is uniform on the incoming history and is displayed
explicitly. No estimate on the initial derivative is required. -/
theorem density_duhamel_bound_of_ratio
    {ui e a b v P : ℝ} {S : Fields} (hS : IsSolution e S (origDomain ui))
    (hia : ui ≤ a) (hab : a ≤ b) (hbv : b < v) (hv0 : v ≤ 0)
    (hratio : ∀ s ∈ Icc a b,
      0 ≤ S.lam s v / S.lam b v ∧ S.lam s v / S.lam b v ≤ P) :
    ‖densityRepresentative e S a b v‖ ≤ P * ‖deriv (S.a a) v‖ +
      P * (∫ s in a..b, ‖rawDensitySource e S s v‖) := by
  have hs : inSeg a b v ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff hab).2 ⟨hia, hbv.trans_le hv0, hbv.le, hv0⟩
  have hsproper : inSeg a b v ⊆ origDomain ui ∩ {p | p.1 < p.2} := by
    intro p hp
    exact ⟨hs hp, by
      rcases hp with ⟨ha, hb, hv⟩
      change p.1 < p.2
      rw [hv]
      exact hb.trans_lt hbv⟩
  have cl := Calculus.continuousOn_in_section hS.cont_lam hs
  have cA := Calculus.continuousOn_in_section hS.cont_A hs
  have cF : ContinuousOn (fun s => rawDensitySource e S s v) (Icc a b) :=
    (Calculus.continuousOn_rawDensitySource hS hsproper).comp (f := fun s : ℝ => (s, v))
      (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs.1, hs.2, rfl⟩)
  have cInt : ContinuousOn (fun s => ∫ t in s..b, S.A t v) (Icc a b) := by
    have hi : IntegrableOn (fun s => S.A s v) (uIcc a b) := by
      rw [uIcc_of_le hab]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1
        (cA.intervalIntegrable_of_Icc hab)
    simpa only [uIcc_of_le hab] using intervalIntegral.continuousOn_primitive_interval_left hi
  have cPhase : ContinuousOn (fun s => Complex.exp (-I * e * ∫ t in s..b, S.A t v))
      (Icc a b) :=
    ((Complex.continuous_ofReal.comp_continuousOn cInt).const_mul (-I * e)).cexp
  have cRatio : ContinuousOn (fun s => ((S.lam s v / S.lam b v : ℝ) : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn (cl.div_const _)
  have hi : IntervalIntegrable (fun s => (S.lam s v / S.lam b v : ℝ) *
      Complex.exp (-I * e * ∫ t in s..b, S.A t v) * rawDensitySource e S s v)
      volume a b := ((cRatio.mul cPhase).mul cF).intervalIntegrable_of_Icc hab
  have hinit : ‖(S.lam a v / S.lam b v : ℝ) *
      Complex.exp (-I * e * ∫ s in a..b, S.A s v) * deriv (S.a a) v‖ ≤
      P * ‖deriv (S.a a) v‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hratio a ⟨le_rfl, hab⟩).1, density_phase_norm, mul_one]
    exact mul_le_mul_of_nonneg_right (hratio a ⟨le_rfl, hab⟩).2 (norm_nonneg _)
  have hsource := intervalIntegral.integral_mono_on hab hi.norm
    ((cF.norm.intervalIntegrable_of_Icc hab).const_mul P) (fun s hs => by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hratio s hs).1, density_phase_norm, mul_one]
      exact mul_le_mul_of_nonneg_right (hratio s hs).2 (norm_nonneg _))
  rw [intervalIntegral.integral_const_mul] at hsource
  rw [densityRepresentative_def]
  exact (norm_add_le _ _).trans (add_le_add hinit
    ((intervalIntegral.norm_integral_le_integral_norm hab).trans hsource))

/-- [internal]
An integrable labelwise coefficient majorant supplies one propagator
bound on every later proper incoming history. The multiplier is
`exp(∫ k)` on the complete late interval, fixed before its two endpoints.
No terminal expansion limit or lower expansion bound is needed. -/
theorem lambda_ratio_le_of_integrable_majorant
    {ui e c a b v : ℝ} {S : Fields} {k : ℝ → ℝ}
    (h : OriginalData ui e S) (hc : c ∈ Ico ui 0)
    (hca : c ≤ a) (_hab : a ≤ b) (hbv : b < v) (hv0 : v ≤ 0)
    (hk : IntervalIntegrable k volume c 0)
    (hk₀ : ∀ u ∈ Ico c 0, 0 ≤ k u)
    (hcoef : ∀ u ∈ Icc a b, |S.rUV u v / S.lam u v| ≤ k u) :
    ∀ s ∈ Icc a b, 0 ≤ S.lam s v / S.lam b v ∧
      S.lam s v / S.lam b v ≤ Real.exp (∫ u in c..0, k u) := by
  intro s hs
  have hsseg : inSeg s b v ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff hs.2).2
      ⟨hc.1.trans (hca.trans hs.1), hbv.trans_le hv0, hbv.le, hv0⟩
  have hls := h.solution.lam_pos (s, v) (hsseg ⟨le_rfl, hs.2, rfl⟩)
  have hlb := h.solution.lam_pos (b, v) (hsseg ⟨hs.2, le_rfl, rfl⟩)
  refine ⟨div_nonneg hls.le hlb.le, ?_⟩
  have hlog := in_log_lam_integralForm h hs.2 hbv hsseg
  have hsub : uIcc s b ⊆ uIcc c 0 := by
    rw [uIcc_of_le hs.2, uIcc_of_le hc.2.le]
    exact Icc_subset_Icc (hca.trans hs.1) (hbv.trans_le hv0).le
  have hle := intervalIntegral.integral_mono_on hs.2 hlog.1.norm
    (hk.mono_set hsub) (fun u hu => by
      rw [Real.norm_eq_abs]
      exact hcoef u ⟨hs.1.trans hu.1, hu.2⟩)
  have hle' := intervalIntegral.integral_mono_interval (hca.trans hs.1) hs.2
    (hbv.trans_le hv0).le
    (by
      rw [restrict_Ioc_eq_restrict_Icc, ← restrict_Ico_eq_restrict_Icc]
      exact (ae_restrict_mem measurableSet_Ico).mono fun u hu => hk₀ u hu) hk
  have habs := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    hs.2 (f := fun u => S.rUV u v / S.lam u v)
  rw [← hlog.2] at habs
  have hlogle : Real.log (S.lam s v) - Real.log (S.lam b v) ≤ ∫ u in c..0, k u := by
    have hn := neg_le_abs (Real.log (S.lam b v) - Real.log (S.lam s v))
    simp only [Real.norm_eq_abs] at hle
    linarith only [hn, habs, hle, hle']
  calc
    S.lam s v / S.lam b v =
        Real.exp (Real.log (S.lam s v) - Real.log (S.lam b v)) := by
      rw [Real.exp_sub, Real.exp_log hls, Real.exp_log hlb]
    _ ≤ _ := Real.exp_le_exp.mpr hlogle

end EmcsfAcExtension.Global.Exterior
