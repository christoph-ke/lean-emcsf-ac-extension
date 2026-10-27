module

public import EmcsfAcExtension.Local.Stability.JCloseCoefficient
import EmcsfAcExtension.Infra.AC.Complex

/-! # Real propagator budgets for both derivative transports

The connection contributes zero real part. The incoming j amplification
uses its full Hardy budget; the outgoing k amplification is at most one.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- Both homogeneous complex coefficients are continuous on the closed
triangle. The imaginary connection is included with its literal coefficient. -/
theorem transport_complex_coefficients_continuousOn {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) :
    ContinuousOn (fun p => (jRealCoefficient S p.1 p.2 : ℂ) - I * e * S.A p.1 p.2)
      (triangle 0 T) ∧
    ContinuousOn (fun p => (kRealCoefficient S p.1 p.2 : ℂ)) (triangle 0 T) := by
  have hc := transport_real_coefficients_continuousOn hs
  have hj := Complex.continuous_ofReal.comp_continuousOn hc.1
  have hk := Complex.continuous_ofReal.comp_continuousOn hc.2
  have hA := Complex.continuous_ofReal.comp_continuousOn hs.c1.c1_A.continuousOn
  constructor
  · simpa only [Function.comp_apply, Function.uncurry_def, Pi.sub_def, Pi.mul_def] using!
      hj.sub ((continuousOn_const (c := I * e)).mul hA)
  · exact hk

private theorem real_integral_le_of_lintegral_bound {a b B : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hB : 0 ≤ B) (hf : IntervalIntegrable f volume a b)
    (hnn : ∀ x ∈ Icc a b, 0 ≤ f x)
    (hbound : (∫⁻ x in Icc a b, ENNReal.ofReal (f x)) ≤ ENNReal.ofReal B) :
    (∫ x in a..b, f x) ≤ B := by
  apply (ENNReal.ofReal_le_ofReal_iff hB).mp
  rw [intervalIntegral.integral_of_le hab, restrict_Ioc_eq_restrict_Icc,
    ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hf)
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx; exact hnn x hx)]
  exact hbound

private theorem real_part_subinterval_integral_le {a b B : ℝ} {f : ℝ → ℝ} {c : ℝ → ℂ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) (hc : IntervalIntegrable c volume a b)
    (hnn : ∀ x ∈ Icc a b, 0 ≤ f x) (hre : ∀ x ∈ Icc a b, (c x).re = f x)
    (hbound : (∫ x in a..b, f x) ≤ B)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc s b) :
    (∫ x in s..t, c x).re ≤ B := by
  have hsub : uIcc s t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc hs.1 ht.2
  have hRe : (∫ x in s..t, c x).re = ∫ x in s..t, (c x).re := by
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.intervalIntegral_comp_comm (hc.mono_set hsub)).symm
  rw [hRe]
  calc
    _ = ∫ x in s..t, f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le ht.1] at hx
      exact hre x ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩
    _ ≤ ∫ x in a..b, f x :=
      intervalIntegral.integral_mono_interval hs.1 ht.1 ht.2
        (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx; exact hnn x ⟨hx.1.le,
              hx.2⟩) hf
    _ ≤ B := hbound

/-- The real j propagator on every incoming subsegment has budget `C A ε²`.
`C` is universal, independent of all physical parameters and envelope or
solution derivative suprema. The imaginary connection contributes exactly zero. -/
theorem j_propagator_budget : ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M A : ℝ) (S : Fields) (h : ℝ → ℂ), 0 < A →
      StabSetting e T ε M A S h → ε ^ 2 ≤ 1 / 4 →
      ∀ v ∈ Icc 0 T, ∀ s ∈ Icc 0 v, ∀ t ∈ Icc s v,
      (∫ u in s..t, (jRealCoefficient S u v : ℂ) - I * e * S.A u v).re ≤ C * A * ε ^ 2 := by
  obtain ⟨C, hC, hhom⟩ := j_homogeneous_integral
  refine ⟨C, hC, ?_⟩
  intro T e ε M A S h hA hs hsmall v hv s hs' t ht
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs.box.2 (0, 0) ⟨le_rfl, le_rfl, hs.pos.le⟩).2.2.2.2.2.1
  have hmap : MapsTo (fun u => (u, v)) (Icc 0 v) (triangle 0 T) :=
    fun u hu => ⟨hu.1, hu.2, hv.2⟩
  have hir : IntervalIntegrable (fun u => jRealCoefficient S u v) volume 0 v := by
    simpa only [Function.comp_apply, Function.uncurry_def, id_eq] using!
      ((transport_real_coefficients_continuousOn hs).1.comp
        (continuous_id.prodMk continuous_const).continuousOn hmap).intervalIntegrable_of_Icc
        (μ := volume) hv.1
  have hic : IntervalIntegrable (fun u => (jRealCoefficient S u v : ℂ) - I * e * S.A u v) volume 0 v
      := by
    simpa only [Function.comp_apply, Function.uncurry_def, id_eq] using!
      ((transport_complex_coefficients_continuousOn hs).1.comp
        (continuous_id.prodMk continuous_const).continuousOn hmap).intervalIntegrable_of_Icc
        (μ := volume) hv.1
  have henv : (∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) u) ≤
      ENNReal.ofReal (A * ε) := (le_add_left le_rfl).trans hs.env
  have hlower : (∫⁻ u in Icc 0 v, ENNReal.ofReal (jRealCoefficient S u v)) ≤
      ENNReal.ofReal (C * A * ε ^ 2) := by
    calc
      _ ≤ ENNReal.ofReal (C * ε) * ENNReal.ofReal (A * ε) :=
        (hhom e T ε M A S h hs hsmall v hv).trans (mul_le_mul' le_rfl henv)
      _ = _ := by rw [← ENNReal.ofReal_mul (mul_nonneg hC.le hε)]; congr 1; ring
  have hnn : ∀ u ∈ Icc 0 v, 0 ≤ jRealCoefficient S u v :=
    fun u hu => jRealCoefficient_nonneg hs (hmap hu)
  have hreal := real_integral_le_of_lintegral_bound hv.1 (by positivity : 0 ≤ C * A * ε ^ 2)
    hir hnn hlower
  apply real_part_subinterval_integral_le hv.1 hir hic hnn _ hreal hs' ht
  intro u hu
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, zero_mul, mul_zero, sub_zero]

/-- Every real k propagator integral is nonpositive. The bound zero is
universal and gives the exact amplification coefficient one at the axis. -/
theorem k_propagator_budget {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) {u : ℝ} (hu : u ∈ Icc 0 T)
    {s t : ℝ} (hs' : s ∈ Icc u T) (ht : t ∈ Icc s T) :
    (∫ v in s..t, (kRealCoefficient S u v : ℂ)).re ≤ 0 := by
  rw [intervalIntegral.integral_ofReal, ofReal_re]
  have hnn := intervalIntegral.integral_nonneg (μ := volume) ht.1 (fun v hv =>
    neg_nonneg.mpr (kRealCoefficient_nonpos hs ⟨hu.1, hs'.1.trans hv.1, hv.2.trans ht.2⟩))
  rw [intervalIntegral.integral_neg] at hnn
  linarith only [hnn]

end EmcsfAcExtension.Local.Stab
