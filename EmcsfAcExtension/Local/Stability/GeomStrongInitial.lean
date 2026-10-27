module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Infra.Hardy
import EmcsfAcExtension.Local.Stability.GeometryDifferenceInitialGauge
import EmcsfAcExtension.Local.Stability.FieldDifferenceInitial
import EmcsfAcExtension.Local.Stability.FieldDifferenceInitialAverage
import EmcsfAcExtension.Local.Stability.DifferenceMomentsAlgebra
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.HardyBV
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Initial renormalized geometric difference

The common initial radial gauge removes the expansion derivative and
the moving radial weight. Hardy is applied to the literal datum
difference before estimating the quadratic correction, as in
charged_SF_new_version.tex:L5425–5428.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The initial geometric renormalization is exactly its quadratic
correction. Both endpoints are included, using `0 < T` already present
in the stability setting; no estimate constant or smallness is needed. -/
theorem stab_initial_geomL {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {v : ℝ} (hv : v ∈ Icc 0 T) :
    geomL (triangle 0 T) S 0 v =
      S.lam 0 v / S.r 0 v * ‖S.theta 0 v / (S.lam 0 v : ℂ)‖ ^ 2 := by
  have hs : MapsTo (fun x : ℝ => (0, x)) (Icc 0 T) (triangle 0 T) :=
    fun x hx => ⟨le_rfl, hx.1, hx.2⟩
  have hd := hasDerivWithinAt_pdV hset.c1.c1_lam (hs hv) hs
  have hz : HasDerivWithinAt (S.lam 0) 0 (Icc 0 T) v :=
    (hasDerivAt_const v (1 / 2 : ℝ)).hasDerivWithinAt.congr_of_mem
      (fun x hx => stab_initial_lam hset hx) hv
  have heq : pdV (triangle 0 T) S.lam 0 v = 0 :=
    (hd.derivWithin (uniqueDiffOn_Icc hset.pos v hv)).symm.trans
      (hz.derivWithin (uniqueDiffOn_Icc hset.pos v hv))
  simp only [geomL, heq, zero_div, zero_add]

/-- On the common initial cone the scalar-ratio difference is the
radial deviation of the datum difference. This identity has coefficient
one, uniformly in all parameters; its off-axis restriction is necessary
because the totalized radial average is zero at the vertex. -/
theorem stab_initial_ratio_difference_as_deviation
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {v : ℝ} (hv0 : 0 < v) (hvT : v ≤ T) :
    S₁.theta 0 v / (S₁.lam 0 v : ℂ) - S₂.theta 0 v / (S₂.lam 0 v : ℂ) =
      (h₁ - h₂) v - radialAverage (fun _ => (1 : ℝ)) (h₁ - h₂) 0 v := by
  have hv : v ∈ Icc 0 T := ⟨hv0.le, hvT⟩
  have hi₁ : IntervalIntegrable h₁ volume 0 v :=
    ((stab_initial_datum_ac h₁s).mono (by
      rw [uIcc_of_le hv0.le, uIcc_of_le h₁s.pos.le]
      exact Icc_subset_Icc_right hvT)).continuousOn.intervalIntegrable
  have hi₂ : IntervalIntegrable h₂ volume 0 v :=
    ((stab_initial_datum_ac h₂s).mono (by
      rw [uIcc_of_le hv0.le, uIcc_of_le h₂s.pos.le]
      exact Icc_subset_Icc_right hvT)).continuousOn.intervalIntegrable
  have heq : (v : ℂ) * (S₁.phi 0 v - S₂.phi 0 v) =
      ∫ s in 0..v, (h₁ - h₂) s := by
    rw [mul_sub, stab_initial_scalar_average h₁s hv,
      stab_initial_scalar_average h₂s hv]
    change (∫ s in 0..v, h₁ s) - (∫ s in 0..v, h₂ s) =
      ∫ s in 0..v, h₁ s - h₂ s
    exact (intervalIntegral.integral_sub hi₁ hi₂).symm
  have havg : radialAverage (fun _ => (1 : ℝ)) (h₁ - h₂) 0 v =
      S₁.phi 0 v - S₂.phi 0 v := by
    dsimp only [radialAverage]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one,
      one_smul]
    rw [Complex.real_smul, Complex.ofReal_inv, ← heq, ← mul_assoc,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hv0.ne'), one_mul]
  rw [havg]
  have ha₁ := (h₁s.data.1 v hv).2
  have ha₂ := (h₂s.data.1 v hv).2
  dsimp only [Fields.a] at ha₁ ha₂
  simp only [Pi.sub_apply]
  linear_combination ha₁ - ha₂

/-- [internal]
The initial geometric renormalizations differ by at most `2εΔ₀` in L¹,
charged_SF_new_version.tex:L5425–5428. The universal constant precedes all parameters,
the data and the pair, and is independent of derivative suprema and the
coupling. The common initial gauge makes smallness unnecessary here. -/
theorem Stab.initial_geometric_renormalized_difference :
    ∃ C : ℝ, 0 < C ∧ ∀ (T e ε M A : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      (∫⁻ v in Icc 0 T, ‖geomL (triangle 0 T) S₁ 0 v -
        geomL (triangle 0 T) S₂ 0 v‖ₑ) ≤
          ENNReal.ofReal (C * ε * dataDist h₁ h₂ T) := by
  refine ⟨2, by norm_num, ?_⟩
  intro T e ε M A S₁ S₂ h₁ h₂ h₁s h₂s
  let f := h₁ - h₂
  let H := fun x : ℝ => 1 / (∫ s in 0..x, (1 : ℝ)) *
    ‖f x - radialAverage (fun _ => (1 : ℝ)) f 0 x‖
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₁.xi 0 0 / (S₁.nu 0 0 : ℂ)))).trans
      (h₁s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₁s.pos.le⟩).2.2.2.2.2.1)
  have hf := (stab_initial_datum_ac h₁s).sub (stab_initial_datum_ac h₂s)
  have hh := integrable_and_integral_weighted_deviation_le_variation h₁s.pos.le
    (w := fun _ => (1 : ℝ)) intervalIntegrable_const (fun _ _ => by norm_num)
    (by simpa only [uIcc_of_le h₁s.pos.le] using hf.continuousOn)
    (hf.boundedVariationOn_Icc h₁s.pos.le)
  have hH0 : ∀ x ∈ Icc 0 T, 0 ≤ H x := by
    intro x hx
    dsimp only [H]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    exact mul_nonneg (div_nonneg (by norm_num) hx.1) (norm_nonneg _)
  have hH : (∫⁻ x in Icc 0 T, ENNReal.ofReal (H x)) ≤
      ENNReal.ofReal (datumVar f T) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Icc_of_le h₁s.pos.le).mp hh.1)
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx; exact hH0 x hx),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h₁s.pos.le]
    exact ENNReal.ofReal_le_ofReal hh.2
  have hpoint : ∀ᵐ v ∂volume.restrict (Icc 0 T),
      ‖geomL (triangle 0 T) S₁ 0 v - geomL (triangle 0 T) S₂ 0 v‖ₑ ≤
        ENNReal.ofReal (2 * ε) * ENNReal.ofReal (H v) := by
    have hn : ∀ᵐ v : ℝ, v ≠ 0 := by simp [ae_iff, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn] with v hv hvn
    have hv0 : 0 < v := lt_of_le_of_ne hv.1 hvn.symm
    have hweight : S₁.lam 0 v / S₁.r 0 v = 1 / v := by
      rw [stab_initial_lam h₁s hv, (h₁s.data.1 v hv).1]
      field_simp
    have hweight₂ : S₂.lam 0 v / S₂.r 0 v = 1 / v := by
      rw [stab_initial_lam h₂s hv, (h₂s.data.1 v hv).1]
      field_simp
    rw [stab_initial_geomL h₁s hv, stab_initial_geomL h₂s hv, hweight, hweight₂,
      ← mul_sub, ← ofReal_norm, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (div_nonneg (by norm_num) hv.1),
      ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hε)]
    apply ENNReal.ofReal_le_ofReal
    have hz₁ : ‖S₁.theta 0 v / (S₁.lam 0 v : ℂ)‖ ≤ ε :=
      (le_add_of_nonneg_right (norm_nonneg _)).trans
        (h₁s.box.2 (0, v) ⟨le_rfl, hv.1, hv.2⟩).2.2.2.2.2.1
    have hz₂ : ‖S₂.theta 0 v / (S₂.lam 0 v : ℂ)‖ ≤ ε :=
      (le_add_of_nonneg_right (norm_nonneg _)).trans
        (h₂s.box.2 (0, v) ⟨le_rfl, hv.1, hv.2⟩).2.2.2.2.2.1
    have hsq := mul_le_mul_of_nonneg_left (stab_norm_sq_sub_le hz₁ hz₂)
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hv.1)
    rw [stab_initial_ratio_difference_as_deviation h₁s h₂s hv0 hv.2] at hsq
    dsimp only [H, f]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    nlinarith only [hsq]
  apply (lintegral_mono_ae hpoint).trans
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply (mul_le_mul' le_rfl hH).trans
  rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hε)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left (norm_nonneg (h₁ 0 - h₂ 0))) (mul_nonneg (by norm_num) hε)

end EmcsfAcExtension.Local
