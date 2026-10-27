module

public import EmcsfAcExtension.Local.Stability.JCloseInitialHardy
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Infra.Calculus.PartialsC1
import EmcsfAcExtension.Infra.Calculus.TriangleDiff
import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # Initial datum variation from the independent derivative envelope

The cubic correction is absorbed using the data Hardy estimate itself.
This derives the small initial variation needed in the j comparison from
the standing setting, without adding a datum-size hypothesis.
-/

public section

open Set MeasureTheory Complex Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

private theorem initial_partial_norm_le {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) {v : ℝ} (hv : v ∈ Icc 0 T) :
    ‖pdV (triangle 0 T) S.a 0 v‖ ≤ 4 * ‖jC1 (triangle 0 T) S 0 v‖ +
      ε ^ 2 * (S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖) := by
  have hp : (0, v) ∈ triangle 0 T := ⟨le_rfl, hv.1, hv.2⟩
  have hγ := hs.c1.one_sub_mu_pos (0, v) hp
  have hγlow := (hs.box.2 (0, v) hp).2.2.2.2.1
  have hr : 0 ≤ S.r 0 v := by rw [(hs.data.1 v hv).1]; exact div_nonneg hv.1 (by norm_num)
  have hq : 0 ≤ S.lam 0 v / S.r 0 v := div_nonneg (hs.c1.lam_pos (0, v) hp).le hr
  have hx := (le_add_of_nonneg_right (norm_nonneg _)).trans (hs.box.2 (0, v) hp).2.2.2.2.2.1
  have hε : 0 ≤ ε := (norm_nonneg _).trans hx
  have heq : pdV (triangle 0 T) S.a 0 v =
      jC1 (triangle 0 T) S 0 v / ((1 - S.mu 0 v : ℝ) : ℂ) +
        ((S.lam 0 v / S.r 0 v : ℝ) : ℂ) * (‖S.theta 0 v / S.lam 0 v‖ : ℂ) ^ 2 *
          (S.theta 0 v / S.lam 0 v) := by
    have hγc : 1 - (S.mu 0 v : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
    simp only [jC1]
    push_cast
    field_simp [hγc]
    ; ring
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_real, norm_real, norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hγ, abs_of_nonneg hq, abs_norm]
  have hdiv : ‖jC1 (triangle 0 T) S 0 v‖ / (1 - S.mu 0 v) ≤ 4 * ‖jC1 (triangle 0 T) S 0 v‖ := by
    apply (div_le_iff₀ hγ).2
    have h := mul_le_mul_of_nonneg_left hγlow (by positivity : 0 ≤ 4 * ‖jC1 (triangle 0 T) S 0 v‖)
    nlinarith only [h]
  have hpow := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx 2)
    (mul_nonneg hq (norm_nonneg (S.theta 0 v / S.lam 0 v)))
  nlinarith only [hdiv, hpow]

/-- Small initial variation follows from the standing envelope assumption.
`C` depends only on its fixed constant `A`, uniformly in the coupling,
length, background, fields, data and every derivative supremum. -/
theorem initial_datum_variation_bound (A : ℝ) (hA : 0 < A) : ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      StabSetting e T ε M A S h → ε ^ 2 ≤ 1 / 4 → datumVar h T ≤ C * ε := by
  refine ⟨6 * A, by positivity, ?_⟩
  intro T e ε M S h hs hsmall
  have hac := initial_datum_ac hs
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs.box.2 (0, 0) ⟨le_rfl, le_rfl, hs.pos.le⟩).2.2.2.2.2.1
  have hmap : MapsTo (fun v => (0, v)) (Icc 0 T) (triangle 0 T) :=
    fun v hv => ⟨le_rfl, hv.1, hv.2⟩
  have hcp : ContinuousOn (pdV (triangle 0 T) S.a 0) (Icc 0 T) := by
    simpa only [Function.comp_apply, Function.uncurry_def, id_eq] using!
      (continuousOn_partial_v (stab_normalized_out_c1 hs.c1)
        (uniqueDiffOn_triangle hs.pos)).comp (continuous_const.prodMk continuous_id).continuousOn
            hmap
  have hcj : ContinuousOn (fun v => jC1 (triangle 0 T) S 0 v) (Icc 0 T) := by
    simpa only [Function.comp_apply, Function.uncurry_def, id_eq] using!
      (continuousOn_jC1_aux hs.pos hs.c1).comp
        (continuous_const.prodMk continuous_id).continuousOn hmap
  have hip := hcp.intervalIntegrable_of_Icc (μ := volume) hs.pos.le
  have hij := hcj.intervalIntegrable_of_Icc (μ := volume) hs.pos.le
  have hHardy := initial_hardy hs
  have hJ : (∫ v in 0..T, ‖jC1 (triangle 0 T) S 0 v‖) ≤ A * ε := by
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA.le hε)).mp
    rw [intervalIntegral.integral_of_le hs.pos.le, restrict_Ioc_eq_restrict_Icc,
      ofReal_integral_norm_eq_lintegral_enorm
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hs.pos.le).mp hij)]
    calc
      _ ≤ ∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) v := by
        apply setLIntegral_mono' measurableSet_Icc
        intro v hv
        exact le_iSup₂_of_le 0 ⟨le_rfl, hv.1⟩ le_rfl
      _ ≤ _ := (le_add_right le_rfl).trans hs.env
  have hvar : datumVar h T = ∫ v in 0..T, ‖pdV (triangle 0 T) S.a 0 v‖ := by
    rw [datumVar, hac.toReal_eVariationOn_eq_integral_norm_deriv hs.pos.le]
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hs.pos.le, restrict_Ioc_eq_restrict_Icc]
    filter_upwards [initial_pdV_eq_deriv_ae hs] with v hv
    rw [hv]
  have hV : 0 ≤ datumVar h T := ENNReal.toReal_nonneg
  have hineq : datumVar h T ≤ 4 * A * ε + ε ^ 2 * datumVar h T := by
    rw [hvar]
    apply (intervalIntegral.integral_mono_on hs.pos.le hip.norm
      ((hij.norm.const_mul 4).add (hHardy.1.const_mul (ε ^ 2)))
      (fun v hv => initial_partial_norm_le hs hv)).trans
    rw [intervalIntegral.integral_add (hij.norm.const_mul 4) (hHardy.1.const_mul (ε ^ 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have h₁ := mul_le_mul_of_nonneg_left hJ (by norm_num : (0 : ℝ) ≤ 4)
    have h₂ := mul_le_mul_of_nonneg_left hHardy.2 (sq_nonneg ε)
    rw [← hvar]
    nlinarith only [h₁, h₂]
  have hsmallV := mul_le_mul_of_nonneg_right hsmall hV
  have hAε := mul_nonneg hA.le hε
  nlinarith only [hineq, hsmallV, hAε]

end EmcsfAcExtension.Local.Stab
