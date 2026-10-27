module

public import EmcsfAcExtension.Local.Stability.OrderedKernelIncoming
import EmcsfAcExtension.Local.Stability.MomentsFieldMeasurable

/-! # Incoming scalar-curvature area estimate

The field-dependent estimate needs only the outgoing reconstruction
identity. Tonelli and the four-variable kernel theorem supply finiteness.
The radius is never bounded away from zero by an additional parameter.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Incoming scalar-curvature area estimate from the outgoing sectional
identity. The exact coefficient `512` is universal, independently of the
domain, coupling, field size, envelope constant, and derivative suprema.
The same estimate works for every `1/2 ≤ p ≤ 1 - ε²`. -/
theorem stab_incoming_ordered_primitive_l1_of_identity
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    (hidentity : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
      HasDerivWithinAt (fun s => S.theta u s / (S.lam u s : ℂ))
        (jC1 (triangle 0 T) S u v / ((1 - S.mu u v : ℝ) : ℂ) -
          (S.lam u v / S.r u v * (1 - ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2)) •
            (S.theta u v / (S.lam u v : ℂ))) (Icc u T) v)
    {p : ℝ} (hp0 : 1 / 2 ≤ p) (hp : p ≤ 1 - ε ^ 2) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖(S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
        curvScalarInConj e (triangle 0 T) S u v‖ₑ) ≤
      ENNReal.ofReal (512 * ε) *
        (∫⁻ s in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) s) *
        (∫⁻ w in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) w) := by
  classical
  let K := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S))
  let J := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))
  have hK : Measurable K := stab_measurable_inEnv_of_offAxis
    (stab_kC1_borel hset) (stab_kC1_continuous_offAxis hset)
  have hJ : Measurable J := stab_measurable_outEnv_of_offAxis
    (stab_jC1_borel hset) (stab_jC1_continuous_offAxis hset)
  have hp' : 0 < p := lt_of_lt_of_le (by norm_num) hp0
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S.xi 0 0 / (S.nu 0 0 : ℂ)))).trans
      (hset.box.2 (0, 0) ⟨le_rfl, le_rfl, hset.pos.le⟩).2.2.2.2.2.1)
  have hb : (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖(S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
        curvScalarInConj e (triangle 0 T) S u v‖ₑ) ≤
      ENNReal.ofReal (256 * ε) *
        ∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, stabOrderedKernel p K J u v := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro v hv
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hne : ∀ᵐ u : ℝ, u ≠ v := by simp [ae_iff, measure_singleton]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with u hu hne
    exact stab_incoming_ordered_pointwise_of_identity hset hidentity hp0 hp hu.1
      (lt_of_le_of_ne hu.2 hne) hv.2
  have hk := stab_ordered_kernel_area (T := T) hp' hK hJ
  have hC : ENNReal.ofReal (1 / p) ≤ ENNReal.ofReal 2 :=
    ENNReal.ofReal_le_ofReal ((div_le_iff₀ hp').2 (by linarith only [hp0]))
  have hmassK : (∫⁻ s in Icc 0 T, K s) =
      ∫⁻ s in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) s := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    exact indicator_of_mem hs _
  have hmassJ : (∫⁻ w in Icc 0 T, J w) =
      ∫⁻ w in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) w := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro w hw
    exact indicator_of_mem hw _
  apply hb.trans
  calc
    _ ≤ ENNReal.ofReal (256 * ε) *
        (ENNReal.ofReal (1 / p) * (∫⁻ s in Icc 0 T, K s) * (∫⁻ w in Icc 0 T, J w)) :=
      mul_le_mul' le_rfl hk
    _ ≤ ENNReal.ofReal (256 * ε) *
        (ENNReal.ofReal 2 * (∫⁻ s in Icc 0 T, K s) * (∫⁻ w in Icc 0 T, J w)) :=
      mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' hC le_rfl) le_rfl)
    _ = _ := by
      rw [hmassK, hmassJ]
      simp only [← mul_assoc]
      rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hε)]
      rw [show (256 * ε) * 2 = 512 * ε by ring]

private theorem norm_incoming_scalar_combination_le (c z : ℂ) :
    ‖c * (z + 2 * starRingEnd ℂ z)‖ ≤ 3 * ‖c * z‖ := by
  rw [norm_mul, norm_mul]
  calc
    _ ≤ ‖c‖ * (‖z‖ + ‖2 * starRingEnd ℂ z‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg c)
    _ = _ := by
      simp only [norm_mul, RCLike.norm_conj]
      norm_num
      ring

/-- Incoming ordered scalar-source area bound from the outgoing sectional
identity, with the exact repaired primitive and both curvature terms.
The coefficient `1536` is universal: independent of `T,e,M,A`, the fields,
the derivative suprema, and every `1/2 ≤ p ≤ 1 - ε²`. -/
theorem stab_incoming_ordered_l1_of_identity
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    (hidentity : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
      HasDerivWithinAt (fun s => S.theta u s / (S.lam u s : ℂ))
        (jC1 (triangle 0 T) S u v / ((1 - S.mu u v : ℝ) : ℂ) -
          (S.lam u v / S.r u v * (1 - ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2)) •
            (S.theta u v / (S.lam u v : ℂ))) (Icc u T) v)
    {p : ℝ} (hp0 : 1 / 2 ≤ p) (hp : p ≤ 1 - ε ^ 2) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖(S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
        (curvScalarInConj e (triangle 0 T) S u v +
          2 * starRingEnd ℂ (curvScalarInConj e (triangle 0 T) S u v))‖ₑ) ≤
      ENNReal.ofReal (1536 * ε) *
        (∫⁻ s in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) s) *
        (∫⁻ w in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) w) := by
  have hbound := stab_incoming_ordered_primitive_l1_of_identity hset hidentity hp0 hp
  have hpoint (u v : ℝ) :
      ‖(S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
        (curvScalarInConj e (triangle 0 T) S u v +
          2 * starRingEnd ℂ (curvScalarInConj e (triangle 0 T) S u v))‖ₑ ≤
      ENNReal.ofReal 3 * ‖(S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
        curvScalarInConj e (triangle 0 T) S u v‖ₑ := by
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ofReal_norm] using
      ENNReal.ofReal_le_ofReal (norm_incoming_scalar_combination_le
        ((S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2)
        (curvScalarInConj e (triangle 0 T) S u v))
  have harea : (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖(S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
        (curvScalarInConj e (triangle 0 T) S u v +
          2 * starRingEnd ℂ (curvScalarInConj e (triangle 0 T) S u v))‖ₑ) ≤
      ENNReal.ofReal 3 * ∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖(S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
          curvScalarInConj e (triangle 0 T) S u v‖ₑ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono
    intro v
    dsimp only
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono (fun u => hpoint u v)
  apply harea.trans
  apply (mul_le_mul' le_rfl hbound).trans_eq
  simp only [← mul_assoc]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [show (3 : ℝ) * (512 * ε) = 1536 * ε by ring]

end EmcsfAcExtension.Local
