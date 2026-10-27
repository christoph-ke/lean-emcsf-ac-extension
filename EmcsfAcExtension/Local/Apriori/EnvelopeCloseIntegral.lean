module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseFields
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseAxis
import EmcsfAcExtension.Local.Calculus.AxisMatch
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Integrating the characteristic modulus estimates

The outgoing label supremum follows incoming transport, and the incoming
label supremum follows outgoing transport. The axis datum is precisely the
scalar axis variation, as in `charged_SF_new_version.tex:L4734–L4767`.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Integrated outgoing characteristic modulus estimate with the full
forcing area retained. `C` depends only on the fixed box and is independent
of every solution parameter and derivative norm. No source integrability
or closed-envelope bound is assumed. -/
theorem outgoing_envelope_bound_with_forcing :
    ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h → ε ≤ 1 / 8 →
      (∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 s) S) v) ≤
        ENNReal.ofReal (Real.exp (C * ε *
          ∫ x in 0..s, (inEnv s (kC1 e (triangle 0 s) S) x).toReal)) *
        ((∫⁻ v in Icc 0 s, ‖jC1 (triangle 0 s) S 0 v‖ₑ) +
          ∫⁻ v in Icc 0 s, ∫⁻ u in Icc 0 v,
            ‖S.nu u v * S.theta u v / S.r u v ^ 2 *
              (curv S u v + 2 * starRingEnd ℂ (curv S u v)) + emSourceJ e S u v‖ₑ) := by
  obtain ⟨C, hC, hchar⟩ := j_characteristic_enorm_bound
  refine ⟨C, hC, ?_⟩
  intro e s ε M S h hset hε
  let H := ENNReal.ofReal (Real.exp (C * ε *
    ∫ x in 0..s, (inEnv s (kC1 e (triangle 0 s) S) x).toReal))
  let F := fun u v => ‖S.nu u v * S.theta u v / S.r u v ^ 2 *
    (curv S u v + 2 * starRingEnd ℂ (curv S u v)) + emSourceJ e S u v‖ₑ
  have ci : ContinuousOn (fun v => jC1 (triangle 0 s) S 0 v) (Icc 0 s) :=
    (continuousOn_jC1_aux hset.pos hset.c1).comp (f := fun v : ℝ => (0, v))
      (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  calc
    _ ≤ ∫⁻ v in Icc 0 s,
        H * (‖jC1 (triangle 0 s) S 0 v‖ₑ + ∫⁻ u in Icc 0 v, F u v) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro v hv
      apply iSup₂_le
      intro u hu
      exact hchar e s ε M S h hset hε u v hu.1 hu.2 hv.2
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left' (ci.enorm.aemeasurable measurableSet_Icc)]

/-- Integrated incoming characteristic modulus estimate, retaining the
forcing area and exactly the scalar axis variation as its boundary datum.
The displayed coefficients are one, uniformly in all parameters and higher
data norms. No scalar smallness is required. -/
theorem incoming_envelope_bound_with_forcing {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) :
    (∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 s) S) u) ≤
      eVariationOn (fun t => S.phi t t) (Icc 0 s) +
        ∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s,
          ‖S.lam u v * S.xi u v / S.r u v ^ 2 *
            (starRingEnd ℂ (curv S u v) + 2 * curv S u v) + emSourceK e S u v‖ₑ := by
  let F := fun u v => ‖S.lam u v * S.xi u v / S.r u v ^ 2 *
    (starRingEnd ℂ (curv S u v) + 2 * curv S u v) + emSourceK e S u v‖ₑ
  have ck : ContinuousOn (fun t => kC1 e (triangle 0 s) S t t) (Icc 0 s) :=
    (continuousOn_kC1_aux hset.pos hset.c1).comp (f := fun t : ℝ => (t, t))
      (continuous_id.prodMk continuous_id).continuousOn
      (fun t ht => ⟨ht.1, le_rfl, ht.2⟩)
  have haxis : (∫⁻ u in Icc 0 s, ‖kC1 e (triangle 0 s) S u u‖ₑ) =
      eVariationOn (fun t => S.phi t t) (Icc 0 s) := by
    rw [smooth_axis_variation_eq_lintegral hset.pos hset.c1 hset.data.2]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    change ‖kC1 e (triangle 0 s) S u u‖ₑ = ‖jC1 (triangle 0 s) S u u‖ₑ
    rw [(bv_axis_match hset.pos hset.c1 hset.data.2 hu).1]
  calc
    _ ≤ ∫⁻ u in Icc 0 s,
        ‖kC1 e (triangle 0 s) S u u‖ₑ + ∫⁻ v in Icc u s, F u v := by
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      apply iSup₂_le
      intro v hv
      exact k_characteristic_enorm_bound hset hu.1 hv.1 hv.2
    _ = _ := by
      rw [lintegral_add_left' (ck.enorm.aemeasurable measurableSet_Icc), haxis]

end EmcsfAcExtension.Local
