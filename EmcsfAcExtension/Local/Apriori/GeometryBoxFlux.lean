module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseFinal
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseNorms
import EmcsfAcExtension.Local.Apriori.TVEnvelope
import EmcsfAcExtension.Local.Apriori.TVEnvelopeAux
import EmcsfAcExtension.Local.Apriori.Hardy
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Infra.HardyQuadratic

/-! # Closed quadratic scalar budgets for the geometric estimates

The characteristic Hardy densities are integrable before their real
integrals are used. Closing the scalar envelopes gives numerical budgets
uniform in all higher data norms (`charged_SF_new_version.tex:L4633–L4640`).
-/

public section

open Set MeasureTheory Filter Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem quadratic_section_integrable {a b B : ℝ} {w : ℝ → ℝ} {y : ℝ → ℂ}
    (hab : a ≤ b) (hy : ContinuousOn y (Icc a b))
    (hw : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hB : ∀ x ∈ Icc a b, ‖y x‖ ≤ B)
    (hH : IntervalIntegrable (fun x => w x * ‖y x‖) volume a b) :
    IntervalIntegrable (fun x => w x * ‖y x‖ ^ 2) volume a b := by
  have hi := integrable_and_integral_weight_mul_norm_sq_le
    (hy.aestronglyMeasurable (μ := volume) measurableSet_Icc)
    (show ∀ᵐ x ∂volume.restrict (Icc a b), 0 ≤ w x from by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact hw x hx)
    (show ∀ᵐ x ∂volume.restrict (Icc a b), w x ≠ 0 → ‖y x‖ ≤ B from by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact fun _ => hB x hx)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hH)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hi.1

/-- Both quadratic scalar densities are integrable on every complete
axis-to-point segment. This assertion requires no smallness and makes no
uniform assumption on the classical field's derivative norms. -/
theorem AprioriSetting.quadratic_scalar_integrable {e T ε M : ℝ}
    {S : Fields} {h : ℝ → ℂ} (hset : AprioriSetting e T ε M S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvs : v ≤ T) :
    IntervalIntegrable (fun x => S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖ ^ 2)
        volume u v ∧
      IntervalIntegrable (fun x => -S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖ ^ 2)
        volume u v := by
  have hsO : MapsTo (fun x => (u, x)) (Icc u v) (triangle 0 T) :=
    fun x hx => ⟨hu, hx.1, hx.2.trans hvs⟩
  have hsI : MapsTo (fun x => (x, v)) (Icc u v) (triangle 0 T) :=
    fun x hx => ⟨hu.trans hx.1, hx.2, hvs⟩
  have cyO : ContinuousOn (fun x => S.theta u x / S.lam u x) (Icc u v) :=
    (hset.c1.c1_theta.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hsO).div
      (Complex.continuous_ofReal.comp_continuousOn (hset.c1.c1_lam.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn hsO))
      (fun x hx => Complex.ofReal_ne_zero.mpr (hset.c1.lam_pos (u, x) (hsO hx)).ne')
  have cyI : ContinuousOn (fun x => S.xi x v / S.nu x v) (Icc u v) :=
    (hset.c1.c1_xi.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hsI).div
      (Complex.continuous_ofReal.comp_continuousOn (hset.c1.c1_nu.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn hsI))
      (fun x hx => Complex.ofReal_ne_zero.mpr (hset.c1.nu_neg (x, v) (hsI hx)).ne)
  constructor
  · exact quadratic_section_integrable huv cyO
      (fun x hx => div_nonneg (hset.c1.lam_pos (u, x) (hsO hx)).le
        (hset.radius_nonneg (hsO hx)))
      (fun x hx => (hset.box (u, x) (hsO hx)).2.2.2.2.2.2.1)
      (bv_hardy_out_integrated hset.c1 hu huv hvs).1
  · exact quadratic_section_integrable huv cyI
      (fun x hx => div_nonneg (neg_pos.mpr (hset.c1.nu_neg (x, v) (hsI hx))).le
        (hset.radius_nonneg (hsI hx)))
      (fun x hx => (hset.box (x, v) (hsI hx)).2.2.2.2.2.2.2)
      (bv_hardy_in_integrated hset.c1 hu huv hvs).1

/-- Both quadratic scalar budgets are bounded by the universal coefficient
`14` times `ε²`. The positive thresholds precede all data and depend only
on the fixed box, uniformly in higher initial derivatives. -/
theorem closed_quadratic_scalar_budgets : ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
    ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      (∫ x in u..v, S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖ ^ 2) ≤
          14 * ε ^ 2 ∧
      (∫ x in u..v, -S.nu x v / S.r x v * ‖S.xi x v / S.nu x v‖ ^ 2) ≤
          14 * ε ^ 2 := by
  obtain ⟨ε₁, δ₀, hε₁, hδ₀, hclosed⟩ := bv_envelope_final_individual
  refine ⟨min ε₁ (1 / 8), δ₀, lt_min hε₁ (by norm_num), hδ₀, ?_⟩
  intro e T ε M S h hset hε hδ u v hu huv hvT
  obtain ⟨hJ, hK, _, _⟩ := hclosed e T ε M S h hset (hε.trans (min_le_left _ _)) hδ
  have hε0 := hset.eps_nonneg
  have hε8 := hε.trans (min_le_right _ _)
  have hj : (∫⁻ x in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) x).toReal ≤
      9 / 8 * ε := ENNReal.toReal_le_of_le_ofReal (by positivity) hJ
  have hk : (∫⁻ x in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) x).toReal ≤
      9 / 8 * ε := ENNReal.toReal_le_of_le_ofReal (by positivity) hK
  rw [outgoing_envelope_integral_toReal hset.pos hset.c1] at hj
  rw [incoming_envelope_integral_toReal hset.pos hset.c1] at hk
  have hmj := intervalIntegral.integral_mono_interval hu huv hvT
    (ae_of_all _ (fun _ => ENNReal.toReal_nonneg)) (apriori_envelopes_integrable hset).1
  have hmk := intervalIntegral.integral_mono_interval hu huv hvT
    (ae_of_all _ (fun _ => ENNReal.toReal_nonneg)) (apriori_envelopes_integrable hset).2
  have hbj := (bv_fluxes_out hset hε8 hu huv hvT).trans
    (mul_le_mul_of_nonneg_left (hmj.trans hj) (by positivity : 0 ≤ 12 * ε))
  have hbk := (bv_fluxes_in hset hε8 hu huv hvT).trans
    (mul_le_mul_of_nonneg_left (hmk.trans hk) (by positivity : 0 ≤ 12 * ε))
  constructor <;> nlinarith only [hbj, hbk, sq_nonneg ε]

end EmcsfAcExtension.Local
