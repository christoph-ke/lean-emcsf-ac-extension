module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.TVEnvelope
import EmcsfAcExtension.Local.Apriori.TVEnvelopeAux
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Real envelope integrals and the coarse characteristic variation budgets

These are the finite real quantities in `charged_SF_new_version.tex:L4734–L4743` and
approved internal project record (13). The numerical coefficient three depends
only on the fixed bootstrap box.
-/

public section

open Set MeasureTheory Filter Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The outgoing envelope's real integral agrees with the real part of its
extended integral. Finiteness is proved from classical continuity, with no
uniform bound on higher derivatives. -/
theorem outgoing_envelope_integral_toReal {e s : ℝ} {S : Fields}
    (hs : 0 < s) (hS : IsC1Solution e S (triangle 0 s)) :
    (∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 s) S) v).toReal =
      ∫ v in 0..s, (outEnv 0 (jC1 (triangle 0 s) S) v).toReal := by
  rw [intervalIntegral.integral_of_le hs.le, ← integral_Icc_eq_integral_Ioc]
  symm
  apply integral_toReal (aemeasurable_outEnv (continuousOn_jC1_aux hs hS))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  exact lt_top_iff_ne_top.mpr
    (outEnv_ne_top_of_continuousOn (continuousOn_jC1_aux hs hS) hv)

/-- The incoming envelope's real integral agrees with the real part of its
extended integral. The assertion uses only classical continuity and positive
time and introduces no estimate constant. -/
theorem incoming_envelope_integral_toReal {e s : ℝ} {S : Fields}
    (hs : 0 < s) (hS : IsC1Solution e S (triangle 0 s)) :
    (∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 s) S) u).toReal =
      ∫ u in 0..s, (inEnv s (kC1 e (triangle 0 s) S) u).toReal := by
  rw [intervalIntegral.integral_of_le hs.le, ← integral_Icc_eq_integral_Ioc]
  symm
  apply integral_toReal (aemeasurable_inEnv (continuousOn_kC1_aux hs hS))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  exact lt_top_iff_ne_top.mpr
    (inEnv_ne_top_of_continuousOn (continuousOn_kC1_aux hs hS) hu)

private theorem reciprocal_mass_sup_le {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) {u v : ℝ}
    (hu : 0 ≤ u) (_huv : u ≤ v) (hvs : v ≤ s) :
    (⨆ w ∈ Icc u v, (1 - S.mu u w)⁻¹) ≤ 2 ∧
      (⨆ w ∈ Icc u v, (1 - S.mu w v)⁻¹) ≤ 2 := by
  have hinv (a b : ℝ) (hp : (a, b) ∈ triangle 0 s) : (1 - S.mu a b)⁻¹ ≤ 2 := by
    have hb := (hset.box (a, b) hp).2.2.2.2.1
    have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hb
    norm_num at hi
    exact hi
  constructor
  all_goals
    apply ciSup_le
    intro w
    rw [ciSup_eq_ite]
    split_ifs with hw
    · first
      | exact hinv u w ⟨hu, hw.1, hw.2.trans hvs⟩
      | exact hinv w v ⟨hu.trans hw.1, hw.2, hvs⟩
    · norm_num [Real.sSup_empty]

/-- The coarse outgoing and covariant incoming variation budgets on every
complete axis-to-point segment. The coefficient three is universal within
the fixed box, uniformly in all solution parameters and derivative norms.
No closed-envelope conclusion is assumed. -/
theorem characteristic_variation_budgets {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hε : ε ≤ 1 / 8)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvs : v ≤ s) :
    (eVariationOn (S.a u) (Icc u v)).toReal ≤
        3 * ∫ x in u..v, (outEnv 0 (jC1 (triangle 0 s) S) x).toReal ∧
      (∫ x in u..v,
        ‖pdU (triangle 0 s) S.b x v + I * e * S.A x v * S.b x v‖) ≤
        3 * ∫ x in u..v, (inEnv s (kC1 e (triangle 0 s) S) x).toReal := by
  have hε0 := hset.eps_nonneg
  have hcoeff : (3 : ℝ) / 4 ≤ 1 - 16 * ε ^ 2 := by
    nlinarith only [hε, hε0]
  have hsup := reciprocal_mass_sup_le hset hu huv hvs
  have hJ0 : 0 ≤ ∫ x in u..v, (outEnv 0 (jC1 (triangle 0 s) S) x).toReal :=
    intervalIntegral.integral_nonneg huv (fun _ _ => ENNReal.toReal_nonneg)
  have hK0 : 0 ≤ ∫ x in u..v, (inEnv s (kC1 e (triangle 0 s) S) x).toReal :=
    intervalIntegral.integral_nonneg huv (fun _ _ => ENNReal.toReal_nonneg)
  have hj := (bv_tvj hset hu huv hvs).trans
    (mul_le_mul_of_nonneg_right hsup.1 hJ0)
  have hk := (bv_tvk hset hu huv hvs).trans
    (mul_le_mul_of_nonneg_right hsup.2 hK0)
  constructor
  · have hi := mul_le_mul_of_nonneg_right hcoeff
      (show 0 ≤ (eVariationOn (S.a u) (Icc u v)).toReal from ENNReal.toReal_nonneg)
    linarith only [hi, hj, hJ0]
  · have hV0 : 0 ≤ ∫ x in u..v,
        ‖pdU (triangle 0 s) S.b x v + I * e * S.A x v * S.b x v‖ :=
      intervalIntegral.integral_nonneg huv (fun _ _ => norm_nonneg _)
    have hi := mul_le_mul_of_nonneg_right hcoeff hV0
    linarith only [hi, hk, hK0]

/-- The supremum of outgoing characteristic variations is controlled by
the outgoing envelope integral, with universal coefficient three. This is
the coarse version of approved internal project record (13), before envelope closure. -/
theorem outgoing_variation_sup_le {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hε : ε ≤ 1 / 8) :
    (⨆ u ∈ Icc 0 s, eVariationOn (S.a u) (Icc u s)) ≤
      ENNReal.ofReal 3 * ∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 s) S) v := by
  apply iSup₂_le
  intro u hu
  have ca : ContDiffOn ℝ 1 (S.a u) (Icc u s) :=
    hset.c1.c1_a.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun v hv => ⟨hu.1, hv.1, hv.2⟩)
  have hac : AbsolutelyContinuousOnInterval (S.a u) u s := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hu.2] using ca
  have hvfin := hac.boundedVariationOn_Icc hu.2
  have hJfin := outEnv_lintegral_ne_top_of_continuousOn
    (continuousOn_jC1_aux hset.pos hset.c1)
  have hm := intervalIntegral.integral_mono_interval hu.1 hu.2 le_rfl
    (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
    (apriori_envelopes_integrable hset).1
  calc
    _ = ENNReal.ofReal (eVariationOn (S.a u) (Icc u s)).toReal :=
      (ENNReal.ofReal_toReal hvfin).symm
    _ ≤ ENNReal.ofReal (3 * ∫ x in u..s,
        (outEnv 0 (jC1 (triangle 0 s) S) x).toReal) :=
      ENNReal.ofReal_le_ofReal (characteristic_variation_budgets hset hε hu.1 hu.2 le_rfl).1
    _ ≤ ENNReal.ofReal (3 * ∫ x in 0..s,
        (outEnv 0 (jC1 (triangle 0 s) S) x).toReal) := by gcongr
    _ = _ := by
      rw [← outgoing_envelope_integral_toReal hset.pos hset.c1,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_toReal hJfin]

/-- The supremum of integrated covariant incoming derivatives is controlled
by the incoming envelope integral. The coefficient three is universal and
independent of the coupling, background size, and higher data norms. -/
theorem incoming_variation_sup_le {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hε : ε ≤ 1 / 8) :
    (⨆ v ∈ Icc 0 s, ∫⁻ u in Icc 0 v,
      ‖pdU (triangle 0 s) S.b u v + I * e * S.A u v * S.b u v‖ₑ) ≤
      ENNReal.ofReal 3 * ∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 s) S) u := by
  apply iSup₂_le
  intro v hv
  let q : ℝ → ℂ := fun u =>
    pdU (triangle 0 s) S.b u v + I * e * S.A u v * S.b u v
  have hs : MapsTo (fun u => (u, v)) (Icc 0 v) (triangle 0 s) :=
    fun u hu => ⟨hu.1, hu.2, hv.2⟩
  have cq : ContinuousOn q (Icc 0 v) := by
    apply ((continuousOn_pdU hset.c1.c1_b (uniqueDiffOn_triangle hset.pos)).add
      (((continuousOn_const (c := I * e)).mul
        (Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_A.continuousOn)).mul
          hset.c1.c1_b.continuousOn)).comp
            (continuous_id.prodMk continuous_const).continuousOn hs
  have hi := cq.intervalIntegrable_of_Icc (μ := volume) hv.1
  have hKfin := inEnv_lintegral_ne_top_of_continuousOn
    (continuousOn_kC1_aux hset.pos hset.c1)
  have hm := intervalIntegral.integral_mono_interval le_rfl hv.1 hv.2
    (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
    (apriori_envelopes_integrable hset).2
  calc
    _ = ENNReal.ofReal (∫ u in 0..v, ‖q u‖) := by
      rw [intervalIntegral.integral_of_le hv.1, ← integral_Icc_eq_integral_Ioc,
        ofReal_integral_norm_eq_lintegral_enorm
          ((intervalIntegrable_iff_integrableOn_Icc_of_le hv.1).mp hi)]
    _ ≤ ENNReal.ofReal (3 * ∫ u in 0..v,
        (inEnv s (kC1 e (triangle 0 s) S) u).toReal) :=
      ENNReal.ofReal_le_ofReal
        (characteristic_variation_budgets hset hε le_rfl hv.1 hv.2).2
    _ ≤ ENNReal.ofReal (3 * ∫ u in 0..s,
        (inEnv s (kC1 e (triangle 0 s) S) u).toReal) := by gcongr
    _ = _ := by
      rw [← incoming_envelope_integral_toReal hset.pos hset.c1,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_toReal hKfin]

end EmcsfAcExtension.Local
