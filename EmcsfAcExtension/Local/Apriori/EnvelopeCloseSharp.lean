module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.Mass
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.AreaJAux
import EmcsfAcExtension.Local.Apriori.TVEnvelope
import EmcsfAcExtension.Local.Apriori.TVEnvelopeAux
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseNorms
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Sharpening variation absorption before geometric bootstrap improvement

The direct mass constraint improves the inverse-gap coefficient without
using any downstream geometric improvement. This is the sharp part of
approved internal project record (18), after the coupled envelope closure.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- A direct mass bound gives a gap of at least `7/8` under fixed numerical
smallness margins. The constants are universal within the bootstrap box;
no geometric improvement or closed-envelope hypothesis is used. -/
theorem AprioriSetting.mass_gap_seven_eighths {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hε : ε ≤ 1 / 64)
    (hδ : |e| * (s / 2) * M ≤ 1) {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    7 / 8 ≤ 1 - S.mu u v := by
  have hε0 := hset.eps_nonneg
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hset.one_le_M
  have hδ0 : 0 ≤ |e| * (s / 2) * M := by have := hset.pos; positivity
  have hδ2 : (|e| * (s / 2) * M) ^ 2 ≤ 1 := by nlinarith only [hδ, hδ0]
  have hr0 := hset.radius_nonneg hp
  have hr : S.r u v ≤ s := (Area.radius_bounds hset hp.1 hp.2.1 hp.2.2).2.trans
    (by linarith only [hp.1, hp.2.2])
  have hscale : e ^ 2 * M ^ 2 * S.r u v ^ 2 ≤
      4 * (|e| * (s / 2) * M) ^ 2 := by
    have hi := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr 2)
      (show 0 ≤ e ^ 2 * M ^ 2 by positivity)
    convert hi using 1
    simp only [mul_pow, sq_abs]
    ring
  have heps := pow_le_pow_left₀ hε0 hε 2
  have hmass := hset.mu_le hp
  have hm : S.mu u v ≤ 22 * ε ^ 2 := by
    have hi := mul_le_mul_of_nonneg_right (hscale.trans
      (mul_le_mul_of_nonneg_left hδ2 (by norm_num : (0 : ℝ) ≤ 4))) (sq_nonneg ε)
    nlinarith only [hmass, hi, sq_nonneg ε]
  norm_num at heps
  linarith only [hm, heps]

private theorem reciprocal_sup_bound {a b H : ℝ} {f : ℝ → ℝ}
    (hH : 0 ≤ H) (hf : ∀ x ∈ Icc a b, f x ≤ H) : (⨆ x ∈ Icc a b, f x) ≤ H := by
  apply ciSup_le
  intro x
  rw [ciSup_eq_ite]
  split_ifs with hx
  · exact hf x hx
  · simpa only [Real.sSup_empty] using hH

/-- The two characteristic variation absorptions have coefficient at most
`4/3` under the direct mass-gap improvement. This numerical coefficient is
universal within the box and independent of every derivative norm. -/
theorem characteristic_variation_sharp_budgets {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hε : ε ≤ 1 / 64)
    (hδ : |e| * (s / 2) * M ≤ 1) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvs : v ≤ s) :
    (eVariationOn (S.a u) (Icc u v)).toReal ≤
        4 / 3 * ∫ x in u..v, (outEnv 0 (jC1 (triangle 0 s) S) x).toReal ∧
      (∫ x in u..v,
        ‖pdU (triangle 0 s) S.b x v + I * e * S.A x v * S.b x v‖) ≤
        4 / 3 * ∫ x in u..v, (inEnv s (kC1 e (triangle 0 s) S) x).toReal := by
  have hε0 := hset.eps_nonneg
  have hcoeff : (15 : ℝ) / 16 ≤ 1 - 16 * ε ^ 2 := by
    nlinarith only [hε, hε0]
  have hinv (a b : ℝ) (hp : (a, b) ∈ triangle 0 s) : (1 - S.mu a b)⁻¹ ≤ 8 / 7 := by
    have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 7 / 8)
      (hset.mass_gap_seven_eighths hε hδ hp)
    norm_num at hi
    exact hi
  have hsupj := reciprocal_sup_bound (by norm_num : (0 : ℝ) ≤ 8 / 7)
    (fun w hw => hinv u w ⟨hu, hw.1, hw.2.trans hvs⟩)
  have hsupk := reciprocal_sup_bound (by norm_num : (0 : ℝ) ≤ 8 / 7)
    (fun w hw => hinv w v ⟨hu.trans hw.1, hw.2, hvs⟩)
  have hJ0 : 0 ≤ ∫ x in u..v, (outEnv 0 (jC1 (triangle 0 s) S) x).toReal :=
    intervalIntegral.integral_nonneg huv (fun _ _ => ENNReal.toReal_nonneg)
  have hK0 : 0 ≤ ∫ x in u..v, (inEnv s (kC1 e (triangle 0 s) S) x).toReal :=
    intervalIntegral.integral_nonneg huv (fun _ _ => ENNReal.toReal_nonneg)
  have hj := (bv_tvj hset hu huv hvs).trans (mul_le_mul_of_nonneg_right hsupj hJ0)
  have hk := (bv_tvk hset hu huv hvs).trans (mul_le_mul_of_nonneg_right hsupk hK0)
  constructor
  · have hi := mul_le_mul_of_nonneg_right hcoeff
      (show 0 ≤ (eVariationOn (S.a u) (Icc u v)).toReal from ENNReal.toReal_nonneg)
    linarith only [hi, hj, hJ0]
  · have hV0 : 0 ≤ ∫ x in u..v,
        ‖pdU (triangle 0 s) S.b x v + I * e * S.A x v * S.b x v‖ :=
      intervalIntegral.integral_nonneg huv (fun _ _ => norm_nonneg _)
    have hi := mul_le_mul_of_nonneg_right hcoeff hV0
    linarith only [hi, hk, hK0]

/-- Closed individual envelope bounds imply individual characteristic
variation bounds with coefficient `3/2`. This conditional helper has exact
numerical coefficients, universal in all parameters and higher derivatives;
the envelope node discharges both envelope premises. -/
theorem closed_variations_of_envelopes {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hε : ε ≤ 1 / 64)
    (hδ : |e| * (s / 2) * M ≤ 1)
    (hJ : (∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 s) S) v) ≤
      ENNReal.ofReal (9 / 8 * ε))
    (hK : (∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 s) S) u) ≤
      ENNReal.ofReal (9 / 8 * ε)) :
    (⨆ u ∈ Icc 0 s, eVariationOn (S.a u) (Icc u s)) ≤ ENNReal.ofReal (3 / 2 * ε) ∧
      (⨆ v ∈ Icc 0 s, ∫⁻ u in Icc 0 v,
        ‖pdU (triangle 0 s) S.b u v + I * e * S.A u v * S.b u v‖ₑ) ≤
        ENNReal.ofReal (3 / 2 * ε) := by
  have hε0 := hset.eps_nonneg
  have hrJ : (∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 s) S) v).toReal ≤
      9 / 8 * ε := ENNReal.toReal_le_of_le_ofReal (by positivity) hJ
  have hrK : (∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 s) S) u).toReal ≤
      9 / 8 * ε := ENNReal.toReal_le_of_le_ofReal (by positivity) hK
  rw [outgoing_envelope_integral_toReal hset.pos hset.c1] at hrJ
  rw [incoming_envelope_integral_toReal hset.pos hset.c1] at hrK
  constructor
  · apply iSup₂_le
    intro u hu
    have ca : ContDiffOn ℝ 1 (S.a u) (Icc u s) :=
      hset.c1.c1_a.comp (contDiffOn_const.prodMk contDiffOn_id)
        (fun v hv => ⟨hu.1, hv.1, hv.2⟩)
    have hac : AbsolutelyContinuousOnInterval (S.a u) u s := by
      apply ContDiffOn.absolutelyContinuousOnInterval
      simpa only [uIcc_of_le hu.2] using ca
    have hm := intervalIntegral.integral_mono_interval hu.1 hu.2 le_rfl
      (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
      (apriori_envelopes_integrable hset).1
    have hv := (characteristic_variation_sharp_budgets hset hε hδ hu.1 hu.2 le_rfl).1
    have hb : (eVariationOn (S.a u) (Icc u s)).toReal ≤ 3 / 2 * ε := by
      linarith only [hv, hm, hrJ]
    rw [← ENNReal.ofReal_toReal (hac.boundedVariationOn_Icc hu.2)]
    exact ENNReal.ofReal_le_ofReal hb
  · apply iSup₂_le
    intro v hv
    let q := fun u => pdU (triangle 0 s) S.b u v + I * e * S.A u v * S.b u v
    have hsec : MapsTo (fun u => (u, v)) (Icc 0 v) (triangle 0 s) :=
      fun u hu => ⟨hu.1, hu.2, hv.2⟩
    have cq : ContinuousOn q (Icc 0 v) := by
      apply ((continuousOn_pdU hset.c1.c1_b (uniqueDiffOn_triangle hset.pos)).add
        (((continuousOn_const (c := I * e)).mul
          (Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_A.continuousOn)).mul
            hset.c1.c1_b.continuousOn)).comp
              (continuous_id.prodMk continuous_const).continuousOn hsec
    have hi := cq.intervalIntegrable_of_Icc (μ := volume) hv.1
    have hm := intervalIntegral.integral_mono_interval le_rfl hv.1 hv.2
      (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
      (apriori_envelopes_integrable hset).2
    have ht := (characteristic_variation_sharp_budgets hset hε hδ le_rfl hv.1 hv.2).2
    have hb : (∫ u in 0..v, ‖q u‖) ≤ 3 / 2 * ε := by
      linarith only [ht, hm, hrK]
    have he : (∫⁻ u in Icc 0 v, ‖q u‖ₑ) = ENNReal.ofReal (∫ u in 0..v, ‖q u‖) := by
      rw [intervalIntegral.integral_of_le hv.1, ← integral_Icc_eq_integral_Ioc,
        ofReal_integral_norm_eq_lintegral_enorm
          ((intervalIntegrable_iff_integrableOn_Icc_of_le hv.1).mp hi)]
    rw [he]
    exact ENNReal.ofReal_le_ofReal hb

end EmcsfAcExtension.Local
