module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.AreaJAux
import EmcsfAcExtension.Local.Apriori.AreaKKernel
import EmcsfAcExtension.Local.Apriori.Hardy
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Calculus.TriangleDiff
import EmcsfAcExtension.Infra.AC.Variation

/-! # Incoming scalar curvature area bound

The reflected three-variable integration leaves the outgoing Hardy budget.
This is the approved incoming calculation in internal project record,
equation (16), for `charged_SF_new_version.tex:L4721–L4730`.
-/

public section

open Set MeasureTheory Filter Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem outgoing_hardy_lintegral_le {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {a : ℝ} (ha : a ∈ Icc 0 T) :
    (∫⁻ v in Icc a T,
      ENNReal.ofReal (S.lam a v / S.r a v * ‖S.theta a v / S.lam a v‖)) ≤
      eVariationOn (S.a a) (Icc a T) := by
  have hh := bv_hardy_out_integrated hset.c1 ha.1 ha.2 le_rfl
  have ca : ContDiffOn ℝ 1 (S.a a) (Icc a T) :=
    hset.c1.c1_a.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun v hv => ⟨ha.1, hv.1, hv.2⟩)
  have hac : AbsolutelyContinuousOnInterval (S.a a) a T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le ha.2] using ca
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Icc_of_le ha.2).mp hh.1)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      have hp : (a, v) ∈ triangle 0 T := ⟨ha.1, hv.1, hv.2⟩
      exact mul_nonneg (div_nonneg (hset.c1.lam_pos (a, v) hp).le
        (hset.radius_nonneg hp)) (norm_nonneg _)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.2]
  exact (ENNReal.ofReal_le_ofReal hh.2).trans_eq
    (ENNReal.ofReal_toReal (hac.boundedVariationOn_Icc ha.2))

/-- [node restart-bv-area-k]
The incoming scalar curvature source has its area bound with the outgoing
variation budget retained. The universal constant depends only on the fixed
bootstrap box, independently of the coupling, interval, background size, and
all initial derivative norms. No smallness of `ε` is assumed.
-/
theorem bv_area_k : ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h →
    (∫⁻ v in Icc 0 s, ∫⁻ u in Icc 0 v,
      ‖S.lam u v * S.xi u v / S.r u v ^ 2 * curvScalarIn e (triangle 0 s) S u v‖ₑ) ≤
    ENNReal.ofReal (C * ε) *
      (⨆ a ∈ Icc 0 s, eVariationOn (S.a a) (Icc a s)) *
      ∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 s) S) u := by
  refine ⟨512, by norm_num, ?_⟩
  intro e s ε M S h hset
  classical
  let D := triangle 0 s
  let K := (Icc 0 s).indicator (inEnv s (kC1 e D S))
  let R := D.indicator (Function.uncurry S.r)
  let X := D.indicator (fun p => S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ))
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (R p) * ‖X p‖ₑ * K p.1
  let B : ℝ≥0∞ := ⨆ a ∈ Icc 0 s, eVariationOn (S.a a) (Icc a s)
  have hK : Measurable K := measurable_indicator_inEnv
    (continuousOn_kC1_aux hset.pos hset.c1)
  have hR : Measurable R := Area.measurable_triangle_extension hset.c1.c1_r.continuousOn
  have hX : Measurable X := Area.measurable_triangle_extension
    (hset.c1.c1_theta.continuousOn.div
      (Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_lam.continuousOn)
      (fun p hp => Complex.ofReal_ne_zero.mpr (hset.c1.lam_pos p hp).ne'))
  have hF : Measurable F := by fun_prop
  have hF_eq {a v : ℝ} (hp : (a, v) ∈ D) :
      F (a, v) = ENNReal.ofReal (S.r a v) * ‖S.theta a v / S.lam a v‖ₑ * K a := by
    simp only [F, R, X, indicator_of_mem hp, Function.uncurry_def]
  have hpoint {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvs : v ≤ s) :
      ‖S.lam u v * S.xi u v / S.r u v ^ 2 * curvScalarIn e D S u v‖ₑ ≤
      ENNReal.ofReal (256 * ε) *
        (ENNReal.ofReal (1 / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (a, v)) := by
    let c := (S.lam u v * S.xi u v / (S.r u v : ℂ) ^ 2) * (S.r u v : ℂ)⁻¹
    have hc : ‖c‖ₑ ≤ ENNReal.ofReal (256 * ε / (v - u) ^ 3) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (Area.scalar_in_coefficient_le hset hu huv hvs)
    have hp : ‖S.lam u v * S.xi u v / S.r u v ^ 2 * curvScalarIn e D S u v‖ₑ ≤
        ‖c‖ₑ * ∫⁻ a in Icc u v, F (a, v) := by
      rw [curvScalarIn, mul_neg, enorm_neg, intervalIntegral.integral_of_le huv.le,
        ← mul_assoc, enorm_mul, restrict_Ioc_eq_restrict_Icc]
      apply mul_le_mul' le_rfl
      apply (enorm_integral_le_lintegral_enorm _).trans
      apply setLIntegral_mono' measurableSet_Icc
      intro a ha
      have hpa : (a, v) ∈ D := ⟨hu.trans ha.1, ha.2, hvs⟩
      rw [hF_eq hpa, enorm_mul, enorm_mul, RCLike.enorm_conj]
      have hr : ‖(S.r a v : ℂ)‖ₑ = ENNReal.ofReal (S.r a v) := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hset.radius_nonneg hpa)]
      rw [hr]
      apply mul_le_mul' le_rfl
      dsimp only [K]
      rw [indicator_of_mem (show a ∈ Icc 0 s from ⟨hu.trans ha.1, ha.2.trans hvs⟩)]
      exact le_iSup₂_of_le v ⟨ha.2, hvs⟩ le_rfl
    apply hp.trans
    calc
      _ ≤ ENNReal.ofReal (256 * ε / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (a, v) :=
        mul_le_mul' hc le_rfl
      _ = _ := by
        rw [div_eq_mul_one_div, ENNReal.ofReal_mul
          (mul_nonneg (by norm_num) hset.eps_nonneg), mul_assoc]
  have harea :
      (∫⁻ v in Icc 0 s, ∫⁻ u in Icc 0 v,
        ‖S.lam u v * S.xi u v / S.r u v ^ 2 * curvScalarIn e D S u v‖ₑ) ≤
      ENNReal.ofReal (256 * ε) * ∫⁻ a in Icc 0 s, ∫⁻ v in Icc a s,
        ENNReal.ofReal (1 / (2 * (v - a) ^ 2)) * F (a, v) := by
    apply le_trans (b := ENNReal.ofReal (256 * ε) * ∫⁻ v in Icc 0 s, ∫⁻ u in Icc 0 v,
      ENNReal.ofReal (1 / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (a, v))
    · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_mono' measurableSet_Icc
      intro v hv
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hne : ∀ᵐ u : ℝ, u ≠ v := by simp [ae_iff, measure_singleton]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with u hu hne
      exact hpoint hu.1 (lt_of_le_of_ne hu.2 hne) hv.2
    · exact mul_le_mul' le_rfl (Area.incoming_primitive_area_le hF)
  have hinner {a : ℝ} (ha : a ∈ Icc 0 s) :
      (∫⁻ v in Icc a s, ENNReal.ofReal (1 / (2 * (v - a) ^ 2)) * F (a, v)) ≤
        ENNReal.ofReal 2 * B * K a := by
    have hHi := (intervalIntegrable_iff_integrableOn_Icc_of_le ha.2).mp
      (bv_hardy_out_integrated hset.c1 ha.1 ha.2 le_rfl).1
    have hHm : AEMeasurable
        (fun v => ENNReal.ofReal (S.lam a v / S.r a v * ‖S.theta a v / S.lam a v‖))
        (volume.restrict (Icc a s)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hHi.aestronglyMeasurable.aemeasurable
    have hw : (∫⁻ v in Icc a s, ENNReal.ofReal (1 / (2 * (v - a) ^ 2)) * F (a, v)) ≤
        ENNReal.ofReal 2 * (∫⁻ v in Icc a s,
          ENNReal.ofReal (S.lam a v / S.r a v * ‖S.theta a v / S.lam a v‖)) * K a := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_mul_const'' (K a) (hHm.const_mul (ENNReal.ofReal 2))]
      have hne : ∀ᵐ v : ℝ, v ≠ a := by simp [ae_iff, measure_singleton]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with v hv hne
      have hp : (a, v) ∈ D := ⟨ha.1, hv.1, hv.2⟩
      have hr := hset.c1.r_pos (a, v) hp (lt_of_le_of_ne hv.1 hne.symm)
      have hru := (Area.radius_bounds hset ha.1 hv.1 hv.2).2
      have hl := (hset.box (a, v) hp).1
      have hd : 0 < v - a := sub_pos.mpr (lt_of_le_of_ne hv.1 hne.symm)
      have hb : S.r a v / (2 * (v - a) ^ 2) ≤ 2 * S.lam a v / S.r a v := by
        apply (div_le_div_iff₀ (by positivity) hr).mpr
        have hs := pow_le_pow_left₀ hr.le hru 2
        have hprod := mul_le_mul_of_nonneg_right hl (sq_nonneg (v - a))
        nlinarith only [hs, hprod]
      rw [hF_eq hp, ← ofReal_norm]
      calc
        _ = ENNReal.ofReal (S.r a v / (2 * (v - a) ^ 2)) *
            ENNReal.ofReal ‖S.theta a v / S.lam a v‖ * K a := by
          rw [← mul_assoc, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * (v - a) ^ 2))]
          congr 2
          ring
        _ ≤ ENNReal.ofReal (2 * S.lam a v / S.r a v) *
            ENNReal.ofReal ‖S.theta a v / S.lam a v‖ * K a := by gcongr
        _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * S.lam a v / S.r a v),
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 2
          ring
    exact hw.trans (mul_le_mul' (mul_le_mul' le_rfl
      ((outgoing_hardy_lintegral_le hset ha).trans
        (le_iSup₂_of_le a ha le_rfl))) le_rfl)
  apply harea.trans
  calc
    _ ≤ ENNReal.ofReal (256 * ε) * ∫⁻ a in Icc 0 s, ENNReal.ofReal 2 * B * K a :=
      mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Icc (fun a ha => hinner ha))
    _ = _ := by
      rw [lintegral_const_mul'' _ hK.aemeasurable.restrict]
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul
        (mul_nonneg (by norm_num) hset.eps_nonneg)]
      have hmass : (∫⁻ a in Icc 0 s, K a) =
          ∫⁻ a in Icc 0 s, inEnv s (kC1 e D S) a := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro a ha
        exact indicator_of_mem ha _
      rw [hmass]
      congr 3
      ring

end EmcsfAcExtension.Local
