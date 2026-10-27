module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.AreaJAux
import EmcsfAcExtension.Local.Apriori.AreaJKernel
import EmcsfAcExtension.Local.Apriori.Hardy
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Calculus.TriangleDiff
import EmcsfAcExtension.Infra.AC.Variation

/-! # Outgoing scalar curvature area bound

The primitive variable is retained until after the outgoing inverse-cube
kernel has been integrated. The remaining integral is the incoming Hardy
budget, exactly as in `charged_SF_new_version.tex:L4695–L4719`.
-/

public section

open Set MeasureTheory Filter Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem incoming_hardy_lintegral_le {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {a : ℝ} (ha : a ∈ Icc 0 T) :
    (∫⁻ u in Icc 0 a,
      ENNReal.ofReal (-S.nu u a / S.r u a * ‖S.xi u a / S.nu u a‖)) ≤
      ∫⁻ u in Icc 0 a,
        ‖pdU (triangle 0 T) S.b u a + I * e * S.A u a * S.b u a‖ₑ := by
  have hh := bv_hardy_in_integrated hset.c1 le_rfl ha.1 ha.2
  have hm : MapsTo (fun u => (u, a)) (Icc 0 a) (triangle 0 T) :=
    fun u hu => ⟨hu.1, hu.2, ha.2⟩
  have cb := hset.c1.c1_b.continuousOn
  have cp := continuousOn_pdU hset.c1.c1_b (uniqueDiffOn_triangle hset.pos)
  have cf : ContinuousOn
      (fun u => pdU (triangle 0 T) S.b u a + I * e * S.A u a * S.b u a) (Icc 0 a) :=
    (cp.add (((continuousOn_const (c := I * (e : ℂ))).mul
      (Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_A.continuousOn)).mul cb)).comp
      (continuous_id.prodMk continuous_const).continuousOn hm
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Icc_of_le ha.1).mp hh.1)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact mul_nonneg (div_nonneg
        (neg_pos.mpr (hset.c1.nu_neg (u, a) (hm hu))).le
        (hset.radius_nonneg (hm hu))) (norm_nonneg _)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.1]
  apply (ENNReal.ofReal_le_ofReal hh.2).trans_eq
  rw [intervalIntegral.integral_of_le ha.1, ← integral_Icc_eq_integral_Ioc]
  exact ofReal_integral_norm_eq_lintegral_enorm
    ((intervalIntegrable_iff_integrableOn_Icc_of_le ha.1).mp
      (cf.intervalIntegrable_of_Icc (μ := volume) ha.1))

private theorem coordinate_hardy_lintegral_le {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) {F : ℝ × ℝ → ℝ≥0∞} {J : ℝ → ℝ≥0∞}
    (hF_eq : ∀ {u a : ℝ}, (u, a) ∈ triangle 0 s →
      F (u, a) = ENNReal.ofReal (S.r u a) * ‖S.xi u a / S.nu u a‖ₑ * J a)
    {a : ℝ} (ha : a ∈ Icc 0 s) :
    (∫⁻ u in Icc 0 a, ENNReal.ofReal (1 / (2 * (a - u) ^ 2)) * F (u, a)) ≤
      ENNReal.ofReal 2 * (∫⁻ u in Icc 0 a,
        ENNReal.ofReal (-S.nu u a / S.r u a * ‖S.xi u a / S.nu u a‖)) * J a := by
  let D := triangle 0 s
  have hHi := (intervalIntegrable_iff_integrableOn_Icc_of_le ha.1).mp
    (bv_hardy_in_integrated hset.c1 le_rfl ha.1 ha.2).1
  have hHm : AEMeasurable
      (fun u => ENNReal.ofReal (-S.nu u a / S.r u a * ‖S.xi u a / S.nu u a‖))
      (volume.restrict (Icc 0 a)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hHi.aestronglyMeasurable.aemeasurable
  have hw : (∫⁻ u in Icc 0 a, ENNReal.ofReal (1 / (2 * (a - u) ^ 2)) * F (u, a)) ≤
      ENNReal.ofReal 2 * (∫⁻ u in Icc 0 a,
        ENNReal.ofReal (-S.nu u a / S.r u a * ‖S.xi u a / S.nu u a‖)) * J a := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_mul_const'' (J a) (hHm.const_mul (ENNReal.ofReal 2))]
    have hne : ∀ᵐ u : ℝ, u ≠ a := by simp [ae_iff, measure_singleton]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with u hu hne
    have hp : (u, a) ∈ D := ⟨hu.1, hu.2, ha.2⟩
    have hr := hset.c1.r_pos (u, a) hp (lt_of_le_of_ne hu.2 hne)
    have hru := (Area.radius_bounds hset hu.1 hu.2 ha.2).2
    have hn := (hset.box (u, a) hp).2.2.1
    have hd : 0 < a - u := sub_pos.mpr (lt_of_le_of_ne hu.2 hne)
    have hb : S.r u a / (2 * (a - u) ^ 2) ≤ 2 * (-S.nu u a) / S.r u a := by
      apply (div_le_div_iff₀ (by positivity) hr).mpr
      have hs := pow_le_pow_left₀ hr.le hru 2
      have hprod := mul_le_mul_of_nonneg_right hn (sq_nonneg (a - u))
      nlinarith only [hs, hprod]
    rw [hF_eq hp, ← ofReal_norm]
    calc
      _ = ENNReal.ofReal (S.r u a / (2 * (a - u) ^ 2)) *
          ENNReal.ofReal ‖S.xi u a / S.nu u a‖ * J a := by
        rw [← mul_assoc, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * (a - u) ^ 2))]
        congr 2
        ring
      _ ≤ ENNReal.ofReal (2 * (-S.nu u a) / S.r u a) *
          ENNReal.ofReal ‖S.xi u a / S.nu u a‖ * J a := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (-S.nu u a) / S.r u a),
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 2
        ring
  exact hw

/-- [node restart-bv-area-j]
The outgoing scalar curvature source has its area bound with the incoming
covariant derivative budget retained. The universal constant depends only
on the fixed bootstrap box, independently of `e`, `s`, `ε`, `M`, and all
initial derivative norms. No smallness assumption on `ε` is needed.
The companion `bv_area_j_kernel` exports the literal weighted-kernel chain;
its conclusion alone does not include domination of this scalar source.
-/
theorem bv_area_j : ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h →
    (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s,
      ‖S.nu u v * S.theta u v / S.r u v ^ 2 * curvScalar (triangle 0 s) S u v‖ₑ) ≤
    ENNReal.ofReal (C * ε) *
      (⨆ a ∈ Icc 0 s, ∫⁻ u in Icc 0 a,
        ‖pdU (triangle 0 s) S.b u a + I * e * S.A u a * S.b u a‖ₑ) *
      ∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 s) S) v := by
  refine ⟨512, by norm_num, ?_⟩
  intro e s ε M S h hset
  classical
  let D := triangle 0 s
  let J := (Icc 0 s).indicator (outEnv 0 (jC1 D S))
  let R := D.indicator (Function.uncurry S.r)
  let Y := D.indicator (fun p => S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ))
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (R p) * ‖Y p‖ₑ * J p.2
  let B : ℝ≥0∞ := ⨆ a ∈ Icc 0 s, ∫⁻ u in Icc 0 a,
    ‖pdU D S.b u a + I * e * S.A u a * S.b u a‖ₑ
  have hJ : Measurable J := measurable_indicator_outEnv
    (continuousOn_jC1_aux hset.pos hset.c1)
  have hR : Measurable R := Area.measurable_triangle_extension hset.c1.c1_r.continuousOn
  have hY : Measurable Y := Area.measurable_triangle_extension
    (hset.c1.c1_xi.continuousOn.div
      (Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_nu.continuousOn)
      (fun p hp => Complex.ofReal_ne_zero.mpr (hset.c1.nu_neg p hp).ne))
  have hF : Measurable F := by fun_prop
  have hF_eq {u a : ℝ} (hp : (u, a) ∈ D) :
      F (u, a) = ENNReal.ofReal (S.r u a) * ‖S.xi u a / S.nu u a‖ₑ * J a := by
    simp only [F, R, Y, indicator_of_mem hp, Function.uncurry_def]
  have hpoint {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvs : v ≤ s) :
      ‖S.nu u v * S.theta u v / S.r u v ^ 2 * curvScalar D S u v‖ₑ ≤
      ENNReal.ofReal (256 * ε) *
        (ENNReal.ofReal (1 / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (u, a)) := by
    let c := (S.nu u v * S.theta u v / (S.r u v : ℂ) ^ 2) * (S.r u v : ℂ)⁻¹
    have hc : ‖c‖ₑ ≤ ENNReal.ofReal (256 * ε / (v - u) ^ 3) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (Area.scalar_out_coefficient_le hset hu huv hvs)
    have hp : ‖S.nu u v * S.theta u v / S.r u v ^ 2 * curvScalar D S u v‖ₑ ≤
        ‖c‖ₑ * ∫⁻ a in Icc u v, F (u, a) := by
      rw [curvScalar, intervalIntegral.integral_of_le huv.le, ← mul_assoc, enorm_mul,
        restrict_Ioc_eq_restrict_Icc]
      apply mul_le_mul' le_rfl
      apply (enorm_integral_le_lintegral_enorm _).trans
      apply setLIntegral_mono' measurableSet_Icc
      intro a ha
      have hpa : (u, a) ∈ D := ⟨hu, ha.1, ha.2.trans hvs⟩
      rw [hF_eq hpa, enorm_mul, enorm_mul, RCLike.enorm_conj]
      have hr : ‖(S.r u a : ℂ)‖ₑ = ENNReal.ofReal (S.r u a) := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hset.radius_nonneg hpa)]
      rw [hr]
      apply mul_le_mul' le_rfl
      dsimp only [J]
      rw [indicator_of_mem (show a ∈ Icc 0 s from ⟨hu.trans ha.1, ha.2.trans hvs⟩)]
      exact enorm_le_normEnvelope (jC1 D S) ⟨hu, ha.1⟩
    apply hp.trans
    calc
      _ ≤ ENNReal.ofReal (256 * ε / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (u, a) :=
        mul_le_mul' hc le_rfl
      _ = _ := by
        rw [div_eq_mul_one_div, ENNReal.ofReal_mul
          (mul_nonneg (by norm_num) hset.eps_nonneg), mul_assoc]
  have harea :
      (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s,
        ‖S.nu u v * S.theta u v / S.r u v ^ 2 * curvScalar D S u v‖ₑ) ≤
      ENNReal.ofReal (256 * ε) * ∫⁻ a in Icc 0 s, ∫⁻ u in Icc 0 a,
        ENNReal.ofReal (1 / (2 * (a - u) ^ 2)) * F (u, a) := by
    apply le_trans (b := ENNReal.ofReal (256 * ε) * ∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s,
      ENNReal.ofReal (1 / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (u, a))
    · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hne : ∀ᵐ v : ℝ, v ≠ u := by simp [ae_iff, measure_singleton]
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with v hv hne
      exact hpoint hu.1 (lt_of_le_of_ne hv.1 hne.symm) hv.2
    · exact mul_le_mul' le_rfl (Area.outgoing_primitive_area_le hF)
  have hinner {a : ℝ} (ha : a ∈ Icc 0 s) :
      (∫⁻ u in Icc 0 a, ENNReal.ofReal (1 / (2 * (a - u) ^ 2)) * F (u, a)) ≤
        ENNReal.ofReal 2 * B * J a := by
    have hw := coordinate_hardy_lintegral_le hset hF_eq ha
    exact hw.trans (mul_le_mul' (mul_le_mul' le_rfl
      ((incoming_hardy_lintegral_le hset ha).trans
        (le_iSup₂_of_le a ha le_rfl))) le_rfl)
  apply harea.trans
  calc
    _ ≤ ENNReal.ofReal (256 * ε) * ∫⁻ a in Icc 0 s, ENNReal.ofReal 2 * B * J a :=
      mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Icc (fun a ha => hinner ha))
    _ = _ := by
      rw [lintegral_const_mul'' _ hJ.aemeasurable.restrict]
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul
        (mul_nonneg (by norm_num) hset.eps_nonneg)]
      have hmass : (∫⁻ a in Icc 0 s, J a) =
          ∫⁻ a in Icc 0 s, outEnv 0 (jC1 D S) a := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro a ha
        exact indicator_of_mem ha _
      rw [hmass]
      congr 3
      ring

/-- [node restart-bv-area-j]
The literal weighted-kernel chain of charged_SF_new_version.tex:L4699–L4706, retaining
its intermediate incoming Hardy integral. One universal constant works in
both inequalities, independently of `e,s,ε,M,S,h` and all derivative norms;
no smallness assumption is used. The companion `bv_area_j` retains the
actual scalar-source estimate, whose pointwise domination is separate.
-/
theorem bv_area_j_kernel : ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h →
    (ENNReal.ofReal ε * (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s,
      ENNReal.ofReal ((-S.nu u v) * S.lam u v / S.r u v ^ 3) *
        ∫⁻ a in Icc u v, ENNReal.ofReal (S.r u a) * ‖S.xi u a / S.nu u a‖ₑ *
          outEnv 0 (jC1 (triangle 0 s) S) a) ≤
      ENNReal.ofReal (C * ε) * (∫⁻ a in Icc 0 s,
        (∫⁻ u in Icc 0 a, ENNReal.ofReal
          (-S.nu u a / S.r u a * ‖S.xi u a / S.nu u a‖)) *
        outEnv 0 (jC1 (triangle 0 s) S) a)) ∧
    (ENNReal.ofReal (C * ε) * (∫⁻ a in Icc 0 s,
        (∫⁻ u in Icc 0 a, ENNReal.ofReal
          (-S.nu u a / S.r u a * ‖S.xi u a / S.nu u a‖)) *
        outEnv 0 (jC1 (triangle 0 s) S) a) ≤
      ENNReal.ofReal (C * ε) *
        (⨆ a ∈ Icc 0 s, ∫⁻ u in Icc 0 a,
          ‖pdU (triangle 0 s) S.b u a + I * e * S.A u a * S.b u a‖ₑ) *
        ∫⁻ a in Icc 0 s, outEnv 0 (jC1 (triangle 0 s) S) a) := by
  refine ⟨128, by norm_num, ?_⟩
  intro e s ε M S h hset
  classical
  let D := triangle 0 s
  let J := (Icc 0 s).indicator (outEnv 0 (jC1 D S))
  let R := D.indicator (Function.uncurry S.r)
  let Y := D.indicator (fun p => S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ))
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (R p) * ‖Y p‖ₑ * J p.2
  let B : ℝ≥0∞ := ⨆ a ∈ Icc 0 s, ∫⁻ u in Icc 0 a,
    ‖pdU D S.b u a + I * e * S.A u a * S.b u a‖ₑ
  have hJ : Measurable J := measurable_indicator_outEnv
    (continuousOn_jC1_aux hset.pos hset.c1)
  have hR : Measurable R := Area.measurable_triangle_extension hset.c1.c1_r.continuousOn
  have hY : Measurable Y := Area.measurable_triangle_extension
    (hset.c1.c1_xi.continuousOn.div
      (Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_nu.continuousOn)
      (fun p hp => Complex.ofReal_ne_zero.mpr (hset.c1.nu_neg p hp).ne))
  have hF : Measurable F := by fun_prop
  have hF_eq {u a : ℝ} (hp : (u, a) ∈ D) :
      F (u, a) = ENNReal.ofReal (S.r u a) * ‖S.xi u a / S.nu u a‖ₑ * J a := by
    simp only [F, R, Y, indicator_of_mem hp, Function.uncurry_def]
  let H : ℝ≥0∞ := ∫⁻ a in Icc 0 s,
    (∫⁻ u in Icc 0 a, ENNReal.ofReal
      (-S.nu u a / S.r u a * ‖S.xi u a / S.nu u a‖)) * J a
  have hmass : (∫⁻ a in Icc 0 s, J a) =
      ∫⁻ a in Icc 0 s, outEnv 0 (jC1 D S) a := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro a ha
    exact indicator_of_mem ha _
  have hH : H = ∫⁻ a in Icc 0 s,
      (∫⁻ u in Icc 0 a, ENNReal.ofReal
        (-S.nu u a / S.r u a * ‖S.xi u a / S.nu u a‖)) *
        outEnv 0 (jC1 D S) a := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro a ha
    dsimp only
    rw [show J a = outEnv 0 (jC1 D S) a from indicator_of_mem ha _]
  have hcoordinate : (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s,
      ENNReal.ofReal (1 / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (u, a)) ≤
      ENNReal.ofReal 2 * H := by
    apply (Area.outgoing_primitive_area_le hF).trans
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro a ha
    simpa only [mul_assoc] using coordinate_hardy_lintegral_le hset hF_eq ha
  have hweighted : (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s,
      ENNReal.ofReal ((-S.nu u v) * S.lam u v / S.r u v ^ 3) *
        ∫⁻ a in Icc u v, ENNReal.ofReal (S.r u a) * ‖S.xi u a / S.nu u a‖ₑ *
          outEnv 0 (jC1 D S) a) ≤
      ENNReal.ofReal 64 * (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s,
        ENNReal.ofReal (1 / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (u, a)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro u hu
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hne : ∀ᵐ v : ℝ, v ≠ u := by simp [ae_iff, measure_singleton]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with v hv hne
    have huv : u < v := lt_of_le_of_ne hv.1 hne.symm
    have hp : (u, v) ∈ D := ⟨hu.1, hv.1, hv.2⟩
    have hr := hset.c1.r_pos (u, v) hp huv
    have hb := hset.box (u, v) hp
    have hcoef : (-S.nu u v) * S.lam u v / S.r u v ^ 3 ≤ 64 / (v - u) ^ 3 := by
      calc
        _ ≤ 1 / S.r u v ^ 3 := by
          apply div_le_div_of_nonneg_right _ (pow_nonneg hr.le _)
          simpa using mul_le_mul hb.2.2.2.1 hb.2.1
            (hset.c1.lam_pos (u, v) hp).le (by norm_num : (0 : ℝ) ≤ 1)
        _ ≤ 1 / ((v - u) / 4) ^ 3 := by
          gcongr
          exact (Area.radius_bounds hset hu.1 hv.1 hv.2).1
        _ = _ := by field_simp; ring
    have hFeq : (∫⁻ a in Icc u v, F (u, a)) =
        ∫⁻ a in Icc u v, ENNReal.ofReal (S.r u a) * ‖S.xi u a / S.nu u a‖ₑ *
          outEnv 0 (jC1 D S) a := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro a ha
      dsimp only
      rw [hF_eq ⟨hu.1, ha.1, ha.2.trans hv.2⟩]
      rw [show J a = outEnv 0 (jC1 D S) a from
        indicator_of_mem (show a ∈ Icc 0 s from ⟨hu.1.trans ha.1, ha.2.trans hv.2⟩) _]
    rw [← hFeq, ← mul_assoc]
    apply mul_le_mul' _ le_rfl
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_one_div] using hcoef
  constructor
  · apply (mul_le_mul' le_rfl hweighted).trans
    apply (mul_le_mul' le_rfl (mul_le_mul' le_rfl hcoordinate)).trans_eq
    rw [hH]
    simp only [← mul_assoc]
    rw [← ENNReal.ofReal_mul hset.eps_nonneg,
      ← ENNReal.ofReal_mul (mul_nonneg hset.eps_nonneg (by norm_num))]
    congr 2
    ring
  · rw [← hH, mul_assoc]
    apply mul_le_mul' le_rfl
    calc
      H ≤ ∫⁻ a in Icc 0 s, B * J a := by
        apply setLIntegral_mono' measurableSet_Icc
        intro a ha
        apply mul_le_mul' _ le_rfl
        exact (incoming_hardy_lintegral_le hset ha).trans (le_iSup₂_of_le a ha le_rfl)
      _ = B * ∫⁻ a in Icc 0 s, outEnv 0 (jC1 D S) a := by
        rw [lintegral_const_mul'' _ hJ.aemeasurable.restrict, hmass]

end EmcsfAcExtension.Local
