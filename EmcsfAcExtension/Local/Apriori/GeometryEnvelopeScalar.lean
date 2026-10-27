module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseFinal
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseNorms
import EmcsfAcExtension.Local.Apriori.AreaJAux
import EmcsfAcExtension.Local.Apriori.AreaJKernel
import EmcsfAcExtension.Local.Apriori.Hardy
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Calculus.TriangleDiff
import EmcsfAcExtension.Infra.AC.Variation

/-! # Scalar geometric transport source area

The outgoing inverse-cube calculation is performed with its scalar-ratio
factor removed. Tonelli leaves the incoming Hardy budget and the outgoing
envelope (`charged_SF_new_version.tex:L4878–L4883`, approved internal project record (32)–(33)).
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

private theorem geometric_scalar_coefficient_le {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖((S.nu u v : ℂ) * S.lam u v / (S.r u v : ℂ) ^ 2) *
      (S.r u v : ℂ)⁻¹‖ ≤ 256 / (v - u) ^ 3 := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := hset.c1.r_pos (u, v) hp huv
  have hl := hset.c1.lam_pos (u, v) hp
  have hn := hset.c1.nu_neg (u, v) hp
  have hb := hset.box (u, v) hp
  have hrb := (Area.radius_bounds hset hu huv.le hvT).1
  simp only [norm_mul, norm_div, norm_pow, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_neg hn, abs_of_pos hl, abs_of_pos hr]
  calc
    (-S.nu u v) * S.lam u v / S.r u v ^ 2 * (S.r u v)⁻¹ ≤
        1 * 1 / S.r u v ^ 2 * (S.r u v)⁻¹ := by
      gcongr
      · exact hb.2.2.2.1
      · exact hb.2.1
    _ = 1 / S.r u v ^ 3 := by field_simp
    _ ≤ 1 / ((v - u) / 4) ^ 3 := by gcongr
    _ = 64 / (v - u) ^ 3 := by field_simp; ring
    _ ≤ _ := by gcongr; norm_num

/-- Removing the scalar-ratio factor from the curvature transport area
calculation gives the universal coefficient `512` times the incoming
covariant variation budget and the outgoing envelope mass. The coefficient
is independent of every field parameter and higher initial derivative.
No smallness assumption is needed. -/
theorem scalar_geometric_area_preclosure :
    ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h →
    (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s,
      ‖S.nu u v * (S.lam u v : ℂ) / S.r u v ^ 2 * curvScalar (triangle 0 s) S u v‖ₑ) ≤
    ENNReal.ofReal (C) *
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
      ‖S.nu u v * (S.lam u v : ℂ) / S.r u v ^ 2 * curvScalar D S u v‖ₑ ≤
      ENNReal.ofReal ((256 : ℝ)) *
        (ENNReal.ofReal (1 / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (u, a)) := by
    let c := (S.nu u v * (S.lam u v : ℂ) / (S.r u v : ℂ) ^ 2) * (S.r u v : ℂ)⁻¹
    have hc : ‖c‖ₑ ≤ ENNReal.ofReal ((256 : ℝ) / (v - u) ^ 3) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (geometric_scalar_coefficient_le hset hu huv hvs)
    have hp : ‖S.nu u v * (S.lam u v : ℂ) / S.r u v ^ 2 * curvScalar D S u v‖ₑ ≤
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
      _ ≤ ENNReal.ofReal ((256 : ℝ) / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (u, a) :=
        mul_le_mul' hc le_rfl
      _ = _ := by
        rw [div_eq_mul_one_div, ENNReal.ofReal_mul
          (by norm_num : (0 : ℝ) ≤ 256), mul_assoc]
  have harea :
      (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s,
        ‖S.nu u v * (S.lam u v : ℂ) / S.r u v ^ 2 * curvScalar D S u v‖ₑ) ≤
      ENNReal.ofReal ((256 : ℝ)) * ∫⁻ a in Icc 0 s, ∫⁻ u in Icc 0 a,
        ENNReal.ofReal (1 / (2 * (a - u) ^ 2)) * F (u, a) := by
    apply le_trans (b := ENNReal.ofReal ((256 : ℝ)) * ∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s,
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
          congr 3
          ring
        _ ≤ ENNReal.ofReal (2 * (-S.nu u a) / S.r u a) *
            ENNReal.ofReal ‖S.xi u a / S.nu u a‖ * J a := by gcongr
        _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * (-S.nu u a) / S.r u a),
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 2
          ring
    exact hw.trans (mul_le_mul' (mul_le_mul' le_rfl
      ((incoming_hardy_lintegral_le hset ha).trans
        (le_iSup₂_of_le a ha le_rfl))) le_rfl)
  apply harea.trans
  calc
    _ ≤ ENNReal.ofReal ((256 : ℝ)) * ∫⁻ a in Icc 0 s, ENNReal.ofReal 2 * B * J a :=
      mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Icc (fun a ha => hinner ha))
    _ = _ := by
      rw [lintegral_const_mul'' _ hJ.aemeasurable.restrict]
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul
        (by norm_num : (0 : ℝ) ≤ 256)]
      have hmass : (∫⁻ a in Icc 0 s, J a) =
          ∫⁻ a in Icc 0 s, outEnv 0 (jC1 D S) a := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro a ha
        exact indicator_of_mem ha _
      rw [hmass]
      congr 3
      ring

/-- [node restart-sec-independent-area#scalar-geometric-area]
The scalar geometric transport source has area bounded both by `C K J`
and by `C ε²`. The common positive thresholds and `C` precede every datum
and depend only on the fixed box, uniformly in higher initial derivatives.
The inverse-cube kernel is integrated before the incoming Hardy budget. -/
theorem scalar_geometric_area : ∃ ε₀ δ₀ C : ℝ,
    0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
    let A := ∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T,
      ‖S.nu u v * (S.lam u v : ℂ) / S.r u v ^ 2 * curvScalar (triangle 0 T) S u v‖ₑ
    A ≤ ENNReal.ofReal C * (∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) u) *
        (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) v) ∧
      A ≤ ENNReal.ofReal (C * ε ^ 2) := by
  obtain ⟨Cp, hCp, harea⟩ := scalar_geometric_area_preclosure
  obtain ⟨ε₁, δ₀, hε₁, hδ₀, hclosed⟩ := bv_envelope_final_individual
  refine ⟨min ε₁ (1 / 8), δ₀, 3 * Cp, lt_min hε₁ (by norm_num), hδ₀,
    mul_pos (by norm_num) hCp, ?_⟩
  intro e T ε M S h hset hε hδ
  dsimp only
  have hp := harea e T ε M S h hset
  have hB := incoming_variation_sup_le hset (hε.trans (min_le_right _ _))
  obtain ⟨hJ, _, _, hV⟩ := hclosed e T ε M S h hset (hε.trans (min_le_left _ _)) hδ
  constructor
  · apply hp.trans
    calc
      _ ≤ ENNReal.ofReal Cp * (ENNReal.ofReal 3 *
          ∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) u) *
          ∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) v := by gcongr
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]; ring
  · apply hp.trans
    calc
      _ ≤ ENNReal.ofReal Cp * ENNReal.ofReal (3 / 2 * ε) *
          ENNReal.ofReal (9 / 8 * ε) := by gcongr
      _ = ENNReal.ofReal (Cp * (3 / 2 * ε) * (9 / 8 * ε)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hCp.le (by have := hset.eps_nonneg; positivity)),
          ENNReal.ofReal_mul hCp.le]
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have hn := mul_nonneg hCp.le (sq_nonneg ε)
        nlinarith only [hn]

end EmcsfAcExtension.Local
