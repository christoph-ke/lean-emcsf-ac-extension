module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.Hardy
import EmcsfAcExtension.Local.Apriori.TVEnvelope
import EmcsfAcExtension.Local.Apriori.TVEnvelopeAux
import EmcsfAcExtension.Infra.HardyQuadratic

/-! # Homogeneous amplification and damping

The outgoing homogeneous factor is controlled by the incoming quadratic
budget, and the incoming homogeneous coefficient is nonpositive, as in
`charged_SF_new_version.tex:L4674–L4679`.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Area

variable {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}

private theorem homogeneous_coeff_eq (hset : AprioriSetting e s ε M S h)
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 s) :
    -‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v) =
      -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2 := by
  have hn := (hset.c1.nu_neg (u, v) hp).ne
  by_cases hr : S.r u v = 0
  · simp [hr]
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  field_simp

private theorem quadratic_in_integrable (hset : AprioriSetting e s ε M S h)
    {v : ℝ} (hv : v ∈ Icc 0 s) :
    IntervalIntegrable (fun u => -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2)
      volume 0 v := by
  have hm : MapsTo (fun u => (u, v)) (Icc 0 v) (triangle 0 s) :=
    fun _ hu => ⟨hu.1, hu.2, hv.2⟩
  have cxi := hset.c1.c1_xi.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hm
  have cn := hset.c1.c1_nu.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hm
  have cy := cxi.div (Complex.continuous_ofReal.comp_continuousOn cn)
    (fun u hu => Complex.ofReal_ne_zero.mpr (hset.c1.nu_neg (u, v) (hm hu)).ne)
  have hi := (bv_hardy_in_integrated hset.c1 le_rfl hv.1 hv.2).1
  have hi' := (intervalIntegrable_iff_integrableOn_Icc_of_le hv.1).mp hi
  have hq := integrable_and_integral_weight_mul_norm_sq_le
    (cy.aestronglyMeasurable measurableSet_Icc)
    (show ∀ᵐ u ∂volume.restrict (Icc 0 v), 0 ≤ -S.nu u v / S.r u v from by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact div_nonneg (neg_pos.mpr (hset.c1.nu_neg (u, v) (hm hu))).le
        (hset.radius_nonneg (hm hu)))
    (show ∀ᵐ u ∂volume.restrict (Icc 0 v), -S.nu u v / S.r u v ≠ 0 →
      ‖S.xi u v / S.nu u v‖ ≤ 4 * ε from by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact fun _ => (hset.box (u, v) (hm hu)).2.2.2.2.2.2.2) hi'
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hv.1).mpr hq.1

/-- [node restart-sec-independent-area#homogeneous-transport-bounds]
Homogeneous `j` amplification on every subsegment and nonpositive `k`
coefficient (`charged_SF_new_version.tex:L4674–L4679`). `C` is universal, independent
of `e`, `s`, `M`, and higher data norms. The threshold `ε ≤ 1/8` is the
fixed cubic-absorption margin used by the landed quadratic budget. -/
theorem homogeneous_transport_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h → ε ≤ 1 / 8 →
      (∀ v ∈ Icc 0 s, ∀ a b, 0 ≤ a → a ≤ b → b ≤ v →
        Real.exp (∫ u in a..b, -‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v)) ≤
          Real.exp (C * ε * ∫ u in 0..s, (inEnv s (kC1 e (triangle 0 s) S) u).toReal)) ∧
      (∀ u v, (u, v) ∈ triangle 0 s →
        0 ≤ -‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v) ∧
        -‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v) ≤ 0) := by
  refine ⟨12, by norm_num, ?_⟩
  intro e s ε M S h hset hε
  constructor
  · intro v hv a b ha hab hb
    apply Real.exp_le_exp.mpr
    have heq : (∫ u in a..b, -‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v)) =
        ∫ u in a..b, -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hab] at hu
      exact homogeneous_coeff_eq hset ⟨ha.trans hu.1, hu.2.trans hb, hv.2⟩
    rw [heq]
    have hmono := intervalIntegral.integral_mono_interval ha hab hb
      (show ∀ᵐ u ∂volume.restrict (Ioc 0 v),
        0 ≤ -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2 from by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        exact mul_nonneg
          (div_nonneg (neg_pos.mpr (hset.c1.nu_neg (u, v) ⟨hu.1.le, hu.2, hv.2⟩)).le
            (hset.radius_nonneg ⟨hu.1.le, hu.2, hv.2⟩)) (sq_nonneg _))
      (quadratic_in_integrable hset hv)
    have hflux := bv_fluxes_in hset hε le_rfl hv.1 hv.2
    have henv := intervalIntegral.integral_mono_interval le_rfl hv.1 hv.2
      (ae_of_all _ (fun _ => ENNReal.toReal_nonneg)) (apriori_envelopes_integrable hset).2
    exact hmono.trans (hflux.trans
      (mul_le_mul_of_nonneg_left henv (mul_nonneg (by norm_num) hset.eps_nonneg)))
  · intro u v hp
    constructor
    · rw [homogeneous_coeff_eq hset hp]
      exact mul_nonneg
        (div_nonneg (neg_pos.mpr (hset.c1.nu_neg (u, v) hp)).le (hset.radius_nonneg hp))
        (sq_nonneg _)
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
        (mul_nonneg (hset.c1.lam_pos (u, v) hp).le (hset.radius_nonneg hp))

/-- The forward homogeneous `k` factor is at most one on every controlled
outgoing subsegment. This numerical bound is independent of all parameters
and requires no smallness of the scalar variation. -/
theorem homogeneous_k_factor_le_one (hset : AprioriSetting e s ε M S h)
    {u a b : ℝ} (hu : 0 ≤ u) (hua : u ≤ a) (hab : a ≤ b) (hbs : b ≤ s) :
    Real.exp (∫ v in a..b, -‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  rw [intervalIntegral.integral_of_le hab]
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  have hv : v ∈ Icc a b := ⟨hv.1.le, hv.2⟩
  have hp : (u, v) ∈ triangle 0 s := ⟨hu, hua.trans hv.1, hv.2.trans hbs⟩
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
    (mul_nonneg (hset.c1.lam_pos (u, v) hp).le (hset.radius_nonneg hp))

end EmcsfAcExtension.Local.Area
