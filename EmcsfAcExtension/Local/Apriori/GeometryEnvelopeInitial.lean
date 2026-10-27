module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Apriori.Hardy
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Initial geometric derivative budget

The initial radius gauge fixes `λ = 1/2` and its outgoing derivative is
zero. The remaining quadratic correction is bounded using the initial
Hardy inequality, as in `charged_SF_new_version.tex:L4885–L4887`.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {e s ε M : ℝ} {S : Fields} {h : ℝ → ℂ}

/-- The initial radius gauge fixes the outgoing expansion to `1/2` on the
whole closed initial section. No smallness assumption is required. -/
theorem AprioriSetting.initial_lam (hset : AprioriSetting e s ε M S h)
    {v : ℝ} (hv : v ∈ Icc 0 s) : S.lam 0 v = 1 / 2 := by
  have hs : MapsTo (fun x => (0, x)) (Icc 0 s) (triangle 0 s) :=
    fun x hx => ⟨le_rfl, hx.1, hx.2⟩
  have hinner : EqOn (S.lam 0) (fun _ => 1 / 2) (Ioo 0 s) := by
    intro x hx
    have hd := hasDerivWithinAt_pdV hset.c1.c1_r (hs ⟨hx.1.le, hx.2.le⟩) hs
    rw [(hset.c1.eq_v (0, x) (hs ⟨hx.1.le, hx.2.le⟩) hx.1).1] at hd
    have hg : HasDerivWithinAt (S.r 0) (1 / 2) (Icc 0 s) x := by
      exact ((hasDerivAt_id x).div_const 2).hasDerivWithinAt.congr_of_mem
        (fun y hy => (hset.data.1 y hy).1) ⟨hx.1.le, hx.2.le⟩
    exact (hd.hasDerivAt (Icc_mem_nhds hx.1 hx.2)).unique
      (hg.hasDerivAt (Icc_mem_nhds hx.1 hx.2))
  have cl := hset.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hs
  exact hinner.of_subset_closure cl continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hset.pos.ne]) hv

/-- The outgoing within-domain derivative of the initial expansion vanishes,
including at both endpoints of the nondegenerate initial section. -/
theorem AprioriSetting.initial_lam_partial (hset : AprioriSetting e s ε M S h)
    {v : ℝ} (hv : v ∈ Icc 0 s) : pdV (triangle 0 s) S.lam 0 v = 0 := by
  have hs : MapsTo (fun x => (0, x)) (Icc 0 s) (triangle 0 s) :=
    fun x hx => ⟨le_rfl, hx.1, hx.2⟩
  have hd := hasDerivWithinAt_pdV hset.c1.c1_lam (hs hv) hs
  have hz : HasDerivWithinAt (S.lam 0) 0 (Icc 0 s) v :=
    (hasDerivAt_const v (1 / 2 : ℝ)).hasDerivWithinAt.congr_of_mem
      (fun x hx => hset.initial_lam hx) hv
  exact (hd.derivWithin (uniqueDiffOn_Icc hset.pos v hv)).symm.trans
    (hz.derivWithin (uniqueDiffOn_Icc hset.pos v hv))

/-- [node restart-sec-independent-area#initial-geometric-derivative-budget]
The initial geometric derivative has an `L¹` budget of quadratic size,
`charged_SF_new_version.tex:L4885–L4887`. `C` is universal: independent of `e,s,ε,M,S,h`
and all higher initial derivatives. Initial data variation suffices; no
envelope closure or smallness hypothesis is needed. -/
theorem initial_geometric_derivative_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      AprioriSetting e s ε M S h →
        (∀ v ∈ Icc 0 s, geomL (triangle 0 s) S 0 v =
          S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖ ^ 2) ∧
        (∫⁻ v in Icc 0 s, ‖geomL (triangle 0 s) S 0 v‖ₑ) ≤
          ENNReal.ofReal (C * ε ^ 2) := by
  refine ⟨4, by norm_num, ?_⟩
  intro e s ε M S h hset
  have heq (v : ℝ) (hv : v ∈ Icc 0 s) : geomL (triangle 0 s) S 0 v =
      S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖ ^ 2 := by
    simp only [geomL, hset.initial_lam_partial hv, zero_div, zero_add]
  refine ⟨heq, ?_⟩
  have hs : MapsTo (fun x => (0, x)) (Icc 0 s) (triangle 0 s) :=
    fun x hx => ⟨le_rfl, hx.1, hx.2⟩
  have hregular (v : ℝ) (hv : v ∈ Icc 0 s) : geomL (triangle 0 s) S 0 v =
      S.r 0 v / S.lam 0 v * ‖pdV (triangle 0 s) S.phi 0 v‖ ^ 2 := by
    rw [heq v hv, theta_eq_radius_partial_aux hset.pos hset.c1 (hs hv)]
    simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, div_pow, sq_abs]
    by_cases hr : S.r 0 v = 0
    · simp [hr]
    · have hl := (hset.c1.lam_pos (0, v) (hs hv)).ne'
      field_simp
  have cr : ContinuousOn (S.r 0) (Icc 0 s) := hset.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hs
  have cl : ContinuousOn (S.lam 0) (Icc 0 s) := hset.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hs
  have cp : ContinuousOn (pdV (triangle 0 s) S.phi 0) (Icc 0 s) :=
    (continuousOn_pdV hset.c1.c1_phi (uniqueDiffOn_triangle hset.pos)).comp
      (continuous_const.prodMk continuous_id).continuousOn hs
  have cL : ContinuousOn (geomL (triangle 0 s) S 0) (Icc 0 s) :=
    ((cr.div cl (fun x hx => (hset.c1.lam_pos (0, x) (hs hx)).ne')).mul
      (cp.norm.pow 2)).congr (fun v hv => hregular v hv)
  have hi := cL.intervalIntegrable_of_Icc (μ := volume) hset.pos.le
  have hh := bv_hardy_out_integrated hset.c1 le_rfl hset.pos.le le_rfl
  have hv : (eVariationOn (S.a 0) (Icc 0 s)).toReal ≤ ε := by
    rw [eVariationOn.congr (fun v hv => (hset.data.1 v hv).2)]
    exact hset.eps
  rw [← ofReal_integral_norm_eq_lintegral_enorm
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hset.pos.le).mp hi),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hset.pos.le]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ v in 0..s, (4 * ε) *
        (S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖) := by
      apply intervalIntegral.integral_mono_on hset.pos.le hi.norm (hh.1.const_mul _)
      intro v hv
      have hl := (hset.c1.lam_pos (0, v) (hs hv)).le
      have hr := hset.radius_nonneg (hs hv)
      rw [heq v hv, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc
        _ = (S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖) *
            ‖S.theta 0 v / S.lam 0 v‖ := by ring
        _ ≤ (S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖) * (4 * ε) := by
          gcongr
          exact (hset.box (0, v) (hs hv)).2.2.2.2.2.2.1
        _ = _ := by ring
    _ = (4 * ε) * ∫ v in 0..s,
        S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖ :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (4 * ε) * ε := mul_le_mul_of_nonneg_left (hh.2.trans hv)
      (mul_nonneg (by norm_num) hset.eps_nonneg)
    _ = _ := by ring

end EmcsfAcExtension.Local
