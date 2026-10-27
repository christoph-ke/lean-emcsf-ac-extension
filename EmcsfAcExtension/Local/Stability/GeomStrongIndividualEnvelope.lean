module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongIndividualSource
import EmcsfAcExtension.Local.Stability.GeomStrongTransport
import EmcsfAcExtension.Local.Stability.GeomStrongRegularity
import EmcsfAcExtension.Local.Stability.GeomStrongBorel
import EmcsfAcExtension.Local.Stability.GeomStrongInitial
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassBudgets
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Calculus.Geometric
import EmcsfAcExtension.Local.Calculus.GeometricAxis
import EmcsfAcExtension.Infra.Triangle

/-! # Individual geometric envelope control in a stability setting

The stability setting supplies its own small mixed envelope. No
additional smooth-bound conclusion is assumed to convert logarithmic
geometric derivatives into expansion derivatives.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The individual geometric source has the same area norm in both
characteristic orders. This exact equality has no finiteness premise,
smallness condition or estimate constant. -/
theorem stab_geometric_source_area_orders_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖geomSource S u v‖ₑ) =
      (∫⁻ p in triangle 0 T, ‖geomSource S p.1 p.2‖ₑ) ∧
    (∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T, ‖geomSource S u v‖ₑ) =
      (∫⁻ p in triangle 0 T, ‖geomSource S p.1 p.2‖ₑ) := by
  let F := fun p : ℝ × ℝ => ‖(triangle 0 T).indicator (Function.uncurry (geomSource S)) p‖ₑ
  have mF : Measurable F := (stab_geomSource_borel_c1 hset).enorm
  have hF p (hp : p ∈ triangle 0 T) : F p = ‖geomSource S p.1 p.2‖ₑ := by
    dsimp only [F]
    rw [indicator_of_mem hp]
    rfl
  have harea : (∫⁻ p in triangle 0 T, F p) =
      ∫⁻ p in triangle 0 T, ‖geomSource S p.1 p.2‖ₑ :=
    setLIntegral_congr_fun (measurableSet_triangle 0 T) hF
  constructor
  · have heq := lintegral_triangle_eq_lintegral_lintegral_symm (a := 0) (b := T) mF
    rw [← Measure.volume_eq_prod, harea] at heq
    apply Eq.trans ?_ heq.symm
    apply setLIntegral_congr_fun measurableSet_Icc
    intro v hv
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    exact (hF (u, v) ⟨hu.1, hu.2, hv.2⟩).symm
  · have heq := lintegral_triangle_eq_lintegral_lintegral (a := 0) (b := T) mF
    rw [← Measure.volume_eq_prod, harea] at heq
    apply Eq.trans ?_ heq.symm
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    apply setLIntegral_congr_fun measurableSet_Icc
    intro v hv
    exact (hF (u, v) ⟨hu.1, hv.1, hv.2⟩).symm

private theorem individual_transport_aux
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    (∫⁻ v in Icc 0 T, outEnv 0 (geomL (triangle 0 T) S) v) +
      (∫⁻ u in Icc 0 T, inEnv T (geomN (triangle 0 T) S) u) ≤
      2 * (∫⁻ v in Icc 0 T, ‖geomL (triangle 0 T) S 0 v‖ₑ) +
        3 * (∫⁻ p in triangle 0 T, ‖geomSource S p.1 p.2‖ₑ) := by
  have ht := stab_geometric_envelopes_of_transport_c1 hset.pos.le
    (stab_geomL_continuous_c1 hset) (stab_geomN_continuous_c1 hset)
    (H := geomSource S)
    (fun v hv => (stab_geomSource_aemeasurable_on_c1 hset
      (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu.1, hu.2, hv.2⟩)).aestronglyMeasurable)
    (fun u hu => (stab_geomSource_aemeasurable_on_c1 hset
      (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨hu.1, hv.1, hv.2⟩)).aestronglyMeasurable)
    (fun v hv u hu => (bv_geom_trans_out hset.c1 hu.1.le hu.2 hv.2).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2))
    (fun u hu v hv => (bv_geom_trans_in hset.c1 hu.1 hv.1 hv.2.le).hasDerivAt
      (Icc_mem_nhds hv.1 hv.2))
    (fun t ht => (Area.smooth_geometric_axis_match hset.pos hset.c1 ht).1.symm)
  obtain ⟨hi, ho⟩ := stab_geometric_source_area_orders_c1 hset
  rw [hi, ho] at ht
  exact ht.trans_eq (by ring)

/-- The initial geometric envelope has quadratic budget `256 A ε²`
from the stability setting alone. The coefficient is universal, before
all fields and data, without an extra initial-variation assumption. -/
theorem stab_initial_geometric_budget_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) (hε : ε ^ 2 ≤ 1 / 4) :
    (∫⁻ v in Icc 0 T, ‖geomL (triangle 0 T) S 0 v‖ₑ) ≤ ENNReal.ofReal (256 * A * ε ^ 2) := by
  have heq : (∫⁻ v in Icc 0 T, ‖geomL (triangle 0 T) S 0 v‖ₑ) =
      ∫⁻ v in Icc 0 T, ENNReal.ofReal
        (S.lam 0 v / S.r 0 v * ‖S.theta 0 v / (S.lam 0 v : ℂ)‖ ^ 2) := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro v hv
    have hr : 0 ≤ S.r 0 v := by
      have hh := (stab_radius_bounds hset le_rfl hv.1 hv.2).1
      linarith only [hh, hv.1]
    change ‖geomL (triangle 0 T) S 0 v‖ₑ =
      ENNReal.ofReal (S.lam 0 v / S.r 0 v * ‖S.theta 0 v / (S.lam 0 v : ℂ)‖ ^ 2)
    rw [stab_initial_geomL hset hv, ← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (div_nonneg (hset.c1.lam_pos (0, v) ⟨le_rfl, hv.1, hv.2⟩).le hr)
        (sq_nonneg _))]
  rw [heq]
  exact stab_out_mixed_quadratic_le hset hset hε le_rfl hset.pos.le

/-- Individual geometric envelopes have quadratic budget with displayed
constant `512 A+3(4096 A²+800)`. Only the envelope constant and fixed box
enter; the estimate is uniform in all fields, data, coupling, scale,
background, derivative suprema and minimum radii. -/
theorem stab_geometric_envelope_budget_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) (hA : 0 ≤ A)
    (hε : ε ^ 2 ≤ 1 / 4) (hσ : sigma e M T ≤ 1) :
    (∫⁻ v in Icc 0 T, outEnv 0 (geomL (triangle 0 T) S) v) +
      (∫⁻ u in Icc 0 T, inEnv T (geomN (triangle 0 T) S) u) ≤
        ENNReal.ofReal ((512 * A + 3 * (4096 * A ^ 2 + 800)) * ε ^ 2) := by
  apply (individual_transport_aux hset).trans
  apply (add_le_add (mul_le_mul' le_rfl (stab_initial_geometric_budget_c1 hset hε))
    (mul_le_mul' le_rfl (stab_geometric_source_area_le_c1 hset hA hε hσ))).trans_eq
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_ofNat 3,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end EmcsfAcExtension.Local
