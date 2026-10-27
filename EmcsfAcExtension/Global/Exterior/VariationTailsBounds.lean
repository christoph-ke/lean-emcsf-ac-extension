module

public import EmcsfAcExtension.Global.Exterior.VariationTailsExit
public import EmcsfAcExtension.Global.Exterior.VariationTails
public import EmcsfAcExtension.Global.Exterior.VariationTransportExit

/-! # Moving-interval modulus and the variation comparison inequality

The canonical local capped exit discharges the geometric inverse-map
premises. The two-dimensional history estimate is then replaced by its
proved row majorant. This is internal project record (M3),
`charged_SF_new_version.tex:L1364–L1380`. Every coefficient is displayed.
-/

public section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal] The raw moving-interval formula with the exit map
constructed from the actual proper boundary. No inverse-map assumptions
remain. The forward and inverse Lipschitz constants are local to this
proper interval, fixed before both labels vary. -/
theorem moving_interval_modulus
    {ui e a b : ℝ} {S : Fields} {t : ℝ → ℝ} {K L : ℝ≥0}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (ht : LipschitzOnWith K t (uIcc a b)) (hm : MonotoneOn t (uIcc a b))
    (ha : AntilipschitzWith L ((uIcc a b).domRestrict t))
    (hmem : ∀ u ∈ Icc a b, (u, t u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < t u) :
    (eVariationOn (S.a b) (Icc (t b) 0)).toReal +
        (∫ u in a..b, deriv t u * ‖densityRepresentative e S a u (t u)‖) ≤
      (eVariationOn (S.a a) (Icc (t a) 0)).toReal +
        ∫ u in a..b, ∫ v in t u..0, densityModulusHistory e S a (u, v) := by
  have htc : ContinuousOn t (Icc a b) := by
    simpa only [uIcc_of_le hab] using ht.continuousOn
  have hmc : MonotoneOn t (Icc a b) := by simpa only [uIcc_of_le hab] using hm
  have hstrict : StrictMonoOn t (Icc a b) :=
    hmc.strictMonoOn_of_injOn (by
      intro u hu w hw heq
      have hu' : u ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hu
      have hw' : w ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hw
      exact congrArg Subtype.val (ha.injective (a₁ := ⟨u, hu'⟩) (a₂ := ⟨w, hw'⟩) heq))
  obtain ⟨τ, hc, hτm, hi, he, hmτ⟩ := exists_variation_swept_exit hab htc hstrict
  apply moving_interval_modulus_of_exit_map hS hab ht hm ha hmem hproper hc.measurable hmτ
  · simpa only [uIcc_of_le hab] using hi
  · exact fun u hu v hv => he u hu v hv.1

/-- [internal] The favorable exit cost is nonnegative. Monotonicity of
the boundary suffices; its density remains the prescribed representative. -/
theorem boundary_density_exit_nonneg
    {e a b : ℝ} {S : Fields} {t : ℝ → ℝ} (hab : a ≤ b)
    (hm : MonotoneOn t (Icc a b)) :
    0 ≤ ∫ u in a..b, deriv t u * ‖densityRepresentative e S a u (t u)‖ := by
  apply intervalIntegral.integral_nonneg_of_ae_restrict hab
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hd : 0 ≤ deriv t u := by
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)]
    exact hm.derivWithin_nonneg
  exact mul_nonneg hd (norm_nonneg _)

/-- [internal]
The moving-interval estimate after integrating the genuine history row
majorant. Both variation and the favorable exit term are retained. The
terminal consumer supplies `k=20744 nA` and `q=20480 nG`, so no estimate
for variation or the exit integral is a premise. -/
theorem moving_interval_modulus_inequality_of_history_bound
    {ui e a b : ℝ} {S : Fields} {t k q : ℝ → ℝ} {K L : ℝ≥0}
    (hS : IsSolution e S (origDomain ui)) (hab : a ≤ b)
    (ht : LipschitzOnWith K t (uIcc a b)) (hm : MonotoneOn t (uIcc a b))
    (ha : AntilipschitzWith L ((uIcc a b).domRestrict t))
    (hmem : ∀ u ∈ Icc a b, (u, t u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Icc a b, u < t u)
    (hk : IntervalIntegrable k volume a b) (hq : IntervalIntegrable q volume a b)
    (hrow : ∀ u ∈ Icc a b,
      (∫ v in t u..0, densityModulusHistory e S a (u, v)) ≤
        k u * (eVariationOn (S.a u) (Icc (t u) 0)).toReal + q u) :
    (eVariationOn (S.a b) (Icc (t b) 0)).toReal +
        (∫ u in a..b, deriv t u * ‖densityRepresentative e S a u (t u)‖) ≤
      (eVariationOn (S.a a) (Icc (t a) 0)).toReal +
        ∫ u in a..b, (k u * (eVariationOn (S.a u) (Icc (t u) 0)).toReal + q u) := by
  have htc : ContinuousOn t (Icc a b) := by
    simpa only [uIcc_of_le hab] using ht.continuousOn
  have hmc : MonotoneOn t (Icc a b) := by simpa only [uIcc_of_le hab] using hm
  have hcont := continuousOn_outgoing_variation hS hab htc hmc hmem hproper
  have hi := (hk.mul_continuousOn (by rwa [uIcc_of_le hab])).add hq
  have hmajor : (∫ u in a..b, ∫ v in t u..0, densityModulusHistory e S a (u, v)) ≤
      ∫ u in a..b, (k u * (eVariationOn (S.a u) (Icc (t u) 0)).toReal + q u) := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    apply integral_mono_of_nonneg
      ((ae_restrict_mem measurableSet_Ioc).mono fun u hu =>
        intervalIntegral.integral_nonneg (hmem u ⟨hu.1.le, hu.2⟩).2.2.2
          (fun v _ => densityModulusHistory_nonneg e S a (u, v))) hi.1
    exact (ae_restrict_mem measurableSet_Ioc).mono fun u hu => hrow u ⟨hu.1.le, hu.2⟩
  exact (moving_interval_modulus hS hab ht hm ha hmem hproper).trans
    (add_le_add le_rfl hmajor)

end EmcsfAcExtension.Global.Exterior
