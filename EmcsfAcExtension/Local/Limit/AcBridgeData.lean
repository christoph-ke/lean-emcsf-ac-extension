module

public import EmcsfAcExtension.Local.Defs.Params
public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Local.Broad.ScalarAverage
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Api.EqOn
import EmcsfAcExtension.Infra.HardyBV

/-! # The AC datum Hardy estimate for broad identification

internal project record item 7 starts with the initial normalized AC datum, without
presupposing characteristic AC of b or of any geometric derivative.
The fixed initial radius identifies lambda and the radial scalar average.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem initial_lam {e T : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hT : 0 < T) (hS : IsSolution e S (triangle 0 T)) (hd : IsRestartData S h T) :
    ∀ v ∈ Icc 0 T, S.lam 0 v = 1 / 2 := by
  have hc : ContinuousOn (S.lam 0) (Icc 0 T) :=
    hS.cont_lam.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  have he : EqOn (S.lam 0) (fun _ => (1 : ℝ) / 2) (Ioo 0 T) := by
    intro v hv
    have hseg : outSeg 0 0 T ⊆ triangle 0 T := by
      rintro ⟨x, y⟩ ⟨rfl, hy⟩
      exact ⟨le_rfl, hy⟩
    have hr := IsSolution.hasDerivAt_radius_out hS hseg hv
    have hEq : S.r 0 =ᶠ[𝓝 v] (fun x : ℝ => x / 2) :=
      Filter.eventuallyEq_of_mem (Icc_mem_nhds hv.1 hv.2) (fun x hx => (hd.1 x hx).1)
    exact hr.deriv.symm.trans (hEq.deriv_eq.trans (by simp))
  exact he.of_subset_closure hc continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hT.ne])

private theorem initial_average {e T v : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hT : 0 < T) (hS : IsSolution e S (triangle 0 T)) (hd : IsRestartData S h T)
    (hv : v ∈ Ioc 0 T) : radialAverage (fun _ => 1 / 2) h 0 v = S.phi 0 v := by
  have hseg : outSeg 0 0 v ⊆ triangle 0 T := by
    rintro ⟨x, y⟩ ⟨rfl, hy⟩
    exact ⟨le_rfl, hy.1, hy.2.trans hv.2⟩
  have hprim := Broad.outgoing_scalar_reconstruction hS hv.1.le hseg
  have hi : (∫ x in (0 : ℝ)..v, (S.lam 0 x : ℂ) * S.a 0 x) =
      ∫ x in (0 : ℝ)..v, (1 / 2 : ℂ) * h x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hv.1.le] at hx
    dsimp only
    rw [initial_lam hT hS hd x ⟨hx.1, hx.2.trans hv.2⟩, (hd.1 x ⟨hx.1, hx.2.trans hv.2⟩).2]
    norm_num
  rw [(hd.1 v ⟨hv.1.le, hv.2⟩).1, hi] at hprim
  have hweight : (∫ x in (0 : ℝ)..v, (1 / 2 : ℝ)) = v / 2 := by simp [div_eq_mul_inv]
  unfold radialAverage
  rw [hweight]
  have hnum : (∫ x in (0 : ℝ)..v, (1 / 2 : ℝ) • h x) =
      ∫ x in (0 : ℝ)..v, (1 / 2 : ℂ) * h x := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [hnum, ← hprim, Complex.real_smul]
  have hvn : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.1.ne'
  push_cast
  field_simp [hvn]

/-- The sharp initial outgoing Hardy estimate for any broad AC integral
solution with normalized AC data. The coefficient is exactly one, uniformly
in coupling, time, datum size and every derivative supremum. Incoming AC of
the normalized scalar and geometric characteristic AC are not premises. -/
theorem initial_hardy_of_ac_data {e T : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hT : 0 < T) (hS : IsSolution e S (triangle 0 T))
    (hd : IsRestartData S h T) (hac : AbsolutelyContinuousOnInterval h 0 T) :
    IntervalIntegrable (fun v => S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖) volume 0 T ∧
      (∫ v in (0 : ℝ)..T, S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖) ≤ datumVar h T := by
  have hw : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 2) volume 0 T := intervalIntegrable_const
  have hc : ContinuousOn h (Icc 0 T) := by
    simpa only [uIcc_of_le hT.le] using hac.continuousOn
  obtain ⟨hi, hb⟩ := integrable_and_integral_weighted_deviation_le_variation hT.le hw
    (fun _ _ => by norm_num) hc (hac.boundedVariationOn_Icc hT.le)
  have heq : (fun v => S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖) =ᵐ[
      volume.restrict (uIoc 0 T)]
      (fun v => (1 / 2 : ℝ) / (∫ x in (0 : ℝ)..v, (1 / 2 : ℝ)) *
        ‖h v - radialAverage (fun _ => 1 / 2) h 0 v‖) := by
    rw [uIoc_of_le hT.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    have hfield := (hd.1 v ⟨hv.1.le, hv.2⟩).2
    have hx : S.theta 0 v / S.lam 0 v = h v - S.phi 0 v := by
      rw [← hfield, Fields.a]
      abel
    rw [initial_lam hT hS hd v ⟨hv.1.le, hv.2⟩, (hd.1 v ⟨hv.1.le, hv.2⟩).1]
    rw [initial_lam hT hS hd v ⟨hv.1.le, hv.2⟩] at hx
    rw [hx, initial_average hT hS hd hv]
    simp [div_eq_mul_inv]
  exact ⟨hi.congr_ae heq.symm, (intervalIntegral.integral_congr_ae_restrict heq).le.trans hb⟩

end EmcsfAcExtension.Local
