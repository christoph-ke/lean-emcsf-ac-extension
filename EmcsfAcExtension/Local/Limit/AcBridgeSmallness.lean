module

public import EmcsfAcExtension.Local.Limit.AcBridgeData
public import EmcsfAcExtension.Local.Defs.Box
public import EmcsfAcExtension.Frozen.JOut
import EmcsfAcExtension.Infra.AC.Variation

/-! # Recovering datum smallness from a general AC envelope

The initial Hardy coefficient is one. The frozen j identity therefore
absorbs the cubic term without any incoming AC premise (internal project record item 7.2).
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Recover the initial datum variation from an integrable outgoing
renormalized envelope in a general AC box. The coefficient `2 / c` depends
only on the fixed positive gap `c`; all time, coupling, size and derivative
suprema remain free. This is an initial-cone helper, not a sequence node. -/
theorem datumVar_le_of_initial_envelope {e T c Cb η M H : ℝ}
    {S : Fields} {h : ℝ → ℂ} {J : ℝ → ℝ}
    (hT : 0 < T) (hc : 0 < c) (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 2)
    (hS : IsSolution e S (triangle 0 T)) (hd : IsRestartData S h T)
    (hac : AbsolutelyContinuousOnInterval h 0 T)
    (hbox : StabBox S c Cb η M (triangle 0 T))
    (hJ : IntervalIntegrable J volume 0 T)
    (hdom : ∀ᵐ v ∂volume.restrict (Icc 0 T), ‖jOut S 0 v‖ ≤ J v)
    (hmass : (∫ v in (0 : ℝ)..T, J v) ≤ H * η) :
    datumVar h T ≤ 2 * H / c * η := by
  let F v := S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖
  obtain ⟨hF, hFb⟩ := initial_hardy_of_ac_data hT hS hd hac
  have hderiv := hac.intervalIntegrable_deriv_finiteDimensional.norm
  have hpoint : ∀ᵐ v ∂volume.restrict (Icc 0 T),
      ‖deriv h v‖ ≤ J v / c + η ^ 2 * F v := by
    have hz : ∀ᵐ v : ℝ, v ≠ 0 := by simp [ae_iff, measure_singleton]
    have ht : ∀ᵐ v : ℝ, v ≠ T := by simp [ae_iff, measure_singleton]
    filter_upwards [hdom, ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae hz, ae_restrict_of_ae ht] with v hj hmem hv0 hvT'
    have hv : v ∈ Ioc 0 T := ⟨lt_of_le_of_ne hmem.1 hv0.symm, hmem.2⟩
    have hvT : v < T := lt_of_le_of_ne hmem.2 hvT'
    have hp : (0, v) ∈ triangle 0 T := ⟨le_rfl, hv.1.le, hv.2⟩
    obtain ⟨hl, _, _, _, hg, hx, _⟩ := hbox.2 (0, v) hp
    have hgpos : 0 < 1 - S.mu 0 v := hc.trans_le hg
    have hq : 0 ≤ S.lam 0 v / S.r 0 v := div_nonneg
      (hc.le.trans hl) (hS.r_pos (0, v) hp hv.1).le
    have hEq : S.a 0 =ᶠ[𝓝 v] h := eventuallyEq_of_mem
      (Icc_mem_nhds hv.1 hvT) (fun x hx => (hd.1 x hx).2)
    let z : ℂ := S.lam 0 v / S.r 0 v * ‖S.theta 0 v / S.lam 0 v‖ ^ 2 *
      (S.theta 0 v / S.lam 0 v)
    have hjnorm : ‖jOut S 0 v‖ = (1 - S.mu 0 v) * ‖deriv h v - z‖ := by
      simp only [jOut, hEq.deriv_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub]
      change ‖((1 - S.mu 0 v : ℝ) : ℂ) * (deriv h v - z)‖ = _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgpos]
    have hsub : ‖deriv h v - z‖ ≤ J v / c := by
      apply (le_div_iff₀ hc).2
      calc
        _ ≤ ‖deriv h v - z‖ * (1 - S.mu 0 v) :=
          mul_le_mul_of_nonneg_left hg (norm_nonneg _)
        _ = ‖jOut S 0 v‖ := by rw [hjnorm, mul_comm]
        _ ≤ J v := hj
    have hz : ‖z‖ ≤ η ^ 2 * F v := by
      have hx' : ‖S.theta 0 v / S.lam 0 v‖ ≤ η :=
        (le_add_of_nonneg_right (norm_nonneg _)).trans hx
      have hsq : ‖S.theta 0 v / S.lam 0 v‖ ^ 2 ≤ η ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hx' 2
      have hnz : ‖z‖ = S.lam 0 v / S.r 0 v *
          ‖S.theta 0 v / S.lam 0 v‖ ^ 2 * ‖S.theta 0 v / S.lam 0 v‖ := by
        simp only [z, ← Complex.ofReal_div, ← Complex.ofReal_pow, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq,
          abs_of_nonneg (sq_nonneg ‖S.theta 0 v / S.lam 0 v‖)]
      rw [hnz]
      dsimp only [F]
      convert mul_le_mul_of_nonneg_right hsq
        (mul_nonneg hq (norm_nonneg (S.theta 0 v / S.lam 0 v))) using 1; ring
    exact (norm_le_norm_sub_add (deriv h v) z).trans (add_le_add hsub hz)
  have hi := intervalIntegral.integral_mono_ae_restrict hT.le hderiv
    ((hJ.div_const c).add (hF.const_mul (η ^ 2))) hpoint
  rw [intervalIntegral.integral_add (hJ.div_const c) (hF.const_mul (η ^ 2)),
    intervalIntegral.integral_div, intervalIntegral.integral_const_mul] at hi
  have hv : datumVar h T = ∫ v in (0 : ℝ)..T, ‖deriv h v‖ :=
    hac.toReal_eVariationOn_eq_integral_norm_deriv hT.le
  rw [← hv] at hi
  have hb : datumVar h T ≤ H * η / c + η ^ 2 * datumVar h T :=
    hi.trans (add_le_add (div_le_div_of_nonneg_right hmass hc.le)
      (mul_le_mul_of_nonneg_left hFb (sq_nonneg η)))
  have hδ : 0 ≤ datumVar h T := ENNReal.toReal_nonneg
  have hη2 : η ^ 2 ≤ 1 / 2 := by nlinarith
  have ha := mul_le_mul_of_nonneg_right hη2 hδ
  have hr : datumVar h T ≤ 2 * (H * η / c) := by linarith
  convert hr using 1; ring

end EmcsfAcExtension.Local
