module

public import EmcsfAcExtension.Local.Limit.Construct2Settings
import EmcsfAcExtension.Infra.W11.Completeness
import EmcsfAcExtension.Local.Limit.Construct2Cauchy
import EmcsfAcExtension.Local.Limit.ScalarAxisDerivative

/-! # The constructed common AC diagonal trace

internal project record P3: construct the axis trace directly by W¹¹ completeness.
Its incoming mixed Cauchy control comes from the pending smooth comparison,
and the common vertex value fixes the primitive constant. No `StrongLimit`
is assumed or asserted in this diagonal construction.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Construct a common AC axis trace from classical approximants, their
zero axis gauge, common vertex and incoming mixed Cauchy control.
The coefficient in the diagonal-to-envelope estimate is one, uniformly
in the sequence. This analytic helper selects no numerical constant. -/
theorem Null.axis_trace_of_mixed_cauchy {e T : ℝ} {Sn : ℕ → Fields} {z : ℂ}
    (hT : 0 < T) (hS : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hA : ∀ n t, t ∈ Icc 0 T → (Sn n).A t t = 0)
    (hv : ∀ n, (Sn n).phi 0 0 = z)
    (hC : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      kDist e T (Sn n) (Sn m) < ENNReal.ofReal ρ) :
    ∃ psi : ℝ → ℂ, AbsolutelyContinuousOnInterval psi 0 T ∧ psi 0 = z ∧
      TendstoUniformlyOn (fun n t => (Sn n).phi t t) psi atTop (Icc 0 T) ∧
      TendstoUniformlyOn (fun n t => (Sn n).a t t) psi atTop (Icc 0 T) ∧
      TendstoUniformlyOn (fun n t => (Sn n).b t t) psi atTop (Icc 0 T) ∧
      ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
        (∫ t in (0 : ℝ)..T, ‖kC1 e (triangle 0 T) (Sn n) t t - deriv psi t‖) < ρ := by
  let F n t := (Sn n).phi t t
  have hAC n : AbsolutelyContinuousOnInterval (F n) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hT.le]
    exact (hS n).c1_phi.comp (contDiff_id.prodMk contDiff_id).contDiffOn
      (fun t ht => ⟨ht.1, le_rfl, ht.2⟩)
  have hdiag n : deriv (F n) =ᵐ[volume.restrict (Icc 0 T)]
      (fun t => kC1 e (triangle 0 T) (Sn n) t t) := by
    have ha : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
    have hb : ∀ᵐ t : ℝ, t ≠ T := by simp [ae_iff, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae ha,
      ae_restrict_of_ae hb] with t ht hta htb
    exact ((hS n).axis_hasDerivWithinAt hT (hA n) ht).hasDerivAt
      (Icc_mem_nhds (lt_of_le_of_ne ht.1 hta.symm) (lt_of_le_of_ne ht.2 htb)) |>.deriv
  have hderiv : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫ t in (0 : ℝ)..T, ‖deriv (F n) t - deriv (F m) t‖) < ρ := by
    intro ρ hρ
    obtain ⟨N, hN⟩ := hC ρ hρ
    refine ⟨N, fun n hn m hm => (ENNReal.ofReal_lt_ofReal_iff hρ).1 ?_⟩
    apply lt_of_le_of_lt ?_ (hN n hn m hm)
    have hi : IntegrableOn (fun t => deriv (F n) t - deriv (F m) t) (Icc 0 T) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).1
        ((hAC n).intervalIntegrable_deriv_complex.sub (hAC m).intervalIntegrable_deriv_complex)
    rw [intervalIntegral.integral_of_le hT.le, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_norm_eq_lintegral_enorm hi]
    apply lintegral_mono_ae
    filter_upwards [hdiag n, hdiag m, ae_restrict_mem measurableSet_Icc] with t hn hm ht
    rw [hn, hm]
    exact le_iSup₂_of_le t ⟨le_rfl, ht.2⟩ le_rfl
  obtain ⟨psi, hac, hdist, hunif, hvar⟩ := W11.exists_ac_limit_of_cauchy hT.le hAC (by
    intro ρ hρ
    obtain ⟨N, hN⟩ := hderiv ρ hρ
    refine ⟨N, fun n hn m hm => ?_⟩
    change ‖F n 0 - F m 0‖ + (eVariationOn (F n - F m) (Icc 0 T)).toReal < ρ
    rw [W11.variation_sub_eq_integral hT.le (hAC n) (hAC m)]
    simpa only [F, hv, sub_self, norm_zero, zero_add] using hN n hn m hm)
  have hz : psi 0 = z := tendsto_nhds_unique (hunif.tendsto_at ⟨le_rfl, hT.le⟩)
    (by simpa only [F, hv] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z)))
  refine ⟨psi, hac, hz, hunif, ?_, ?_, ?_⟩
  · exact hunif.congr (Eventually.of_forall fun n t ht =>
      ((hS n).axis t ⟨ht.1, le_rfl, ht.2⟩).2.2.2.2.1.symm)
  · exact hunif.congr (Eventually.of_forall fun n t ht =>
      ((hS n).axis t ⟨ht.1, le_rfl, ht.2⟩).2.2.2.2.2.symm)
  · intro ρ hρ
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hvar).2 ρ hρ)
    refine ⟨N, fun n hn => ?_⟩
    have he : (∫ t in (0 : ℝ)..T, ‖kC1 e (triangle 0 T) (Sn n) t t - deriv psi t‖) =
        (eVariationOn (F n - psi) (Icc 0 T)).toReal := by
      rw [W11.variation_sub_eq_integral hT.le (hAC n) hac]
      apply intervalIntegral.integral_congr_ae
      have hh := (ae_restrict_iff' measurableSet_Icc).1 (hdiag n)
      filter_upwards [hh] with t ht ht'
      rw [uIoc_of_le hT.le] at ht'
      rw [ht ⟨ht'.1.le, ht'.2⟩]
    rw [he]
    exact hN n hn

end EmcsfAcExtension.Local
