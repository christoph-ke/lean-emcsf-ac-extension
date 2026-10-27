module

public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Local.Defs.Envelope
import EmcsfAcExtension.Local.Limit.Scalar
import EmcsfAcExtension.Local.Limit.ScalarAxisDerivative
import EmcsfAcExtension.Local.Calculus.AxisLimits

/-! # Strong AC convergence of the axis scalar

`charged_SF_new_version.tex:L6453–6459`. The diagonal derivative is the continuous
incoming density at the axis. Its L¹ differences are bounded by the incoming
mixed-envelope differences, so completeness identifies the AC diagonal limit.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- The uniform primary-field limit retains the common normalized scalar value
at every axis point, even without a positive lower bound on the limit expansions. -/
theorem StrongLimit.axis_scalar_matching_of_c1 {e T : ℝ} {Sn : ℕ → Fields} {S : Fields}
    (hlim : StrongLimit e T Sn S) (hS : ∀ n, IsC1Solution e (Sn n) (triangle 0 T)) :
    ∀ t ∈ Icc 0 T, S.a t t = S.phi t t ∧ S.b t t = S.phi t t := by
  intro t ht
  have hp : (t, t) ∈ triangle 0 T := ⟨ht.1, le_rfl, ht.2⟩
  have hθ : S.theta t t = 0 := tendsto_nhds_unique (hlim.unif_theta.tendsto_at hp)
    (by simpa only [Function.uncurry_apply_pair, fun n => (hS n).theta_axis ht] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))
  have hz n : (Sn n).xi t t = 0 := by
    have heq := (hS n).axis t hp |>.2.2.2.2.2
    have hn : ((Sn n).nu t t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr ((hS n).nu_neg _ hp).ne
    simpa only [Fields.b, add_eq_left, div_eq_zero_iff, or_iff_left hn] using heq
  have hξ : S.xi t t = 0 := tendsto_nhds_unique (hlim.unif_xi.tendsto_at hp)
    (by simpa only [Function.uncurry_apply_pair, hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))
  simp [Fields.a, Fields.b, hθ, hξ]

/-- [internal]
The fixed-label strong limit has an AC diagonal scalar trace. Its derivatives
are the strong L¹ limits of the incoming classical diagonal densities.
The only Cauchy input is the incoming part of `#strong-same-label-cauchy`;
there is no bound on a classical derivative supremum and no selected constant. -/
theorem Null.axis_strong_ac_limit_of_strongLimit_of_cauchy {e T : ℝ}
    {Sn : ℕ → Fields} {S : Fields} (hT : 0 < T)
    (hS : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hA : ∀ n t, t ∈ Icc 0 T → (Sn n).A t t = 0)
    (hlim : StrongLimit e T Sn S)
    (hC : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      kDist e T (Sn n) (Sn m) < ENNReal.ofReal ε) :
    AbsolutelyContinuousOnInterval (fun t => S.phi t t) 0 T ∧
      (∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
        (∫ t in (0 : ℝ)..T,
          ‖kC1 e (triangle 0 T) (Sn n) t t - deriv (fun s => S.phi s s) t‖) < ε) ∧
      ∀ t ∈ Icc 0 T, S.a t t = S.phi t t ∧ S.b t t = S.phi t t := by
  let ψ n t := (Sn n).phi t t
  have hAC n : AbsolutelyContinuousOnInterval (ψ n) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hT.le]
    exact (hS n).c1_phi.comp (contDiff_id.prodMk contDiff_id).contDiffOn
      (fun t ht => (show (t, t) ∈ triangle 0 T from ⟨ht.1, le_rfl, ht.2⟩))
  have hdiag n : deriv (ψ n) =ᵐ[volume.restrict (Icc 0 T)]
      (fun t => kC1 e (triangle 0 T) (Sn n) t t) := by
    have ha : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
    have hb : ∀ᵐ t : ℝ, t ≠ T := by simp [ae_iff, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae ha,
      ae_restrict_of_ae hb] with t ht hta htb
    exact ((hS n).axis_hasDerivWithinAt hT (hA n) ht).hasDerivAt
      (Icc_mem_nhds (lt_of_le_of_ne ht.1 hta.symm) (lt_of_le_of_ne ht.2 htb)) |>.deriv
  have hderiv : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      (∫ t in (0 : ℝ)..T, ‖deriv (ψ n) t - deriv (ψ m) t‖) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn m hm => (ENNReal.ofReal_lt_ofReal_iff hε).mp ?_⟩
    apply lt_of_le_of_lt ?_ (hN n hn m hm)
    have hi := ((hAC n).intervalIntegrable_deriv_complex.sub
      (hAC m).intervalIntegrable_deriv_complex)
    have hii : IntegrableOn (fun t => deriv (ψ n) t - deriv (ψ m) t) (Icc 0 T) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mp hi
    rw [intervalIntegral.integral_of_le hT.le, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_norm_eq_lintegral_enorm hii]
    apply lintegral_mono_ae
    filter_upwards [hdiag n, hdiag m, ae_restrict_mem measurableSet_Icc] with t hn hm ht
    rw [hn, hm]
    exact le_iSup₂_of_le t ⟨le_rfl, ht.2⟩ le_rfl
  have hψlim : TendstoUniformlyOn ψ (fun t => S.phi t t) atTop (Icc 0 T) := by
    apply (hlim.unif_phi.comp (fun t : ℝ => (t, t))).mono
    intro t ht
    exact ⟨ht.1, le_rfl, ht.2⟩
  obtain ⟨hac, hstrong, _⟩ := ac_family_limit_of_derivative_cauchy
    (s := fun _ : Unit => (0 : ℝ)) (t := fun _ : Unit => T)
    (F := fun n _ t => ψ n t) (f := fun _ t => S.phi t t)
    (fun _ => hT.le) (fun n _ => hAC n)
    (by simpa only [Function.comp_def, Set.preimage] using
      hψlim.comp (Prod.snd : Unit × ℝ → ℝ))
    (by
      intro ε hε
      obtain ⟨N, hN⟩ := hderiv ε hε
      exact ⟨N, fun n hn m hm _ => hN n hn m hm⟩)
  refine ⟨hac (), (fun ε hε => ?_), hlim.axis_scalar_matching_of_c1 hS⟩
  obtain ⟨N, hN⟩ := hstrong ε hε
  refine ⟨N, fun n hn => ?_⟩
  have he : (∫ t in (0 : ℝ)..T,
      ‖kC1 e (triangle 0 T) (Sn n) t t - deriv (fun s => S.phi s s) t‖) =
      ∫ t in (0 : ℝ)..T, ‖deriv (ψ n) t - deriv (fun s => S.phi s s) t‖ := by
    apply intervalIntegral.integral_congr_ae
    have hh := (ae_restrict_iff' measurableSet_Icc).mp (hdiag n)
    filter_upwards [hh] with t ht ht'
    rw [uIoc_of_le hT.le] at ht'
    rw [ht ⟨ht'.1.le, ht'.2⟩]
  rw [he]
  exact hN n hn ()

end EmcsfAcExtension.Local
