module

public import EmcsfAcExtension.Infra.Mixed.SectionIntegral
public import EmcsfAcExtension.Frozen.Triangle
public import EmcsfAcExtension.Frozen.IntegralForm
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Uniform strong section integrals and density identification

Continuous uniform limits give uniform characteristic L¹ limits, with the
explicit section-length factor `T`. Density identities are sectionwise a.e.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace EmcsfAcExtension.Local

/-- Uniform convergence of continuous densities gives strong L¹ convergence
uniformly over both full families of triangle sections. The integration
coefficient is exactly the section length, at most `T`. -/
theorem section_integrals_tendsto_of_uniform {E : Type*} [NormedAddCommGroup E]
    {T : ℝ} {Fn : ℕ → ℝ → ℝ → E} {f : ℝ → ℝ → E} (hT : 0 < T)
    (hFn : ∀ n, ContinuousOn (Function.uncurry (Fn n)) (triangle 0 T))
    (hf : ContinuousOn (Function.uncurry f) (triangle 0 T))
    (hl : TendstoUniformlyOn (fun n => Function.uncurry (Fn n)) (Function.uncurry f) atTop (triangle
        0 T)) :
    (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ Icc 0 T,
      (∫ v in u..T, ‖Fn n u v - f u v‖) < ρ) ∧
    (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
      (∫ u in (0 : ℝ)..v, ‖Fn n u v - f u v‖) < ρ) := by
  have hsmall ρ (hρ : 0 < ρ) : ∃ N : ℕ, ∀ n ≥ N, ∀ p ∈ triangle 0 T,
      ‖Fn n p.1 p.2 - f p.1 p.2‖ ≤ ρ / (2 * T) := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((Metric.tendstoUniformlyOn_iff.1 hl)
      (ρ / (2 * T)) (by positivity))
    refine ⟨N, fun n hn p hp => ?_⟩
    have hh : ‖Fn n p.1 p.2 - f p.1 p.2‖ < ρ / (2 * T) := by
      simpa only [Function.uncurry_def, dist_comm, dist_eq_norm] using hN n hn p hp
    exact hh.le
  constructor
  · intro ρ hρ
    obtain ⟨N, hN⟩ := hsmall ρ hρ
    refine ⟨N, fun n hn u hu => ?_⟩
    have hm : MapsTo (fun v => (u,v)) (Icc u T) (triangle 0 T) :=
      fun v hv => ⟨hu.1, hv.1, hv.2⟩
    have hi : IntervalIntegrable (fun v => Fn n u v - f u v) volume u T :=
      (((hFn n).sub hf).comp (continuous_const.prodMk continuous_id).continuousOn
          hm).intervalIntegrable_of_Icc hu.2
    have hh := Mixed.integral_norm_section_le hu.1 hu.2 le_rfl (by positivity : 0 ≤ ρ / (2*T)) hi
      (fun v hv => hN n hn (u,v) (hm hv))
    have he : T * (ρ / (2*T)) = ρ / 2 := by field_simp
    rw [he] at hh
    linarith
  · intro ρ hρ
    obtain ⟨N, hN⟩ := hsmall ρ hρ
    refine ⟨N, fun n hn v hv => ?_⟩
    have hm : MapsTo (fun u => (u,v)) (Icc 0 v) (triangle 0 T) :=
      fun u hu => ⟨hu.1, hu.2, hv.2⟩
    have hi : IntervalIntegrable (fun u => Fn n u v - f u v) volume 0 v :=
      (((hFn n).sub hf).comp (continuous_id.prodMk continuous_const).continuousOn
          hm).intervalIntegrable_of_Icc hv.1
    have hh := Mixed.integral_norm_section_le le_rfl hv.1 hv.2 (by positivity : 0 ≤ ρ / (2*T)) hi
      (fun u hu => hN n hn (u,v) (hm hu))
    have he : T * (ρ / (2*T)) = ρ / 2 := by field_simp
    rw [he] at hh
    linarith

/-- Interior continuous integral equations identify the ordinary derivative
a.e. on the whole closed interval, including degenerate intervals. There is
no assertion of endpoint differentiability and no estimate constant. -/
theorem deriv_ae_of_interior_integralForm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f q : ℝ → E} {a b : ℝ}
    (hq : ContinuousOn q (Icc a b))
    (heq : ∀ c d, a < c → c ≤ d → d < b → IntegralForm f q c d) :
    deriv f =ᵐ[volume.restrict (Icc a b)] q := by
  have hne (x : ℝ) : ∀ᵐ y : ℝ, y ≠ x := by simp [ae_iff]
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (hne a),
    ae_restrict_of_ae (hne b)] with x hx hxa hxb
  have hxi : x ∈ Ioo a b := ⟨lt_of_le_of_ne hx.1 hxa.symm, lt_of_le_of_ne hx.2 hxb⟩
  exact (hasDerivAt_of_integralForm_interior hxi (hq.mono Ioo_subset_Icc_self) heq).deriv

end EmcsfAcExtension.Local
