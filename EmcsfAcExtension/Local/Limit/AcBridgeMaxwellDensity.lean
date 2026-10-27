module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Local.Limit.AcBridgeIntegrals
import EmcsfAcExtension.Infra.Mixed.SectionIntegral
import EmcsfAcExtension.Infra.Triangle
import EmcsfAcExtension.Infra.Null.IntegralForm

/-! # Strong Maxwell densities of general AC solution sequences

The Maxwell currents are continuous polynomials of primary fields, including
on the regular axis. Integral equations identify their ordinary derivatives.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem continuous_QV {e T : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle 0 T)) :
    ContinuousOn (Function.uncurry (S.QV e)) (triangle 0 T) := by
  simpa only [Fields.QV, Function.uncurry_def] using!
    (((continuousOn_const (c := e)).mul hS.cont_r).mul
      (Complex.continuous_im.comp_continuousOn
        ((continuous_star.comp_continuousOn hS.cont_phi).mul hS.cont_theta))).neg

private theorem continuous_QU {e T : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle 0 T)) :
    ContinuousOn (Function.uncurry (S.QU e)) (triangle 0 T) := by
  simpa only [Fields.QU, Function.uncurry_def] using!
    ((continuousOn_const (c := e)).mul hS.cont_r).mul
      (Complex.continuous_im.comp_continuousOn
        ((continuous_star.comp_continuousOn hS.cont_phi).mul hS.cont_xi))

/-- Both continuous Maxwell densities equal the ordinary characteristic
derivatives a.e. on each full section. The quantifier order is section first,
then its null exceptional set. This applies directly to broad AC solutions. -/
theorem _root_.EmcsfAcExtension.IsSolution.charge_derivatives_ae {e T : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle 0 T)) :
    (∀ u ∈ Icc 0 T, deriv (S.Q u) =ᵐ[volume.restrict (Icc u T)] S.QV e u) ∧
    (∀ v ∈ Icc 0 T, deriv (fun u => S.Q u v) =ᵐ[volume.restrict (Icc 0 v)]
      (fun u => S.QU e u v)) := by
  constructor
  · intro u hu
    apply deriv_ae_of_interior_integralForm
      ((continuous_QV hS).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun v hv => ⟨hu.1, hv.1, hv.2⟩))
    intro a b hua hab hbT
    exact (hS.eq_out u a b hua hab (by
      rintro ⟨x,y⟩ ⟨rfl, hy⟩
      exact ⟨hu.1, hua.le.trans hy.1, hy.2.trans hbT.le⟩)).2.2.2.1
  · intro v hv
    apply deriv_ae_of_interior_integralForm
      ((continuous_QU hS).comp (continuous_id.prodMk continuous_const).continuousOn
        (fun u hu => ⟨hu.1, hu.2, hv.2⟩))
    intro a b h0a hab hbv
    exact (hS.eq_in a b v hab hbv (by
      rintro ⟨x,y⟩ ⟨hax, hxb, rfl⟩
      exact ⟨h0a.le.trans hax, hxb.trans hbv.le, hv.2⟩)).2.2.2.1

private theorem mul_uniform_real {T : ℝ} {F G : ℕ → (ℝ × ℝ) → ℝ}
    {f g : (ℝ × ℝ) → ℝ}
    (hF : TendstoUniformlyOn F f atTop (triangle 0 T))
    (hG : TendstoUniformlyOn G g atTop (triangle 0 T))
    (hf : ContinuousOn f (triangle 0 T)) (hg : ContinuousOn g (triangle 0 T)) :
    TendstoUniformlyOn (fun n p => F n p * G n p) (fun p => f p * g p) atTop (triangle 0 T) :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_triangle 0 T)).1
    (hF.tendstoLocallyUniformlyOn.mul₀ hG.tendstoLocallyUniformlyOn hf hg)

/-- Pass both Maxwell currents strongly, uniformly over all sections, from
primary uniform convergence of a general AC sequence. No smoothness or
constructed provenance is required by this analytic helper. The integral
conversion retains the explicit factor at most `T`. -/
theorem charge_strong_limits_of_primary_uniform {e T : ℝ} {Sn : ℕ → Fields} {S : Fields}
    (hT : 0 < T) (hSn : ∀ n, IsSolution e (Sn n) (triangle 0 T))
    (hS : IsSolution e S (triangle 0 T))
    (hr : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).r) (Function.uncurry S.r) atTop
        (triangle 0 T))
    (hphi : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).phi) (Function.uncurry S.phi) atTop
        (triangle 0 T))
    (hθ : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).theta) (Function.uncurry S.theta)
        atTop (triangle 0 T))
    (hξ : TendstoUniformlyOn (fun n => Function.uncurry (Sn n).xi) (Function.uncurry S.xi) atTop
        (triangle 0 T)) :
    TendstoUniformlyOn (fun n => Function.uncurry ((Sn n).QV e)) (Function.uncurry (S.QV e)) atTop
        (triangle 0 T) ∧
    TendstoUniformlyOn (fun n => Function.uncurry ((Sn n).QU e)) (Function.uncurry (S.QU e)) atTop
        (triangle 0 T) ∧
    (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ Icc 0 T,
      (∫ v in u..T, ‖deriv ((Sn n).Q u) v - deriv (S.Q u) v‖) < ρ) ∧
    (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
      (∫ u in (0 : ℝ)..v, ‖deriv (fun u => (Sn n).Q u v) u - deriv (fun u => S.Q u v) u‖) < ρ) := by
  have hconj := Complex.conjLIE.isometry.uniformContinuous.comp_tendstoUniformlyOn hphi
  have hpθ := Mixed.tendstoUniformlyOn_mul_of_isCompact (isCompact_triangle 0 T)
    (fun n => continuous_star.comp_continuousOn (hSn n).cont_phi)
    (fun n => (hSn n).cont_theta) hconj hθ
  have hpξ := Mixed.tendstoUniformlyOn_mul_of_isCompact (isCompact_triangle 0 T)
    (fun n => continuous_star.comp_continuousOn (hSn n).cont_phi)
    (fun n => (hSn n).cont_xi) hconj hξ
  have himθ := Complex.imCLM.uniformContinuous.comp_tendstoUniformlyOn hpθ
  have himξ := Complex.imCLM.uniformContinuous.comp_tendstoUniformlyOn hpξ
  have he := (uniformContinuous_mul_right' e).comp_tendstoUniformlyOn hr
  have hEr : TendstoUniformlyOn (fun n p => e * (Sn n).r p.1 p.2)
      (fun p => e * S.r p.1 p.2) atTop (triangle 0 T) := by
    simpa only [Function.comp_def, Function.uncurry_def, mul_comm] using he
  have hQV := (mul_uniform_real hEr himθ ((continuousOn_const (c := e)).mul hS.cont_r)
    (Complex.continuous_im.comp_continuousOn
      ((continuous_star.comp_continuousOn hS.cont_phi).mul hS.cont_theta))).neg
  have hQU := mul_uniform_real hEr himξ ((continuousOn_const (c := e)).mul hS.cont_r)
    (Complex.continuous_im.comp_continuousOn
      ((continuous_star.comp_continuousOn hS.cont_phi).mul hS.cont_xi))
  have hqv : TendstoUniformlyOn (fun n => Function.uncurry ((Sn n).QV e))
      (Function.uncurry (S.QV e)) atTop (triangle 0 T) := hQV
  have hqu : TendstoUniformlyOn (fun n => Function.uncurry ((Sn n).QU e))
      (Function.uncurry (S.QU e)) atTop (triangle 0 T) := hQU
  have hv := (section_integrals_tendsto_of_uniform hT (fun n => continuous_QV (hSn n))
      (continuous_QV hS) hqv).1
  have hu := (section_integrals_tendsto_of_uniform hT (fun n => continuous_QU (hSn n))
      (continuous_QU hS) hqu).2
  refine ⟨hqv, hqu, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨N,hN⟩ := hv ρ hρ
    refine ⟨N, fun n hn u hu => ?_⟩
    have heq : (∫ v in u..T, ‖deriv ((Sn n).Q u) v - deriv (S.Q u) v‖) =
        ∫ v in u..T, ‖(Sn n).QV e u v - S.QV e u v‖ := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le hu.2]
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self ((hSn
          n).charge_derivatives_ae.1 u hu),
        ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self (hS.charge_derivatives_ae.1 u hu)]
            with v hvn hvs
      rw [hvn, hvs]
    rw [heq]
    exact hN n hn u hu
  · intro ρ hρ
    obtain ⟨N,hN⟩ := hu ρ hρ
    refine ⟨N, fun n hn v hv => ?_⟩
    have heq : (∫ u in (0 : ℝ)..v, ‖deriv (fun u => (Sn n).Q u v) u - deriv (fun u => S.Q u v) u‖) =
        ∫ u in (0 : ℝ)..v, ‖(Sn n).QU e u v - S.QU e u v‖ := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le hv.1]
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self ((hSn
          n).charge_derivatives_ae.2 v hv),
        ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self (hS.charge_derivatives_ae.2 v hv)]
            with u hun hus
      rw [hun, hus]
    rw [heq]
    exact hN n hn v hv

/-- The outgoing charge primitive extends to the axis for every broad AC
solution. Its integration coefficient is one and its axis trace is zero. -/
theorem _root_.EmcsfAcExtension.IsSolution.charge_eq_outgoing_integral {e T : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle 0 T)) {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    S.Q u v = ∫ w in u..v, S.QV e u w := by
  have hs : outSeg u u v ⊆ triangle 0 T := by
    rintro ⟨x,y⟩ ⟨rfl, hy⟩
    exact ⟨hp.1, hy.1, hy.2.trans hp.2.2⟩
  have hac := (hS.ac_out u u v hp.2.1 hs).2.2.1
  have hd := hS.charge_derivatives_ae.1 u ⟨hp.1, hp.2.1.trans hp.2.2⟩
  have hde : deriv (S.Q u) =ᵐ[volume.restrict (uIcc u v)] S.QV e u := by
    rw [uIcc_of_le hp.2.1]
    exact ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc le_rfl hp.2.2) hd
  have heq := (integralForm_of_ac_of_ae_deriv_eq hac hde).2
  have haxis := (hS.axis u ⟨hp.1, le_rfl, hp.2.1.trans hp.2.2⟩).2.2.1
  simpa only [haxis, sub_zero] using heq

/-- Uniform current convergence supplies uniform charge convergence, including
the common zero axis trace. The primitive error retains the factor at most `T`. -/
theorem charge_uniform_of_current_uniform {e T : ℝ} {Sn : ℕ → Fields} {S : Fields}
    (hT : 0 < T) (hSn : ∀ n, IsSolution e (Sn n) (triangle 0 T))
    (hS : IsSolution e S (triangle 0 T))
    (hl : TendstoUniformlyOn (fun n => Function.uncurry ((Sn n).QV e))
      (Function.uncurry (S.QV e)) atTop (triangle 0 T)) :
    TendstoUniformlyOn (fun n => Function.uncurry (Sn n).Q) (Function.uncurry S.Q) atTop (triangle 0
        T) := by
  apply Metric.tendstoUniformlyOn_iff.2
  intro ρ hρ
  let δ := ρ / (T+1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  filter_upwards [(Metric.tendstoUniformlyOn_iff.1 hl) δ hδ] with n hn p hp
  have hm : MapsTo (fun w => (p.1,w)) (Icc p.1 p.2) (triangle 0 T) :=
    fun w hw => ⟨hp.1, hw.1, hw.2.trans hp.2.2⟩
  have hi₁ : IntervalIntegrable ((Sn n).QV e p.1) volume p.1 p.2 :=
    ((continuous_QV (hSn n)).comp (continuous_const.prodMk continuous_id).continuousOn
        hm).intervalIntegrable_of_Icc hp.2.1
  have hi₂ : IntervalIntegrable (S.QV e p.1) volume p.1 p.2 :=
    ((continuous_QV hS).comp (continuous_const.prodMk continuous_id).continuousOn
        hm).intervalIntegrable_of_Icc hp.2.1
  have hbound := Mixed.integral_norm_section_le hp.1 hp.2.1 hp.2.2 hδ.le (hi₁.sub hi₂)
    (fun w hw => by
      have hh := hn (p.1,w) (hm hw)
      rw [dist_comm, dist_eq_norm] at hh
      exact hh.le)
  have hlt : T * δ < ρ := by
    dsimp only [δ]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < T+1)]
    nlinarith only [hρ]
  rw [dist_comm, dist_eq_norm]
  change ‖(Sn n).Q p.1 p.2 - S.Q p.1 p.2‖ < ρ
  rw [(hSn n).charge_eq_outgoing_integral hp, hS.charge_eq_outgoing_integral hp,
    ← intervalIntegral.integral_sub hi₁ hi₂]
  exact (intervalIntegral.norm_integral_le_integral_norm hp.2.1).trans_lt (hbound.trans_lt hlt)

end EmcsfAcExtension.Local
