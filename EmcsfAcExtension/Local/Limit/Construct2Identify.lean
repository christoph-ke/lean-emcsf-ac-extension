module

public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Local.Defs.Envelope
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Limit.UIAux
import EmcsfAcExtension.Infra.W11.Completeness

/-! # Sectionwise identification of limiting renormalized derivatives

Strong ordinary derivative convergence gives an a.e. convergent subsequence
on each section. Algebraic convergence off the axis then identifies the
mixed-density limit with the frozen derivative. No two-dimensional null set
is restricted to a prescribed section.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem ae_eq_of_lintegral_of_ae_tendsto {F : ℕ → ℝ → ℂ} {f g : ℝ → ℂ}
    {μ : Measure ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n - g) μ)
    (hlim : Tendsto (fun n => ∫⁻ x, ‖F n x - g x‖ₑ ∂μ) atTop (𝓝 0))
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    f =ᵐ[μ] g := by
  have hmeasure : TendstoInMeasure μ F atTop g := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
    simpa only [fun n => eLpNorm_one_eq_lintegral_enorm (hF n), Pi.sub_apply] using hlim
  obtain ⟨ns, hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  filter_upwards [hpoint, hae] with x hx hg
  exact tendsto_nhds_unique (hx.comp hns.tendsto_atTop) hg

private theorem exists_derivative_subseq {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ n, AbsolutelyContinuousOnInterval (F n) a b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hlim : Tendsto (fun n => ∫ x in a..b, ‖deriv (F n) x - deriv f x‖)
      atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂volume.restrict (Icc a b),
        Tendsto (fun n => deriv (F (ns n)) x) atTop (𝓝 (deriv f x)) := by
  have hi n : IntegrableOn (fun x => deriv (F n) x - deriv f x) (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1
      ((hF n).intervalIntegrable_deriv_complex.sub hf.intervalIntegrable_deriv_complex)
  have he n : eLpNorm ((fun x => deriv (F n) x) - deriv f) 1
      (volume.restrict (Icc a b)) =
      ENNReal.ofReal (∫ x in a..b, ‖deriv (F n) x - deriv f x‖) := by
    change eLpNorm (fun x => deriv (F n) x - deriv f x) 1
      (volume.restrict (Icc a b)) = _
    rw [eLpNorm_one_eq_lintegral_enorm (hi n).aestronglyMeasurable]
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_norm_eq_lintegral_enorm (hi n)]
  have hm : TendstoInMeasure (volume.restrict (Icc a b))
      (fun n x => deriv (F n) x) atTop (deriv f) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
    simpa only [he, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  exact hm.exists_seq_tendsto_ae

/-- Identify an outgoing mixed-density limit with the frozen `jOut` on each
fixed outgoing section. This helper assumes the already constructed uniform
fields, AC scalar and strong ordinary derivatives. Only coefficient one is
used, independently of the triangle and all field sizes. The endpoint null
sets are taken in the one-dimensional section measure. -/
theorem jOut_eq_of_uniform_of_derivative_limit {T : ℝ} {Sn : ℕ → Fields} {S : Fields}
    {e : ℝ} {j : ℝ → ℝ → ℂ}
    (hT : 0 < T)
    (hS : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hr : ∀ p ∈ triangle 0 T, Tendsto (fun n => (Sn n).r p.1 p.2) atTop (𝓝 (S.r p.1 p.2)))
    (hl : ∀ p ∈ triangle 0 T, Tendsto (fun n => (Sn n).lam p.1 p.2) atTop (𝓝 (S.lam p.1 p.2)))
    (hm : ∀ p ∈ triangle 0 T, Tendsto (fun n => (Sn n).m p.1 p.2) atTop (𝓝 (S.m p.1 p.2)))
    (ht : ∀ p ∈ triangle 0 T, Tendsto (fun n => (Sn n).theta p.1 p.2) atTop (𝓝 (S.theta p.1 p.2)))
    (hrpos : ∀ p ∈ triangle 0 T, p.1 < p.2 → 0 < S.r p.1 p.2)
    (hlpos : ∀ p ∈ triangle 0 T, 0 < S.lam p.1 p.2)
    (hjm : Measurable (Function.uncurry j))
    (hjl : Tendsto (fun n => ∫⁻ v in Icc 0 T,
      outEnv 0 (fun u v => jC1 (triangle 0 T) (Sn n) u v - j u v) v) atTop (𝓝 0))
    {u : ℝ} (hu : u ∈ Icc 0 T)
    (ha : AbsolutelyContinuousOnInterval (S.a u) u T)
    (hder : Tendsto (fun n => ∫ v in u..T,
      ‖deriv ((Sn n).a u) v - deriv (S.a u) v‖) atTop (𝓝 0)) :
    jOut S u =ᵐ[volume.restrict (Icc u T)] j u := by
  have hac n : AbsolutelyContinuousOnInterval ((Sn n).a u) u T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hu.2]
    exact (hS n).c1_a.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun v hv => ⟨hu.1, hv.1, hv.2⟩)
  obtain ⟨ns, hns, hdae⟩ := exists_derivative_subseq hu.2 hac ha hder
  have hpoint : ∀ᵐ v ∂volume.restrict (Icc u T),
      Tendsto (fun n => jC1 (triangle 0 T) (Sn (ns n)) u v) atTop (𝓝 (jOut S u v)) := by
    have hu0 : ∀ᵐ v : ℝ, v ≠ u := by simp [ae_iff, measure_singleton]
    have hT0 : ∀ᵐ v : ℝ, v ≠ T := by simp [ae_iff, measure_singleton]
    filter_upwards [hdae, ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae hu0, ae_restrict_of_ae hT0] with v hd hv hvu hvT
    have huv : u < v := lt_of_le_of_ne hv.1 hvu.symm
    have hvT' : v < T := lt_of_le_of_ne hv.2 hvT
    have hp : (u, v) ∈ triangle 0 T := ⟨hu.1, hv.1, hv.2⟩
    have hpd n : pdV (triangle 0 T) (Sn (ns n)).a u v = deriv ((Sn (ns n)).a u) v :=
      (deriv_eq_pdV (hS _).c1_a hp (s := Icc u T)
        (fun w hw => ⟨hu.1, hw.1, hw.2⟩) (Icc_mem_nhds huv hvT')).symm
    have hrr := (hr _ hp).comp hns.tendsto_atTop
    have hll := (hl _ hp).comp hns.tendsto_atTop
    have hmm := (hm _ hp).comp hns.tendsto_atTop
    have htt := (ht _ hp).comp hns.tendsto_atTop
    have hmu := (hmm.const_mul 2).div hrr (hrpos _ hp huv).ne'
    have hx := htt.div (Complex.continuous_ofReal.continuousAt.tendsto.comp hll)
      (Complex.ofReal_ne_zero.mpr (hlpos _ hp).ne')
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (hll.div hrr (hrpos _ hp huv).ne')
    have hg := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (hmu.const_sub 1)
    have hnorm := Complex.continuous_ofReal.continuousAt.tendsto.comp (hx.norm.pow 2)
    simpa only [jC1, jOut, Fields.mu, hpd, Function.comp_def, Pi.div_apply,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_pow] using hg.mul
          (hd.sub ((hc.mul hnorm).mul hx))
  have hc n : ContinuousOn (jC1 (triangle 0 T) (Sn n) u) (Icc u T) :=
    ((hS n).continuousOn_jC1 hT).comp (f := fun v : ℝ => (u, v))
      (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨hu.1, hv.1, hv.2⟩)
  have hjmeas : Measurable (j u) := hjm.comp (measurable_const.prodMk measurable_id)
  apply ae_eq_of_lintegral_of_ae_tendsto
    (fun n => ((hc (ns n)).aestronglyMeasurable measurableSet_Icc).sub hjmeas.aestronglyMeasurable)
    (hpoint := hpoint)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hjl.comp hns.tendsto_atTop) (fun _ => zero_le) (fun n => ?_)
  calc
    (∫⁻ v in Icc u T, ‖jC1 (triangle 0 T) (Sn (ns n)) u v - j u v‖ₑ) ≤
        ∫⁻ v in Icc u T,
          outEnv 0 (fun u v => jC1 (triangle 0 T) (Sn (ns n)) u v - j u v) v := by
      apply setLIntegral_mono' measurableSet_Icc
      intro v hv
      exact le_iSup₂_of_le u ⟨hu.1, hv.1⟩ le_rfl
    _ ≤ _ := lintegral_mono_set (Icc_subset_Icc hu.1 le_rfl)

/-- Identify an incoming mixed-density limit with the frozen `kIn`, retaining
the actual limiting connection `e * A`. This helper uses sectionwise strong
ordinary derivatives and pointwise primary limits. Its coefficient is one,
independently of coupling, time and field sizes, and it uses no common
two-dimensional exceptional set for the section derivatives. -/
theorem kIn_eq_of_uniform_of_derivative_limit {T : ℝ} {Sn : ℕ → Fields} {S : Fields}
    {e : ℝ} {k : ℝ → ℝ → ℂ} (hT : 0 < T)
    (hS : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hr : ∀ p ∈ triangle 0 T, Tendsto (fun n => (Sn n).r p.1 p.2) atTop (𝓝 (S.r p.1 p.2)))
    (hn : ∀ p ∈ triangle 0 T, Tendsto (fun n => (Sn n).nu p.1 p.2) atTop (𝓝 (S.nu p.1 p.2)))
    (hm : ∀ p ∈ triangle 0 T, Tendsto (fun n => (Sn n).m p.1 p.2) atTop (𝓝 (S.m p.1 p.2)))
    (hx : ∀ p ∈ triangle 0 T, Tendsto (fun n => (Sn n).xi p.1 p.2) atTop (𝓝 (S.xi p.1 p.2)))
    (hA : ∀ p ∈ triangle 0 T, Tendsto (fun n => (Sn n).A p.1 p.2) atTop (𝓝 (S.A p.1 p.2)))
    (hb : ∀ p ∈ triangle 0 T, Tendsto (fun n => (Sn n).b p.1 p.2) atTop (𝓝 (S.b p.1 p.2)))
    (hrpos : ∀ p ∈ triangle 0 T, p.1 < p.2 → 0 < S.r p.1 p.2)
    (hnneg : ∀ p ∈ triangle 0 T, S.nu p.1 p.2 < 0)
    (hkm : Measurable (Function.uncurry k))
    (hkl : Tendsto (fun n => ∫⁻ u in Icc 0 T,
      inEnv T (fun u v => kC1 e (triangle 0 T) (Sn n) u v - k u v) u) atTop (𝓝 0))
    {v : ℝ} (hv : v ∈ Icc 0 T)
    (ha : AbsolutelyContinuousOnInterval (fun u => S.b u v) 0 v)
    (hder : Tendsto (fun n => ∫ u in (0 : ℝ)..v,
      ‖deriv (fun u => (Sn n).b u v) u - deriv (fun u => S.b u v) u‖) atTop (𝓝 0)) :
    (fun u => kIn e S u v) =ᵐ[volume.restrict (Icc 0 v)] (fun u => k u v) := by
  have hac n : AbsolutelyContinuousOnInterval (fun u => (Sn n).b u v) 0 v := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hv.1]
    exact (hS n).c1_b.comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun u hu => ⟨hu.1, hu.2, hv.2⟩)
  obtain ⟨ns, hns, hdae⟩ := exists_derivative_subseq hv.1 hac ha hder
  have hpoint : ∀ᵐ u ∂volume.restrict (Icc 0 v),
      Tendsto (fun n => kC1 e (triangle 0 T) (Sn (ns n)) u v) atTop (𝓝 (kIn e S u v)) := by
    have h00 : ∀ᵐ u : ℝ, u ≠ 0 := by simp [ae_iff, measure_singleton]
    have hv0 : ∀ᵐ u : ℝ, u ≠ v := by simp [ae_iff, measure_singleton]
    filter_upwards [hdae, ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae h00, ae_restrict_of_ae hv0] with u hd hu hu0 huv
    have hu0' : 0 < u := lt_of_le_of_ne hu.1 hu0.symm
    have huv' : u < v := lt_of_le_of_ne hu.2 huv
    have hp : (u, v) ∈ triangle 0 T := ⟨hu.1, hu.2, hv.2⟩
    have hpd n : pdU (triangle 0 T) (Sn (ns n)).b u v =
        deriv (fun u => (Sn (ns n)).b u v) u :=
      (deriv_eq_pdU (hS _).c1_b hp (s := Icc 0 v)
        (fun w hw => ⟨hw.1, hw.2, hv.2⟩) (Icc_mem_nhds hu0' huv')).symm
    have hrr := (hr _ hp).comp hns.tendsto_atTop
    have hnn := (hn _ hp).comp hns.tendsto_atTop
    have hmm := (hm _ hp).comp hns.tendsto_atTop
    have hxx := (hx _ hp).comp hns.tendsto_atTop
    have hAA := (hA _ hp).comp hns.tendsto_atTop
    have hbb := (hb _ hp).comp hns.tendsto_atTop
    have hmu := (hmm.const_mul 2).div hrr (hrpos _ hp huv').ne'
    have hy := hxx.div (Complex.continuous_ofReal.continuousAt.tendsto.comp hnn)
      (Complex.ofReal_ne_zero.mpr (hnneg _ hp).ne)
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (hnn.div hrr (hrpos _ hp huv').ne')
    have hg := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (hmu.const_sub 1)
    have hnorm := Complex.continuous_ofReal.continuousAt.tendsto.comp (hy.norm.pow 2)
    have hconn := ((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => I * (e : ℂ)) atTop (𝓝 (I * (e : ℂ)))).mul
        (Complex.continuous_ofReal.continuousAt.tendsto.comp hAA)).mul hbb
    simpa only [kC1, kIn, Fields.mu, hpd, Function.comp_def, Pi.div_apply,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_pow] using hg.mul
          ((hd.add hconn).sub ((hc.mul hnorm).mul hy))
  have hc n : ContinuousOn (fun u => kC1 e (triangle 0 T) (Sn n) u v) (Icc 0 v) :=
    ((hS n).continuousOn_kC1 hT).comp (f := fun u : ℝ => (u, v))
      (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu.1, hu.2, hv.2⟩)
  have hkmeas : Measurable (fun u => k u v) := hkm.comp (measurable_id.prodMk measurable_const)
  apply ae_eq_of_lintegral_of_ae_tendsto
    (fun n => ((hc (ns n)).aestronglyMeasurable measurableSet_Icc).sub hkmeas.aestronglyMeasurable)
    (hpoint := hpoint)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hkl.comp hns.tendsto_atTop) (fun _ => zero_le) (fun n => ?_)
  calc
    (∫⁻ u in Icc 0 v, ‖kC1 e (triangle 0 T) (Sn (ns n)) u v - k u v‖ₑ) ≤
        ∫⁻ u in Icc 0 v,
          inEnv T (fun u v => kC1 e (triangle 0 T) (Sn (ns n)) u v - k u v) u := by
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      exact le_iSup₂_of_le v ⟨hu.2, hv.2⟩ le_rfl
    _ ≤ _ := lintegral_mono_set (Icc_subset_Icc le_rfl hv.2)

end EmcsfAcExtension.Local
