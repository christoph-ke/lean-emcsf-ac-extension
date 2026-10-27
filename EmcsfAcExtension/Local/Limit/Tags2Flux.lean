module

public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Limit.Tags2FluxAlgebra
import EmcsfAcExtension.Local.Limit.Construct2Strong
import EmcsfAcExtension.Local.Limit.UIAux
import EmcsfAcExtension.Local.Limit.Construct2Cauchy
import EmcsfAcExtension.Local.Stability.ExtendedLimits
import EmcsfAcExtension.Local.Stability.FluxDifferenceRegularity
import EmcsfAcExtension.Infra.Mixed.FiberCauchy
import EmcsfAcExtension.Local.Limit.StabilityPointwise
import EmcsfAcExtension.Local.Limit.AcBridgeIntegrals
import EmcsfAcExtension.Local.Stability.ExtendedLipschitz
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Calculus.C1ToSolution2
import EmcsfAcExtension.Local.Calculus.RelativeCharge

/-! # Strong actual currents and mass fluxes of the smooth approximation

The mass fluxes are the literal frozen mV and mU, including their electric
terms. A quadratic charge cusp controls the axis quotient Q/r before uniform
convergence is used; this excludes any unidentified quadratic defect.
charged_SF_new_version.tex:L6468–6477.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private structure Expr {E : Type} [NormedAddCommGroup E]
    (D : Set (ℝ × ℝ)) (F : ℕ → (ℝ × ℝ) → E) (f : (ℝ × ℝ) → E) : Prop where
  cn : ∀ n, ContinuousOn (F n) D
  c : ContinuousOn f D
  lim : TendstoLocallyUniformlyOn F f atTop D

private theorem Expr.of_uniform {E : Type} [NormedAddCommGroup E]
    {D : Set (ℝ × ℝ)} {F : ℕ → (ℝ × ℝ) → E} {f : (ℝ × ℝ) → E}
    (hc : ∀ n, ContinuousOn (F n) D) (hl : TendstoUniformlyOn F f atTop D) : Expr D F f :=
  ⟨hc, hl.continuousOn (Eventually.of_forall hc).frequently, hl.tendstoLocallyUniformlyOn⟩

private theorem Expr.const {E : Type} [NormedAddCommGroup E]
    (D : Set (ℝ × ℝ)) (z : E) : Expr D (fun _ _ => z) (fun _ => z) :=
  ⟨fun _ => continuousOn_const, continuousOn_const,
    (tendsto_const_nhds.tendstoUniformlyOn_const D).tendstoLocallyUniformlyOn⟩

private theorem Expr.add {E : Type} [NormedAddCommGroup E]
    {D : Set (ℝ × ℝ)} {F G : ℕ → (ℝ × ℝ) → E} {f g : (ℝ × ℝ) → E}
    (hf : Expr D F f) (hg : Expr D G g) : Expr D (fun n p => F n p + G n p) (fun p => f p + g p) :=
  ⟨fun n => (hf.cn n).add (hg.cn n), hf.c.add hg.c, hf.lim.add hg.lim⟩

private theorem Expr.sub {E : Type} [NormedAddCommGroup E]
    {D : Set (ℝ × ℝ)} {F G : ℕ → (ℝ × ℝ) → E} {f g : (ℝ × ℝ) → E}
    (hf : Expr D F f) (hg : Expr D G g) : Expr D (fun n p => F n p - G n p) (fun p => f p - g p) :=
  ⟨fun n => (hf.cn n).sub (hg.cn n), hf.c.sub hg.c, hf.lim.sub hg.lim⟩

private theorem Expr.mul {E : Type} [NormedField E]
    {D : Set (ℝ × ℝ)} {F G : ℕ → (ℝ × ℝ) → E} {f g : (ℝ × ℝ) → E}
    (hf : Expr D F f) (hg : Expr D G g) : Expr D (fun n p => F n p * G n p) (fun p => f p * g p) :=
  ⟨fun n => (hf.cn n).mul (hg.cn n), hf.c.mul hg.c, hf.lim.mul₀ hg.lim hf.c hg.c⟩

private theorem Expr.div {E : Type} [NormedField E]
    {D : Set (ℝ × ℝ)} {F G : ℕ → (ℝ × ℝ) → E} {f g : (ℝ × ℝ) → E}
    (hf : Expr D F f) (hg : Expr D G g)
    (hn : ∀ n p, p ∈ D → G n p ≠ 0) (h : ∀ p ∈ D, g p ≠ 0) :
    Expr D (fun n p => F n p / G n p) (fun p => f p / g p) :=
  ⟨fun n => (hf.cn n).div (hg.cn n) (hn n), hf.c.div hg.c h,
    hf.lim.div₀ hg.lim hf.c hg.c h⟩

private theorem Expr.map {E H : Type} [NormedAddCommGroup E] [NormedAddCommGroup H]
    {D : Set (ℝ × ℝ)} {F : ℕ → (ℝ × ℝ) → E} {f : (ℝ × ℝ) → E}
    (hf : Expr D F f) {g : E → H} (hg : UniformContinuous g) :
    Expr D (fun n p => g (F n p)) (fun p => g (f p)) :=
  ⟨fun n => hg.continuous.comp_continuousOn (hf.cn n), hg.continuous.comp_continuousOn hf.c,
    hg.comp_tendstoLocallyUniformlyOn hf.lim⟩

private theorem Expr.uniform {E : Type} [NormedAddCommGroup E]
    {T : ℝ} {F : ℕ → (ℝ × ℝ) → E} {f : (ℝ × ℝ) → E}
    (hf : Expr (triangle 0 T) F f) : TendstoUniformlyOn F f atTop (triangle 0 T) :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_triangle 0 T)).1 hf.lim

private theorem ae_eq_of_uniform_L1_limit {μ : Measure ℝ} {F : ℕ → ℝ → ℝ} {f q : ℝ → ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hq : Integrable q μ)
    (herror : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, (∫ x, ‖F n x - q x‖ ∂μ) < ρ)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) : f =ᵐ[μ] q := by
  have ht : Tendsto (fun n => ∫ x, ‖F n x - q x‖ ∂μ) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ρ hρ
    obtain ⟨N,hN⟩ := herror ρ hρ
    refine ⟨N,fun n hn => ?_⟩
    have hnonneg : 0 ≤ ∫ x, ‖F n x - q x‖ ∂μ :=
      MeasureTheory.integral_nonneg (fun x => norm_nonneg (F n x - q x))
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hN n hn
  have hm : TendstoInMeasure μ F atTop q :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
      (Mixed.tendsto_eLpNorm_one_of_integral hF hq ht)
  obtain ⟨ns,hns,hae⟩ := hm.exists_seq_tendsto_ae
  filter_upwards [hpoint,hae] with x hx hqx
  exact tendsto_nhds_unique (hx.comp hns.tendsto_atTop) hqx

/-- [node restart-sec-independent-null-construction#strong-current-mass-flux-limit]
The actual Maxwell currents and both actual mass fluxes converge uniformly
and strongly in L¹ uniformly over their characteristic sections. Both
oriented weighted scalar quadratic fluxes also converge strongly to their
actual limiting-field expressions, uniformly over complete sections. The same
fixed-label limit retains uniform scalar averages through `StrongLimit`.
The positive threshold depends only on the fixed envelope coefficient `A`;
it precedes time, coupling, background, datum and smooth approximants. No
initial derivative supremum or limiting flux is assumed. The section-length
factor in uniform-to-L¹ passage is at most `T`. -/
theorem strong_current_mass_flux_limit (A : ℝ) (hA : 0 < A) :
    ∃ s : ℝ, 0 < s ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        AbsolutelyContinuousOnInterval h 0 T → (∀ n, hn n 0 = h 0) →
        Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) →
        ε ^ 2 + sigma e M T ≤ s →
        ∃ S : Fields, StrongLimit e T Sn S ∧
          TendstoUniformlyOn (fun n => Function.uncurry ((Sn n).QV e))
            (Function.uncurry (S.QV e)) atTop (triangle 0 T) ∧
          TendstoUniformlyOn (fun n => Function.uncurry ((Sn n).QU e))
            (Function.uncurry (S.QU e)) atTop (triangle 0 T) ∧
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).mV)
            (Function.uncurry S.mV) atTop (triangle 0 T) ∧
          TendstoUniformlyOn (fun n => Function.uncurry (Sn n).mU)
            (Function.uncurry S.mU) atTop (triangle 0 T) ∧
          (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ Icc 0 T,
            (∫ v in u..T, ‖(Sn n).QV e u v - S.QV e u v‖) < ρ) ∧
          (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
            (∫ u in (0 : ℝ)..v, ‖(Sn n).QU e u v - S.QU e u v‖) < ρ) ∧
          (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ u ∈ Icc 0 T,
            (∫ v in u..T, ‖(Sn n).mV u v - S.mV u v‖) < ρ) ∧
          (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ v ∈ Icc 0 T,
            (∫ u in (0 : ℝ)..v, ‖(Sn n).mU u v - S.mU u v‖) < ρ) ∧
          (∀ u ∈ Icc 0 T, IntegrableOn
            (fun v => S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2) (Icc u T)) ∧
          (∀ v ∈ Icc 0 T, IntegrableOn
            (fun u => -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2) (Icc 0 v)) ∧
          (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N,
            (∀ u ∈ Icc 0 T, (∫ v in Icc u T,
              |(Sn n).lam u v / (Sn n).r u v * ‖(Sn n).theta u v / (Sn n).lam u v‖ ^ 2 -
                S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2|) < ρ) ∧
            (∀ v ∈ Icc 0 T, (∫ u in Icc 0 v,
              |-(Sn n).nu u v / (Sn n).r u v * ‖(Sn n).xi u v / (Sn n).nu u v‖ ^ 2 -
                -S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2|) < ρ)) := by
  obtain ⟨s, hs, hlim⟩ := Null.strong_limit_of_inputs stab_extended A hA
  obtain ⟨sw,hsw,hweighted⟩ := Stab.weighted_quadratic_flux_strong_limit A hA
  refine ⟨min s sw,lt_min hs hsw,?_⟩
  intro T e ε M Sn hn h hset hac hv hd hsmall
  obtain ⟨S,hl,hMu,_⟩ := hlim T e ε M Sn hn h hset hac hv hd (hsmall.trans (min_le_left _ _))
  have hT := (hset 0).pos
  have hM : 0 ≤ M := zero_le_one.trans (hset 0).box.1
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg ((Sn 0).xi 0 0 / (Sn 0).nu 0 0))).trans
      ((hset 0).box.2 (0,0) ⟨le_rfl,le_rfl,hT.le⟩).2.2.2.2.2.1)
  let B := |e| * M * ε / 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb n (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) :
      0 ≤ (Sn n).r p.1 p.2 ∧ (Sn n).r p.1 p.2 ≤ T ∧
        |(Sn n).Q p.1 p.2| ≤ B * (Sn n).r p.1 p.2 ^ 2 := by
    have hr := stab_radius_bounds (hset n) hp.1 hp.2.1 hp.2.2
    refine ⟨(by linarith only [hr.1,hp.2.1]), (by linarith only [hr.2,hp.1,hp.2.2]), ?_⟩
    have hseg : outSeg p.1 p.1 p.2 ⊆ triangle 0 T := by
      rintro ⟨x,y⟩ ⟨rfl,hy⟩
      exact ⟨hp.1,hy.1,hy.2.trans hp.2.2⟩
    have hQ := Stab.oscillatory_charge_bound ((hset n).c1.toIsSolution hT) hp.2.1 hseg
      (fun t ht => ((hset n).box.2 (p.1,t) (hseg ⟨rfl,ht⟩)).2.2.2.2.2.2)
      (fun t ht => (le_add_of_nonneg_right (norm_nonneg _)).trans
        ((hset n).box.2 (p.1,t) (hseg ⟨rfl,ht⟩)).2.2.2.2.2.1)
    simpa only [B, div_mul_eq_mul_div] using hQ
  obtain ⟨cqn,cq,hq⟩ := uniform_charge_ratio_of_quadratic_bound hB hT.le
    (fun n => (hset n).c1.c1_r.continuousOn) (fun n => (hset n).c1.c1_Q.continuousOn)
    hl.unif_r hl.unif_Q hb
  let D := triangle 0 T
  have radius := Expr.of_uniform (fun n => (hset n).c1.c1_r.continuousOn) hl.unif_r
  have lam := Expr.of_uniform (fun n => (hset n).c1.c1_lam.continuousOn) hl.unif_lam
  have nu := Expr.of_uniform (fun n => (hset n).c1.c1_nu.continuousOn) hl.unif_nu
  have mu := Expr.of_uniform (fun n => (hset n).c1.continuousOn_mu hT) hMu
  have theta := Expr.of_uniform (fun n => (hset n).c1.c1_theta.continuousOn) hl.unif_theta
  have xi := Expr.of_uniform (fun n => (hset n).c1.c1_xi.continuousOn) hl.unif_xi
  have phi := Expr.of_uniform (fun n => (hset n).c1.c1_phi.continuousOn) hl.unif_phi
  have qr := Expr.of_uniform cqn hq
  have geo := hl.lower_geometry_of_settings hset
  have hlam p (hp : p ∈ D) : S.lam p.1 p.2 ≠ 0 := by
    have hh := (geo p hp).1
    linarith only [hh]
  have hnu p (hp : p ∈ D) : S.nu p.1 p.2 ≠ 0 := by
    have hh := (geo p hp).2.1
    linarith only [hh]
  have g := (Expr.const D (1 : ℝ)).sub mu
  have two := Expr.const D (2 : ℝ)
  have tv := (theta.map uniformContinuous_norm).mul (theta.map uniformContinuous_norm)
  have xv := (xi.map uniformContinuous_norm).mul (xi.map uniformContinuous_norm)
  have mv := ((g.mul tv).div (two.mul lam)
    (fun n p hp => mul_ne_zero (by norm_num) ((hset n).c1.lam_pos p hp).ne')
    (fun p hp => mul_ne_zero (by norm_num) (hlam p hp))).add
      ((((qr.mul qr).mul lam).div two (by intros; norm_num) (by intros; norm_num)))
  have muFlux := ((g.mul xv).div (two.mul nu)
    (fun n p hp => mul_ne_zero (by norm_num) ((hset n).c1.nu_neg p hp).ne)
    (fun p hp => mul_ne_zero (by norm_num) (hnu p hp))).add
      ((((qr.mul qr).mul nu).div two (by intros; norm_num) (by intros; norm_num)))
  have hmV : Expr D (fun n => Function.uncurry (Sn n).mV) (Function.uncurry S.mV) := by
    convert mv using 1 <;> first
      | (funext n p; simp only [Fields.mV, Function.uncurry_def, pow_two]; ring)
      | (funext p; simp only [Fields.mV, Function.uncurry_def, pow_two]; ring)
  have hmU : Expr D (fun n => Function.uncurry (Sn n).mU) (Function.uncurry S.mU) := by
    convert muFlux using 1 <;> first
      | (funext n p; simp only [Fields.mU, Function.uncurry_def, pow_two]; ring)
      | (funext p; simp only [Fields.mU, Function.uncurry_def, pow_two]; ring)
  have conjPhi := phi.map Complex.conjLIE.isometry.uniformContinuous
  have currentV := (((Expr.const D e).mul radius).mul
    ((conjPhi.mul theta).map Complex.imCLM.uniformContinuous))
  have currentU := (((Expr.const D e).mul radius).mul
    ((conjPhi.mul xi).map Complex.imCLM.uniformContinuous))
  have hQV : Expr D (fun n => Function.uncurry ((Sn n).QV e)) (Function.uncurry (S.QV e)) := by
    convert (Expr.const D (0 : ℝ)).sub currentV using 1 <;> first
      | (funext n p; simp only [Fields.QV, Function.uncurry_def, zero_sub,
          Complex.imCLM_apply, Complex.conjLIE_apply])
      | (funext p; simp only [Fields.QV, Function.uncurry_def, zero_sub,
          Complex.imCLM_apply, Complex.conjLIE_apply])
  have hQU : Expr D (fun n => Function.uncurry ((Sn n).QU e)) (Function.uncurry (S.QU e)) := by
    exact currentU
  obtain ⟨qo,qi,hqo,hqi,hclose⟩ := hweighted T e ε M Sn hn hset
    (hsmall.trans (min_le_right _ _)) (data_dist_cauchy_of_stabSetting hset hac hv hd)
  have hFo n (u : Icc (0 : ℝ) T) : Integrable
      (fun v => (Sn n).lam u.1 v / (Sn n).r u.1 v *
        ‖(Sn n).theta u.1 v / (Sn n).lam u.1 v‖ ^ 2) (volume.restrict (Icc u.1 T)) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le u.property.2).1
    exact ((stab_out_quadratic_flux_continuous (hset n)).comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨u.property.1,hv.1,hv.2⟩)).intervalIntegrable_of_Icc u.property.2
  have hFi n (v : Icc (0 : ℝ) T) : Integrable
      (fun u => -(Sn n).nu u v.1 / (Sn n).r u v.1 *
        ‖(Sn n).xi u v.1 / (Sn n).nu u v.1‖ ^ 2) (volume.restrict (Icc 0 v.1)) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le v.property.1).1
    exact ((stab_in_quadratic_flux_continuous (hset n)).comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun u hu => ⟨hu.1,hu.2,v.property.2⟩)).intervalIntegrable_of_Icc v.property.1
  have ho (u : Icc (0 : ℝ) T) :
      (fun v => S.lam u.1 v / S.r u.1 v * ‖S.theta u.1 v / S.lam u.1 v‖ ^ 2)
        =ᵐ[volume.restrict (Icc u.1 T)] qo u := by
    apply ae_eq_of_uniform_L1_limit (fun n => hFo n u) (hqo u)
    · intro ρ hρ
      obtain ⟨N,hN⟩ := hclose ρ hρ
      exact ⟨N,fun n hn => by simpa only [Real.norm_eq_abs] using (hN n hn).1 u⟩
    · have hne : ∀ᵐ v : ℝ, v ≠ u.1 := by simp [ae_iff, measure_singleton]
      filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hne] with v hv hne
      have hp : (u.1,v) ∈ D := ⟨u.property.1,hv.1,hv.2⟩
      have huv := lt_of_le_of_ne hv.1 hne.symm
      have hr : 0 < S.r u.1 v := (div_pos (sub_pos.mpr huv) (by norm_num)).trans_le
        (geo (u.1,v) hp).2.2
      exact ((hl.unif_lam.tendsto_at hp).div (hl.unif_r.tendsto_at hp) hr.ne').mul
        (((hl.unif_theta.tendsto_at hp).div
          (Complex.continuous_ofReal.continuousAt.tendsto.comp (hl.unif_lam.tendsto_at hp))
          (Complex.ofReal_ne_zero.mpr (hlam _ hp))).norm.pow 2)
  have hi (v : Icc (0 : ℝ) T) :
      (fun u => -S.nu u v.1 / S.r u v.1 * ‖S.xi u v.1 / S.nu u v.1‖ ^ 2)
        =ᵐ[volume.restrict (Icc 0 v.1)] qi v := by
    apply ae_eq_of_uniform_L1_limit (fun n => hFi n v) (hqi v)
    · intro ρ hρ
      obtain ⟨N,hN⟩ := hclose ρ hρ
      exact ⟨N,fun n hn => by simpa only [Real.norm_eq_abs] using (hN n hn).2 v⟩
    · have hne : ∀ᵐ u : ℝ, u ≠ v.1 := by simp [ae_iff, measure_singleton]
      filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hne] with u hu hne
      have hp : (u,v.1) ∈ D := ⟨hu.1,hu.2,v.property.2⟩
      have huv := lt_of_le_of_ne hu.2 hne
      have hr : 0 < S.r u v.1 := (div_pos (sub_pos.mpr huv) (by norm_num)).trans_le
        (geo (u,v.1) hp).2.2
      exact (((hl.unif_nu.tendsto_at hp).neg).div (hl.unif_r.tendsto_at hp) hr.ne').mul
        (((hl.unif_xi.tendsto_at hp).div
          (Complex.continuous_ofReal.continuousAt.tendsto.comp (hl.unif_nu.tendsto_at hp))
          (Complex.ofReal_ne_zero.mpr (hnu _ hp))).norm.pow 2)
  refine ⟨S,hl,hQV.uniform,hQU.uniform,hmV.uniform,hmU.uniform,
    (section_integrals_tendsto_of_uniform hT hQV.cn hQV.c hQV.uniform).1,
    (section_integrals_tendsto_of_uniform hT hQU.cn hQU.c hQU.uniform).2,
    (section_integrals_tendsto_of_uniform hT hmV.cn hmV.c hmV.uniform).1,
    (section_integrals_tendsto_of_uniform hT hmU.cn hmU.c hmU.uniform).2,
    fun u hu => (hqo ⟨u,hu⟩).congr (ho ⟨u,hu⟩).symm,
    fun v hv => (hqi ⟨v,hv⟩).congr (hi ⟨v,hv⟩).symm,?_⟩
  intro ρ hρ
  obtain ⟨N,hN⟩ := hclose ρ hρ
  refine ⟨N,fun n hn => ⟨?_,?_⟩⟩
  · intro u hu
    have heq := integral_congr_ae ((ho ⟨u,hu⟩).mono fun v hv =>
      congrArg (fun z => |(Sn n).lam u v / (Sn n).r u v *
        ‖(Sn n).theta u v / (Sn n).lam u v‖ ^ 2 - z|) hv)
    exact heq.trans_lt ((hN n hn).1 ⟨u,hu⟩)
  · intro v hv
    have heq := integral_congr_ae ((hi ⟨v,hv⟩).mono fun u hu =>
      congrArg (fun z => |-(Sn n).nu u v / (Sn n).r u v *
        ‖(Sn n).xi u v / (Sn n).nu u v‖ ^ 2 - z|) hu)
    exact heq.trans_lt ((hN n hn).2 ⟨v,hv⟩)

end EmcsfAcExtension.Local
