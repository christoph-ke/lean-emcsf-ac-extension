module

public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Local.Calculus.C1ToSolution2

/-! # Off-axis integral equations of a primary uniform limit

Local uniform convergence is closed under the algebraic operations in the
reduced equations wherever the limiting denominators are nonzero. Compact
off-axis segments then give uniform convergence of every equation density.
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

private theorem pass_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {D : Set (ℝ × ℝ)} {Fn Gn : ℕ → (ℝ × ℝ) → E} {f g : (ℝ × ℝ) → E}
    (hF : ∀ p ∈ D, Tendsto (fun n => Fn n p) atTop (𝓝 (f p))) (hG : Expr D Gn g)
    {a b : ℝ} (hab : a ≤ b) {p : ℝ → ℝ × ℝ}
    (hp : MapsTo p (Icc a b) D) (cp : Continuous p)
    (hform : ∀ n, IntegralForm (Fn n ∘ p) (Gn n ∘ p) a b) :
    IntegralForm (f ∘ p) (g ∘ p) a b := by
  have hlocal := hG.lim.comp p hp cp.continuousOn
  have hunif := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).1 hlocal
  have hcont n : ContinuousOn (Gn n ∘ p) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact (hG.cn n).comp cp.continuousOn hp
  have hi := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn (μ := volume)
    (Eventually.of_forall hcont) (by simpa only [uIcc_of_le hab] using hunif)
  refine ⟨(hG.c.comp cp.continuousOn hp).intervalIntegrable_of_Icc hab, ?_⟩
  exact tendsto_nhds_unique ((hF _ (hp (right_mem_Icc.mpr hab))).sub
    (hF _ (hp (left_mem_Icc.mpr hab))))
      (hi.congr' (Eventually.of_forall fun n => (hform n).2.symm))

/-- Every outgoing and incoming off-axis integral equation passes to a
classical strong limit whose limiting denominators have the required signs.
The passage uses compact contained segments, including either outer boundary;
there is no estimate constant or near-axis integrability premise. -/
theorem StrongLimit.integral_equations_of_c1 {e T : ℝ} {Sn : ℕ → Fields} {S : Fields}
    (hT : 0 < T) (hc1 : ∀ n, IsC1Solution e (Sn n) (triangle 0 T))
    (hlim : StrongLimit e T Sn S)
    (hr : ∀ p ∈ triangle 0 T, p.1 < p.2 → 0 < S.r p.1 p.2)
    (hl : ∀ p ∈ triangle 0 T, 0 < S.lam p.1 p.2)
    (hn : ∀ p ∈ triangle 0 T, S.nu p.1 p.2 < 0)
    (hg : ∀ p ∈ triangle 0 T, 0 < 1 - S.mu p.1 p.2) :
    (∀ u v₁ v₂, u < v₁ → v₁ ≤ v₂ → outSeg u v₁ v₂ ⊆ triangle 0 T →
      IntegralForm (S.r u) (S.lam u) v₁ v₂ ∧ IntegralForm (S.nu u) (S.rUV u) v₁ v₂ ∧
      IntegralForm (S.m u) (S.mV u) v₁ v₂ ∧ IntegralForm (S.Q u) (S.QV e u) v₁ v₂ ∧
      IntegralForm (S.A u) (S.AV u) v₁ v₂ ∧ IntegralForm (S.phi u) (S.phiV u) v₁ v₂ ∧
      IntegralForm (S.xi u) (S.xiV e u) v₁ v₂) ∧
    (∀ u₁ u₂ v, u₁ ≤ u₂ → u₂ < v → inSeg u₁ u₂ v ⊆ triangle 0 T →
      IntegralForm (fun u => S.r u v) (fun u => S.nu u v) u₁ u₂ ∧
      IntegralForm (fun u => S.lam u v) (fun u => S.rUV u v) u₁ u₂ ∧
      IntegralForm (fun u => S.m u v) (fun u => S.mU u v) u₁ u₂ ∧
      IntegralForm (fun u => S.Q u v) (fun u => S.QU e u v) u₁ u₂ ∧
      IntegralForm (fun u => S.phi u v) (fun u => S.phiU e u v) u₁ u₂ ∧
      IntegralForm (fun u => S.theta u v) (fun u => S.thetaU e u v) u₁ u₂) := by
  let D := triangle 0 T ∩ {p : ℝ × ℝ | p.1 < p.2}
  have radius := Expr.of_uniform (fun n => (hc1 n).c1_r.continuousOn.mono (show D ⊆ triangle 0 T
      from inter_subset_left))
    (hlim.unif_r.mono (show D ⊆ triangle 0 T from inter_subset_left))
  have lam := Expr.of_uniform (fun n => (hc1 n).c1_lam.continuousOn.mono (show D ⊆ triangle 0 T from
      inter_subset_left))
    (hlim.unif_lam.mono (show D ⊆ triangle 0 T from inter_subset_left))
  have nu := Expr.of_uniform (fun n => (hc1 n).c1_nu.continuousOn.mono (show D ⊆ triangle 0 T from
      inter_subset_left))
    (hlim.unif_nu.mono (show D ⊆ triangle 0 T from inter_subset_left))
  have mass := Expr.of_uniform (fun n => (hc1 n).c1_m.continuousOn.mono (show D ⊆ triangle 0 T from
      inter_subset_left))
    (hlim.unif_m.mono (show D ⊆ triangle 0 T from inter_subset_left))
  have charge := Expr.of_uniform (fun n => (hc1 n).c1_Q.continuousOn.mono (show D ⊆ triangle 0 T
      from inter_subset_left))
    (hlim.unif_Q.mono (show D ⊆ triangle 0 T from inter_subset_left))
  have phi := Expr.of_uniform (fun n => (hc1 n).c1_phi.continuousOn.mono (show D ⊆ triangle 0 T from
      inter_subset_left))
    (hlim.unif_phi.mono (show D ⊆ triangle 0 T from inter_subset_left))
  have pot := Expr.of_uniform (fun n => (hc1 n).c1_A.continuousOn.mono (show D ⊆ triangle 0 T from
      inter_subset_left))
    (hlim.unif_A.mono (show D ⊆ triangle 0 T from inter_subset_left))
  have theta := Expr.of_uniform (fun n => (hc1 n).c1_theta.continuousOn.mono (show D ⊆ triangle 0 T
      from inter_subset_left))
    (hlim.unif_theta.mono (show D ⊆ triangle 0 T from inter_subset_left))
  have xi := Expr.of_uniform (fun n => (hc1 n).c1_xi.continuousOn.mono (show D ⊆ triangle 0 T from
      inter_subset_left))
    (hlim.unif_xi.mono (show D ⊆ triangle 0 T from inter_subset_left))
  have rn n p (hp : p ∈ D) := ((hc1 n).r_pos p hp.1 hp.2).ne'
  have r0 p (hp : p ∈ D) := (hr p hp.1 hp.2).ne'
  have ln n p (hp : p ∈ D) := ((hc1 n).lam_pos p hp.1).ne'
  have l0 p (hp : p ∈ D) := (hl p hp.1).ne'
  have nn n p (hp : p ∈ D) := ((hc1 n).nu_neg p hp.1).ne
  have n0 p (hp : p ∈ D) := (hn p hp.1).ne
  have mu : Expr D (fun n => Function.uncurry (Sn n).mu) (Function.uncurry S.mu) :=
    ((Expr.const D (2 : ℝ)).mul mass).div radius rn r0
  have g := (Expr.const D (1 : ℝ)).sub mu
  have gn n p (hp : p ∈ D) := ((hc1 n).one_sub_mu_pos p hp.1).ne'
  have g0 p (hp : p ∈ D) := (hg p hp.1).ne'
  have rsq := radius.mul radius
  have rsqn n p hp := mul_ne_zero (rn n p hp) (rn n p hp)
  have rsq0 p hp := mul_ne_zero (r0 p hp) (r0 p hp)
  have qsq := charge.mul charge
  have z := ((nu.mul lam).div radius rn r0).mul
    ((mu.sub (qsq.div rsq rsqn rsq0)).div g gn g0)
  have rc := radius.map Complex.isometry_ofReal.uniformContinuous
  have lc := lam.map Complex.isometry_ofReal.uniformContinuous
  have nc := nu.map Complex.isometry_ofReal.uniformContinuous
  have qc := charge.map Complex.isometry_ofReal.uniformContinuous
  have ac := pot.map Complex.isometry_ofReal.uniformContinuous
  have gc := g.map Complex.isometry_ofReal.uniformContinuous
  have rcn n p hp := Complex.ofReal_ne_zero.mpr (rn n p hp)
  have rc0 p hp := Complex.ofReal_ne_zero.mpr (r0 p hp)
  have wave := (((((Expr.const D (I * (e : ℂ))).mul qc).mul phi).mul nc).mul lc).div
    (gc.mul rc) (fun n p hp => mul_ne_zero (Complex.ofReal_ne_zero.mpr (gn n p hp)) (rcn n p hp))
    (fun p hp => mul_ne_zero (Complex.ofReal_ne_zero.mpr (g0 p hp)) (rc0 p hp))
  have mV := (g.mul ((theta.map uniformContinuous_norm).mul (theta.map uniformContinuous_norm))).div
    ((Expr.const D (2 : ℝ)).mul lam) (fun n p hp => mul_ne_zero (by norm_num) (ln n p hp))
    (fun p hp => mul_ne_zero (by norm_num) (l0 p hp)) |>.add
      ((qsq.mul lam).div ((Expr.const D (2 : ℝ)).mul rsq)
        (fun n p hp => mul_ne_zero (by norm_num) (rsqn n p hp))
        (fun p hp => mul_ne_zero (by norm_num) (rsq0 p hp)))
  have mU := (g.mul ((xi.map uniformContinuous_norm).mul (xi.map uniformContinuous_norm))).div
    ((Expr.const D (2 : ℝ)).mul nu) (fun n p hp => mul_ne_zero (by norm_num) (nn n p hp))
    (fun p hp => mul_ne_zero (by norm_num) (n0 p hp)) |>.add
      ((qsq.mul nu).div ((Expr.const D (2 : ℝ)).mul rsq)
        (fun n p hp => mul_ne_zero (by norm_num) (rsqn n p hp))
        (fun p hp => mul_ne_zero (by norm_num) (rsq0 p hp)))
  have QV := ((Expr.const D (-e)).mul radius).mul
    (((phi.map Complex.isometry_conj.uniformContinuous).mul theta).map
        Complex.imCLM.uniformContinuous)
  have QU := ((Expr.const D e).mul radius).mul
    (((phi.map Complex.isometry_conj.uniformContinuous).mul xi).map Complex.imCLM.uniformContinuous)
  have AV := ((((Expr.const D (2 : ℝ)).mul nu).mul lam).mul charge).div (g.mul rsq)
    (fun n p hp => mul_ne_zero (gn n p hp) (rsqn n p hp))
    (fun p hp => mul_ne_zero (g0 p hp) (rsq0 p hp))
  have phiV := theta.div rc rcn rc0
  have phiU := (xi.div rc rcn rc0).sub (((Expr.const D (I * (e : ℂ))).mul ac).mul phi)
  have xiV := ((Expr.const D (0 : ℂ)).sub ((nc.mul theta).div rc rcn rc0)).add wave
  have thetaU := (((Expr.const D (0 : ℂ)).sub
    (((Expr.const D (I * (e : ℂ))).mul ac).mul theta)).sub
      ((lc.mul xi).div rc rcn rc0)).sub wave
  have z' : Expr D (fun n => Function.uncurry (Sn n).rUV) (Function.uncurry S.rUV) := by
    simpa only [Fields.rUV, Function.uncurry_def, pow_two] using z
  have mV' : Expr D (fun n => Function.uncurry (Sn n).mV) (Function.uncurry S.mV) := by
    simpa only [Fields.mV, Function.uncurry_def, pow_two] using mV
  have mU' : Expr D (fun n => Function.uncurry (Sn n).mU) (Function.uncurry S.mU) := by
    simpa only [Fields.mU, Function.uncurry_def, pow_two] using mU
  have QV' : Expr D (fun n => Function.uncurry ((Sn n).QV e)) (Function.uncurry (S.QV e)) := by
    simpa only [Fields.QV, Function.uncurry_def, Complex.imCLM_apply, neg_mul] using! QV
  have QU' : Expr D (fun n => Function.uncurry ((Sn n).QU e)) (Function.uncurry (S.QU e)) := by
    simpa only [Fields.QU, Function.uncurry_def, Complex.imCLM_apply] using! QU
  have AV' : Expr D (fun n => Function.uncurry (Sn n).AV) (Function.uncurry S.AV) := by
    simpa only [Fields.AV, Function.uncurry_def, pow_two] using AV
  have phiV' : Expr D (fun n => Function.uncurry (Sn n).phiV) (Function.uncurry S.phiV) := by
    simpa only [Fields.phiV, Function.uncurry_def] using phiV
  have phiU' : Expr D (fun n => Function.uncurry ((Sn n).phiU e)) (Function.uncurry (S.phiU e)) :=
      by
    simpa only [Fields.phiU, Function.uncurry_def] using phiU
  have xiV' : Expr D (fun n => Function.uncurry ((Sn n).xiV e)) (Function.uncurry (S.xiV e)) := by
    simpa only [Fields.xiV, Fields.waveSource, Function.uncurry_def, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_one, zero_sub] using xiV
  have thetaU' : Expr D (fun n => Function.uncurry ((Sn n).thetaU e))
      (Function.uncurry (S.thetaU e)) := by
    simpa only [Fields.thetaU, Fields.waveSource, Function.uncurry_def, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_one, zero_sub] using thetaU
  constructor
  · intro u a b hua hab hseg
    have hp : MapsTo (fun x => (u, x)) (Icc a b) D :=
      fun x hx => ⟨hseg ⟨rfl, hx.1, hx.2⟩, hua.trans_le hx.1⟩
    have pass {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
        {Fn Gn : ℕ → (ℝ × ℝ) → E} {f g : (ℝ × ℝ) → E}
        (hF : Expr D Fn f) (hG : Expr D Gn g)
        (he : ∀ n, IntegralForm (fun x => Fn n (u, x)) (fun x => Gn n (u, x)) a b) :
        IntegralForm (fun x => f (u, x)) (fun x => g (u, x)) a b :=
      pass_integral (fun _ hx => hF.lim.tendsto_at hx) hG hab hp
        (continuous_const.prodMk continuous_id) he
    have hs n := (hc1 n).toIsSolution hT |>.eq_out u a b hua hab hseg
    exact ⟨pass radius lam (fun n => (hs n).1), pass nu z' (fun n => (hs n).2.1),
      pass mass mV' (fun n => (hs n).2.2.1), pass charge QV' (fun n => (hs n).2.2.2.1),
      pass pot AV' (fun n => (hs n).2.2.2.2.1), pass phi phiV' (fun n => (hs n).2.2.2.2.2.1),
      pass xi xiV' (fun n => (hs n).2.2.2.2.2.2)⟩
  · intro a b v hab hbv hseg
    have hp : MapsTo (fun x => (x, v)) (Icc a b) D :=
      fun x hx => ⟨hseg ⟨hx.1, hx.2, rfl⟩, hx.2.trans_lt hbv⟩
    have pass {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
        {Fn Gn : ℕ → (ℝ × ℝ) → E} {f g : (ℝ × ℝ) → E}
        (hF : Expr D Fn f) (hG : Expr D Gn g)
        (he : ∀ n, IntegralForm (fun x => Fn n (x, v)) (fun x => Gn n (x, v)) a b) :
        IntegralForm (fun x => f (x, v)) (fun x => g (x, v)) a b :=
      pass_integral (fun _ hx => hF.lim.tendsto_at hx) hG hab hp
        (continuous_id.prodMk continuous_const) he
    have hs n := (hc1 n).toIsSolution hT |>.eq_in a b v hab hbv hseg
    exact ⟨pass radius nu (fun n => (hs n).1), pass lam z' (fun n => (hs n).2.1),
      pass mass mU' (fun n => (hs n).2.2.1), pass charge QU' (fun n => (hs n).2.2.2.1),
      pass phi phiU' (fun n => (hs n).2.2.2.2.1), pass theta thetaU' (fun n => (hs n).2.2.2.2.2)⟩

end EmcsfAcExtension.Local
