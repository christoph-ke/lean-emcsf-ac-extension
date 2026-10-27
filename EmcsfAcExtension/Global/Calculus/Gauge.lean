module

public import EmcsfAcExtension.Global.Calculus.Sections
public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Relabel
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Infra.AC.Quotient
import EmcsfAcExtension.Infra.AC.Variation

/-! # Weak gauge calculus and parallel variation

The potential equation supplies the weak commutator by the sectional AC
product rule. Parallel transport gives covariant variation as ordinary
variation. The residual gauge on each proper cylinder is constructed from
its own potential trace (`charged_SF_new_version.tex:L650–L699`; internal project record).
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ContDiff

namespace EmcsfAcExtension.Global.Calculus

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [internal]
The weak charged commutator on an outgoing section, expressed as the AC
product rule against a test field. With a test function vanishing at the
endpoints the right endpoint difference is zero. After the commuting mixed
test derivatives cancel, the multiplier is `2ie(-ν)λQ/((1-μ)r²)`.
Only AC of the field and test section is required. -/
theorem main_gauge (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    {f ψ : ℝ → ℂ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hψ : AbsolutelyContinuousOnInterval ψ a b) :
    IntegralForm (fun v => I * e * S.A u v * f v * ψ v)
      (fun v => I * e * S.A u v * (deriv f v * ψ v + f v * deriv ψ v) -
        2 * I * e * (-S.nu u v) * S.lam u v * S.Q u v /
          ((1 - S.mu u v) * S.r u v ^ 2) * f v * ψ v) a b := by
  have hA := (Local.IsSolution.out_section hS hua hab hs).2.2.2.2.1
  have hac := (hA.1.ofReal.const_smul (I * e)).mul_normed_ring hf |>.mul_normed_ring hψ
  simp only [smul_eq_mul] at hac
  apply integralForm_of_ac_of_ae_deriv_eq hac
  rw [uIcc_of_le hab]
  filter_upwards [hA.2,
    (ae_restrict_iff' measurableSet_Icc).2 (by
      simpa only [uIcc_of_le hab] using hf.ae_differentiableAt_of_mem_uIcc),
    (ae_restrict_iff' measurableSet_Icc).2 (by
      simpa only [uIcc_of_le hab] using hψ.ae_differentiableAt_of_mem_uIcc)]
      with v hAv hfv hψv
  have hd := ((hAv.ofReal_comp.const_mul (I * e)).mul hfv.hasDerivAt).mul hψv.hasDerivAt
  have hd' : HasDerivAt (fun x => I * e * (S.A u x : ℂ) * f x * ψ x)
      ((I * e * S.AV u v * f v + I * e * S.A u v * deriv f v) * ψ v +
        I * e * S.A u v * f v * deriv ψ v) v := by
    simpa only [Pi.mul_apply] using! hd
  rw [hd'.deriv]
  dsimp [Fields.AV]
  push_cast
  ring

/-- [internal]
Ordinary mixed derivatives of a smooth test function commute. Only the
test function is differentiated twice (charged_SF_new_version.tex:L650–658). -/
theorem smooth_test_mixed_commute {ψ : ℝ × ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ)
    (p : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ ψ) p (1, 0) (0, 1) =
      fderiv ℝ (fderiv ℝ ψ) p (0, 1) (1, 0) :=
  (hψ.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

/-- [internal]
Expanded weak action of `[Dᵤ,Dᵥ]f - 2iq(-ν)λQ f/((1-μ)r²)` on
a test function, after integration by parts in the two ordinary mixed
derivatives (charged_SF_new_version.tex:L650–658; internal project record). The charge `q` belongs
to the field being tested; no mixed derivative of that field is used. -/
@[expose] noncomputable def commutatorTestDensity (q : ℝ) (S : Fields)
    (f : ℝ → ℝ → ℂ) (ψ : ℝ × ℝ → ℂ) (u v : ℝ) : ℂ :=
  f u v * (fderiv ℝ (fderiv ℝ ψ) (u, v) (1, 0) (0, 1) -
    fderiv ℝ (fderiv ℝ ψ) (u, v) (0, 1) (1, 0)) +
  I * q * S.A u v * (deriv (f u) v * ψ (u, v) +
    f u v * deriv (fun w => ψ (u, w)) v) -
  2 * I * q * (-S.nu u v) * S.lam u v * S.Q u v /
    ((1 - S.mu u v) * S.r u v ^ 2) * f u v * ψ (u, v)

/-- [internal]
Transpose test for `DᵤDᵥ`: the outgoing derivative of the potential
test product is expanded using the frozen potential equation. This is a
test operator and differentiates no rough field (charged_SF_new_version.tex:L650–658). -/
@[expose] noncomputable def weakDuDvTest (q : ℝ) (S : Fields)
    (ψ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ (fderiv ℝ ψ) p (1, 0) (0, 1) - I * q *
    (S.AV p.1 p.2 * ψ p + S.A p.1 p.2 * fderiv ℝ ψ p (0, 1))

/-- [internal]
Transpose test for `DᵥDᵤ` in the gauge `Aᵥ=0`. Its connection term
requires only the first outgoing test derivative (charged_SF_new_version.tex:L650–658). -/
@[expose] noncomputable def weakDvDuTest (q : ℝ) (S : Fields)
    (ψ : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ (fderiv ℝ ψ) p (0, 1) (1, 0) -
    I * q * S.A p.1 p.2 * fderiv ℝ ψ p (0, 1)

private theorem rectangle_integrable {F : ℝ × ℝ → ℂ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hF : ContinuousOn F (Icc a b ×ˢ Icc c d)) :
    (∀ u ∈ Icc a b, IntervalIntegrable (fun v => F (u, v)) volume c d) ∧
      IntervalIntegrable (fun u => ∫ v in c..d, F (u, v)) volume a b := by
  let P (p : ℝ × ℝ) := (min (max a p.1) b, min (max c p.2) d)
  have cP : Continuous P := by dsimp [P]; fun_prop
  have hP (p : ℝ × ℝ) : P p ∈ Icc a b ×ˢ Icc c d :=
    ⟨⟨le_min (le_max_left _ _) hab, min_le_right _ _⟩,
      ⟨le_min (le_max_left _ _) hcd, min_le_right _ _⟩⟩
  have hfix (p : ℝ × ℝ) (hp : p ∈ Icc a b ×ˢ Icc c d) : P p = p := by
    dsimp [P]; rw [max_eq_right hp.1.1, min_eq_left hp.1.2,
      max_eq_right hp.2.1, min_eq_left hp.2.2]
  have cG : Continuous (fun p => F (P p)) := hF.comp_continuous cP hP
  have cI : Continuous (fun u => ∫ v in c..d, F (P (u, v))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous cG continuous_const
  refine ⟨fun u hu => (hF.comp (continuousOn_const.prodMk continuousOn_id)
    (fun v hv => ⟨hu, hv⟩)).intervalIntegrable_of_Icc hcd, ?_⟩
  apply (cI.continuousOn.congr ?_).intervalIntegrable_of_Icc hab
  intro u hu
  apply intervalIntegral.integral_congr
  intro v hv
  change F (u, v) = F (P (u, v))
  rw [hfix (u, v) ⟨hu, by simpa only [uIcc_of_le hcd] using hv⟩]

/-- [node eq:main-gauge]
The distributional rectangle identity `[Dᵤ,Dᵥ]f =
2ie(-ν)λQ f/((1-μ)r²)` tested against an interior smooth test
(charged_SF_new_version.tex:L650–658). Both transposed operator pairings are proved
integrable before subtraction. A continuous rough field suffices; only
the test has mixed derivatives. The potential product rule is
`main_gauge`, and the ordinary mixed test derivatives commute by
`smooth_test_mixed_commute`. There are no constants. -/
theorem main_gauge_weak_rectangle (hS : IsSolution e S D) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hbc : b < c)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D) {f : ℝ → ℝ → ℂ} {ψ : ℝ × ℝ → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc c d))
    (hψ : ContDiff ℝ 2 ψ) (_hsupp : tsupport ψ ⊆ Ioo a b ×ˢ Ioo c d) :
    (∀ u ∈ Icc a b, IntervalIntegrable (fun v => f u v * weakDuDvTest e S ψ (u, v))
      volume c d ∧ IntervalIntegrable (fun v => f u v * weakDvDuTest e S ψ (u, v))
      volume c d) ∧
    IntervalIntegrable (fun u => ∫ v in c..d, f u v * weakDuDvTest e S ψ (u, v)) volume a b ∧
    IntervalIntegrable (fun u => ∫ v in c..d, f u v * weakDvDuTest e S ψ (u, v)) volume a b ∧
    (∫ u in a..b, ∫ v in c..d, f u v * weakDuDvTest e S ψ (u, v)) -
      (∫ u in a..b, ∫ v in c..d, f u v * weakDvDuTest e S ψ (u, v)) =
      ∫ u in a..b, ∫ v in c..d,
        2 * I * e * (-S.nu u v) * S.lam u v * S.Q u v /
          ((1 - S.mu u v) * S.r u v ^ 2) * f u v * ψ (u, v) := by
  let K := Icc a b ×ˢ Icc c d
  have cr := hS.cont_r.mono hrect
  have hr (p : ℝ × ℝ) (hp : p ∈ K) :=
    hS.r_pos p (hrect hp) (hp.1.2.trans_lt (hbc.trans_le hp.2.1))
  have cg : ContinuousOn (fun p : ℝ × ℝ => 1 - S.mu p.1 p.2) K := by
    exact continuousOn_const.sub (((hS.cont_m.mono hrect).const_mul 2).div cr
      (fun p hp => (hr p hp).ne'))
  have cAV : ContinuousOn (fun p : ℝ × ℝ => (S.AV p.1 p.2 : ℂ)) K := by
    apply Complex.continuous_ofReal.comp_continuousOn
    exact ((((hS.cont_nu.mono hrect).const_mul 2).mul
      (hS.cont_lam.mono hrect)).mul (hS.cont_Q.mono hrect)).div (cg.mul (cr.pow 2))
        (fun p hp => mul_ne_zero (hS.one_sub_mu_pos p (hrect hp)).ne'
          (pow_ne_zero 2 (hr p hp).ne'))
  have cA : ContinuousOn (fun p : ℝ × ℝ => (S.A p.1 p.2 : ℂ)) K :=
    Complex.continuous_ofReal.comp_continuousOn (hS.cont_A.mono hrect)
  have cD := hψ.continuous_fderiv (by norm_num)
  have cDD := ((contDiff_succ_iff_fderiv (n := 1)).mp hψ).2.2.continuous_fderiv (by norm_num)
  have cT₁ : ContinuousOn (weakDuDvTest e S ψ) K :=
    ((cDD.clm_apply continuous_const).clm_apply continuous_const).continuousOn.sub
      (continuousOn_const.mul ((cAV.mul hψ.continuous.continuousOn).add
        (cA.mul (cD.clm_apply continuous_const).continuousOn)))
  have cT₂ : ContinuousOn (weakDvDuTest e S ψ) K :=
    ((cDD.clm_apply continuous_const).clm_apply continuous_const).continuousOn.sub
      (((continuousOn_const.mul continuousOn_const).mul cA).mul
        (cD.clm_apply continuous_const).continuousOn)
  obtain ⟨hi₁, ho₁⟩ := rectangle_integrable hab hcd (hf.mul cT₁)
  obtain ⟨hi₂, ho₂⟩ := rectangle_integrable hab hcd (hf.mul cT₂)
  dsimp only [Pi.mul_apply, Function.uncurry] at hi₁ ho₁ hi₂ ho₂
  refine ⟨fun u hu => ⟨hi₁ u hu, hi₂ u hu⟩, ho₁, ho₂, ?_⟩
  rw [← intervalIntegral.integral_sub ho₁ ho₂]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu' : u ∈ Icc a b := by simpa only [uIcc_of_le hab] using hu
  dsimp only
  rw [← intervalIntegral.integral_sub (hi₁ u hu') (hi₂ u hu')]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only [weakDuDvTest, weakDvDuTest]
  rw [smooth_test_mixed_commute hψ]
  dsimp only [Fields.AV]
  push_cast
  ring

/-- [node eq:main-gauge]
For a charge-zero scalar, the connection term in the incoming derivative
vanishes and the weak commutator is zero on every rectangle
(charged_SF_new_version.tex:L650–658). The background solution may carry arbitrary
charge; smoothness is required only of the test. There are no constants. -/
theorem main_gauge_charge_zero (S : Fields) (f : ℝ → ℝ → ℂ)
    {ψ : ℝ × ℝ → ℂ} (hψ : ContDiff ℝ 2 ψ) (a b c d : ℝ) :
    (∀ u v, deriv (fun x => f x v) u + I * (0:ℝ) * S.A u v * f u v =
      deriv (fun x => f x v) u) ∧
    (∀ p, weakDuDvTest 0 S ψ p = weakDvDuTest 0 S ψ p) ∧
    (∀ u v, commutatorTestDensity 0 S f ψ u v = 0) ∧
    (∫ u in a..b, ∫ v in c..d, commutatorTestDensity 0 S f ψ u v) = 0 := by
  have hz (u v : ℝ) : commutatorTestDensity 0 S f ψ u v = 0 := by
    simp [commutatorTestDensity, smooth_test_mixed_commute hψ]
  exact ⟨by intros; simp, by
    intro p
    simp [weakDuDvTest, weakDvDuTest, smooth_test_mixed_commute hψ],
    hz, by simp only [hz, intervalIntegral.integral_zero]⟩

/-- [internal] The unit parallel multiplier has norm one for every real
potential and real coordinate labels; no regularity hypothesis is needed. -/
theorem norm_curveParallel (e : ℝ) (S : Fields) (f : ℝ → ℝ → ℂ)
    (U V : ℝ → ℝ) (s x : ℝ) :
    ‖curveParallel e S f U V s x‖ = ‖f (U x) (V x)‖ := by
  simp [curveParallel_def, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- [internal] Parallel transport preserves AC of a trace whenever the
pulled-back connection is integrable. -/
theorem curveParallel_ac {f : ℝ → ℝ → ℂ} {U V : ℝ → ℝ} {s t : ℝ}
    (hf : AbsolutelyContinuousOnInterval (fun x => f (U x) (V x)) s t)
    (hA : IntervalIntegrable (fun x => S.A (U x) (V x) * deriv U x) volume s t) :
    AbsolutelyContinuousOnInterval (curveParallel e S f U V s) s t := by
  have hp := (hA.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).const_mul e
  apply (hp.unit_phase.mul_normed_ring hf).congr
  intro x hx
  simp only [curveParallel_def, Complex.ofReal_mul]
  congr 2
  ring

/-- [node sec:charged-equations#parallel-frame-variation]
The derivative of the parallel representative is its unit multiplier times
the covariant trace derivative a.e. This uses only a one-dimensional AC trace
and the integrable pulled-back connection, not an ambient derivative trace. -/
theorem curveParallel_ae_hasDerivAt {f : ℝ → ℝ → ℂ} {U V : ℝ → ℝ} {s t : ℝ}
    (hf : AbsolutelyContinuousOnInterval (fun x => f (U x) (V x)) s t)
    (hA : IntervalIntegrable (fun x => S.A (U x) (V x) * deriv U x) volume s t) :
    ∀ᵐ x, x ∈ uIcc s t → HasDerivAt (curveParallel e S f U V s)
      (Complex.exp (I * e * ∫ y in s..x, S.A (U y) (V y) * deriv U y) *
        (deriv (fun y => f (U y) (V y)) x +
          I * e * (S.A (U x) (V x) * deriv U x) * f (U x) (V x))) x := by
  filter_upwards [hA.ae_hasDerivAt_integral, hf.ae_differentiableAt_of_mem_uIcc]
    with x hAx hfx hx
  have hd := (((hAx hx s left_mem_uIcc).ofReal_comp.const_mul (I * e)).cexp).mul
    (hfx hx).hasDerivAt
  convert hd using 1 <;> first | rfl | (push_cast; ring)

/-- [node sec:charged-equations#covariant-variation]
For an AC trace, the adopted parallel-frame definition equals the source's
integral of the covariant speed. No constants enter this exact identity. -/
theorem curveCovVar_eq_integral {f : ℝ → ℝ → ℂ} {U V : ℝ → ℝ} {s t : ℝ}
    (hst : s ≤ t)
    (hf : AbsolutelyContinuousOnInterval (fun x => f (U x) (V x)) s t)
    (hA : IntervalIntegrable (fun x => S.A (U x) (V x) * deriv U x) volume s t) :
    curveCovVar e S f U V s t =
      ENNReal.ofReal (∫ x in s..t,
        ‖deriv (fun y => f (U y) (V y)) x +
          I * e * (S.A (U x) (V x) * deriv U x) * f (U x) (V x)‖) := by
  rw [curveCovVar, (curveParallel_ac hf hA).eVariationOn_eq_integral_norm_deriv hst]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [curveParallel_ae_hasDerivAt hf hA] with x hx hmem
  rw [(hx (uIoc_subset_uIcc hmem)).deriv, norm_mul]
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- [internal] A constant unit multiplier preserves every partition sum, and
therefore total variation, including for fields of infinite variation. -/
theorem eVariationOn_unit_mul {α : Type*} [LinearOrder α]
    (z : ℂ) (hz : ‖z‖ = 1) (f : α → ℂ) (s : Set α) :
    eVariationOn (fun x => z * f x) s = eVariationOn f s := by
  have he : ‖z‖ₑ = 1 := by rw [← ofReal_norm, hz, ENNReal.ofReal_one]
  unfold eVariationOn
  congr 1
  funext p
  apply Finset.sum_congr rfl
  intro i hi
  simp only [edist_eq_enorm_sub, ← mul_sub, enorm_mul, he, one_mul]

/-- [node sec:charged-equations#parallel-frame-variation]
Outgoing parallel variation is ordinary outgoing variation in `A_v = 0`. -/
theorem curveCovVar_out (e : ℝ) (S : Fields) (f : ℝ → ℝ → ℂ) (u s t : ℝ) :
    curveCovVar e S f (fun _ => u) id s t = eVariationOn (f u) (Icc s t) := by
  rw [curveCovVar_def]
  congr 1
  funext x
  rw [curveParallel_def]
  simp

/-- [node sec:charged-equations#parallel-frame-variation]
A residual incoming gauge preserves outgoing variation of any charged field.
The datum on each row is multiplied by one constant unit factor. -/
theorem outgoing_variation_gauge (e : ℝ) (χ : ℝ → ℝ)
    (f : ℝ → ℝ → ℂ) (u s t : ℝ) :
    eVariationOn (fun v => Complex.exp (I * e * χ u) * f u v) (Icc s t) =
      eVariationOn (f u) (Icc s t) := by
  apply eVariationOn_unit_mul
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- [internal] A residual gauge changes a curve's parallel representative
by the single unit phase on its initial row. Curve coordinates and the gauge
are C¹; the charged field itself has no additional regularity premise. -/
theorem curveParallel_gauge_eq {χ U V : ℝ → ℝ} {f : ℝ → ℝ → ℂ} {s t : ℝ}
    (hst : s ≤ t) (hχ : ContDiff ℝ 1 χ) (hU : ContDiffOn ℝ 1 U (uIcc s t))
    (hA : IntervalIntegrable (fun x => S.A (U x) (V x) * deriv U x) volume s t) :
    ∀ x ∈ Icc s t,
      curveParallel e (gaugeFields e S χ)
        (fun u v => Complex.exp (I * e * χ u) * f u v) U V s x =
      Complex.exp (I * e * χ (U s)) * curveParallel e S f U V s x := by
  have hUac := hU.absolutelyContinuousOnInterval
  have hχU := (hχ.fun_comp_contDiffOn hU).absolutelyContinuousOnInterval
  have hd : ∀ᵐ x, x ∈ uIcc s t → HasDerivAt (fun y => χ (U y))
      (deriv χ (U x) * deriv U x) x := by
    filter_upwards [hUac.ae_differentiableAt] with x hx hxm
    exact (hχ.differentiable (by norm_num) (U x)).hasDerivAt.comp x (hx hxm).hasDerivAt
  have hq := integralForm_of_ac_of_ae_deriv_eq hχU (by
    apply (ae_restrict_iff' measurableSet_uIcc).2
    exact hd.mono fun x hx hxm => (hx hxm).deriv)
  intro x hx
  have hx' : x ∈ uIcc s t := by rwa [uIcc_of_le hst]
  have hsub := uIcc_subset_uIcc left_mem_uIcc hx'
  have hiχ := (hχU.mono hsub).integral_eq_sub_of_ae_hasDerivAt_normed
    (hq.1.mono_set hsub) (hd.mono fun y hy hym => hy (hsub hym))
  rw [curveParallel_def, curveParallel_def]
  simp only [gaugeFields, sub_mul]
  rw [intervalIntegral.integral_sub (hA.mono_set hsub) (hq.1.mono_set hsub), hiχ]
  rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- [node sec:charged-equations#parallel-frame-variation]
Covariant variation is invariant under residual incoming gauges on proper
C¹ curve segments. This follows from equality of parallel representatives
up to one constant unit multiplier, and allows infinite total variation. -/
theorem curveCovVar_gauge {χ U V : ℝ → ℝ} {f : ℝ → ℝ → ℂ} {s t : ℝ}
    (hst : s ≤ t) (hχ : ContDiff ℝ 1 χ) (hU : ContDiffOn ℝ 1 U (uIcc s t))
    (hA : IntervalIntegrable (fun x => S.A (U x) (V x) * deriv U x) volume s t) :
    curveCovVar e (gaugeFields e S χ)
      (fun u v => Complex.exp (I * e * χ u) * f u v) U V s t =
      curveCovVar e S f U V s t := by
  rw [curveCovVar_def, curveCovVar_def]
  calc
    _ = eVariationOn
        (fun x => Complex.exp (I * e * χ (U s)) * curveParallel e S f U V s x)
        (Icc s t) := eVariationOn.eq_of_eqOn (fun x hx => curveParallel_gauge_eq hst hχ hU hA x hx)
    _ = _ := eVariationOn_unit_mul _ (by
      simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]) _ _

/-- [node sec:charged-equations#cylinder-parallel-gauge]
On each proper cylinder graph, a residual gauge has zero pulled-back
potential. The construction extends the continuous potential trace by
clamping, then takes its primitive; it is globally C¹ and is normalized on
the initial row. Moduli and outgoing variation are preserved by the preceding
unit-phase identities. No simultaneous gauge on different cylinders is used. -/
theorem cylinder_parallel_gauge (hS : IsSolution e S D) {vb : ℝ → ℝ} {s t : ℝ}
    (hst : s ≤ t) (hvb : ContinuousOn vb (Icc s t))
    (hmem : ∀ u ∈ Icc s t, (u, vb u) ∈ D) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ 1 χ ∧ χ s = 0 ∧
      (∀ u ∈ Icc s t, deriv χ u = S.A u (vb u)) ∧
      (∀ u ∈ Icc s t, (gaugeFields e S χ).A u (vb u) = 0) := by
  let π : ℝ → ℝ := fun x => min (max s x) t
  have hπ : Continuous π := (continuous_const.max continuous_id).min continuous_const
  have hmπ (x : ℝ) : π x ∈ Icc s t :=
    ⟨le_min (le_max_left _ _) hst, min_le_right _ _⟩
  let q : ℝ → ℝ := fun x => S.A (π x) (vb (π x))
  have cq : Continuous q := hS.cont_A.comp_continuous
    (hπ.prodMk (hvb.comp_continuous hπ hmπ)) (fun x => hmem _ (hmπ x))
  let χ : ℝ → ℝ := fun x => ∫ y in s..x, q y
  have hd (x : ℝ) : HasDerivAt χ (q x) x :=
    intervalIntegral.integral_hasDerivAt_right (cq.intervalIntegrable s x)
      cq.stronglyMeasurable.stronglyMeasurableAtFilter cq.continuousAt
  have hχ : ContDiff ℝ 1 χ := contDiff_one_iff_deriv.mpr
    ⟨fun x => (hd x).differentiableAt, by simpa only [funext (fun x => (hd x).deriv)] using cq⟩
  have he (u : ℝ) (hu : u ∈ Icc s t) : deriv χ u = S.A u (vb u) := by
    rw [(hd u).deriv]
    simp only [q, π, max_eq_right hu.1, min_eq_left hu.2]
  exact ⟨χ, hχ, by simp [χ], he, fun u hu => by simp [gaugeFields, he u hu]⟩

end EmcsfAcExtension.Global.Calculus
