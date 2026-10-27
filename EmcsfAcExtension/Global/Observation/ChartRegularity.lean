module

public import EmcsfAcExtension.Global.Api.Definitions

/-! # Continuity on actual observation charts

Only original field continuity and C¹ chart/gauge regularity are used.
The chart diagonal may be a positive-radius cylinder; there is no
transformed regular-axis assertion. Source: charged_SF_new_version.tex:L1975–2034.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
All nine transported fields are continuous on any actual comparison set.
Its defining map takes values in the original development. Derivatives
of the positive C¹ chart maps and the C¹ residual gauge are continuous;
no second derivatives, field differentiability or comparison estimate
are hypotheses. There are no constants. -/
theorem chart_fields_continuousOn {e ui s : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) (U V : ℝ → ℝ)
    (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
    (K : Set (ℝ × ℝ))
    (hsource : ∀ p ∈ K, (s * U p.1, s * V p.2) ∈ origDomain ui) :
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
    ContinuousOn (Function.uncurry P.r) K ∧ ContinuousOn (Function.uncurry P.nu) K ∧
    ContinuousOn (Function.uncurry P.lam) K ∧ ContinuousOn (Function.uncurry P.A) K ∧
    ContinuousOn (Function.uncurry P.phi) K ∧ ContinuousOn (Function.uncurry P.theta) K ∧
    ContinuousOn (Function.uncurry P.m) K ∧ ContinuousOn (Function.uncurry P.Q) K ∧
    ContinuousOn (Function.uncurry P.xi) K := by
  have cU : Continuous (fun p : ℝ × ℝ => s * U p.1) :=
    continuous_const.mul (hU.continuous.comp continuous_fst)
  have cV : Continuous (fun p : ℝ × ℝ => s * V p.2) :=
    continuous_const.mul (hV.continuous.comp continuous_snd)
  have cmap : Continuous (fun p : ℝ × ℝ => (s * U p.1, s * V p.2)) := cU.prodMk cV
  have cr := hS.cont_r.comp cmap.continuousOn hsource
  have cn := hS.cont_nu.comp cmap.continuousOn hsource
  have cl := hS.cont_lam.comp cmap.continuousOn hsource
  have ca := hS.cont_A.comp cmap.continuousOn hsource
  have cp := hS.cont_phi.comp cmap.continuousOn hsource
  have ct := hS.cont_theta.comp cmap.continuousOn hsource
  have cm := hS.cont_m.comp cmap.continuousOn hsource
  have cq := hS.cont_Q.comp cmap.continuousOn hsource
  have cx := hS.cont_xi.comp cmap.continuousOn hsource
  have cdU : Continuous (fun p : ℝ × ℝ => deriv U p.1) :=
    (contDiff_one_iff_deriv.mp hU).2.comp continuous_fst
  have cdV : Continuous (fun p : ℝ × ℝ => deriv V p.2) :=
    (contDiff_one_iff_deriv.mp hV).2.comp continuous_snd
  have cdχ : Continuous (fun p : ℝ × ℝ => deriv χ (s * U p.1)) :=
    (contDiff_one_iff_deriv.mp hχ).2.comp cU
  have cphase : Continuous (fun p : ℝ × ℝ => Complex.exp (I * e * χ (s * U p.1))) := by
    exact (continuous_const.mul (Complex.continuous_ofReal.comp (hχ.continuous.comp cU))).cexp
  dsimp only [nullPullback, rescaleFields, gaugeFields]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Function.comp_def, Function.uncurry_apply_pair] using! cr.div_const s
  · simpa only [Function.comp_def, Function.uncurry_apply_pair] using! cdU.continuousOn.mul cn
  · simpa only [Function.comp_def, Function.uncurry_apply_pair] using! cdV.continuousOn.mul cl
  · simpa only [Function.comp_def, Function.uncurry_apply_pair] using!
      cdU.continuousOn.mul (ca.sub cdχ.continuousOn)
  · simpa only [Function.comp_def, Function.uncurry_apply_pair] using! cphase.continuousOn.mul cp
  · simpa only [Function.comp_def, Function.uncurry_apply_pair] using!
      (Complex.continuous_ofReal.comp cdV).continuousOn.mul (cphase.continuousOn.mul ct)
  · simpa only [Function.comp_def, Function.uncurry_apply_pair] using! cm.div_const s
  · simpa only [Function.comp_def, Function.uncurry_apply_pair] using! cq.div_const s
  · simpa only [Function.comp_def, Function.uncurry_apply_pair] using!
      (Complex.continuous_ofReal.comp cdU).continuousOn.mul (cphase.continuousOn.mul cx)

end EmcsfAcExtension.Global.Observation
