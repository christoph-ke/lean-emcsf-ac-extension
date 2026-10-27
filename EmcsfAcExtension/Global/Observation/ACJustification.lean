module

public import EmcsfAcExtension.Global.Observation.ChartEquations
public import EmcsfAcExtension.Global.Observation.BoundaryFailure
public import EmcsfAcExtension.Global.Observation.NullTransport

/-! # AC justification of the actual comparison operations

The original frozen solution supplies the boundary representatives, finite
flux and variation. The chosen C¹ gauge and null chart transport the
characteristic integral equations, and strict original source margins give
ordinary component equations on the smaller comparison sets.
Source: charged_SF_new_version.tex:L2782–2783; internal project record AC comparison justification.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [node prop:charged-observation#ac-comparison-justification]
The complete analytic comparison interface in the original AC class:
ordinary and parallel boundary AC, continuous and square-integrable
measured incoming difference, finite covariant variation, both sets of
transported characteristic integral equations, all thirteen ordinary
component equations on strict source interiors, and the original zero
mass/charge axis constraints. There is no incoming trace supremum or
square of an initial outgoing derivative among the premises. The chart
and gauge hypotheses are only their C¹ geometric definitions; no
normalized chart is required to satisfy an axis-normalized solution class.
There are no estimate constants. -/
theorem ac_comparison_justification {e ui b a z s : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (γ : ClockCylinder S (origDomain ui) b a z) (haz : a ≤ z) (hb : 0 < b)
    (hs : 0 < s) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) (U V : ℝ → ℝ)
    (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
    (hUp : ∀ x, 0 < deriv U x) (hVp : ∀ x, 0 < deriv V x) :
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
    (AbsolutelyContinuousOnInterval (fun x => S.a (γ.U x) (γ.V x)) a z ∧
      AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V a) a z ∧
      ContinuousOn (fun x => S.theta (γ.U x) (γ.V x) /
        (S.lam (γ.U x) (γ.V x) : ℂ) - S.xi (γ.U x) (γ.V x) /
        (S.nu (γ.U x) (γ.V x) : ℂ)) (Icc a z) ∧
      IntervalIntegrable (fun x => ‖S.theta (γ.U x) (γ.V x) /
        (S.lam (γ.U x) (γ.V x) : ℂ) - S.xi (γ.U x) (γ.V x) /
        (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2) volume a z ∧
      curveCovVar e S S.a γ.U γ.V a z < ⊤) ∧
    (∀ u a b : ℝ, a ≤ b → U u < V a →
      outSeg (s * U u) (s * V a) (s * V b) ⊆ origDomain ui →
    IntegralForm (P.r u) (P.lam u) a b ∧
      IntegralForm (P.nu u) (P.rUV u) a b ∧
      IntegralForm (P.m u) (P.mV u) a b ∧
      IntegralForm (P.Q u) (P.QV (s * e) u) a b ∧
      IntegralForm (P.A u) (P.AV u) a b ∧
      IntegralForm (P.phi u) (P.phiV u) a b ∧
      IntegralForm (P.xi u) (P.xiV (s * e) u) a b ) ∧
    (∀ a b v : ℝ, a ≤ b → U b < V v →
      inSeg (s * U a) (s * U b) (s * V v) ⊆ origDomain ui →
    IntegralForm (fun u => P.r u v) (fun u => P.nu u v) a b ∧
      IntegralForm (fun u => P.lam u v) (fun u => P.rUV u v) a b ∧
      IntegralForm (fun u => P.m u v) (fun u => P.mU u v) a b ∧
      IntegralForm (fun u => P.Q u v) (fun u => P.QU (s * e) u v) a b ∧
      IntegralForm (fun u => P.phi u v) (fun u => P.phiU (s * e) u v) a b ∧
      IntegralForm (fun u => P.theta u v) (fun u => P.thetaU (s * e) u v) a b ) ∧
    (∀ u v : ℝ, ui < s * U u → s * U u < s * V v → s * V v < 0 →
    (HasDerivAt (P.r u) (P.lam u v) v ∧
      HasDerivAt (P.nu u) (P.rUV u v) v ∧
      HasDerivAt (P.m u) (P.mV u v) v ∧
      HasDerivAt (P.Q u) (P.QV (s * e) u v) v ∧
      HasDerivAt (P.A u) (P.AV u v) v ∧
      HasDerivAt (P.phi u) (P.phiV u v) v ∧
      HasDerivAt (P.xi u) (P.xiV (s * e) u v) v) ∧
    (HasDerivAt (fun x => P.r x v) (P.nu u v) u ∧
      HasDerivAt (fun x => P.lam x v) (P.rUV u v) u ∧
      HasDerivAt (fun x => P.m x v) (P.mU u v) u ∧
      HasDerivAt (fun x => P.Q x v) (P.QU (s * e) u v) u ∧
      HasDerivAt (fun x => P.phi x v) (P.phiU (s * e) u v) u ∧
      HasDerivAt (fun x => P.theta x v) (P.thetaU (s * e) u v) u) ) ∧
    ∀ t : ℝ, (t, t) ∈ origDomain ui → S.m t t = 0 ∧ S.Q t t = 0 := by
  refine ⟨comparison_boundary_regularity hS γ hb haz, ?_, ?_, ?_, ?_⟩
  · intro u a b hab hproper hseg
    exact observation_out_integral_forms hS hs χ hχ U V hU hV hUp hVp hab hproper hseg
  · intro a b v hab hproper hseg
    exact observation_in_integral_forms hS hs χ hχ U V hU hV hUp hVp hab hproper hseg
  · intro u v hi hproper hv
    exact observation_chart_equations hS hs χ hχ U V hU hV hUp hVp hi hproper hv
  · intro t ht
    exact ⟨(hS.axis t ht).2.1, (hS.axis t ht).2.2.1⟩

end EmcsfAcExtension.Global.Observation
