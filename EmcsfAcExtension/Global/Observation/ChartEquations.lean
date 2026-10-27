module

public import EmcsfAcExtension.Global.Observation.SourceEquations

/-! # Ordinary equations on the actual normalized observation chart

The original integral equations give the ordinary derivatives on strict
source interiors; gauge, scale and null-label covariance transport all
thirteen equations. No chart is asserted to be an axis-normalized solution.
Source: charged_SF_new_version.tex:L1975–2034, L2782–2783; internal project record AC justification.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
All thirteen characteristic equations on the constructed gauged and
rescaled null chart. Only C¹ positive chart Jacobians and strict original
source margins are required. The conclusion holds at every point of a
smaller closed comparison set having these margins. No constants occur. -/
theorem observation_chart_equations {e ui s u v : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (hs : 0 < s)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) (U V : ℝ → ℝ)
    (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
    (hUp : ∀ x, 0 < deriv U x) (hVp : ∀ x, 0 < deriv V x)
    (hi : ui < s * U u) (hproper : s * U u < s * V v) (hv : s * V v < 0) :
    let P := nullPullback (rescaleFields (gaugeFields e S χ) s) U V
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
      HasDerivAt (fun x => P.theta x v) (P.thetaU (s * e) u v) u) := by
  let D := {p : ℝ × ℝ | ui < p.1 ∧ p.1 < p.2 ∧ p.2 < 0}
  let G := gaugeFields e S χ
  have heq (p : ℝ × ℝ) (hp : p ∈ D) :=
    gaugeFields_equations e S χ p.1 p.2 (deriv χ p.1)
      ((contDiff_one_iff_deriv.mp hχ).1 p.1).hasDerivAt
      (original_characteristic_equations hS hp.1 hp.2.1 hp.2.2).1
      (original_characteristic_equations hS hp.1 hp.2.1 hp.2.2).2
  have hscaled := rescaleFields_equations G D s e hs
    (fun p hp => (heq p hp).1) (fun p hp => (heq p hp).2)
  have hp : (U u, V v) ∈ {p : ℝ × ℝ | (s * p.1, s * p.2) ∈ D} := ⟨hi, hproper, hv⟩
  exact nullPullback_equations (rescaleFields G s) U V (s * e) u v (deriv U u) (deriv V v)
    ((contDiff_one_iff_deriv.mp hU).1 u).hasDerivAt
    ((contDiff_one_iff_deriv.mp hV).1 v).hasDerivAt (hUp u) (hVp v)
    (hscaled (U u, V v) hp).1 (hscaled (U u, V v) hp).2

end EmcsfAcExtension.Global.Observation
