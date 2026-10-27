/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Cooling.SquareRoot
import EmcsfAcExtension.Global.Observation.Energy

/-! # Discharge of the cooling cylinder input

The landed exact energy identity is transported to the common parallel
frame and divided by the fixed radius (`charged_SF_new_version.tex:L2874`–L2884).
The interval and a.e. convention are unchanged. No observation is used.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ComplexConjugate

namespace EmcsfAcExtension.Global.Cooling

/-- [internal] The undivided exact AC cylinder identity
`charged_SF_new_version.tex:L1887–L1894`, quantified over all proper cylinders.
The covariant derivative is evaluated as the derivative of the AC parallel
representative, paired with the outgoing ratio in the same unitary frame. -/
@[expose] def cylinderInput : Prop :=
  ∀ (ui e b s t : ℝ) (S : Fields), OriginalData ui e S → 0 < b → s < t →
    ∀ γ : ClockCylinder S (origDomain ui) b s t,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t →
    AbsolutelyContinuousOnInterval (fun x => cylinderEnergy S b (γ.U x) (γ.V x)) s t ∧
      ∀ᵐ x ∂volume.restrict (Icc s t),
        deriv (fun y => cylinderEnergy S b (γ.U y) (γ.V y)) x +
          ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ) -
            S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 / 2 =
          b * (starRingEnd ℂ (curveParallel e S
            (fun u v => S.theta u v / (S.lam u v : ℂ)) γ.U γ.V s x) *
              deriv (curveParallel e S S.a γ.U γ.V s) x).re

/-- [internal] The exact AC cylinder input follows from the frozen original
solution and the landed energy calculus. The common unitary phase cancels
in the real pairing. Constants: none, for arbitrary coupling and data. -/
theorem cylinder_input : cylinderInput := by
  intro ui e b s t S h hb hst γ hac
  refine ⟨Cylinder.ac_energy h.solution γ hb hst.le hac, ?_⟩
  have hd := Cylinder.ae_deriv_curveParallel hst.le
    (Cylinder.intervalIntegrable_potential_clock h.solution γ hst.le) hac
  filter_upwards [co_exact_energy h.solution γ hb hst.le, hd] with x hx hdx
  rw [hdx]
  have hp : ∀ y z : ℂ,
      conj (Complex.exp (I * e * ∫ y in s..x, S.A (γ.U y) (γ.V y) * deriv γ.U y) * y) *
        (Complex.exp (I * e * ∫ y in s..x, S.A (γ.U y) (γ.V y) * deriv γ.U y) * z) =
      conj y * z := by
    intro y z
    rw [map_mul]
    have hunit : conj (Complex.exp (I * e * ∫ y in s..x,
        S.A (γ.U y) (γ.V y) * deriv γ.U y)) *
        Complex.exp (I * e * ∫ y in s..x, S.A (γ.U y) (γ.V y) * deriv γ.U y) = 1 := by
      rw [Complex.conj_mul']
      simp [Complex.norm_exp, Complex.mul_re]
    calc
      _ = (conj (Complex.exp (I * e * ∫ y in s..x,
        S.A (γ.U y) (γ.V y) * deriv γ.U y)) *
        Complex.exp (I * e * ∫ y in s..x, S.A (γ.U y) (γ.V y) * deriv γ.U y)) *
          (conj y * z) := by ring
      _ = _ := by rw [hunit, one_mul]
  change _ = b * (conj (Complex.exp (I * e * ∫ y in s..x,
    S.A (γ.U y) (γ.V y) * deriv γ.U y) *
      (S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ))) * _).re
  rw [hp]
  convert hx using 1; ring

end EmcsfAcExtension.Global.Cooling

namespace EmcsfAcExtension.Global

/-- [node eq:charged-cool-identity]
The normalized exact identity in a common parallel frame, a.e. on the
proper clock interval, with AC of the energy. Source: L2576–L2589.
Constants: none. The only analytic premise is the source covariant AC. -/
theorem charged_cool_identity (ui e b s t : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hb : 0 < b) (hst : s < t)
    (γ : ClockCylinder S (origDomain ui) b s t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t) :
    AbsolutelyContinuousOnInterval
        (fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b) s t ∧
      ∀ᵐ x ∂volume.restrict (Icc s t),
        deriv (fun y => cylinderEnergy S b (γ.U y) (γ.V y) / b) x +
          ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ) -
            S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 / (2 * b) =
          (starRingEnd ℂ (curveParallel e S
            (fun u v => S.theta u v / (S.lam u v : ℂ)) γ.U γ.V s x) *
              deriv (curveParallel e S S.a γ.U γ.V s) x).re := by
  obtain ⟨hQ, hid⟩ := Cooling.cylinder_input ui e b s t S h hb hst γ hac
  exact charged_cool_identity_of_cylinder hb hst.le hQ hid

/-- [internal]
Square-root energy growth on every proper cylinder segment, with the
universal coefficient `1 / sqrt 2`, independent of observation windows.
The covariant AC premise is internal project record; source: L2591–L2602. -/
theorem Observation.square_root_energy (ui e b s t : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hb : 0 < b) (hst : s < t)
    (γ : ClockCylinder S (origDomain ui) b s t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t) :
    ENNReal.ofReal (Real.sqrt (cylinderEnergy S b (γ.U t) (γ.V t) / b)) ≤
      ENNReal.ofReal (Real.sqrt (cylinderEnergy S b (γ.U s) (γ.V s) / b)) +
      ENNReal.ofReal (1 / Real.sqrt 2) * curveCovVar e S S.a γ.U γ.V s t :=
  square_root_energy_of_cylinder ui e b s t S h hb hst γ hac
    (charged_cool_identity ui e b s t S h hb hst γ hac)

/-- [node eq:charged-cool-square-root]
The square-root estimate on every ordered closed clock interval, including
a singleton (L2591–L2602). The universal coefficient is independent of
observation, duration, radius, coupling and data. Covariant AC is explicit
as required by internal project record. -/
theorem Observation.square_root_energy_le (ui e b s t : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hb : 0 < b) (hst : s ≤ t)
    (γ : ClockCylinder S (origDomain ui) b s t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t) :
    ENNReal.ofReal (Real.sqrt (cylinderEnergy S b (γ.U t) (γ.V t) / b)) ≤
      ENNReal.ofReal (Real.sqrt (cylinderEnergy S b (γ.U s) (γ.V s) / b)) +
      ENNReal.ofReal (1 / Real.sqrt 2) * curveCovVar e S S.a γ.U γ.V s t := by
  rcases lt_or_eq_of_le hst with hlt | rfl
  · exact square_root_energy ui e b s t S h hb hlt γ hac
  · exact le_add_of_nonneg_right zero_le

end EmcsfAcExtension.Global
