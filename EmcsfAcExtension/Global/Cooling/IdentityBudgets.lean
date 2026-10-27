/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Cooling.Cylinder
public import EmcsfAcExtension.Global.Cooling.Budgets
import EmcsfAcExtension.Global.Observation.Energy
import EmcsfAcExtension.Infra.AC.Variation

/-! # Identity-only cylinder budgets

These field estimates discharge every balance premise from the frozen
original data. No completed observation window is required. Suprema are
literal real suprema of the compact energy range (source L2603–L2620).
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [internal] Identity-only field budgets with universal numerical
coefficients, on any proper interval. No observation result is assumed. -/
theorem charged_cool_energy_bounds
    (ui e b s t : ℝ) (S : Fields) (h : OriginalData ui e S)
    (hb : 0 < b) (hst : s < t) (γ : ClockCylinder S (origDomain ui) b s t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t) :
    let σ := (curveCovVar e S S.a γ.U γ.V s t).toReal
    (∀ x ∈ Icc s t, cylinderEnergy S b (γ.U x) (γ.V x) / b ≤
      2 * (cylinderEnergy S b (γ.U s) (γ.V s) / b) + σ ^ 2) ∧
    cylinderDissipation S γ.U γ.V s t / b ≤
      4 * (cylinderEnergy S b (γ.U s) (γ.V s) / b) + 3 * σ ^ 2 ∧
    (∀ x ∈ Icc s t, cylinderEnergy S b (γ.U x) (γ.V x) / b +
      cylinderDissipation S γ.U γ.V s t / b ≤
        6 * (cylinderEnergy S b (γ.U s) (γ.V s) / b + σ ^ 2)) :=
  charged_cool_energy_of_cylinder ui e b s t S h hb hst γ hac
    (charged_cool_identity ui e b s t S h hb hst γ hac)

/-- [node prop:charged-cool#supremum-energy-bound]
The actual compact energy supremum is at most twice its initial value
plus the squared covariant variation (L2603–L2607). Universal coefficients,
uniform in radius, duration, coupling and data, before observation. -/
theorem charged_cool_supremum_energy_bound (ui e b s t : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hb : 0 < b) (hst : s < t)
    (γ : ClockCylinder S (origDomain ui) b s t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t) :
    sSup ((fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b) '' Icc s t) ≤
      2 * (cylinderEnergy S b (γ.U s) (γ.V s) / b) +
        (curveCovVar e S S.a γ.U γ.V s t).toReal ^ 2 := by
  apply csSup_le ((nonempty_Icc.mpr hst.le).image _)
  rintro _ ⟨x, hx, rfl⟩
  exact (charged_cool_energy_bounds ui e b s t S h hb hst γ hac).1 x hx

/-- [node prop:charged-cool#integrated-dissipation]
Integrating the exact identity gives the forcing estimate with the actual
energy supremum, before inserting its separate bound (L2608–L2617).
All coefficients are universal. No observation premise or window is used. -/
theorem charged_cool_integrated_dissipation (ui e b s t : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hb : 0 < b) (hst : s < t)
    (γ : ClockCylinder S (origDomain ui) b s t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t) :
    cylinderDissipation S γ.U γ.V s t / (2 * b) ≤
      cylinderEnergy S b (γ.U s) (γ.V s) / b +
        Real.sqrt (2 * sSup
          ((fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b) '' Icc s t)) *
          (curveCovVar e S S.a γ.U γ.V s t).toReal := by
  let q := fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b
  let D := fun x => ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ) -
    S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2
  let g := fun x => ‖deriv (curveParallel e S S.a γ.U γ.V s) x‖
  let M := sSup (q '' Icc s t)
  have hi := charged_cool_identity ui e b s t S h hb hst γ hac
  have hqn (x : ℝ) (hx : x ∈ Icc s t) : 0 ≤ q x :=
    (Cooling.normalized_energy_lower hb (h.mu _ (γ.mem x hx))).1
  have hbounded : BddAbove (q '' Icc s t) := by
    refine ⟨2 * q s + (curveCovVar e S S.a γ.U γ.V s t).toReal ^ 2, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact (charged_cool_energy_bounds ui e b s t S h hb hst γ hac).1 x hx
  have hle (x : ℝ) (hx : x ∈ Icc s t) : q x ≤ M :=
    le_csSup hbounded (mem_image_of_mem _ hx)
  obtain ⟨cy, cz, _⟩ := Cylinder.continuousOn_normalized_traces h.solution γ
  have hD : IntervalIntegrable D volume s t :=
    ((cy.sub cz).norm.pow 2).intervalIntegrable_of_Icc hst.le
  have hg : IntervalIntegrable g volume s t := hac.intervalIntegrable_deriv_finiteDimensional.norm
  have hbal : ∀ᵐ x ∂volume.restrict (Icc s t),
      deriv q x + D x / (2 * b) ≤ Real.sqrt (2 * M) * g x := by
    filter_upwards [hi.2, ae_restrict_mem measurableSet_Icc] with x hx hxm
    have hy : ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ≤
        Real.sqrt (2 * M) := by
      apply Real.le_sqrt_of_sq_le
      exact (Cooling.normalized_energy_lower hb (h.mu _ (γ.mem x hxm))).2.trans
        (mul_le_mul_of_nonneg_left (hle x hxm) (by norm_num))
    have hp := Complex.re_le_norm (starRingEnd ℂ (curveParallel e S
      (fun u v => S.theta u v / (S.lam u v : ℂ)) γ.U γ.V s x) *
        deriv (curveParallel e S S.a γ.U γ.V s) x)
    rw [norm_mul, Complex.norm_conj, Cylinder.norm_curveParallel] at hp
    exact hx.le.trans (hp.trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _)))
  have hint := intervalIntegral.integral_mono_ae_restrict hst.le
    (hi.1.intervalIntegrable_deriv.add (hD.div_const _))
    (hg.const_mul (Real.sqrt (2 * M))) hbal
  rw [intervalIntegral.integral_add hi.1.intervalIntegrable_deriv (hD.div_const _),
    hi.1.integral_deriv_eq_sub, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul] at hint
  have hv := hac.toReal_eVariationOn_eq_integral_norm_deriv hst.le
  change (curveCovVar e S S.a γ.U γ.V s t).toReal = ∫ x in s..t, g x at hv
  rw [← hv] at hint
  change (∫ x in s..t, D x) / (2 * b) ≤ _
  linarith only [hint, hqn t (right_mem_Icc.mpr hst.le)]

/-- [internal] Literal supremum-plus-dissipation budget on a proper
interval. The constant `6` is universal and needs no observation. -/
theorem charged_cool_energy_sup (ui e b s t : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hb : 0 < b) (hst : s < t)
    (γ : ClockCylinder S (origDomain ui) b s t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t) :
    sSup ((fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b) '' Icc s t) +
        cylinderDissipation S γ.U γ.V s t / b ≤
      6 * (cylinderEnergy S b (γ.U s) (γ.V s) / b +
        (curveCovVar e S S.a γ.U γ.V s t).toReal ^ 2) := by
  have hs := charged_cool_supremum_energy_bound ui e b s t S h hb hst γ hac
  have hd := (charged_cool_energy_bounds ui e b s t S h hb hst γ hac).2.1
  have hn := (Cooling.normalized_energy_lower hb (h.mu _ (γ.mem s (left_mem_Icc.mpr hst.le)))).1
  nlinarith only [hs, hd, hn, sq_nonneg (curveCovVar e S S.a γ.U γ.V s t).toReal]

end EmcsfAcExtension.Global
