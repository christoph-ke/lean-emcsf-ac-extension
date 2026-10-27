/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Cooling.Full
import EmcsfAcExtension.Global.Cooling.ObservationDischarge

/-! # The full unconditional charged cooling proposition

The proved observation theorem discharges the observation input of the full
cooling assembly, retaining both supremum-plus-integral budgets on every
ordered subinterval and the endpoint decrease.
Source: `charged_SF_new_version.tex:L2798`–L2871, L2986–L3021.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [node prop:charged-cool]
The full charged cooling proposition, with both supremum-plus-integral budgets
on every ordered subinterval, including singletons, and the endpoint decrease.
`Tstar`, `δstar`, `ηstar`, and `Cbudget` depend only on `δ`; `Hd` and `Cd` depend
only on `δ` and `d`. All constants precede every physical datum and are uniform
in the coupling, scalar background, radius, duration, and initial energy,
subject to the stated hypotheses. Source: `charged_SF_new_version.tex:L2798`–L2871. -/
theorem charged_cool (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Tstar δstar ηstar Cbudget : ℝ,
    0 < Tstar ∧ 0 < δstar ∧ 0 < ηstar ∧ 0 < Cbudget ∧
    ∀ d : ℝ, 0 < d → ∃ Hd Cd : ℝ, 0 < Hd ∧ 0 < Cd ∧
    ∀ (ui e b ε T : ℝ) (S : Fields), 0 < b → 0 < ε → 0 < T → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b 0 T,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V 0) 0 T →
    (∀ τ ∈ Icc 0 T, S.mu (γ.U τ) (γ.V τ) +
      ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    (∀ τ ∈ Icc (Tstar * b) (T - Tstar * b),
      triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
    (∀ a ∈ Icc 0 T, ∀ c ∈ Icc a T,
      let σ := (curveCovVar e S S.a γ.U γ.V a c).toReal
      (sSup ((fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b) '' Icc a c) +
        cylinderDissipation S γ.U γ.V a c / b ≤
      Cbudget * (cylinderEnergy S b (γ.U a) (γ.V a) / b + σ ^ 2)) ∧
      (sSup ((fun x => S.m (γ.U x) (γ.V x) / b +
      ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2) '' Icc a c) +
        (∫ x in a..c,
          (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           ‖S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           S.mu (γ.U x) (γ.V x) ^ 2 +
           (cylinderEnergy S b (γ.U x) (γ.V x) / b) ^ 2) / b) ≤
      Cbudget * (cylinderEnergy S b (γ.U a) (γ.V a) / b + σ ^ 2))) ∧
    (cylinderEnergy S b (γ.U 0) (γ.V 0) / b ≤ ε → T = Hd * b / ε →
      cylinderEnergy S b (γ.U T) (γ.V T) / b ≤ d * ε + Cd *
        (curveCovVar e S S.a γ.U γ.V 0 T).toReal ^ 2) :=
  charged_cool_full_of_observation δ hδ (Cooling.observation_input δ hδ)

end EmcsfAcExtension.Global
