/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Observation
public import EmcsfAcExtension.Global.Defs.Original
import EmcsfAcExtension.Global.Cooling.ObservationDischarge
import EmcsfAcExtension.Infra.AC.Variation

/-! # Unconditional cooling subnodes

The proved observation theorem discharges the observation premise of the
cooling helpers. These exports retain the exact center coefficient, the
literal supremum budgets on every ordered subinterval, the two averaging
bounds, and the real endpoint decrease.
Source: `charged_SF_new_version.tex:L2841`–L2870, L2923–L3021.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [node eq:charged-cool-centers]
Integrated observation on full-window centers, with exact coefficient
`2 * Cstar * Tstar`. All constants depend only on `δ`, before every
solution, coupling, scalar background, radius and interval. The estimate
also covers an empty center interval. Source: `charged_SF_new_version.tex:L2935`–L2947. -/
theorem charged_cool_centers (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Tstar Cstar δstar ηstar C : ℝ,
    0 < Tstar ∧ 0 < Cstar ∧ 0 < δstar ∧ δstar ≤ 1 / 2 ∧ 0 < ηstar ∧ 0 < C ∧
    ∀ (ui e b s t : ℝ) (S : Fields), 0 < b → s < t → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b s t,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t →
    (∀ τ ∈ Icc s t, S.mu (γ.U τ) (γ.V τ) +
      ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    (∀ τ ∈ Icc (s + Tstar * b) (t - Tstar * b),
      triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
    let σ := (curveCovVar e S S.a γ.U γ.V s t).toReal
    (∫ x in Icc (s + Tstar * b) (t - Tstar * b),
      (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
        S.mu (γ.U x) (γ.V x) ^ 2) / b) ≤
      2 * Cstar * Tstar * (cylinderDissipation S γ.U γ.V s t / b + σ ^ 2) :=
  Cooling.centers_of_observation δ hδ (Cooling.observation_input δ hδ)

/-- [node eq:charged-cool-outgoing-budget]
The outgoing-ratio and mass-square budget, including short intervals.
All constants depend only on `δ`, before every solution, coupling, scalar
background, radius, duration and initial energy.
Source: `charged_SF_new_version.tex:L2961`–L2965. -/
theorem charged_cool_outgoing_budget (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Tstar Cstar δstar ηstar C : ℝ,
    0 < Tstar ∧ 0 < Cstar ∧ 0 < δstar ∧ δstar ≤ 1 / 2 ∧ 0 < ηstar ∧ 0 < C ∧
    ∀ (ui e b s t : ℝ) (S : Fields), 0 < b → s < t → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b s t,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t →
    (∀ τ ∈ Icc s t, S.mu (γ.U τ) (γ.V τ) +
      ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    (∀ τ ∈ Icc (s + Tstar * b) (t - Tstar * b),
      triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
    let σ := (curveCovVar e S S.a γ.U γ.V s t).toReal
    (∫ x in s..t,
      (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
        S.mu (γ.U x) (γ.V x) ^ 2) / b) ≤
      C * (cylinderEnergy S b (γ.U s) (γ.V s) / b + σ ^ 2) :=
  Cooling.outgoing_budget_of_observation δ hδ (Cooling.observation_input δ hδ)

/-- [node eq:charged-cool-integrated]
The literal supremum-plus-integral scalar, mass and squared-energy budget.
All constants depend only on `δ`, before every solution, coupling, scalar
background, radius, duration and initial energy.
Source: `charged_SF_new_version.tex:L2841`–L2852, L2967–L2984. -/
theorem charged_cool_integrated (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Tstar Cstar δstar ηstar C : ℝ,
    0 < Tstar ∧ 0 < Cstar ∧ 0 < δstar ∧ δstar ≤ 1 / 2 ∧ 0 < ηstar ∧ 0 < C ∧
    ∀ (ui e b s t : ℝ) (S : Fields), 0 < b → s < t → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b s t,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t →
    (∀ τ ∈ Icc s t, S.mu (γ.U τ) (γ.V τ) +
      ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    (∀ τ ∈ Icc (s + Tstar * b) (t - Tstar * b),
      triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
    let σ := (curveCovVar e S S.a γ.U γ.V s t).toReal
    sSup ((fun x => S.m (γ.U x) (γ.V x) / b +
      ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2) '' Icc s t) +
        (∫ x in s..t,
          (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           ‖S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           S.mu (γ.U x) (γ.V x) ^ 2 +
           (cylinderEnergy S b (γ.U x) (γ.V x) / b) ^ 2) / b) ≤
      C * (cylinderEnergy S b (γ.U s) (γ.V s) / b + σ ^ 2) :=
  Cooling.integrated_of_observation δ hδ (Cooling.observation_input δ hδ)

/-- [node prop:charged-cool#subinterval-budgets]
Both literal supremum-plus-integral budgets on every ordered subinterval,
including singletons and unfinished stages, using its own initial energy
and covariant variation. All constants depend only on `δ`, before every
solution, coupling, scalar background, radius, duration and initial energy.
Source: `charged_SF_new_version.tex:L2986`–L2988. -/
theorem Cooling.subinterval_budgets (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Tstar Cstar δstar ηstar C : ℝ,
    0 < Tstar ∧ 0 < Cstar ∧ 0 < δstar ∧ δstar ≤ 1 / 2 ∧ 0 < ηstar ∧ 0 < C ∧
    ∀ (ui e b s t : ℝ) (S : Fields), 0 < b → s < t → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b s t,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t →
    (∀ τ ∈ Icc s t, S.mu (γ.U τ) (γ.V τ) +
      ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    (∀ τ ∈ Icc (s + Tstar * b) (t - Tstar * b),
      triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
    ∀ a ∈ Icc s t, ∀ c ∈ Icc a t,
    let σ := (curveCovVar e S S.a γ.U γ.V a c).toReal
    (sSup ((fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b) '' Icc a c) +
        cylinderDissipation S γ.U γ.V a c / b ≤
      C * (cylinderEnergy S b (γ.U a) (γ.V a) / b + σ ^ 2)) ∧
    (sSup ((fun x => S.m (γ.U x) (γ.V x) / b +
      ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2) '' Icc a c) +
        (∫ x in a..c,
          (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           ‖S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           S.mu (γ.U x) (γ.V x) ^ 2 +
           (cylinderEnergy S b (γ.U x) (γ.V x) / b) ^ 2) / b) ≤
      C * (cylinderEnergy S b (γ.U a) (γ.V a) / b + σ ^ 2)) :=
  Cooling.subinterval_budgets_of_observation δ hδ (Cooling.observation_input δ hδ)

/-- [node prop:charged-cool#averaged-small-energy-time]
A time in the latter half of the cylinder interval satisfying both exact
square-root bounds. All constants depend only on `δ`, before the arbitrary
positive duration factor `H` and every solution, coupling, scalar background,
radius, duration and initial energy. Source: `charged_SF_new_version.tex:L2990`–L3001. -/
theorem Cooling.averaged_small_energy_time_on_cylinder (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Tstar Cstar δstar ηstar C : ℝ,
    0 < Tstar ∧ 0 < Cstar ∧ 0 < δstar ∧ δstar ≤ 1 / 2 ∧ 0 < ηstar ∧ 0 < C ∧
    ∀ H : ℝ, 0 < H →
    ∀ (ui e b ε T : ℝ) (S : Fields), 0 < b → 0 < ε → 0 < T → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b 0 T,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V 0) 0 T →
    (∀ τ ∈ Icc 0 T, S.mu (γ.U τ) (γ.V τ) +
      ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    (∀ τ ∈ Icc (0 + Tstar * b) (T - Tstar * b),
      triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
    cylinderEnergy S b (γ.U 0) (γ.V 0) / b ≤ ε → T = H * b / ε →
    let σ := (curveCovVar e S S.a γ.U γ.V 0 T).toReal
    ∃ x ∈ Icc (T / 2) T,
      cylinderEnergy S b (γ.U x) (γ.V x) / b ≤
        Real.sqrt ((2 * C * ε / H) * (ε + σ ^ 2)) ∧
      Real.sqrt ((2 * C * ε / H) * (ε + σ ^ 2)) ≤
        Real.sqrt (2 * C / H) * (ε + Real.sqrt ε * σ) :=
  Cooling.averaged_small_energy_time_of_observation δ hδ (Cooling.observation_input δ hδ)

/-- [node eq:charged-cool-decrease]
The real endpoint cooling decrease on the `b / ε` clock. The thresholds
and budget constant depend only on `δ`; `Hd` and `Cd` depend only on `δ`
and `d`, before every solution, coupling, scalar background, radius,
duration and initial energy. Source: `charged_SF_new_version.tex:L2857`–L2870.
-/
theorem charged_cool_decrease (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
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
    (cylinderEnergy S b (γ.U 0) (γ.V 0) / b ≤ ε → T = Hd * b / ε →
      cylinderEnergy S b (γ.U T) (γ.V T) / b ≤ d * ε + Cd *
        (curveCovVar e S S.a γ.U γ.V 0 T).toReal ^ 2) := by
  obtain ⟨Ts, δs, ηs, Cb, hTs, hδs, hηs, hCb, hcool⟩ :=
    charged_cool_decrease_of_observation δ hδ (Cooling.observation_input δ hδ)
  refine ⟨Ts, δs, ηs, Cb, hTs, hδs, hηs, hCb, ?_⟩
  intro d hd
  obtain ⟨Hd, Cd, hHd, hCd, hcool⟩ := hcool d hd
  refine ⟨Hd, Cd, hHd, hCd, ?_⟩
  intro ui e b ε T S hb hε hT h γ hac hweak hwindows hq₀ hclock
  have hdec := hcool ui e b ε T S hb hε hT h γ hac hweak hwindows hq₀ hclock
  have hvarfin : curveCovVar e S S.a γ.U γ.V 0 T ≠ ∞ :=
    hac.boundedVariationOn_Icc hT.le
  have hrhs : ENNReal.ofReal (d * ε + Cd *
        (curveCovVar e S S.a γ.U γ.V 0 T).toReal ^ 2) =
      ENNReal.ofReal (d * ε) + ENNReal.ofReal Cd *
        (curveCovVar e S S.a γ.U γ.V 0 T) ^ 2 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul hCd.le, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hvarfin]
  rw [← hrhs] at hdec
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hdec

end EmcsfAcExtension.Global
