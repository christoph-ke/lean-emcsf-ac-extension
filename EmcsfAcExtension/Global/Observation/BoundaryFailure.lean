module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.OrigDomain
public import EmcsfAcExtension.Global.Defs.Observation
public import EmcsfAcExtension.Global.Defs.Curves
import EmcsfAcExtension.Global.Observation.BoundaryData
import EmcsfAcExtension.Global.Observation.Energy
import EmcsfAcExtension.Infra.AC.Variation

/-! # Analytic inputs for the quantitative observation assembly

The finite real boundary budgets agree with the extended nonnegative budgets
in the architecture's observation statement. The observation coefficient is
selected before every physical datum. The outer and inner comparison records
are still required for the strict-barrier application and the parent theorem.
Source: `charged_SF_new_version.tex:L2756–L2783`; approved internal project record, observation
synthesis and AC comparison justification.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
On a proper positive-radius cylinder, the frozen solution supplies the
ordinary and parallel AC boundary representatives and a continuous measured
incoming difference. Its squared flux is integrable and its covariant
variation is finite. This uses no square of an initial outgoing derivative.
There are no uniform constants or additional regularity hypotheses. -/
theorem comparison_boundary_regularity {e ui b s t : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (γ : ClockCylinder S (origDomain ui) b s t) (hb : 0 < b) (hst : s ≤ t) :
    AbsolutelyContinuousOnInterval (fun x => S.a (γ.U x) (γ.V x)) s t ∧
      AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t ∧
      ContinuousOn (fun x => S.theta (γ.U x) (γ.V x) /
        (S.lam (γ.U x) (γ.V x) : ℂ) - S.xi (γ.U x) (γ.V x) /
        (S.nu (γ.U x) (γ.V x) : ℂ)) (Icc s t) ∧
      IntervalIntegrable (fun x => ‖S.theta (γ.U x) (γ.V x) /
        (S.lam (γ.U x) (γ.V x) : ℂ) - S.xi (γ.U x) (γ.V x) /
        (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2) volume s t ∧
      curveCovVar e S S.a γ.U γ.V s t < ⊤ := by
  have ha := Cylinder.ac_a hS γ hb hst
  have hp := Cylinder.ac_curveParallel_a hS γ hb hst
  obtain ⟨hy, hz, _⟩ := Cylinder.continuousOn_normalized_traces hS γ
  refine ⟨ha, hp, hy.sub hz, ((hy.sub hz).norm.pow 2).intervalIntegrable_of_Icc hst, ?_⟩
  rw [Cylinder.cylinder_covariant_variation hS γ hb hst]
  exact ENNReal.ofReal_lt_top

/-- [internal]
Failure of the architecture's extended nonnegative observation budget gives
both normalized small-boundary norms, for the prescribed continuous traces.
The single positive coefficient depends only on the fixed window `T` and
requested tolerance `ε`; it is chosen before all physical data, backgrounds,
normalizing scales and variations. Adding charge to the scale is allowed by
`m + b‖y‖ ≤ s`. The comparison consumer must identify these traces with its
parallel boundary scalar and measured incoming difference. -/
theorem small_boundary_of_failed_observation {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (b m s τ₀ : ℝ) (V : ℝ≥0∞) (y H : ℂ) (a q : ℝ → ℂ),
        0 < b → 0 ≤ m → 0 < s → V ≠ ⊤ → m + b * ‖y‖ ≤ s →
        ContinuousOn a (Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2)) →
        ContinuousOn q (Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2)) → a τ₀ = H →
        eVariationOn a (Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2)) = V →
        ¬ ENNReal.ofReal (b * (‖y‖ ^ 2 + (2 * m / b) ^ 2)) ≤
          ENNReal.ofReal C *
            (ENNReal.ofReal (∫ τ in (τ₀ - T * b / 2)..(τ₀ + T * b / 2), ‖q τ‖ ^ 2) +
              ENNReal.ofReal b * V ^ 2) →
        (∀ t ∈ Icc (-T * (b / s)) (T * (b / s)),
          ‖a (τ₀ + (s / 2) * t) - H‖ ≤ ε / (b / s)) ∧
        (∫ t in (-T * (b / s))..(T * (b / s)),
          ‖a (τ₀ + (s / 2) * t) - H - q (τ₀ + (s / 2) * t)‖ ^ 2) ≤ ε ^ 2 / (b / s) := by
  obtain ⟨C, hC, hsmall⟩ := co_small_boundary_of_failed_observation hT hε
  refine ⟨C, hC, ?_⟩
  intro b m s τ₀ V y H a q hb hm hs hV hscale ha hq hH hvar hfailure
  have hI : 0 ≤ ∫ τ in (τ₀ - T * b / 2)..(τ₀ + T * b / 2), ‖q τ‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by nlinarith only [mul_nonneg hT hb.le])
      (fun _ _ => sq_nonneg _)
  have hA : 0 ≤ b * (‖y‖ ^ 2 + (2 * m / b) ^ 2) := by positivity
  have hfinite : ENNReal.ofReal (∫ τ in (τ₀ - T * b / 2)..(τ₀ + T * b / 2), ‖q τ‖ ^ 2) +
      ENNReal.ofReal b * V ^ 2 ≠ ⊤ := by finiteness
  have hreal := (ENNReal.toReal_lt_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite) ENNReal.ofReal_ne_top).mpr
      (lt_of_not_ge hfailure)
  rw [ENNReal.toReal_mul, ENNReal.toReal_add ENNReal.ofReal_ne_top
    (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hC.le, ENNReal.toReal_ofReal hI,
    ENNReal.toReal_ofReal hb.le, ENNReal.toReal_ofReal hA] at hreal
  apply hsmall b m s τ₀ V.toReal y H a q hb hm hs ENNReal.toReal_nonneg hscale ha hq hH
  · rw [hvar, ENNReal.ofReal_toReal hV]
  · exact hreal

end EmcsfAcExtension.Global.Observation
