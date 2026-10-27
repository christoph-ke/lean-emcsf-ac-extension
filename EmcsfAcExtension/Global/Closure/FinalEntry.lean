module

public import EmcsfAcExtension.Global.Closure.CallbackContinuation
import EmcsfAcExtension.Global.Interaction.Profiles
import EmcsfAcExtension.Global.Interaction.ClosuresScalar
import Mathlib.Tactic

/-! # Numerical and singleton-entry adapters for the final construction

Keep the proper entry family selected by the initialization theorem. Only
the singleton graph is transferred to its constant entry label; the
original proper roots and limiting entry density are retained.
Source: `charged_SF_new_version.tex:L3854–L3898`.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
The proper initializer's weak-regime margin gives the numerical
`F+εweak` margin needed by the recurrence and budget producers. Its
threshold is fixed before the weak box. Constants: none are chosen. -/
theorem weak_box_margin_of_initialization {δ c Λ F εweak ρ η : ℝ}
    (hbox : ExteriorBox δ c Λ F εweak ρ) (hη : 0 < η)
    (hmargin : ∀ μ x : ℝ, 0 ≤ μ → μ < 1 → μ / (1 - μ) ≤ εweak →
      x ≤ F → μ + x < η / 4) : F + εweak ≤ η := by
  have he : 0 ≤ εweak := hbox.2.2.2.2.2.2.1
  have hF : 0 ≤ F := hbox.2.2.2.2.1
  have he1 : εweak < 1 :=
    ((le_max_left _ _).trans_lt hbox.2.2.2.2.2.2.2.1).trans_le
      (sub_le_self _ (sq_nonneg F))
  have hμ : εweak / 2 < 1 := by linarith only [he1]
  have hratio : (εweak / 2) / (1 - εweak / 2) ≤ εweak := by
    apply (div_le_iff₀ (sub_pos.mpr hμ)).mpr
    have hp := mul_nonneg he (sub_nonneg.mpr he1.le)
    nlinarith only [hp]
  have hh := hmargin (εweak / 2) F (by positivity) hμ hratio le_rfl
  linarith only [hh, hη, hF]

/-- [internal]
Transfer the proper singleton entry stop to the constant graph at its
actual outgoing entry label. The incoming norm becomes the initial
density, with no source or continuity premise. Constants: none. -/
theorem constant_entry_of_proper_initialization
    {S : Fields} {ui a R₀ δ c Λ F ε εstop : ℝ} {V : ℝ → ℝ}
    (hentry : StrictFiniteCutoffStops S ui a R₀ V
      (fun t => (interactionNorm e S (exteriorDomain ui a t V) a (V a)).toReal)
      (fun _ => 0) δ c Λ F ε εstop a) :
    StrictFiniteCutoffStops S ui a R₀ (fun _ => V a)
      (fun _ => (initialInteraction S a (V a)).toReal) (fun _ => 0)
      δ c Λ F ε εstop a := by
  have heq : EqOn (fun _ => V a) V (Icc a a) := by
    intro u hu
    exact congrArg V (le_antisymm hu.1 hu.2)
  have hdom := exteriorDomain_congr_boundary (ui := ui) heq
  simpa only [StrictFiniteCutoffStops, hdom, interactionNorm_initial_cutoff] using hentry

/-- [internal]
The canonical exterior scalar background is nonnegative at every proper
entry. Its terminal supremum contains that entry itself. All stopping
parameters are fixed before the entry row. -/
theorem scalar_background_nonneg_at_entry {S : Fields} {ui e a c F Jstop : ℝ}
    (h : OriginalData ui e S) (ha : a ∈ Ico ui 0) (hR : 0 < S.r a 0)
    (hc : 0 < c) (hF : 0 ≤ F) (hF2 : F ^ 2 < 1) (hJ : 0 ≤ Jstop) :
    0 ≤ Interaction.scalarBackground ui (S.r a 0) c F Jstop S := by
  have hsup : 0 ≤ Interaction.terminalScalarSup ui (S.r a 0) S :=
    (norm_nonneg _).trans (Interaction.terminal_scalar_le_sup h hR ha
      ⟨half_le_self hR.le, le_rfl⟩)
  have hden : 0 < 1 - F ^ 2 := sub_pos.mpr hF2
  unfold Interaction.scalarBackground
  positivity

/-- [internal]
The canonical charged error is bounded by its logarithmic majorant's
charged error, with coefficient one, uniformly in all couplings and
physical scales. The two nonnegative amplitudes precede the comparison. -/
theorem charged_error_le_of_background {e B M R : ℝ}
    (hB : 0 ≤ B) (hBM : B ≤ M) :
    Local.sigma e B (2 * R) ≤ e ^ 2 * M ^ 2 * R ^ 2 := by
  rw [ct_zeta]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hB (hB.trans hBM)).mpr hBM) (sq_nonneg e))
    (sq_nonneg R)

end EmcsfAcExtension.Global.Closure
