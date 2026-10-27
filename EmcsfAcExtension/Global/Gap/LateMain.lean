module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Stages
import EmcsfAcExtension.Global.Gap.Application
import EmcsfAcExtension.Global.Terminal.Hypotheses

/-! # Terminal hypotheses discharged in the late-gap application

The terminal equivalence supplies the radius and scalar estimates, and the
optical theorem supplies the finite global bound. The positive terminal
condition in the application remark is converted by the proved iff.
Source: `charged_SF_new_version.tex:L1818–1829`.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Gap

/-- [node sec:charged-gap#terminal-hypothesis-estimates]
Terminal estimates from the positive exponent, charged_SF_new_version.tex:L1821–1825.
The positive reference radius and scalar constant may depend on the fixed
original development and terminal bound, uniformly in the terminal label. -/
theorem terminal_hypothesis_estimates (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hp : PositiveTerminalFinite ui S) :
    Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0) ∧
      (∀ u ∈ Ico ui 0, 0 ≤ S.m u 0 ∧ S.m u 0 ≤ S.r u 0 / 2) ∧
      ∃ Rstar C : ℝ, 0 < Rstar ∧ 0 < C ∧
        ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
          C * (1 + Real.sqrt (Real.log (Rstar / S.r u 0))) := by
  have ht := charged_terminal_equivalence ui e S h
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmass, hR, htail, hlimit, hlog⟩ :=
    ht.2 (ht.1.mpr hp)
  exact terminal_hypothesis_estimates_of_terminal ui e S h hR ⟨C, hC, hlog⟩

/-- [node sec:charged-gap#terminal-estimates-imply-size]
The exact late-gap size premise follows from the positive terminal exponent,
charged_SF_new_version.tex:L1824–1826. The finite real `Λ` is fixed before the limit;
no uniform convergence rate in `Λ` or the development is asserted. -/
theorem terminal_estimates_imply_size (ui e Λ : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hp : PositiveTerminalFinite ui S) :
    Tendsto (fun u => S.r u 0 * ‖S.phi u 0‖ +
      Real.sqrt (2 * Λ * S.m u 0 * (-u))) (𝓝[<] 0) (𝓝 0) := by
  have ht := charged_terminal_equivalence ui e S h
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmass, hR, htail, hlimit, hlog⟩ :=
    ht.2 (ht.1.mpr hp)
  exact terminal_estimates_imply_size_of_terminal ui e Λ S h hR ⟨C, hC, hlog⟩

/-- [node sec:charged-gap#late-gap-application]
The terminal proposition discharges every premise of the late-gap
application, charged_SF_new_version.tex:L1818–1829. The numerical gap is universal;
the entry label may depend on the fixed development, terminal bound and
coupling, uniformly in both late labels, including the existing axis. -/
theorem late_gap_application (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ a ∈ Ioo ui 0, ∀ p ∈ origDomain ui, a ≤ p.1 →
      gapConstant / 2 ≤ 1 - S.mu p.1 p.2 ∧
        S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2 / 2 := by
  obtain ⟨δ, C, lam₀, hδ, hC, hlam, hgap, hflux, hmass, hR, htail, hlimit, hlog⟩ :=
    (charged_terminal_equivalence ui e S h).2 hs
  obtain ⟨Λ, hΛ, hopt, _⟩ := Terminal.lambda_gap_upper_bound h.ui_neg h.solution h.mu
  exact late_gap_application_of_terminal ui e Λ S h hR ⟨C, hC, hlog⟩ hopt

/-- [internal] Architecture §3's unconditional terminal-to-gap interface.
The numerical gap is universal; the cutoff depends on the fixed original
development, signed terminal bound and coupling, uniformly in both labels. -/
theorem late_from_terminal (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ a ∈ Ioo ui 0, ∀ p ∈ origDomain ui, a ≤ p.1 →
      gapConstant / 2 ≤ 1 - S.mu p.1 p.2 ∧
        S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2 / 2 := by
  exact late_gap_application ui e S h hs

end EmcsfAcExtension.Global.Gap
