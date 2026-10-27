module

public import EmcsfAcExtension.Global.Defs.Original
import EmcsfAcExtension.Global.Terminal.Amplitude
import EmcsfAcExtension.Global.Terminal.Hypotheses

/-! # Unconditional terminal amplitude estimates

The terminal proposition and the global optical bound discharge all terminal
inputs to the amplitude helpers. Source: `charged_SF_new_version.tex:L1038–1066`.
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global

namespace Amplitude

/-- [internal] The proved optical upper bound, including the existing axis.
The positive witness depends on the fixed original development, uniformly
in both labels. The off-axis theorem supplies the bound on positive radius;
the frozen axis traces supply the remaining values. -/
theorem optical_upper (ui e : ℝ) (S : Fields) (h : OriginalData ui e S) :
    ∃ C : ℝ, 0 < C ∧
      ∀ p ∈ origDomain ui, S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ C := by
  obtain ⟨C, hC, hopt, hlam⟩ := Terminal.lambda_gap_upper_bound h.ui_neg h.solution h.mu
  refine ⟨C, hC, ?_⟩
  rintro ⟨u, v⟩ hp
  have huv : u ≤ v := hp.2.2.1
  rcases huv.eq_or_lt with rfl | huv
  · simpa only [Fields.mu, (h.solution.axis u hp).2.1, mul_zero, zero_div,
      sub_zero, div_one] using hlam (u, u) hp
  · exact hopt (u, v) hp huv

/-- [node lem:charged-rphi-small#outgoing-scalar-comparison]
Outgoing Cauchy–Schwarz comparison, charged_SF_new_version.tex:L1048–1057. The positive
optical constant depends on the fixed original development, uniformly in
both labels. Both proper integrals and both inequalities are retained. -/
theorem outgoing_scalar_comparison (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) (_hs : SignedTerminalBound ui S) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v, u ∈ Ico ui 0 → v ∈ Ioc u 0 →
      let E := fun s => (1 - S.mu u s) * ‖S.theta u s‖ ^ 2 / S.lam u s
      let W := fun s => S.lam u s / ((1 - S.mu u s) * S.r u s ^ 2)
      IntervalIntegrable E volume v 0 ∧ IntervalIntegrable W volume v 0 ∧
        ‖S.phi u v - S.phi u 0‖ ^ 2 ≤ (∫ s in v..0, E s) * (∫ s in v..0, W s) ∧
        (∫ s in v..0, E s) * (∫ s in v..0, W s) ≤
          2 * C * S.m u 0 * (-v) / S.r u v ^ 2 := by
  obtain ⟨C, hC, hopt⟩ := optical_upper ui e S h
  exact ⟨C, hC, outgoing_scalar_comparison_of_terminal ui e S h C hC hopt⟩

/-- [node lem:charged-rphi-small#row-amplitude-limit]
The uniform row majorant tends to zero, charged_SF_new_version.tex:L1058–1064. Its optical
constant depends on the fixed development, uniformly in the row and point.
No interior gap or lower expansion bound is assumed. -/
theorem row_amplitude_limit (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ C : ℝ, 0 < C ∧
      (∀ p ∈ origDomain ui, S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤
        S.r p.1 0 * ‖S.phi p.1 0‖ + Real.sqrt (2 * C * S.m p.1 0 * (-p.1))) ∧
      Tendsto (fun u => S.r u 0 * ‖S.phi u 0‖ + Real.sqrt (2 * C * S.m u 0 * (-u)))
        (𝓝[<] 0) (𝓝 0) := by
  obtain ⟨δ, K, lam₀, hδ, hK, hlam, hgap, hflux, hmass, hR, htail, hlimit, hlog⟩ :=
    (charged_terminal_equivalence ui e S h).2 hs
  obtain ⟨C, hC, hopt⟩ := optical_upper ui e S h
  exact ⟨C, hC, row_amplitude_limit_of_terminal ui e S h C K hC hopt hR hlog⟩

end Amplitude

/-- [node lem:charged-rphi-small]
Uniform smallness of the dimensionless scalar amplitude and charged
amplitude on every late row, charged_SF_new_version.tex:L1038–1046. The coupling is
arbitrary. Entry labels may depend on the development, signed bound,
coupling and tolerance; the estimates are uniform in both late labels. -/
theorem charged_rphi_small (ui e : ℝ) (S : Fields) (h : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) :
    (∀ η : ℝ, 0 < η → ∃ u₀ ∈ Ioo ui 0,
      ∀ p ∈ origDomain ui, u₀ ≤ p.1 → S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ η) ∧
    (∀ η : ℝ, 0 < η → ∃ u₀ ∈ Ioo ui 0,
      ∀ p ∈ origDomain ui, u₀ ≤ p.1 → |e| * S.r p.1 p.2 * ‖S.phi p.1 p.2‖ ≤ η) := by
  exact charged_rphi_small_of_terminal ui e S h hs
    (charged_terminal_equivalence ui e S h) (Amplitude.optical_upper ui e S h)

end EmcsfAcExtension.Global
