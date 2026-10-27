module

public import EmcsfAcExtension.Global.Exterior.TerminalPackage
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceAggregateTerminal
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceTerminal

/-! # Signed-terminal exterior consumers

Source: `charged_SF_new_version.tex:L1231–1416`; approved internal project record.
The terminal package is discharged before the quantified geometric objects.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The signed terminal hypothesis discharges the terminal estimates in
`charged_exterior_FV_of_terminal`. The fixed adaptive profile precedes
all late rows, carriers and endpoints. Numerical coefficients are universal;
remaining constants depend on the development, signed bound and profile. -/
theorem charged_exterior_fv {ui e : ℝ} {S : Fields}
 (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ)
    {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ u₀ ∈ Ioo ui 0, ∀ u a, (u, a) ∈ adaptiveExterior S ui u₀ ell →
      S.r u a = ell (S.r u 0) → ∀ v ∈ Icc a 0,
        ‖S.theta u v / (S.lam u v : ℂ)‖ ≤
          (eVariationOn (S.a u) (Icc a 0)).toReal +
            4 * Real.sqrt (terminalMass S u / ell (S.r u 0)) := by
  obtain ⟨_, _, hcollapse, _⟩ := terminal_control h hs
  exact charged_exterior_FV_of_terminal h M ell hR hcollapse hmass hell hellsmall hsmall

/-- [node c:exterior#source-quadratic-coupling-bound]
[node c:exterior#source-scalar-charge-bound]
[node c:exterior#source-linear-charge-bound]
[node c:exterior#source-cubic-charge-bound]
The signed terminal hypothesis discharges the terminal estimates in
`source_charge_bounds_of_terminal`. The fixed adaptive profile precedes
all late rows, carriers and endpoints. Numerical coefficients are universal;
remaining constants depend on the development, signed bound and profile. -/
theorem source_charge_bounds {ui e : ℝ} {S : Fields}
 (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ)
    {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ C > 0,
    ∃ u₀ ∈ Ioo ui 0, ∀ u a, (u, a) ∈ adaptiveExterior S ui u₀ ell →
      let L := (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))
      (∫ v in a..0, e ^ 2 * ‖S.phi u v‖ ^ 2 *
        ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v) ≤
          2 * e ^ 2 * L ^ 2 * Real.sqrt (terminalMass S u * terminalRadius S u) ∧
      (∫ v in a..0, |e| * |S.Q u v| * ‖S.phi u v‖ / S.r u v ^ 2 * S.lam u v) ≤
          2 * |e| * L * Real.sqrt (terminalMass S u / S.r u a) ∧
      (∫ v in a..0, |e| * |S.Q u v| / S.r u v ^ 2 *
        ‖S.theta u v / (S.lam u v : ℂ)‖ * S.lam u v) ≤
          4 * |e| * (terminalMass S u / S.r u a) ∧
      (∫ v in a..0, |e| * |S.Q u v| * ‖S.phi u v‖ / S.r u v ^ 2 *
        ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤
          32 * |e| * L * (terminalMass S u / S.r u a) *
            Real.sqrt (terminalMass S u / S.r u a) := by
  obtain ⟨C, hC, hcollapse, hphi⟩ := terminal_control h hs
  exact ⟨C, hC, source_charge_bounds_of_terminal h M ell hR hC hcollapse hmass hell
    hellsmall hsmall hphi⟩

/-- [internal]
The signed terminal hypothesis discharges the terminal estimates in
`charged_exterior_source_bound_of_terminal`. The fixed adaptive profile precedes
all late rows, carriers and endpoints. Numerical coefficients are universal;
remaining constants depend on the development, signed bound and profile. -/
theorem charged_exterior_source_bound {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ)
    {R₀ : ℝ} (hR : 0 < R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ C > 0,
    ∃ u₀ ∈ Ioo ui 0, ∀ u a, (u, a) ∈ adaptiveExterior S ui u₀ ell →
      ∀ SF : ℝ, (∀ v ∈ Icc a 0, ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ SF) →
      let L := (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))
      (∫ v in a..0, ‖rawDensitySource e S u v‖) ≤
        4096 * (-S.nu u 0) *
          (terminalMass S u / S.r u a ^ 2 *
            (SF + Real.sqrt (terminalMass S u / S.r u a)) +
          |e| * L * (terminalMass S u / S.r u a) *
            Real.sqrt (terminalMass S u / S.r u a) +
          |e| * (terminalMass S u / S.r u a) +
          |e| * L * Real.sqrt (terminalMass S u / S.r u a) +
          e ^ 2 * L ^ 2 * Real.sqrt (terminalMass S u * terminalRadius S u)) := by
  obtain ⟨C, hC, hcollapse, hphi⟩ := terminal_control h hs
  exact ⟨C, hC, charged_exterior_source_bound_of_terminal h M ell hR hC hcollapse hmass
    hell hellsmall hsmall hphi⟩

end EmcsfAcExtension.Global.Exterior

namespace EmcsfAcExtension.Global

/-- [node eq:charged-exterior-FV]
Canonical signed-terminal field-versus-variation estimate. The universal
coefficient is `4`, with the cutoff before every later row and label. -/
alias charged_exterior_fv := Exterior.charged_exterior_fv

/-- [node eq:charged-exterior-source-bound]
Canonical signed-terminal source estimate. The universal coefficient is
`4096`, with the scalar constant and cutoff before all later rows. -/
alias charged_exterior_source_bound := Exterior.charged_exterior_source_bound

end EmcsfAcExtension.Global
