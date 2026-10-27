module

public import EmcsfAcExtension.Frozen.Fields.Mu
public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.Params

/-! # Bootstrap and stability boxes

Literal internal definitions from internal project record and
`source/charged_SF_new_version.tex`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The temporary bootstrap assumptions (restart-bv-bootstrap-independent,
  charged_SF_new_version.tex:L4503–4506). -/
def BootBox (S : Fields) (ε M : ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  ∀ p ∈ D, 1 / 4 ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ 1 ∧ 1 / 4 ≤ -S.nu p.1 p.2 ∧
    -S.nu p.1 p.2 ≤ 1 ∧ 1 / 2 ≤ 1 - S.mu p.1 p.2 ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
    ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ 4 * ε ∧ ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ 4 * ε

/-- [internal]
The geometric box of §4.4 (restart-stab-geometry-box, charged_SF_new_version.tex:L4961–4966). -/
def StabBox (S : Fields) (c₀ C₀ ε M : ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  1 ≤ M ∧ ∀ p ∈ D, c₀ ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C₀ ∧ c₀ ≤ -S.nu p.1 p.2 ∧
    -S.nu p.1 p.2 ≤ C₀ ∧ c₀ ≤ 1 - S.mu p.1 p.2 ∧
    ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ + ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ ε ∧ ‖S.phi p.1 p.2‖ ≤ M

/-- [def-node restart-stab-geometry-box]
Complete fixed-coordinate comparison framework (charged_SF_new_version.tex:L4955–4970).
Both fields use the same carrier `D = triangle 0 T`, where `T = 2R`, the same
initial radial gauge and axis labels, and the same numerical box. `IsC1Solution`
supplies the regular axis; `IsRestartData` supplies the initial radius and zero
axis potential. The gauge `A_v = 0` is built into `Fields`. The last clause
identifies the displayed charged parameter. This is an internal predicate under
internal project record and must never be a premise of a frozen statement. -/
def StabGeometryFramework (e T c₀ C₀ ε M σ : ℝ) (D : Set (ℝ × ℝ))
    (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ) : Prop :=
  0 < T ∧ D = triangle 0 T ∧
    IsC1Solution e S₁ D ∧ IsC1Solution e S₂ D ∧
    IsRestartData S₁ h₁ T ∧ IsRestartData S₂ h₂ T ∧
    StabBox S₁ c₀ C₀ ε M D ∧ StabBox S₂ c₀ C₀ ε M D ∧ σ = sigma e M T

end EmcsfAcExtension.Local
