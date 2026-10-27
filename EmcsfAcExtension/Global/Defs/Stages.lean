module

public import Mathlib
public import EmcsfAcExtension.Frozen.Fields.Mu
public import EmcsfAcExtension.Frozen.OrigDomain
public import EmcsfAcExtension.Frozen.Fields.NormalizedOut
public import EmcsfAcExtension.Frozen.Fields.NormalizedIn

/-! # Root A Stages

Literal objects from internal project record, adopted by internal project record.
Source: `source/charged_SF_new_version.tex`; individual declarations give line references.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [internal]
Finite cylinder and connector path, charged_SF_new_version.tex:L3835–L3928 and L3899–L3932. -/
structure FiniteBoundary (S : Fields) (ui u₀ u₁ v₀ ρ : ℝ) (vb : ℝ → ℝ) (N : ℕ) where
  /-- Stage cut labels. -/
  cuts : Fin (N + 1) → ℝ
  /-- Cooling endpoints. -/
  cool : Fin N → ℝ
  /-- Stage cylinder radii. -/
  radii : Fin N → ℝ
  /-- First cut equals the entry label. -/
  first : cuts 0 = u₀
  /-- Last cut equals the finite cutoff. -/
  last : cuts (Fin.last N) = u₁
  /-- Cuts are ordered. -/
  ordered : Monotone cuts
  /-- The cooling endpoint lies inside its stage. -/
  split : ∀ n, cuts n.castSucc ≤ cool n ∧ cool n ≤ cuts n.succ
  /-- Initial outgoing boundary label. -/
  entry_label : vb u₀ = v₀
  /-- The boundary lies in the original development. -/
  mem : ∀ u ∈ Icc u₀ u₁, (u, vb u) ∈ origDomain ui
  /-- The boundary stays off the axis. -/
  off_axis : ∀ u ∈ Icc u₀ u₁, u < vb u
  /-- Continuous boundary graph. -/
  cont : ContinuousOn vb (Icc u₀ u₁)
  /-- Nondecreasing boundary graph. -/
  mono : MonotoneOn vb (Icc u₀ u₁)
  /-- Positive cylinder radii. -/
  radius_pos : ∀ n, 0 < radii n
  /-- Constant radius during each cylinder stage. -/
  cylinder : ∀ n, ∀ u ∈ Icc (cuts n.castSucc) (cool n), S.r u (vb u) = radii n
  /-- C¹ cylinder graph. -/
  cylinder_c1 : ∀ n, ContDiffOn ℝ 1 vb (Icc (cuts n.castSucc) (cool n))
  /-- Cylinder slope almost everywhere. -/
  cylinder_rate : ∀ n, ∀ᵐ u ∂volume.restrict (Icc (cuts n.castSucc) (cool n)),
    deriv vb u = -S.nu u (vb u) / S.lam u (vb u)
  /-- Constant outgoing label during each connector. -/
  connector : ∀ n, ∀ u ∈ Icc (cool n) (cuts n.succ), vb u = vb (cool n)
  /-- Radius range throughout a stage. -/
  radius_range : ∀ n, ∀ u ∈ Icc (cuts n.castSucc) (cuts n.succ),
    ρ * radii n ≤ S.r u (vb u) ∧ S.r u (vb u) ≤ radii n

/-- [internal]
Shared finite-stage boundary budgets, charged_SF_new_version.tex:L3899–L3932. -/
def BoundaryBudgets (S : Fields) (ui u₀ u₁ v₀ ρ : ℝ) (vb : ℝ → ℝ) (N : ℕ)
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E : Fin N → ℝ) : Prop :=
  ∀ n, 0 ≤ E n ∧
    (∀ u ∈ Icc (B.cuts n.castSucc) (B.cuts n.succ),
      S.m u (vb u) / S.r u (vb u) +
        ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 ≤ E n) ∧
    (∫ u in (B.cuts n.castSucc)..(B.cuts n.succ),
      (‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ ^ 2 +
       ‖S.xi u (vb u) / (S.nu u (vb u) : ℂ)‖ ^ 2 + S.mu u (vb u) ^ 2) *
        (-S.nu u (vb u)) / S.r u (vb u)) ≤ E n

/-- [internal]
Universal gap constant, independent of coupling and data, charged_SF_new_version.tex:L1515. -/
noncomputable def gapConstant : ℝ := Real.exp (-32) / 256

/-- [internal]
Geometric stage radii, charged_SF_new_version.tex:L3899–L3928. -/
noncomputable def stageRadius (ρ b₀ : ℝ) (n : ℕ) : ℝ := ρ ^ n * b₀

/-- Unfold `stageRadius` to the source formula above. -/
theorem stageRadius_def (ρ b₀ : ℝ) (n : ℕ) :
    stageRadius ρ b₀ n = ρ ^ n * b₀ := rfl

/-- [internal]
Recursive stage energy envelope, charged_SF_new_version.tex:L3899–L3928. -/
noncomputable def energyEnvelope (χ C ε₀ : ℝ) (σ : ℕ → ℝ) : ℕ → ℝ
  | 0 => ε₀
  | n + 1 => χ * energyEnvelope χ C ε₀ σ n + C * σ n ^ 2

/-- [internal]
Prescribed stage budget, charged_SF_new_version.tex:L3899–L3928. -/
noncomputable def stageBudget (Cbudget χ C ε₀ : ℝ) (σ : ℕ → ℝ) (n : ℕ) : ℝ :=
  Cbudget * (energyEnvelope χ C ε₀ σ n + σ n ^ 2)

/-- [internal]
Prescribed stage clock duration, charged_SF_new_version.tex:L4074–L4079. -/
noncomputable def stageDuration (H ρ b₀ χ C ε₀ : ℝ) (σ : ℕ → ℝ) (n : ℕ) : ℝ :=
  H * stageRadius ρ b₀ n / energyEnvelope χ C ε₀ σ n

end EmcsfAcExtension.Global
