module

public import EmcsfAcExtension.Local.Defs.Recon

/-! # Incoming Picard updates

Literal internal definitions from internal project record and
`source/charged_SF_new_version.tex`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

namespace Recon

variable (e : ℝ) (lam : ℝ → ℝ → ℝ) (hh : ℝ → ℝ → ℂ)

/-- [def-node restart-null-picard-lambda]
Incoming Picard update for `λ` from the cone `u = u₀` with datum `λ₀`
(charged_SF_new_version.tex:L5975–5980; `u₀ = 0`, `λ₀ = 1/2` initially,
later cones charged_SF_new_version.tex:L5991–5992). -/
noncomputable def picardLam (u₀ : ℝ) (lam₀ : ℝ → ℝ) (u v : ℝ) : ℝ :=
  lam₀ v * Real.exp (∫ s in u₀..u, nu e lam hh s v / r lam s v * z e lam hh s v)

/-- Unfold `picardLam` to its literal internal project record formula. -/
theorem picardLam_def (u₀ : ℝ) (lam₀ : ℝ → ℝ) (u v : ℝ) :
    picardLam e lam hh u₀ lam₀ u v =
  lam₀ v * Real.exp (∫ s in u₀..u, nu e lam hh s v / r lam s v * z e lam hh s v) := rfl

/-- [def-node restart-null-picard-h]
Unitary incoming Picard update for `h = α/λ` from the cone `u = u₀` with datum `h₀`
(restart-null-picard-h, charged_SF_new_version.tex:L5981–5990). -/
noncomputable def picardH (u₀ : ℝ) (h₀ : ℝ → ℂ) (u v : ℝ) : ℂ :=
  Complex.exp (-(I * e * ∫ s in u₀..u, A e lam hh s v)) * h₀ v +
    ∫ s in u₀..u, Complex.exp (-(I * e * ∫ t in s..u, A e lam hh t v)) *
      (((-nu e lam hh s v / r lam s v : ℝ) : ℂ) *
        ((z e lam hh s v : ℂ) * ratio lam hh s v +
          I * e * Q e lam hh s v * phi lam hh s v / (1 - (mu e lam hh s v : ℂ))))

/-- Unfold `picardH` to its literal internal project record formula. -/
theorem picardH_def (u₀ : ℝ) (h₀ : ℝ → ℂ) (u v : ℝ) :
    picardH e lam hh u₀ h₀ u v =
  Complex.exp (-(I * e * ∫ s in u₀..u, A e lam hh s v)) * h₀ v +
    ∫ s in u₀..u, Complex.exp (-(I * e * ∫ t in s..u, A e lam hh t v)) *
      (((-nu e lam hh s v / r lam s v : ℝ) : ℂ) *
        ((z e lam hh s v : ℂ) * ratio lam hh s v +
          I * e * Q e lam hh s v * phi lam hh s v / (1 - (mu e lam hh s v : ℂ)))) := rfl

end Recon

end EmcsfAcExtension.Local
