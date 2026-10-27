module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.AssemblyIdentity

/-! # Exact difference transport for the outgoing renormalized derivative

The ordinary incoming derivative retains the difference of the two
connections explicitly. Both scalar and electromagnetic source primitives
are those of the approved literal curvature split.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Stab

/-- Subtraction of the two j transports in the common fixed gauge.
This identity introduces no source estimate and no frame identification. -/
theorem j_difference_transport {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hset₁ : StabSetting e T ε M A S₁ h₁) (hset₂ : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    let j₁ := jC1 (triangle 0 T) S₁
    let j₂ := jC1 (triangle 0 T) S₂
    let c₁ := -‖S₁.xi u v‖ ^ 2 / (S₁.nu u v * S₁.r u v)
    let c₂ := -‖S₂.xi u v‖ ^ 2 / (S₂.nu u v * S₂.r u v)
    let s₁ := (S₁.nu u v : ℂ) * S₁.theta u v / (S₁.r u v : ℂ) ^ 2 *
      (curvScalar (triangle 0 T) S₁ u v +
        2 * starRingEnd ℂ (curvScalar (triangle 0 T) S₁ u v))
    let s₂ := (S₂.nu u v : ℂ) * S₂.theta u v / (S₂.r u v : ℂ) ^ 2 *
      (curvScalar (triangle 0 T) S₂ u v +
        2 * starRingEnd ℂ (curvScalar (triangle 0 T) S₂ u v))
    let E₁ := (S₁.nu u v : ℂ) * S₁.theta u v / (S₁.r u v : ℂ) ^ 2 *
      (curvEM e S₁ u v + 2 * starRingEnd ℂ (curvEM e S₁ u v)) + emSourceJ e S₁ u v
    let E₂ := (S₂.nu u v : ℂ) * S₂.theta u v / (S₂.r u v : ℂ) ^ 2 *
      (curvEM e S₂ u v + 2 * starRingEnd ℂ (curvEM e S₂ u v)) + emSourceJ e S₂ u v
    HasDerivWithinAt (fun x => j₁ x v - j₂ x v)
      ((c₁ : ℂ) * (j₁ u v - j₂ u v) - I * e * S₁.A u v * (j₁ u v - j₂ u v) +
        ((c₁ - c₂ : ℝ) : ℂ) * j₂ u v - I * e * (S₁.A u v - S₂.A u v) * j₂ u v +
        (s₁ - s₂) + (E₁ - E₂)) (Icc 0 v) u := by
  dsimp only
  have ht₁ := stab_j_transport_split hset₁.c1 hu huv hvT
  have ht₂ := stab_j_transport_split hset₂.c1 hu huv hvT
  convert ht₁.sub ht₂ using 1
  push_cast
  ring

end EmcsfAcExtension.Local.Stab
