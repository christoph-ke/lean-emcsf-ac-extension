module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.AssemblyIdentity
import EmcsfAcExtension.Local.Calculus.AxisMatch
import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # Exact difference transport for the incoming renormalized derivative

The outgoing transport has no connection subtraction because the common
gauge has `A_v = 0`. Its real homogeneous coefficient is nonpositive.
-/

public section

open Set Complex MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- Subtraction of the two k transports, with the literal incoming scalar
and charged curvature primitives. The axis boundary is handled separately. -/
theorem k_difference_transport {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hset₁ : StabSetting e T ε M A S₁ h₁) (hset₂ : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    let k₁ := kC1 e (triangle 0 T) S₁
    let k₂ := kC1 e (triangle 0 T) S₂
    let c₁ := -‖S₁.theta u v‖ ^ 2 / (S₁.lam u v * S₁.r u v)
    let c₂ := -‖S₂.theta u v‖ ^ 2 / (S₂.lam u v * S₂.r u v)
    let s₁ := (S₁.lam u v : ℂ) * S₁.xi u v / (S₁.r u v : ℂ) ^ 2 *
      (curvScalarIn e (triangle 0 T) S₁ u v +
        2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S₁ u v))
    let s₂ := (S₂.lam u v : ℂ) * S₂.xi u v / (S₂.r u v : ℂ) ^ 2 *
      (curvScalarIn e (triangle 0 T) S₂ u v +
        2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S₂ u v))
    let E₁ := (S₁.lam u v : ℂ) * S₁.xi u v / (S₁.r u v : ℂ) ^ 2 *
      (curvEMIn e S₁ u v + 2 * starRingEnd ℂ (curvEMIn e S₁ u v)) + emSourceK e S₁ u v
    let E₂ := (S₂.lam u v : ℂ) * S₂.xi u v / (S₂.r u v : ℂ) ^ 2 *
      (curvEMIn e S₂ u v + 2 * starRingEnd ℂ (curvEMIn e S₂ u v)) + emSourceK e S₂ u v
    HasDerivWithinAt (fun x => k₁ u x - k₂ u x)
      ((c₁ : ℂ) * (k₁ u v - k₂ u v) + ((c₁ - c₂ : ℝ) : ℂ) * k₂ u v +
        (s₁ - s₂) + (E₁ - E₂)) (Icc u T) v := by
  dsimp only
  have ht₁ := stab_k_transport_split hset₁.c1 hu huv hvT
  have ht₂ := stab_k_transport_split hset₂.c1 hu huv hvT
  convert ht₁.sub ht₂ using 1
  push_cast
  ring

/-- The matching axis derivative difference has label integral at most
`Δ_j`, with its exact coefficient `1`, uniformly in all pair parameters. -/
theorem k_axis_difference_le_jDist {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hset₁ : StabSetting e T ε M A S₁ h₁) (hset₂ : StabSetting e T ε M A S₂ h₂) :
    (∫⁻ t in Icc 0 T,
      ‖kC1 e (triangle 0 T) S₁ t t - kC1 e (triangle 0 T) S₂ t t‖ₑ) ≤ jDist T S₁ S₂ := by
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  rw [(stab_axis hset₁.pos hset₁.c1 hset₁.data.2 ht).1,
    (stab_axis hset₂.pos hset₂.c1 hset₂.data.2 ht).1]
  exact le_iSup₂_of_le t ⟨ht.1, le_rfl⟩ le_rfl

end EmcsfAcExtension.Local.Stab
