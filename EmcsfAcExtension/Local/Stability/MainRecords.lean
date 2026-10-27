module

public import EmcsfAcExtension.Local.Defs.Setting

/-! # Difference conclusions consumed by the stability closure

These records are inputs to conditional helpers only. Their fields are
conclusions of internal project record, with constants fixed before the pair.
-/

public section

open Set Complex MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- Outgoing and incoming ratio comparisons consumed from internal project record.
`C` is fixed before all pair parameters. The incoming phase remainder is retained. -/
structure RatioDifferences (C e T ε M Δ₀ : ℝ) (S₁ S₂ : Fields) : Prop where
  /-- Pointwise outgoing ratio comparison. -/
  out_pointwise : ∀ p ∈ triangle 0 T,
    ‖S₁.theta p.1 p.2 / (S₁.lam p.1 p.2 : ℂ) -
      S₂.theta p.1 p.2 / (S₂.lam p.1 p.2 : ℂ)‖ ≤
        C * ((jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal)
  /-- Incoming ratio comparison including the covariant phase difference. -/
  in_pointwise : ∀ p ∈ triangle 0 T,
    ‖S₁.xi p.1 p.2 / (S₁.nu p.1 p.2 : ℂ) -
      S₂.xi p.1 p.2 / (S₂.nu p.1 p.2 : ℂ)‖ ≤
        C * ((kDist e T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal +
          sigma e M T * ε / M * ((jDist T S₁ S₂).toReal +
            ε * (geomDist T S₁ S₂).toReal + ε * Δ₀ / M))
  /-- Complete outgoing weighted ratio-difference budget. -/
  out_hardy : ∀ u ∈ Icc 0 T,
    (∫⁻ v in Icc u T, ENNReal.ofReal (S₁.lam u v / S₁.r u v *
      ‖S₁.theta u v / (S₁.lam u v : ℂ) - S₂.theta u v / (S₂.lam u v : ℂ)‖)) ≤
        ENNReal.ofReal (C * ((jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal))
  /-- Complete incoming weighted ratio-difference budget. -/
  in_hardy : ∀ v ∈ Icc 0 T,
    (∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₁.nu u v / S₁.r u v *
      ‖S₁.xi u v / (S₁.nu u v : ℂ) - S₂.xi u v / (S₂.nu u v : ℂ)‖)) ≤
        ENNReal.ofReal (C * ((kDist e T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal +
          sigma e M T * ε / M * ((jDist T S₁ S₂).toReal +
            ε * (geomDist T S₁ S₂).toReal + ε * Δ₀ / M)))

/-- Scalar and outgoing normalized-field comparison consumed from internal project record.
The fixed constant `C` has no dependence on pair parameters or derivative suprema. -/
structure FieldDifference (C T ε Δ₀ : ℝ) (S₁ S₂ : Fields) : Prop where
  /-- Pointwise projection of the two uniform field estimates. -/
  bound : ∀ p ∈ triangle 0 T,
    ‖S₁.a p.1 p.2 - S₂.a p.1 p.2‖ + ‖S₁.phi p.1 p.2 - S₂.phi p.1 p.2‖ ≤
      C * (Δ₀ + (jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal)

/-- Unabsorbed geometry comparison consumed from internal project record.
The constant is fixed before all pair parameters as in internal project record. -/
structure GeometryDifference (C e T ε M Δ₀ : ℝ) (S₁ S₂ : Fields) : Prop where
  /-- Geometric feedback inequality before simultaneous absorption. -/
  bound : (geomDist T S₁ S₂).toReal ≤
    C * ε * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
      C * sigma e M T * Δ₀ + C * (ε ^ 2 + sigma e M T) * (geomDist T S₁ S₂).toReal

end EmcsfAcExtension.Local.Stab
