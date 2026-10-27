module

public import EmcsfAcExtension.Local.Defs.Envelope
public import EmcsfAcExtension.Frozen.CovVarIn
public import EmcsfAcExtension.Frozen.Fields.Omega2

/-! # Smooth a priori and stability conclusion bundles

Literal internal definitions from internal project record and
`source/charged_SF_new_version.tex`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Conclusions of the smooth a priori theorem (restart-sec-independent-null-construction#
smooth-apriori-box, charged_SF_new_version.tex:L6201–6254, with restart-bv-envelope-final,
  restart-bv-geometry-TV,
restart-bv-Q-bounds, restart-sec-independent-area#ordinary-incoming-variation) on `𝒟_T`. -/
structure SmoothBounds (C e T ε M : ℝ) (S : Fields) : Prop where
  /-- The `geom` clause of `SmoothBounds` in internal project record. -/
  geom : ∀ p ∈ triangle 0 T,
    |S.lam p.1 p.2 - 1 / 2| + |S.nu p.1 p.2 + 1 / 2| + S.mu p.1 p.2 ≤ C * ε ^ 2
  /-- The `mu_nonneg` clause of `SmoothBounds` in internal project record. -/
  mu_nonneg : ∀ p ∈ triangle 0 T, 0 ≤ S.mu p.1 p.2
  /-- The `phi_le` clause of `SmoothBounds` in internal project record. -/
  phi_le : ∀ p ∈ triangle 0 T, ‖S.phi p.1 p.2‖ ≤ M
  /-- The `ratio` clause of `SmoothBounds` in internal project record. -/
  ratio : ∀ p ∈ triangle 0 T,
    ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ + ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ C * ε
  /-- The `charge` clause of `SmoothBounds` in internal project record. -/
  charge : ∀ p ∈ triangle 0 T, |S.Q p.1 p.2| ≤ C * |e| * M * ε * S.r p.1 p.2 ^ 2
  /-- The `env` clause of `SmoothBounds` in internal project record. -/
  env : (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) v) +
      (∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) u) ≤ ENNReal.ofReal (C * ε)
  /-- The `tvj` clause of `SmoothBounds` in internal project record. -/
  tvj : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T → eVariationOn (S.a u) (Icc u v) ≤
    ENNReal.ofReal (C * ∫ s in u..v, (outEnv 0 (jC1 (triangle 0 T) S) s).toReal)
  /-- The `tvk` clause of `SmoothBounds` in internal project record. -/
  tvk : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T → covVarIn e S.A S.b u v v ≤
    ENNReal.ofReal (C * ∫ s in u..v, (inEnv T (kC1 e (triangle 0 T) S) s).toReal)
  /-- The `tv_in` clause of `SmoothBounds` in internal project record. -/
  tv_in : ∀ v ∈ Icc 0 T, eVariationOn (fun u => S.b u v) (Icc 0 v) ≤ ENNReal.ofReal (C * ε)
  /-- The `geomTV_out` clause of `SmoothBounds` in internal project record. -/
  geomTV_out : ∀ u ∈ Icc 0 T,
    eVariationOn (S.lam u) (Icc u T) + eVariationOn (S.nu u) (Icc u T) +
      eVariationOn (S.mu u) (Icc u T) + eVariationOn (S.Omega2 u) (Icc u T) ≤
        ENNReal.ofReal (C * ε ^ 2)
  /-- The `geomTV_in` clause of `SmoothBounds` in internal project record. -/
  geomTV_in : ∀ v ∈ Icc 0 T,
    eVariationOn (fun u => S.lam u v) (Icc 0 v) + eVariationOn (fun u => S.nu u v) (Icc 0 v) +
      eVariationOn (fun u => S.mu u v) (Icc 0 v) +
        eVariationOn (fun u => S.Omega2 u v) (Icc 0 v) ≤ ENNReal.ofReal (C * ε ^ 2)
  /-- The `geomEnv` clause of `SmoothBounds` in internal project record. -/
  geomEnv : (∫⁻ v in Icc 0 T, outEnv 0 (geomL (triangle 0 T) S) v) +
      (∫⁻ u in Icc 0 T, inEnv T (geomN (triangle 0 T) S) u) ≤ ENNReal.ofReal (C * ε ^ 2)
  /-- The `crossTV` clause of `SmoothBounds` in internal project record. -/
  crossTV : (∀ v ∈ Icc 0 T, eVariationOn (fun u => S.a u v) (Icc 0 v) ≤ ENNReal.ofReal C) ∧
    ∀ u ∈ Icc 0 T, eVariationOn (S.b u) (Icc u T) ≤ ENNReal.ofReal C
  /-- Localized outgoing Hardy estimate of internal project record
  (charged_SF_new_version.tex:L4606). -/
  hardyOut : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T → ∫⁻ w in Icc u v,
      ENNReal.ofReal (S.lam u w / S.r u w * ‖S.theta u w / S.lam u w‖) ≤
    ENNReal.ofReal (C * ∫ s in u..v, (outEnv 0 (jC1 (triangle 0 T) S) s).toReal)
  /-- Localized incoming Hardy estimate of internal project record
  (charged_SF_new_version.tex:L4606). -/
  hardyIn : ∀ u v, 0 ≤ u → u ≤ v → v ≤ T → ∫⁻ w in Icc u v,
      ENNReal.ofReal (-S.nu w v / S.r w v * ‖S.xi w v / S.nu w v‖) ≤
    ENNReal.ofReal (C * ∫ s in u..v, (inEnv T (kC1 e (triangle 0 T) S) s).toReal)
  /-- The `massFlux` clause of `SmoothBounds` in internal project record. -/
  massFlux : (∀ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
      ENNReal.ofReal (S.lam u v * S.mu u v / S.r u v) ≤ ENNReal.ofReal (C * ε ^ 2)) ∧
    ∀ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
      ENNReal.ofReal (-S.nu u v * S.mu u v / S.r u v) ≤ ENNReal.ofReal (C * ε ^ 2)

/-- Conclusions of the smooth two-solution stability theorem (restart-stab-main-lipschitz,
charged_SF_new_version.tex:L5366–5371, with restart-stab-charge-difference,
restart-stab-potential-difference,
#mass-Volterra-difference, #scalar-characteristic-strong-W11, #pure-geometric-derivatives-strong).
The charge and potential clauses follow architecture internal project record. The constant `C`
may depend only on the envelope constant of the stability setting, uniformly in
`e`, `T`, `M`, the data and the two solutions. -/
structure StabBounds (C e T M Δ₀ : ℝ) (S₁ S₂ : Fields) : Prop where
  /-- The `main` clause of `StabBounds` in internal project record. -/
  main : jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ + supDist T S₁.a S₂.a +
      supDist T S₁.b S₂.b + supDist T S₁.phi S₂.phi ≤ ENNReal.ofReal (C * Δ₀)
  /-- The dimensionless mass-ratio difference, as specified by internal project record. -/
  extra_mu : supDist T S₁.mu S₂.mu ≤ ENNReal.ofReal (C * Δ₀)
  /-- The radius-weighted charge difference off the axis, as specified by internal project record.
  -/
  extra_Q : ∀ p ∈ triangle 0 T, p.1 < p.2 →
      |S₁.Q p.1 p.2 - S₂.Q p.1 p.2| / S₁.r p.1 p.2 ^ 2 ≤ C * |e| * M * Δ₀
  /-- The potential difference with its charged length scale, as specified by internal project
  record. -/
  extra_A : supDist T S₁.A S₂.A ≤ ENNReal.ofReal (C * |e| * T * M * Δ₀)
  /-- The `tv` clause of `StabBounds` in internal project record. -/
  tv : (⨆ u ∈ Icc 0 T, eVariationOn (fun v => S₁.a u v - S₂.a u v) (Icc u T)) +
      (⨆ v ∈ Icc 0 T, eVariationOn (fun u => S₁.b u v - S₂.b u v) (Icc 0 v)) ≤
        ENNReal.ofReal (C * Δ₀)
  /-- The `geomStrong` clause of `StabBounds` in internal project record. -/
  geomStrong : (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
        ‖pdV (triangle 0 T) S₁.lam u v - pdV (triangle 0 T) S₂.lam u v‖ₑ) +
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖pdU (triangle 0 T) S₁.nu u v - pdU (triangle 0 T) S₂.nu u v‖ₑ) ≤
          ENNReal.ofReal (C * Δ₀)

  /-- Pairwise weighted scalar differences `H_{z,+} + H_{z,-}` (internal project record). -/
  hardyDiff : (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal (S₁.lam u v / S₁.r u v *
      ‖S₁.theta u v / S₁.lam u v - S₂.theta u v / S₂.lam u v‖)) +
    (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₁.nu u v / S₁.r u v *
      ‖S₁.xi u v / S₁.nu u v - S₂.xi u v / S₂.nu u v‖)) ≤ ENNReal.ofReal (C * Δ₀)

  /-- Pairwise weighted mass-ratio differences `H_{μ,+} + H_{μ,-}` (internal project record). -/
  muFluxDiff : (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal (S₁.lam u v / S₁.r u v *
      |S₁.mu u v - S₂.mu u v|)) +
    (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal (-S₁.nu u v / S₁.r u v *
      |S₁.mu u v - S₂.mu u v|)) ≤ ENNReal.ofReal (C * Δ₀)

  /-- Renormalized geometric envelope difference (internal project record). -/
  geomEnvDiff : (∫⁻ v in Icc 0 T, outEnv 0 (fun u v => geomL (triangle 0 T) S₁ u v -
      geomL (triangle 0 T) S₂ u v) v) +
    (∫⁻ u in Icc 0 T, inEnv T (fun u v => geomN (triangle 0 T) S₁ u v -
      geomN (triangle 0 T) S₂ u v) u) ≤ ENNReal.ofReal (C * Δ₀)

  /-- Incoming scalar-ratio difference over the triangle (internal project record G3+A12p, internal
  project record). -/
  xiRatioArea : (∫⁻ p in triangle 0 T, ENNReal.ofReal
      (‖S₁.xi p.1 p.2 / S₁.nu p.1 p.2 - S₂.xi p.1 p.2 / S₂.nu p.1 p.2‖ / (p.2 - p.1))) ≤
    ENNReal.ofReal (C * T * Δ₀)

end EmcsfAcExtension.Local
