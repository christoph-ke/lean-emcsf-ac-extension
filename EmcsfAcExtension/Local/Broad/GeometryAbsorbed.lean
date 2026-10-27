module

public import EmcsfAcExtension.Local.Broad.Geometry
import EmcsfAcExtension.Local.Broad.GeometryAbsorption

/-! # Absorbed broad geometric comparison at fixed finite variation -/

public section

open Set
open scoped ENNReal

namespace EmcsfAcExtension.Local

open Broad

/-- [node restart-stab-broad-uniqueness#geometry-after-absorption]
Absorb the geometric feedback of charged_SF_new_version.tex:L5820–5827. The positive
constant depends only on the fixed geometric box, before the triangle,
coupling, scalar and variation sizes and both solutions. Only `ε` and the
charged scale are small; `L` is an arbitrary finite nonnegative budget. -/
theorem stab_broad_geometry_absorbed (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε L : ℝ) (S₁ S₂ : Fields), s < t →
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 → ε ^ 2 ≤ 1 / 2 → 0 ≤ L →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧ c ≤ -S.nu p.1 p.2 ∧
        -S.nu p.1 p.2 ≤ C ∧ c ≤ 1 - S.mu p.1 p.2 ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
        ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε ∧ ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ ε) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u v, (u, v) ∈ triangle s t →
        eVariationOn (S.a u) (Icc u v) ≤ ENNReal.ofReal L) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ v ∈ Icc s t,
        eVariationOn (fun x => S.b x v) (Icc s v) ≤ ENNReal.ofReal L) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u ∈ Icc s t, S.A u u = 0) →
      (∀ v ∈ Icc s t, S₁.r s v = S₂.r s v ∧ S₁.a s v = S₂.a s v) →
      e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1 →
      K * ε * (L + 1) ≤ 1 / 2 →
      (geometry_distance s t S₁ S₂).toReal ≤
        K * (L + 1) * (normalized_field_distance s t S₁ S₂).toReal := by
  obtain ⟨K₀, hK₀, hgeom⟩ := stab_broad_geometry c C hc hC
  refine ⟨2 * K₀, by positivity, ?_⟩
  intro s t e M ε L S₁ S₂ hst hS₁ hS₂ hM hε hε1 hsmall hL hbox hosc hvo hvi haxis hdata hσ habs
  have hraw := hgeom s t e M ε L S₁ S₂ hst hS₁ hS₂ hM hε hε1 hsmall hL hbox hosc
    hvo hvi haxis hdata hσ
  have hpos : 0 ≤ K₀ * ε * (L + 1) := by positivity
  have habs' : K₀ * ε * (L + 1) ≤ 1 / 2 := by nlinarith only [habs, hpos]
  exact geometry_after_absorption_of_bound hK₀.le hL hε ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg hσ habs' hraw

end EmcsfAcExtension.Local
