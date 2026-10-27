module

public import EmcsfAcExtension.Local.Assembly.Inputs

import EmcsfAcExtension.Local.Assembly.Support
import EmcsfAcExtension.Local.Api.Mono

/-! # Root B assembly from explicit Limit-layer contracts

The existence and stability constants are combined before any data are introduced.
Broad uniqueness identifies arbitrary competitors with constructed limits, including
on shorter triangles. The root remains conditional until the sealed provider
supplies the two Limit-layer inputs.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [internal] The frozen Root B conclusion assembled from the two Limit exports.
The positive thresholds are `min ε₃ ε₄` and `min δ₃ δ₄`, and the bound constant is
`max C₃ C₄`, all chosen before and independent of `T, e`, data and solutions (internal project
record).
Uses internal project record L798–L838. This conditional helper closes no
root node; the sealed provider must discharge both input propositions. -/
theorem restart_local_main_of_limit (hex : AcDataExistenceStmt)
    (hst : LimitClassStabilityStmt) :
    ∃ ε₀ δ₀ C : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ T e : ℝ, 0 < T →
    -- existence on the closed triangle, bounds, and uniqueness in the broad class
    (∀ h : ℝ → ℂ, AbsolutelyContinuousOnInterval h 0 T →
      datumVar h T ≤ ε₀ → |e| * (T / 2) * (1 + ‖h 0‖ + 10 * datumVar h T) ≤ δ₀ →
      ∃ S : Fields,
        IsSolution e S (triangle 0 T) ∧
        (∀ v ∈ Icc 0 T, S.r 0 v = v / 2 ∧ S.a 0 v = h v) ∧
        (∀ t ∈ Icc 0 T, S.A t t = 0) ∧
        (∀ u ∈ Icc 0 T, AbsolutelyContinuousOnInterval (S.a u) u T) ∧
        (∀ v ∈ Icc 0 T, AbsolutelyContinuousOnInterval (fun u => S.b u v) 0 v) ∧
        AbsolutelyContinuousOnInterval (fun t => S.phi t t) 0 T ∧
        (⨆ u ∈ Icc 0 T, eVariationOn (S.a u) (Icc u T)) +
            (⨆ v ∈ Icc 0 T, covVarIn e S.A S.b 0 v v) ≤
          ENNReal.ofReal (C * datumVar h T) ∧
        (∀ p ∈ triangle 0 T,
          ‖S.phi p.1 p.2‖ ≤ 1 + ‖h 0‖ + 10 * datumVar h T ∧
          ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ + ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤
            C * datumVar h T ∧
          |S.lam p.1 p.2 - 1 / 2| + |S.nu p.1 p.2 + 1 / 2| + S.mu p.1 p.2 ≤
            C * datumVar h T ^ 2 ∧
          |S.Q p.1 p.2| ≤
            C * |e| * (1 + ‖h 0‖ + 10 * datumVar h T) * datumVar h T * S.r p.1 p.2 ^ 2) ∧
        (∀ u ∈ Icc 0 T,
          eVariationOn (S.lam u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (S.nu u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (S.mu u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (S.Omega2 u) (Icc u T) ≤ ENNReal.ofReal (C * datumVar h T ^ 2)) ∧
        (∀ v ∈ Icc 0 T,
          eVariationOn (fun u => S.lam u v) (Icc 0 v) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (fun u => S.nu u v) (Icc 0 v) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (fun u => S.mu u v) (Icc 0 v) ≤ ENNReal.ofReal (C * datumVar h T ^ 2) ∧
          eVariationOn (fun u => S.Omega2 u v) (Icc 0 v) ≤
            ENNReal.ofReal (C * datumVar h T ^ 2)) ∧
        (∀ u ∈ Icc 0 T,
          AbsolutelyContinuousOnInterval (S.lam u) u T ∧
          AbsolutelyContinuousOnInterval (S.nu u) u T ∧
          AbsolutelyContinuousOnInterval (S.mu u) u T ∧
          AbsolutelyContinuousOnInterval (S.Omega2 u) u T) ∧
        (∀ v ∈ Icc 0 T,
          AbsolutelyContinuousOnInterval (fun u => S.lam u v) 0 v ∧
          AbsolutelyContinuousOnInterval (fun u => S.nu u v) 0 v ∧
          AbsolutelyContinuousOnInterval (fun u => S.mu u v) 0 v ∧
          AbsolutelyContinuousOnInterval (fun u => S.Omega2 u v) 0 v) ∧
        ContDiffOn ℝ 1 (Function.uncurry S.r) (triangle 0 T) ∧
        (⨆ v ∈ Icc 0 T, eVariationOn (fun u => S.b u v) (Icc 0 v)) ≤
          ENNReal.ofReal (C * datumVar h T) ∧
        (∀ T' ∈ Ioc 0 T, ∀ S' : Fields, IsSolution e S' (triangle 0 T') →
          (∀ v ∈ Icc 0 T', S'.r 0 v = v / 2 ∧ S'.a 0 v = h v) →
          (∀ t ∈ Icc 0 T', S'.A t t = 0) → S'.EqOn S (triangle 0 T'))) ∧
    -- Lipschitz stability in `W^{1,1}` of the datum, fixed gauge
    (∀ (h₁ h₂ : ℝ → ℂ) (S₁ S₂ : Fields),
      AbsolutelyContinuousOnInterval h₁ 0 T → datumVar h₁ T ≤ ε₀ →
      |e| * (T / 2) * (1 + ‖h₁ 0‖ + 10 * datumVar h₁ T) ≤ δ₀ →
      AbsolutelyContinuousOnInterval h₂ 0 T → datumVar h₂ T ≤ ε₀ →
      |e| * (T / 2) * (1 + ‖h₂ 0‖ + 10 * datumVar h₂ T) ≤ δ₀ →
      IsSolution e S₁ (triangle 0 T) → (∀ v ∈ Icc 0 T, S₁.r 0 v = v / 2 ∧ S₁.a 0 v = h₁ v) →
      (∀ t ∈ Icc 0 T, S₁.A t t = 0) →
      IsSolution e S₂ (triangle 0 T) → (∀ v ∈ Icc 0 T, S₂.r 0 v = v / 2 ∧ S₂.a 0 v = h₂ v) →
      (∀ t ∈ Icc 0 T, S₂.A t t = 0) →
      (∃ J K : ℝ → ℝ, IntegrableOn J (Icc 0 T) ∧ IntegrableOn K (Icc 0 T) ∧
        (∀ u ∈ Icc 0 T, ∀ᵐ v ∂(volume.restrict (Icc u T)),
          ‖jOut S₁ u v - jOut S₂ u v‖ ≤ J v) ∧
        (∀ v ∈ Icc 0 T, ∀ᵐ u ∂(volume.restrict (Icc 0 v)),
          ‖kIn e S₁ u v - kIn e S₂ u v‖ ≤ K u) ∧
        ∀ p₁ ∈ triangle 0 T, ∀ p₂ ∈ triangle 0 T, ∀ p₃ ∈ triangle 0 T, ∀ p₄ ∈ triangle 0 T,
          (∫ v in (0 : ℝ)..T, J v) + (∫ u in (0 : ℝ)..T, K u) +
            (|S₁.lam p₁.1 p₁.2 - S₂.lam p₁.1 p₁.2| + |S₁.nu p₁.1 p₁.2 - S₂.nu p₁.1 p₁.2| +
              |S₁.r p₁.1 p₁.2 - S₂.r p₁.1 p₁.2| / S₁.r p₁.1 p₁.2) +
            ‖S₁.a p₂.1 p₂.2 - S₂.a p₂.1 p₂.2‖ + ‖S₁.b p₃.1 p₃.2 - S₂.b p₃.1 p₃.2‖ +
            ‖S₁.phi p₄.1 p₄.2 - S₂.phi p₄.1 p₄.2‖ ≤
          C * (‖h₁ 0 - h₂ 0‖ + datumVar (h₁ - h₂) T)) ∧
      (⨆ u ∈ Icc 0 T, eVariationOn (fun v => S₁.a u v - S₂.a u v) (Icc u T)) +
          (⨆ v ∈ Icc 0 T, eVariationOn (fun u => S₁.b u v - S₂.b u v) (Icc 0 v)) ≤
        ENNReal.ofReal (C * (‖h₁ 0 - h₂ 0‖ + datumVar (h₁ - h₂) T))) := by
  obtain ⟨ε₃, δ₃, C₃, hε₃, hδ₃, hC₃, hexists⟩ := hex
  obtain ⟨ε₄, δ₄, C₄, hε₄, hδ₄, hC₄, hstab⟩ := hst
  refine ⟨min ε₃ ε₄, min δ₃ δ₄, max C₃ C₄, lt_min hε₃ hε₄, lt_min hδ₃ hδ₄,
    lt_max_of_lt_left hC₃, ?_⟩
  intro T e hT
  -- the constructed solution for any small datum
  have hcon : ∀ h : ℝ → ℂ, AbsolutelyContinuousOnInterval h 0 T →
      datumVar h T ≤ min ε₃ ε₄ → |e| * (T / 2) * (1 + ‖h 0‖ + 10 * datumVar h T) ≤ min δ₃ δ₄ →
      ∃ S : Fields, IsSolution e S (triangle 0 T) ∧ IsRestartData S h T ∧
        IsConstructedLimit e T h S ∧ ExistenceBounds (max C₃ C₄) e T h S := by
    intro h hac hε hδ
    obtain ⟨S, hS, hd, hl, hb⟩ :=
      hexists T e h hT hac (hε.trans (min_le_left _ _)) (hδ.trans (min_le_left _ _))
    exact ⟨S, hS, hd, hl, hb.mono (le_max_left _ _)⟩
  refine ⟨?_, ?_⟩
  · intro h hac hε hδ
    obtain ⟨S, hS, hd, -, hb⟩ := hcon h hac hε hδ
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hb
    refine ⟨S, hS, hd.1, hd.2, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, ?_⟩
    intro T' hT' S' hS' hd' hg'
    exact broad_uniqueness_restart hT'.1 hS' (isSolution_mono hS (triangle_subset_triangle hT'.2))
      ⟨hd', hg'⟩ (isRestartData_mono hd hT'.2)
  · intro h₁ h₂ S₁ S₂ hac₁ hε₁ hδ₁ hac₂ hε₂ hδ₂ hS₁ hd₁ hg₁ hS₂ hd₂ hg₂
    obtain ⟨S₁', hS₁', hd₁', hl₁, -⟩ := hcon h₁ hac₁ hε₁ hδ₁
    obtain ⟨S₂', hS₂', hd₂', hl₂, -⟩ := hcon h₂ hac₂ hε₂ hδ₂
    have e₁ : S₁.EqOn S₁' (triangle 0 T) := broad_uniqueness_restart hT hS₁ hS₁' ⟨hd₁, hg₁⟩ hd₁'
    have e₂ : S₂.EqOn S₂' (triangle 0 T) := broad_uniqueness_restart hT hS₂ hS₂' ⟨hd₂, hg₂⟩ hd₂'
    have hc := hstab T e h₁ h₂ S₁' S₂' hT hac₁ (hε₁.trans (min_le_right _ _))
      (hδ₁.trans (min_le_right _ _)) hac₂ (hε₂.trans (min_le_right _ _))
      (hδ₂.trans (min_le_right _ _)) hl₁ hl₂
    exact StabConclusion.congr e₁ e₂ (hc.mono (le_max_right _ _))

end EmcsfAcExtension.Local
