module

public import EmcsfAcExtension.Global.Closure.NodeTagsFinite
import EmcsfAcExtension.Global.Closure.Absorption
import Mathlib.Tactic

/-! # Absorption and strict improvement of the interaction stop

The physical coupled inequalities are supplied by `cc_inequalities`, which
constructs the finite budgets from initial stage energies.
Source: `charged_SF_new_version.tex:L4041–L4052`.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [node eq:cc-closed]
Absorb both physical stopped inequalities and strictly improve `J+S`.
All constants and both tolerances depend only on the fixed geometric,
recurrence and stopping parameters, before physical data, entry row,
cutoff and durations. The entry error is required small only after those
constants have been selected. No source or forcing inequality is assumed.
Source: charged_SF_new_version.tex:L4041–L4052. -/
theorem cc_closed (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Ts δs ηs : ℝ, 0 < Ts ∧ 0 < δs ∧ 0 < ηs ∧
      ∀ (εweak ρ χ C₁ c Λ F : ℝ),
      ExteriorBox δ c Λ F εweak ρ → 0 < ρ →
      0 ≤ χ → χ < 1 → 0 ≤ C₁ → F + εweak ≤ δs →
      ∃ Cbudget Csum εstop η A : ℝ,
      0 < Cbudget ∧ 0 < Csum ∧ 0 < εstop ∧ 0 < η ∧ 0 < A ∧
      ∀ (ui e : ℝ) (S : Fields), OriginalData ui e S → SignedTerminalBound ui S →
      ∃ a ∈ Ioo ui 0,
      ∀ (u₀ u₁ v₀ R₀ εentry : ℝ) (vb : ℝ → ℝ) (σ : ℕ → ℝ)
        (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (T : Fin N → ℝ),
      a ≤ u₀ → 0 < N → 0 ≤ εentry → (∀ n, 0 ≤ σ n) →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F εweak →
      S.r u₀ 0 = R₀ → (∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0) →
      (∀ p ∈ origDomain ui, u₀ ≤ p.1 → 0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
      (∀ n, B.radii n < R₀ / 2) → (∀ n, 0 < T n) →
      ∀ γ : ∀ n, ClockCylinder S (origDomain ui) (B.radii n) 0 (T n),
      (∀ n, (γ n).U 0 = B.cuts n.castSucc ∧ (γ n).U (T n) = B.cool n) →
      (∀ n, ∀ τ ∈ Icc 0 (T n), vb ((γ n).U τ) = (γ n).V τ) →
      (∀ n : Fin N, σ n = (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) →
      (∀ n, cylinderEnergy S (B.radii n) ((γ n).U 0) ((γ n).V 0) / B.radii n ≤
        energyEnvelope χ C₁ εentry σ n) →
      let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
      let V := ∑ n ∈ Finset.range N, σ n
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F εstop S) (2 * R₀)
      J + V ≤ εstop → z ≤ 1 → 9 * z ≤ ηs ^ 2 →
      Csum * (εentry + V ^ 2) ≤ F ^ 2 → εentry + z ≤ η →
      A * ((initialInteraction S u₀ v₀).toReal + εentry + z) < εstop →
      V ≤ A * (J + εentry + z) ∧
      J + V ≤ A * ((initialInteraction S u₀ v₀).toReal + εentry + z) ∧
      J + V < εstop := by
  obtain ⟨Ts, δs, ηs, hTs, hδs, hηs, hineq⟩ := cc_inequalities δ hδ
  refine ⟨Ts, δs, ηs, hTs, hδs, hηs, ?_⟩
  intro εweak ρ χ C₁ c Λ F hbox hρ hχ hχ1 hC₁ hweak
  obtain ⟨Cb, Csum, C, hCb, hCs, hC, hineq⟩ :=
    hineq εweak ρ χ C₁ c Λ F hbox hρ hχ hχ1 hC₁ hweak
  have hc := hbox.2.2.1
  obtain ⟨εabs, η, Aabs, hεabs, hη, hAabsPos, habsorb⟩ :=
    Interaction.stopped_absorption c C F hc hC
      ⟨hbox.2.2.2.2.1, hbox.2.2.2.2.2.1.le⟩
  let εstop := min εabs (1 / (2 * C))
  have hεstop : 0 < εstop := lt_min hεabs (by positivity)
  let A := Aabs + 2 * c⁻¹ + 2 * C
  have hi : 0 < c⁻¹ := inv_pos.mpr hc
  have hA : 0 < A := by dsimp [A]; positivity
  have hAabs : Aabs ≤ A := by dsimp [A]; linarith only [hi, hC]
  have hAc : 2 * c⁻¹ ≤ A := by dsimp [A]; linarith only [hAabsPos, hC]
  have hAC : 2 * C ≤ A := by dsimp [A]; linarith only [hi, hAabsPos]
  have hCsε : C * εstop ≤ 1 / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp
      (min_le_right εabs (1 / (2 * C)))
    change εstop * (2 * C) ≤ 1 at hh
    nlinarith only [hh]
  refine ⟨Cb, Csum, εstop, η, A, hCb, hCs, hεstop, hη, hA, ?_⟩
  intro ui e S h hs
  obtain ⟨a, ha, hineq⟩ := hineq ui e S h hs εstop hεstop.le
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ εentry vb σ N B T hau hN he hσ hstop hR₀ hhalf hgap hradii hT
    γ hends hgraph hσeq hinit
  dsimp only
  let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
  let V := ∑ n ∈ Finset.range N, σ n
  let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F εstop S) (2 * R₀)
  let D := (initialInteraction S u₀ v₀).toReal
  intro hsmall hz hηs hbudgetSmall hηentry hstrict
  have hJ0 : 0 ≤ J := ENNReal.toReal_nonneg
  have hV0 : 0 ≤ V := Finset.sum_nonneg (fun n _ => hσ n)
  have hz0 : 0 ≤ z := by dsimp [z, Local.sigma]; positivity
  have hJ : J ≤ εstop := by linarith only [hsmall, hV0]
  obtain ⟨hfirst, hsecond⟩ := hineq u₀ u₁ v₀ R₀ εentry vb σ N B T hau hN he hσ
    hstop hR₀ hhalf hgap hradii hT γ hends hgraph hσeq hinit hJ hz hηs hbudgetSmall
  have hclosed := habsorb D εentry z J V ENNReal.toReal_nonneg he hz0 hJ0 hV0 hηentry
    (hsmall.trans (min_le_left _ _)) hfirst hsecond
  have hclosedA : J + V ≤ A * (D + εentry + z) :=
    hclosed.trans (mul_le_mul_of_nonneg_right hAabs (by positivity))
  have hVε : V ^ 2 ≤ εstop * V := by
    have hv : V ≤ εstop := by linarith only [hsmall, hJ0]
    nlinarith only [hv, hV0]
  have hCV : C * V ^ 2 ≤ V / 2 := by
    calc
      _ ≤ C * (εstop * V) := mul_le_mul_of_nonneg_left hVε hC.le
      _ = (C * εstop) * V := by ring
      _ ≤ (1 / 2) * V := mul_le_mul_of_nonneg_right hCsε hV0
      _ = V / 2 := by ring
  have hlinear : V ≤ 2 * c⁻¹ * J + 2 * C * εentry + 2 * C * z := by
    linarith only [hsecond, hCV]
  have hlinearA : V ≤ A * (J + εentry + z) := by
    calc
      _ ≤ 2 * c⁻¹ * J + 2 * C * εentry + 2 * C * z := hlinear
      _ ≤ A * J + A * εentry + A * z := by gcongr
      _ = _ := by ring
  exact ⟨hlinearA, hclosedA, hclosedA.trans_lt hstrict⟩

end EmcsfAcExtension.Global
