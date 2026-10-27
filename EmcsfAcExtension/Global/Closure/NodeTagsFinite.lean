module

public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Observation
public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Global.Interaction.ClosuresScalar
import EmcsfAcExtension.Global.Closure.Absorption
import EmcsfAcExtension.Global.Closure.StageSums
import EmcsfAcExtension.Global.Closure.Clock
import Mathlib.Tactic

/-! # The coupled stopped inequalities from actual initial energies

Boundary budgets and both of their sums are produced here, rather than
assumed as additional stopping conditions. All assertions concern an
available finite path, including an unfinished last cylinder.
Source: `charged_SF_new_version.tex:L4016–L4052`.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [node eq:cc-inequalities]
Both stopped inequalities, with one constant fixed before the physical
data, shrinking scales, durations and cutoff. Observation thresholds depend
only on `δ`; budget constants then depend on `εweak,ρ,χ,C₁`; the final
coefficient also depends on `c,Λ,F`. Inputs describe an available stopped
prefix with its propagated initial energies. Its boundary profiles, actual
integrated budgets, and sums are derived, not separate bootstraps.
The numerical smallness conditions are the prescribed parameter choices.
Source: charged_SF_new_version.tex:L4028–L4040. -/
theorem cc_inequalities (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Ts δs ηs : ℝ, 0 < Ts ∧ 0 < δs ∧ 0 < ηs ∧
      ∀ (εweak ρ χ C₁ c Λ F : ℝ),
      ExteriorBox δ c Λ F εweak ρ → 0 < ρ →
      0 ≤ χ → χ < 1 → 0 ≤ C₁ → F + εweak ≤ δs →
      ∃ Cbudget Csum C : ℝ, 0 < Cbudget ∧ 0 < Csum ∧ 0 < C ∧
      ∀ (ui e : ℝ) (S : Fields), OriginalData ui e S → SignedTerminalBound ui S →
      ∀ Jstop : ℝ, 0 ≤ Jstop → ∃ a ∈ Ioo ui 0,
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
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
      J ≤ Jstop → z ≤ 1 → 9 * z ≤ ηs ^ 2 → Csum * (εentry + V ^ 2) ≤ F ^ 2 →
      J ≤ (initialInteraction S u₀ v₀).toReal + C * (εentry + V ^ 2) +
        C * J * (εentry + V ^ 2) + C * F * J * (Real.sqrt εentry + V) +
        C * F * J ^ 2 + C * z * (1 + J) ∧
      V ≤ c⁻¹ * J + C * (εentry + V ^ 2) + C * z := by
  obtain ⟨Ts, δs, ηs, hTs, hδs, hηs, hbud⟩ :=
    Closure.stopped_boundary_budgets_of_initial_energies δ hδ
  refine ⟨Ts, δs, ηs, hTs, hδs, hηs, ?_⟩
  intro εweak ρ χ C₁ c Λ F hbox hρ hχ hχ1 hC₁ hweak
  obtain ⟨Cb, hCb, hbud⟩ := hbud εweak ρ hbox.2.2.2.2.2.2.1 hρ
  obtain ⟨Csum, hCs, hsums⟩ := Closure.finite_stage_sums χ C₁ Cb ⟨hχ, hχ1⟩ hC₁ hCb.le
  obtain ⟨Cs, hCsrc, hsource⟩ :=
    Closure.stopped_source_inequality_of_budgets δ c Λ F εweak ρ Csum hbox hCs.le
  obtain ⟨Cf, hCf, hforcing⟩ := Closure.stopped_forcing_inequality_of_budgets δ F
    hδ.1 hδ.2.le hbox.2.2.2.2.1 hbox.2.2.2.2.2.1
  let C := Cs + Cf * (Csum + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hsC : Cs ≤ C := le_add_of_nonneg_right (mul_nonneg hCf.le (by positivity))
  have hfC : Cf ≤ C := by dsimp [C]; nlinarith only [hCsrc, mul_nonneg hCf.le hCs.le]
  have hfprod : Cf * Csum ≤ C := by dsimp [C]; linarith only [hCsrc, hCf]
  refine ⟨Cb, Csum, C, hCb, hCs, hC, ?_⟩
  intro ui e S h hs Jstop hJstop
  obtain ⟨a, ha, hsource⟩ := hsource ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ εentry vb σ N B T hau hN he hσ hstop hR₀ hhalf hgap hradii hT
    γ hends hgraph hσeq hinit
  dsimp only
  let J := (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal
  let V := ∑ n ∈ Finset.range N, σ n
  let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
  intro hJ hz hη hsmall
  have hE := hbud χ C₁ εentry c Λ F ui e u₀ u₁ v₀ Jstop R₀ S vb σ N B T
    hχ hC₁ he hJstop hweak h hbox hstop hR₀ hhalf hJ hgap hradii
    (fun n => (hT n).le) γ hends hgraph hσeq hinit hz hη
  let E := fun n : Fin N => stageBudget Cb χ C₁ εentry σ n
  have hsum : (∑ n, E n) ≤ Csum * (εentry + V ^ 2) := by
    simpa only [E, V, ← Fin.sum_univ_eq_sum_range] using (hsums εentry σ N he hσ).1
  have hroot : (∑ n, Real.sqrt (E n)) ≤ Csum * (Real.sqrt εentry + V) := by
    simpa only [E, V, ← Fin.sum_univ_eq_sum_range] using (hsums εentry σ N he hσ).2
  have hpoint (u : ℝ) (hu : u ∈ Icc u₀ u₁) :=
    Closure.boundary_budget_le_sum B hN E hE hu
  have hmass (u : ℝ) (hu : u ∈ Icc u₀ u₁) : S.m u (vb u) / S.r u (vb u) ≤ F ^ 2 := by
    have hh := (hpoint u hu).trans (hsum.trans hsmall)
    linarith only [hh, sq_nonneg ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖]
  have hsrc := hsource u₀ u₁ v₀ R₀ εentry V vb (fun _ => F ^ 2) N B E hau he
    (Finset.sum_nonneg (fun n _ => hσ n)) hstop hR₀ hhalf hJ
    (fun u hu => ⟨hmass u hu, le_rfl⟩) hE hsum hroot
  have hcore (u : ℝ) (hu : u ∈ Icc u₀ u₁) (w : ℝ) (hw : w ∈ Icc u 0) :
      δ ≤ 1 - S.mu u w :=
    (hgap (u, w) ⟨(B.mem u hu).1, (B.mem u hu).2.1, hw⟩ hu.1).2
  have hEF (n : Fin N) : E n ≤ F ^ 2 :=
    (Finset.single_le_sum (fun i _ => (hE i).1) (Finset.mem_univ n)).trans (hsum.trans hsmall)
  have hforce := hforcing ui e u₀ u₁ v₀ ρ R₀ c Λ εweak Jstop S vb N B E T h hbox hJstop
    hstop hR₀ hhalf hJ hcore hE hEF hT γ hends hgraph
  have hV : (∑ n, (curveCovVar e S S.a (γ n).U (γ n).V 0 (T n)).toReal) = V := by
    simp only [← hσeq, V, Fin.sum_univ_eq_sum_range]
  rw [hV] at hforce
  constructor
  · apply hsrc.trans
    change _ ≤ (initialInteraction S u₀ v₀).toReal + C * (εentry + V ^ 2) +
      C * J * (εentry + V ^ 2) + C * F * J * (Real.sqrt εentry + V) +
      C * F * J ^ 2 + C * z * (1 + J)
    have hF := hbox.2.2.2.2.1
    have hJ0 : 0 ≤ J := ENNReal.toReal_nonneg
    have hV0 : 0 ≤ V := Finset.sum_nonneg (fun n _ => hσ n)
    have hz0 : 0 ≤ z := by dsimp [z, Local.sigma]; positivity
    gcongr
  · have ht : Cf * (∑ n, E n) ≤ C * (εentry + V ^ 2) := by
      calc
        _ ≤ Cf * (Csum * (εentry + V ^ 2)) := mul_le_mul_of_nonneg_left hsum hCf.le
        _ = (Cf * Csum) * (εentry + V ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hfprod (by positivity)
    have hz0 : 0 ≤ z := by dsimp [z, Local.sigma]; positivity
    have hzt := mul_le_mul_of_nonneg_right hfC hz0
    change V ≤ c⁻¹ * J + Cf * (∑ n, E n) + Cf * z at hforce
    linarith only [hforce, ht, hzt]

end EmcsfAcExtension.Global
