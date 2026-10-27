module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Observation
public import EmcsfAcExtension.Global.Defs.Domains
import EmcsfAcExtension.Global.Closure.CutoffContinuity
import EmcsfAcExtension.Global.Cooling.Full
import EmcsfAcExtension.Global.Cooling.ObservationDischarge

/-! # Comparison regions and all short or partial boundary windows

The proper original triangle supplies the independent late gap. The full
cooling consumer applies its observation comparison internally and supplies
budgets on every ordered subinterval, including short and partial windows.
No interior exterior-expansion bound enters this export.
Source: `charged_SF_new_version.tex:L4093–L4102`; approved internal project record (O1)–(O2).
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

/-- [node sec:charged-closure#observation-window-regions]
Every full available window has its comparison region and complete axis
rows in a proper original triangle with the independent late gap. The
observation comparison and its characteristic margins are consumed by the
actual cooling theorem; its two budgets hold on every ordered subinterval,
including short, partial and singleton windows. The constants depend only
on the fixed gap, before all physical data, scales and durations. There is
no lower exterior expansion bound on the interior.
Source: charged_SF_new_version.tex:L4093–L4102. -/
theorem observation_window_regions_complete (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Ts δs ηs Cbudget : ℝ,
      0 < Ts ∧ 0 < δs ∧ 0 < ηs ∧ 0 < Cbudget ∧
      ∀ (ui e b T u₀ : ℝ) (S : Fields), 0 < b → 0 < T → OriginalData ui e S →
      ∀ γ : ClockCylinder S (origDomain ui) b 0 T,
      u₀ ≤ γ.U 0 → (∀ τ ∈ Icc 0 T, b < S.r (γ.U τ) 0) →
      (∀ p ∈ origDomain ui, u₀ ≤ p.1 →
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
      AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V 0) 0 T →
      (∀ τ ∈ Icc 0 T, S.mu (γ.U τ) (γ.V τ) +
        ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δs) →
      (∀ τ ∈ Icc (Ts * b) (T - Ts * b),
        |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηs) →
      (∀ τ ∈ Icc (Ts * b) (T - Ts * b),
        let a := τ - Ts * b
        let z := τ + Ts * b
        triangle (γ.U a) (γ.V z) ⊆ origDomain ui ∧
        (∀ p ∈ triangle (γ.U a) (γ.V z),
          0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
        comparisonDomain S (origDomain ui) γ.U γ.V a z b ⊆ triangle (γ.U a) (γ.V z) ∧
        (∀ p ∈ triangle (γ.U a) (γ.V z), outSeg p.1 p.1 p.2 ⊆ triangle (γ.U a) (γ.V z))) ∧
    (∀ a ∈ Icc 0 T, ∀ c ∈ Icc a T,
      let σ := (curveCovVar e S S.a γ.U γ.V a c).toReal
      (sSup ((fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b) '' Icc a c) +
        cylinderDissipation S γ.U γ.V a c / b ≤
      Cbudget * (cylinderEnergy S b (γ.U a) (γ.V a) / b + σ ^ 2)) ∧
      (sSup ((fun x => S.m (γ.U x) (γ.V x) / b +
      ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2) '' Icc a c) +
        (∫ x in a..c,
          (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           ‖S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           S.mu (γ.U x) (γ.V x) ^ 2 +
           (cylinderEnergy S b (γ.U x) (γ.V x) / b) ^ 2) / b) ≤
      Cbudget * (cylinderEnergy S b (γ.U a) (γ.V a) / b + σ ^ 2))) := by
  obtain ⟨Ts, δs, ηs, Cbudget, hTs, hδs, hηs, hCb, hcool⟩ :=
    charged_cool_full_of_observation δ hδ (Cooling.observation_input δ hδ)
  obtain ⟨H, Cd, _hH, _hCd, hcool⟩ := hcool 1 (by norm_num)
  refine ⟨Ts, δs, ηs, Cbudget, hTs, hδs, hηs, hCb, ?_⟩
  intro ui e b T u₀ S hb hT h γ hentry hterminal hgap hac hweak hscale
  have hregions := observation_window_regions h γ hb hTs.le hentry hterminal hgap
  have hwindows : ∀ τ ∈ Icc (Ts * b) (T - Ts * b),
      triangle (γ.U (τ - Ts * b)) (γ.V (τ + Ts * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Ts * b)) (γ.V (τ + Ts * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηs := by
    intro τ hτ
    exact ⟨(hregions τ hτ).1, (hregions τ hτ).2, hscale τ hτ⟩
  refine ⟨?_, (hcool ui e b 1 T S hb (by norm_num) hT h γ hac hweak hwindows).1⟩
  intro τ hτ
  exact ⟨(hregions τ hτ).1, (hregions τ hτ).2,
    comparisonDomain_subset_triangle, fun p hp => outgoing_axis_segment_subset_window hp⟩

end EmcsfAcExtension.Global.Closure
