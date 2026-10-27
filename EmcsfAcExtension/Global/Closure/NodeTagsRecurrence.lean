module

public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Observation
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Domains
import EmcsfAcExtension.Global.Closure.Parameters
import EmcsfAcExtension.Global.Closure.StageSums
import EmcsfAcExtension.Global.Cooling.ObservationDischarge

/-! # The physical cooling recurrence on an available completed stage

Observation is discharged by its proved input. This export concerns available
stages and connectors; it does not assert their existence.
Source: `charged_SF_new_version.tex:L3862–L3871`, `L3908–L3917`.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global

/-- [internal]
The physical next energy is bounded by the recursive envelope, with no
additive electric floor. The fixed gap chooses the observation thresholds;
`εweak,ρ,χ` then choose `K,d,H,Cd,C₁`, before all physical data and shrinking
scales. The same `C₁` works on every available completed cylinder and its
possibly partial incoming connector. The numerical envelopes have the lower
geometric bound and every prescribed clock is positive and finite (real).
Source: charged_SF_new_version.tex:L3908–L3917. -/
theorem cc_recurrence (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Tstar δstar ηstar : ℝ, 0 < Tstar ∧ 0 < δstar ∧ 0 < ηstar ∧
      ∀ (εweak ρ χ : ℝ), 0 ≤ εweak → 0 < ρ → 0 < χ →
      ∃ K d H Cd C₁ : ℝ, 0 < K ∧ 0 < d ∧ 0 < H ∧ 0 < Cd ∧ 0 < C₁ ∧ 2 * K * d < χ ∧
      (∀ (ε₀ b₀ : ℝ) (σ : ℕ → ℝ) (n : ℕ), 0 < ε₀ → 0 < b₀ →
        χ ^ n * ε₀ ≤ energyEnvelope χ C₁ ε₀ σ n ∧
        0 < stageDuration H ρ b₀ χ C₁ ε₀ σ n) ∧
      ∀ (c Λ F ui e b ε x Bterm Jstop R₀ : ℝ) (S : Fields) (g : ℝ → ℝ),
      0 < c → 0 ≤ F → F < 1 → 0 < b → 0 < ε → 0 ≤ Jstop → b ≤ R₀ →
      OriginalData ui e S →
      ∀ γ : ClockCylinder S (origDomain ui) b 0 (H * b / ε),
      AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V 0) 0 (H * b / ε) →
      (∀ τ ∈ Set.Icc 0 (H * b / ε), S.mu (γ.U τ) (γ.V τ) +
        ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
      (∀ τ ∈ Set.Icc (Tstar * b) (H * b / ε - Tstar * b),
        triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
        (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
          0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
        |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
      cylinderEnergy S b (γ.U 0) (γ.V 0) / b ≤ ε →
      let a := γ.U (H * b / ε)
      let v := γ.V (H * b / ε)
      a ≤ x → x < v →
      (∀ u ∈ Set.Icc a x, ρ * b ≤ S.r u v) →
      ExteriorStops S (exteriorDomain ui a x (fun _ => v)) δ c Λ F εweak →
      (∀ u ∈ Set.Icc a x, ∀ w ∈ Set.Icc u 0, δ ≤ 1 - S.mu u w) →
      (∀ u ∈ Set.Icc a x, ‖S.phi u 0‖ ≤ Bterm) →
      IntegrableOn g (Set.Icc v 0) →
      (∀ᵐ w ∂volume.restrict (Set.Icc v 0), 0 ≤ g w) →
      (∀ u ∈ Set.Icc a x, ∀ᵐ w ∂volume.restrict (Set.Icc v 0), ‖weightedJ S u w‖ ≤ g w) →
      (∫ w in v..0, g w) ≤ Jstop →
      e ^ 2 * (1 + Bterm + (F + c⁻¹ * Jstop) / (1 - F ^ 2)) ^ 2 * R₀ ^ 2 ≤ 1 →
      let σ := (curveCovVar e S S.a γ.U γ.V 0 (H * b / ε)).toReal
      cylinderEnergy S (S.r x v) x v / S.r x v ≤ χ * ε + C₁ * σ ^ 2 := by
  obtain ⟨Ts, δs, ηs, hTs, hδs, hηs, hrec⟩ :=
    cc_recurrence_of_estimates δ hδ (Cooling.observation_input δ hδ)
  refine ⟨Ts, δs, ηs, hTs, hδs, hηs, ?_⟩
  intro εweak ρ χ hε hρ hχ
  obtain ⟨K, d, H, Cd, C₁, hK, hd, hH, hCd, hC₁, hcontract, hphysical⟩ :=
    hrec εweak ρ χ hε hρ hχ
  refine ⟨K, d, H, Cd, C₁, hK, hd, hH, hCd, hC₁, hcontract, ?_, hphysical⟩
  intro ε₀ b₀ σ n he hb
  exact ⟨Closure.geometric_le_energyEnvelope hχ.le hC₁.le ε₀ σ n,
    Closure.stageDuration_pos hH hρ hb hχ hC₁.le he σ n⟩

end EmcsfAcExtension.Global
