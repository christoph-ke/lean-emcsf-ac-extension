module

public import EmcsfAcExtension.Global.Closure.ConnectorEnergy

/-! # The full stopped connector recurrence

Package the analytic connector estimate with the recursively assigned energy
envelope, its geometric lower bound, and positive finite prescribed clocks.
Source: `charged_SF_new_version.tex:L3908–L3917`, `charged_SF_new_version.tex:L4086–L4102`.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Closure

/-- [node eq:cc-recurrence]
Cooling and the actual incoming connector propagate the starting observation
energy, with the same fixed constants as the recursively assigned envelope.
The envelope has its exact initial and successor values and dominates
`χ ^ n * εentry`; every prescribed stage duration is a positive real number.
The analytic estimate holds at every partial or full connector endpoint,
without an additive electromagnetic floor. All analytic inputs of
`stopped_connector_recurrence` are retained.
The thresholds depend only on `δ`; `H,C₁` depend only on `δ,εweak,ρ,χ`.
They precede the entry energy, initial radius, variation sequence, solution,
coupling, entry row, shrinking scales, stage number and duration.
Source: `charged_SF_new_version.tex:L3908–L3917`, `charged_SF_new_version.tex:L4086–L4102`. -/
theorem stopped_connector_recurrence_full (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Ts δs ηs : ℝ, 0 < Ts ∧ 0 < δs ∧ 0 < ηs ∧
      ∀ (εweak ρ χ : ℝ), 0 ≤ εweak → 0 < ρ → 0 < χ →
      ∃ H C₁ : ℝ, 0 < H ∧ 0 < C₁ ∧
      (∀ (εentry b₀ : ℝ) (σ : ℕ → ℝ), 0 < εentry → 0 < b₀ →
        energyEnvelope χ C₁ εentry σ 0 = εentry ∧
        (∀ k, energyEnvelope χ C₁ εentry σ (k + 1) =
          χ * energyEnvelope χ C₁ εentry σ k + C₁ * σ k ^ 2) ∧
        (∀ k, χ ^ k * εentry ≤ energyEnvelope χ C₁ εentry σ k) ∧
        (∀ k, 0 < stageDuration H ρ b₀ χ C₁ εentry σ k)) ∧
      ∀ (ui e u₀ u₁ v₀ R₀ c Λ F Jstop εn : ℝ) (S : Fields)
        (vb : ℝ → ℝ) (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (n : Fin N),
      OriginalData ui e S → ExteriorBox δ c Λ F εweak ρ → 0 ≤ Jstop → 0 < εn →
      F + εweak ≤ δs →
      ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F εweak →
      S.r u₀ 0 = R₀ → (∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0) →
      (interactionNorm e S (exteriorDomain ui u₀ u₁ vb) u₀ v₀).toReal ≤ Jstop →
      (∀ p ∈ origDomain ui, u₀ ≤ p.1 → 0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) →
      B.radii n < R₀ / 2 →
      ∀ γ : ClockCylinder S (origDomain ui) (B.radii n) 0 (H * B.radii n / εn),
      (γ.U 0 = B.cuts n.castSucc ∧ γ.U (H * B.radii n / εn) = B.cool n) →
      (∀ τ ∈ Icc 0 (H * B.radii n / εn), vb (γ.U τ) = γ.V τ) →
      cylinderEnergy S (B.radii n) (γ.U 0) (γ.V 0) / B.radii n ≤ εn →
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F Jstop S) (2 * R₀)
      z ≤ 1 → 9 * z ≤ ηs ^ 2 →
      ∀ x ∈ Icc (B.cool n) (B.cuts n.succ),
        cylinderEnergy S (S.r x (vb x)) x (vb x) / S.r x (vb x) ≤
          χ * εn + C₁ * (curveCovVar e S S.a γ.U γ.V 0 (H * B.radii n / εn)).toReal ^ 2 := by
  obtain ⟨Ts, δs, ηs, hTs, hδs, hηs, hsteps⟩ := stopped_connector_recurrence δ hδ
  refine ⟨Ts, δs, ηs, hTs, hδs, hηs, ?_⟩
  intro εweak ρ χ hεweak hρ hχ
  obtain ⟨H, C₁, hH, hC₁, hstep⟩ := hsteps εweak ρ χ hεweak hρ hχ
  refine ⟨H, C₁, hH, hC₁, ?_, hstep⟩
  intro εentry b₀ σ he hb
  exact ⟨energyEnvelope_zero χ C₁ εentry σ, energyEnvelope_succ χ C₁ εentry σ,
    geometric_le_energyEnvelope hχ.le hC₁.le εentry σ,
    stageDuration_pos hH hρ hb hχ hC₁.le he σ⟩

end EmcsfAcExtension.Global.Closure
