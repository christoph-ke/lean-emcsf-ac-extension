module

public import EmcsfAcExtension.Global.Closure.NodeTagsRecurrence

/-! # The cooling parameter order before the shrinking scales

The physical recurrence export retains its actual cooling contraction and
time constant; its coefficients precede all stage data.
Source: `charged_SF_new_version.tex:L3862–L3871`.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global

/-- [node sec:charged-closure#cooling-parameter-order]
Choose the connector/equivalence factor, then `d,H,Cd,C₁`, before the
stop, entry energy and late row. The factor `2*K*d` is strictly below `χ`,
and the returned time constant gives the actual physical transfer for
every available prescribed cylinder and connector. Thresholds depend only
on the gap; the remaining coefficients depend only on `εweak,ρ,χ`,
uniformly over all data, stages and scales. The result holds in particular
for the source order `0 < ρ < χ < 1`.
Source: charged_SF_new_version.tex:L3862–L3871. -/
theorem Closure.cooling_parameter_order (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
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
  exact cc_recurrence δ hδ

end EmcsfAcExtension.Global
