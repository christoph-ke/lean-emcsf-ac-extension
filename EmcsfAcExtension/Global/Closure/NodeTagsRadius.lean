module

public import EmcsfAcExtension.Global.Closure.NodeTagsImprovements
import EmcsfAcExtension.Global.Closure.Clock

/-! # Strict radius improvement on an available finite schedule

Clock comparison is derived from the finite stopped budgets. The actual
cylinder and connector clocks are summed before estimating radius loss.
Source: `charged_SF_new_version.tex:L4079–L4083`.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [node sec:charged-closure#radius-stop-improvement]
Terminal radius loss is at most twice the actual boundary clock and is
strictly less than `R₀/4`. The schedule and sufficiently late entry satisfy
the displayed mixed-clock smallness, exactly the numerical consequence of
`b₀/(εentry*R₀) → 0`. Observation thresholds depend only on the gap; all
other constants and tolerances depend only on the fixed geometry,
recurrence and stops, before physical data and finite cutoffs. Neither
clock comparison nor a total-clock bound is assumed.
Source: charged_SF_new_version.tex:L4079–L4083. -/
theorem Closure.radius_stop_improvement (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ Ts δs ηs : ℝ, 0 < Ts ∧ 0 < δs ∧ 0 < ηs ∧
      ∀ (εweak ρ χ C₁ c Λ F : ℝ),
      ExteriorBox δ c Λ F εweak ρ → 0 < ρ →
      0 ≤ χ → χ < 1 → 0 ≤ C₁ → F + εweak ≤ δs → 0 < F → 0 < εweak →
      ∃ Cbudget Csum C η : ℝ, 0 < Cbudget ∧ 0 < Csum ∧ 0 < C ∧ 0 < η ∧
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
      let z := Local.sigma e (Interaction.scalarBackground ui R₀ c F η S) (2 * R₀)
      J + V ≤ η → εentry ≤ η → z ≤ η →
      (∀ v ∈ Icc v₀ 0, 2 * c ≤ S.lam u₀ v) →
      ∀ (H b₀ : ℝ), 0 < H → 0 < b₀ → 0 < χ → ρ < χ → 0 < εentry →
      (∀ n : Fin N, B.radii n = stageRadius ρ b₀ n) →
      (∀ n, T n ≤ stageDuration H ρ b₀ χ C₁ εentry σ n) →
      2 * (H * b₀ / (εentry * (1 - ρ / χ)) + b₀) < R₀ / 4 →
      R₀ - S.r u₁ 0 ≤ 2 * cylinderClock S vb u₀ u₁ ∧
      R₀ - S.r u₁ 0 < R₀ / 4 ∧ 3 * R₀ / 4 < S.r u₁ 0 := by
  obtain ⟨Ts, δs, ηs, hTs, hδs, hηs, hest⟩ := cc_optics δ hδ
  refine ⟨Ts, δs, ηs, hTs, hδs, hηs, ?_⟩
  intro εweak ρ χ C₁ c Λ F hbox hρ hχ hχ1 hC₁ hweak hF hεweak
  obtain ⟨Cb, Csum, C, η, hCb, hCs, hC, hη, hest⟩ :=
    hest εweak ρ χ C₁ c Λ F hbox hρ hχ hχ1 hC₁ hweak hF hεweak
  refine ⟨Cb, Csum, C, η, hCb, hCs, hC, hη, ?_⟩
  intro ui e S h hs
  obtain ⟨a, ha, hest⟩ := hest ui e S h hs
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ εentry vb σ N B T hau hN he hσ hstop hR₀ hhalf hgap hradii hT
    γ hends hgraph hσeq hinit
  dsimp only
  intro hsmall heη hzη hentry H b₀ hH hb₀ hχpos hρχ hepos hradiiEq hshort hclockSmall
  have hfields := hest u₀ u₁ v₀ R₀ εentry vb σ N B T hau hN he hσ hstop hR₀ hhalf
    hgap hradii hT γ hends hgraph hσeq hinit hsmall heη hzη
  have hratio := (hfields.2.2.2 hentry).2
  have hclock := Closure.total_boundary_clock_of_duration_le h.solution B hH ⟨hρ, hρχ⟩
    ⟨hχpos, hχ1⟩ hC₁ hepos hb₀ σ hradiiEq T hT hshort γ hends hgraph
  have hab : u₀ ≤ u₁ := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have hrat (u : ℝ) (hu : u ∈ Icc u₀ u₁) : -S.nu u 0 ≤ 2 * (-S.nu u (vb u)) :=
    ((div_lt_iff₀ (neg_pos.mpr (h.solution.nu_neg _ (B.mem u hu)))).mp (hratio u hu)).le
  have hr := Closure.radius_stop_improvement_of_estimates h.solution B hab hR₀ hrat
    hclock hclockSmall
  exact ⟨hr.1, hr.1.trans_lt
    ((mul_le_mul_of_nonneg_left hclock (by norm_num)).trans_lt hclockSmall), hr.2⟩

end EmcsfAcExtension.Global
