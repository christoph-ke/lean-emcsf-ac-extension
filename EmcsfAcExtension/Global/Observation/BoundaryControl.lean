module

public import EmcsfAcExtension.Global.Observation.BoundarySource
import EmcsfAcExtension.Global.Observation.Gauge

/-! # Boundary control for the normalized original solution

The scalar background and central parameters are determined by the actual
parallel-frame trace. The enlarged scale bounds these central parameters.
Source: charged_SF_new_version.tex:L2060–2106; internal project record (B), (B1), (C3).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Boundary control in the actual solution and chosen parallel frame, with
all tangent and continuity inputs discharged. The two small-boundary
norms remain inputs of this helper; its failure-of-observation consumer
supplies them. The constant depends only on `T`, before all physical data,
normalizing scales, gauges, backgrounds and error tolerances. -/
theorem boundary_control_of_small_boundary {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (ui e b s τ₀ ε : ℝ) (S : Fields) (_h : OriginalData ui e S)
      (γ : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2))
      (χ : ℝ → ℝ),
    let G := gaugeFields e S χ
    let L := b / s
    let f := fun t => τ₀ + s * t / 2
    let φ := fun t => G.phi (γ.U (f t)) (γ.V (f t))
    let y := fun t => G.theta (γ.U (f t)) (γ.V (f t)) / G.lam (γ.U (f t)) (γ.V (f t))
    let z := fun t => G.xi (γ.U (f t)) (γ.V (f t)) / G.nu (γ.U (f t)) (γ.V (f t))
    let M := S.m (γ.U τ₀) (γ.V τ₀) / s
    let H := G.a (γ.U τ₀) (γ.V τ₀)
    let P := -(L : ℂ) * y 0
    0 < b → 0 < s → s ≤ b → 0 ≤ ε → ε ≤ 1 / C →
    ContDiff ℝ 1 χ →
    (∀ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2),
      HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ)) →
    S.m (γ.U τ₀) (γ.V τ₀) + b *
      ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ ≤ s →
    (∀ t ∈ Icc (-T * L) (T * L), ‖φ t + y t - H‖ ≤ ε / L) →
    (∫ t in (-T * L)..(T * L), ‖φ t - H + z t‖ ^ 2) ≤ ε ^ 2 / L →
    ∀ t ∈ Icc (-T * L) (T * L),
      ((‖φ t - H - P / (L : ℝ)‖ ≤ C * ε / L ∧
        |S.m (γ.U (f t)) (γ.V (f t)) / s - M| ≤ C * ε / L ∧
        S.m (γ.U (f t)) (γ.V (f t)) / s ≤ 2 ∧
        ‖φ t‖ ≤ ‖H‖ + 2 / L ∧ ‖y t + P / (L : ℝ)‖ ≤ C * ε / L) ∧
        |S.Q (γ.U (f t)) (γ.V (f t)) / s - S.Q (γ.U τ₀) (γ.V τ₀) / s| ≤
          C * (|s * e| * L * (1 + ‖H‖))) ∧
      (|S.m (γ.U (f t)) (γ.V (f t)) / s - M| ≤ 1 ∧
        S.m (γ.U (f t)) (γ.V (f t)) ≤ 2 * s ∧
        ‖S.phi (γ.U (f t)) (γ.V (f t))‖ ≤ ‖H‖ + 2 * s / b) := by
  obtain ⟨C, hC, hcontrol⟩ := physical_boundary_inputs hT
  refine ⟨C, hC, ?_⟩
  intro ui e b s τ₀ ε S h γ χ
  dsimp only
  intro hb hs hsb hε hεC hχ hχd hscale hosc hl2
  let G := gaugeFields e S χ
  let L := b / s
  let f := fun t : ℝ => τ₀ + s * t / 2
  let φ := fun t => G.phi (γ.U (f t)) (γ.V (f t))
  let y := fun t => G.theta (γ.U (f t)) (γ.V (f t)) / G.lam (γ.U (f t)) (γ.V (f t))
  let z := fun t => G.xi (γ.U (f t)) (γ.V (f t)) / G.nu (γ.U (f t)) (γ.V (f t))
  let m := fun t => S.m (γ.U (f t)) (γ.V (f t)) / s
  let g := fun t => 1 - S.mu (γ.U (f t)) (γ.V (f t))
  let Q := fun t => S.Q (γ.U (f t)) (γ.V (f t)) / s
  let H := G.a (γ.U τ₀) (γ.V τ₀)
  let M := S.m (γ.U τ₀) (γ.V τ₀) / s
  let P := -(L : ℂ) * y 0
  have hL : 0 < L := div_pos hb hs
  have hL1 : 1 ≤ L := (le_div_iff₀ hs).mpr (by simpa only [one_mul] using hsb)
  have htime : τ₀ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2) := by
    constructor <;> nlinarith only [mul_nonneg hT hb.le]
  have hm0 : 0 ≤ S.m (γ.U τ₀) (γ.V τ₀) := by
    have hh := (h.mu _ (γ.mem τ₀ htime)).1
    simp only [Fields.mu, γ.radius τ₀ htime] at hh
    have hh' := (le_div_iff₀ hb).mp hh
    linarith only [hh']
  have hM : M ≤ 1 := (div_le_iff₀ hs).mpr (by
    simpa only [one_mul] using (le_add_of_nonneg_right
      (mul_nonneg hb.le (norm_nonneg _))).trans hscale)
  have hy : ‖y 0‖ = ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ := by
    simpa only [y, f, mul_zero, zero_div, add_zero] using (gauge_ratio_norms e S χ _ _).1
  have hP : ‖P‖ ≤ 1 := by
    rw [show ‖P‖ = L * ‖y 0‖ by
      simp only [P, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]]
    rw [hy, div_mul_eq_mul_div]
    exact (div_le_iff₀ hs).mpr (by linarith only [hscale, hm0])
  have hφ0 : φ 0 = H + P / (L : ℝ) := by
    dsimp only [P, H, φ, y, f, G, Fields.a]
    simp only [mul_zero, zero_div, add_zero]
    have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
    field_simp
    ring
  obtain ⟨cφ, cy, cz, cm, cg, cQ, hd⟩ := boundary_profiles_of_solution
    (T := T) (τ₀ := τ₀) h.solution γ χ hχ hs hb Subset.rfl hχd
  have hg (t) (ht : t ∈ Icc (-T * L) (T * L)) : 0 ≤ g t ∧ g t ≤ 1 := by
    have hmem : f t ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2) := by
      dsimp only [f]
      constructor
      · have hh := mul_le_mul_of_nonneg_left ht.1 (div_pos hs (by norm_num : (0 : ℝ) < 2)).le
        dsimp only [L] at hh
        field_simp at hh ⊢
        nlinarith only [hh]
      · have hh := mul_le_mul_of_nonneg_left ht.2 (div_pos hs (by norm_num : (0 : ℝ) < 2)).le
        dsimp only [L] at hh
        field_simp at hh ⊢
        nlinarith only [hh]
    have hh := h.mu _ (γ.mem _ hmem)
    exact ⟨by dsimp only [g]; linarith only [hh.2], by dsimp only [g]; linarith only [hh.1]⟩
  have hmzero : m 0 = M := by simp only [m, M, f, mul_zero, zero_div, add_zero]
  have hdz (t) (ht : t ∈ Ioo (-T * L) (T * L)) := hd t ht
  intro t ht
  have hc := hcontrol L ε (s * e) M H P φ y z m g Q hL1 hε hεC hP hM hmzero hφ0
    cφ cy cz cm cg cQ hg hosc hl2 (fun t ht => (hdz t ht).1)
    (fun t ht => (hdz t ht).2.1) (fun t ht => (hdz t ht).2.2) t ht
  refine ⟨?_, hc.2 s b _ _ hs hb rfl rfl ?_⟩
  · simpa only [φ, y, z, m, g, Q, H, M, P, L, G, f, mul_zero, zero_div, add_zero] using! hc.1
  · exact (gauge_invariants e S χ _ _).2.2.2.1

end EmcsfAcExtension.Global.Observation
