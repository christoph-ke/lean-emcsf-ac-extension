module

public import EmcsfAcExtension.Global.Observation.BoundaryFailure
public import EmcsfAcExtension.Global.Observation.BoundaryControl
import EmcsfAcExtension.Global.Observation.Gauge

/-! # Failed observation supplies the actual small boundary norms

The parallel gauge is the constructed incoming-coordinate gauge, with
its derivative and initial phase. All trace regularity, variation and
flux identifications are proved from the original solution.
Source: charged_SF_new_version.tex:L2060–2074, L2756–2783; internal project record (B).
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
A failed physical observation estimate supplies the two small-boundary
norms of the actual normalized solution in its parallel frame. The
positive coefficient depends only on `T,ε`, before all physical data,
scales, backgrounds and gauges. No independent trace, AC, integrability,
variation or clock-equation premise remains. -/
theorem small_boundary_of_solution_failed_observation {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (ui e b s τ₀ : ℝ) (S : Fields) (_h : OriginalData ui e S)
      (γ : ClockCylinder S (origDomain ui) b (τ₀ - T * b / 2) (τ₀ + T * b / 2))
      (χ : ℝ → ℝ),
    let G := gaugeFields e S χ
    let L := b / s
    let f := fun t => τ₀ + s * t / 2
    let H := G.a (γ.U τ₀) (γ.V τ₀)
    let φ := fun t => G.phi (γ.U (f t)) (γ.V (f t))
    let y := fun t => G.theta (γ.U (f t)) (γ.V (f t)) / G.lam (γ.U (f t)) (γ.V (f t))
    let z := fun t => G.xi (γ.U (f t)) (γ.V (f t)) / G.nu (γ.U (f t)) (γ.V (f t))
    0 < b → 0 < s → ContDiff ℝ 1 χ →
    (∀ τ ∈ Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2),
      HasDerivAt χ (S.A (γ.U τ) (γ.V τ)) (γ.U τ)) →
    χ (γ.U (τ₀ - T * b / 2)) = 0 →
    S.m (γ.U τ₀) (γ.V τ₀) + b *
      ‖S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)‖ ≤ s →
    (¬ ENNReal.ofReal (b * (‖S.theta (γ.U τ₀) (γ.V τ₀) /
      S.lam (γ.U τ₀) (γ.V τ₀)‖ ^ 2 + S.mu (γ.U τ₀) (γ.V τ₀) ^ 2)) ≤
      ENNReal.ofReal C * (ENNReal.ofReal (cylinderDissipation S γ.U γ.V
        (τ₀ - T * b / 2) (τ₀ + T * b / 2)) + ENNReal.ofReal b *
        (curveCovVar e S S.a γ.U γ.V (τ₀ - T * b / 2) (τ₀ + T * b / 2)) ^ 2)) →
    (∀ t ∈ Icc (-T * L) (T * L), ‖φ t + y t - H‖ ≤ ε / L) ∧
      (∫ t in (-T * L)..(T * L), ‖φ t - H + z t‖ ^ 2) ≤ ε ^ 2 / L := by
  obtain ⟨C, hC, hsmall⟩ := small_boundary_of_failed_observation hT hε
  refine ⟨C, hC, ?_⟩
  intro ui e b s τ₀ S h γ χ
  dsimp only
  intro hb hs hχ hχd hχ0 hscale hfailure
  let G := gaugeFields e S χ
  let A := fun τ => G.a (γ.U τ) (γ.V τ)
  let Q := fun τ => G.theta (γ.U τ) (γ.V τ) / G.lam (γ.U τ) (γ.V τ) -
    G.xi (γ.U τ) (γ.V τ) / G.nu (γ.U τ) (γ.V τ)
  let J := Icc (τ₀ - T * b / 2) (τ₀ + T * b / 2)
  have hst : τ₀ - T * b / 2 ≤ τ₀ + T * b / 2 := by
    nlinarith only [mul_nonneg hT hb.le]
  have htime : τ₀ ∈ J := by
    constructor <;> nlinarith only [mul_nonneg hT hb.le]
  have hm : 0 ≤ S.m (γ.U τ₀) (γ.V τ₀) := by
    have hh := (h.mu _ (γ.mem τ₀ htime)).1
    simp only [Fields.mu, γ.radius τ₀ htime] at hh
    have hh' := (le_div_iff₀ hb).mp hh
    linarith only [hh']
  have cphase : ContinuousOn (fun τ => Complex.exp (I * e * χ (γ.U τ))) J := by
    have cχ := hχ.continuous.comp_continuousOn γ.c1_U.continuousOn
    exact (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn cχ)).cexp
  have ca : ContinuousOn A J := by
    simpa only [A, G, gauge_normalized_out] using!
      cphase.mul (by simpa only [uIcc_of_le hst] using
        (Cylinder.ac_a h.solution γ hb hst).continuousOn)
  obtain ⟨cy, cz, _⟩ := Cylinder.continuousOn_normalized_traces h.solution γ
  have cq : ContinuousOn Q J := by
    simpa only [Q, G, gaugeFields, mul_div_assoc, ← mul_sub] using!
      cphase.mul (cy.sub cz)
  have hvar := gauge_clock_variation_on_cylinder h.solution γ hst χ hχd hχ0
  have hf := (comparison_boundary_regularity h.solution γ hb hst).2.2.2.2.ne
  have hQnorm (τ : ℝ) : ‖Q τ‖ = ‖S.theta (γ.U τ) (γ.V τ) /
      S.lam (γ.U τ) (γ.V τ) - S.xi (γ.U τ) (γ.V τ) / S.nu (γ.U τ) (γ.V τ)‖ :=
    (gauge_ratio_norms e S χ _ _).2
  have hQint : (∫ τ in (τ₀ - T * b / 2)..(τ₀ + T * b / 2), ‖Q τ‖ ^ 2) =
      cylinderDissipation S γ.U γ.V (τ₀ - T * b / 2) (τ₀ + T * b / 2) := by
    apply intervalIntegral.integral_congr
    intro τ _hτ
    exact congrArg (fun r : ℝ => r ^ 2) (hQnorm τ)
  have hfailure' : ¬ ENNReal.ofReal (b * (‖S.theta (γ.U τ₀) (γ.V τ₀) /
      S.lam (γ.U τ₀) (γ.V τ₀)‖ ^ 2 + (2 * S.m (γ.U τ₀) (γ.V τ₀) / b) ^ 2)) ≤
      ENNReal.ofReal C * ((ENNReal.ofReal
        (∫ τ in (τ₀ - T * b / 2)..(τ₀ + T * b / 2), ‖Q τ‖ ^ 2)) + ENNReal.ofReal b *
        (curveCovVar e S S.a γ.U γ.V (τ₀ - T * b / 2) (τ₀ + T * b / 2)) ^ 2) := by
    simpa only [hQint, Fields.mu, γ.radius τ₀ htime] using hfailure
  have hsmall' := hsmall b (S.m (γ.U τ₀) (γ.V τ₀)) s τ₀
    (curveCovVar e S S.a γ.U γ.V (τ₀ - T * b / 2) (τ₀ + T * b / 2))
    (S.theta (γ.U τ₀) (γ.V τ₀) / S.lam (γ.U τ₀) (γ.V τ₀)) (A τ₀) A Q
    hb hm hs hf hscale ca cq rfl hvar hfailure'
  have hclock (t : ℝ) : τ₀ + s / 2 * t = τ₀ + s * t / 2 := by ring
  constructor
  · intro t ht
    simpa only [A, Fields.a, hclock] using hsmall'.1 t ht
  · calc
      _ = ∫ t in (-T * (b / s))..(T * (b / s)),
          ‖A (τ₀ + s / 2 * t) - A τ₀ - Q (τ₀ + s / 2 * t)‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t _ht
        simp only [A, Q, G, hclock, Fields.a]
        congr 2
        ring
      _ ≤ ε ^ 2 / (b / s) := hsmall'.2

end EmcsfAcExtension.Global.Observation
