module

public import Mathlib
import EmcsfAcExtension.Global.Observation.BoundaryEstimates
import EmcsfAcExtension.Global.Observation.BoundaryData

/-! # Consequences of the normalized cylinder tangent equations

The tangent inputs are the interface to the original-clock transport
helpers. FTC discharges every integral-form premise of the boundary
estimates, whose outputs then discharge the Maxwell estimate's trace
bounds. Constants are chosen before all fields and physical parameters.
Source: charged_SF_new_version.tex:L2060–2106; internal project record (B), (B1), (B2), (C3).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

/-- [internal]
The normalized scalar and mass tangent equations give all boundary
closeness estimates, and the Maxwell tangent equation gives boundary
charge control. A single positive constant depends only on `T`, uniformly
in the radius, coupling, background, central data and all trace profiles.
The two small-boundary inputs are supplied by `co_small_boundary` helpers. -/
theorem co_boundary_control_of_clock_tangents {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (L ε e M : ℝ) (H P : ℂ) (φ y z : ℝ → ℂ) (m g Q : ℝ → ℝ),
        1 ≤ L → 0 ≤ ε → ε ≤ 1 / C → ‖P‖ ≤ 1 → M ≤ 1 → m 0 = M →
        φ 0 = H + P / (L : ℝ) →
        ContinuousOn φ (Icc (-T * L) (T * L)) →
        ContinuousOn y (Icc (-T * L) (T * L)) →
        ContinuousOn z (Icc (-T * L) (T * L)) →
        ContinuousOn m (Icc (-T * L) (T * L)) →
        ContinuousOn g (Icc (-T * L) (T * L)) →
        ContinuousOn Q (Icc (-T * L) (T * L)) →
        (∀ t ∈ Icc (-T * L) (T * L), 0 ≤ g t ∧ g t ≤ 1) →
        (∀ t ∈ Icc (-T * L) (T * L), ‖φ t + y t - H‖ ≤ ε / L) →
        (∫ t in (-T * L)..(T * L), ‖φ t - H + z t‖ ^ 2) ≤ ε ^ 2 / L →
        (∀ t ∈ Ioo (-T * L) (T * L),
          HasDerivAt φ ((y t - z t) / (2 * L : ℝ)) t) →
        (∀ t ∈ Ioo (-T * L) (T * L),
          HasDerivAt m (g t / 4 * (‖y t‖ ^ 2 - ‖z t‖ ^ 2)) t) →
        (∀ t ∈ Ioo (-T * L) (T * L),
          HasDerivAt Q (-(e * L / 2) * (starRingEnd ℂ (φ t) * (y t + z t)).im) t) →
        ∀ t ∈ Icc (-T * L) (T * L),
          (‖φ t - H - P / (L : ℝ)‖ ≤ C * ε / L ∧ |m t - M| ≤ C * ε / L ∧
            m t ≤ 2 ∧ ‖φ t‖ ≤ ‖H‖ + 2 / L ∧ ‖y t + P / (L : ℝ)‖ ≤ C * ε / L) ∧
          |Q t - Q 0| ≤ C * (|e| * L * (1 + ‖H‖)) := by
  obtain ⟨C₁, hC₁, hclose⟩ := co_boundary_close_of_boundary_equations hT
  obtain ⟨C₂, hC₂, hcharge⟩ := co_boundary_charge_of_trace_bounds hT
  let C := C₁ + C₂
  have hC : 0 < C := add_pos hC₁ hC₂
  have hC₁C : C₁ ≤ C := le_add_of_nonneg_right hC₂.le
  have hC₂C : C₂ ≤ C := le_add_of_nonneg_left hC₁.le
  refine ⟨C, hC, ?_⟩
  intro L ε e M H P φ y z m g Q hL hε0 hε hP hM hm0 hφ0 cφ cy cz cm cg cQ hg ha hβ
    dφ dm dQ t ht
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hφeq := Observation.integralForm_on_of_continuous_tangent cφ
    ((cy.sub cz).div_const (2 * L : ℝ)) dφ
  have hmeq := Observation.integralForm_on_of_continuous_tangent cm
    ((cg.div_const 4).mul ((cy.norm.pow 2).sub (cz.norm.pow 2))) dm
  have hQeq := Observation.integralForm_on_of_continuous_tangent cQ
    (continuousOn_const.mul (continuous_im.comp_continuousOn (cφ.star.mul (cy.add cz)))) dQ
  have hε₁ : ε ≤ 1 / C₁ := hε.trans
    (one_div_le_one_div_of_le hC₁ hC₁C)
  obtain ⟨hbounds, hweight⟩ := hclose L ε M H P φ y z m g hL hε0 hε₁ hP hM hm0 hφ0
    cφ cy cz hg ha hβ hφeq hmeq
  have hcharge' := hcharge e L H Q φ y z hL cφ cy cz
    (fun x hx => (hbounds x hx).2.2.2.1) hweight hQeq t ht
  have hstep : C₁ * ε / L ≤ C * ε / L :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁C hε0) hL0.le
  have hb := hbounds t ht
  refine ⟨⟨hb.1.trans hstep, hb.2.1.trans hstep, hb.2.2.1,
    hb.2.2.2.1, hb.2.2.2.2.trans hstep⟩, ?_⟩
  exact hcharge'.trans (mul_le_mul_of_nonneg_right hC₂C (by positivity))

end EmcsfAcExtension.Global
