module

public import EmcsfAcExtension.Global.Observation.BoundaryConsequences

/-! # Physical boundary values from normalized clock control

This is the checked internal project record internal project record bridge. The mass is
rescaled by the physical length scale and the scalar norm is unchanged
by the parallel gauge. Source: charged_SF_new_version.tex:L2082–2123.
-/

public section

open Set MeasureTheory Complex
namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Clock control supplies all three physical boundary inputs needed by the
core estimates. The positive constant depends only on `T`, before every
profile, central datum, physical scale, radius and coupling. The source
consumer must derive the tangent and failed-observation inputs. -/
theorem physical_boundary_inputs {T : ℝ} (hT : 0 ≤ T) :
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
          ((‖φ t - H - P / (L : ℝ)‖ ≤ C * ε / L ∧ |m t - M| ≤ C * ε / L ∧
            m t ≤ 2 ∧ ‖φ t‖ ≤ ‖H‖ + 2 / L ∧ ‖y t + P / (L : ℝ)‖ ≤ C * ε / L) ∧
          |Q t - Q 0| ≤ C * (|e| * L * (1 + ‖H‖))) ∧
          ∀ (s b mPhys : ℝ) (phiPhys : ℂ),
          0 < s → 0 < b → L = b / s → m t = mPhys / s → ‖φ t‖ = ‖phiPhys‖ →
          |mPhys / s - M| ≤ 1 ∧ mPhys ≤ 2 * s ∧ ‖phiPhys‖ ≤ ‖H‖ + 2 * s / b := by
  obtain ⟨C,hC,hcontrol⟩ := co_boundary_control_of_clock_tangents hT
  refine ⟨C,hC,?_⟩
  intro L ε e M H P φ y z m g Q hL hε0 hε hP hM hm0 hφ0 cφ cy cz cm cg cQ hg ha hβ dφ dm dQ t ht
  have hbnd := hcontrol L ε e M H P φ y z m g Q hL hε0 hε hP hM hm0 hφ0
    cφ cy cz cm cg cQ hg ha hβ dφ dm dQ t ht
  refine ⟨hbnd, ?_⟩
  intro s b mPhys phiPhys hs hb hscale hmTrace hphiTrace
  have hCL : C*ε/L ≤ 1 := by
    have he : C*ε ≤ 1 := by simpa only [mul_comm] using (le_div_iff₀ hC).mp hε
    exact (div_le_iff₀ (zero_lt_one.trans_le hL)).mpr (by simpa only [one_mul] using he.trans hL)
  have hclose : |mPhys/s-M| ≤ 1 := by
    simpa only [hmTrace] using hbnd.1.2.1.trans hCL
  have hmass : mPhys ≤ 2*s :=
    (div_le_iff₀ hs).mp (by simpa only [hmTrace] using hbnd.1.2.2.1)
  have hdiv : 2/L = 2*s/b := by rw [hscale]; field_simp
  refine ⟨hclose,hmass,?_⟩
  calc
    _ = ‖φ t‖ := hphiTrace.symm
    _ ≤ ‖H‖+2/L := hbnd.1.2.2.2.1
    _ = _ := by rw [hdiv]

end EmcsfAcExtension.Global.Observation
