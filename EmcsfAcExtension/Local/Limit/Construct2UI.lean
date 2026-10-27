module

public import EmcsfAcExtension.Local.Limit.Construct2Settings
import EmcsfAcExtension.Local.Limit.Construct2Cauchy

/-! # Uniform integrability for the actual full-triangle approximants

The P2 repair in internal project record, conditional only on the two explicitly pending
producer contracts. The mixed Cauchy and common comparison setting premises
of the analytic helpers are both discharged inside the construction.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
[internal]
Construct whole-triangle classical approximants whose actual j/k envelopes
are uniformly integrable. Only the pending internal project record contracts
are premises; all Cauchy, setting and smallness obligations are discharged.
The positive thresholds are universal, before time, coupling, AC datum and
every approximation derivative. This is the constructed-sequence P2 repair. -/
theorem Null.constructed_envelope_ui_of_inputs
    (hex : WholeTriangleExistenceStmt) (hstab : StabExtendedStmt) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T →
        AbsolutelyContinuousOnInterval h 0 T → datumVar h T ≤ ε →
        chargedScale e h T ≤ δ →
        ∃ (hn : ℕ → ℝ → ℂ) (Sn : ℕ → Fields),
          (∀ n, ContDiffOn ℝ 1 (hn n) (Icc 0 T)) ∧ (∀ n, hn n 0 = h 0) ∧
          Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) ∧
          Tendsto (fun n => eVariationOn (hn n - h) (Icc 0 T)) atTop (𝓝 0) ∧
          (∀ n, IsC1Solution e (Sn n) (triangle 0 T) ∧ IsRestartData (Sn n) (hn n) T) ∧
          UnifIntegrable (fun n v => (outEnv 0 (jC1 (triangle 0 T) (Sn n)) v).toReal)
            1 (volume.restrict (Icc 0 T)) ∧
          UnifIntegrable (fun n u => (inEnv T (kC1 e (triangle 0 T) (Sn n)) u).toReal)
            1 (volume.restrict (Icc 0 T)) := by
  obtain ⟨η, hη, hui⟩ := Null.envelope_ui_of_inputs hstab 1 (by norm_num)
  obtain ⟨ε, δ, q, hε, hδ, _, happ⟩ := Null.comparison_approximants_of_inputs hex η hη
  refine ⟨ε, δ, hε, hδ, ?_⟩
  intro T e h hT hac hsmall hscale
  obtain ⟨hn, Sn, hs, hv, herr, hevar, _, hset, hcomparison⟩ :=
    happ T e h hT hac hsmall hscale
  obtain ⟨hj, hk⟩ := hui T e q (2 * datumM h T) Sn hn h hset hac hv herr hcomparison
  exact ⟨hn, Sn, hs, hv, herr, hevar, fun n => ⟨(hset n).c1, (hset n).data⟩, hj, hk⟩

end EmcsfAcExtension.Local
