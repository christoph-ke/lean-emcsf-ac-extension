module

public import EmcsfAcExtension.Local.Defs.Params
public import EmcsfAcExtension.Infra.W11.Approximation

/-! # Data parameters under strong representative W¹¹ convergence

The vertex values are allowed to vary. This supplies the trace part of
internal project record item 7.5 for the full general AC sequence statements.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Strong representative W¹¹ convergence preserves variation, literal datum
size, and charged scale. No common vertex is required. All inequalities used
here have coefficient one, independently of time, coupling, and the data. -/
theorem data_parameters_tendsto_of_dataDist {T e : ℝ}
    {hn : ℕ → ℝ → ℂ} {h : ℝ → ℂ} (hT : 0 ≤ T)
    (hacn : ∀ n, AbsolutelyContinuousOnInterval (hn n) 0 T)
    (hac : AbsolutelyContinuousOnInterval h 0 T)
    (hd : Tendsto (fun n => dataDist (hn n) h T) atTop (𝓝 0)) :
    Tendsto (fun n => hn n 0) atTop (𝓝 (h 0)) ∧
    Tendsto (fun n => datumVar (hn n) T) atTop (𝓝 (datumVar h T)) ∧
    Tendsto (fun n => datumM (hn n) T) atTop (𝓝 (datumM h T)) ∧
    Tendsto (fun n => chargedScale e (hn n) T) atTop (𝓝 (chargedScale e h T)) := by
  have hv : Tendsto (fun n => ‖hn n 0 - h 0‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun _ =>
      le_add_of_nonneg_right ENNReal.toReal_nonneg) hd
  have hvar : Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) :=
    squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun _ =>
      le_add_of_nonneg_left (norm_nonneg _)) hd
  have hz := tendsto_iff_norm_sub_tendsto_zero.2 hv
  have hvar' : Tendsto (fun n => datumVar (hn n) T) atTop (𝓝 (datumVar h T)) :=
    W11.tendsto_variation_of_sub (fun n => (hacn n).boundedVariationOn_Icc hT)
      (hac.boundedVariationOn_Icc hT) hvar
  have hM : Tendsto (fun n => datumM (hn n) T) atTop (𝓝 (datumM h T)) :=
    (tendsto_const_nhds.add hz.norm).add (hvar'.const_mul 10)
  exact ⟨hz, hvar', hM, hM.const_mul (|e| * (T / 2))⟩

end EmcsfAcExtension.Local
