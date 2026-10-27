module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.Params
import EmcsfAcExtension.Infra.W11.Approximation
public import EmcsfAcExtension.Local.Construction.ContinuationInputs
import EmcsfAcExtension.Local.Construction.Whole

/-! # Whole-triangle approximants on the C¹ construction route

The landed approximation theorem gives exact vertex preservation and strong
variation-error convergence. Positive smallness margins make a tail admissible
for a whole-triangle existence theorem. No uniform first-derivative bound on
the approximating data is asserted or consumed.
-/

public section

open Set Filter MeasureTheory Topology
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Strong vertex-preserving approximation makes the charged scale
converge with the variation. The coefficient and canonical background
are the literal ones of `chargedScale`, uniformly in the approximation. -/
theorem chargedScale_tendsto_of_vertex_variation {T e : ℝ}
    {hn : ℕ → ℝ → ℂ} {h : ℝ → ℂ} (hv : ∀ n, hn n 0 = h 0)
    (hvar : Tendsto (fun n => datumVar (hn n) T) atTop (𝓝 (datumVar h T))) :
    Tendsto (fun n => chargedScale e (hn n) T) atTop (𝓝 (chargedScale e h T)) := by
  simp only [chargedScale, datumM, hv]
  exact tendsto_const_nhds.mul
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hvar))

/-- Classical whole-triangle approximants from classical data existence.
The input is the construction theorem's literal statement, an explicit
`_of_` helper premise. It is not a new pending producer input and does
not replace the proof of whole-triangle existence.

Universal thresholds `ε,δ` precede all data. The final AC datum uses half
of each threshold; its approximants then satisfy the original thresholds
after a tail shift. Their first-derivative norms may depend on the index.
The error converges in `eVariationOn`, as required by the limit layer. -/
theorem whole_triangle_approximants_of_existence
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hexistence : ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T →
      ContDiffOn ℝ 1 h (Icc 0 T) → datumVar h T ≤ ε → chargedScale e h T ≤ δ →
      ∃ F : Fields, IsC1Solution e F (triangle 0 T) ∧ IsRestartData F h T)
    {T e : ℝ} {h : ℝ → ℂ} (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval h 0 T)
    (hvar : datumVar h T ≤ ε / 2) (hscale : chargedScale e h T ≤ δ / 2) :
    ∃ (hn : ℕ → ℝ → ℂ) (Fn : ℕ → Fields),
      (∀ n, ContDiffOn ℝ 1 (hn n) (Icc 0 T) ∧ hn n 0 = h 0 ∧
        datumVar (hn n) T ≤ ε ∧ chargedScale e (hn n) T ≤ δ ∧
        IsC1Solution e (Fn n) (triangle 0 T) ∧ IsRestartData (Fn n) (hn n) T) ∧
      Tendsto (fun n => eVariationOn (hn n - h) (Icc 0 T)) atTop (𝓝 0) := by
  obtain ⟨hn, hc, hv, _herr, ht⟩ := Null.smallness_preserving_smooth_data hT hac
  have hb n : BoundedVariationOn (hn n) (Icc 0 T) := by
    have hc' : ContDiffOn ℝ 1 (hn n) (uIcc 0 T) := by
      rw [uIcc_of_le hT.le]
      exact hc n
    exact hc'.absolutelyContinuousOnInterval.boundedVariationOn_Icc hT.le
  have hbh : BoundedVariationOn h (Icc 0 T) := hac.boundedVariationOn_Icc hT.le
  have htvar : Tendsto (fun n => datumVar (hn n) T) atTop (𝓝 (datumVar h T)) :=
    W11.tendsto_variation_of_sub hb hbh ht
  have htscale := chargedScale_tendsto_of_vertex_variation (e := e) hv htvar
  have heventvar : ∀ᶠ n in atTop, datumVar (hn n) T < ε :=
    htvar.eventually (gt_mem_nhds (by linarith : datumVar h T < ε))
  have heventscale : ∀ᶠ n in atTop, chargedScale e (hn n) T < δ :=
    htscale.eventually (gt_mem_nhds (by linarith : chargedScale e h T < δ))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (heventvar.and heventscale)
  let hn' : ℕ → ℝ → ℂ := fun n => hn (n + N)
  have hadmissible n : datumVar (hn' n) T ≤ ε ∧ chargedScale e (hn' n) T ≤ δ :=
    ⟨(hN (n + N) (Nat.le_add_left N n)).1.le,
      (hN (n + N) (Nat.le_add_left N n)).2.le⟩
  have hex n : ∃ F : Fields, IsC1Solution e F (triangle 0 T) ∧ IsRestartData F (hn' n) T :=
    hexistence T e (hn' n) hT (hc (n + N)) (hadmissible n).1 (hadmissible n).2
  choose Fn hFn using hex
  refine ⟨hn', Fn, ?_, ?_⟩
  · intro n
    exact ⟨hc (n + N), hv (n + N), (hadmissible n).1, (hadmissible n).2,
      (hFn n).1, (hFn n).2⟩
  · have herrorfinite n : eVariationOn (hn n - h) (Icc 0 T) ≠ ⊤ :=
      (hb n).sub hbh
    have herror : Tendsto (fun n => eVariationOn (hn n - h) (Icc 0 T)) atTop (𝓝 0) := by
      have hreal := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
      change Tendsto (fun n => ENNReal.ofReal (datumVar (hn n - h) T))
        atTop (𝓝 (ENNReal.ofReal 0)) at hreal
      have heq : (fun n => ENNReal.ofReal (datumVar (hn n - h) T)) =
          (fun n => eVariationOn (hn n - h) (Icc 0 T)) := by
        funext n
        exact ENNReal.ofReal_toReal (herrorfinite n)
      rw [heq, ENNReal.ofReal_zero] at hreal
      exact hreal
    exact herror.comp (tendsto_add_atTop_nat N)

/-- internal project record's selected whole-triangle approximants on the C¹ reading
of internal project record, starting from a final AC datum. The only
pending inputs are the four approved construction and a priori inputs;
the actual whole-triangle theorem supplies classical existence.

Universal `ε,δ` are chosen before the final AC datum. A half-threshold
margin selects a tail whose members meet the whole-triangle thresholds.
Each approximant has exact vertex value and a solution on the same
complete closed triangle. No uniform first-derivative norm is assumed. -/
theorem whole_triangle_approximants_of_inputs
    (hOriginal : ContinuationOriginalPicardInput)
    (hShort : ContinuationShortPicardInput)
    (hRecovery : ContinuationRecoveryInput)
    (hBound : ContinuationC1BoundInput) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T →
        AbsolutelyContinuousOnInterval h 0 T →
        datumVar h T ≤ ε/2 → chargedScale e h T ≤ δ/2 →
        ∃ (hn : ℕ → ℝ → ℂ) (Fn : ℕ → Fields),
          (∀ n, ContDiffOn ℝ 1 (hn n) (Icc 0 T) ∧ hn n 0 = h 0 ∧
            datumVar (hn n) T ≤ ε ∧ chargedScale e (hn n) T ≤ δ ∧
            IsC1Solution e (Fn n) (triangle 0 T) ∧ IsRestartData (Fn n) (hn n) T) ∧
          Tendsto (fun n => eVariationOn (hn n-h) (Icc 0 T)) atTop (𝓝 0) := by
  obtain ⟨ε,δ,hε,hδ,hex⟩ :=
    whole_triangle_solution_of_inputs hOriginal hShort hRecovery hBound
  refine ⟨ε,δ,hε,hδ,?_⟩
  intro T e h hT hac hvar hscale
  exact whole_triangle_approximants_of_existence hε hδ hex hT hac hvar hscale

end EmcsfAcExtension.Local
