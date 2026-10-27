module

public import EmcsfAcExtension.Global.Interaction.NEstimateMeasurable
import EmcsfAcExtension.Global.Renormalized.WeakTransfer

/-! # Integral decomposition on the finite stopped exterior

Tonelli changes the label-first source norm to the row integrals used by
the landed estimates. The seven measurable contributions can then be
summed without an integrability premise. Source: `charged_SF_new_version.tex:L3625–L3745`.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.InteractionEstimate

private theorem zeroExtension_row_integral {ui u₀ u₁ v₀ ρ : ℝ} {S : Fields}
    {vb : ℝ → ℝ} {N : ℕ} (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N)
    (k : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ u, ∫⁻ v, (exteriorDomain ui u₀ u₁ vb).indicator k (u, v)) =
      ∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0, k (u, v) := by
  let D := exteriorDomain ui u₀ u₁ vb
  have hs : Function.support (fun u => ∫⁻ v, D.indicator k (u, v)) ⊆ Icc u₀ u₁ := by
    intro u hu
    by_contra hn
    have hz (v : ℝ) : D.indicator k (u, v) = 0 :=
      indicator_of_notMem (fun h => hn ⟨h.2.1, h.2.2.1⟩) _
    simp only [hz, lintegral_zero, Function.mem_support, ne_eq, not_true_eq_false] at hu
  rw [← setLIntegral_eq_of_support_subset hs]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro u hu
  have heq : (fun v => D.indicator k (u, v)) =
      (Icc (vb u) 0).indicator (fun v => k (u, v)) := by
    ext v
    by_cases hv : v ∈ Icc (vb u) 0
    · rw [indicator_of_mem hv,
        indicator_of_mem (show (u, v) ∈ D from finite_boundary_row B u hu ⟨rfl, hv⟩)]
    · rw [indicator_of_notMem hv,
        indicator_of_notMem (fun h => hv ⟨h.2.2.2, h.1.2.2.2⟩)]
  change (∫⁻ v, D.indicator k (u, v)) = _
  rw [heq, lintegral_indicator measurableSet_Icc]

/-- [internal]
The actual label-first source norm is bounded by the sum of the seven
actual row contributions. Measurability, the moving-domain Tonelli step,
and the rough-derivative representative change are discharged here.
No estimate constant or finiteness hypothesis occurs. -/
theorem sourceInteraction_le_sum_contributions {ui e u₀ u₁ v₀ ρ : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) :
    sourceInteraction e S (exteriorDomain ui u₀ u₁ vb) v₀ ≤
      ∑ i : Fin 7, ∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ‖sourceContribution e S vb i u v‖ := by
  classical
  let D := exteriorDomain ui u₀ u₁ vb
  let f := D.indicator (fun p => ‖weightedJSource e S p.1 p.2‖ₑ)
  let K := fun i : Fin 7 => D.indicator (fun p => ‖sourceContribution e S vb i p.1 p.2‖ₑ)
  have hf : Measurable f := measurable_exterior_indicator B _
    ((Renormalized.continuousOn_weightedJSource hS (fun p hp =>
      ⟨hp.1, (B.off_axis p.1 ⟨hp.2.1, hp.2.2.1⟩).trans_le hp.2.2.2⟩)).enorm)
  have hK (i : Fin 7) : Measurable (K i) := by
    simpa only [K, D, enorm_indicator_eq_indicator_enorm, Function.uncurry] using!
      (measurable_sourceContribution hS B i).enorm
  have hsec (v : ℝ) :
      (∫⁻ u in {u | (u, v) ∈ D}, ‖weightedJSource e S u v‖ₑ) = ∫⁻ u, f (u, v) := by
    have hm : MeasurableSet {u | (u, v) ∈ D} :=
      (measurableSet_exteriorDomain B).preimage (measurable_id.prodMk measurable_const)
    rw [← lintegral_indicator hm]
    rfl
  have hs : Function.support (fun v => ∫⁻ u, f (u, v)) ⊆ Icc v₀ 0 := by
    intro v hv
    by_contra hn
    have hz (u : ℝ) : f (u, v) = 0 := by
      apply indicator_of_notMem
      intro hp
      exact hn ⟨(finite_boundary_label_bounds B u ⟨hp.2.1, hp.2.2.1⟩).1.trans hp.2.2.2,
        hp.1.2.2.2⟩
    simp only [hz, lintegral_zero, Function.mem_support, ne_eq, not_true_eq_false] at hv
  have hpoint (p : ℝ × ℝ) : f p ≤ ∑ i, K i p := by
    by_cases hp : p ∈ D
    · simp only [f, K, indicator_of_mem hp]
      have hrow := finite_boundary_row B p.1 ⟨hp.2.1, hp.2.2.1⟩
      have heq := weightedJSource_seven_terms hS (B.off_axis p.1 ⟨hp.2.1, hp.2.2.1⟩)
        hp.2.2.2 (fun q hq => (hrow ⟨hq.1, hq.2.1, hq.2.2.trans hp.1.2.2.2⟩).1)
      have heq' : weightedJSource e S p.1 p.2 = ∑ i, sourceContribution e S vb i p.1 p.2 := by
        rw [heq]
        simp only [sourceContribution, Fin.sum_univ_succ, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
        abel
      rw [heq']
      exact enorm_sum_le _ _
    · simp only [f, K, indicator_of_notMem hp, Finset.sum_const_zero, le_refl]
  calc
    _ = ∫⁻ v, ∫⁻ u, f (u, v) := by
      change (∫⁻ v in Icc v₀ 0, ∫⁻ u in {u | (u, v) ∈ D},
        ‖weightedJSource e S u v‖ₑ) = _
      calc
        _ = ∫⁻ v in Icc v₀ 0, ∫⁻ u, f (u, v) :=
          setLIntegral_congr_fun measurableSet_Icc (fun v _ => hsec v)
        _ = _ := setLIntegral_eq_of_support_subset hs
    _ = ∫⁻ u, ∫⁻ v, f (u, v) := lintegral_lintegral_swap (hf.comp measurable_swap).aemeasurable
    _ ≤ ∫⁻ u, ∫⁻ v, ∑ i, K i (u, v) :=
      lintegral_mono (fun u => lintegral_mono (fun v => hpoint (u, v)))
    _ = ∑ i, ∫⁻ u, ∫⁻ v, K i (u, v) := by
      calc
        _ = ∫⁻ u, ∑ i, ∫⁻ v, K i (u, v) := by
          apply lintegral_congr
          intro u
          exact lintegral_finsetSum _ (fun i _ =>
            (hK i).comp (measurable_const.prodMk measurable_id))
        _ = _ := lintegral_finsetSum _ (fun i _ => (hK i).lintegral_prod_right')
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [zeroExtension_row_integral B]
      simp only [ofReal_norm]

end EmcsfAcExtension.Global.InteractionEstimate
