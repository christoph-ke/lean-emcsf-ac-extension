module

public import EmcsfAcExtension.Local.Limit.Inputs
import EmcsfAcExtension.Infra.W11.Approximation
import EmcsfAcExtension.Local.Apriori.Bootstrap

/-! # Admissible whole-triangle approximation sequences

The threshold margins of internal project record internal project record are
discharged here. A single tail makes every approximant admissible for both
construction and the a priori estimate. No derivative supremum is assumed.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
Choose classical solutions on the same complete triangle from AC data.
The thresholds and a priori constant are universal, independent of time,
coupling, datum and all approximation derivatives. The only pending input
is the exact internal project record contract; a single tail satisfies both producers.
This constructs approximants, without asserting a strong limiting solution. -/
theorem Null.whole_triangle_approximants_of_inputs
    (hex : WholeTriangleExistenceStmt) :
    ∃ ε δ C : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < C ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T →
        AbsolutelyContinuousOnInterval h 0 T →
        datumVar h T ≤ ε → chargedScale e h T ≤ δ →
        ∃ (hn : ℕ → ℝ → ℂ) (Sn : ℕ → Fields),
          (∀ n, ContDiffOn ℝ 1 (hn n) (Icc 0 T)) ∧
          (∀ n, hn n 0 = h 0) ∧
          Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) ∧
          Tendsto (fun n => eVariationOn (hn n - h) (Icc 0 T)) atTop (𝓝 0) ∧
          Tendsto (fun n => datumVar (hn n) T) atTop (𝓝 (datumVar h T)) ∧
          (∀ n, IsC1Solution e (Sn n) (triangle 0 T) ∧ IsRestartData (Sn n) (hn n) T) ∧
          ∀ n, SmoothBounds C e T (datumVar (hn n) T) (datumM (hn n) T) (Sn n) := by
  obtain ⟨εc, δc, hεc, hδc, hc⟩ := hex
  obtain ⟨εa, δa, C, hεa, hδa, hC, ha⟩ := Null.smooth_apriori_box
  let εu := min εc εa
  let δu := min δc δa
  have hεu : 0 < εu := lt_min hεc hεa
  have hδu : 0 < δu := lt_min hδc hδa
  refine ⟨εu / 2, δu / 2, C, by positivity, by positivity, hC, ?_⟩
  intro T e h hT hac hε hδ
  obtain ⟨hn, hs, hv, herr, hvar, _⟩ := Stab.smooth_data_approximation_choice hT hac
  have hscale : Tendsto (fun n => chargedScale e (hn n) T) atTop
      (𝓝 (chargedScale e h T)) := by
    unfold chargedScale datumM
    simpa only [hv] using
      ((tendsto_const_nhds.add (hvar.const_mul 10)).const_mul (|e| * (T / 2)))
  have hεlt : datumVar h T < εu := lt_of_le_of_lt hε (by linarith only [hεu])
  have hδlt : chargedScale e h T < δu := lt_of_le_of_lt hδ (by linarith only [hδu])
  have hev := (tendsto_order.1 hvar).2 εu hεlt
  have hec := (tendsto_order.1 hscale).2 δu hδlt
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and hec)
  let hn' n := hn (n + N)
  have hs' n : ContDiffOn ℝ 1 (hn' n) (Icc 0 T) := hs _
  have hε' n : datumVar (hn' n) T ≤ εu := (hN (n + N) (Nat.le_add_left _ _)).1.le
  have hδ' n : chargedScale e (hn' n) T ≤ δu := (hN (n + N) (Nat.le_add_left _ _)).2.le
  have hex' n : ∃ S, IsC1Solution e S (triangle 0 T) ∧ IsRestartData S (hn' n) T :=
    hc T e (hn' n) hT (hs' n) ((hε' n).trans (min_le_left _ _))
      ((hδ' n).trans (min_le_left _ _))
  choose Sn hc1 hd using hex'
  have hevar : Tendsto (fun n => eVariationOn (hn n - h) (Icc 0 T)) atTop (𝓝 0) := by
    have heq n : eVariationOn (hn n - h) (Icc 0 T) =
        ENNReal.ofReal (datumVar (hn n - h) T) := by
      have hacn : AbsolutelyContinuousOnInterval (hn n) 0 T := by
        apply ContDiffOn.absolutelyContinuousOnInterval
        simpa only [uIcc_of_le hT.le] using hs n
      symm
      apply ENNReal.ofReal_toReal
      exact (hacn.sub hac).boundedVariationOn_Icc hT.le
    simpa only [Function.comp_def, ← heq, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp herr
  refine ⟨hn', Sn, hs', fun n => hv _, herr.comp (tendsto_add_atTop_nat N),
    hevar.comp (tendsto_add_atTop_nat N),
    hvar.comp (tendsto_add_atTop_nat N), fun n => ⟨hc1 n, hd n⟩, ?_⟩
  intro n
  exact ha T e (Sn n) (hn' n) hT (hc1 n) (hd n)
    ((hε' n).trans (min_le_right _ _)) ((hδ' n).trans (min_le_right _ _))

end EmcsfAcExtension.Local
