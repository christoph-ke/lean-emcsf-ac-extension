module

public import EmcsfAcExtension.Local.Defs.Params
import EmcsfAcExtension.Infra.W11.MollifyData
import EmcsfAcExtension.Infra.W11.Approximation
import EmcsfAcExtension.Infra.W11.Completeness

/-!
# Smooth data preserving the exact smallness thresholds

Export the full internal project record smooth-data record for
`charged_SF_new_version.tex:L6350–L6371`.
Global C∞ approximants preserve the vertex, decrease variation and `datumM`,
converge uniformly and in W¹¹, and preserve both original smallness thresholds,
including equality. The estimates are uniform in the datum, interval, coupling,
and thresholds; no derivative supremum bound is needed.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace EmcsfAcExtension.Local.Null

/-- [node restart-sec-independent-null-construction#smallness-preserving-smooth-data]
Global C∞ approximation of AC data, with exact vertex and nonincreasing variation.
The variations and `datumM` converge, and the functions converge uniformly and in
both L¹ parts of W¹¹. Every original variation and charged-scale threshold holds
for every approximant, including equality cases. All coefficients are universal,
independent of `T`, `h`, `e`, and both thresholds. Here `∞` is Mathlib's C∞ order. -/
theorem smallness_preserving_smooth_data_full {T : ℝ} {h : ℝ → ℂ} (hT : 0 < T)
    (hac : AbsolutelyContinuousOnInterval h 0 T) :
    ∃ hn : ℕ → ℝ → ℂ, (∀ n, ContDiff ℝ ∞ (hn n)) ∧
      (∀ n, hn n 0 = h 0) ∧
      (∀ n, datumVar (hn n) T ≤ datumVar h T) ∧
      Tendsto (fun n => datumVar (hn n) T) atTop (𝓝 (datumVar h T)) ∧
      TendstoUniformlyOn hn h atTop (Icc 0 T) ∧
      Tendsto (fun n => ∫ x in 0..T, ‖hn n x - h x‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x in 0..T, ‖deriv (hn n) x - deriv h x‖) atTop (𝓝 0) ∧
      Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) ∧
      (∀ n, datumM (hn n) T ≤ datumM h T) ∧
      Tendsto (fun n => datumM (hn n) T) atTop (𝓝 (datumM h T)) ∧
      ∀ e εstar δstar : ℝ, datumVar h T ≤ εstar → chargedScale e h T ≤ δstar →
        ∀ n, datumVar (hn n) T ≤ εstar ∧ chargedScale e (hn n) T ≤ δstar := by
  obtain ⟨hn, hs, hv, hb, ht⟩ :=
    W11.exists_smooth_variation_nonincreasing_approximation hT hac
  have hacn n : AbsolutelyContinuousOnInterval (hn n) 0 T :=
    ((hs n).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval
  have hBV n := (hacn n).boundedVariationOn_Icc hT.le
  have hBVh := hac.boundedVariationOn_Icc hT.le
  have hvar : Tendsto (fun n => datumVar (hn n) T) atTop (𝓝 (datumVar h T)) :=
    W11.tendsto_variation_of_sub hBV hBVh ht
  have hpoint n x (hx : x ∈ Icc 0 T) : ‖hn n x - h x‖ ≤ datumVar (hn n - h) T := by
    simpa only [W11.intervalDist_zero, hv, sub_self, norm_zero, zero_add] using
      W11.norm_sub_le_intervalDist (hBV n) hBVh hx
  have hunif : TendstoUniformlyOn hn h atTop (Icc 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(tendsto_order.1 ht).2 ε hε] with n hn' x hx
    rw [dist_comm, dist_eq_norm]
    exact (hpoint n x hx).trans_lt hn'
  have hL1 : Tendsto (fun n => ∫ x in 0..T, ‖hn n x - h x‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => intervalIntegral.integral_nonneg hT.le
      (fun _ _ => norm_nonneg _)) _ (by simpa using ht.const_mul T)
    intro n
    rw [intervalIntegral.integral_of_le hT.le]
    calc
      _ ≤ ∫ x in Ioc 0 T, datumVar (hn n - h) T := by
        apply integral_mono_of_nonneg (ae_of_all _ (fun x => norm_nonneg _))
          (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        exact hpoint n x ⟨hx.1.le, hx.2⟩
      _ = T * datumVar (hn n - h) T := by simp [hT.le]
  have hderiv : Tendsto (fun n => ∫ x in 0..T, ‖deriv (hn n) x - deriv h x‖)
      atTop (𝓝 0) := by
    have heq n : (∫ x in 0..T, ‖deriv (hn n) x - deriv h x‖) =
        datumVar (hn n - h) T :=
      (W11.variation_sub_eq_integral hT.le (hacn n) hac).symm
    simpa only [heq] using ht
  have hM n : datumM (hn n) T ≤ datumM h T := by
    simp only [datumM_def, hv]
    linarith [hb n]
  have hMt : Tendsto (fun n => datumM (hn n) T) atTop (𝓝 (datumM h T)) := by
    simpa only [datumM_def, hv] using
      (tendsto_const_nhds (x := 1 + ‖h 0‖)).add (hvar.const_mul 10)
  refine ⟨hn, hs, hv, hb, hvar, hunif, hL1, hderiv, ht, hM, hMt, ?_⟩
  intro e εstar δstar hε hδ n
  refine ⟨(hb n).trans hε, le_trans ?_ hδ⟩
  unfold chargedScale
  exact mul_le_mul_of_nonneg_left (hM n)
    (mul_nonneg (abs_nonneg e) (div_nonneg hT.le (by norm_num)))

end EmcsfAcExtension.Local.Null
