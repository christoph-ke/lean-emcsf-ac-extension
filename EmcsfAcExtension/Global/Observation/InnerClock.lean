module

public import EmcsfAcExtension.Global.Observation.Window
public import EmcsfAcExtension.Global.Observation.InnerNormalization
import EmcsfAcExtension.Infra.Level.Clock
import Mathlib

/-! # The inner clock on a reserved level segment

The clock has density twice the outgoing expansion in the outer chart.
Its inverse supplies the two inner label rates. The inner chart retains
the outer gauge. Source: charged_SF_new_version.tex:L2741–2755; internal project record (D4), (N0).
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Construct the normalized inner null maps from a C¹ level segment whose
clock density has the fixed lower bound `2c`. The reserved segment and
`K ≤ 2cB` give the entire requested clock window. All inverse rates and
closed-endpoint derivatives are derived internally. The radius, optical
bound and label budget precede all fields and backgrounds; there are
no additional estimate constants and no gauge change. -/
theorem inner_maps_of_reserved_level_segment
    (S : Fields) {g : ℝ → ℝ} {B K c ρ : ℝ}
    (hB : 0 < B) (hK : 0 < K) (hc : 0 < c) (hbudget : K ≤ 2 * c * B)
    (hg : ContinuousOn g (Icc (-B) B))
    (hnu : ContinuousOn (fun v => S.nu (g v) v) (Icc (-B) B))
    (hlam : ContinuousOn (fun v => S.lam (g v) v) (Icc (-B) B))
    (hopt : ∀ v ∈ Icc (-B) B,
      -S.nu (g v) v ∈ Icc c (1 / 2) ∧ S.lam (g v) v ∈ Icc c (1 / 2))
    (hroot : ∀ v ∈ Icc (-B) B, S.r (g v) v = ρ)
    (hderiv : ∀ v ∈ Icc (-B) B,
      HasDerivWithinAt g (S.lam (g v) v / (-S.nu (g v) v)) (Icc (-B) B) v) :
    ∃ clock U V : ℝ ≃o ℝ,
      ContDiff ℝ 1 (clock : ℝ → ℝ) ∧ ContDiff ℝ 1 (clock.symm : ℝ → ℝ) ∧
      clock 0 = 0 ∧
      (∀ v ∈ Icc (-B) B, HasDerivAt (clock : ℝ → ℝ) (2 * S.lam (g v) v) v) ∧
      ContDiff ℝ 1 (U : ℝ → ℝ) ∧ ContDiff ℝ 1 (V : ℝ → ℝ) ∧
      ContDiff ℝ 1 (U.symm : ℝ → ℝ) ∧ ContDiff ℝ 1 (V.symm : ℝ → ℝ) ∧
      (∀ x, 0 < deriv (U : ℝ → ℝ) x) ∧ (∀ x, 0 < deriv (V : ℝ → ℝ) x) ∧
      ∀ t ∈ Icc (-K) K,
        clock.symm t ∈ Icc (-B) B ∧ U t = g (clock.symm t) ∧ V t = clock.symm t ∧
        S.r (U t) (V t) = ρ ∧
        deriv (U : ℝ → ℝ) t ∈ Icc 1 (1 / (2 * c)) ∧
        deriv (V : ℝ → ℝ) t ∈ Icc 1 (1 / (2 * c)) ∧
        (nullPullback S U V).nu t t = -1 / 2 ∧
        (nullPullback S U V).lam t t = 1 / 2 ∧
        (nullPullback S U V).A t t = S.A (U t) (V t) / (-2 * S.nu (U t) (V t)) := by
  have hBB : -B ≤ B := by linarith only [hB]
  have hKK : -K ≤ K := by linarith only [hK]
  have hz : (0 : ℝ) ∈ Icc (-B) B := ⟨by linarith only [hB], hB.le⟩
  let w := fun v => 2 * S.lam (g v) v
  let primitive := Level.integralClock w (-B)
  let f := fun v => primitive v - primitive 0
  have cw : ContinuousOn w (Icc (-B) B) := hlam.const_mul 2
  have iw := cw.intervalIntegrable_of_Icc (μ := volume) hBB
  have cp : ContinuousOn primitive (Icc (-B) B) := by
    simpa only [uIcc_of_le hBB] using
      (Level.absolutelyContinuousOnInterval_integralClock iw).continuousOn
  have cf : ContinuousOn f (Icc (-B) B) := cp.sub continuousOn_const
  have df (v) (hv : v ∈ Icc (-B) B) :
      HasDerivWithinAt f (w v) (Icc (-B) B) v :=
    (Level.hasDerivWithinAt_integralClock hBB cw hv).sub_const (primitive 0)
  have hwpos (v) (hv : v ∈ Icc (-B) B) : 0 < w v :=
    mul_pos (by norm_num) (hc.trans_le (hopt v hv).2.1)
  obtain ⟨clock, hclock, hinverse, heq, hdclock, _⟩ :=
    c1_orderIso_of_positive_clock hBB cf cw hwpos (fun v hv =>
      (df v (Ioo_subset_Icc_self hv)).hasDerivAt (Icc_mem_nhds hv.1 hv.2))
  have hform (x y : ℝ) (hx : x ∈ Icc (-B) B) (hy : y ∈ Icc (-B) B) :
      IntegralForm f w x y := by
    refine ⟨iw.mono_set (uIcc_subset_uIcc
      (by simpa only [uIcc_of_le hBB] using hx)
      (by simpa only [uIcc_of_le hBB] using hy)), ?_⟩
    have hi := Level.integralClock_sub iw
      (by simpa only [uIcc_of_le hBB] using hx)
      (by simpa only [uIcc_of_le hBB] using hy)
    change (primitive y - primitive 0) - (primitive x - primitive 0) = _
    rw [← hi]
    ring
  have hwindow : Icc (-K) K ⊆ f '' Icc (-B) B :=
    inner_clock_window_of_speed hB.le hbudget cf (sub_self _)
      (hform (-B) 0 (left_mem_Icc.mpr hBB) hz)
      (hform 0 B hz (right_mem_Icc.mpr hBB))
      (fun v hv => mul_le_mul_of_nonneg_left (hopt v hv).2.1 (by norm_num))
  have hmem (t : ℝ) (ht : t ∈ Icc (-K) K) : clock.symm t ∈ Icc (-B) B := by
    obtain ⟨v, hv, hfv⟩ := hwindow ht
    have he : clock v = t := (heq v hv).trans hfv
    simpa only [← he, OrderIso.symm_apply_apply] using hv
  have hmemInterior (t : ℝ) (ht : t ∈ Ioo (-K) K) : clock.symm t ∈ Ioo (-B) B := by
    exact ⟨(hmem (-K) (left_mem_Icc.mpr hKK)).1.trans_lt (clock.symm.strictMono ht.1),
      (clock.symm.strictMono ht.2).trans_le (hmem K (right_mem_Icc.mpr hKK)).2⟩
  let v₀ := fun t => clock.symm t
  let u₀ := fun t => g (v₀ t)
  have cv : ContinuousOn v₀ (Icc (-K) K) := clock.symm.continuous.continuousOn
  have cu : ContinuousOn u₀ (Icc (-K) K) := hg.comp cv hmem
  have cn : ContinuousOn (fun t => S.nu (u₀ t) (v₀ t)) (Icc (-K) K) := hnu.comp cv hmem
  have cl : ContinuousOn (fun t => S.lam (u₀ t) (v₀ t)) (Icc (-K) K) := hlam.comp cv hmem
  have hop (t) (ht : t ∈ Icc (-K) K) :
      -S.nu (u₀ t) (v₀ t) ∈ Icc c (1 / 2) ∧
        S.lam (u₀ t) (v₀ t) ∈ Icc c (1 / 2) := hopt _ (hmem t ht)
  have dv (t) (ht : t ∈ Ioo (-K) K) :
      HasDerivAt v₀ (1 / (2 * S.lam (u₀ t) (v₀ t))) t := by
    have hm := hmem t (Ioo_subset_Icc_self ht)
    have hd := hdclock (clock.symm t) hm
    have hdinv := hd.of_local_left_inverse clock.symm.continuous.continuousAt
      (hwpos _ hm).ne' (Filter.Eventually.of_forall clock.apply_symm_apply)
    simpa only [v₀, u₀, w, one_div] using hdinv
  have du (t) (ht : t ∈ Ioo (-K) K) :
      HasDerivAt u₀ (1 / (-2 * S.nu (u₀ t) (v₀ t))) t := by
    have hm := hmemInterior t ht
    have hdg := (hderiv _ (Ioo_subset_Icc_self hm)).hasDerivAt (Icc_mem_nhds hm.1 hm.2)
    have hn : S.nu (u₀ t) (v₀ t) ≠ 0 := by
      have hh := hc.trans_le (hop t (Ioo_subset_Icc_self ht)).1.1
      exact (neg_pos.mp hh).ne
    have hl : S.lam (u₀ t) (v₀ t) ≠ 0 :=
      (hc.trans_le (hop t (Ioo_subset_Icc_self ht)).2.1).ne'
    dsimp only [u₀, v₀] at hn hl
    convert hdg.comp t (dv t ht) using 1 <;> dsimp only [u₀, v₀, Function.comp_def]
    field_simp [hn, hl]
  obtain ⟨U, V, hU, hV, hUi, hVi, hUp, hVp, hUV, hnorm⟩ :=
    inner_null_normalization_of_clock_rates S hKK hc cu cv cn cl hop du dv
  refine ⟨clock, U, V, hclock, hinverse, ?_, hdclock, hU, hV, hUi, hVi, hUp, hVp, ?_⟩
  · rw [heq 0 hz]
    exact sub_self _
  · intro t ht
    have huv := hUV t ht
    have hn := hnorm t ht
    refine ⟨hmem t ht, huv.1, huv.2, ?_, hn.1, hn.2.1,
      hn.2.2.2.2.1, hn.2.2.2.2.2.1, hn.2.2.2.2.2.2.1⟩
    rw [huv.1, huv.2]
    exact hroot _ (hmem t ht)

end EmcsfAcExtension.Global.Observation
