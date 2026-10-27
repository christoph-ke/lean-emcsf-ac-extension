module

public import EmcsfAcExtension.Local.Stability.MomentsForcing
public import EmcsfAcExtension.Local.Api.Finite

/-! # Measurable envelopes without an axis continuity assumption

For the ordered nonnegative integrals, Borel measurability on the triangle
and continuity off the axis suffice. Parametrize each open section by the
fixed separable interval `[0,1)`, and include the diagonal separately.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- A Borel field continuous off the axis has a measurable outgoing
envelope, extended by zero outside its label interval. The diagonal is
included separately, so continuity at the axis is not assumed. -/
theorem stab_measurable_outEnv_of_offAxis
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {f : ℝ → ℝ → E} {a b : ℝ}
    (hf : Measurable ((triangle a b).indicator (Function.uncurry f)))
    (hc : ContinuousOn (Function.uncurry f)
      {p : ℝ × ℝ | p ∈ triangle a b ∧ p.1 < p.2}) :
    Measurable ((Icc a b).indicator (outEnv a f)) := by
  classical
  let F := (triangle a b).indicator (Function.uncurry f)
  let g := fun (t : Ico (0 : ℝ) 1) (v : ℝ) => ‖F (a + t.val * (v - a), v)‖ₑ
  have hnot (v : ℝ) (hv : v ∉ Icc a b) (x : ℝ) : (x, v) ∉ triangle a b := by
    intro hp
    exact hv ⟨hp.1.trans hp.2.1, hp.2.2⟩
  have hmap {v : ℝ} (hv : v ∈ Icc a b) (t : Ico (0 : ℝ) 1) :
      (a + t.val * (v - a), v) ∈ triangle a b := by
    have hdelta : 0 ≤ v - a := sub_nonneg.mpr hv.1
    have hlo := mul_nonneg t.2.1 hdelta
    have hhi := mul_le_mul_of_nonneg_right t.2.2.le hdelta
    exact ⟨by linarith only [hlo], by linarith only [hhi], hv.2⟩
  have hm (t : Ico (0 : ℝ) 1) : Measurable (g t) :=
    (hf.comp ((measurable_const.add
      (measurable_const.mul (measurable_id.sub measurable_const))).prodMk measurable_id)).enorm
  have hct (v : ℝ) : Continuous (fun t : Ico (0 : ℝ) 1 => g t v) := by
    by_cases hv : v ∈ Icc a b
    · rcases hv.1.eq_or_lt with rfl | hav
      · change Continuous (fun t : Ico (0 : ℝ) 1 => ‖F (a + t.val * (a - a), a)‖ₑ)
        simpa only [sub_self, mul_zero, add_zero] using
          (continuous_const : Continuous (fun _ : Ico (0 : ℝ) 1 => ‖F (a, a)‖ₑ))
      · have hmp : MapsTo (fun t : Ico (0 : ℝ) 1 => (a + t.val * (v - a), v))
            univ {p : ℝ × ℝ | p ∈ triangle a b ∧ p.1 < p.2} := by
          intro t _
          refine ⟨hmap hv t, ?_⟩
          have ht := mul_lt_mul_of_pos_right t.2.2 (sub_pos.mpr hav)
          linarith only [ht]
        have hcc := hc.comp
          ((continuous_const.add (continuous_subtype_val.mul continuous_const)).prodMk
            continuous_const).continuousOn hmp
        have hcc' : Continuous (fun t : Ico (0 : ℝ) 1 =>
            F (a + t.val * (v - a), v)) := by
          apply (continuousOn_univ.mp hcc).congr
          intro t
          exact (indicator_of_mem (hmap hv t) (Function.uncurry f)).symm
        exact hcc'.enorm
    · have heq : (fun t : Ico (0 : ℝ) 1 => g t v) = fun _ => 0 := by
        funext t
        simp only [g, F, indicator_of_notMem (hnot v hv _), enorm_zero]
      rw [heq]
      exact continuous_const
  have hsup : Measurable (fun v => ⨆ t : Ico (0 : ℝ) 1, g t v) := by
    convert measurable_iSup_of_lowerSemicontinuous hm
      (fun v => (hct v).lowerSemicontinuous) using 1
    funext v
    simp only [iSup_apply]
  have hdiag : Measurable (fun v => ‖F (v, v)‖ₑ) :=
    (hf.comp (measurable_id.prodMk measurable_id)).enorm
  convert hdiag.sup hsup using 1
  funext v
  simp only [Pi.sup_apply]
  symm
  by_cases hv : v ∈ Icc a b
  · rw [indicator_of_mem hv]
    apply le_antisymm
    · apply sup_le
      · dsimp only [F]
        rw [indicator_of_mem (show (v, v) ∈ triangle a b from ⟨hv.1, le_rfl, hv.2⟩)]
        exact enorm_le_normEnvelope f ⟨hv.1, le_rfl⟩
      · apply iSup_le
        intro t
        dsimp only [g, F]
        rw [indicator_of_mem (hmap hv t)]
        exact enorm_le_normEnvelope f ⟨(hmap hv t).1, (hmap hv t).2.1⟩
    · apply iSup₂_le
      intro x hx
      rcases hx.2.eq_or_lt with rfl | hxv
      · apply le_sup_of_le_left
        dsimp only [F]
        rw [indicator_of_mem (show (x, x) ∈ triangle a b from ⟨hv.1, le_rfl, hv.2⟩)]
        exact le_rfl
      · have hav : 0 < v - a := sub_pos.mpr (hx.1.trans_lt hxv)
        let t : Ico (0 : ℝ) 1 := ⟨(x - a) / (v - a),
          div_nonneg (sub_nonneg.mpr hx.1) hav.le,
          (div_lt_one hav).2 (by linarith only [hxv])⟩
        have htx : a + t.val * (v - a) = x := by
          dsimp only [t]
          rw [div_mul_cancel₀ _ hav.ne']
          ring
        apply le_sup_of_le_right
        apply le_iSup_of_le t
        dsimp only [g, F]
        rw [htx, indicator_of_mem (show (x, v) ∈ triangle a b from ⟨hx.1, hx.2, hv.2⟩)]
        exact le_rfl
  · rw [indicator_of_notMem hv]
    apply le_antisymm
    · apply sup_le
      · simp only [F, indicator_of_notMem (hnot v hv v), enorm_zero, le_refl]
      · apply iSup_le
        intro t
        simp only [g, F, indicator_of_notMem (hnot v hv _), enorm_zero, le_refl]
    · exact zero_le

/-- The reflected incoming envelope is measurable under the same Borel and
off-axis continuity assumptions. Both coordinate directions are reversed. -/
theorem stab_measurable_inEnv_of_offAxis
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {f : ℝ → ℝ → E} {a b : ℝ}
    (hf : Measurable ((triangle a b).indicator (Function.uncurry f)))
    (hc : ContinuousOn (Function.uncurry f)
      {p : ℝ × ℝ | p ∈ triangle a b ∧ p.1 < p.2}) :
    Measurable ((Icc a b).indicator (inEnv b f)) := by
  classical
  let F := fun x y => f (-y) (-x)
  have hmem (p : ℝ × ℝ) : (-p.2, -p.1) ∈ triangle a b ↔
      p ∈ triangle (-b) (-a) := by
    constructor <;> rintro ⟨hp1, hp2, hp3⟩ <;> refine ⟨?_, ?_, ?_⟩ <;>
      linarith only [hp1, hp2, hp3]
  have hm : Measurable ((triangle (-b) (-a)).indicator (Function.uncurry F)) := by
    convert hf.comp (measurable_snd.neg.prodMk measurable_fst.neg) using 1
    funext p
    by_cases hp : p ∈ triangle (-b) (-a)
    · simp only [Function.comp_apply, Pi.neg_apply, indicator_of_mem hp,
        indicator_of_mem ((hmem p).2 hp), Function.uncurry_def, F]
    · simp only [Function.comp_apply, Pi.neg_apply, indicator_of_notMem hp,
        indicator_of_notMem (fun h => hp ((hmem p).1 h))]
  have hct : ContinuousOn (Function.uncurry F)
      {p : ℝ × ℝ | p ∈ triangle (-b) (-a) ∧ p.1 < p.2} := by
    exact hc.comp (continuous_snd.neg.prodMk continuous_fst.neg).continuousOn
      (fun p hp => ⟨(hmem p).2 hp.1, neg_lt_neg hp.2⟩)
  have hM := (stab_measurable_outEnv_of_offAxis hm hct).comp measurable_neg
  convert hM using 1
  funext u
  by_cases hu : u ∈ Icc a b
  · have hn : -u ∈ Icc (-b) (-a) := ⟨neg_le_neg hu.2, neg_le_neg hu.1⟩
    simp only [Function.comp_apply, indicator_of_mem hu, indicator_of_mem hn]
    exact inEnv_eq_outEnv_neg b f u
  · have hn : -u ∉ Icc (-b) (-a) := by
      intro hnu
      exact hu ⟨by linarith only [hnu.2], by linarith only [hnu.1]⟩
    simp only [Function.comp_apply, indicator_of_notMem hu, indicator_of_notMem hn]

end EmcsfAcExtension.Local
