module

public import EmcsfAcExtension.Local.Stability.OrderedKernelArea

/-! # Measurability of the ordered geometric area majorant

Both ordered inner variables are represented by measurable indicators.
This justifies addition and area integration of the separate telescope
terms before finiteness is obtained from the ordered kernel estimate.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The complete two-label ordered kernel is measurable for measurable
nonnegative input labels. No finite-mass or exponent-sign assumption is
needed, and no estimate constant is introduced.
-/
theorem stab_ordered_kernel_measurable {p : ℝ} {K J : ℝ → ℝ≥0∞}
    (hK : Measurable K) (hJ : Measurable J) :
    Measurable (fun q : ℝ × ℝ => stabOrderedKernel p K J q.1 q.2) := by
  let F := fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
    if q.1.1.1 ≤ q.2 ∧ q.2 ≤ q.1.2 then
      ENNReal.ofReal ((q.1.2 - q.2) ^ p) * K q.2 * J q.1.2 else 0
  have hset : MeasurableSet {q : ((ℝ × ℝ) × ℝ) × ℝ |
      q.1.1.1 ≤ q.2 ∧ q.2 ≤ q.1.2} :=
    (measurableSet_le (measurable_fst.fst.fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.snd)
  have hF : Measurable F := by
    apply Measurable.ite hset
    · exact (ENNReal.measurable_ofReal.comp
        ((measurable_fst.snd.sub measurable_snd).pow_const p)).mul
          (hK.comp measurable_snd) |>.mul (hJ.comp measurable_fst.snd)
    · exact measurable_const
  have hinner : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      ∫⁻ s in Icc q.1.1 q.2, ENNReal.ofReal ((q.2 - s) ^ p) * K s * J q.2) := by
    convert hF.lintegral_prod_right' (ν := (volume : Measure ℝ)) using 1
    funext q
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro s
    by_cases hs : s ∈ Icc q.1.1 q.2
    · rw [indicator_of_mem hs]
      dsimp only [F]
      rw [ite_eq_left (show q.1.1 ≤ s ∧ s ≤ q.2 from hs)]
    · rw [indicator_of_notMem hs]
      dsimp only [F]
      rw [ite_eq_right (show ¬(q.1.1 ≤ s ∧ s ≤ q.2) from hs)]
  let G := fun q : (ℝ × ℝ) × ℝ =>
    if q.1.1 ≤ q.2 ∧ q.2 ≤ q.1.2 then
      ∫⁻ s in Icc q.1.1 q.2, ENNReal.ofReal ((q.2 - s) ^ p) * K s * J q.2 else 0
  have hG : Measurable G := Measurable.ite
    ((measurableSet_le measurable_fst.fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.snd)) hinner measurable_const
  have houter : Measurable (fun q : ℝ × ℝ =>
      ∫⁻ w in Icc q.1 q.2, ∫⁻ s in Icc q.1 w,
        ENNReal.ofReal ((w - s) ^ p) * K s * J w) := by
    convert hG.lintegral_prod_right' (ν := (volume : Measure ℝ)) using 1
    funext q
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro w
    by_cases hw : w ∈ Icc q.1 q.2
    · rw [indicator_of_mem hw]
      dsimp only [G]
      rw [ite_eq_left (show q.1 ≤ w ∧ w ≤ q.2 from hw)]
    · rw [indicator_of_notMem hw]
      dsimp only [G]
      rw [ite_eq_right (show ¬(q.1 ≤ w ∧ w ≤ q.2) from hw)]
  exact (ENNReal.measurable_ofReal.comp
    ((measurable_snd.sub measurable_fst).pow_const (-p - 2))).mul houter

/-- The ordered majorant on the complete geometric triangle has mass
at most `1/p` times the product of its two label masses. The constant
depends only on `p > 0`, before the time interval and label functions.
-/
theorem stab_ordered_kernel_triangle_area {p T : ℝ} {K J : ℝ → ℝ≥0∞}
    (hp : 0 < p) (hK : Measurable K) (hJ : Measurable J) :
    (∫⁻ q in triangle 0 T, stabOrderedKernel p K J q.1 q.2) ≤
      ENNReal.ofReal (1 / p) * (∫⁻ s in Icc 0 T, K s) * (∫⁻ s in Icc 0 T, J s) := by
  rw [Measure.volume_eq_prod,
    lintegral_triangle_eq_lintegral_lintegral_symm (stab_ordered_kernel_measurable hK hJ)]
  exact stab_ordered_kernel_area hp hK hJ

end EmcsfAcExtension.Local
