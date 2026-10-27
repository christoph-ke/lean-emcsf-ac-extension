module

public import EmcsfAcExtension.Local.Apriori.AreaJKernel

/-! # Reflected integration for the incoming scalar area estimate

Reflection preserves both endpoint order and the surviving outgoing Hardy
weight in the approved proof of `charged_SF_new_version.tex:L4721–L4730`.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local.Area

private theorem lintegral_neg_Icc (f : ℝ → ℝ≥0∞) (a b : ℝ) :
    (∫⁻ t in Icc (-b) (-a), f (-t)) = ∫⁻ s in Icc a b, f s := by
  simpa only [image_neg_Icc, neg_neg] using
    (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_emb
      (Homeomorph.neg ℝ).measurableEmbedding f (Icc (-b) (-a))

/-- The incoming three-variable inverse-cube kernel leaves the outgoing
inverse-square Hardy weight. The coefficient `1/2` is universal; the input
need only be measurable and may have infinite mass.
-/
theorem incoming_primitive_area_le {T : ℝ} {F : ℝ × ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
      ENNReal.ofReal (1 / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (a, v)) ≤
      ∫⁻ a in Icc 0 T, ∫⁻ v in Icc a T,
        ENNReal.ofReal (1 / (2 * (v - a) ^ 2)) * F (a, v) := by
  have hb := outgoing_primitive_area_le (a₀ := -T) (T := 0)
    (F := fun p : ℝ × ℝ => F (-p.2, -p.1)) (by fun_prop)
  have hleft :
      (∫⁻ x in Icc (-T) 0, ∫⁻ y in Icc x 0,
        ENNReal.ofReal (1 / (y - x) ^ 3) * ∫⁻ z in Icc x y, F (-z, -x)) =
      ∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
        ENNReal.ofReal (1 / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (a, v) := by
    rw [← lintegral_neg_Icc (fun v => ∫⁻ u in Icc 0 v,
      ENNReal.ofReal (1 / (v - u) ^ 3) * ∫⁻ a in Icc u v, F (a, v)) 0 T]
    simp only [neg_zero]
    apply lintegral_congr
    intro x
    rw [← lintegral_neg_Icc (fun u =>
      ENNReal.ofReal (1 / (-x - u) ^ 3) * ∫⁻ a in Icc u (-x), F (a, -x)) 0 (-x)]
    simp only [neg_zero, neg_neg]
    apply lintegral_congr
    intro y
    rw [show y - x = -x - -y by ring,
      ← lintegral_neg_Icc (fun a => F (a, -x)) (-y) (-x)]
    simp only [neg_neg]
  have hright :
      (∫⁻ z in Icc (-T) 0, ∫⁻ x in Icc (-T) z,
        ENNReal.ofReal (1 / (2 * (z - x) ^ 2)) * F (-z, -x)) =
      ∫⁻ a in Icc 0 T, ∫⁻ v in Icc a T,
        ENNReal.ofReal (1 / (2 * (v - a) ^ 2)) * F (a, v) := by
    rw [← lintegral_neg_Icc (fun a => ∫⁻ v in Icc a T,
      ENNReal.ofReal (1 / (2 * (v - a) ^ 2)) * F (a, v)) 0 T]
    simp only [neg_zero]
    apply lintegral_congr
    intro z
    rw [← lintegral_neg_Icc (fun v =>
      ENNReal.ofReal (1 / (2 * (v - -z) ^ 2)) * F (-z, v)) (-z) T]
    simp only [neg_neg]
    apply lintegral_congr
    intro x
    rw [show z - x = -x - -z by ring]
  rwa [hleft, hright] at hb

end EmcsfAcExtension.Local.Area
