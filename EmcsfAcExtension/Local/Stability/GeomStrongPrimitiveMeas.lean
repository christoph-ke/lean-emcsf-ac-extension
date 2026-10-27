module

public import EmcsfAcExtension.Local.Stability.GeomStrongScalarPrimitive
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import Mathlib.MeasureTheory.Integral.Prod

/-! # Borel geometric scalar primitives

The moving endpoints are represented by two measurable interval
indicators. No integrability assertion is needed for measurability;
the ordered bounds establish finiteness separately.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- A jointly strongly measurable density has a strongly measurable
primitive with both endpoints varying. There is no integrability
premise and no estimate constant. -/
theorem stab_stronglyMeasurable_moving_primitive {F : ℝ × ℝ → ℂ}
    (hF : StronglyMeasurable F) :
    StronglyMeasurable (fun p : ℝ × ℝ => ∫ t in p.1..p.2, F (p.1, t)) := by
  classical
  let L : Set ((ℝ × ℝ) × ℝ) := {q | q.1.1 < q.2 ∧ q.2 ≤ q.1.2}
  let R : Set ((ℝ × ℝ) × ℝ) := {q | q.1.2 < q.2 ∧ q.2 ≤ q.1.1}
  let K : (ℝ × ℝ) × ℝ → ℂ := fun q => F (q.1.1, q.2)
  have hK : StronglyMeasurable K := hF.comp_measurable (measurable_fst.fst.prodMk measurable_snd)
  have hL : MeasurableSet L := (measurableSet_lt measurable_fst.fst measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst.snd)
  have hR : MeasurableSet R := (measurableSet_lt measurable_fst.snd measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst.fst)
  have hm := (hK.indicator hL).integral_prod_right' (ν := (volume : Measure ℝ)) |>.sub
    ((hK.indicator hR).integral_prod_right' (ν := (volume : Measure ℝ)))
  convert hm using 1
  funext p
  have hleft : (fun t => L.indicator K (p, t)) = (Ioc p.1 p.2).indicator (fun t => F (p.1, t)) :=
      rfl
  have hright : (fun t => R.indicator K (p, t)) = (Ioc p.2 p.1).indicator (fun t => F (p.1, t)) :=
      rfl
  change (∫ t in p.1..p.2, F (p.1, t)) =
    (∫ t, (Ioc p.1 p.2).indicator (fun t => F (p.1, t)) t) -
      ∫ t, (Ioc p.2 p.1).indicator (fun t => F (p.1, t)) t
  rw [integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc]
  rcases le_total p.1 p.2 with hp | hp
  · simp only [intervalIntegral.integral_of_le hp, Ioc_eq_empty_of_le hp,
      Measure.restrict_empty, integral_zero_measure, sub_zero]
  · simp only [intervalIntegral.integral_of_ge hp, Ioc_eq_empty_of_le hp,
      Measure.restrict_empty, integral_zero_measure, zero_sub]

/-- The geometric scalar source, extended by zero outside the closed
classical triangle, is Borel measurable. There is no finite-integral
premise and no hidden uniform regularity bound. -/
theorem stab_geometricScalarSource_borel_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    Measurable ((triangle 0 T).indicator
      (Function.uncurry (geometricScalarSource (triangle 0 T) S))) := by
  classical
  let D := triangle 0 T
  let F : ℝ × ℝ → ℂ := fun p => (S.r p.1 p.2 : ℂ) *
    starRingEnd ℂ (S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ)) * jC1 D S p.1 p.2
  have cF : ContinuousOn F D := by
    exact ((Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_r.continuousOn).mul
      (stab_in_ratio_c1 hset.c1).continuousOn.star).mul (continuousOn_jC1_aux hset.pos hset.c1)
  have mF : Measurable (D.indicator F) := by
    rw [← piecewise_eq_indicator]
    exact cF.measurable_piecewise continuousOn_const (measurableSet_triangle 0 T)
  have mP := (stab_stronglyMeasurable_moving_primitive mF.stronglyMeasurable).measurable
  let R := D.indicator (Function.uncurry S.r)
  let L := D.indicator (Function.uncurry S.lam)
  let N := D.indicator (Function.uncurry S.nu)
  let m := D.indicator (Function.uncurry S.m)
  have hR : Measurable R := by
    dsimp only [R]; rw [← piecewise_eq_indicator]
    exact hset.c1.c1_r.continuousOn.measurable_piecewise continuousOn_const (measurableSet_triangle
        0 T)
  have hL : Measurable L := by
    dsimp only [L]; rw [← piecewise_eq_indicator]
    exact hset.c1.c1_lam.continuousOn.measurable_piecewise continuousOn_const
        (measurableSet_triangle 0 T)
  have hN : Measurable N := by
    dsimp only [N]; rw [← piecewise_eq_indicator]
    exact hset.c1.c1_nu.continuousOn.measurable_piecewise continuousOn_const (measurableSet_triangle
        0 T)
  have hm : Measurable m := by
    dsimp only [m]; rw [← piecewise_eq_indicator]
    exact hset.c1.c1_m.continuousOn.measurable_piecewise continuousOn_const (measurableSet_triangle
        0 T)
  let W := fun p => (2 * N p * L p / ((1 - 2 * m p / R p) * R p ^ 3) : ℝ)
  have hW : Measurable W := by dsimp only [W]; fun_prop
  have hz : Measurable (fun p : ℝ × ℝ => (W p : ℂ) *
      ∫ t in p.1..p.2, D.indicator F (p.1, t)) :=
    (Complex.measurable_ofReal.comp hW).mul mP
  convert hz using 1
  funext p
  by_cases hp : p ∈ D
  · have hpT : p ∈ triangle 0 T := hp
    rw [indicator_of_mem hp]
    change geometricScalarSource D S p.1 p.2 = _
    rw [geometricScalarSource_eq_cubic_primitive]
    have hP : (∫ t in p.1..p.2, D.indicator F (p.1, t)) = ∫ t in p.1..p.2, F (p.1, t) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with t ht
      rw [uIoc_of_le hpT.2.1] at ht
      exact indicator_of_mem (show (p.1, t) ∈ D from ⟨hpT.1, ht.1.le, ht.2.trans hpT.2.2⟩) F
    rw [hP]
    simp only [W, R, L, N, m, indicator_of_mem hp, Function.uncurry_def, Fields.mu, F]
  · rw [indicator_of_notMem hp]
    simp only [W, R, L, N, m, indicator_of_notMem hp, zero_mul, mul_zero,
      zero_pow (by decide : 3 ≠ 0), div_zero, Complex.ofReal_zero]

end EmcsfAcExtension.Local
