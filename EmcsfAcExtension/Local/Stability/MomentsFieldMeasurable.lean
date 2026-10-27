module

public import EmcsfAcExtension.Local.Stability.MomentsEnvelope

/-! # Borel renormalized fields on the classical triangle

The total quotients in `jC1` and `kC1` are Borel, including at the axis.
Their restrictions off the axis are continuous. These facts supply the
measurability needed by Tonelli without adding an envelope hypothesis.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}

private theorem measurable_triangle_indicator {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {f : ℝ × ℝ → E}
    (hf : ContinuousOn f (triangle 0 T)) :
    Measurable ((triangle 0 T).indicator f) := by
  classical
  exact hf.measurable_piecewise continuousOn_const (measurableSet_triangle 0 T)

/-- The outgoing renormalized field, extended by zero, is Borel measurable.
Only the standing classical setting is used. -/
theorem stab_jC1_borel (hset : StabSetting e T ε M A S h) :
    Measurable ((triangle 0 T).indicator (Function.uncurry (jC1 (triangle 0 T) S))) := by
  let D := triangle 0 T
  let R := D.indicator (Function.uncurry S.r)
  let L := D.indicator (Function.uncurry S.lam)
  let m := D.indicator (Function.uncurry S.m)
  let θ := D.indicator (Function.uncurry S.theta)
  let P := D.indicator (fun p => pdV D S.a p.1 p.2)
  have hR : Measurable R := measurable_triangle_indicator hset.c1.c1_r.continuousOn
  have hL : Measurable L := measurable_triangle_indicator hset.c1.c1_lam.continuousOn
  have hm : Measurable m := measurable_triangle_indicator hset.c1.c1_m.continuousOn
  have hθ : Measurable θ := measurable_triangle_indicator hset.c1.c1_theta.continuousOn
  have hP : Measurable P := measurable_triangle_indicator
    (continuousOn_partial_v (stab_normalized_out_c1 hset.c1) (uniqueDiffOn_triangle hset.pos))
  have hF : Measurable (fun p =>
      ((1 - 2 * m p / R p : ℝ) : ℂ) *
        (P p - ((L p / R p * ‖θ p / (L p : ℂ)‖ ^ 2 : ℝ) : ℂ) *
          (θ p / (L p : ℂ)))) := by fun_prop
  convert hF using 1
  funext p
  symm
  by_cases hp : p ∈ D
  · simp only [R, L, m, θ, P, indicator_of_mem hp, jC1, Fields.mu, D,
      Function.uncurry_def]
    push_cast
    ring
  · simp only [R, L, m, θ, P, indicator_of_notMem hp,
      zero_div, Complex.ofReal_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, sub_zero]
    exact (indicator_of_notMem hp _).symm

/-- The incoming renormalized field, extended by zero, is Borel measurable.
The connection term is included with its literal real potential. -/
theorem stab_kC1_borel (hset : StabSetting e T ε M A S h) :
    Measurable ((triangle 0 T).indicator (Function.uncurry (kC1 e (triangle 0 T) S))) := by
  let D := triangle 0 T
  let R := D.indicator (Function.uncurry S.r)
  let N := D.indicator (Function.uncurry S.nu)
  let m := D.indicator (Function.uncurry S.m)
  let ξ := D.indicator (Function.uncurry S.xi)
  let P := D.indicator (fun p => pdU D S.b p.1 p.2)
  let V := D.indicator (Function.uncurry S.A)
  let B := D.indicator (Function.uncurry S.b)
  have hR : Measurable R := measurable_triangle_indicator hset.c1.c1_r.continuousOn
  have hN : Measurable N := measurable_triangle_indicator hset.c1.c1_nu.continuousOn
  have hm : Measurable m := measurable_triangle_indicator hset.c1.c1_m.continuousOn
  have hξ : Measurable ξ := measurable_triangle_indicator hset.c1.c1_xi.continuousOn
  have hP : Measurable P := measurable_triangle_indicator
    (continuousOn_partial_u (stab_normalized_in_c1 hset.c1) (uniqueDiffOn_triangle hset.pos))
  have hV : Measurable V := measurable_triangle_indicator hset.c1.c1_A.continuousOn
  have hB : Measurable B := measurable_triangle_indicator
    (stab_normalized_in_c1 hset.c1).continuousOn
  have hF : Measurable (fun p =>
      ((1 - 2 * m p / R p : ℝ) : ℂ) *
        (P p + Complex.I * e * V p * B p -
          ((N p / R p * ‖ξ p / (N p : ℂ)‖ ^ 2 : ℝ) : ℂ) * (ξ p / (N p : ℂ)))) := by
    fun_prop
  convert hF using 1
  funext p
  symm
  by_cases hp : p ∈ D
  · simp only [R, N, m, ξ, P, V, B, indicator_of_mem hp, kC1, Fields.mu, D,
      Function.uncurry_def]
    push_cast
    ring
  · simp only [R, N, m, ξ, P, V, B, indicator_of_notMem hp,
      zero_div, Complex.ofReal_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, sub_zero, add_zero]
    exact (indicator_of_notMem hp _).symm

/-- The outgoing renormalized field is continuous off the axis, with
within-domain derivatives as in the architecture. -/
theorem stab_jC1_continuous_offAxis (hset : StabSetting e T ε M A S h) :
    ContinuousOn (Function.uncurry (jC1 (triangle 0 T) S))
      {p : ℝ × ℝ | p ∈ triangle 0 T ∧ p.1 < p.2} := by
  let U := {p : ℝ × ℝ | p ∈ triangle 0 T ∧ p.1 < p.2}
  have hsub : U ⊆ triangle 0 T := fun _ hp => hp.1
  have hR := hset.c1.c1_r.continuousOn.mono hsub
  have hL := hset.c1.c1_lam.continuousOn.mono hsub
  have hm := hset.c1.c1_m.continuousOn.mono hsub
  have hx := (stab_out_ratio_c1 hset.c1).continuousOn.mono hsub
  have hP := (continuousOn_partial_v (stab_normalized_out_c1 hset.c1)
    (uniqueDiffOn_triangle hset.pos)).mono hsub
  have hnz : ∀ p ∈ U, S.r p.1 p.2 ≠ 0 :=
    fun p hp => (hset.c1.r_pos p hp.1 hp.2).ne'
  have hγ := (continuousOn_const (c := (1 : ℝ))).sub ((hm.const_mul 2).div hR hnz)
  have hcoeff := (hL.div hR hnz).mul (hx.norm.pow 2)
  have hc := (Complex.continuous_ofReal.comp_continuousOn hγ).mul
    (hP.sub ((Complex.continuous_ofReal.comp_continuousOn hcoeff).mul hx))
  apply hc.congr
  intro p hp
  simp only [jC1, Fields.mu, pdV, Function.uncurry_def, Function.comp_apply,
    Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.pow_apply]
  push_cast
  ring

/-- The incoming renormalized field is continuous off the axis, including
its unitary connection coefficient. -/
theorem stab_kC1_continuous_offAxis (hset : StabSetting e T ε M A S h) :
    ContinuousOn (Function.uncurry (kC1 e (triangle 0 T) S))
      {p : ℝ × ℝ | p ∈ triangle 0 T ∧ p.1 < p.2} := by
  let U := {p : ℝ × ℝ | p ∈ triangle 0 T ∧ p.1 < p.2}
  have hsub : U ⊆ triangle 0 T := fun _ hp => hp.1
  have hR := hset.c1.c1_r.continuousOn.mono hsub
  have hN := hset.c1.c1_nu.continuousOn.mono hsub
  have hm := hset.c1.c1_m.continuousOn.mono hsub
  have hy := (stab_in_ratio_c1 hset.c1).continuousOn.mono hsub
  have hP := (continuousOn_partial_u (stab_normalized_in_c1 hset.c1)
    (uniqueDiffOn_triangle hset.pos)).mono hsub
  have hV := hset.c1.c1_A.continuousOn.mono hsub
  have hB := (stab_normalized_in_c1 hset.c1).continuousOn.mono hsub
  have hnz : ∀ p ∈ U, S.r p.1 p.2 ≠ 0 :=
    fun p hp => (hset.c1.r_pos p hp.1 hp.2).ne'
  have hγ := (continuousOn_const (c := (1 : ℝ))).sub ((hm.const_mul 2).div hR hnz)
  have hcoeff := (hN.div hR hnz).mul (hy.norm.pow 2)
  have hc := (Complex.continuous_ofReal.comp_continuousOn hγ).mul
    ((hP.add (((Complex.continuous_ofReal.comp_continuousOn hV).const_mul
      (Complex.I * e)).mul hB)).sub
        ((Complex.continuous_ofReal.comp_continuousOn hcoeff).mul hy))
  apply hc.congr
  intro p hp
  simp only [kC1, Fields.mu, pdU, Function.uncurry_def, Function.comp_apply,
    Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply]
  push_cast
  ring

/-- The outgoing stability envelope is measurable for its label measure.
This follows from the standing setting, with no axis-continuity assumption. -/
theorem stab_outEnv_aemeasurable (hset : StabSetting e T ε M A S h) :
    AEMeasurable (outEnv 0 (jC1 (triangle 0 T) S)) (volume.restrict (Icc 0 T)) := by
  have hm := stab_measurable_outEnv_of_offAxis (stab_jC1_borel hset)
    (stab_jC1_continuous_offAxis hset)
  apply hm.aemeasurable.restrict.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  exact indicator_of_mem hv _

/-- The incoming stability envelope is measurable for its label measure.
The coordinate reflection is explicit, and no axis continuity is assumed. -/
theorem stab_inEnv_aemeasurable (hset : StabSetting e T ε M A S h) :
    AEMeasurable (inEnv T (kC1 e (triangle 0 T) S)) (volume.restrict (Icc 0 T)) := by
  have hm := stab_measurable_inEnv_of_offAxis (stab_kC1_borel hset)
    (stab_kC1_continuous_offAxis hset)
  apply hm.aemeasurable.restrict.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  exact indicator_of_mem hu _

end EmcsfAcExtension.Local
