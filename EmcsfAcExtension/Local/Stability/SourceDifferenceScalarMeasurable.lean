module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.SourceDifferenceIdentity
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Null.Parametric

/-! # Measurability of the literal scalar curvature sources

The primitive integrands are continuous on the closed triangle. Their
primitive is continuous, while total inverse powers of the radius are
Borel measurable. Zero extension supplies global measurable representatives.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- Incoming integrals with both characteristic endpoints vary continuously.
This follows from the two primitives based at the common lower endpoint. -/
theorem continuousOn_integral_incoming_between {T : ℝ} {f : ℝ → ℝ → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (triangle 0 T)) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ w in p.1..p.2, f w p.2) (triangle 0 T) := by
  have hbase := continuousOn_integral_incoming hf
  have hdiag := hbase.comp (continuous_snd.prodMk continuous_snd).continuousOn
    (show MapsTo (fun p : ℝ × ℝ => (p.2, p.2)) (triangle 0 T) (triangle 0 T) from
      fun p hp => ⟨hp.1.trans hp.2.1, le_rfl, hp.2.2⟩)
  apply (hdiag.sub hbase).congr
  intro p hp
  have hsec : ContinuousOn (fun w => f w p.2) (Icc 0 p.2) :=
    hf.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun w hw => ⟨hw.1, hw.2, hp.2.2⟩)
  have hi₂ := hsec.intervalIntegrable_of_Icc (μ := volume) (hp.1.trans hp.2.1)
  have hi₁ := hi₂.mono_set (show uIcc 0 p.1 ⊆ uIcc 0 p.2 from by
    rw [uIcc_of_le hp.1, uIcc_of_le (hp.1.trans hp.2.1)]
    exact Icc_subset_Icc le_rfl hp.2.1)
  change (∫ w in p.1..p.2, f w p.2) =
    (∫ w in 0..p.2, f w p.2) - (∫ w in 0..p.1, f w p.2)
  rw [intervalIntegral.integral_interval_sub_left hi₂ hi₁]

/-- Measurability of an inverse-cube coefficient multiplying a primitive
and its conjugate. All four numerator fields are continuous only on the
triangle; the total inverse power remains Borel at its zero radius. -/
theorem measurable_inverse_cube_primitive_source {T : ℝ}
    {r n : ℝ × ℝ → ℝ} {t Z : ℝ × ℝ → ℂ} (hT : 0 ≤ T)
    (hr : ContinuousOn r (triangle 0 T)) (hn : ContinuousOn n (triangle 0 T))
    (ht : ContinuousOn t (triangle 0 T)) (hZ : ContinuousOn Z (triangle 0 T)) :
    Measurable ((triangle 0 T).indicator (fun p =>
      (n p : ℂ) * t p / (r p : ℂ) ^ 3 * (Z p + 2 * starRingEnd ℂ (Z p)))) := by
  let R := fun p => r (triangleProj 0 T p)
  let N := fun p => n (triangleProj 0 T p)
  let X := fun p => t (triangleProj 0 T p)
  let W := fun p => Z (triangleProj 0 T p)
  have hR : Continuous R := hr.comp_continuous (continuous_triangleProj 0 T) (triangleProj_mem hT)
  have hN : Continuous N := hn.comp_continuous (continuous_triangleProj 0 T) (triangleProj_mem hT)
  have hX : Continuous X := ht.comp_continuous (continuous_triangleProj 0 T) (triangleProj_mem hT)
  have hW : Continuous W := hZ.comp_continuous (continuous_triangleProj 0 T) (triangleProj_mem hT)
  have hm : Measurable (fun p =>
      (N p : ℂ) * X p / (R p : ℂ) ^ 3 * (W p + 2 * starRingEnd ℂ (W p))) := by fun_prop
  convert hm.indicator (measurableSet_triangle 0 T) using 1
  funext p
  by_cases hp : p ∈ triangle 0 T
  · simp only [indicator_of_mem hp, R, N, X, W, triangleProj_of_mem hp]
  · simp only [indicator_of_notMem hp]

/-- The literal outgoing scalar source has a measurable zero extension.
No regularity or support assumption is imposed outside the triangle. -/
theorem measurable_scalar_source_j {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    Measurable ((triangle 0 T).indicator (fun p =>
      (S.nu p.1 p.2 : ℂ) * S.theta p.1 p.2 / (S.r p.1 p.2 : ℂ) ^ 2 *
        (curvScalar (triangle 0 T) S p.1 p.2 +
          2 * starRingEnd ℂ (curvScalar (triangle 0 T) S p.1 p.2)))) := by
  have hr := Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_r.continuousOn
  have hy := continuous_star.comp_continuousOn (stab_in_ratio_c1 hset.c1).continuousOn
  have hj := continuousOn_jC1_aux hset.pos hset.c1
  have hZ := continuousOn_integral_outgoing
    (F := fun u v => (S.r u v : ℂ) * starRingEnd ℂ (S.xi u v / S.nu u v) *
      jC1 (triangle 0 T) S u v)
    (by simpa only [Function.uncurry_def, Function.comp_apply, Pi.mul_def] using! (hr.mul hy).mul
          hj)
  have hm := measurable_inverse_cube_primitive_source hset.pos.le hset.c1.c1_r.continuousOn
    hset.c1.c1_nu.continuousOn hset.c1.c1_theta.continuousOn hZ
  convert hm using 1
  funext p
  by_cases hp : p ∈ triangle 0 T
  · simp only [indicator_of_mem hp]
    exact scalar_source_j_eq_primitive _ S p.1 p.2
  · simp only [indicator_of_notMem hp]

/-- The literal incoming scalar source has a measurable zero extension.
The negative orientation of its primitive is kept in its expansion factor. -/
theorem measurable_scalar_source_k {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    Measurable ((triangle 0 T).indicator (fun p =>
      (S.lam p.1 p.2 : ℂ) * S.xi p.1 p.2 / (S.r p.1 p.2 : ℂ) ^ 2 *
        (curvScalarIn e (triangle 0 T) S p.1 p.2 +
          2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S p.1 p.2)))) := by
  have hr := Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_r.continuousOn
  have hx := continuous_star.comp_continuousOn (stab_out_ratio_c1 hset.c1).continuousOn
  have hk := continuousOn_kC1_aux hset.pos hset.c1
  have hZ := continuousOn_integral_incoming_between
    (f := fun u v => (S.r u v : ℂ) * starRingEnd ℂ (S.theta u v / S.lam u v) *
      kC1 e (triangle 0 T) S u v)
    (by simpa only [Function.uncurry_def, Function.comp_apply, Pi.mul_def] using! (hr.mul hx).mul
          hk)
  have hm := measurable_inverse_cube_primitive_source hset.pos.le hset.c1.c1_r.continuousOn
    hset.c1.c1_lam.continuousOn.neg hset.c1.c1_xi.continuousOn hZ
  convert hm using 1
  funext p
  by_cases hp : p ∈ triangle 0 T
  · simp only [indicator_of_mem hp, Pi.neg_apply, Function.uncurry_def, Complex.ofReal_neg]
    exact scalar_source_k_eq_primitive e (triangle 0 T) S p.1 p.2
  · simp only [indicator_of_notMem hp]

/-- Norm difference of two zero-extended measurable complex fields.
The zero extension and norm commute on and off the triangle. -/
theorem measurable_triangle_difference_enorm {T : ℝ} {f g : ℝ × ℝ → ℂ}
    (hf : Measurable ((triangle 0 T).indicator f))
    (hg : Measurable ((triangle 0 T).indicator g)) :
    Measurable ((triangle 0 T).indicator (fun p => ‖f p - g p‖ₑ)) := by
  have hm := (hf.fun_sub hg).enorm
  convert hm using 1
  funext p
  by_cases hp : p ∈ triangle 0 T
  · simp only [indicator_of_mem hp]
  · simp only [indicator_of_notMem hp, sub_self, enorm_zero]

end EmcsfAcExtension.Local.Stab
