module

public import EmcsfAcExtension.Local.Defs.Renormalized
public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Literal scalar sources as coefficient-weighted primitives

These identities preserve the approved primitive-only split of curvature.
No phase-dependent term is reassigned to the electromagnetic source.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Stab

/-- The literal outgoing scalar source as one inverse-cube coefficient and
its scalar primitive. The identity is total, including the zero radius. -/
theorem scalar_source_j_eq_primitive (D : Set (ℝ × ℝ)) (S : Fields) (u v : ℝ) :
    (S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2 *
      (curvScalar D S u v + 2 * starRingEnd ℂ (curvScalar D S u v)) =
    ((S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 3) *
      ((∫ w in u..v, (S.r u w : ℂ) * starRingEnd ℂ (S.xi u w / S.nu u w) * jC1 D S u w) +
        2 * starRingEnd ℂ (∫ w in u..v,
          (S.r u w : ℂ) * starRingEnd ℂ (S.xi u w / S.nu u w) * jC1 D S u w)) := by
  by_cases hr : S.r u v = 0
  · simp [curvScalar, hr]
  have hrc : (S.r u v : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  simp only [curvScalar, map_mul, map_inv₀, conj_ofReal]
  field_simp

/-- The literal incoming scalar source, with its negative primitive
orientation. The identity is total, including the zero radius. -/
theorem scalar_source_k_eq_primitive (e : ℝ) (D : Set (ℝ × ℝ)) (S : Fields) (u v : ℝ) :
    (S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
      (curvScalarIn e D S u v + 2 * starRingEnd ℂ (curvScalarIn e D S u v)) =
    (-(S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 3) *
      ((∫ w in u..v, (S.r w v : ℂ) * starRingEnd ℂ (S.theta w v / S.lam w v) *
          kC1 e D S w v) +
        2 * starRingEnd ℂ (∫ w in u..v,
          (S.r w v : ℂ) * starRingEnd ℂ (S.theta w v / S.lam w v) * kC1 e D S w v)) := by
  by_cases hr : S.r u v = 0
  · simp [curvScalarIn, hr]
  have hrc : (S.r u v : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  simp only [curvScalarIn, map_neg, map_mul, map_inv₀, conj_ofReal]
  field_simp
  ; ring

/-- The outgoing scalar primitive has an integrable complex integrand on
every outgoing segment in a standing stability setting. -/
theorem scalar_primitive_j_integrable {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (_huv : u ≤ v) (hvT : v ≤ T) :
    IntegrableOn (fun w => (S.r u w : ℂ) * starRingEnd ℂ (S.xi u w / S.nu u w) *
      jC1 (triangle 0 T) S u w) (Icc u v) := by
  have hmap : MapsTo (fun w => (u, w)) (Icc u v) (triangle 0 T) :=
    fun w hw => ⟨hu, hw.1, hw.2.trans hvT⟩
  have hr := Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_r.continuousOn
  have hy := continuous_star.comp_continuousOn (stab_in_ratio_c1 hset.c1).continuousOn
  have hj := continuousOn_jC1_aux hset.pos hset.c1
  have hcont := ((hr.mul hy).mul hj).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  exact hcont.integrableOn_Icc

/-- The incoming scalar primitive has an integrable complex integrand on
every incoming segment in a standing stability setting. -/
theorem scalar_primitive_k_integrable {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (_huv : u ≤ v) (hvT : v ≤ T) :
    IntegrableOn (fun w => (S.r w v : ℂ) * starRingEnd ℂ (S.theta w v / S.lam w v) *
      kC1 e (triangle 0 T) S w v) (Icc u v) := by
  have hmap : MapsTo (fun w => (w, v)) (Icc u v) (triangle 0 T) :=
    fun w hw => ⟨hu.trans hw.1, hw.2, hvT⟩
  have hr := Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_r.continuousOn
  have hx := continuous_star.comp_continuousOn (stab_out_ratio_c1 hset.c1).continuousOn
  have hk := continuousOn_kC1_aux hset.pos hset.c1
  have hcont := ((hr.mul hx).mul hk).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  exact hcont.integrableOn_Icc

end EmcsfAcExtension.Local.Stab
