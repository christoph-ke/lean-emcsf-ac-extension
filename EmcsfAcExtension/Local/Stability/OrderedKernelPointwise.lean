module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Stability.OrderedKernelArea
import EmcsfAcExtension.Local.Stability.MomentsIncoming
import EmcsfAcExtension.Local.Stability.MomentsFieldMeasurable
import EmcsfAcExtension.Local.Stability.OrderedKernelMoment

/-! # Outgoing scalar-source majorant from the incoming identity

Insert the incoming moment into the literal definition of `curvScalar`.
The radius is multiplied into the moment before either ratio is replaced
by a supremum. No curvature or renormalized transport theorem is assumed.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Outgoing scalar-curvature source from the incoming reconstruction
identity. The exact coefficient `256` is universal: independent of
`T,e,ε,M,A,S,h,p` for `1/2 ≤ p ≤ 1 - ε²`. The two inputs are the actual
characteristic envelopes, extended by zero outside `[0,T]`. -/
theorem stab_ordered_pointwise_of_identity
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    (hidentity : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
      HasDerivWithinAt (fun s => S.xi s v / (S.nu s v : ℂ))
        (kC1 e (triangle 0 T) S u v / ((1 - S.mu u v : ℝ) : ℂ) -
          (S.nu u v / S.r u v * (1 - ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2)) •
            (S.xi u v / (S.nu u v : ℂ)) -
          (e * S.A u v) • (Complex.I * (S.xi u v / (S.nu u v : ℂ)))) (Icc 0 v) u)
    {p u v : ℝ} (hp0 : 1 / 2 ≤ p) (hp : p ≤ 1 - ε ^ 2)
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖(S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2 *
      curvScalar (triangle 0 T) S u v‖ₑ ≤
      ENNReal.ofReal (256 * ε) * stabOrderedKernel p
        ((Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S)))
        ((Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))) u v := by
  classical
  let K := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S))
  let J := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))
  have hK : Measurable K := stab_measurable_inEnv_of_offAxis
    (stab_kC1_borel hset) (stab_kC1_continuous_offAxis hset)
  have hp' : 0 < p := lt_of_lt_of_le (by norm_num) hp0
  have hp1 : p ≤ 1 := hp.trans (sub_le_self _ (sq_nonneg ε))
  have hL : 0 < v - u := sub_pos.mpr huv
  have hr := hset.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv
  have hR (w : ℝ) (hw : w ∈ Ioc u v) : 0 < S.r u w ∧ S.r u w ≤ v - u :=
    ⟨hset.c1.r_pos (u, w) ⟨hu, hw.1.le, hw.2.trans hvT⟩ hw.1,
      ((stab_radius_bounds hset hu hw.1.le (hw.2.trans hvT)).2).trans
        (sub_le_sub_right hw.2 u)⟩
  have hρ (w : ℝ) (hw : w ∈ Ioc u v) (s : ℝ) (hs : s ∈ Icc u w) :
      0 ≤ S.r s w ∧ S.r s w ≤ w - s := by
    have hb := stab_radius_bounds hset (hu.trans hs.1) hs.2 (hw.2.trans hvT)
    exact ⟨(div_nonneg (sub_nonneg.mpr hs.2) (by norm_num : (0 : ℝ) ≤ 4)).trans hb.1, hb.2⟩
  have hk (w : ℝ) (hw : w ∈ Ioc u v) :
      AEMeasurable (fun s => ENNReal.ofReal ((S.r s w / S.r u w) ^ p) * K s)
        (volume.restrict (Icc u w)) := by
    have hrr : ContinuousOn (fun s => S.r s w / S.r u w) (Icc u w) :=
      (hset.c1.c1_r.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hu.trans hs.1, hs.2, hw.2.trans hvT⟩)).div_const _
    exact ((ENNReal.continuous_ofReal.comp_continuousOn
      ((Real.continuous_rpow_const hp'.le).comp_continuousOn hrr)).aemeasurable
        measurableSet_Icc).mul hK.aemeasurable.restrict
  have hmoment (w : ℝ) (hw : w ∈ Ioc u v) :
      ENNReal.ofReal ‖S.xi u w / (S.nu u w : ℂ)‖ ≤
        ENNReal.ofReal 4 * ∫⁻ s in Icc u w,
          ENNReal.ofReal ((S.r s w / S.r u w) ^ p) * K s := by
    apply (stab_in_moment_of_identity hset hidentity hp' hp hu hw.1
      (hw.2.trans hvT)).trans_eq
    congr 1
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only [K]
    rw [indicator_of_mem (show s ∈ Icc 0 T from ⟨hu.trans hs.1, hs.2.trans (hw.2.trans hvT)⟩)]
  have hm := stab_integral_moment_product_le_of_bound
    (I := Ioc u v) (E := fun w => Icc u w) (R := S.r u)
    (q := fun w s => (S.r s w / S.r u w) ^ p) (P := fun w s => (w - s) ^ p)
    (y := fun w => S.xi u w / (S.nu u w : ℂ)) (K := K) (J := J)
    (B := (v - u) ^ (1 - p)) measurableSet_Ioc (fun _ _ => measurableSet_Icc)
    (Real.rpow_nonneg hL.le _) (fun w hw => (hR w hw).1.le)
    (fun w hw s hs => Real.rpow_nonneg (div_nonneg (hρ w hw s hs).1 (hR w hw).1.le) p)
    (fun w hw s hs => Real.rpow_nonneg (sub_nonneg.mpr hs.2) p) hk hmoment
    (fun w hw s hs => stab_radius_power_product_le (hR w hw).1 (hR w hw).2
      (hρ w hw s hs).1 (hρ w hw s hs).2 hp'.le hp1)
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S.xi u v / (S.nu u v : ℂ)))).trans
      (hset.box.2 (u, v) ⟨hu, huv.le, hvT⟩).2.2.2.2.2.1)
  let c := ((S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2) * (S.r u v : ℂ)⁻¹
  have hc : ‖c‖ₑ ≤ ENNReal.ofReal (64 * ε / (v - u) ^ 3) := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (stab_scalar_primitive_coefficients_le hset hu huv hvT).1
  have hprimitive : ‖(S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2 *
      curvScalar (triangle 0 T) S u v‖ₑ ≤
      ‖c‖ₑ * ∫⁻ w in Ioc u v, ENNReal.ofReal (S.r u w) *
        ENNReal.ofReal ‖S.xi u w / (S.nu u w : ℂ)‖ * J w := by
    rw [curvScalar, intervalIntegral.integral_of_le huv.le, ← mul_assoc, enorm_mul]
    apply mul_le_mul' le_rfl
    apply (enorm_integral_le_lintegral_enorm _).trans
    apply setLIntegral_mono' measurableSet_Ioc
    intro w hw
    rw [← ofReal_norm, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hR w hw).1, RCLike.norm_conj]
    rw [ENNReal.ofReal_mul (mul_nonneg (hR w hw).1.le (norm_nonneg _)),
      ENNReal.ofReal_mul (hR w hw).1.le]
    apply mul_le_mul' le_rfl
    dsimp only [J]
    rw [indicator_of_mem (show w ∈ Icc 0 T from ⟨hu.trans hw.1.le, hw.2.trans hvT⟩),
      ofReal_norm]
    exact enorm_le_normEnvelope (jC1 (triangle 0 T) S) ⟨hu, hw.1.le⟩
  apply hprimitive.trans
  apply (mul_le_mul' hc hm).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 64 * ε / (v - u) ^ 3)]
  have hcoeff : (64 * ε / (v - u) ^ 3) * (4 * (v - u) ^ (1 - p)) =
      256 * ε * (v - u) ^ (-p - 2) := by
    rw [← mul_assoc]
    exact stab_ordered_coefficient_eq hL
  rw [hcoeff, ENNReal.ofReal_mul (mul_nonneg (by norm_num) hε), stabOrderedKernel,
    restrict_Ioc_eq_restrict_Icc]
  dsimp only [K, J]
  ac_rfl

end EmcsfAcExtension.Local
