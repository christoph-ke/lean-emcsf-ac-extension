module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Stability.OrderedKernelArea
import EmcsfAcExtension.Local.Stability.Moments
import EmcsfAcExtension.Local.Stability.MomentsFieldMeasurable
import EmcsfAcExtension.Local.Stability.OrderedKernelMoment

/-! # The incoming scalar curvature primitive

The approved internal project record repair defines the conjugate scalar primitive by an
integral from the axis down to `u`. Its minus sign is explicit here. The
incoming ordered kernel is obtained by inserting the outgoing moment.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The conjugate incoming scalar curvature primitive in the approved
internal project record repair of `incoming-ordered-l1` (`charged_SF_new_version.tex:L5065–5068`).
Its sign records integration from the terminal axis down to `u`. -/
@[expose] noncomputable def curvScalarInConj (e : ℝ) (D : Set (ℝ × ℝ))
    (S : Fields) (u v : ℝ) : ℂ :=
  -((S.r u v : ℂ)⁻¹ * ∫ w in u..v,
    (S.r w v : ℂ) * starRingEnd ℂ (S.theta w v / (S.lam w v : ℂ)) * kC1 e D S w v)

/-- The incoming scalar primitive from the outgoing sectional reconstruction
identity. The exact coefficient `256` is universal, independently of all
parameters and derivative suprema, for `1/2 ≤ p ≤ 1 - ε²`. -/
theorem stab_incoming_ordered_pointwise_of_identity
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    (hidentity : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
      HasDerivWithinAt (fun s => S.theta u s / (S.lam u s : ℂ))
        (jC1 (triangle 0 T) S u v / ((1 - S.mu u v : ℝ) : ℂ) -
          (S.lam u v / S.r u v * (1 - ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2)) •
            (S.theta u v / (S.lam u v : ℂ))) (Icc u T) v)
    {p u v : ℝ} (hp0 : 1 / 2 ≤ p) (hp : p ≤ 1 - ε ^ 2)
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖(S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
      curvScalarInConj e (triangle 0 T) S u v‖ₑ ≤
      ENNReal.ofReal (256 * ε) * stabOrderedKernel p
        ((Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S)))
        ((Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))) u v := by
  classical
  let K := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S))
  let J := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))
  have hK : Measurable K := stab_measurable_inEnv_of_offAxis
    (stab_kC1_borel hset) (stab_kC1_continuous_offAxis hset)
  have hJ : Measurable J := stab_measurable_outEnv_of_offAxis
    (stab_jC1_borel hset) (stab_jC1_continuous_offAxis hset)
  have hp' : 0 < p := lt_of_lt_of_le (by norm_num) hp0
  have hp1 : p ≤ 1 := hp.trans (sub_le_self _ (sq_nonneg ε))
  have hL : 0 < v - u := sub_pos.mpr huv
  have hR (w : ℝ) (hw : w ∈ Ico u v) : 0 < S.r w v ∧ S.r w v ≤ v - u :=
    ⟨hset.c1.r_pos (w, v) ⟨hu.trans hw.1, hw.2.le, hvT⟩ hw.2,
      ((stab_radius_bounds hset (hu.trans hw.1) hw.2.le hvT).2).trans
        (sub_le_sub_left hw.1 v)⟩
  have hρ (w : ℝ) (hw : w ∈ Ico u v) (s : ℝ) (hs : s ∈ Icc w v) :
      0 ≤ S.r w s ∧ S.r w s ≤ s - w := by
    have hb := stab_radius_bounds hset (hu.trans hw.1) hs.1 (hs.2.trans hvT)
    exact ⟨(div_nonneg (sub_nonneg.mpr hs.1) (by norm_num : (0 : ℝ) ≤ 4)).trans hb.1, hb.2⟩
  have hk (w : ℝ) (hw : w ∈ Ico u v) :
      AEMeasurable (fun s => ENNReal.ofReal ((S.r w s / S.r w v) ^ p) * J s)
        (volume.restrict (Icc w v)) := by
    have hrr : ContinuousOn (fun s => S.r w s / S.r w v) (Icc w v) :=
      (hset.c1.c1_r.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun s hs => ⟨hu.trans hw.1, hs.1, hs.2.trans hvT⟩)).div_const _
    exact ((ENNReal.continuous_ofReal.comp_continuousOn
      ((Real.continuous_rpow_const hp'.le).comp_continuousOn hrr)).aemeasurable
        measurableSet_Icc).mul hJ.aemeasurable.restrict
  have hmoment (w : ℝ) (hw : w ∈ Ico u v) :
      ENNReal.ofReal ‖S.theta w v / (S.lam w v : ℂ)‖ ≤
        ENNReal.ofReal 4 * ∫⁻ s in Icc w v,
          ENNReal.ofReal ((S.r w s / S.r w v) ^ p) * J s := by
    have hb := stab_out_moment_of_identity hset hidentity hp' hp (hu.trans hw.1) hw.2 hvT
    rw [restrict_Ioc_eq_restrict_Icc] at hb
    apply hb.trans_eq
    congr 1
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only [J]
    rw [indicator_of_mem (show s ∈ Icc 0 T from ⟨hu.trans (hw.1.trans hs.1), hs.2.trans hvT⟩)]
  have hm := stab_integral_moment_product_le_of_bound
    (I := Ico u v) (E := fun w => Icc w v) (R := fun w => S.r w v)
    (q := fun w s => (S.r w s / S.r w v) ^ p) (P := fun w s => (s - w) ^ p)
    (y := fun w => S.theta w v / (S.lam w v : ℂ)) (K := J) (J := K)
    (B := (v - u) ^ (1 - p)) measurableSet_Ico (fun _ _ => measurableSet_Icc)
    (Real.rpow_nonneg hL.le _) (fun w hw => (hR w hw).1.le)
    (fun w hw s hs => Real.rpow_nonneg (div_nonneg (hρ w hw s hs).1 (hR w hw).1.le) p)
    (fun w hw s hs => Real.rpow_nonneg (sub_nonneg.mpr hs.1) p) hk hmoment
    (fun w hw s hs => stab_radius_power_product_le (hR w hw).1 (hR w hw).2
      (hρ w hw s hs).1 (hρ w hw s hs).2 hp'.le hp1)
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S.xi u v / (S.nu u v : ℂ)))).trans
      (hset.box.2 (u, v) ⟨hu, huv.le, hvT⟩).2.2.2.2.2.1)
  let c := ((S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2) * (S.r u v : ℂ)⁻¹
  have hc : ‖c‖ₑ ≤ ENNReal.ofReal (64 * ε / (v - u) ^ 3) := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (stab_scalar_primitive_coefficients_le hset hu huv hvT).2
  have hprimitive : ‖(S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
      curvScalarInConj e (triangle 0 T) S u v‖ₑ ≤
      ‖c‖ₑ * ∫⁻ w in Ico u v, ENNReal.ofReal (S.r w v) *
        ENNReal.ofReal ‖S.theta w v / (S.lam w v : ℂ)‖ * K w := by
    rw [curvScalarInConj, intervalIntegral.integral_of_le huv.le,
      restrict_Ioc_eq_restrict_Icc, ← restrict_Ico_eq_restrict_Icc,
      mul_neg, ← mul_assoc, enorm_neg, enorm_mul]
    apply mul_le_mul' le_rfl
    apply (enorm_integral_le_lintegral_enorm _).trans
    apply setLIntegral_mono' measurableSet_Ico
    intro w hw
    rw [← ofReal_norm, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hR w hw).1, RCLike.norm_conj]
    rw [ENNReal.ofReal_mul (mul_nonneg (hR w hw).1.le (norm_nonneg _)),
      ENNReal.ofReal_mul (hR w hw).1.le]
    apply mul_le_mul' le_rfl
    dsimp only [K]
    rw [indicator_of_mem (show w ∈ Icc 0 T from ⟨hu.trans hw.1, hw.2.le.trans hvT⟩),
      ofReal_norm]
    exact le_iSup_of_le v (le_iSup_of_le ⟨hw.2.le, hvT⟩ le_rfl)
  have hnumerator : (∫⁻ w in Ico u v, ∫⁻ s in Icc w v,
      ENNReal.ofReal ((s - w) ^ p) * J s * K w) =
      ∫⁻ w in Icc u v, ∫⁻ s in Icc u w,
        ENNReal.ofReal ((w - s) ^ p) * K s * J w := by
    rw [restrict_Ico_eq_restrict_Icc]
    calc
      _ = ∫⁻ w in Icc u v, ∫⁻ s in Icc w v,
          ENNReal.ofReal ((s - w) ^ p) * K w * J s := by
        apply lintegral_congr
        intro w
        apply lintegral_congr
        intro s
        ac_rfl
      _ = _ := (stab_ordered_inner_swap hK hJ).symm
  apply hprimitive.trans
  apply (mul_le_mul' hc hm).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 64 * ε / (v - u) ^ 3)]
  have hcoeff : (64 * ε / (v - u) ^ 3) * (4 * (v - u) ^ (1 - p)) =
      256 * ε * (v - u) ^ (-p - 2) := by
    rw [← mul_assoc]
    exact stab_ordered_coefficient_eq hL
  rw [hcoeff, ENNReal.ofReal_mul (mul_nonneg (by norm_num) hε), hnumerator, stabOrderedKernel]
  dsimp only [K, J]
  ac_rfl

end EmcsfAcExtension.Local
