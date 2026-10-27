module

public import EmcsfAcExtension.Local.Stability.GeomStrongScalarPrimitive
public import EmcsfAcExtension.Local.Stability.OrderedKernelArea
import EmcsfAcExtension.Local.Stability.GeomStrongPrimitiveC1
import EmcsfAcExtension.Local.Stability.GeomStrongSourceCoefficients
import EmcsfAcExtension.Local.Stability.DifferenceMomentsIncoming
import EmcsfAcExtension.Local.Stability.AssemblyMoments
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux

/-! # Ordered majorants for the four geometric scalar differences

The unabsorbed incoming difference moment controls the third term.
Every term retains both inner variables and a positive ordered kernel.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem enorm_four_aux (a b c d : ℂ) :
    ‖a + b + c + d‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ + ‖c‖ₑ + ‖d‖ₑ :=
  (enorm_add_le _ _).trans (add_le_add
    ((enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)) le_rfl)

/-- Four positive ordered majorants for the geometric scalar source
difference. The coefficient `B` is universal and precedes all field,
envelope, data and scale parameters. The explicit geometric, mass and
phase feedback is retained for the later comparison absorption.
-/
theorem stab_geometric_scalar_difference_ordered_c1 :
    ∃ B : ℝ, 0 < B ∧ ∀ (T e ε M A : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      3 * ε ^ 2 ≤ 1 / 2 → ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
      let G := (geomDist T S₁ S₂).toReal
      let U := (supDist T S₁.mu S₂.mu).toReal
      let P := T * |e| * (supDist T S₁.A S₂.A).toReal
      let K₁ := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S₁))
      let K₂ := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S₂))
      let J₂ := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S₂))
      let DK := (Icc 0 T).indicator (inEnv T
        (fun u v => kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v))
      let DJ := (Icc 0 T).indicator (outEnv 0
        (fun u v => jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v))
      ‖geometricScalarSource (triangle 0 T) S₁ u v -
        geometricScalarSource (triangle 0 T) S₂ u v‖ₑ ≤
      ENNReal.ofReal (4096 * (G + U) * 4 * 1) * stabOrderedKernel (1 / 2) K₂ J₂ u v +
      ENNReal.ofReal (512 * 4 * (4 * G)) * stabOrderedKernel (1 / 2) K₂ J₂ u v +
      ENNReal.ofReal (512 * B * 1) * stabOrderedKernel (1 / 2)
        (fun s => DK s + ENNReal.ofReal (G + P + U) * K₂ s) J₂ u v +
      ENNReal.ofReal (512 * 4 * 1) * stabOrderedKernel (1 / 2) K₁ DJ u v := by
  obtain ⟨B, hB, hDifference⟩ := Stab.incoming_difference_moment_before_absorption
  refine ⟨B, hB, ?_⟩
  intro T e ε M A S₁ S₂ h₁ h₂ h₁s h₂s hε u v hu huv hvT
  dsimp only
  let G := (geomDist T S₁ S₂).toReal
  let U := (supDist T S₁.mu S₂.mu).toReal
  let P := T * |e| * (supDist T S₁.A S₂.A).toReal
  let K₁ := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S₁))
  let K₂ := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S₂))
  let J₂ := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S₂))
  let DK := (Icc 0 T).indicator (inEnv T
    (fun u v => kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v))
  let DJ := (Icc 0 T).indicator (outEnv 0
    (fun u v => jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v))
  let KF := fun s => DK s + ENNReal.ofReal (G + P + U) * K₂ s
  let W (S : Fields) : ℂ := (2 * S.nu u v * S.lam u v /
    ((1 - S.mu u v) * S.r u v ^ 3) : ℝ)
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hU : 0 ≤ U := ENNReal.toReal_nonneg
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg h₁s.pos.le (abs_nonneg e)) ENNReal.toReal_nonneg
  have hεsq : ε ^ 2 ≤ 1 / 4 := by linarith only [hε]
  have hp : (1 / 2 : ℝ) ≤ 1 - ε ^ 2 := by linarith only [hε]
  have cK₁ := continuousOn_inEnv (continuousOn_kC1_aux h₁s.pos h₁s.c1)
  have cK₂ := continuousOn_inEnv (continuousOn_kC1_aux h₂s.pos h₂s.c1)
  have cDeltaK : ContinuousOn (Function.uncurry
      (fun u v => kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v))
      (triangle 0 T) := by
    simpa only [Function.uncurry_def, Pi.sub_apply] using!
      (continuousOn_kC1_aux h₁s.pos h₁s.c1).sub (continuousOn_kC1_aux h₂s.pos h₂s.c1)
  have cDK := continuousOn_inEnv cDeltaK
  have mK₁ : Measurable K₁ := by
    dsimp only [K₁]
    rw [← Set.piecewise_eq_indicator]
    exact cK₁.measurable_piecewise continuousOn_const measurableSet_Icc
  have mK₂ : Measurable K₂ := by
    dsimp only [K₂]
    rw [← Set.piecewise_eq_indicator]
    exact cK₂.measurable_piecewise continuousOn_const measurableSet_Icc
  have mDK : Measurable DK := by
    dsimp only [DK]
    rw [← Set.piecewise_eq_indicator]
    exact cDK.measurable_piecewise continuousOn_const measurableSet_Icc
  have mKF : Measurable KF := mDK.add (measurable_const.mul mK₂)
  have hlabel w (hw : w ∈ Ioc u v) : w ∈ Icc 0 T :=
    ⟨hu.trans hw.1.le, hw.2.trans hvT⟩
  have hinner w (hw : w ∈ Ioc u v) s (hs : s ∈ Icc u w) : s ∈ Icc 0 T :=
    ⟨hu.trans hs.1, hs.2.trans (hw.2.trans hvT)⟩
  have hm₁ w (hw : w ∈ Ioc u v) :
      ENNReal.ofReal ‖S₁.xi u w / (S₁.nu u w : ℂ)‖ ≤ ENNReal.ofReal 4 *
        ∫⁻ s in Icc u w, ENNReal.ofReal ((S₁.r s w / S₁.r u w) ^ (1 / 2 : ℝ)) * K₁ s := by
    apply (stab_in_moment h₁s hεsq hp hu hw.1.le (hw.2.trans hvT)).trans_eq
    congr 1
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only [K₁]
    rw [indicator_of_mem (hinner w hw s hs)]
  have hm₂ w (hw : w ∈ Ioc u v) :
      ENNReal.ofReal ‖S₂.xi u w / (S₂.nu u w : ℂ)‖ ≤ ENNReal.ofReal 4 *
        ∫⁻ s in Icc u w, ENNReal.ofReal ((S₂.r s w / S₂.r u w) ^ (1 / 2 : ℝ)) * K₂ s := by
    apply (stab_in_moment h₂s hεsq hp hu hw.1.le (hw.2.trans hvT)).trans_eq
    congr 1
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only [K₂]
    rw [indicator_of_mem (hinner w hw s hs)]
  have hmD w (hw : w ∈ Ioc u v) :
      ENNReal.ofReal ‖S₁.xi u w / (S₁.nu u w : ℂ) - S₂.xi u w / (S₂.nu u w : ℂ)‖ ≤
        ENNReal.ofReal B * ∫⁻ s in Icc u w,
          ENNReal.ofReal ((S₁.r s w / S₁.r u w) ^ (1 / 2 : ℝ)) * KF s := by
    apply (hDifference T e ε M A S₁ S₂ h₁ h₂ h₁s h₂s hε u w hu hw.1
      (hw.2.trans hvT)).trans_eq
    congr 1
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only [KF, DK, K₂]
    rw [indicator_of_mem (hinner w hw s hs), indicator_of_mem (hinner w hw s hs)]
  have hj₂ w (hw : w ∈ Ioc u v) : ‖jC1 (triangle 0 T) S₂ u w‖ₑ ≤ J₂ w := by
    dsimp only [J₂]
    rw [indicator_of_mem (hlabel w hw)]
    exact enorm_le_normEnvelope (jC1 (triangle 0 T) S₂) ⟨hu, hw.1.le⟩
  have hjD w (hw : w ∈ Ioc u v) :
      ‖jC1 (triangle 0 T) S₁ u w - jC1 (triangle 0 T) S₂ u w‖ₑ ≤ DJ w := by
    dsimp only [DJ]
    rw [indicator_of_mem (hlabel w hw)]
    exact enorm_le_normEnvelope (fun u v =>
      jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v) ⟨hu, hw.1.le⟩
  have hc := stab_geometric_scalar_coefficients_c1 h₁s h₂s hu huv hvT
  have hc₁ : ‖W S₁‖ₑ ≤ ENNReal.ofReal (512 / (v - u) ^ 3) := by
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    simpa only [W, Complex.norm_real, Real.norm_eq_abs] using hc.1
  have hcD : ‖W S₁ - W S₂‖ₑ ≤ ENNReal.ofReal (4096 * (G + U) / (v - u) ^ 3) := by
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    dsimp only [W]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hc.2
  have hr₁ w (hw : w ∈ Ioc u v) : |S₁.r u w| ≤ 1 * S₁.r u w := by
    rw [abs_of_pos (h₁s.c1.r_pos (u, w) ⟨hu, hw.1.le, hw.2.trans hvT⟩ hw.1), one_mul]
  have hr₂ w (hw : w ∈ Ioc u v) : |S₂.r u w| ≤ 1 * S₂.r u w := by
    rw [abs_of_pos (h₂s.c1.r_pos (u, w) ⟨hu, hw.1.le, hw.2.trans hvT⟩ hw.1), one_mul]
  have hrD w (hw : w ∈ Ioc u v) : |S₁.r u w - S₂.r u w| ≤ (4 * G) * S₂.r u w := by
    have hpt : (u, w) ∈ triangle 0 T := ⟨hu, hw.1.le, hw.2.trans hvT⟩
    have hR := h₁s.c1.r_pos _ hpt hw.1
    have hg := stab_geom_sum_le h₁s h₂s hpt
    have hrel : |S₁.r u w - S₂.r u w| / S₁.r u w ≤ G := by
      linarith only [hg, abs_nonneg (S₁.lam u w - S₂.lam u w),
        abs_nonneg (S₁.nu u w - S₂.nu u w)]
    calc
      _ ≤ G * S₁.r u w := (div_le_iff₀ hR).mp hrel
      _ ≤ G * (4 * S₂.r u w) := mul_le_mul_of_nonneg_left
        (stab_radius_compare h₁s h₂s hu hw.1.le (hw.2.trans hvT)).1 hG
      _ = _ := by ring
  have t₁ := stab_geometric_primitive_ordered_of_c1_moment h₂s hu huv hvT
    (r := S₂.r u) (y := fun w => S₂.xi u w / (S₂.nu u w : ℂ))
    (j := jC1 (triangle 0 T) S₂ u) (K := K₂) (J := J₂) (c := W S₁ - W S₂)
    (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 4)
    (show 0 ≤ 4096 * (G + U) by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    mK₂ hr₂ hm₂ hj₂ hcD
  have t₂ := stab_geometric_primitive_ordered_of_c1_moment h₂s hu huv hvT
    (r := fun w => S₁.r u w - S₂.r u w) (y := fun w => S₂.xi u w / (S₂.nu u w : ℂ))
    (j := jC1 (triangle 0 T) S₂ u) (K := K₂) (J := J₂) (c := W S₁)
    (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 4)
    (by norm_num : (0 : ℝ) ≤ 512) (show 0 ≤ 4 * G by positivity)
    mK₂ hrD hm₂ hj₂ hc₁
  have t₃ := stab_geometric_primitive_ordered_of_c1_moment h₁s hu huv hvT
    (r := S₁.r u) (y := fun w => S₁.xi u w / (S₁.nu u w : ℂ) - S₂.xi u w / (S₂.nu u w : ℂ))
    (j := jC1 (triangle 0 T) S₂ u) (K := KF) (J := J₂) (c := W S₁)
    (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hB.le
    (by norm_num : (0 : ℝ) ≤ 512) (by norm_num : (0 : ℝ) ≤ 1)
    mKF hr₁ hmD hj₂ hc₁
  have t₄ := stab_geometric_primitive_ordered_of_c1_moment h₁s hu huv hvT
    (r := S₁.r u) (y := fun w => S₁.xi u w / (S₁.nu u w : ℂ))
    (j := fun w => jC1 (triangle 0 T) S₁ u w - jC1 (triangle 0 T) S₂ u w) (K := K₁) (J := DJ) (c :=
        W S₁)
    (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 4)
    (by norm_num : (0 : ℝ) ≤ 512) (by norm_num : (0 : ℝ) ≤ 1)
    mK₁ hr₁ hm₁ hjD hc₁
  rw [stab_geometric_scalar_source_telescope_c1 h₁s h₂s hu huv hvT]
  exact (enorm_four_aux _ _ _ _).trans (add_le_add
    (add_le_add (add_le_add t₁ t₂) t₃) t₄)

end EmcsfAcExtension.Local
