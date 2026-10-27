module

public import EmcsfAcExtension.Local.Stability.MainRecords
public import EmcsfAcExtension.Local.Stability.SourceDifferenceKernel
import EmcsfAcExtension.Local.Stability.SourceDifferenceCoeffField
import EmcsfAcExtension.Local.Stability.SourceDifferenceIdentity
import EmcsfAcExtension.Local.Stability.SourceDifferencePrimitiveKernel
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Stability.MainFinite
import EmcsfAcExtension.Local.Stability.OrderedKernelPower
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Four-kernel pointwise scalar source comparison

All factors of the literal primitive are subtracted before applying the
positive kernel estimate. The first-half ratio record supplies the outer
coefficient comparison; the relative radius distance controls the inner radius.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- [internal]
 Outgoing scalar source difference bounded by four positive primitive
kernels. `C` depends only on the fixed ratio comparison constant `D`,
uniformly in the pair and every scale and derivative supremum. -/
theorem scalar_source_j_pointwise_of_differences (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M A : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      ∀ u v, 0 ≤ u → u < v → v ≤ T →
      let G := (geomDist T S₁ S₂).toReal
      let E := (jDist T S₁ S₂).toReal + ε * G
      let F₁ := (triangle 0 T).indicator
        (fun p => ‖S₁.xi p.1 p.2 / (S₁.nu p.1 p.2 : ℂ)‖ₑ)
      let F₂ := (triangle 0 T).indicator
        (fun p => ‖S₂.xi p.1 p.2 / (S₂.nu p.1 p.2 : ℂ)‖ₑ)
      let Fδ := (triangle 0 T).indicator (fun p =>
        ‖S₁.xi p.1 p.2 / (S₁.nu p.1 p.2 : ℂ) - S₂.xi p.1 p.2 / (S₂.nu p.1 p.2 : ℂ)‖ₑ)
      let J₁ := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S₁))
      let J₂ := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S₂))
      let Dj := (Icc 0 T).indicator (outEnv 0 (fun a b =>
        jC1 (triangle 0 T) S₁ a b - jC1 (triangle 0 T) S₂ a b))
      ‖(S₁.nu u v : ℂ) * S₁.theta u v / (S₁.r u v : ℂ) ^ 2 *
          (curvScalar (triangle 0 T) S₁ u v +
            2 * starRingEnd ℂ (curvScalar (triangle 0 T) S₁ u v)) -
        (S₂.nu u v : ℂ) * S₂.theta u v / (S₂.r u v : ℂ) ^ 2 *
          (curvScalar (triangle 0 T) S₂ u v +
            2 * starRingEnd ℂ (curvScalar (triangle 0 T) S₂ u v))‖ₑ ≤
      ENNReal.ofReal C * (ENNReal.ofReal E * scalarPrimitiveKernelOut F₁ J₁ u v +
        ENNReal.ofReal ε * scalarPrimitiveKernelOut Fδ J₁ u v +
        ENNReal.ofReal ε * scalarPrimitiveKernelOut F₂ Dj u v +
        ENNReal.ofReal (ε * G) * scalarPrimitiveKernelOut F₂ J₂ u v) := by
  obtain ⟨C₀, hC₀, hcoef⟩ := scalar_primitive_coefficients_difference_of_differences D hD
  let B := C₀ + 64
  have hB : 0 < B := by dsimp [B]; linarith only [hC₀]
  refine ⟨3 * B, mul_pos (by norm_num) hB, ?_⟩
  intro T e ε M A S₁ S₂ h₁ h₂ hset₁ hset₂ hratio u v hu huv hvT
  dsimp only
  let G := (geomDist T S₁ S₂).toReal
  let E := (jDist T S₁ S₂).toReal + ε * G
  let F₁ := (triangle 0 T).indicator
    (fun p => ‖S₁.xi p.1 p.2 / (S₁.nu p.1 p.2 : ℂ)‖ₑ)
  let F₂ := (triangle 0 T).indicator
    (fun p => ‖S₂.xi p.1 p.2 / (S₂.nu p.1 p.2 : ℂ)‖ₑ)
  let Fδ := (triangle 0 T).indicator (fun p =>
    ‖S₁.xi p.1 p.2 / (S₁.nu p.1 p.2 : ℂ) - S₂.xi p.1 p.2 / (S₂.nu p.1 p.2 : ℂ)‖ₑ)
  let J₁ := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S₁))
  let J₂ := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S₂))
  let Dj := (Icc 0 T).indicator (outEnv 0 (fun a b =>
    jC1 (triangle 0 T) S₁ a b - jC1 (triangle 0 T) S₂ a b))
  let c₁ := (S₁.nu u v : ℂ) * S₁.theta u v / (S₁.r u v : ℂ) ^ 3
  let c₂ := (S₂.nu u v : ℂ) * S₂.theta u v / (S₂.r u v : ℂ) ^ 3
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hd : 0 < v - u := sub_pos.mpr huv
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hset₂.box.2 (u, v) hp).2.2.2.2.2.1
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hc : ‖c₁ - c₂‖ₑ ≤ ENNReal.ofReal (B * E / (v - u) ^ 3) := by
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    apply ((hcoef T e ε M A S₁ S₂ h₁ h₂ hset₁ hset₂ hratio u v hu huv hvT).1).trans
    apply (div_le_div_iff_of_pos_right (pow_pos hd 3)).2
    dsimp [B]
    nlinarith only [hE]
  have hc₂ : ‖c₂‖ₑ ≤ ENNReal.ofReal (B * ε / (v - u) ^ 3) := by
    have hr := ofReal_ne_zero.mpr (hset₂.c1.r_pos (u, v) hp huv).ne'
    have heq : c₂ = ((S₂.nu u v : ℂ) * S₂.theta u v / (S₂.r u v : ℂ) ^ 2) *
        (S₂.r u v : ℂ)⁻¹ := by dsimp [c₂]; field_simp
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [heq]
    apply (stab_scalar_primitive_coefficients_le hset₂ hu huv hvT).1.trans
    apply (div_le_div_iff_of_pos_right (pow_pos hd 3)).2
    dsimp [B]
    nlinarith only [hC₀, hε]
  have hjc₁ := continuousOn_jC1_aux hset₁.pos hset₁.c1
  have hjc₂ := continuousOn_jC1_aux hset₂.pos hset₂.c1
  have hJ₁ : Measurable J₁ := measurable_indicator_outEnv hjc₁
  have hJ₂ : Measurable J₂ := measurable_indicator_outEnv hjc₂
  have hDj : Measurable Dj := measurable_indicator_outEnv (hjc₁.sub hjc₂)
  have hmap : MapsTo (fun w => (u, w)) (Icc u v) (triangle 0 T) :=
    fun w hw => ⟨hu, hw.1, hw.2.trans hvT⟩
  have hy₁ : AEStronglyMeasurable (fun w => S₁.xi u w / (S₁.nu u w : ℂ))
      (volume.restrict (Icc u v)) :=
    ((stab_in_ratio_c1 hset₁.c1).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap).aestronglyMeasurable
          measurableSet_Icc
  have hy₂ : AEStronglyMeasurable (fun w => S₂.xi u w / (S₂.nu u w : ℂ))
      (volume.restrict (Icc u v)) :=
    ((stab_in_ratio_c1 hset₂.c1).continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hmap).aestronglyMeasurable
          measurableSet_Icc
  have hr (w : ℝ) (hw : w ∈ Icc u v) : 0 ≤ S₁.r u w ∧ S₁.r u w ≤ w - u := by
    have hb := stab_radius_bounds hset₁ hu hw.1 (hw.2.trans hvT)
    exact ⟨(div_nonneg (sub_nonneg.mpr hw.1) (by norm_num : (0 : ℝ) ≤ 4)).trans hb.1, hb.2⟩
  have hδr (w : ℝ) (hw : w ∈ Icc u v) : |S₁.r u w - S₂.r u w| ≤ G * (w - u) :=
    (radius_difference_le_geomDist hset₁ hset₂ (hmap hw)).trans
      (mul_le_mul_of_nonneg_left (hr w hw).2 hG)
  have hlabel₁ (w : ℝ) (hw : w ∈ Icc u v) : ‖jC1 (triangle 0 T) S₁ u w‖ₑ ≤ J₁ w := by
    dsimp only [J₁]
    rw [indicator_of_mem (show w ∈ Icc 0 T from ⟨hu.trans hw.1, hw.2.trans hvT⟩)]
    exact le_iSup₂_of_le u ⟨hu, hw.1⟩ le_rfl
  have hlabel₂ (w : ℝ) (hw : w ∈ Icc u v) : ‖jC1 (triangle 0 T) S₂ u w‖ₑ ≤ J₂ w := by
    dsimp only [J₂]
    rw [indicator_of_mem (show w ∈ Icc 0 T from ⟨hu.trans hw.1, hw.2.trans hvT⟩)]
    exact le_iSup₂_of_le u ⟨hu, hw.1⟩ le_rfl
  have hlabelδ (w : ℝ) (hw : w ∈ Icc u v) :
      ‖jC1 (triangle 0 T) S₁ u w - jC1 (triangle 0 T) S₂ u w‖ₑ ≤ Dj w := by
    dsimp only [Dj]
    rw [indicator_of_mem (show w ∈ Icc 0 T from ⟨hu.trans hw.1, hw.2.trans hvT⟩)]
    exact le_iSup₂_of_le u ⟨hu, hw.1⟩ le_rfl
  have hraw := scalar_primitive_difference_kernel_le huv hB.le hE hε hG
    (by fun_prop : AEMeasurable (fun w : ℝ => w - u) (volume.restrict (Icc u v)))
    hy₁ hy₂ hJ₁ hJ₂ hDj
    (scalar_primitive_j_integrable hset₁ hu huv.le hvT)
    (scalar_primitive_j_integrable hset₂ hu huv.le hvT)
    hr hδr hlabel₁ hlabel₂ hlabelδ hc hc₂
  have hkernel (F : ℝ × ℝ → ℝ≥0∞) (f : ℝ → ℝ≥0∞) (J : ℝ → ℝ≥0∞)
      (hF : ∀ w ∈ Icc u v, F (u, w) = f w) :
      scalarPrimitiveKernelOut F J u v = ENNReal.ofReal (1 / (v - u) ^ 3) *
        ∫⁻ w in Icc u v, ENNReal.ofReal (w - u) * f w * J w := by
    unfold scalarPrimitiveKernelOut
    congr 1
    apply setLIntegral_congr_fun measurableSet_Icc
    intro w hw
    dsimp only
    rw [hF w hw]
  have hF₁ (w : ℝ) (hw : w ∈ Icc u v) :
      F₁ (u, w) = ‖S₁.xi u w / (S₁.nu u w : ℂ)‖ₑ := by
    exact indicator_of_mem (hmap hw) _
  have hF₂ (w : ℝ) (hw : w ∈ Icc u v) :
      F₂ (u, w) = ‖S₂.xi u w / (S₂.nu u w : ℂ)‖ₑ := by
    exact indicator_of_mem (hmap hw) _
  have hFδ (w : ℝ) (hw : w ∈ Icc u v) : Fδ (u, w) =
      ‖S₁.xi u w / (S₁.nu u w : ℂ) - S₂.xi u w / (S₂.nu u w : ℂ)‖ₑ := by
    exact indicator_of_mem (hmap hw) _
  rw [scalar_source_j_eq_primitive, scalar_source_j_eq_primitive]
  simp only [intervalIntegral.integral_of_le huv.le, restrict_Ioc_eq_restrict_Icc]
  change _ ≤ ENNReal.ofReal (3 * B) * (ENNReal.ofReal E * scalarPrimitiveKernelOut F₁ J₁ u v +
    ENNReal.ofReal ε * scalarPrimitiveKernelOut Fδ J₁ u v +
    ENNReal.ofReal ε * scalarPrimitiveKernelOut F₂ Dj u v +
    ENNReal.ofReal (ε * G) * scalarPrimitiveKernelOut F₂ J₂ u v)
  rw [hkernel F₁ _ J₁ hF₁, hkernel Fδ _ J₁ hFδ, hkernel F₂ _ Dj hF₂, hkernel F₂ _ J₂ hF₂]
  exact hraw

/-- [internal]
 Incoming scalar source difference bounded by four positive primitive
kernels. `C` depends only on the fixed ratio comparison constant `D`,
uniformly in the pair and every scale and derivative supremum. -/
theorem scalar_source_k_pointwise_of_differences (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M A : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      ∀ u v, 0 ≤ u → u < v → v ≤ T →
      let G := (geomDist T S₁ S₂).toReal
      let E := (kDist e T S₁ S₂).toReal + ε * G + sigma e M T * ε / M *
        ((jDist T S₁ S₂).toReal + ε * G + ε * dataDist h₁ h₂ T / M)
      let F₁ := (triangle 0 T).indicator
        (fun p => ‖S₁.theta p.1 p.2 / (S₁.lam p.1 p.2 : ℂ)‖ₑ)
      let F₂ := (triangle 0 T).indicator
        (fun p => ‖S₂.theta p.1 p.2 / (S₂.lam p.1 p.2 : ℂ)‖ₑ)
      let Fδ := (triangle 0 T).indicator (fun p =>
        ‖S₁.theta p.1 p.2 / (S₁.lam p.1 p.2 : ℂ) - S₂.theta p.1 p.2 / (S₂.lam p.1 p.2 : ℂ)‖ₑ)
      let J₁ := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S₁))
      let J₂ := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S₂))
      let Dj := (Icc 0 T).indicator (inEnv T (fun a b =>
        kC1 e (triangle 0 T) S₁ a b - kC1 e (triangle 0 T) S₂ a b))
      ‖(S₁.lam u v : ℂ) * S₁.xi u v / (S₁.r u v : ℂ) ^ 2 *
          (curvScalarIn e (triangle 0 T) S₁ u v +
            2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S₁ u v)) -
        (S₂.lam u v : ℂ) * S₂.xi u v / (S₂.r u v : ℂ) ^ 2 *
          (curvScalarIn e (triangle 0 T) S₂ u v +
            2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S₂ u v))‖ₑ ≤
      ENNReal.ofReal C * (ENNReal.ofReal E * scalarPrimitiveKernelIn F₁ J₁ u v +
        ENNReal.ofReal ε * scalarPrimitiveKernelIn Fδ J₁ u v +
        ENNReal.ofReal ε * scalarPrimitiveKernelIn F₂ Dj u v +
        ENNReal.ofReal (ε * G) * scalarPrimitiveKernelIn F₂ J₂ u v) := by
  obtain ⟨C₀, hC₀, hcoef⟩ := scalar_primitive_coefficients_difference_of_differences D hD
  let B := C₀ + 64
  have hB : 0 < B := by dsimp [B]; linarith only [hC₀]
  refine ⟨3 * B, mul_pos (by norm_num) hB, ?_⟩
  intro T e ε M A S₁ S₂ h₁ h₂ hset₁ hset₂ hratio u v hu huv hvT
  dsimp only
  let G := (geomDist T S₁ S₂).toReal
  let E := (kDist e T S₁ S₂).toReal + ε * G + sigma e M T * ε / M *
        ((jDist T S₁ S₂).toReal + ε * G + ε * dataDist h₁ h₂ T / M)
  let F₁ := (triangle 0 T).indicator
    (fun p => ‖S₁.theta p.1 p.2 / (S₁.lam p.1 p.2 : ℂ)‖ₑ)
  let F₂ := (triangle 0 T).indicator
    (fun p => ‖S₂.theta p.1 p.2 / (S₂.lam p.1 p.2 : ℂ)‖ₑ)
  let Fδ := (triangle 0 T).indicator (fun p =>
    ‖S₁.theta p.1 p.2 / (S₁.lam p.1 p.2 : ℂ) - S₂.theta p.1 p.2 / (S₂.lam p.1 p.2 : ℂ)‖ₑ)
  let J₁ := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S₁))
  let J₂ := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S₂))
  let Dj := (Icc 0 T).indicator (inEnv T (fun a b =>
    kC1 e (triangle 0 T) S₁ a b - kC1 e (triangle 0 T) S₂ a b))
  let c₁ := (S₁.lam u v : ℂ) * S₁.xi u v / (S₁.r u v : ℂ) ^ 3
  let c₂ := (S₂.lam u v : ℂ) * S₂.xi u v / (S₂.r u v : ℂ) ^ 3
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hd : 0 < v - u := sub_pos.mpr huv
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hset₂.box.2 (u, v) hp).2.2.2.2.2.1
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hM0 : 0 ≤ M := zero_le_one.trans hset₂.box.1
  have hδ0 : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hσ0 : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hc : ‖c₁ - c₂‖ₑ ≤ ENNReal.ofReal (B * E / (v - u) ^ 3) := by
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    apply ((hcoef T e ε M A S₁ S₂ h₁ h₂ hset₁ hset₂ hratio u v hu huv hvT).2).trans
    apply (div_le_div_iff_of_pos_right (pow_pos hd 3)).2
    dsimp [B]
    nlinarith only [hE]
  have hc₂ : ‖c₂‖ₑ ≤ ENNReal.ofReal (B * ε / (v - u) ^ 3) := by
    have hr := ofReal_ne_zero.mpr (hset₂.c1.r_pos (u, v) hp huv).ne'
    have heq : c₂ = ((S₂.lam u v : ℂ) * S₂.xi u v / (S₂.r u v : ℂ) ^ 2) *
        (S₂.r u v : ℂ)⁻¹ := by dsimp [c₂]; field_simp
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [heq]
    apply (stab_scalar_primitive_coefficients_le hset₂ hu huv hvT).2.trans
    apply (div_le_div_iff_of_pos_right (pow_pos hd 3)).2
    dsimp [B]
    nlinarith only [hC₀, hε]
  have hjc₁ := continuousOn_kC1_aux hset₁.pos hset₁.c1
  have hjc₂ := continuousOn_kC1_aux hset₂.pos hset₂.c1
  have hJ₁ : Measurable J₁ := measurable_indicator_inEnv hjc₁
  have hJ₂ : Measurable J₂ := measurable_indicator_inEnv hjc₂
  have hDj : Measurable Dj := measurable_indicator_inEnv (hjc₁.sub hjc₂)
  have hmap : MapsTo (fun w => (w, v)) (Icc u v) (triangle 0 T) :=
    fun w hw => ⟨hu.trans hw.1, hw.2, hvT⟩
  have hy₁ : AEStronglyMeasurable (fun w => S₁.theta w v / (S₁.lam w v : ℂ))
      (volume.restrict (Icc u v)) :=
    ((stab_out_ratio_c1 hset₁.c1).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap).aestronglyMeasurable
          measurableSet_Icc
  have hy₂ : AEStronglyMeasurable (fun w => S₂.theta w v / (S₂.lam w v : ℂ))
      (volume.restrict (Icc u v)) :=
    ((stab_out_ratio_c1 hset₂.c1).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hmap).aestronglyMeasurable
          measurableSet_Icc
  have hr (w : ℝ) (hw : w ∈ Icc u v) : 0 ≤ S₁.r w v ∧ S₁.r w v ≤ v - w := by
    have hb := stab_radius_bounds hset₁ (hu.trans hw.1) hw.2 hvT
    exact ⟨(div_nonneg (sub_nonneg.mpr hw.2) (by norm_num : (0 : ℝ) ≤ 4)).trans hb.1, hb.2⟩
  have hδr (w : ℝ) (hw : w ∈ Icc u v) : |S₁.r w v - S₂.r w v| ≤ G * (v - w) :=
    (radius_difference_le_geomDist hset₁ hset₂ (hmap hw)).trans
      (mul_le_mul_of_nonneg_left (hr w hw).2 hG)
  have hlabel₁ (w : ℝ) (hw : w ∈ Icc u v) : ‖kC1 e (triangle 0 T) S₁ w v‖ₑ ≤ J₁ w := by
    dsimp only [J₁]
    rw [indicator_of_mem (show w ∈ Icc 0 T from ⟨hu.trans hw.1, hw.2.trans hvT⟩)]
    exact le_iSup₂_of_le v ⟨hw.2, hvT⟩ le_rfl
  have hlabel₂ (w : ℝ) (hw : w ∈ Icc u v) : ‖kC1 e (triangle 0 T) S₂ w v‖ₑ ≤ J₂ w := by
    dsimp only [J₂]
    rw [indicator_of_mem (show w ∈ Icc 0 T from ⟨hu.trans hw.1, hw.2.trans hvT⟩)]
    exact le_iSup₂_of_le v ⟨hw.2, hvT⟩ le_rfl
  have hlabelδ (w : ℝ) (hw : w ∈ Icc u v) :
      ‖kC1 e (triangle 0 T) S₁ w v - kC1 e (triangle 0 T) S₂ w v‖ₑ ≤ Dj w := by
    dsimp only [Dj]
    rw [indicator_of_mem (show w ∈ Icc 0 T from ⟨hu.trans hw.1, hw.2.trans hvT⟩)]
    exact le_iSup₂_of_le v ⟨hw.2, hvT⟩ le_rfl
  have hraw := scalar_primitive_difference_kernel_le huv hB.le hE hε hG
    (by fun_prop : AEMeasurable (fun w : ℝ => v - w) (volume.restrict (Icc u v)))
    hy₁ hy₂ hJ₁ hJ₂ hDj
    (scalar_primitive_k_integrable hset₁ hu huv.le hvT)
    (scalar_primitive_k_integrable hset₂ hu huv.le hvT)
    hr hδr hlabel₁ hlabel₂ hlabelδ hc hc₂
  have hkernel (F : ℝ × ℝ → ℝ≥0∞) (f : ℝ → ℝ≥0∞) (J : ℝ → ℝ≥0∞)
      (hF : ∀ w ∈ Icc u v, F (w, v) = f w) :
      scalarPrimitiveKernelIn F J u v = ENNReal.ofReal (1 / (v - u) ^ 3) *
        ∫⁻ w in Icc u v, ENNReal.ofReal (v - w) * f w * J w := by
    unfold scalarPrimitiveKernelIn
    congr 1
    apply setLIntegral_congr_fun measurableSet_Icc
    intro w hw
    dsimp only
    rw [hF w hw]
  have hF₁ (w : ℝ) (hw : w ∈ Icc u v) :
      F₁ (w, v) = ‖S₁.theta w v / (S₁.lam w v : ℂ)‖ₑ := by
    exact indicator_of_mem (hmap hw) _
  have hF₂ (w : ℝ) (hw : w ∈ Icc u v) :
      F₂ (w, v) = ‖S₂.theta w v / (S₂.lam w v : ℂ)‖ₑ := by
    exact indicator_of_mem (hmap hw) _
  have hFδ (w : ℝ) (hw : w ∈ Icc u v) : Fδ (w, v) =
      ‖S₁.theta w v / (S₁.lam w v : ℂ) - S₂.theta w v / (S₂.lam w v : ℂ)‖ₑ := by
    exact indicator_of_mem (hmap hw) _
  let z₁ := ∫ w in Icc u v, (S₁.r w v : ℂ) *
    starRingEnd ℂ (S₁.theta w v / S₁.lam w v) * kC1 e (triangle 0 T) S₁ w v
  let z₂ := ∫ w in Icc u v, (S₂.r w v : ℂ) *
    starRingEnd ℂ (S₂.theta w v / S₂.lam w v) * kC1 e (triangle 0 T) S₂ w v
  have hswap : ‖c₂ * (z₂ + 2 * starRingEnd ℂ z₂) - c₁ * (z₁ + 2 * starRingEnd ℂ z₁)‖ₑ =
      ‖c₁ * (z₁ + 2 * starRingEnd ℂ z₁) - c₂ * (z₂ + 2 * starRingEnd ℂ z₂)‖ₑ := by
    rw [show c₂ * (z₂ + 2 * starRingEnd ℂ z₂) - c₁ * (z₁ + 2 * starRingEnd ℂ z₁) =
      -(c₁ * (z₁ + 2 * starRingEnd ℂ z₁) - c₂ * (z₂ + 2 * starRingEnd ℂ z₂)) by ring,
      enorm_neg]
  rw [scalar_source_k_eq_primitive, scalar_source_k_eq_primitive]
  simp only [intervalIntegral.integral_of_le huv.le, restrict_Ioc_eq_restrict_Icc,
    neg_mul, neg_div, neg_sub_neg]
  rw [hswap]
  change _ ≤ ENNReal.ofReal (3 * B) * (ENNReal.ofReal E * scalarPrimitiveKernelIn F₁ J₁ u v +
    ENNReal.ofReal ε * scalarPrimitiveKernelIn Fδ J₁ u v +
    ENNReal.ofReal ε * scalarPrimitiveKernelIn F₂ Dj u v +
    ENNReal.ofReal (ε * G) * scalarPrimitiveKernelIn F₂ J₂ u v)
  rw [hkernel F₁ _ J₁ hF₁, hkernel Fδ _ J₁ hFδ, hkernel F₂ _ Dj hF₂, hkernel F₂ _ J₂ hF₂]
  exact hraw

end EmcsfAcExtension.Local.Stab
