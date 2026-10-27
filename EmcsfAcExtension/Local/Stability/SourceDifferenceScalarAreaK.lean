module

public import EmcsfAcExtension.Local.Stability.MainRecords
import EmcsfAcExtension.Local.Stability.SourceDifferenceScalarPointwise
import EmcsfAcExtension.Local.Stability.SourceDifferenceScalarAlgebra
import EmcsfAcExtension.Local.Stability.SourceDifferenceArea
import EmcsfAcExtension.Local.Stability.SourceDifferenceHardy
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Stability.MainFinite
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Incoming scalar source area difference

Each of the four positive kernels is integrated before replacing its
remaining Hardy norm by the first-half comparison or an independent envelope.
The repaired phase-dependent datum remainder is retained explicitly.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- [internal]
 Incoming half of the repaired scalar-curvature source comparison.
`C` depends only on the fixed envelope and ratio constants `A,D`, uniformly
in the data, triangle, coupling, background and derivative suprema. -/
theorem scalar_source_k_difference_of_differences (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 ≤ 1 / 4 → sigma e M T ≤ 1 →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖(S₁.lam u v : ℂ) * S₁.xi u v / (S₁.r u v : ℂ) ^ 2 *
            (curvScalarIn e (triangle 0 T) S₁ u v +
              2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S₁ u v)) -
          (S₂.lam u v : ℂ) * S₂.xi u v / (S₂.r u v : ℂ) ^ 2 *
            (curvScalarIn e (triangle 0 T) S₂ u v +
              2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S₂ u v))‖ₑ) ≤
        ENNReal.ofReal (C * ε ^ 2 * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
          C * ε ^ 3 * (geomDist T S₁ S₂).toReal +
          C * sigma e M T * ε ^ 4 * dataDist h₁ h₂ T / M) := by
  obtain ⟨P, hP, hpoint⟩ := scalar_source_k_pointwise_of_differences D hD
  obtain ⟨C, hC, hclose⟩ := scalar_source_remainder_absorption_in A D P hA hD hP
  refine ⟨C, hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hset₁ hset₂ hε₂ hσ₁ hratio
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hset₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hset₂.pos.le⟩).2.2.2.2.2.1
  have hε₁ : ε ≤ 1 := by nlinarith only [hε, hε₂]
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hM : 0 < M := zero_lt_one.trans_le hset₂.box.1
  let δ := dataDist h₁ h₂ T
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let Eo := J + ε * G
  let Ei := K + ε * G + sigma e M T * ε / M * (J + ε * G + ε * δ / M)
  have hδ : 0 ≤ δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hEo : 0 ≤ Eo := by dsimp [Eo]; positivity
  have hEi : 0 ≤ Ei := by dsimp [Ei]; positivity
  let F₁ := (triangle 0 T).indicator
    (fun p => ‖S₁.theta p.1 p.2 / (S₁.lam p.1 p.2 : ℂ)‖ₑ)
  let F₂ := (triangle 0 T).indicator
    (fun p => ‖S₂.theta p.1 p.2 / (S₂.lam p.1 p.2 : ℂ)‖ₑ)
  let Fδ := (triangle 0 T).indicator (fun p =>
    ‖S₁.theta p.1 p.2 / (S₁.lam p.1 p.2 : ℂ) - S₂.theta p.1 p.2 / (S₂.lam p.1 p.2 : ℂ)‖ₑ)
  let J₁ := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S₁))
  let J₂ := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S₂))
  let Dk := (Icc 0 T).indicator (inEnv T (fun a b =>
    kC1 e (triangle 0 T) S₁ a b - kC1 e (triangle 0 T) S₂ a b))
  let L := fun p : ℝ × ℝ =>
    ‖(S₁.lam p.1 p.2 : ℂ) * S₁.xi p.1 p.2 / (S₁.r p.1 p.2 : ℂ) ^ 2 *
        (curvScalarIn e (triangle 0 T) S₁ p.1 p.2 +
          2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S₁ p.1 p.2)) -
      (S₂.lam p.1 p.2 : ℂ) * S₂.xi p.1 p.2 / (S₂.r p.1 p.2 : ℂ) ^ 2 *
        (curvScalarIn e (triangle 0 T) S₂ p.1 p.2 +
          2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S₂ p.1 p.2))‖ₑ
  let K₁ := fun p : ℝ × ℝ => scalarPrimitiveKernelIn F₁ J₁ p.1 p.2
  let Kδ := fun p : ℝ × ℝ => scalarPrimitiveKernelIn Fδ J₁ p.1 p.2
  let KD := fun p : ℝ × ℝ => scalarPrimitiveKernelIn F₂ Dk p.1 p.2
  let K₂ := fun p : ℝ × ℝ => scalarPrimitiveKernelIn F₂ J₂ p.1 p.2
  have hy₁ := (stab_out_ratio_c1 hset₁.c1).continuousOn
  have hy₂ := (stab_out_ratio_c1 hset₂.c1).continuousOn
  have hF₁ : Measurable F₁ := measurable_triangle_enorm_indicator hy₁
  have hF₂ : Measurable F₂ := measurable_triangle_enorm_indicator hy₂
  have hFδ : Measurable Fδ := measurable_triangle_enorm_indicator (hy₁.sub hy₂)
  have hJ₁ : Measurable J₁ := measurable_indicator_inEnv (continuousOn_kC1_aux hset₁.pos hset₁.c1)
  have hJ₂ : Measurable J₂ := measurable_indicator_inEnv (continuousOn_kC1_aux hset₂.pos hset₂.c1)
  have hDk : Measurable Dk := measurable_indicator_inEnv
    ((continuousOn_kC1_aux hset₁.pos hset₁.c1).sub (continuousOn_kC1_aux hset₂.pos hset₂.c1))
  have hm₁ : Measurable K₁ := measurable_scalarPrimitiveKernelIn hF₁ hJ₁
  have hmδ : Measurable Kδ := measurable_scalarPrimitiveKernelIn hFδ hJ₁
  have hmD : Measurable KD := measurable_scalarPrimitiveKernelIn hF₂ hDk
  have hm₂ : Measurable K₂ := measurable_scalarPrimitiveKernelIn hF₂ hJ₂
  have hH₁ (w : ℝ) (hw : w ∈ Icc 0 T) :
      (∫⁻ u in Icc w T, ENNReal.ofReal (1 / (u - w)) * F₁ (w, u)) ≤
        ENNReal.ofReal (32 * A * ε) := by
    convert coordinate_out_ratio_budget hset₁ hε₂ hw using 1
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp only [F₁]
    rw [indicator_of_mem (show (w, u) ∈ triangle 0 T from ⟨hw.1, hu.1, hu.2⟩)]
  have hH₂ (w : ℝ) (hw : w ∈ Icc 0 T) :
      (∫⁻ u in Icc w T, ENNReal.ofReal (1 / (u - w)) * F₂ (w, u)) ≤
        ENNReal.ofReal (32 * A * ε) := by
    convert coordinate_out_ratio_budget hset₂ hε₂ hw using 1
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp only [F₂]
    rw [indicator_of_mem (show (w, u) ∈ triangle 0 T from ⟨hw.1, hu.1, hu.2⟩)]
  have hHδ (w : ℝ) (hw : w ∈ Icc 0 T) :
      (∫⁻ u in Icc w T, ENNReal.ofReal (1 / (u - w)) * Fδ (w, u)) ≤
        ENNReal.ofReal (4 * D * Eo) := by
    convert coordinate_out_difference_budget_of_differences hset₁ hratio hw using 1
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp only [Fδ]
    rw [indicator_of_mem (show (w, u) ∈ triangle 0 T from ⟨hw.1, hu.1, hu.2⟩)]
  have hN₁ : (∫⁻ w in Icc 0 T, J₁ w) ≤ ENNReal.ofReal (A * ε) := by
    calc
      _ = ∫⁻ w in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S₁) w := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro w hw
        exact indicator_of_mem hw _
      _ ≤ _ := (le_add_left le_rfl).trans hset₁.env
  have hN₂ : (∫⁻ w in Icc 0 T, J₂ w) ≤ ENNReal.ofReal (A * ε) := by
    calc
      _ = ∫⁻ w in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S₂) w := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro w hw
        exact indicator_of_mem hw _
      _ ≤ _ := (le_add_left le_rfl).trans hset₂.env
  have hND : (∫⁻ w in Icc 0 T, Dk w) = ENNReal.ofReal K := by
    calc
      _ = kDist e T S₁ S₂ := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro w hw
        exact indicator_of_mem hw _
      _ = _ := (ENNReal.ofReal_toReal (kDist_ne_top_of_settings hset₁ hset₂)).symm
  have hk₁ : (∫⁻ p in triangle 0 T, K₁ p ∂(volume.prod volume)) ≤
      ENNReal.ofReal (16 * A ^ 2 * ε ^ 2) := by
    apply (incoming_primitive_kernel_area_le hF₁ hJ₁ hH₁).trans
    calc
      _ ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal (32 * A * ε) *
          ENNReal.ofReal (A * ε) := mul_le_mul' le_rfl hN₁
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  have hk₂ : (∫⁻ p in triangle 0 T, K₂ p ∂(volume.prod volume)) ≤
      ENNReal.ofReal (16 * A ^ 2 * ε ^ 2) := by
    apply (incoming_primitive_kernel_area_le hF₂ hJ₂ hH₂).trans
    calc
      _ ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal (32 * A * ε) *
          ENNReal.ofReal (A * ε) := mul_le_mul' le_rfl hN₂
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  have hkδ : (∫⁻ p in triangle 0 T, Kδ p ∂(volume.prod volume)) ≤
      ENNReal.ofReal (2 * D * A * ε * Eo) := by
    apply (incoming_primitive_kernel_area_le hFδ hJ₁ hHδ).trans
    calc
      _ ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal (4 * D * Eo) *
          ENNReal.ofReal (A * ε) := mul_le_mul' le_rfl hN₁
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  have hkD : (∫⁻ p in triangle 0 T, KD p ∂(volume.prod volume)) ≤
      ENNReal.ofReal (16 * A * ε * K) := by
    apply (incoming_primitive_kernel_area_le hF₂ hDk hH₂).trans
    rw [hND]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← ENNReal.ofReal_mul (by positivity)]
    apply le_of_eq
    congr 1
    ring
  have hmajor (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) :
      L p ≤ ENNReal.ofReal (P * Ei) * K₁ p + ENNReal.ofReal (P * ε) * Kδ p +
        ENNReal.ofReal (P * ε) * KD p + ENNReal.ofReal (P * (ε * G)) * K₂ p := by
    rcases hp.2.1.eq_or_lt with heq | hlt
    · have hr₁ := (hset₁.c1.axis p.1 ⟨hp.1, le_rfl, heq.trans_le hp.2.2⟩).1
      have hr₂ := (hset₂.c1.axis p.1 ⟨hp.1, le_rfl, heq.trans_le hp.2.2⟩).1
      have hz : L p = 0 := by
        dsimp only [L]
        rw [← heq, hr₁, hr₂]
        simp
      rw [hz]
      exact bot_le
    · apply (hpoint T e ε M A S₁ S₂ h₁ h₂ hset₁ hset₂ hratio p.1 p.2 hp.1 hlt hp.2.2).trans_eq
      simp only [ENNReal.ofReal_mul hP.le]
      dsimp only [K₁, Kδ, KD, K₂, Ei, G]
      ring
  have harea := source_area_le_four_majorants hm₁ hmδ hmD hm₂ hmajor
  apply harea.trans
  calc
    _ ≤ ENNReal.ofReal (P * Ei) * ENNReal.ofReal (16 * A ^ 2 * ε ^ 2) +
        ENNReal.ofReal (P * ε) * ENNReal.ofReal (2 * D * A * ε * Eo) +
        ENNReal.ofReal (P * ε) * ENNReal.ofReal (16 * A * ε * K) +
        ENNReal.ofReal (P * (ε * G)) * ENNReal.ofReal (16 * A ^ 2 * ε ^ 2) :=
      add_le_add (add_le_add (add_le_add (mul_le_mul' le_rfl hk₁)
        (mul_le_mul' le_rfl hkδ)) (mul_le_mul' le_rfl hkD)) (mul_le_mul' le_rfl hk₂)
    _ = ENNReal.ofReal (P * (16 * A ^ 2 * ε ^ 2 * Ei + 2 * D * A * ε ^ 2 * Eo +
        16 * A * ε ^ 2 * K + 16 * A ^ 2 * ε ^ 3 * G)) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (hclose ε (sigma e M T) M δ J K G hε hε₁ hσ hσ₁ hset₂.box.1 hδ hJ hK hG)

end EmcsfAcExtension.Local.Stab
