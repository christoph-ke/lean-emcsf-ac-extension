module

public import EmcsfAcExtension.Local.Stability.MainRecords
public import EmcsfAcExtension.Local.Stability.SourceDifferenceCharge
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMPrimitiveFields
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMPrimitiveEstimate
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMIntegrable
import EmcsfAcExtension.Local.Stability.SourceDifferenceCoeffField
import EmcsfAcExtension.Local.Stability.OrderedKernelPower

/-! # Incoming charged curvature source comparison

The full length cube from the raw primitive cancels the exterior inverse
cube. The sharper datum remainder is retained pointwise before integration.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Stab

/-- [internal]
 Incoming charged curvature source from first-half comparison records.
`C` depends only on their fixed constant `D`, uniformly in every physical
parameter, solution pair and derivative supremum. The data scale is `ε/M`. -/
theorem em_curvature_source_k_difference_of_differences (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M A : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ≤ 1 → sigma e M T ≤ 1 →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      FieldDifference D T ε (dataDist h₁ h₂ T) S₁ S₂ →
      ChargeDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      ∀ u v, 0 ≤ u → u < v → v ≤ T →
      ‖(S₁.lam u v : ℂ) * S₁.xi u v / (S₁.r u v : ℂ) ^ 2 *
          (curvEMIn e S₁ u v + 2 * starRingEnd ℂ (curvEMIn e S₁ u v)) -
        (S₂.lam u v : ℂ) * S₂.xi u v / (S₂.r u v : ℂ) ^ 2 *
          (curvEMIn e S₂ u v + 2 * starRingEnd ℂ (curvEMIn e S₂ u v))‖ ≤
        C * e ^ 2 * M ^ 2 * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal +
          ε * (geomDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T / M) := by
  obtain ⟨P, hP, hint⟩ := emPrimitive_difference_of_differences D hD
  obtain ⟨B, hB, hcoef⟩ := scalar_primitive_coefficients_difference_of_differences D hD
  obtain ⟨C, hC, hunif⟩ := em_primitive_source_uniform_difference (2 * B) P (by positivity) hP
  refine ⟨C, hC, ?_⟩
  intro T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁ hratio hfield hcharge u v hu huv hvT
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hd : 0 < v - u := sub_pos.mpr huv
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (u, v) hp).2.2.2.2.2.1
  have hM : 0 < M := zero_lt_one.trans_le hs₂.box.1
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let δ := dataDist h₁ h₂ T
  let H := J + ε * G + ε * δ / M
  let X := J + K + ε * G + ε * δ / M
  let Z := K + ε * G + sigma e M T * ε / M * H
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hδ : 0 ≤ δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hterm : 0 ≤ ε * δ / M := by positivity
  have hεG : 0 ≤ ε * G := mul_nonneg hε hG
  have hphase : sigma e M T * ε / M * H ≤ H := by
    have hq : sigma e M T * ε / M ≤ 1 := by
      apply (div_le_iff₀ hM).2
      rw [one_mul]
      exact ((mul_le_of_le_one_left hε hσ₁).trans hε₁).trans hs₂.box.1
    have hH : 0 ≤ H := by dsimp [H]; positivity
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hq hH
  have hZX : Z ≤ 2 * X := by
    dsimp only [Z, X, H] at *
    linarith only [hphase, hJ, hK, hεG, hterm]
  let c₁ := -(S₁.lam u v : ℂ) * S₁.xi u v / (S₁.r u v : ℂ) ^ 3
  let c₂ := -(S₂.lam u v : ℂ) * S₂.xi u v / (S₂.r u v : ℂ) ^ 3
  have hδc : ‖c₁ - c₂‖ ≤ (2 * B) * X / (v - u) ^ 3 := by
    have h := (hcoef T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hratio u v hu huv hvT).2
    have hscaled : B * Z / (v - u) ^ 3 ≤ (2 * B) * X / (v - u) ^ 3 := by
      apply (div_le_div_iff_of_pos_right (pow_pos hd 3)).2
      have := mul_le_mul_of_nonneg_left hZX hB.le
      nlinarith only [this]
    have hneg : c₁ - c₂ = -((S₁.lam u v : ℂ) * S₁.xi u v / (S₁.r u v : ℂ) ^ 3 -
        (S₂.lam u v : ℂ) * S₂.xi u v / (S₂.r u v : ℂ) ^ 3) := by dsimp [c₁, c₂]; ring
    rw [hneg, norm_neg]
    exact h.trans hscaled
  have hc₂ : ‖c₂‖ ≤ 64 * ε / (v - u) ^ 3 := by
    have hr := ofReal_ne_zero.mpr (hs₂.c1.r_pos (u, v) hp huv).ne'
    have heq : (S₂.lam u v : ℂ) * S₂.xi u v / (S₂.r u v : ℂ) ^ 3 =
        ((S₂.lam u v : ℂ) * S₂.xi u v / (S₂.r u v : ℂ) ^ 2) *
          (S₂.r u v : ℂ)⁻¹ := by field_simp
    have hneg : c₂ = -((S₂.lam u v : ℂ) * S₂.xi u v / (S₂.r u v : ℂ) ^ 3) := by dsimp [c₂]; ring
    rw [hneg, norm_neg, heq]
    exact (stab_scalar_primitive_coefficients_le hs₂ hu huv hvT).2
  have hmap : MapsTo (fun w => (w, v)) (Icc u v) (triangle 0 T) :=
    fun w hw => ⟨hu.trans hw.1, hw.2, hvT⟩
  have hrbound (S : Fields) (hs : StabSetting e T ε M A S h₁)
      (w : ℝ) (hw : w ∈ Icc u v) : S.r w v ≤ v - u := by
    have h := (stab_radius_bounds hs (hmap hw).1 (hmap hw).2.1 (hmap hw).2.2).2
    linarith only [h, hw.1, hw.2]
  have hr₁ (w : ℝ) (hw : w ∈ Icc u v) : S₁.r w v ≤ v - u := hrbound S₁ hs₁ w hw
  have hr₂ (w : ℝ) (hw : w ∈ Icc u v) : S₂.r w v ≤ v - u := by
    have h := (stab_radius_bounds hs₂ (hmap hw).1 (hmap hw).2.1 (hmap hw).2.2).2
    linarith only [h, hw.1, hw.2]
  have hi₁ : IntervalIntegrable (fun w => emPrimitiveIn e S₁ w v) volume u v := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le huv.le]
    exact (emPrimitive_integrable_along hs₁ (continuous_id.prodMk continuous_const).continuousOn
        hmap).2
  have hi₂ : IntervalIntegrable (fun w => emPrimitiveIn e S₂ w v) volume u v := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le huv.le]
    exact (emPrimitive_integrable_along hs₂ (continuous_id.prodMk continuous_const).continuousOn
        hmap).2
  have hnorm (w : ℝ) (hw : w ∈ Icc u v) :
      ‖emPrimitiveIn e S₁ w v‖ ≤ 2 * (e ^ 2 * M ^ 2) * ε ^ 2 * (v - u) ^ 2 := by
    have hpw := hmap hw
    have hr0 : 0 ≤ S₁.r w v :=
      (div_nonneg (sub_nonneg.mpr hpw.2.1) (by norm_num : (0 : ℝ) ≤ 4)).trans
        (stab_radius_bounds hs₁ hpw.1 hpw.2.1 hpw.2.2).1
    apply (emPrimitive_norm_le hs₁ hε₁ hpw).2.trans
    have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 (hr₁ w hw) 2)
      (by positivity : 0 ≤ 2 * e ^ 2 * M ^ 2 * ε ^ 2)
    nlinarith only [this]
  have hδnorm (w : ℝ) (hw : w ∈ Icc u v) :
      ‖emPrimitiveIn e S₁ w v - emPrimitiveIn e S₂ w v‖ ≤ P * (e ^ 2 * M ^ 2) * (v - u) ^ 2 * X :=
          by
    rcases hw.2.eq_or_lt with heq | hlt
    · have ha₁ := hs₁.c1.axis v ⟨hu.trans huv.le, le_rfl, hvT⟩
      have ha₂ := hs₂.c1.axis v ⟨hu.trans huv.le, le_rfl, hvT⟩
      rw [heq]
      simp only [emPrimitiveIn, ha₁.1, ha₂.1, ha₁.2.2.1, ha₂.2.2.1]
      norm_num
      positivity
    · have h := (hint T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁ hratio hfield hcharge
        (w, v) (hmap hw) hlt (v - u) hd.le (hr₁ w hw) (hr₂ w hw)).2
      simpa only [mul_assoc] using h
  have h := hunif u v (e ^ 2 * M ^ 2) ε X
    (fun w => emPrimitiveIn e S₁ w v) (fun w => emPrimitiveIn e S₂ w v) c₁ c₂
    huv (by positivity) hε hε₁ hX hi₁ hi₂ hδc hc₂ hnorm hδnorm
  rw [em_curvature_source_k_eq_primitive, em_curvature_source_k_eq_primitive]
  simpa only [c₁, c₂, X, J, K, G, δ, mul_assoc] using h

end EmcsfAcExtension.Local.Stab
