module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.JCloseInitialMass
import EmcsfAcExtension.Local.Stability.JCloseInitialVariation
import EmcsfAcExtension.Local.Stability.JCloseInitialNorm
import EmcsfAcExtension.Local.Stability.JCloseInitialAlgebra
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Calculus.PartialsC1
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Data-only initial-j Lipschitz estimate

Initial scalar, Maxwell and mass constraints are compared in their common
radius gauge before the renormalized initial derivatives are subtracted.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- [node restart-sec-bv-stability-independent#initial-j-Lipschitz]
The initial j trace is Lipschitz in the normalized datum distance.
Constants depend only on the fixed envelope constant `A`, uniformly in
all physical scales, solution pairs and initial derivative suprema.
The small initial variation used in the proof is derived from the setting. -/
theorem initial_j_lipschitz (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      (∫⁻ v in Icc 0 T, ‖jC1 (triangle 0 T) S₁ 0 v - jC1 (triangle 0 T) S₂ 0 v‖ₑ) ≤
        ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨Cm, hCm, hm⟩ := initial_mass_difference
  obtain ⟨Cv, hCv, hv⟩ := initial_datum_variation_bound A hA
  refine ⟨1 / 4, 4 + 2 * Cm * Cv, by norm_num, by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall
  let δ := dataDist h₁ h₂ T
  let U := Cm * ε * δ
  let w := fun v => S₁.lam 0 v / S₁.r 0 v
  let x₁ := fun v => S₁.theta 0 v / (S₁.lam 0 v : ℂ)
  let x₂ := fun v => S₂.theta 0 v / (S₂.lam 0 v : ℂ)
  let d₁ := pdV (triangle 0 T) S₁.a 0
  let d₂ := pdV (triangle 0 T) S₂.a 0
  have hδ : 0 ≤ δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.2.1
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hεsmall : ε ^ 2 ≤ 1 / 4 := (le_add_of_nonneg_right hσ).trans hsmall
  have hε₁ : ε ≤ 1 := by nlinarith only [hεsmall]
  have hσ₁ : sigma e M T ≤ 1 := by nlinarith only [hsmall, sq_nonneg ε]
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hmass := hm T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁
  have hvar₂ := hv T e ε M S₂ h₂ hs₂ hεsmall
  have hmap : MapsTo (fun v => (0, v)) (Icc 0 T) (triangle 0 T) :=
    fun v hv => ⟨le_rfl, hv.1, hv.2⟩
  have hcont (S : Fields) (hs : StabSetting e T ε M A S h₁) :=
    (continuousOn_partial_v (stab_normalized_out_c1 hs.c1) (uniqueDiffOn_triangle hs.pos)).comp
      (continuous_const.prodMk continuous_id).continuousOn hmap
  have hd₁ : IntervalIntegrable d₁ volume 0 T :=
    (hcont S₁ hs₁).intervalIntegrable_of_Icc (μ := volume) hs₁.pos.le
  have hd₂ : IntervalIntegrable d₂ volume 0 T :=
    ((continuousOn_partial_v (stab_normalized_out_c1 hs₂.c1) (uniqueDiffOn_triangle hs₂.pos)).comp
      (continuous_const.prodMk continuous_id).continuousOn hmap).intervalIntegrable_of_Icc
      (μ := volume) hs₂.pos.le
  have hhardyδ := initial_hardy_difference hs₁ hs₂
  have hhardy₂ := initial_hardy hs₂
  have hwcommon (v : ℝ) (hv : v ∈ Icc 0 T) :
      S₁.lam 0 v / S₁.r 0 v = S₂.lam 0 v / S₂.r 0 v := by
    rw [initial_lam_of_stabSetting hs₁ hv, initial_lam_of_stabSetting hs₂ hv,
      (hs₁.data.1 v hv).1, (hs₂.data.1 v hv).1]
  have hhardy₂' : IntervalIntegrable (fun v => w v * ‖x₂ v‖) volume 0 T := by
    apply hhardy₂.1.congr
    intro v hv
    have hvT : v ∈ Icc 0 T := by simpa only [uIcc_of_le hs₂.pos.le] using uIoc_subset_uIcc hv
    dsimp only [w, x₂]
    rw [hwcommon v hvT]
  have hpoint (v : ℝ) (hv : v ∈ Icc 0 T) :
      ‖jC1 (triangle 0 T) S₁ 0 v - jC1 (triangle 0 T) S₂ 0 v‖ ≤
        ‖d₁ v - d₂ v‖ + U * ‖d₂ v‖ + 3 * ε ^ 2 * (w v * ‖x₁ v - x₂ v‖) +
          U * ε ^ 2 * (w v * ‖x₂ v‖) := by
    have hp := hmap hv
    have hγ := initial_gamma_le_one hs₁ hv
    have hr : 0 ≤ S₁.r 0 v := by rw [(hs₁.data.1 v hv).1]; exact div_nonneg hv.1 (by norm_num)
    have hw : 0 ≤ w v := div_nonneg (hs₁.c1.lam_pos (0, v) hp).le hr
    have hx₁ := (le_add_of_nonneg_right (norm_nonneg _)).trans (hs₁.box.2 (0, v) hp).2.2.2.2.2.1
    have hx₂ := (le_add_of_nonneg_right (norm_nonneg _)).trans (hs₂.box.2 (0, v) hp).2.2.2.2.2.1
    have hγδ : |(1 - S₁.mu 0 v) - (1 - S₂.mu 0 v)| ≤ U := by
      rw [show (1 - S₁.mu 0 v) - (1 - S₂.mu 0 v) = -(S₁.mu 0 v - S₂.mu 0 v) by ring, abs_neg]
      exact hmass v hv
    have h := norm_initial_j_difference_le (x₁ := x₁ v) (x₂ := x₂ v) (d₁ := d₁ v) (d₂ := d₂ v)
      hγ.1.le hγ.2 hγδ hw hx₁ hx₂
    have heq (S : Fields) (d x : ℂ) (hd : d = pdV (triangle 0 T) S.a 0 v)
        (hx : x = S.theta 0 v / S.lam 0 v) (hq : w v = S.lam 0 v / S.r 0 v) :
        jC1 (triangle 0 T) S 0 v = ((1 - S.mu 0 v : ℝ) : ℂ) *
          (d - (w v : ℂ) * (‖x‖ : ℂ) ^ 2 * x) := by
      rw [hd, hx, hq]
      dsimp only [jC1]
      push_cast
      ring
    rw [heq S₁ (d₁ v) (x₁ v) rfl rfl rfl,
      heq S₂ (d₂ v) (x₂ v) rfl rfl (hwcommon v hv)]
    nlinarith only [h]
  have hjint : IntervalIntegrable
      (fun v => jC1 (triangle 0 T) S₁ 0 v - jC1 (triangle 0 T) S₂ 0 v) volume 0 T := by
    simpa only [Function.comp_apply, Function.uncurry_def, Pi.sub_def, id_eq] using!
      (((continuousOn_jC1_aux hs₁.pos hs₁.c1).sub
        (continuousOn_jC1_aux hs₂.pos hs₂.c1)).comp
        (continuous_const.prodMk continuous_id).continuousOn hmap).intervalIntegrable_of_Icc
        (μ := volume) hs₁.pos.le
  have hint := intervalIntegral.integral_mono_on hs₁.pos.le hjint.norm
    ((((hd₁.sub hd₂).norm.add (hd₂.norm.const_mul U)).add
      (hhardyδ.1.const_mul (3 * ε ^ 2))).add (hhardy₂'.const_mul (U * ε ^ 2))) hpoint
  have hD : (∫ v in 0..T, ‖d₁ v - d₂ v‖) ≤ δ := by
    rw [initial_partial_difference_integral_eq_variation hs₁ hs₂]
    exact le_add_of_nonneg_left (norm_nonneg _)
  have hD₂ : (∫ v in 0..T, ‖d₂ v‖) ≤ Cv * ε := by
    rw [initial_partial_integral_eq_variation hs₂]
    exact hvar₂
  have hW₂ : (∫ v in 0..T, w v * ‖x₂ v‖) ≤ Cv * ε := by
    calc
      _ = ∫ v in 0..T, S₂.lam 0 v / S₂.r 0 v * ‖S₂.theta 0 v / S₂.lam 0 v‖ := by
        apply intervalIntegral.integral_congr
        intro v hv
        dsimp only [w, x₂]
        rw [hwcommon v (by simpa only [uIcc_of_le hs₁.pos.le] using hv)]
      _ ≤ _ := hhardy₂.2.trans hvar₂
  rw [intervalIntegral.integral_add
      (((hd₁.sub hd₂).norm.add (hd₂.norm.const_mul U)).add (hhardyδ.1.const_mul (3 * ε ^ 2)))
      (hhardy₂'.const_mul (U * ε ^ 2)),
    intervalIntegral.integral_add ((hd₁.sub hd₂).norm.add (hd₂.norm.const_mul U))
      (hhardyδ.1.const_mul (3 * ε ^ 2)),
    intervalIntegral.integral_add (hd₁.sub hd₂).norm (hd₂.norm.const_mul U),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  have h₁ := mul_le_mul_of_nonneg_left hD₂ hU
  have h₂ := mul_le_mul_of_nonneg_left hhardyδ.2 (by positivity : 0 ≤ 3 * ε ^ 2)
  have h₃ := mul_le_mul_of_nonneg_left hW₂ (by positivity : 0 ≤ U * ε ^ 2)
  have heps₂ : ε ^ 2 ≤ 1 := hεsmall.trans (by norm_num)
  have heps₄ := pow_le_one₀ hε hε₁ (n := 4)
  have hb₁ := mul_le_mul_of_nonneg_right heps₂ (by positivity : 0 ≤ Cm * Cv * δ)
  have hb₂ := mul_le_mul_of_nonneg_right heps₂ (by positivity : 0 ≤ 3 * δ)
  have hb₃ := mul_le_mul_of_nonneg_right heps₄ (by positivity : 0 ≤ Cm * Cv * δ)
  have hfinal : (∫ v in 0..T, ‖jC1 (triangle 0 T) S₁ 0 v - jC1 (triangle 0 T) S₂ 0 v‖) ≤
      (4 + 2 * Cm * Cv) * δ := by
    dsimp only [U] at hint h₁ h₃
    nlinarith only [hint, hD, h₁, h₂, h₃, hb₁, hb₂, hb₃]
  rw [← ofReal_integral_norm_eq_lintegral_enorm
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hs₁.pos.le).mp hjint)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [intervalIntegral.integral_of_le hs₁.pos.le, restrict_Ioc_eq_restrict_Icc] using hfinal

end EmcsfAcExtension.Local.Stab
