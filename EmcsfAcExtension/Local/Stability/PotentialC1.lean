module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.ChargeDifferenceIndividual
import EmcsfAcExtension.Local.Stability.PotentialDifferenceAlgebra
import EmcsfAcExtension.Local.Stability.PotentialDifferenceBudget
import EmcsfAcExtension.Infra.Calculus.PartialsC1
import EmcsfAcExtension.Local.Calculus.Normalized

/-! # Classical potential and background-weighted phase estimates

The zero-axis gauge determines the potential primitive. Its individual
bound and the background-weighted difference bound account for both
connection terms in ordinary incoming scalar derivative comparison.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The outgoing potential partial has bound `8 |e| M ε`, with the
numerical constant uniform in every field parameter and derivative supremum. -/
theorem stab_potential_partial_le_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    |pdV (triangle 0 T) S.A u v| ≤ 8 * |e| * M * ε := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hb := hset.box.2 (u, v) hp
  have hc := stab_potential_coefficient_abs_le
    (by rw [abs_of_neg (hset.c1.nu_neg _ hp)]; exact hb.2.2.2.1)
    (by rw [abs_of_pos (hset.c1.lam_pos _ hp)]; exact hb.2.1) hb.2.2.2.2.1
  rw [(hset.c1.eq_v _ hp huv).2.2.2.2.1]
  have heq : S.AV u v = (2 * S.nu u v * S.lam u v / (1 - S.mu u v)) *
      (S.Q u v / S.r u v ^ 2) := by
    dsimp only [Fields.AV]
    rw [div_mul_div_comm]
  have hq : |S.Q u v / S.r u v ^ 2| ≤ |e| * M * ε := by
    simpa only [abs_div, abs_of_nonneg (sq_nonneg (S.r u v))] using
      stab_charge_ratio_le hset hu huv hvT
  rw [heq, abs_mul]
  apply (mul_le_mul hc hq (abs_nonneg _) (by norm_num)).trans_eq
  ring

/-- [internal]
The classical potential is bounded on every axis-to-point segment by
`8 |e| M ε (v-u)`. The coefficient is universal and does not depend on
a derivative supremum, scalar background or minimum radius. -/
theorem Stab.potential_bound_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    |S.A u v| ≤ 8 * |e| * M * ε * (v - u) := by
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩
  have cf := hset.c1.c1_A.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cg := (continuousOn_partial_v hset.c1.c1_A (uniqueDiffOn_triangle hset.pos)).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have hd : ∀ s ∈ Ioo u v, HasDerivAt (S.A u) (pdV (triangle 0 T) S.A u s) s := by
    intro s hs
    exact (hasDerivWithinAt_v_aux hset.c1.c1_A hu hs.1.le
      (hs.2.le.trans hvT)).hasDerivAt (Icc_mem_nhds hs.1 (hs.2.trans_le hvT))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv cf hd
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv cg)
  change (∫ s in u..v, pdV (triangle 0 T) S.A u s) = S.A u v - S.A u u at hi
  rw [hset.data.2 u ⟨hu, huv.trans hvT⟩, sub_zero] at hi
  have hAE : ∀ᵐ s ∂volume.restrict (Icc u v),
      ‖pdV (triangle 0 T) S.A u s‖ ≤ 8 * |e| * M * ε := by
    have hn : ∀ᵐ s : ℝ, s ≠ u := by simp [ae_iff, measure_singleton]
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn] with s hs hsu
    rw [Real.norm_eq_abs]
    exact stab_potential_partial_le_c1 hset hu
      (lt_of_le_of_ne hs.1 hsu.symm) (hs.2.trans hvT)
  have hb := intervalIntegral.integral_mono_ae_restrict huv
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv cg.norm)
    (intervalIntegrable_const (c := 8 * |e| * M * ε)) hAE
  have hnorm := (intervalIntegral.norm_integral_le_integral_norm
    (f := fun s => pdV (triangle 0 T) S.A u s) huv).trans hb
  rw [hi, intervalIntegral.integral_const, smul_eq_mul, Real.norm_eq_abs] at hnorm
  simpa only [mul_comm] using hnorm

/-- The background-weighted potential phase has a scale-correct bound.
The threshold and constant depend only on `A` and the fixed box, before
all other parameters and the pair. The factor `M` on the left is needed
when the ordinary derivative subtracts the two connections. -/
theorem stab_potential_background_phase_bounds (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        M * T * |e| * (supDist T S₁.A S₂.A).toReal ≤ C * sigma e M T *
          ((jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
            ε * (geomDist T S₁ S₂).toReal) := by
  obtain ⟨η, C, hη, hC, hphase⟩ := stab_potential_phase_bounds A hA
  refine ⟨η, C, hη, hC, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall
  have hM1 := h₁s.box.1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) hM1
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hΔ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hp := mul_le_mul_of_nonneg_left
    (hphase T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall).1 hM.le
  have hbound : (M * (jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
      M * ε * (geomDist T S₁ S₂).toReal) / M ≤
      (jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
        ε * (geomDist T S₁ S₂).toReal := by
    rw [div_le_iff₀ hM]
    have hh := mul_le_mul_of_nonneg_left hM1 (mul_nonneg hε hΔ)
    nlinarith only [hh]
  calc
    _ ≤ M * (C * sigma e M T / M ^ 2 *
        (M * (jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
          M * ε * (geomDist T S₁ S₂).toReal)) := by simpa only [mul_assoc] using hp
    _ = (C * sigma e M T) * ((M * (jDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T +
        M * ε * (geomDist T S₁ S₂).toReal) / M) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (mul_nonneg hC.le hσ)

end EmcsfAcExtension.Local
