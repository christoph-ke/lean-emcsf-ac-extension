module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongCrossIntegral
import EmcsfAcExtension.Local.Stability.ExtendedMass
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMass
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassCharge
import EmcsfAcExtension.Local.Stability.GeomStrongMassInCharge

/-! # Strong cross expansion derivative comparison

The two weighted mass norms and charge-square norms close the cross
source in both section orientations, uniformly through the regular axis.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
Quantitative smooth local cross expansion comparison. Constants and
threshold depend only on `A` and the pending uniform main Lipschitz
constant `C₀`, before coupling, time, background, data and the pair.
There is no minimum-radius or initial derivative-supremum dependence.
-/
theorem Stab.cross_geometric_derivatives_difference_of_main_lipschitz_c1
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤
          ENNReal.ofReal (C₀ * dataDist h₁ h₂ T) →
        (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
          ‖pdV (triangle 0 T) S₁.nu u v - pdV (triangle 0 T) S₂.nu u v‖ₑ) +
        (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
          ‖pdU (triangle 0 T) S₁.lam u v - pdU (triangle 0 T) S₂.lam u v‖ₑ) ≤
            ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨ηw, Cw, hηw, hCw, hWeighted⟩ := stab_mu_flux_difference_of_main_lipschitz A C₀ hA hC₀
  obtain ⟨ηm, Cm, hηm, hCm, hMass⟩ := Stab.mass_volterra_difference A hA
  obtain ⟨ηo, Co, hηo, hCo, hOut⟩ := stab_out_em_difference A hA
  obtain ⟨ηi, Ci, hηi, hCi, hIn⟩ := stab_in_em_difference A hA
  let Cu := Cm * (4 * C₀ + 1)
  let R := 4096 * A + 544
  let D := (84 * C₀ + 16 * Cu) * R
  let C := 4 * Cw + 4 * (Co + Ci) * (2 * C₀ + 1) + 2 * D
  have hCu : 0 < Cu := by dsimp only [Cu]; positivity
  have hR : 0 < R := by dsimp only [R]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨min ηw (min ηm (min ηo (min ηi (1 / 4)))), C,
    lt_min hηw (lt_min hηm (lt_min hηo (lt_min hηi (by norm_num)))),
    by dsimp only [C]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain
  let Δ := dataDist h₁ h₂ T
  let B := C₀ * Δ
  let J := (jDist T S₁ S₂).toReal
  let G := (geomDist T S₁ S₂).toReal
  let U := (supDist T S₁.mu S₂.mu).toReal
  let H := J + ε * Δ + ε * G
  have hT := h₁s.pos
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := mul_nonneg hC₀.le hΔ
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hU0 : 0 ≤ U := ENNReal.toReal_nonneg
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, hT.le⟩).2.2.2.2.2.1)
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hsize : ε ^ 2 + sigma e M T ≤ 1 / 4 := hsmall.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
  have hεsq : ε ^ 2 ≤ 1 / 4 := by linarith only [hsize, hσ]
  have hεsq1 : ε ^ 2 ≤ 1 := by linarith only [hεsq]
  have hε1 : ε ≤ 1 := by nlinarith only [hεsq, sq_nonneg (ε - 1)]
  have hσ1 : sigma e M T ≤ 1 := by linarith only [hsize, sq_nonneg ε]
  have real_bound {X : ℝ≥0∞} (hX : X ≤ ENNReal.ofReal B) : X.toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hX
  have hJ : J ≤ B := real_bound
    ((le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans hmain))
  have hG : G ≤ B := real_bound ((le_add_of_nonneg_left bot_le).trans hmain)
  have hHb : H ≤ (2 * C₀ + 1) * Δ := by
    calc
      _ ≤ B + 1 * Δ + 1 * B := by dsimp only [H]; gcongr
      _ = _ := by dsimp only [B]; ring
  have hm := hMass T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hmB : supDist T S₁.mu S₂.mu ≤ ENNReal.ofReal (Cu * Δ) := by
    apply ((le_add_of_nonneg_right bot_le).trans hm).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Cm * 1 * B + Cm * 1 * B + Cm * 1 * 1 * (B + 1 * Δ + 1 * B) := by gcongr
      _ = _ := by dsimp only [Cu, B]; ring
  have hU : U ≤ Cu * Δ := by
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hCu.le hΔ)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmB
  have hcost : (84 * G + 16 * U) * (4096 * A + 544 * sigma e M T) * ε ^ 2 ≤ D * Δ := by
    have hc : 84 * G + 16 * U ≤ (84 * C₀ + 16 * Cu) * Δ := by
      have hh := add_le_add (mul_le_mul_of_nonneg_left hG (by norm_num : (0 : ℝ) ≤ 84))
        (mul_le_mul_of_nonneg_left hU (by norm_num : (0 : ℝ) ≤ 16))
      simpa only [B, add_mul, mul_assoc] using hh
    have hr : 4096 * A + 544 * sigma e M T ≤ R := by
      dsimp only [R]
      linarith only [hσ1]
    calc
      _ ≤ ((84 * C₀ + 16 * Cu) * Δ) * R * 1 := by gcongr
      _ = _ := by dsimp only [D]; ring
  let Wo := ⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal
    (S₁.lam u v / S₁.r u v * |S₁.mu u v - S₂.mu u v|)
  let Wi := ⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal
    (-S₁.nu u v / S₁.r u v * |S₁.mu u v - S₂.mu u v|)
  let Eo := ⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal
    (S₁.lam u v / S₁.r u v * |S₁.Q u v ^ 2 / S₁.r u v ^ 2 - S₂.Q u v ^ 2 / S₂.r u v ^ 2|)
  let Ei := ⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal
    (-S₁.nu u v / S₁.r u v * |S₁.Q u v ^ 2 / S₁.r u v ^ 2 - S₂.Q u v ^ 2 / S₂.r u v ^ 2|)
  have hW : Wo + Wi ≤ ENNReal.ofReal (Cw * Δ) :=
    hWeighted T e ε M S₁ S₂ h₁ h₂ h₁s h₂s (hsmall.trans (min_le_left _ _)) hmain
  have ho : Eo ≤ ENNReal.ofReal (Co * sigma e M T * ε * H) :=
    hOut T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hi : Ei ≤ ENNReal.ofReal (Ci * sigma e M T * ε * H) :=
    hIn T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
      (hsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))))
  have hE : Eo + Ei ≤ ENNReal.ofReal ((Co + Ci) * (2 * C₀ + 1) * Δ) := by
    apply (add_le_add ho hi).trans
    rw [← ENNReal.ofReal_add (by dsimp only [H, J, G]; positivity)
      (by dsimp only [H, J, G]; positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = (Co + Ci) * sigma e M T * ε * H := by ring
      _ ≤ (Co + Ci) * 1 * 1 * ((2 * C₀ + 1) * Δ) := by gcongr
      _ = _ := by ring
  have hOut : (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
      ‖pdV (triangle 0 T) S₁.nu u v - pdV (triangle 0 T) S₂.nu u v‖ₑ) ≤
        4 * Wo + 4 * Eo + ENNReal.ofReal (D * Δ) := by
    apply iSup₂_le
    intro u hu
    have hn : ∀ᵐ v : ℝ, v ≠ u := by simp [ae_iff, measure_singleton]
    have heq : (∫⁻ v in Icc u T,
        ‖pdV (triangle 0 T) S₁.nu u v - pdV (triangle 0 T) S₂.nu u v‖ₑ) =
        ∫⁻ v in Icc u T, ENNReal.ofReal |S₁.rUV u v - S₂.rUV u v| := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn] with v hv hne
      have hp : (u, v) ∈ triangle 0 T := ⟨hu.1, hv.1, hv.2⟩
      have huv := lt_of_le_of_ne hv.1 hne.symm
      rw [(h₁s.c1.eq_v _ hp huv).2.1, (h₂s.c1.eq_v _ hp huv).2.1,
        ← ofReal_norm, Real.norm_eq_abs]
    rw [heq]
    apply (stab_out_cross_source_integral_c1 hA h₁s h₂s hεsq hu).trans
    exact add_le_add (add_le_add
      (mul_le_mul' le_rfl (le_iSup₂_of_le u hu le_rfl))
      (mul_le_mul' le_rfl (le_iSup₂_of_le u hu le_rfl)))
      (ENNReal.ofReal_le_ofReal hcost)
  have hIn : (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖pdU (triangle 0 T) S₁.lam u v - pdU (triangle 0 T) S₂.lam u v‖ₑ) ≤
        4 * Wi + 4 * Ei + ENNReal.ofReal (D * Δ) := by
    apply iSup₂_le
    intro v hv
    have hn : ∀ᵐ u : ℝ, u ≠ v := by simp [ae_iff, measure_singleton]
    have heq : (∫⁻ u in Icc 0 v,
        ‖pdU (triangle 0 T) S₁.lam u v - pdU (triangle 0 T) S₂.lam u v‖ₑ) =
        ∫⁻ u in Icc 0 v, ENNReal.ofReal |S₁.rUV u v - S₂.rUV u v| := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn] with u hu hne
      have hp : (u, v) ∈ triangle 0 T := ⟨hu.1, hu.2, hv.2⟩
      have huv := lt_of_le_of_ne hu.2 hne
      rw [(h₁s.c1.eq_u _ hp huv).2.1, (h₂s.c1.eq_u _ hp huv).2.1,
        ← ofReal_norm, Real.norm_eq_abs]
    rw [heq]
    apply (stab_in_cross_source_integral_c1 hA h₁s h₂s hεsq hv).trans
    exact add_le_add (add_le_add
      (mul_le_mul' le_rfl (le_iSup₂_of_le v hv le_rfl))
      (mul_le_mul' le_rfl (le_iSup₂_of_le v hv le_rfl)))
      (ENNReal.ofReal_le_ofReal hcost)
  apply (add_le_add hOut hIn).trans
  calc
    _ = 4 * (Wo + Wi) + 4 * (Eo + Ei) +
        (ENNReal.ofReal (D * Δ) + ENNReal.ofReal (D * Δ)) := by ring
    _ ≤ 4 * ENNReal.ofReal (Cw * Δ) +
        4 * ENNReal.ofReal ((Co + Ci) * (2 * C₀ + 1) * Δ) +
        (ENNReal.ofReal (D * Δ) + ENNReal.ofReal (D * Δ)) :=
      add_le_add (add_le_add (mul_le_mul' le_rfl hW) (mul_le_mul' le_rfl hE)) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat 4,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      dsimp only [C]
      ring

end EmcsfAcExtension.Local
