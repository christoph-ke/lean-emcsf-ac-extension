module

public import EmcsfAcExtension.Local.Stability.W11Comparison
import EmcsfAcExtension.Local.Stability.W11Algebra
import EmcsfAcExtension.Local.Stability.PotentialC1
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Stability.DifferenceMomentsIncomingForcing
import EmcsfAcExtension.Local.Calculus.Normalized
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Ordinary incoming scalar derivative differences

Subtracting the two own connections produces both `δA b₁` and `A₂ δb`.
The first is estimated with the background-weighted phase bound, and
the second with the individual zero-axis potential primitive.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem sup_norm_sub_aux {E : Type*} [NormedAddCommGroup E]
    {T B : ℝ} {f g : ℝ → ℝ → E} {u v : ℝ}
    (hB : 0 ≤ B) (h : supDist T f g ≤ ENNReal.ofReal B)
    (hp : (u, v) ∈ triangle 0 T) : ‖f u v - g u v‖ ≤ B := by
  have hh : ‖f u v - g u v‖ₑ ≤ ENNReal.ofReal B :=
    (le_iSup₂_of_le (u, v) hp le_rfl).trans h
  rw [← ofReal_norm] at hh
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hh

/-- [internal]
Ordinary characteristic derivative comparison from the full main Lipschitz
conclusion, with no variation or strong-derivative premise. Constants depend
only on `A` and its uniform main constant `C₀`, before every datum, pair,
coupling, background, time and minimum radius. Both connection errors are
retained, including the factor `M` multiplying the potential difference. -/
theorem Stab.ordinary_incoming_difference_variation_of_main_lipschitz
    (A C₀ : ℝ) (hA : 0 < A) (hC₀ : 0 < C₀) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ +
          supDist T S₁.a S₂.a + supDist T S₁.b S₂.b + supDist T S₁.phi S₂.phi ≤
            ENNReal.ofReal (C₀ * dataDist h₁ h₂ T) →
        (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
          ‖pdV (triangle 0 T) S₁.a u v - pdV (triangle 0 T) S₂.a u v‖ₑ) +
        (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
          ‖pdU (triangle 0 T) S₁.b u v - pdU (triangle 0 T) S₂.b u v‖ₑ) ≤
          ENNReal.ofReal (C * dataDist h₁ h₂ T) := by
  obtain ⟨ηv, Cv, hηv, hCv, hVar⟩ :=
    Stab.characteristic_variation_difference_of_main_lipschitz A C₀ hA hC₀
  obtain ⟨ηp, Cp, hηp, hCp, hPhase⟩ := stab_potential_background_phase_bounds A hA
  let Cextra := 2 * Cp * (2 * C₀ + 1) + 32 * C₀
  have hCextra : 0 < Cextra := by dsimp only [Cextra]; positivity
  refine ⟨min ηv (min ηp (1 / 4)), Cv + Cextra,
    lt_min hηv (lt_min hηp (by norm_num)), add_pos hCv hCextra, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hmain
  let Δ := dataDist h₁ h₂ T
  let B := C₀ * Δ
  let Ad := (supDist T S₁.A S₂.A).toReal
  let D := |e| * (Ad * (2 * M) + (8 * |e| * M * ε * T) * B)
  let H := (jDist T S₁ S₂).toReal + ε * Δ + ε * (geomDist T S₁ S₂).toReal
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hB : 0 ≤ B := mul_nonneg hC₀.le hΔ
  have hT : 0 < T := h₁s.pos
  have hM1 : 1 ≤ M := h₁s.box.1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) hM1
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, hT.le⟩).2.2.2.2.2.1)
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hsize : ε ^ 2 + sigma e M T ≤ 1 / 4 :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := by nlinarith only [hsize, hσ, sq_nonneg (ε - 1)]
  have hσ1 : sigma e M T ≤ 1 := by linarith only [hsize, sq_nonneg ε]
  have hD : 0 ≤ D := by dsimp only [D, Ad]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have htriple : jDist T S₁ S₂ + kDist e T S₁ S₂ + geomDist T S₁ S₂ ≤ ENNReal.ofReal B := by
    apply le_trans ?_ hmain
    exact (le_add_of_nonneg_right bot_le).trans
      ((le_add_of_nonneg_right bot_le).trans (le_add_of_nonneg_right bot_le))
  have hbDist : supDist T S₁.b S₂.b ≤ ENNReal.ofReal B := by
    apply le_trans ?_ hmain
    exact (le_add_of_nonneg_left bot_le).trans (le_add_of_nonneg_right bot_le)
  have hJD : jDist T S₁ S₂ ≤ ENNReal.ofReal B :=
    (le_add_of_nonneg_right bot_le).trans ((le_add_of_nonneg_right bot_le).trans htriple)
  have hGD : geomDist T S₁ S₂ ≤ ENNReal.ofReal B := (le_add_of_nonneg_left bot_le).trans htriple
  have hJ : (jDist T S₁ S₂).toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hJD
  have hG : (geomDist T S₁ S₂).toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hGD
  have hHb : H ≤ 2 * B + Δ := by
    calc
      _ ≤ B + 1 * Δ + 1 * B := by dsimp only [H]; gcongr
      _ = _ := by ring
  have hp := hPhase T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hMM : M ≤ M ^ 2 := by nlinarith only [hM1]
  have hscale : 8 * |e| ^ 2 * M * T ^ 2 ≤ 32 * sigma e M T := by
    have hh := mul_le_mul_of_nonneg_left hMM
      (show 0 ≤ e ^ 2 * T ^ 2 by positivity)
    dsimp only [sigma]
    rw [sq_abs]
    nlinarith only [hh]
  have hTD : T * D ≤ Cextra * Δ := by
    calc
      _ = 2 * (M * T * |e| * Ad) + (8 * |e| ^ 2 * M * T ^ 2) * ε * B := by
        dsimp only [D]; ring
      _ ≤ 2 * (Cp * sigma e M T * H) + (32 * sigma e M T) * ε * B := by
        exact add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num))
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hscale hε) hB)
      _ ≤ 2 * (Cp * 1 * (2 * B + Δ)) + (32 * 1) * 1 * B := by gcongr
      _ = _ := by dsimp only [B, Cextra]; ring
  have hvar := hVar T e ε M S₁ S₂ h₁ h₂ h₁s h₂s
    (hsmall.trans (min_le_left _ _)) htriple
  let Cov := fun u v =>
    (pdU (triangle 0 T) S₁.b u v + Complex.I * e * S₁.A u v * S₁.b u v) -
    (pdU (triangle 0 T) S₂.b u v + Complex.I * e * S₂.A u v * S₂.b u v)
  have hpoint : ∀ u v, (u, v) ∈ triangle 0 T →
      ‖pdU (triangle 0 T) S₁.b u v - pdU (triangle 0 T) S₂.b u v‖ ≤ ‖Cov u v‖ + D := by
    intro u v hpT
    have ha : |S₁.A u v - S₂.A u v| ≤ Ad := by
      have hh : ‖S₁.A u v - S₂.A u v‖ₑ ≤ supDist T S₁.A S₂.A :=
        le_iSup₂_of_le (u, v) hpT le_rfl
      rw [← ofReal_norm, Real.norm_eq_abs] at hh
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using
        ENNReal.toReal_mono (stab_potentialDist_ne_top h₁s h₂s) hh
    have hb : ‖S₁.b u v‖ ≤ 2 * M := by
      have hh := norm_add_le (S₁.phi u v) (S₁.xi u v / (S₁.nu u v : ℂ))
      have hphi := (h₁s.box.2 (u, v) hpT).2.2.2.2.2.2
      have hy := (le_add_of_nonneg_left (norm_nonneg (S₁.theta u v / (S₁.lam u v : ℂ)))).trans
        (h₁s.box.2 (u, v) hpT).2.2.2.2.2.1
      change ‖S₁.phi u v + S₁.xi u v / (S₁.nu u v : ℂ)‖ ≤ _
      linarith only [hh, hphi, hy, hε1, hM1]
    have hA2 : |S₂.A u v| ≤ 8 * |e| * M * ε * T :=
      (Stab.potential_bound_c1 h₂s hpT.1 hpT.2.1 hpT.2.2).trans
        (mul_le_mul_of_nonneg_left (by linarith only [hpT.1, hpT.2.2] : v - u ≤ T)
          (by positivity))
    have hbd := sup_norm_sub_aux hB hbDist hpT
    apply (stab_ordinary_incoming_derivative_sub_le (triangle 0 T) S₁ S₂ e u v).trans
    apply add_le_add le_rfl
    dsimp only [D]
    exact mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul ha hb (norm_nonneg _) (by positivity))
        (mul_le_mul hA2 hbd (norm_nonneg _) (by positivity))) (abs_nonneg e)
  have hIn : (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖pdU (triangle 0 T) S₁.b u v - pdU (triangle 0 T) S₂.b u v‖ₑ) ≤
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ‖Cov u v‖ₑ) + ENNReal.ofReal (Cextra * Δ) := by
    apply iSup₂_le
    intro v hv
    have hmap : MapsTo (fun u : ℝ => (u, v)) (Icc 0 v) (triangle 0 T) :=
      fun u hu => ⟨hu.1, hu.2, hv.2⟩
    have cP₁ := continuousOn_partial_u (stab_normalized_in_c1 h₁s.c1)
      (uniqueDiffOn_triangle hT)
    have cP₂ := continuousOn_partial_u (stab_normalized_in_c1 h₂s.c1)
      (uniqueDiffOn_triangle hT)
    have cCov : ContinuousOn (Function.uncurry Cov) (triangle 0 T) := by
      exact (cP₁.add (((continuousOn_const (c := Complex.I * (e : ℂ))).mul
        (Complex.continuous_ofReal.comp_continuousOn h₁s.c1.c1_A.continuousOn)).mul
          (stab_normalized_in_c1 h₁s.c1).continuousOn)).sub
        (cP₂.add (((continuousOn_const (c := Complex.I * (e : ℂ))).mul
          (Complex.continuous_ofReal.comp_continuousOn h₂s.c1.c1_A.continuousOn)).mul
            (stab_normalized_in_c1 h₂s.c1).continuousOn))
    have hm : AEMeasurable (fun u => ‖Cov u v‖ₑ) (volume.restrict (Icc 0 v)) :=
      (cCov.comp (continuous_id.prodMk continuous_const).continuousOn hmap).enorm.aemeasurable
        measurableSet_Icc
    calc
      _ ≤ ∫⁻ u in Icc 0 v, ‖Cov u v‖ₑ + ENNReal.ofReal D := by
        apply setLIntegral_mono' measurableSet_Icc
        intro u hu
        rw [← ofReal_norm]
        apply (ENNReal.ofReal_le_ofReal (hpoint u v (hmap hu))).trans_eq
        rw [ENNReal.ofReal_add (norm_nonneg (Cov u v)) hD, ofReal_norm]
      _ = (∫⁻ u in Icc 0 v, ‖Cov u v‖ₑ) + ENNReal.ofReal (v * D) := by
        rw [lintegral_add_left' hm, lintegral_const, Measure.restrict_apply_univ,
          Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul hD]
        congr 2
        ring
      _ ≤ _ := add_le_add (le_iSup₂_of_le v hv le_rfl)
        (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right hv.2 hD).trans hTD))
  apply (add_le_add le_rfl hIn).trans
  rw [← add_assoc]
  apply (add_le_add hvar le_rfl).trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end EmcsfAcExtension.Local
