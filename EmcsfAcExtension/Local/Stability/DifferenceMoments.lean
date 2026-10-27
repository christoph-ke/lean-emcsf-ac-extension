module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.DifferenceMomentsRaw
import EmcsfAcExtension.Local.Stability.DifferenceMomentsComparison
import EmcsfAcExtension.Local.Stability.DifferenceMomentsConvolution
import EmcsfAcExtension.Local.Stability.DifferenceMomentsFieldForcing
import EmcsfAcExtension.Local.Stability.DifferenceMomentsDensity
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Outgoing moment of the difference before absorption

The exact cubic monotonicity argument and the separated `1/2`, `3/4`
kernels give the approved internal project record label density. The mass-ratio feedback
remains explicit; this theorem performs no coupled absorption.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-bv-stability-independent#outgoing-difference-moment-before-absorption]
The outgoing difference moment before absorption, charged_SF_new_version.tex:L5116–5200
and approved internal project record (O). The constant is universal, independent of
`A,T,e,ε,M`, the pair, data, derivative suprema and minimum radius. -/
theorem Stab.outgoing_difference_moment_before_absorption : ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M A : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      3 * ε ^ 2 ≤ 1 / 2 →
      ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
        ENNReal.ofReal ‖S₁.theta u v / (S₁.lam u v : ℂ) -
          S₂.theta u v / (S₂.lam u v : ℂ)‖ ≤
        ENNReal.ofReal C * ∫⁻ s in Icc u v,
          ENNReal.ofReal ((S₁.r u s / S₁.r u v) ^ (1 / 2 : ℝ)) *
            (outEnv 0 (fun u v => jC1 (triangle 0 T) S₁ u v -
              jC1 (triangle 0 T) S₂ u v) s +
            ENNReal.ofReal ((geomDist T S₁ S₂).toReal +
              (supDist T S₁.mu S₂.mu).toReal) * outEnv 0 (jC1 (triangle 0 T) S₂) s) := by
  refine ⟨8192, by norm_num, ?_⟩
  intro T e ε M A S₁ S₂ h₁ h₂ h₁s h₂s hε u v hu huv hvT
  let G := ENNReal.ofReal (geomDist T S₁ S₂).toReal
  let U := ENNReal.ofReal (supDist T S₁.mu S₂.mu).toReal
  let J := outEnv 0 (jC1 (triangle 0 T) S₂)
  let D := outEnv 0 (fun u v => jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v)
  let K := fun t => ENNReal.ofReal ((S₁.r u t / S₁.r u v) ^ (1 / 2 : ℝ))
  let B := fun t => ENNReal.ofReal (S₁.lam u t / S₁.r u t)
  let X := fun t => ENNReal.ofReal ‖S₂.theta u t / (S₂.lam u t : ℂ)‖
  let Z := fun t => ∫⁻ s in Icc u t,
    ENNReal.ofReal ((S₁.r u s / S₁.r u t) ^ (3 / 4 : ℝ)) * J s
  let q := fun t : ℝ =>
    jC1 (triangle 0 T) S₁ u t / ((1 - S₁.mu u t : ℝ) : ℂ) -
    jC1 (triangle 0 T) S₂ u t / ((1 - S₂.mu u t : ℝ) : ℂ) -
    (S₁.lam u t / S₁.r u t - S₂.lam u t / S₂.r u t) •
      (S₂.theta u t / (S₂.lam u t : ℂ) -
        ‖S₂.theta u t / (S₂.lam u t : ℂ)‖ ^ 2 • (S₂.theta u t / (S₂.lam u t : ℂ)))
  let Q := fun t => ENNReal.ofReal ‖q t‖
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
  norm_num only [ENNReal.ofReal_ofNat]
  change ENNReal.ofReal ‖S₁.theta u v / (S₁.lam u v : ℂ) -
      S₂.theta u v / (S₂.lam u v : ℂ)‖ ≤ 8192 * ∫⁻ t in Icc u v, K t * (D t + (G + U) * J t)
  have hε1 : ε ≤ 1 := by nlinarith only [hε, sq_nonneg (ε - 1)]
  have hεq : ε ^ 2 ≤ 1 / 4 := by linarith only [hε]
  have hmap : MapsTo (fun t : ℝ => (u, t)) (Icc u v) (triangle 0 T) :=
    fun t ht => ⟨hu, ht.1, ht.2.trans hvT⟩
  have cR := h₁s.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cK : ContinuousOn K (Icc u v) := ENNReal.continuous_ofReal.comp_continuousOn
    ((cR.div_const (S₁.r u v)).rpow_const
      (fun t ht => Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 2)))
  have cJ : ContinuousOn J (Icc u v) :=
    (continuousOn_outEnv (continuousOn_jC1_aux h₂s.pos h₂s.c1)).mono
      (Icc_subset_Icc hu hvT)
  have cD : ContinuousOn D (Icc u v) :=
    (continuousOn_outEnv ((continuousOn_jC1_aux h₁s.pos h₁s.c1).sub
      (continuousOn_jC1_aux h₂s.pos h₂s.c1))).mono (Icc_subset_Icc hu hvT)
  have hKD : AEMeasurable (fun t => K t * D t) (volume.restrict (Icc u v)) :=
    (cK.aemeasurable measurableSet_Icc).mul (cD.aemeasurable measurableSet_Icc)
  have hKJ : AEMeasurable (fun t => K t * J t) (volume.restrict (Icc u v)) :=
    (cK.aemeasurable measurableSet_Icc).mul (cJ.aemeasurable measurableSet_Icc)
  have hne : ∀ᵐ t : ℝ, t ≠ u := by simp [ae_iff, measure_singleton]
  have hforce : ∀ᵐ t ∂volume.restrict (Icc u v),
      Q t ≤ 4 * D t + 16 * U * J t + 20 * G * B t * X t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with t ht htu
    have hut : u < t := lt_of_le_of_ne ht.1 htu.symm
    exact stab_out_difference_forcing_enorm_le h₁s h₂s hε1 hu hut (ht.2.trans hvT)
  have hind : ∀ᵐ t ∂volume.restrict (Icc u v), X t ≤ 64 * Z t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with t ht htu
    have hut : u < t := lt_of_le_of_ne ht.1 htu.symm
    simpa only [X, Z, J, ENNReal.ofReal_ofNat] using
      stab_out_moment_common_radius h₁s h₂s hεq hu hut (ht.2.trans hvT)
  have hconv : (∫⁻ t in Icc u v, K t * B t * Z t) ≤
      4 * ∫⁻ t in Icc u v, K t * J t := by
    have heq : (∫⁻ t in Icc u v, K t * B t * Z t) =
        ∫⁻ t in Icc u v,
          ENNReal.ofReal ((S₁.r u t / S₁.r u v) ^ (1 / 2 : ℝ) * (S₁.lam u t / S₁.r u t)) *
            Z t := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only [K, B]
      have hr := (stab_radius_bounds h₁s hu ht.1 (ht.2.trans hvT)).1
      have hr0 : 0 ≤ S₁.r u t := by linarith only [hr, ht.1]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (div_nonneg hr0
        (h₁s.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv).le) (1 / 2 : ℝ))]
    rw [heq]
    simpa only [K, Z, J, ENNReal.ofReal_ofNat] using
      stab_out_separated_moment_convolution h₁s h₂s hu huv hvT
  have hdensity := stab_difference_density_of_moment_bounds
    (show G ≠ ⊤ from ENNReal.ofReal_ne_top) (show U ≠ ⊤ from ENNReal.ofReal_ne_top)
    hKD hKJ hforce hind hconv
  have hraw := stab_out_difference_moment_raw h₁s h₂s hε hu huv hvT
  apply hraw.trans
  calc
    _ = ∫⁻ t in Ioc u v, K t * Q t := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro t ht
      dsimp only [K, Q]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg
        (div_nonneg (h₁s.c1.r_pos (u, t) ⟨hu, ht.1.le, ht.2.trans hvT⟩ ht.1).le
          (h₁s.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv).le) (1 / 2 : ℝ))]
    _ ≤ ∫⁻ t in Icc u v, K t * Q t := lintegral_mono_set
      (show Ioc u v ⊆ Icc u v from fun t ht => ⟨ht.1.le, ht.2⟩)
    _ ≤ _ := hdensity

end EmcsfAcExtension.Local
