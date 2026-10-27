module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.DifferenceMomentsIncomingRaw
import EmcsfAcExtension.Local.Stability.DifferenceMomentsIncomingComparison
import EmcsfAcExtension.Local.Stability.DifferenceMomentsIncomingConvolution
import EmcsfAcExtension.Local.Stability.DifferenceMomentsIncomingForcing
import EmcsfAcExtension.Local.Stability.DifferenceMomentsDensity
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Incoming moment of the difference before absorption

The exact cubic monotonicity argument and the separated `1/2`, `3/4`
kernels give the approved internal project record label density. The mass-ratio feedback
remains explicit; this theorem performs no coupled absorption.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-bv-stability-independent#incoming-difference-moment-before-absorption]
The incoming difference moment before absorption, charged_SF_new_version.tex:L5205–5205
and approved internal project record (I). The constant is universal, independent of
`A,T,e,ε,M`, the pair, data, derivative suprema and minimum radius. -/
theorem Stab.incoming_difference_moment_before_absorption : ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M A : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      3 * ε ^ 2 ≤ 1 / 2 →
      ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
        ENNReal.ofReal ‖S₁.xi u v / (S₁.nu u v : ℂ) -
          S₂.xi u v / (S₂.nu u v : ℂ)‖ ≤
        ENNReal.ofReal C * ∫⁻ s in Icc u v,
          ENNReal.ofReal ((S₁.r s v / S₁.r u v) ^ (1 / 2 : ℝ)) *
            (inEnv T (fun u v => kC1 e (triangle 0 T) S₁ u v -
              kC1 e (triangle 0 T) S₂ u v) s +
            ENNReal.ofReal ((geomDist T S₁ S₂).toReal +
              T * |e| * (supDist T S₁.A S₂.A).toReal + (supDist T S₁.mu S₂.mu).toReal) *
                inEnv T (kC1 e (triangle 0 T) S₂) s) := by
  refine ⟨8192, by norm_num, ?_⟩
  intro T e ε M A S₁ S₂ h₁ h₂ h₁s h₂s hε u v hu huv hvT
  let G := ENNReal.ofReal ((geomDist T S₁ S₂).toReal +
    T * |e| * (supDist T S₁.A S₂.A).toReal)
  let U := ENNReal.ofReal (supDist T S₁.mu S₂.mu).toReal
  let J := inEnv T (kC1 e (triangle 0 T) S₂)
  let D := inEnv T (fun u v => kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v)
  let K := fun t => ENNReal.ofReal ((S₁.r t v / S₁.r u v) ^ (1 / 2 : ℝ))
  let B := fun t => ENNReal.ofReal (-S₁.nu t v / S₁.r t v)
  let X := fun t => ENNReal.ofReal ‖S₂.xi t v / (S₂.nu t v : ℂ)‖
  let Z := fun t => ∫⁻ s in Icc t v,
    ENNReal.ofReal ((S₁.r s v / S₁.r t v) ^ (3 / 4 : ℝ)) * J s
  let q := fun t : ℝ =>
    kC1 e (triangle 0 T) S₁ t v / ((1 - S₁.mu t v : ℝ) : ℂ) -
    kC1 e (triangle 0 T) S₂ t v / ((1 - S₂.mu t v : ℝ) : ℂ) -
    (S₁.nu t v / S₁.r t v - S₂.nu t v / S₂.r t v) •
      (S₂.xi t v / (S₂.nu t v : ℂ) -
        ‖S₂.xi t v / (S₂.nu t v : ℂ)‖ ^ 2 • (S₂.xi t v / (S₂.nu t v : ℂ))) -
    (e * (S₁.A t v - S₂.A t v)) • (Complex.I * (S₂.xi t v / (S₂.nu t v : ℂ)))
  let Q := fun t => ENNReal.ofReal ‖q t‖
  rw [ENNReal.ofReal_add (add_nonneg ENNReal.toReal_nonneg
    (mul_nonneg (mul_nonneg h₁s.pos.le (abs_nonneg e)) ENNReal.toReal_nonneg))
    ENNReal.toReal_nonneg]
  norm_num only [ENNReal.ofReal_ofNat]
  change ENNReal.ofReal ‖S₁.xi u v / (S₁.nu u v : ℂ) -
      S₂.xi u v / (S₂.nu u v : ℂ)‖ ≤ 8192 * ∫⁻ t in Icc u v, K t * (D t + (G + U) * J t)
  have hε1 : ε ≤ 1 := by nlinarith only [hε, sq_nonneg (ε - 1)]
  have hεq : ε ^ 2 ≤ 1 / 4 := by linarith only [hε]
  have hmap : MapsTo (fun t : ℝ => (t, v)) (Icc u v) (triangle 0 T) :=
    fun t ht => ⟨hu.trans ht.1, ht.2, hvT⟩
  have cR := h₁s.c1.c1_r.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cK : ContinuousOn K (Icc u v) := ENNReal.continuous_ofReal.comp_continuousOn
    ((cR.div_const (S₁.r u v)).rpow_const
      (fun t ht => Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 2)))
  have cJ : ContinuousOn J (Icc u v) :=
    (continuousOn_inEnv (continuousOn_kC1_aux h₂s.pos h₂s.c1)).mono
      (Icc_subset_Icc hu hvT)
  have cD : ContinuousOn D (Icc u v) :=
    (continuousOn_inEnv ((continuousOn_kC1_aux h₁s.pos h₁s.c1).sub
      (continuousOn_kC1_aux h₂s.pos h₂s.c1))).mono (Icc_subset_Icc hu hvT)
  have hKD : AEMeasurable (fun t => K t * D t) (volume.restrict (Icc u v)) :=
    (cK.aemeasurable measurableSet_Icc).mul (cD.aemeasurable measurableSet_Icc)
  have hKJ : AEMeasurable (fun t => K t * J t) (volume.restrict (Icc u v)) :=
    (cK.aemeasurable measurableSet_Icc).mul (cJ.aemeasurable measurableSet_Icc)
  have hne : ∀ᵐ t : ℝ, t ≠ v := by simp [ae_iff, measure_singleton]
  have hforce : ∀ᵐ t ∂volume.restrict (Icc u v),
      Q t ≤ 4 * D t + 16 * U * J t + 20 * G * B t * X t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with t ht htu
    have htv : t < v := lt_of_le_of_ne ht.2 htu
    exact stab_in_difference_forcing_enorm_le h₁s h₂s hε1 (hu.trans ht.1) htv hvT
  have hind : ∀ᵐ t ∂volume.restrict (Icc u v), X t ≤ 64 * Z t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with t ht htu
    have htv : t < v := lt_of_le_of_ne ht.2 htu
    simpa only [X, Z, J, ENNReal.ofReal_ofNat] using
      stab_in_moment_common_radius h₁s h₂s hεq (hu.trans ht.1) htv hvT
  have hconv : (∫⁻ t in Icc u v, K t * B t * Z t) ≤
      4 * ∫⁻ t in Icc u v, K t * J t := by
    have heq : (∫⁻ t in Icc u v, K t * B t * Z t) =
        ∫⁻ t in Icc u v,
          ENNReal.ofReal ((S₁.r t v / S₁.r u v) ^ (1 / 2 : ℝ) * (-S₁.nu t v / S₁.r t v)) *
            Z t := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only [K, B]
      have hr := (stab_radius_bounds h₁s (hu.trans ht.1) ht.2 hvT).1
      have hr0 : 0 ≤ S₁.r t v := by linarith only [hr, ht.2]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (div_nonneg hr0
        (h₁s.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv).le) (1 / 2 : ℝ))]
    rw [heq]
    simpa only [K, Z, J, ENNReal.ofReal_ofNat] using
      stab_in_separated_moment_convolution h₁s h₂s hu huv hvT
  have hdensity := stab_difference_density_of_moment_bounds
    (show G ≠ ⊤ from ENNReal.ofReal_ne_top) (show U ≠ ⊤ from ENNReal.ofReal_ne_top)
    hKD hKJ hforce hind hconv
  have hraw := stab_in_difference_moment_raw h₁s h₂s hε hu huv hvT
  apply hraw.trans
  calc
    _ = ∫⁻ t in Icc u v, K t * Q t := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      dsimp only [K, Q]
      have hr := (stab_radius_bounds h₁s (hu.trans ht.1) ht.2 hvT).1
      have hr0 : 0 ≤ S₁.r t v := by linarith only [hr, ht.2]
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (div_nonneg hr0
        (h₁s.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv).le) (1 / 2 : ℝ))]
    _ ≤ _ := hdensity

end EmcsfAcExtension.Local
