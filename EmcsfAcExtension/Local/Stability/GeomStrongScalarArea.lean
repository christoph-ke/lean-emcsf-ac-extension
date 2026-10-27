module

public import EmcsfAcExtension.Local.Stability.GeomStrongScalarPrimitive
import EmcsfAcExtension.Local.Stability.GeomStrongScalarDifference
import EmcsfAcExtension.Local.Stability.GeomStrongOrderedArea
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Unabsorbed area comparison of the geometric scalar source

The four ordered primitives have finite area costs in the actual
renormalized label norms. Mass and phase feedback remain explicit.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The scalar contribution to the geometric-source difference has
area cost `C[ε(Δj+Δk)+ε²(G+U+P)]`. The constant depends only on `A`
and the literal box before all field, coupling, scale and data parameters,
independently of derivative suprema and the minimum radius.
-/
theorem stab_geometric_scalar_area_difference_c1 (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      3 * ε ^ 2 ≤ 1 / 2 →
      (∫⁻ q in triangle 0 T, ‖geometricScalarSource (triangle 0 T) S₁ q.1 q.2 -
        geometricScalarSource (triangle 0 T) S₂ q.1 q.2‖ₑ) ≤
      ENNReal.ofReal (C * (ε * ((jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal) +
        ε ^ 2 * ((geomDist T S₁ S₂).toReal +
          T * |e| * (supDist T S₁.A S₂.A).toReal + (supDist T S₁.mu S₂.mu).toReal))) := by
  obtain ⟨B, hB, hPoint⟩ := stab_geometric_scalar_difference_ordered_c1
  let C := 65536 * A ^ 2 + 1024 * B * A + 1024 * B * A ^ 2 + 4096 * A
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hε
  let G := (geomDist T S₁ S₂).toReal
  let U := (supDist T S₁.mu S₂.mu).toReal
  let P := T * |e| * (supDist T S₁.A S₂.A).toReal
  let F := G + P + U
  let J := (jDist T S₁ S₂).toReal
  let K := (kDist e T S₁ S₂).toReal
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hU : 0 ≤ U := ENNReal.toReal_nonneg
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg h₁s.pos.le (abs_nonneg e)) ENNReal.toReal_nonneg
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hJ : 0 ≤ J := ENNReal.toReal_nonneg
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  let K₁ := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S₁))
  let K₂ := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S₂))
  let J₂ := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S₂))
  let DK := (Icc 0 T).indicator (inEnv T
    (fun u v => kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v))
  let DJ := (Icc 0 T).indicator (outEnv 0
    (fun u v => jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v))
  let KF := fun s => DK s + ENNReal.ofReal F * K₂ s
  have cDeltaK : ContinuousOn (Function.uncurry
      (fun u v => kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v))
      (triangle 0 T) := by
    simpa only [Function.uncurry_def, Pi.sub_apply] using!
      (continuousOn_kC1_aux h₁s.pos h₁s.c1).sub (continuousOn_kC1_aux h₂s.pos h₂s.c1)
  have cDeltaJ : ContinuousOn (Function.uncurry
      (fun u v => jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v))
      (triangle 0 T) := by
    simpa only [Function.uncurry_def, Pi.sub_apply] using!
      (continuousOn_jC1_aux h₁s.pos h₁s.c1).sub (continuousOn_jC1_aux h₂s.pos h₂s.c1)
  have mK₁ : Measurable K₁ := by
    dsimp only [K₁]
    rw [← Set.piecewise_eq_indicator]
    exact (continuousOn_inEnv (continuousOn_kC1_aux h₁s.pos h₁s.c1)).measurable_piecewise
        continuousOn_const measurableSet_Icc
  have mK₂ : Measurable K₂ := by
    dsimp only [K₂]
    rw [← Set.piecewise_eq_indicator]
    exact (continuousOn_inEnv (continuousOn_kC1_aux h₂s.pos h₂s.c1)).measurable_piecewise
        continuousOn_const measurableSet_Icc
  have mJ₂ : Measurable J₂ := by
    dsimp only [J₂]
    rw [← Set.piecewise_eq_indicator]
    exact (continuousOn_outEnv (continuousOn_jC1_aux h₂s.pos h₂s.c1)).measurable_piecewise
        continuousOn_const measurableSet_Icc
  have mDK : Measurable DK := by
    dsimp only [DK]
    rw [← Set.piecewise_eq_indicator]
    exact (continuousOn_inEnv cDeltaK).measurable_piecewise continuousOn_const measurableSet_Icc
  have mDJ : Measurable DJ := by
    dsimp only [DJ]
    rw [← Set.piecewise_eq_indicator]
    exact (continuousOn_outEnv cDeltaJ).measurable_piecewise continuousOn_const measurableSet_Icc
  have mKF : Measurable KF := mDK.add (measurable_const.mul mK₂)
  have hb := stab_four_ordered_area_of_bound mK₁ mK₂ mKF mJ₂ mDJ
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    (F := fun q : ℝ × ℝ => ‖geometricScalarSource (triangle 0 T) S₁ q.1 q.2 -
      geometricScalarSource (triangle 0 T) S₂ q.1 q.2‖ₑ)
    (a := ENNReal.ofReal (4096 * (G + U) * 4 * 1))
    (b := ENNReal.ofReal (512 * 4 * (4 * G)))
    (c := ENNReal.ofReal (512 * B * 1)) (d := ENNReal.ofReal (512 * 4 * 1)) (by
      intro q hq
      rcases hq.2.1.eq_or_lt with heq | hlt
      · have hr₁ : S₁.r q.1 q.2 = 0 := by
          rw [← heq]
          exact (h₁s.c1.axis q.1 ⟨hq.1, le_rfl, heq.le.trans hq.2.2⟩).1
        have hr₂ : S₂.r q.1 q.2 = 0 := by
          rw [← heq]
          exact (h₂s.c1.axis q.1 ⟨hq.1, le_rfl, heq.le.trans hq.2.2⟩).1
        simp only [geometricScalarSource, hr₁, hr₂, zero_pow (by decide : 2 ≠ 0),
          mul_zero, div_zero, Complex.ofReal_zero, zero_mul, sub_self, enorm_zero, zero_le]
      · exact hPoint T e ε M A S₁ S₂ h₁ h₂ h₁s h₂s hε q.1 q.2 hq.1 hlt hq.2.2)
  have massK₁ : (∫⁻ s in Icc 0 T, K₁ s) = ∫⁻ s in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S₁) s := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    exact indicator_of_mem hs _
  have massK₂ : (∫⁻ s in Icc 0 T, K₂ s) = ∫⁻ s in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S₂) s := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    exact indicator_of_mem hs _
  have massJ₂ : (∫⁻ s in Icc 0 T, J₂ s) = ∫⁻ s in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S₂) s := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    exact indicator_of_mem hs _
  have massDK : (∫⁻ s in Icc 0 T, DK s) = ∫⁻ s in Icc 0 T, inEnv T (fun u v => kC1 e (triangle 0 T)
      S₁ u v - kC1 e (triangle 0 T) S₂ u v) s := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    exact indicator_of_mem hs _
  have massDJ : (∫⁻ s in Icc 0 T, DJ s) = ∫⁻ s in Icc 0 T, outEnv 0 (fun u v => jC1 (triangle 0 T)
      S₁ u v - jC1 (triangle 0 T) S₂ u v) s := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    exact indicator_of_mem hs _
  have hK₁ : (∫⁻ s in Icc 0 T, K₁ s) ≤ ENNReal.ofReal (A * ε) := by
    rw [massK₁]
    exact (le_add_of_nonneg_left bot_le).trans h₁s.env
  have hK₂ : (∫⁻ s in Icc 0 T, K₂ s) ≤ ENNReal.ofReal (A * ε) := by
    rw [massK₂]
    exact (le_add_of_nonneg_left bot_le).trans h₂s.env
  have hJ₂ : (∫⁻ s in Icc 0 T, J₂ s) ≤ ENNReal.ofReal (A * ε) := by
    rw [massJ₂]
    exact (le_add_of_nonneg_right bot_le).trans h₂s.env
  have hDJ : (∫⁻ s in Icc 0 T, DJ s) = ENNReal.ofReal J := by
    rw [massDJ]
    exact (ENNReal.ofReal_toReal (stab_jDist_ne_top h₁s h₂s)).symm
  have hKF : (∫⁻ s in Icc 0 T, KF s) ≤ ENNReal.ofReal (K + F * (A * ε)) := by
    dsimp only [KF]
    rw [lintegral_add_left' (f := DK) (g := fun s => ENNReal.ofReal F * K₂ s)
      mDK.aemeasurable, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, massDK]
    apply (add_le_add le_rfl (mul_le_mul' le_rfl hK₂)).trans_eq
    rw [ENNReal.ofReal_add hK (mul_nonneg hF (mul_nonneg hA.le hε0)),
      ENNReal.ofReal_mul hF, ENNReal.ofReal_toReal (stab_kDist_ne_top h₁s h₂s)]
    rfl
  apply hb.trans
  apply le_trans (add_le_add (add_le_add (add_le_add
    (mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl hK₂) hJ₂))
    (mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl hK₂) hJ₂)))
    (mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl hKF) hJ₂)))
    (mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl hK₁) hDJ.le)))
  rw [← ENNReal.ofReal_ofNat 2]
  repeat rw [← ENNReal.ofReal_mul (by positivity)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hGU : G + U ≤ F := by dsimp only [F]; linarith only [hP]
  have hGF : G ≤ F := by dsimp only [F]; linarith only [hP, hU]
  calc
    _ ≤ (4096 * F * 4 * 1) * (2 * (A * ε) * (A * ε)) +
        (512 * 4 * (4 * F)) * (2 * (A * ε) * (A * ε)) +
        (512 * B * 1) * (2 * (K + F * (A * ε)) * (A * ε)) +
        (512 * 4 * 1) * (2 * (A * ε) * J) := by gcongr
    _ ≤ C * (ε * (J + K) + ε ^ 2 * F) := by
      dsimp only [C]
      have hgap : 0 ≤ (65536 - 49152) * A ^ 2 * (ε ^ 2 * F) := by positivity
      have hJgap : 0 ≤ (65536 * A ^ 2 + 1024 * B * A + 1024 * B * A ^ 2) * (ε * J) := by positivity
      have hKgap : 0 ≤ (65536 * A ^ 2 + 1024 * B * A ^ 2 + 4096 * A) * (ε * K) := by positivity
      have hFgap : 0 ≤ (1024 * B * A + 4096 * A) * (ε ^ 2 * F) := by positivity
      apply sub_nonneg.mp
      convert add_nonneg (add_nonneg (add_nonneg hgap hJgap) hKgap) hFgap using 1; ring

end EmcsfAcExtension.Local
