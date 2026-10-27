module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.Charge

/-! # Area of the normalized bootstrap triangle

Nonnegative integration proves the area budget of
`charged_SF_new_version.tex:L4661–L4664` before any source integrability is assumed.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Area

private theorem triangle_lintegral_le {s A : ℝ} (hs : 0 ≤ s) (hA : 0 ≤ A)
    (F : ℝ → ℝ → ℝ≥0∞)
    (hF : ∀ u v, (u, v) ∈ triangle 0 s → F u v ≤ ENNReal.ofReal A) :
    (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s, F u v) ≤ ENNReal.ofReal (A * s ^ 2) := by
  calc
    _ ≤ ∫⁻ u in Icc 0 s, ENNReal.ofReal A * ENNReal.ofReal s := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      calc
        _ ≤ ∫⁻ _v in Icc u s, ENNReal.ofReal A := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
          exact hF u v ⟨hu.1, hv.1, hv.2⟩
        _ = ENNReal.ofReal A * ENNReal.ofReal (s - u) := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
        _ ≤ _ := by gcongr; linarith only [hu.1]
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
        ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (mul_nonneg hA hs)]
      congr 1
      ring

/-- A pointwise source bounded by `A (-ν)λ` has area cost at most `4 A R²`.
The literal coefficient `4` depends only on the fixed bootstrap box;
`A` is kept explicit and no measurability hypothesis on the source is needed. -/
theorem area_integral_le_of_pointwise {e s ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hA : 0 ≤ A) (F : ℝ → ℝ → ℝ≥0∞)
    (hF : ∀ u v, (u, v) ∈ triangle 0 s →
      F u v ≤ ENNReal.ofReal (A * (-S.nu u v) * S.lam u v)) :
    (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s, F u v) ≤
      ENNReal.ofReal (4 * A * (s / 2) ^ 2) := by
  have hb (u v : ℝ) (hp : (u, v) ∈ triangle 0 s) : F u v ≤ ENNReal.ofReal A := by
    apply (hF u v hp).trans
    apply ENNReal.ofReal_le_ofReal
    have hn := (hset.box (u, v) hp).2.2.2.1
    have hl := (hset.box (u, v) hp).2.1
    have hn0 := (neg_pos.mpr (hset.c1.nu_neg (u, v) hp)).le
    have hl0 := (hset.c1.lam_pos (u, v) hp).le
    calc
      A * (-S.nu u v) * S.lam u v ≤ A * 1 * 1 := by gcongr
      _ = A := by ring
  convert triangle_lintegral_le hset.pos.le hA F hb using 1
  congr 1
  ring

/-- The area comparison in the other order of characteristic integration.
The literal coefficient `4` depends only on the fixed bootstrap box;
`A` remains explicit and the comparison precedes any integrability argument. -/
theorem area_integral_in_le_of_pointwise {e s ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e s ε M S h) (hA : 0 ≤ A) (F : ℝ → ℝ → ℝ≥0∞)
    (hF : ∀ u v, (u, v) ∈ triangle 0 s →
      F u v ≤ ENNReal.ofReal (A * (-S.nu u v) * S.lam u v)) :
    (∫⁻ v in Icc 0 s, ∫⁻ u in Icc 0 v, F u v) ≤
      ENNReal.ofReal (4 * A * (s / 2) ^ 2) := by
  have hb (u v : ℝ) (hp : (u, v) ∈ triangle 0 s) : F u v ≤ ENNReal.ofReal A := by
    apply (hF u v hp).trans
    apply ENNReal.ofReal_le_ofReal
    have hn := (hset.box (u, v) hp).2.2.2.1
    have hl := (hset.box (u, v) hp).2.1
    have hn0 := (neg_pos.mpr (hset.c1.nu_neg (u, v) hp)).le
    have hl0 := (hset.c1.lam_pos (u, v) hp).le
    calc
      A * (-S.nu u v) * S.lam u v ≤ A * 1 * 1 := by gcongr
      _ = A := by ring
  calc
    _ ≤ ∫⁻ _v in Icc 0 s, ENNReal.ofReal A * ENNReal.ofReal s := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      calc
        _ ≤ ∫⁻ _u in Icc 0 v, ENNReal.ofReal A := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
          exact hb u v ⟨hu.1, hu.2, hv.2⟩
        _ = ENNReal.ofReal A * ENNReal.ofReal v := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
        _ ≤ _ := by gcongr; exact hv.2
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
        ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (mul_nonneg hA hset.pos.le)]
      congr 1
      ring

/-- [node restart-sec-independent-area#area-volume-bound]
Area of the normalized finite triangle (`charged_SF_new_version.tex:L4661–L4664`).
`C` depends only on the fixed bootstrap box, independently of all solution
parameters, coupling, and data derivative norms. -/
theorem area_volume_bound : ∃ C : ℝ, 0 < C ∧ ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h →
      (∫⁻ u in Icc 0 s, ∫⁻ v in Icc u s, ENNReal.ofReal ((-S.nu u v) * S.lam u v)) ≤
        ENNReal.ofReal (C * (s / 2) ^ 2) := by
  refine ⟨4, by norm_num, ?_⟩
  intro e s ε M S h hset
  simpa only [one_mul, mul_one] using area_integral_le_of_pointwise hset
    (by norm_num : (0 : ℝ) ≤ 1)
    (fun u v => ENNReal.ofReal ((-S.nu u v) * S.lam u v))
    (fun _ _ _ => by simp only [one_mul, le_refl])

end EmcsfAcExtension.Local.Area
