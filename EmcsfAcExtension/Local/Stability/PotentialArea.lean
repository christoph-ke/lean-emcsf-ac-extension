module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Infra.Triangle

/-! # Area budgets from a.e. measurable triangle densities

Tonelli is applied after a measurable zero extension. This needs only
a.e. measurability on the actual triangle, permitting rational field
expressions with totalized axis values.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Tonelli in outgoing order for a density a.e. measurable on the
triangle itself. There is no finite-integral premise or constant. -/
theorem stab_triangle_lintegral_out_of_aemeasurable {T : ℝ}
    {F : ℝ × ℝ → ℝ≥0∞} (hF : AEMeasurable F (volume.restrict (triangle 0 T))) :
    (∫⁻ p in triangle 0 T, F p) = ∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T, F (u, v) := by
  classical
  rw [Measure.volume_eq_prod] at hF ⊢
  rw [← lintegral_indicator (measurableSet_triangle 0 T),
    lintegral_prod _ ((aemeasurable_indicator_iff (measurableSet_triangle 0 T)).2 hF),
    ← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro u
  by_cases hu : u ∈ Icc 0 T
  · rw [indicator_of_mem hu, ← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro v
    by_cases hv : v ∈ Icc u T
    · rw [indicator_of_mem (show (u, v) ∈ triangle 0 T from ⟨hu.1, hv.1, hv.2⟩), indicator_of_mem
        hv]
    · rw [indicator_of_notMem (show (u, v) ∉ triangle 0 T from fun hp => hv ⟨hp.2.1, hp.2.2⟩),
        indicator_of_notMem hv]
  · rw [indicator_of_notMem hu]
    have hno v : (u, v) ∉ triangle 0 T := fun hp => hu ⟨hp.1, hp.2.1.trans hp.2.2⟩
    simp only [indicator_of_notMem (hno _), lintegral_zero]

/-- A uniform outgoing section budget has area cost exactly the time
length `T`. The coefficient one is uniform in the density and all other
parameters, with no integrability or minimum-radius premise. -/
theorem stab_triangle_area_le_of_outgoing_budget {T : ℝ} {K : ℝ≥0∞}
    {F : ℝ × ℝ → ℝ≥0∞} (_hT : 0 ≤ T)
    (hF : AEMeasurable F (volume.restrict (triangle 0 T)))
    (hbound : ∀ u ∈ Icc 0 T, (∫⁻ v in Icc u T, F (u, v)) ≤ K) :
    (∫⁻ p in triangle 0 T, F p) ≤ ENNReal.ofReal T * K := by
  rw [stab_triangle_lintegral_out_of_aemeasurable hF]
  apply (setLIntegral_mono' measurableSet_Icc hbound).trans_eq
  rw [setLIntegral_const, Real.volume_Icc, sub_zero]
  exact mul_comm _ _

/-- A continuous real field has area norm at most `T` times its incoming
label-envelope norm. The coefficient one is universal, independent of
all field sizes, derivative bounds and minimum radii. -/
theorem stab_triangle_norm_area_le_incoming_envelope {T : ℝ} {F : ℝ → ℝ → ℝ}
    (_hT : 0 ≤ T) (cF : ContinuousOn (Function.uncurry F) (triangle 0 T)) :
    (∫⁻ p in triangle 0 T, ‖F p.1 p.2‖ₑ) ≤ ENNReal.ofReal T *
      ∫⁻ u in Icc 0 T, inEnv T F u := by
  have mF : AEMeasurable (fun p : ℝ × ℝ => ‖F p.1 p.2‖ₑ)
      (volume.restrict (triangle 0 T)) := by
    simpa only [Function.uncurry_def] using!
      cF.enorm.aemeasurable (μ := volume) (measurableSet_triangle 0 T)
  rw [stab_triangle_lintegral_out_of_aemeasurable mF,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro u hu
  have hb : (∫⁻ v in Icc u T, ‖F u v‖ₑ) ≤
      ∫⁻ v in Icc u T, inEnv T F u := by
    apply setLIntegral_mono' measurableSet_Icc
    intro v hv
    rw [inEnv_def]
    exact le_iSup₂_of_le v hv le_rfl
  apply hb.trans
  rw [setLIntegral_const, Real.volume_Icc]
  calc
    _ ≤ inEnv T F u * ENNReal.ofReal T :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (sub_le_self _ hu.1))
    _ = _ := mul_comm _ _

/-- Almost every triangle point is strictly off the diagonal. The
exceptional set has product Lebesgue measure zero; no field regularity
or estimate constant is involved. -/
theorem stab_triangle_ae_off_axis (T : ℝ) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)).restrict (triangle 0 T), p.1 < p.2 := by
  have hne : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ p.2 := by
    rw [Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae
      ((isClosed_eq (continuous_fst : Continuous (fun p : ℝ × ℝ => p.1))
          continuous_snd).measurableSet.compl)).2
    exact ae_of_all _ (fun u => by simp [ae_iff])
  filter_upwards [ae_restrict_mem (measurableSet_triangle 0 T), ae_restrict_of_ae hne] with p hp hnp
  exact lt_of_le_of_ne hp.2.1 hnp

/-- Six positive real majorants retain their products under `ofReal`.
Every coefficient is an explicit nonnegative input and the comparison
has universal coefficient one. -/
theorem stab_six_positive_ofReal_le
    {y b₁ b₂ b₃ b₄ b₅ b₆ x₁ x₂ x₃ x₄ x₅ x₆ : ℝ}
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃)
    (hb₄ : 0 ≤ b₄) (hb₅ : 0 ≤ b₅) (hb₆ : 0 ≤ b₆)
    (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂) (hx₃ : 0 ≤ x₃)
    (hx₄ : 0 ≤ x₄) (hx₅ : 0 ≤ x₅) (hx₆ : 0 ≤ x₆)
    (h : y ≤ b₁ * x₁ + b₂ * x₂ + b₃ * x₃ + b₄ * x₄ + b₅ * x₅ + b₆ * x₆) :
    ENNReal.ofReal y ≤ ENNReal.ofReal b₁ * ENNReal.ofReal x₁ +
      ENNReal.ofReal b₂ * ENNReal.ofReal x₂ + ENNReal.ofReal b₃ * ENNReal.ofReal x₃ +
      ENNReal.ofReal b₄ * ENNReal.ofReal x₄ + ENNReal.ofReal b₅ * ENNReal.ofReal x₅ +
      ENNReal.ofReal b₆ * ENNReal.ofReal x₆ := by
  have hh := ENNReal.ofReal_le_ofReal h
  repeat rw [ENNReal.ofReal_add (by positivity) (by positivity)] at hh
  rw [ENNReal.ofReal_mul hb₁, ENNReal.ofReal_mul hb₂, ENNReal.ofReal_mul hb₃,
    ENNReal.ofReal_mul hb₄, ENNReal.ofReal_mul hb₅, ENNReal.ofReal_mul hb₆] at hh
  exact hh

/-- Six a.e. measurable positive majorants have the sum of their six
area budgets. The estimate has coefficient one, requires no prior
integrability of the source, and permits infinite budgets. -/
theorem stab_six_lintegral_le_of_majorants {μ : Measure (ℝ × ℝ)}
    {F f₁ f₂ f₃ f₄ f₅ f₆ : ℝ × ℝ → ℝ≥0∞} {B₁ B₂ B₃ B₄ B₅ B₆ : ℝ≥0∞}
    (m₁ : AEMeasurable f₁ μ) (m₂ : AEMeasurable f₂ μ) (m₃ : AEMeasurable f₃ μ)
    (m₄ : AEMeasurable f₄ μ) (m₅ : AEMeasurable f₅ μ)
    (hpoint : ∀ᵐ p ∂μ, F p ≤ f₁ p + f₂ p + f₃ p + f₄ p + f₅ p + f₆ p)
    (h₁ : (∫⁻ p, f₁ p ∂μ) ≤ B₁) (h₂ : (∫⁻ p, f₂ p ∂μ) ≤ B₂)
    (h₃ : (∫⁻ p, f₃ p ∂μ) ≤ B₃) (h₄ : (∫⁻ p, f₄ p ∂μ) ≤ B₄)
    (h₅ : (∫⁻ p, f₅ p ∂μ) ≤ B₅) (h₆ : (∫⁻ p, f₆ p ∂μ) ≤ B₆) :
    (∫⁻ p, F p ∂μ) ≤ B₁ + B₂ + B₃ + B₄ + B₅ + B₆ := by
  apply (lintegral_mono_ae hpoint).trans
  rw [lintegral_add_left' (f := fun p => f₁ p + f₂ p + f₃ p + f₄ p + f₅ p) (g := f₆)
      ((((m₁.add m₂).add m₃).add m₄).add m₅),
    lintegral_add_left' (f := fun p => f₁ p + f₂ p + f₃ p + f₄ p) (g := f₅)
      (((m₁.add m₂).add m₃).add m₄),
    lintegral_add_left' (f := fun p => f₁ p + f₂ p + f₃ p) (g := f₄) ((m₁.add m₂).add m₃),
    lintegral_add_left' (f := fun p => f₁ p + f₂ p) (g := f₃) (m₁.add m₂),
    lintegral_add_left' (f := f₁) (g := f₂) m₁]
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄) h₅) h₆

end EmcsfAcExtension.Local
