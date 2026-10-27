module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongPureAlgebra
import EmcsfAcExtension.Local.Stability.GeomStrongPureIntegral
import EmcsfAcExtension.Local.Stability.GeomStrongRegularity
import EmcsfAcExtension.Local.Stability.FluxDifferenceRegularity
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassBudgets
import EmcsfAcExtension.Local.Stability.GeomStrongMassInIndividualBudget

import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux

/-! # Section budgets for the pure expansion differences

The same-direction derivatives are estimated in their actual null
sections. Each envelope contribution is enlarged only in its label
integration range; each flux contribution keeps its own orientation.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The outgoing pure expansion difference costs its renormalized
label envelope, quadratic flux difference, and the second solution's
individual envelope/flux budgets. All coefficients are universal.
- the explicit `256 A ε²` is uniform in all solution parameters. -/
theorem stab_pure_outgoing_section_le_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ^ 2 ≤ 1 / 4)
    {u : ℝ} (hu : u ∈ Icc 0 T) :
    (∫⁻ v in Icc u T, ‖pdV (triangle 0 T) S₁.lam u v - pdV (triangle 0 T) S₂.lam u v‖ₑ) ≤
      (∫⁻ v in Icc 0 T, outEnv 0 (fun u v => geomL (triangle 0 T) S₁ u v -
        geomL (triangle 0 T) S₂ u v) v) +
      (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ENNReal.ofReal
        |S₁.lam u v / S₁.r u v * ‖S₁.theta u v / (S₁.lam u v : ℂ)‖ ^ 2 -
          S₂.lam u v / S₂.r u v * ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2|) +
      ENNReal.ofReal (geomDist T S₁ S₂).toReal *
        ((∫⁻ v in Icc 0 T, outEnv 0 (geomL (triangle 0 T) S₂) v) +
          ENNReal.ofReal (256 * A * ε ^ 2)) := by
  let L₁ := geomL (triangle 0 T) S₁ u
  let L₂ := geomL (triangle 0 T) S₂ u
  let F₁ := fun v => S₁.lam u v / S₁.r u v * ‖S₁.theta u v / (S₁.lam u v : ℂ)‖ ^ 2
  let F₂ := fun v => S₂.lam u v / S₂.r u v * ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2
  have hm : MapsTo (fun v : ℝ => (u, v)) (Icc u T) (triangle 0 T) :=
    fun v hv => ⟨hu.1, hv.1, hv.2⟩
  have cp : ContinuousOn (fun v : ℝ => (u, v)) (Icc u T) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have cL₁ : ContinuousOn L₁ (Icc u T) :=
    (stab_geomL_continuous_c1 h₁s).comp (f := fun v : ℝ => (u, v)) cp hm
  have cL₂ : ContinuousOn L₂ (Icc u T) :=
    (stab_geomL_continuous_c1 h₂s).comp (f := fun v : ℝ => (u, v)) cp hm
  have cF₁ : ContinuousOn F₁ (Icc u T) := (stab_out_quadratic_flux_continuous h₁s).comp cp hm
  have cF₂ : ContinuousOn F₂ (Icc u T) := (stab_out_quadratic_flux_continuous h₂s).comp cp hm
  have hi := stab_pure_derivative_section_integral_le ENNReal.toReal_nonneg cL₁ cL₂ cF₁ cF₂
    (fun v hv => stab_pure_outgoing_difference_le_c1 h₁s h₂s (hm hv))
  have hL : (∫⁻ v in Icc u T, ‖L₁ v - L₂ v‖ₑ) ≤
      ∫⁻ v in Icc 0 T, outEnv 0 (fun u v => geomL (triangle 0 T) S₁ u v -
        geomL (triangle 0 T) S₂ u v) v := by
    apply (setLIntegral_mono' measurableSet_Icc (fun v hv =>
      enorm_le_normEnvelope (fun u v => geomL (triangle 0 T) S₁ u v -
        geomL (triangle 0 T) S₂ u v) ⟨hu.1, hv.1⟩)).trans
    exact lintegral_mono_set (Icc_subset_Icc_left hu.1)
  have hL₂ : (∫⁻ v in Icc u T, ‖L₂ v‖ₑ) ≤
      ∫⁻ v in Icc 0 T, outEnv 0 (geomL (triangle 0 T) S₂) v := by
    apply (setLIntegral_mono' measurableSet_Icc (fun v hv =>
      enorm_le_normEnvelope (geomL (triangle 0 T) S₂) ⟨hu.1, hv.1⟩)).trans
    exact lintegral_mono_set (Icc_subset_Icc_left hu.1)
  have hF₂ : (∫⁻ v in Icc u T, ‖F₂ v‖ₑ) ≤ ENNReal.ofReal (256 * A * ε ^ 2) := by
    have heq : (∫⁻ v in Icc u T, ‖F₂ v‖ₑ) =
        ∫⁻ v in Icc u T, ENNReal.ofReal (F₂ v) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro v hv
      have hr : 0 ≤ S₂.r u v := by
        have hh := (stab_radius_bounds h₂s hu.1 hv.1 hv.2).1
        linarith only [hh, hv.1]
      change ‖F₂ v‖ₑ = ENNReal.ofReal (F₂ v)
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (show 0 ≤ F₂ v from
        mul_nonneg (div_nonneg (h₂s.c1.lam_pos (u, v) (hm hv)).le hr) (sq_nonneg _))]
    rw [heq]
    exact stab_out_mixed_quadratic_le h₂s h₂s hε hu.1 hu.2
  apply hi.trans
  apply add_le_add (add_le_add hL ?_) (mul_le_mul' le_rfl (add_le_add hL₂ hF₂))
  simp only [Real.enorm_eq_ofReal_abs]
  exact le_iSup₂_of_le u hu le_rfl


/-- The incoming pure expansion difference costs its renormalized
label envelope, quadratic flux difference, and the second solution's
individual envelope/flux budgets. All coefficients are universal.
- the explicit `256 A ε²` is uniform in all solution parameters. -/
theorem stab_pure_incoming_section_le_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hA : 0 < A) (hε : ε ^ 2 ≤ 1 / 4)
    {v : ℝ} (hv : v ∈ Icc 0 T) :
    (∫⁻ u in Icc 0 v, ‖pdU (triangle 0 T) S₁.nu u v - pdU (triangle 0 T) S₂.nu u v‖ₑ) ≤
      (∫⁻ u in Icc 0 T, inEnv T (fun u v => geomN (triangle 0 T) S₁ u v -
        geomN (triangle 0 T) S₂ u v) u) +
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v, ENNReal.ofReal
        |(-S₁.nu u v) / S₁.r u v * ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2 -
          (-S₂.nu u v) / S₂.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2|) +
      ENNReal.ofReal (geomDist T S₁ S₂).toReal *
        ((∫⁻ u in Icc 0 T, inEnv T (geomN (triangle 0 T) S₂) u) +
          ENNReal.ofReal (256 * A * ε ^ 2)) := by
  let L₁ := fun u => geomN (triangle 0 T) S₁ u v
  let L₂ := fun u => geomN (triangle 0 T) S₂ u v
  let F₁ := fun u => (-S₁.nu u v) / S₁.r u v * ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2
  let F₂ := fun u => (-S₂.nu u v) / S₂.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2
  have hm : MapsTo (fun u : ℝ => (u, v)) (Icc 0 v) (triangle 0 T) :=
    fun u hu => ⟨hu.1, hu.2, hv.2⟩
  have cp : ContinuousOn (fun u : ℝ => (u, v)) (Icc 0 v) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have cL₁ : ContinuousOn L₁ (Icc 0 v) := by
    have hc := (stab_geomN_continuous_c1 h₁s).comp cp hm
    exact hc
  have cL₂ : ContinuousOn L₂ (Icc 0 v) :=
    (stab_geomN_continuous_c1 h₂s).comp (f := fun u : ℝ => (u, v)) cp hm
  have cF₁ : ContinuousOn F₁ (Icc 0 v) := (stab_in_quadratic_flux_continuous h₁s).comp cp hm
  have cF₂ : ContinuousOn F₂ (Icc 0 v) := (stab_in_quadratic_flux_continuous h₂s).comp cp hm
  have hi := stab_pure_derivative_section_integral_le ENNReal.toReal_nonneg cL₁ cL₂ cF₁ cF₂
    (fun u hu => stab_pure_incoming_difference_le_c1 h₁s h₂s (hm hu))
  have hL : (∫⁻ u in Icc 0 v, ‖L₁ u - L₂ u‖ₑ) ≤
      ∫⁻ u in Icc 0 T, inEnv T (fun u v => geomN (triangle 0 T) S₁ u v -
        geomN (triangle 0 T) S₂ u v) u := by
    have hp : ∀ u ∈ Icc 0 v, ‖L₁ u - L₂ u‖ₑ ≤
        inEnv T (fun u v => geomN (triangle 0 T) S₁ u v - geomN (triangle 0 T) S₂ u v) u := by
      intro u hu
      rw [inEnv_def]
      exact le_iSup₂_of_le v ⟨hu.2, hv.2⟩ le_rfl
    exact (setLIntegral_mono' measurableSet_Icc hp).trans
      (lintegral_mono_set (Icc_subset_Icc_right hv.2))
  have hL₂ : (∫⁻ u in Icc 0 v, ‖L₂ u‖ₑ) ≤
      ∫⁻ u in Icc 0 T, inEnv T (geomN (triangle 0 T) S₂) u := by
    have hp : ∀ u ∈ Icc 0 v, ‖L₂ u‖ₑ ≤ inEnv T (geomN (triangle 0 T) S₂) u := by
      intro u hu
      rw [inEnv_def]
      exact le_iSup₂_of_le v ⟨hu.2, hv.2⟩ le_rfl
    exact (setLIntegral_mono' measurableSet_Icc hp).trans
      (lintegral_mono_set (Icc_subset_Icc_right hv.2))
  have hF₂ : (∫⁻ u in Icc 0 v, ‖F₂ u‖ₑ) ≤ ENNReal.ofReal (256 * A * ε ^ 2) := by
    have heq : (∫⁻ u in Icc 0 v, ‖F₂ u‖ₑ) =
        ∫⁻ u in Icc 0 v, ENNReal.ofReal (F₂ u) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro u hu
      have hr : 0 ≤ S₂.r u v := by
        have hh := (stab_radius_bounds h₂s hu.1 hu.2 hv.2).1
        linarith only [hh, hu.2]
      change ‖F₂ u‖ₑ = ENNReal.ofReal (F₂ u)
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (show 0 ≤ F₂ u from
        mul_nonneg (div_nonneg (neg_pos.mpr (h₂s.c1.nu_neg (u, v) (hm hu))).le hr) (sq_nonneg _))]
    rw [heq]
    exact stab_in_mixed_quadratic_le hA h₂s h₂s hε hv.1 hv.2
  apply hi.trans
  apply add_le_add (add_le_add hL ?_) (mul_le_mul' le_rfl (add_le_add hL₂ hF₂))
  simp only [Real.enorm_eq_ofReal_abs]
  exact le_iSup₂_of_le v hv le_rfl


end EmcsfAcExtension.Local
