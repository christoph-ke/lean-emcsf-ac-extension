module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeomStrongBorel
import EmcsfAcExtension.Local.Stability.GeomStrongEnvelope
import EmcsfAcExtension.Infra.Triangle

/-! # Geometric source area in either characteristic order

The Borel zero extensions give both Tonelli orders before any finite
source bound. They also reduce the envelope transport to one area norm.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The two section integration orders of the source difference equal
its triangle area norm. This exact identity has no finiteness premise
and no estimate constant.
-/
theorem stab_geometric_source_difference_area_orders_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖geomSource S₁ u v - geomSource S₂ u v‖ₑ) =
      (∫⁻ p in triangle 0 T, ‖geomSource S₁ p.1 p.2 - geomSource S₂ p.1 p.2‖ₑ) ∧
    (∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T, ‖geomSource S₁ u v - geomSource S₂ u v‖ₑ) =
      (∫⁻ p in triangle 0 T, ‖geomSource S₁ p.1 p.2 - geomSource S₂ p.1 p.2‖ₑ) := by
  let G₁ := (triangle 0 T).indicator (Function.uncurry (geomSource S₁))
  let G₂ := (triangle 0 T).indicator (Function.uncurry (geomSource S₂))
  let F := fun p : ℝ × ℝ => ‖G₁ p - G₂ p‖ₑ
  have mF : Measurable F := ((stab_geomSource_borel_c1 h₁s).sub
    (stab_geomSource_borel_c1 h₂s)).enorm
  have hF p (hp : p ∈ triangle 0 T) :
      F p = ‖geomSource S₁ p.1 p.2 - geomSource S₂ p.1 p.2‖ₑ := by
    dsimp only [F, G₁, G₂]
    rw [indicator_of_mem hp, indicator_of_mem hp]
    rfl
  have harea : (∫⁻ p in triangle 0 T, F p) =
      ∫⁻ p in triangle 0 T, ‖geomSource S₁ p.1 p.2 - geomSource S₂ p.1 p.2‖ₑ :=
    setLIntegral_congr_fun (measurableSet_triangle 0 T) hF
  constructor
  · have heq := lintegral_triangle_eq_lintegral_lintegral_symm (a := 0) (b := T) mF
    rw [← Measure.volume_eq_prod, harea] at heq
    apply Eq.trans ?_ heq.symm
    apply setLIntegral_congr_fun measurableSet_Icc
    intro v hv
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    exact (hF (u, v) ⟨hu.1, hu.2, hv.2⟩).symm
  · have heq := lintegral_triangle_eq_lintegral_lintegral (a := 0) (b := T) mF
    rw [← Measure.volume_eq_prod, harea] at heq
    apply Eq.trans ?_ heq.symm
    apply setLIntegral_congr_fun measurableSet_Icc
    intro u hu
    apply setLIntegral_congr_fun measurableSet_Icc
    intro v hv
    exact (hF (u, v) ⟨hu.1, hv.1, hv.2⟩).symm

/-- The actual geometric envelope difference costs twice its initial
norm and three times the source area norm. These numerical coefficients
are universal, before all parameters, fields and derivative bounds.
-/
theorem stab_geometric_envelope_difference_le_source_c1
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) :
    (∫⁻ v in Icc 0 T, outEnv 0 (fun u v =>
      geomL (triangle 0 T) S₁ u v - geomL (triangle 0 T) S₂ u v) v) +
    (∫⁻ u in Icc 0 T, inEnv T (fun u v =>
      geomN (triangle 0 T) S₁ u v - geomN (triangle 0 T) S₂ u v) u) ≤
      2 * (∫⁻ v in Icc 0 T, ‖geomL (triangle 0 T) S₁ 0 v -
        geomL (triangle 0 T) S₂ 0 v‖ₑ) +
      3 * (∫⁻ p in triangle 0 T, ‖geomSource S₁ p.1 p.2 - geomSource S₂ p.1 p.2‖ₑ) := by
  have h := stab_geometric_envelope_transport_difference_c1 h₁s h₂s
  obtain ⟨hi, ho⟩ := stab_geometric_source_difference_area_orders_c1 h₁s h₂s
  rw [hi, ho] at h
  exact h.trans_eq (by ring)

end EmcsfAcExtension.Local
