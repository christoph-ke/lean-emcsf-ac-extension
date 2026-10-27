module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Bounds
import EmcsfAcExtension.Local.Stability.PotentialHardy
import EmcsfAcExtension.Local.Stability.PotentialHardyClosed
import EmcsfAcExtension.Local.Stability.PotentialArea
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux

/-! # Cubic charge area budgets for the potential source

The outgoing Hardy weight is removed with the fixed lower expansion
bound before the outgoing labels are integrated. No bare inverse-radius
integral or prior source integrability is assumed.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Removing the outgoing expansion from a positive cubic radial
integral costs the universal factor four. The forcing can be arbitrary
and the integrals may be infinite; no minimum-radius bound is used. -/
theorem stab_cubic_integral_le_four_weighted_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u : ℝ} (hu : u ∈ Icc 0 T)
    {f : ℝ → ℝ} (hf : ∀ t ∈ Icc u T, 0 ≤ f t) :
    (∫⁻ t in Icc u T, ENNReal.ofReal (f t / S.r u t ^ 3)) ≤
      ENNReal.ofReal 4 * ∫⁻ t in Icc u T, ENNReal.ofReal (S.lam u t * f t / S.r u t ^ 3) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  apply ENNReal.ofReal_le_ofReal
  have hp : (u, t) ∈ triangle 0 T := ⟨hu.1, ht.1, ht.2⟩
  have hr : 0 ≤ S.r u t :=
    (div_nonneg (sub_nonneg.mpr ht.1) (by norm_num : (0 : ℝ) ≤ 4)).trans
      (stab_radius_bounds hset hu.1 ht.1 ht.2).1
  have hz : 0 ≤ f t / S.r u t ^ 3 := div_nonneg (hf t ht) (pow_nonneg hr 3)
  have hh := mul_le_mul_of_nonneg_right (hset.box.2 (u, t) hp).1 hz
  rw [mul_div_assoc]
  linarith only [hh]

/-- The cubic charge area has bound `16 A |e|M T ε`.
All dependence on the envelope constant, background, coupling, time
and ratio size is explicit; the coefficient sixteen is universal and
independent of data derivatives and minimum radii. -/
theorem stab_charge_cubic_area_le_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) (hA : 0 ≤ A) (hεsq : ε ^ 2 ≤ 1 / 4) :
    (∫⁻ p in triangle 0 T, ENNReal.ofReal (|S.Q p.1 p.2| / S.r p.1 p.2 ^ 3)) ≤
      ENNReal.ofReal (16 * A * |e| * M * T * ε) := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S.xi 0 0 / (S.nu 0 0 : ℂ)))).trans
      (hset.box.2 (0, 0) ⟨le_rfl, le_rfl, hset.pos.le⟩).2.2.2.2.2.1)
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hset.box.1
  have aQ := hset.c1.c1_Q.continuousOn.aemeasurable (μ := volume) (measurableSet_triangle 0 T)
  have aR := hset.c1.c1_r.continuousOn.aemeasurable (μ := volume) (measurableSet_triangle 0 T)
  have mF : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (|S.Q p.1 p.2| / S.r p.1 p.2 ^ 3))
      (volume.restrict (triangle 0 T)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (aQ.abs.div (aR.pow_const 3))
  have hsection : ∀ u ∈ Icc 0 T, (∫⁻ t in Icc u T, ENNReal.ofReal (|S.Q u t| / S.r u t ^ 3)) ≤
      ENNReal.ofReal (16 * A * |e| * M * ε) := by
    intro u hu
    have hh := (Stab.charge_radial_hardy_bound hset hεsq hu.1 hu.2 le_rfl).2
    have hJ := (le_add_of_nonneg_right bot_le).trans hset.env
    apply ((stab_cubic_integral_le_four_weighted_c1 hset hu (fun t _ => abs_nonneg (S.Q u t))).trans
      (mul_le_mul' le_rfl (hh.trans (mul_le_mul' le_rfl hJ)))).trans
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    apply ENNReal.ofReal_le_ofReal
    have hn : 0 ≤ A * |e| * M * ε := by positivity
    nlinarith only [hn]
  apply (stab_triangle_area_le_of_outgoing_budget hset.pos.le mF hsection).trans_eq
  rw [← ENNReal.ofReal_mul hset.pos.le]
  congr 1
  ring

/-- The charge-difference cubic area is `K |e|M T Δ₀` under the proved
extended record. `K>0` depends only on `A` and the uniform record
constant `C`, before all data, fields, scales, coupling and background,
uniformly in derivative suprema and minimum radii. -/
theorem stab_charge_cubic_difference_area_of_stab_bounds_c1
    (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 ≤ 1 / 4 → StabBounds C e T M (dataDist h₁ h₂ T) S₁ S₂ →
      (∫⁻ p in triangle 0 T, ENNReal.ofReal
        (|S₁.Q p.1 p.2 - S₂.Q p.1 p.2| / S₁.r p.1 p.2 ^ 3)) ≤
          ENNReal.ofReal (K * |e| * M * T * dataDist h₁ h₂ T) := by
  obtain ⟨K, hK, hHardy⟩ := stab_charge_hardy_difference_of_stab_bounds_c1 A C hA hC
  refine ⟨4 * K, by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hεsq hb
  have aQ₁ := h₁s.c1.c1_Q.continuousOn.aemeasurable (μ := volume) (measurableSet_triangle 0 T)
  have aQ₂ := h₂s.c1.c1_Q.continuousOn.aemeasurable (μ := volume) (measurableSet_triangle 0 T)
  have aR := h₁s.c1.c1_r.continuousOn.aemeasurable (μ := volume) (measurableSet_triangle 0 T)
  have mF : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal
      (|S₁.Q p.1 p.2 - S₂.Q p.1 p.2| / S₁.r p.1 p.2 ^ 3)) (volume.restrict (triangle 0 T)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((aQ₁.sub aQ₂).abs.div (aR.pow_const 3))
  have hh := hHardy T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hεsq hb
  have hsection : ∀ u ∈ Icc 0 T, (∫⁻ t in Icc u T, ENNReal.ofReal
      (|S₁.Q u t - S₂.Q u t| / S₁.r u t ^ 3)) ≤
        ENNReal.ofReal (4 * K * |e| * M * dataDist h₁ h₂ T) := by
    intro u hu
    apply ((stab_cubic_integral_le_four_weighted_c1 h₁s hu (fun t _ => abs_nonneg _)).trans
      (mul_le_mul' le_rfl ((le_iSup₂_of_le u hu le_rfl).trans hh))).trans_eq
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    ring
  apply (stab_triangle_area_le_of_outgoing_budget h₁s.pos.le mF hsection).trans_eq
  rw [← ENNReal.ofReal_mul h₁s.pos.le]
  congr 1
  ring

end EmcsfAcExtension.Local
