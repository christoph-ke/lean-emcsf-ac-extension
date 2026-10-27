module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceInitialMassForcing
import EmcsfAcExtension.Local.Stability.GeometryDifferenceInitialMassMeasure
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassRaw
import EmcsfAcExtension.Local.Stability.ChargeDifferenceInitial
import EmcsfAcExtension.Local.Stability.FieldDifferenceInitialAverage

/-! # Initial mass feedback in the common radial geometry

Initial scalar averaging and the oscillatory charge constraint give
the electromagnetic source cost. The damped normalized mass equation
then bounds the initial mass by the initial radial difference alone.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- Initial ratio point and Hardy bounds `X` imply the initial mass
bound `2εX+40σε(X+εδ₀)`. The numerical coefficients are universal,
before all parameters and the pair. This conditional helper retains
the data term and introduces no global geometric error. -/
theorem stab_initial_mass_le_of_ratio_bounds
    {e T ε M A X : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hX : 0 ≤ X)
    (hx : ∀ v ∈ Icc 0 T,
      ‖S₁.theta 0 v / (S₁.lam 0 v : ℂ) - S₂.theta 0 v / (S₂.lam 0 v : ℂ)‖ ≤ X)
    (hHardy : (∫⁻ t in Icc 0 T, ENNReal.ofReal (S₁.lam 0 t / S₁.r 0 t *
      ‖S₁.theta 0 t / (S₁.lam 0 t : ℂ) - S₂.theta 0 t / (S₂.lam 0 t : ℂ)‖)) ≤
        ENNReal.ofReal X) :
    ∀ v ∈ Icc 0 T, |S₁.mu 0 v - S₂.mu 0 v| ≤
      2 * ε * X + 40 * sigma e M T * ε * (X + ε * dataDist h₁ h₂ T) := by
  let Δ := dataDist h₁ h₂ T
  let D := |e| * (M * X + ε * Δ)
  let H := X + ε * Δ
  let K := |e| * M * ε
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hcharge : ∀ v, 0 < v → v ≤ T → |S₁.Q 0 v - S₂.Q 0 v| / S₁.r 0 v ^ 2 ≤ D := by
    intro v hv hvT
    exact stab_initial_charge_le_of_field_bounds h₁s h₂s hX hΔ hx
      (fun t ht => stab_initial_scalar_difference_le h₁s h₂s ht) hv hvT
  have hem := stab_initial_em_le_of_charge_bound h₁s h₂s hD hcharge
  have hDm : D ≤ |e| * M * H := by
    have hh := mul_nonneg (sub_nonneg.mpr h₁s.box.1) (mul_nonneg hε hΔ)
    have hL : M * X + ε * Δ ≤ M * H := by dsimp only [H]; nlinarith only [hh]
    have hs := mul_le_mul_of_nonneg_left hL (abs_nonneg e)
    dsimp only [D]
    nlinarith only [hs]
  have hEmScale : 10 * K * T ^ 2 * D ≤ 40 * sigma e M T * ε * H := by
    have hh := mul_le_mul_of_nonneg_left hDm (show 0 ≤ 10 * K * T ^ 2 by positivity)
    calc
      _ ≤ (10 * K * T ^ 2) * (|e| * M * H) := hh
      _ = _ := by
        dsimp only [K, sigma]
        rw [← sq_abs e]
        ring
  have hEM := hem.trans (ENNReal.ofReal_le_ofReal hEmScale)
  have hforcing : (∫⁻ t in Icc 0 T, ENNReal.ofReal |massDifferenceForcing S₁ S₂ 0 t|) ≤
      ENNReal.ofReal (2 * ε * X + 40 * sigma e M T * ε * H) := by
    apply (stab_initial_mass_forcing_budget h₁s h₂s).trans
    apply (add_le_add (mul_le_mul' le_rfl hHardy) hEM).trans_eq
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * ε),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  intro v hv
  rcases hv.1.eq_or_lt with rfl | hv0
  · simp only [Fields.mu, (h₁s.c1.axis 0 ⟨le_rfl, le_rfl, h₁s.pos.le⟩).1,
      (h₂s.c1.axis 0 ⟨le_rfl, le_rfl, h₂s.pos.le⟩).1, div_zero, sub_self, abs_zero]
    positivity
  · have hh := (stab_out_mass_difference_raw h₁s h₂s le_rfl hv0 hv.2).1.trans
      ((lintegral_mono_set (show Ioc (0 : ℝ) v ⊆ Icc 0 T from
        fun t ht => ⟨ht.1.le, ht.2.trans hv.2⟩)).trans hforcing)
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    have hB : 0 ≤ 2 * ε * X + 40 * sigma e M T * ε * H := by positivity
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal hB, H, Δ] using! hreal

end EmcsfAcExtension.Local
