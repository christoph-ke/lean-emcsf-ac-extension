module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceOpticalIntegral
import EmcsfAcExtension.Local.Stability.FluxDifferenceRegularity

/-! # Optical exponent budgets on partial sections

Absolute flux estimates on complete sections control every exponent
used by the ordered optical comparison. The incoming partial interval
is `[0,u]` at fixed terminal label `v`.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- A complete outgoing absolute flux budget controls every outgoing
optical exponent difference, with universal coefficient `1`. -/
theorem stab_out_exponent_le_of_flux_bound
    {e T ε M A L : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hL : 0 ≤ L)
    (hbound : (⨆ u ∈ Icc 0 T, ∫⁻ s in Icc u T, ENNReal.ofReal
      |S₁.lam u s / S₁.r u s * ‖S₁.theta u s / (S₁.lam u s : ℂ)‖ ^ 2 -
        S₂.lam u s / S₂.r u s * ‖S₂.theta u s / (S₂.lam u s : ℂ)‖ ^ 2|) ≤ ENNReal.ofReal L) :
    ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      |(∫ s in u..v, S₁.lam u s / S₁.r u s * ‖S₁.theta u s / (S₁.lam u s : ℂ)‖ ^ 2) -
        ∫ s in u..v, S₂.lam u s / S₂.r u s * ‖S₂.theta u s / (S₂.lam u s : ℂ)‖ ^ 2| ≤ L := by
  intro u v hu huv hvT
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩
  have cf := (stab_out_quadratic_flux_continuous h₁s).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cg := (stab_out_quadratic_flux_continuous h₂s).comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  apply stab_optical_integral_sub_le_of_flux_bound huv hL
    (ContinuousOn.intervalIntegrable_of_Icc huv cf) (ContinuousOn.intervalIntegrable_of_Icc huv cg)
  exact (lintegral_mono_set (Icc_subset_Icc_right hvT)).trans
    ((le_iSup₂_of_le u ⟨hu, huv.trans hvT⟩ le_rfl).trans hbound)

/-- A complete incoming absolute flux budget controls every initial
cone-to-point exponent difference on `[0,u]`, with coefficient `1`.
The terminal label `v` and interval orientation are retained literally. -/
theorem stab_in_exponent_le_of_flux_bound
    {e T ε M A L : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hL : 0 ≤ L)
    (hbound : (⨆ v ∈ Icc 0 T, ∫⁻ s in Icc 0 v, ENNReal.ofReal
      |(-S₁.nu s v) / S₁.r s v * ‖S₁.xi s v / (S₁.nu s v : ℂ)‖ ^ 2 -
        (-S₂.nu s v) / S₂.r s v * ‖S₂.xi s v / (S₂.nu s v : ℂ)‖ ^ 2|) ≤ ENNReal.ofReal L) :
    ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      |(∫ s in 0..u, -S₁.nu s v / S₁.r s v * ‖S₁.xi s v / (S₁.nu s v : ℂ)‖ ^ 2) -
        ∫ s in 0..u, -S₂.nu s v / S₂.r s v * ‖S₂.xi s v / (S₂.nu s v : ℂ)‖ ^ 2| ≤ L := by
  intro u v hu huv hvT
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc 0 u) (triangle 0 T) :=
    fun s hs => ⟨hs.1, hs.2.trans huv, hvT⟩
  have cf := (stab_in_quadratic_flux_continuous h₁s).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  have cg := (stab_in_quadratic_flux_continuous h₂s).comp
    (continuous_id.prodMk continuous_const).continuousOn hmap
  apply stab_optical_integral_sub_le_of_flux_bound hu hL
    (ContinuousOn.intervalIntegrable_of_Icc hu cf) (ContinuousOn.intervalIntegrable_of_Icc hu cg)
  exact (lintegral_mono_set (Icc_subset_Icc_right huv)).trans
    ((le_iSup₂_of_le v ⟨hu.trans huv, hvT⟩ le_rfl).trans hbound)

end EmcsfAcExtension.Local
