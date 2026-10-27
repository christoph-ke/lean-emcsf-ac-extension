module

public import EmcsfAcExtension.Local.Limit.Inputs
import EmcsfAcExtension.Local.Limit.AcBridgeDerivative
import EmcsfAcExtension.Local.Stability.PotentialStrong
import EmcsfAcExtension.Local.Stability.GeomStrongMassDerivatives
import EmcsfAcExtension.Local.Stability.GeomStrongCauchy
import EmcsfAcExtension.Local.Stability.GeomStrongSectionC1
import EmcsfAcExtension.Local.Calculus.Partials

/-! # Ordinary smooth mass and potential comparisons for the AC bridge

These are local smooth inputs, preceding the full general-AC nodes.
The incoming potential comparison uses the proved triangular source
estimate, with its literal coupling, background and time factors.
-/

public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Ordinary derivatives equal triangle partials a.e. on each complete real
C¹ section, in both directions. There is no exceptional set of labels. -/
theorem real_c1_deriv_ae_partial {T : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T)) :
    (∀ u ∈ Icc 0 T, deriv (f u) =ᵐ[volume.restrict (Icc u T)] pdV (triangle 0 T) f u) ∧
    (∀ v ∈ Icc 0 T, deriv (fun u => f u v) =ᵐ[volume.restrict (Icc 0 v)]
      fun u => pdU (triangle 0 T) f u v) := by
  constructor
  · intro u hu
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    exact deriv_eq_pdV hf ⟨hu.1,hv.1.le,hv.2.le⟩
      (s := Icc u T) (fun x hx => ⟨hu.1,hx.1,hx.2⟩) (Icc_mem_nhds hv.1 hv.2)
  · intro v hv
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact deriv_eq_pdU hf ⟨hu.1.le,hu.2.le,hv.2⟩
      (s := Icc 0 v) (fun x hx => ⟨hx.1,hx.2,hv.2⟩) (Icc_mem_nhds hu.1 hu.2)

/-- Local smooth potential comparison for ordinary derivatives, including the
incoming direction. The positive coefficient depends only on the fixed `A,C`,
before all solution parameters; the scale is exactly `|e|MT`. -/
theorem potential_ordinary_pair_of_stab_bounds_c1 (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ 1 / 4 → StabBounds C e T M (dataDist h₁ h₂ T) S₁ S₂ →
      (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ‖deriv (S₁.A u) v - deriv (S₂.A u) v‖ₑ) +
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖deriv (fun s => S₁.A s v) u - deriv (fun s => S₂.A s v) u‖ₑ) ≤
          ENNReal.ofReal (K * |e| * M * T * dataDist h₁ h₂ T) := by
  obtain ⟨K,hK,hpair⟩ := Stab.potential_characteristic_strong_of_stab_bounds_c1 A C hA hC
  refine ⟨K,hK,?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall hb
  have ho : (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ‖deriv (S₁.A u) v - deriv (S₂.A u) v‖ₑ) =
      ⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
        ‖pdV (triangle 0 T) S₁.A u v - pdV (triangle 0 T) S₂.A u v‖ₑ := by
    apply iSup_congr; intro u
    apply iSup_congr; intro hu
    apply lintegral_congr_ae
    filter_upwards [(real_c1_deriv_ae_partial hs₁.c1.c1_A).1 u hu,
      (real_c1_deriv_ae_partial hs₂.c1.c1_A).1 u hu] with v hv₁ hv₂
    rw [hv₁,hv₂]
  have hi : (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
      ‖deriv (fun s => S₁.A s v) u - deriv (fun s => S₂.A s v) u‖ₑ) =
      ⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖pdU (triangle 0 T) S₁.A u v - pdU (triangle 0 T) S₂.A u v‖ₑ := by
    apply iSup_congr; intro v
    apply iSup_congr; intro hv
    apply lintegral_congr_ae
    filter_upwards [(real_c1_deriv_ae_partial hs₁.c1.c1_A).2 v hv,
      (real_c1_deriv_ae_partial hs₂.c1.c1_A).2 v hv] with u hu₁ hu₂
    rw [hu₁,hu₂]
  rw [ho,hi]
  exact hpair T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall hb

/-- Supply both smooth mass and ordinary potential derivative comparisons.
The positive thresholds and coefficients depend only on the fixed comparison
input and box, before time, coupling, size, data or derivative suprema. The
potential's dimensional scale is retained; no new standing input is introduced. -/
theorem smooth_mass_potential_pairs_of_inputs (hstab : StabExtendedStmt) :
    ∃ η C K : ℝ, 0 < η ∧ 0 < C ∧ 0 < K ∧
      ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
        StabSetting e T ε M 1 S₁ h₁ → StabSetting e T ε M 1 S₂ h₂ →
        ε ^ 2 + sigma e M T ≤ η →
        ((⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ‖deriv (S₁.mu u) v - deriv (S₂.mu u) v‖ₑ) +
          (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
            ‖deriv (fun s => S₁.mu s v) u - deriv (fun s => S₂.mu s v) u‖ₑ) ≤
              ENNReal.ofReal (C * dataDist h₁ h₂ T)) ∧
        ((⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T, ‖deriv (S₁.A u) v - deriv (S₂.A u) v‖ₑ) +
          (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
            ‖deriv (fun s => S₁.A s v) u - deriv (fun s => S₂.A s v) u‖ₑ) ≤
              ENNReal.ofReal (K * |e| * M * T * dataDist h₁ h₂ T)) := by
  obtain ⟨η,C₀,hη,hC₀,hcomp⟩ := hstab 1 (by norm_num)
  obtain ⟨ηm,C,hηm,hC,hm⟩ := Stab.mass_derivatives_strong_of_main_lipschitz_c1 1 C₀ (by norm_num)
      hC₀
  obtain ⟨K,hK,hp⟩ := potential_ordinary_pair_of_stab_bounds_c1 1 C₀ (by norm_num) hC₀
  refine ⟨min η (min ηm (1/4)),C,K,lt_min hη (lt_min hηm (by norm_num)),hC,hK,?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall
  have hb := hcomp T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ (hsmall.trans (min_le_left _ _))
  exact ⟨hm T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (le_self_add.trans (le_self_add.trans (le_self_add.trans hb.main))),
    hp T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
      (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))) hb⟩

end EmcsfAcExtension.Local
