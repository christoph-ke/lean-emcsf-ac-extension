module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Bounds
import EmcsfAcExtension.Local.Stability.PotentialStrongRaw
import EmcsfAcExtension.Local.Stability.PotentialSourceArea
import EmcsfAcExtension.Local.Stability.PotentialSourceBounds
import EmcsfAcExtension.Local.Stability.ExtendedMain

/-! # Strong classical potential comparison in both characteristic directions

A11p gives the incoming derivative as an actual primitive of its source.
The outgoing constraint is subtracted directly. Both complete-section
L¹ comparisons keep the exact coupling, background and time scale.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [internal]
The ordinary potential partials satisfy the strong pair estimate from
the full extended record. The positive coefficient depends only on
`A,C`, before all fields, data, coupling, time and background, uniformly
in higher derivative suprema and minimum radii. This `_of_` helper is
local to classical inputs; the full general-AC node belongs to internal project record. -/
theorem Stab.potential_characteristic_strong_of_stab_bounds_c1
    (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ 1 / 4 → StabBounds C e T M (dataDist h₁ h₂ T) S₁ S₂ →
      (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
        ‖pdV (triangle 0 T) S₁.A u v - pdV (triangle 0 T) S₂.A u v‖ₑ) +
      (⨆ v ∈ Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖pdU (triangle 0 T) S₁.A u v - pdU (triangle 0 T) S₂.A u v‖ₑ) ≤
          ENNReal.ofReal (K * |e| * M * T * dataDist h₁ h₂ T) := by
  obtain ⟨Ks, hKs, hSource⟩ := stab_potential_source_area_of_stab_bounds_c1 A C hA hC
  refine ⟨384 * C + Ks, by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ h₁s h₂s hsmall hb
  let Δ := dataDist h₁ h₂ T
  have hΔ : 0 ≤ Δ := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hT : 0 ≤ T := h₁s.pos.le
  have hσ : 0 ≤ sigma e M T := by dsimp only [sigma]; positivity
  have hε : ε ≤ 1 := by nlinarith only [hsmall, hσ, sq_nonneg (ε - 1)]
  obtain ⟨H₁, H₂, cH₁, cH₂, heq₁, heq₂, hInRaw⟩ :=
    stab_potential_incoming_difference_le_area_c1 h₁s h₂s
  have hIn := hInRaw.trans (hSource T e ε M S₁ S₂ h₁ h₂ H₁ H₂ h₁s h₂s hsmall hb heq₁ heq₂)
  have hOut : (⨆ u ∈ Icc 0 T, ∫⁻ v in Icc u T,
      ‖pdV (triangle 0 T) S₁.A u v - pdV (triangle 0 T) S₂.A u v‖ₑ) ≤
        ENNReal.ofReal (384 * C * |e| * M * T * Δ) := by
    apply iSup₂_le
    intro u hu
    have hn : ∀ᵐ v : ℝ, v ≠ u := by simp [ae_iff, measure_singleton]
    have hp : ∀ᵐ v ∂volume.restrict (Icc u T),
        ‖pdV (triangle 0 T) S₁.A u v - pdV (triangle 0 T) S₂.A u v‖ₑ ≤
          ENNReal.ofReal (384 * C * |e| * M * Δ) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hn] with v hv hne
      have huv := lt_of_le_of_ne hv.1 hne.symm
      have htri : (u, v) ∈ triangle 0 T := ⟨hu.1, hv.1, hv.2⟩
      rw [(h₁s.c1.eq_v (u, v) htri huv).2.2.2.2.1,
        (h₂s.c1.eq_v (u, v) htri huv).2.2.2.2.1, ← ofReal_norm, Real.norm_eq_abs]
      exact ENNReal.ofReal_le_ofReal
        (stab_potential_constraint_sub_le_of_stab_bounds_c1 hC h₁s h₂s hε hb hu.1 huv hv.2)
    apply (lintegral_mono_ae hp).trans
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (384 * C * |e| * M * Δ) * T := by gcongr; exact sub_le_self T hu.1
      _ = _ := by ring
  apply (add_le_add hOut hIn).trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  dsimp only [Δ]
  ring

end EmcsfAcExtension.Local
