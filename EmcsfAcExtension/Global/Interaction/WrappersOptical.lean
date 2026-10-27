module

public import EmcsfAcExtension.Global.Interaction.WrappersProfiles
public import EmcsfAcExtension.Global.Interaction.IncomingOpticalAssembly
public import EmcsfAcExtension.Global.Interaction.OutgoingOptics
import EmcsfAcExtension.Local.Api.Mono

/-! # Optical bounds with derived canonical charge control

The stopped scalar envelope and the core/boundary Maxwell closures
supply the canonical `M₀` and charge coefficient. The incoming estimate
exports the actual supremum over labels. Source:
`charged_SF_new_version.tex:L3610–L3619`, L3747–L3796.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global

open Interaction

/-- [node eq:ct-optical-out]
Outgoing expansion control on every full stopped row, with the actual
common envelope budget and canonical scalar background. The positive
coefficient depends only on the fixed geometry and stopping parameters,
before coupling, fields, `M₀`, radius scales, stages and duration. -/
theorem ct_optical_out_of_stopped (δ c Λ F ε ρ : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ : ℝ) (vb g en : ℝ → ℝ),
        a ≤ u₀ →
        StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        ∀ u ∈ Icc u₀ u₁,
          Real.log ((-S.nu u 0) / (-S.nu u (vb u))) ≤
            C * (S.m u (vb u) / S.r u (vb u) +
              ‖S.theta u (vb u) / S.lam u (vb u)‖ ^ 2 +
                (∫ v in v₀..0, g v) ^ 2 +
                  Local.sigma e (scalarBackground ui R₀ c F Jstop S) (2 * R₀)) := by
  obtain ⟨Cq, hCq, hprofiles⟩ := stopped_profiles
  obtain ⟨C, hC, hbound⟩ := ct_optical_out δ c F Cq hbox.1 hbox.2.2.1
    hbox.2.2.2.2.1 hbox.2.2.2.2.2.1 hCq.le
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hprof⟩ := hprofiles ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ vb g en hau d hbudget u hu
  have hb0 := (d.rows u hu).2.2.1
  have hv : (0 : ℝ) ∈ Icc (vb u) 0 := ⟨hb0, le_rfl⟩
  have hp := hprof u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hbudget u hu
  have hrow := d.exterior_segment hu hv
  have hSE := Local.isSolution_mono h.solution (D' := exteriorDomain ui u₀ u₁ vb)
    (fun p hp => hp.1)
  have hh := hbound e _ R₀ S _ u (vb u) 0 g hSE (d.rows u hu).2.1 hb0 hrow
    ((by norm_num : (0 : ℝ) ≤ 1).trans (hp 0 hv).1) d.radius_pos.le (d.annulus u hu).2
    (fun v hv => by
      have ht := d.stops (u, v) (d.row_mem hu hv)
      exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.2.1⟩)
    (fun v hv => (hp v hv).2.2) (d.row_integrable hu hv) (d.row_majorant hu hv)
  have hleft : IntervalIntegrable g volume v₀ (vb u) := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (d.rows u hu).2.2.2).mpr
    exact d.integrable.mono_set (Icc_subset_Icc le_rfl hb0)
  have hnleft := intervalIntegral.integral_nonneg_of_ae_restrict
    (d.rows u hu).2.2.2
    (d.nonneg.filter_mono (ae_mono
      (Measure.restrict_mono (Icc_subset_Icc le_rfl hb0) le_rfl)))
  have hnrow := intervalIntegral.integral_nonneg_of_ae_restrict hb0
    (d.nonneg.filter_mono (ae_mono
      (Measure.restrict_mono (Icc_subset_Icc (d.rows u hu).2.2.2 le_rfl) le_rfl)))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft (d.row_integrable hu hv)
  have hJ : (∫ v in vb u..0, g v) ≤ ∫ v in v₀..0, g v := by
    linarith only [hnleft, hadd]
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact add_le_add (add_le_add le_rfl (pow_le_pow_left₀ hnrow hJ 2)) le_rfl

namespace InteractionEstimate

/-- [node eq:ct-optical-in]
The supremum of the actual incoming positive optical histories.
The positive coefficient depends only on fixed geometry and stops,
including the connector ratio. It precedes coupling, canonical `M₀`,
radii, stage count and duration. Both profiles are derived; the stage
budgets are the actual cylinder/connector budgets, as in internal project record. -/
theorem ct_optical_in_of_stopped (δ c Λ F ε ρ : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ : ℝ) (vb g en : ℝ → ℝ)
        (N : ℕ) (B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N) (E : Fin N → ℝ),
        a ≤ u₀ →
        StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        BoundaryBudgets S ui u₀ u₁ v₀ ρ vb N B E →
        (⨆ v ∈ Icc v₀ 0,
          ∫⁻ u in {u | u ∈ Icc u₀ u₁ ∧ vb u ≤ v}, ENNReal.ofReal
            ((-S.nu u v) * S.mu u v / ((1 - S.mu u v) * S.r u v))) ≤
          ENNReal.ofReal (C * (∑ n, E n) + C * (∫ s in v₀..0, g s) ^ 2 +
            C * Local.sigma e (scalarBackground ui R₀ c F Jstop S) (2 * R₀)) := by
  obtain ⟨Cq, hCq, hprofiles⟩ := stopped_profiles
  obtain ⟨C, hC, hbound⟩ := ct_optical_in δ c Λ F ε ρ Cq hbox hCq.le
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hprof⟩ := hprofiles ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ vb g en N B E hau d hbudget hE
  have hp := hprof u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hbudget
  have h01 : u₀ ≤ u₁ := by
    calc
      _ = B.cuts 0 := B.first.symm
      _ ≤ B.cuts (Fin.last N) := B.ordered (Fin.zero_le _)
      _ = _ := B.last
  have hv0 : v₀ ≤ 0 := (d.rows u₀ ⟨le_rfl, h01⟩).2.2.2.trans
    (d.rows u₀ ⟨le_rfl, h01⟩).2.2.1
  apply iSup_le
  intro v
  apply iSup_le
  intro hv
  exact hbound e ui _ R₀ u₀ u₁ v₀ S vb g N B E h.solution hE d.stops
    ((by norm_num : (0 : ℝ) ≤ 1).trans (d.one_le_background h ⟨le_rfl, h01⟩))
    d.radius_pos.le (fun u hu => (d.annulus u hu).2)
    (fun p hp' => (hp p.1 ⟨hp'.2.1, hp'.2.2.1⟩ p.2
      ⟨hp'.2.2.2, hp'.1.2.2.2⟩).2.2)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hv0).mpr d.integrable)
    d.nonneg (fun u hu => d.row_majorant hu ⟨(d.rows u hu).2.2.1, le_rfl⟩) v hv

end InteractionEstimate

end EmcsfAcExtension.Global
