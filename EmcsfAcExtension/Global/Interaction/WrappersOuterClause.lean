module

public import EmcsfAcExtension.Global.Interaction.WrappersCost

/-! # Mixed electromagnetic cost with its outer outgoing clause

The inverse-cube kernel retains the cubic radius and incoming-label
envelope, with exact coefficient `1 / (c * (2 - ε))`. It is exported
together with the full mixed cost, using the same constant and late entry.
Source: `charged_SF_new_version.tex:L3737–L3743`; repair of internal project record.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.InteractionEstimate

open Interaction

private theorem mixed_outer_clause {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u s b c ε q : ℝ}
    (hus : u < s) (hsb : s ≤ b) (hseg : outSeg u s b ⊆ D)
    (hc : 0 < c) (hε : ε < 2) (hq : 0 ≤ q)
    (hlam : ∀ v ∈ Icc s b, c ≤ S.lam u v)
    (hmu : ∀ v ∈ Icc s b, S.mu u v / (1 - S.mu u v) ≤ ε) :
    ENNReal.ofReal (S.r u s ^ 3 * q) *
        (∫⁻ v in Icc s b, ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3)) ≤
      ENNReal.ofReal ((-S.nu u s) * S.r u s * q / (c * (2 - ε))) := by
  have hr := hS.r_pos (u, s) (hseg ⟨rfl, le_rfl, hsb⟩) hus
  have hi := outgoing_inverse_cube_kernel hS hus hsb hseg hc hε hlam hmu
  calc
    _ ≤ ENNReal.ofReal (S.r u s ^ 3 * q) *
        ENNReal.ofReal ((-S.nu u s) / (c * (2 - ε) * S.r u s ^ 2)) :=
      mul_le_mul le_rfl hi (by positivity) (by positivity)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ S.r u s ^ 3 * q)]
      congr 1
      field_simp [hr.ne', hc.ne', (sub_pos.mpr hε).ne']

/-- [node prop:ct-interaction#electromagnetic-mixed-cost]
The mixed electric cost `C ζ² F² J` and the outer-`v` estimate with exact
coefficient `1 / (c * (2 - ε))`, on every stopped row and a.e. incoming
label. The positive cost coefficient depends only on fixed geometry and
stops, before coupling, canonical `M₀`, radii, envelope, stage count and
duration. The late entry is chosen after `Jstop`, before the stopped data.
The outer coefficient depends only on `c, ε`; no profile is assumed. -/
theorem electromagnetic_mixed_cost_with_outer_clause_of_stopped (δ c Λ F ε ρ : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ : ℝ) (vb g en : ℝ → ℝ)
        (N : ℕ) (_B : FiniteBoundary S ui u₀ u₁ v₀ ρ vb N),
        a ≤ u₀ →
        StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        ((∫⁻ u in Icc u₀ u₁, ∫⁻ v in Icc (vb u) 0,
          ENNReal.ofReal ‖curvatureScalarSource S u v (S.theta u v / S.lam u v)
            (radialCurvatureWith S u (vb u) v (radialZEM e S u (vb u)))‖) ≤
          ENNReal.ofReal (C * Local.sigma e (scalarBackground ui R₀ c F Jstop S) (2 * R₀) *
            F ^ 2 * (∫ s in v₀..0, g s))) ∧
        (∀ u ∈ Icc u₀ u₁, ∀ᵐ s ∂volume.restrict (Icc (vb u) 0),
          ENNReal.ofReal (S.r u s ^ 3 * g s) *
              (∫⁻ v in Icc s 0, ENNReal.ofReal ((-S.nu u v) / S.r u v ^ 3)) ≤
            ENNReal.ofReal ((-S.nu u s) * S.r u s * g s / (c * (2 - ε)))) := by
  obtain ⟨C, hC, hcost⟩ := electromagnetic_mixed_cost_of_stopped δ c Λ F ε ρ hbox
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hbound⟩ := hcost ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ vb g en N B hau d hbudget
  refine ⟨hbound u₀ u₁ v₀ R₀ vb g en N B hau d hbudget, ?_⟩
  intro u hu
  have hε : ε < 2 := by
    have hp := (le_max_left ε (1 / 2)).trans_lt hbox.2.2.2.2.2.2.2.1
    linarith only [hp, sq_nonneg F]
  have hg := d.nonneg.filter_mono (ae_mono
    (Measure.restrict_mono (Icc_subset_Icc (d.rows u hu).2.2.2 le_rfl) le_rfl))
  filter_upwards [hg, ae_restrict_mem measurableSet_Icc] with s hgs hsm
  have hseg : outSeg u s 0 ⊆ exteriorDomain ui u₀ u₁ vb := by
    rintro ⟨x, v⟩ ⟨rfl, hv⟩
    exact d.row_mem hu ⟨hsm.1.trans hv.1, hv.2⟩
  have hst (v : ℝ) (hv : v ∈ Icc s 0) := d.stops (u, v) (hseg ⟨rfl, hv⟩)
  exact mixed_outer_clause h.solution ((d.rows u hu).2.1.trans_le hsm.1) hsm.2
    (fun p hp => (hseg hp).1) d.expansion_pos hε hgs
    (fun v hv => (hst v hv).2.2.1) (fun v hv => (hst v hv).2.2.2.2.2.1)

end EmcsfAcExtension.Global.InteractionEstimate
