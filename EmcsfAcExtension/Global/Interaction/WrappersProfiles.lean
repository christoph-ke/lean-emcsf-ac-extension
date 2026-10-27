module

public import EmcsfAcExtension.Global.Interaction.ClosuresProfiles
import EmcsfAcExtension.Local.Api.Mono

/-! # Canonical profiles for the interaction source setting

Only stopped geometry, the incoming label envelope and boundary mass
budgets enter this interface. The scalar profile follows from `ct_m0`;
the core scalar and Maxwell closures in `ct_charge_profile` supply the
charge profile. Source: `charged_SF_new_version.tex:L3317–L3360`.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Interaction

variable {ui e u₀ u₁ v₀ R₀ δ c Λ F ε Jstop : ℝ}
  {S : Fields} {vb g : ℝ → ℝ}

/-- [internal] Every stopped row segment is in the exterior source domain. -/
theorem StoppedProfileData.exterior_segment
    (d : StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g)
    {u v : ℝ} (hu : u ∈ Icc u₀ u₁) (hv : v ∈ Icc (vb u) 0) :
    outSeg u (vb u) v ⊆ exteriorDomain ui u₀ u₁ vb := by
  rintro ⟨x, y⟩ ⟨rfl, hy⟩
  exact d.row_mem hu ⟨hy.1, hy.2.trans hv.2⟩

/-- [internal] The common envelope is integrable on every truncated row. -/
theorem StoppedProfileData.row_integrable
    (d : StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g)
    {u v : ℝ} (hu : u ∈ Icc u₀ u₁) (hv : v ∈ Icc (vb u) 0) :
    IntervalIntegrable g volume (vb u) v := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hv.1).mpr
  exact d.integrable.mono_set (Icc_subset_Icc (d.rows u hu).2.2.2 hv.2)

/-- [internal] Restrict the common a.e. majorant to a truncated row. -/
theorem StoppedProfileData.row_majorant
    (d : StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g)
    {u v : ℝ} (hu : u ∈ Icc u₀ u₁) (hv : v ∈ Icc (vb u) 0) :
    ∀ᵐ x ∂volume.restrict (Icc (vb u) v), ‖weightedJ S u x‖ ≤ g x := by
  have hm := (d.majorant u hu).filter_mono (ae_mono
    (Measure.restrict_mono (Icc_subset_Icc (d.rows u hu).2.2.2 hv.2) le_rfl))
  filter_upwards [hm, ae_restrict_mem measurableSet_Icc] with x hx hxm
  exact hx hxm.1

/-- [internal] The canonical scalar and charge bounds from stopped data.
The universal charge coefficient is selected before the coupling, fields,
`Jstop`, and late entry. No scalar or charge estimate is a premise. -/
theorem stopped_profiles :
    ∃ Cq : ℝ, 0 < Cq ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ δ c Λ F ε : ℝ) (vb g en : ℝ → ℝ),
        a ≤ u₀ →
        StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc (vb u) 0,
          1 ≤ scalarBackground ui R₀ c F Jstop S ∧
          ‖S.phi u v‖ ≤ scalarBackground ui R₀ c F Jstop S ∧
          |S.Q u v| / S.r u v ^ 2 ≤
            Cq * |e| * scalarBackground ui R₀ c F Jstop S * F := by
  obtain ⟨Cq, hCq, hcharge⟩ := ct_charge_profile
  refine ⟨Cq, hCq, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hq⟩ := hcharge ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hbudget u hu v hv
  have hQ := hq u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hbudget u hu v hv
  exact ⟨d.one_le_background h hu, ct_m0 h d (u, v) (d.row_mem hu hv),
    hQ.1.trans hQ.2⟩

end EmcsfAcExtension.Global.Interaction
