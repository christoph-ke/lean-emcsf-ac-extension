module

public import EmcsfAcExtension.Global.Interaction.WrappersProfiles
public import EmcsfAcExtension.Global.Interaction.ElectricArea
public import EmcsfAcExtension.Global.Interaction.ElectricMixed
public import EmcsfAcExtension.Global.Interaction.IncomingOptics
import EmcsfAcExtension.Local.Api.Mono

/-! # Interaction source bounds from the stopped envelope

The canonical scalar background and geometric charge coefficient are
produced by the landed scalar/core/Maxwell closures before applying the
algebraic and radial estimates. Source: `charged_SF_new_version.tex:L3706–L3751`.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global

open Interaction

/-- [node eq:ct-source-pointwise]
The weighted Maxwell remainder from the recorded stopped source setting.
The positive coefficient depends only on the fixed geometry and stops,
before coupling, fields, canonical `M₀`, radius scale, and duration.
`Jstop` precedes the late entry. Both profiles are derived. -/
theorem ct_source_pointwise_of_stopped (δ c Λ F ε ρ : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ : ℝ) (vb g en : ℝ → ℝ),
        a ≤ u₀ →
        StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc (vb u) 0,
          ‖((S.lam u v / (1 - S.mu u v) : ℝ) : ℂ) * Local.emSourceJ e S u v‖ ≤
            C * e ^ 2 * (scalarBackground ui R₀ c F Jstop S) ^ 2 * F *
              (-S.nu u v) * S.lam u v ^ 2 := by
  obtain ⟨Cq, hCq, hprofiles⟩ := stopped_profiles
  obtain ⟨C, hC, hbound⟩ := ct_source_pointwise δ F Cq hbox.1 hbox.2.2.2.2.1 hCq.le
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hprof⟩ := hprofiles ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ vb g en hau d hbudget u hu v hv
  have hp := hprof u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hbudget
  have hm := d.row_mem hu hv
  have ht := d.stops (u, v) hm
  exact hbound e _ S u v
    (h.solution.r_pos (u, v) hm.1 ((d.rows u hu).2.1.trans_le hv.1))
    (h.solution.lam_pos (u, v) hm.1)
    (neg_pos.mpr (h.solution.nu_neg (u, v) hm.1)).le ht.2.1
    (hp u hu v hv).1 (hp u hu v hv).2.1 ht.2.2.2.2.1 (hp u hu v hv).2.2

namespace InteractionEstimate

/-- [node prop:ct-interaction#electromagnetic-mixed-source]
The mixed electric curvature source, retaining its cubic radial moment.
The positive coefficient depends only on fixed geometric stops, before
coupling, canonical `M₀`, radii, stages and duration. Scalar and charge
profiles are produced from the envelope, core and boundary hypotheses. -/
theorem electromagnetic_mixed_source_of_stopped (δ c Λ F ε ρ : ℝ)
    (hbox : ExteriorBox δ c Λ F ε ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ : ℝ) (vb g en : ℝ → ℝ),
        a ≤ u₀ →
        StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc (vb u) 0,
          ‖curvatureScalarSource S u v (S.theta u v / S.lam u v)
            (radialCurvatureWith S u (vb u) v (radialZEM e S u (vb u)))‖ ≤
            C * e ^ 2 * (scalarBackground ui R₀ c F Jstop S) ^ 2 * F ^ 2 *
              ((-S.nu u v) / S.r u v ^ 3) *
                (∫ s in vb u..v, S.r u s ^ 3 * g s) := by
  obtain ⟨Cq, hCq, hprofiles⟩ := stopped_profiles
  obtain ⟨C, hC, hbound⟩ := electromagnetic_mixed_source δ c Λ Cq hbox.1
    hbox.2.2.1 (hbox.2.2.1.trans_le hbox.2.2.2.1) hCq.le
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hprof⟩ := hprofiles ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ vb g en hau d hbudget u hu v hv
  have hp := hprof u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hbudget
  have hrow := d.exterior_segment hu hv
  have hSE := Local.isSolution_mono h.solution (D' := exteriorDomain ui u₀ u₁ vb)
    (fun p hp => hp.1)
  exact hbound e _ F ε S _ u (vb u) v g hSE d.stops (d.rows u hu).2.1 hv.1 hrow
    ((by norm_num : (0 : ℝ) ≤ 1).trans (hp u hu v hv).1) d.scalar_nonneg
    (fun x hx => (hp u hu x ⟨hx.1, hx.2.trans hv.2⟩).2.1)
    (fun x hx => (hp u hu x ⟨hx.1, hx.2.trans hv.2⟩).2.2)
    (d.row_integrable hu hv) (d.row_majorant hu hv)

/-- [node prop:ct-interaction#radial-mass-reconstruction]
The ordinary radial mass bound with the recorded one-half scalar
coefficient and cubic electric remainder. Its positive coefficient is
universal, before coupling, canonical `M₀`, all stops and physical scales.
The charge premise of the radial helper is discharged by the closures. -/
theorem radial_mass_reconstruction_of_stopped :
    ∃ C : ℝ, 0 < C ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ δ c Λ F ε : ℝ) (vb g en : ℝ → ℝ),
        a ≤ u₀ →
        StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc (vb u) 0,
          S.m u v ≤ S.m u (vb u) +
            (1 / 2) * (∫ x in vb u..v, S.lam u x * ‖S.theta u x / S.lam u x‖ ^ 2) +
              C * e ^ 2 * (scalarBackground ui R₀ c F Jstop S) ^ 2 * F ^ 2 * S.r u v ^ 3 := by
  obtain ⟨Cq, hCq, hprofiles⟩ := stopped_profiles
  obtain ⟨C, hC, hbound⟩ := radial_mass_reconstruction Cq hCq.le
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hprof⟩ := hprofiles ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hbudget u hu v hv
  have hp := hprof u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hbudget
  have hrow := d.exterior_segment hu hv
  have hSE := Local.isSolution_mono h.solution (D' := exteriorDomain ui u₀ u₁ vb)
    (fun p hp => hp.1)
  exact hbound e _ F S _ u (vb u) v hSE (d.rows u hu).2.1 hv.1 hrow
    ((by norm_num : (0 : ℝ) ≤ 1).trans (hp u hu v hv).1) d.scalar_nonneg
    (fun x hx => (d.stops (u, x) (hrow ⟨rfl, hx⟩)).1)
    (fun x hx => (hp u hu x ⟨hx.1, hx.2.trans hv.2⟩).2.2)

end InteractionEstimate

end EmcsfAcExtension.Global
