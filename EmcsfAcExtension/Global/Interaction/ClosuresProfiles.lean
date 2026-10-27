module

public import EmcsfAcExtension.Global.Interaction.ClosuresScalar
public import EmcsfAcExtension.Global.Interaction.ClosuresCore
public import EmcsfAcExtension.Global.Interaction.ClosuresCharge
public import EmcsfAcExtension.Global.Interaction.ClosuresChargeProfile
public import EmcsfAcExtension.Global.Interaction.ClosuresElectromagnetic
import EmcsfAcExtension.Global.Gap.LateMain
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Core and electromagnetic profile closures

All scalar profiles are derived from the finite exterior envelope. The core
gap is obtained from the signed terminal hypothesis, uniformly on a late
triangle. Constants precede the solution, coupling, stopping budget, and
late entry. Source: `charged_SF_new_version.tex:L3325–L3360`, L3403–L3405.
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Interaction

variable {ui e u₀ u₁ v₀ R₀ δ c Λ F ε Jstop : ℝ}
  {S : Fields} {vb g : ℝ → ℝ}

/-- [internal] A stopped row is a proper complete original outgoing cone. -/
theorem StoppedProfileData.core_segment
    (d : StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g)
    {u : ℝ} (hu : u ∈ Icc u₀ u₁) : outSeg u u 0 ⊆ origDomain ui := by
  obtain ⟨hui, hub, hb0, _⟩ := d.rows u hu
  rintro ⟨x, y⟩ ⟨rfl, hy⟩
  exact ⟨hui, hub.trans_le hb0, hy.1, hy.2⟩

/-- [internal] Every exterior row point lies in the stopped exterior. -/
theorem StoppedProfileData.row_mem
    (d : StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g)
    {u v : ℝ} (hu : u ∈ Icc u₀ u₁) (hv : v ∈ Icc (vb u) 0) :
    (u, v) ∈ exteriorDomain ui u₀ u₁ vb := by
  refine ⟨d.core_segment hu ⟨rfl, ?_, hv.2⟩, hu.1, hu.2, hv.1⟩
  exact (d.rows u hu).2.1.le.trans hv.1

/-- [internal] The literal `M₀` is at least one, from the nonnegative
envelope and the terminal supremum. No scalar bound is assumed. -/
theorem StoppedProfileData.one_le_background (h : OriginalData ui e S)
    (d : StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g)
    {u : ℝ} (hu : u ∈ Icc u₀ u₁) :
    1 ≤ scalarBackground ui R₀ c F Jstop S := by
  obtain ⟨hui, hub, hb0, hvb⟩ := d.rows u hu
  have hsup : 0 ≤ terminalScalarSup ui R₀ S :=
    (norm_nonneg _).trans (terminal_scalar_le_sup h d.radius_pos
      ⟨hui, hub.trans_le hb0⟩ (d.annulus u hu))
  have hJ : 0 ≤ Jstop :=
    (intervalIntegral.integral_nonneg_of_ae_restrict (hvb.trans hb0) d.nonneg).trans d.budget
  have hp : 0 < 1 - F ^ 2 := by
    nlinarith only [d.scalar_nonneg, d.scalar_lt_one, sq_nonneg (F - 1)]
  have hq : 0 ≤ (F + c⁻¹ * Jstop) / (1 - F ^ 2) :=
    div_nonneg (add_nonneg d.scalar_nonneg
      (mul_nonneg (inv_nonneg.mpr d.expansion_pos.le) hJ)) hp.le
  dsimp [scalarBackground]
  linarith only [hsup, hq]

end EmcsfAcExtension.Global.Interaction

namespace EmcsfAcExtension.Global

/-- [node sec:charged-terminal-interaction#core-scalar-growth]
The core scalar bound from the exterior envelope, charged_SF_new_version.tex:L3325–L3333.
The gap `gapConstant / 2` is universal. `Jstop` is fixed before the late
entry; no derivative bound in the excluded core is assumed. -/
theorem Interaction.core_scalar_growth {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (Jstop : ℝ) :
    ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ δ c Λ F ε : ℝ) (vb g : ℝ → ℝ),
      a ≤ u₀ →
      Interaction.StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
      ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Ioc u (vb u),
        ‖S.phi u v‖ ≤ ‖S.phi u (vb u)‖ +
            Real.sqrt (∫ x in v..vb u, S.lam u x * (1 - S.mu u x) *
              ‖S.theta u x / S.lam u x‖ ^ 2) *
            Real.sqrt (∫ x in v..vb u,
              S.lam u x / ((1 - S.mu u x) * S.r u x ^ 2)) ∧
          ‖S.phi u (vb u)‖ +
            Real.sqrt (∫ x in v..vb u, S.lam u x * (1 - S.mu u x) *
              ‖S.theta u x / S.lam u x‖ ^ 2) *
            Real.sqrt (∫ x in v..vb u,
              S.lam u x / ((1 - S.mu u x) * S.r u x ^ 2)) ≤
          Interaction.scalarBackground ui R₀ c F Jstop S +
          Real.sqrt (2 * S.m u (vb u) / ((gapConstant / 2) * S.r u v)) := by
  obtain ⟨a, ha, hgap⟩ := Gap.late_gap_application ui e S h hs
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ δ c Λ F ε vb g hau d u hu v hv
  have hcore : outSeg u u (vb u) ⊆ origDomain ui := fun p hp =>
    d.core_segment hu ⟨hp.1, hp.2.1, hp.2.2.trans (d.rows u hu).2.2.1⟩
  exact Interaction.core_scalar_growth_chain_of_boundary_bound h.solution hv.1 hv.2 hcore
    (by unfold gapConstant; positivity)
    (fun x hx => (hgap (u, x) (hcore ⟨rfl, hx⟩) (hau.trans hu.1)).1)
    (ct_m0 h d (u, vb u) (d.row_mem hu ⟨le_rfl, (d.rows u hu).2.2.1⟩))

/-- [node eq:ct-boundary-charge-square]
The boundary charge-square estimate derived from the exterior envelope,
charged_SF_new_version.tex:L3334–L3343. The constant depends only on the universal
full-core gap, before the coupling, solution and `Jstop`. -/
theorem ct_boundary_charge_square :
    ∃ C : ℝ, 0 < C ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ δ c Λ F ε : ℝ) (vb g : ℝ → ℝ),
        a ≤ u₀ →
        Interaction.StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        ∀ u ∈ Icc u₀ u₁, S.Q u (vb u) ^ 2 ≤ e ^ 2 *
            (∫ x in u..vb u, S.lam u x * (1 - S.mu u x) * ‖S.theta u x / S.lam u x‖ ^ 2) *
            (∫ x in u..vb u, S.lam u x * S.r u x ^ 2 * ‖S.phi u x‖ ^ 2 / (1 - S.mu u x)) ∧
          e ^ 2 *
            (∫ x in u..vb u, S.lam u x * (1 - S.mu u x) * ‖S.theta u x / S.lam u x‖ ^ 2) *
            (∫ x in u..vb u, S.lam u x * S.r u x ^ 2 * ‖S.phi u x‖ ^ 2 / (1 - S.mu u x)) ≤
          C * e ^ 2 * S.m u (vb u) *
          ((Interaction.scalarBackground ui R₀ c F Jstop S) ^ 2 * S.r u (vb u) ^ 3 +
            S.m u (vb u) * S.r u (vb u) ^ 2) := by
  have hδ : 0 < gapConstant / 2 := by unfold gapConstant; positivity
  have hδ1 : gapConstant / 2 ≤ 1 := by
    have he := Real.exp_le_one_iff.mpr (by norm_num : (-32 : ℝ) ≤ 0)
    unfold gapConstant
    linarith only [he]
  obtain ⟨C, hC, hbound⟩ := ct_boundary_charge_square_chain_of_boundary_bound _ hδ hδ1
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hgap⟩ := Gap.late_gap_application ui e S h hs
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ δ c Λ F ε vb g hau d u hu
  have hcore : outSeg u u (vb u) ⊆ origDomain ui := fun p hp =>
    d.core_segment hu ⟨hp.1, hp.2.1, hp.2.2.trans (d.rows u hu).2.2.1⟩
  exact hbound e _ S _ u (vb u) h.solution (d.rows u hu).2.1 hcore
    (fun x hx => (hgap (u, x) (hcore ⟨rfl, hx⟩) (hau.trans hu.1)).1)
    (ct_m0 h d (u, vb u) (d.row_mem hu ⟨le_rfl, (d.rows u hu).2.2.1⟩))

/-- [node eq:ct-boundary-charge]
Normalized boundary charge, charged_SF_new_version.tex:L3344–L3349. The constant
depends only on the full-core gap, before all solution data and `Jstop`.
The scalar bound is discharged from its finite exterior envelope. -/
theorem ct_boundary_charge :
    ∃ C : ℝ, 0 < C ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ δ c Λ F ε : ℝ) (vb g : ℝ → ℝ),
        a ≤ u₀ →
        Interaction.StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        ∀ u ∈ Icc u₀ u₁, |S.Q u (vb u)| / S.r u (vb u) ^ 2 ≤ C * |e| *
          (Interaction.scalarBackground ui R₀ c F Jstop S *
              Real.sqrt (S.m u (vb u) / S.r u (vb u)) +
            S.m u (vb u) / S.r u (vb u)) := by
  have hδ : 0 < gapConstant / 2 := by unfold gapConstant; positivity
  have hδ1 : gapConstant / 2 ≤ 1 := by
    have he := Real.exp_le_one_iff.mpr (by norm_num : (-32 : ℝ) ≤ 0)
    unfold gapConstant
    linarith only [he]
  obtain ⟨C, hC, hbound⟩ := ct_boundary_charge_of_boundary_bound _ hδ hδ1
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hgap⟩ := Gap.late_gap_application ui e S h hs
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ δ c Λ F ε vb g hau d u hu
  have hcore : outSeg u u (vb u) ⊆ origDomain ui := fun p hp =>
    d.core_segment hu ⟨hp.1, hp.2.1, hp.2.2.trans (d.rows u hu).2.2.1⟩
  exact hbound e _ S _ u (vb u) h.solution (d.rows u hu).2.1 hcore
    (fun x hx => (hgap (u, x) (hcore ⟨rfl, hx⟩) (hau.trans hu.1)).1)
    (ct_m0 h d (u, vb u) (d.row_mem hu ⟨le_rfl, (d.rows u hu).2.2.1⟩))

/-- [node eq:ct-charge-profile]
The exterior charge bound from the scalar envelope and stage mass budget,
charged_SF_new_version.tex:L3350–L3360. The constant depends only on the full-core gap,
before all solution data, stopping parameters, and late choices. -/
theorem ct_charge_profile :
    ∃ C : ℝ, 0 < C ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ δ c Λ F ε : ℝ) (vb g en : ℝ → ℝ),
        a ≤ u₀ →
        Interaction.StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc (vb u) 0,
          |S.Q u v| / S.r u v ^ 2 ≤ C * |e| *
              Interaction.scalarBackground ui R₀ c F Jstop S * F *
                (S.r u (vb u) / S.r u v) ^ 2 +
              (|e| * Interaction.scalarBackground ui R₀ c F Jstop S * F / S.r u v ^ 2) *
                (∫ x in vb u..v, S.lam u x * S.r u x) ∧
            C * |e| * Interaction.scalarBackground ui R₀ c F Jstop S * F *
                (S.r u (vb u) / S.r u v) ^ 2 +
              (|e| * Interaction.scalarBackground ui R₀ c F Jstop S * F / S.r u v ^ 2) *
                (∫ x in vb u..v, S.lam u x * S.r u x) ≤
              C * |e| * Interaction.scalarBackground ui R₀ c F Jstop S * F := by
  have hδ : 0 < gapConstant / 2 := by unfold gapConstant; positivity
  have hδ1 : gapConstant / 2 ≤ 1 := by
    have he := Real.exp_le_one_iff.mpr (by norm_num : (-32 : ℝ) ≤ 0)
    unfold gapConstant
    linarith only [he]
  obtain ⟨C, hC, hbound⟩ := ct_charge_profile_chain_of_scalar_bound _ hδ hδ1
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hgap⟩ := Gap.late_gap_application ui e S h hs
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hbudget u hu v hv
  have hcore : outSeg u u v ⊆ origDomain ui := fun p hp =>
    d.core_segment hu ⟨hp.1, hp.2.1, hp.2.2.trans hv.2⟩
  exact hbound e _ F S _ u (vb u) v h.solution (d.rows u hu).2.1 hv.1 hcore
    (d.one_le_background h hu) d.scalar_nonneg d.scalar_lt_one.le
    (fun x hx => (hgap (u, x) (hcore ⟨rfl, hx⟩) (hau.trans hu.1)).1)
    (fun x hx => ct_m0 h d (u, x) (d.row_mem hu ⟨hx.1, hx.2.trans hv.2⟩))
    (fun x hx => (d.stops (u, x) (d.row_mem hu ⟨hx.1, hx.2.trans hv.2⟩)).2.2.2.2.1)
    ((hbudget u hu).1.trans (hbudget u hu).2)

/-- [node eq:ct-z-charge]
The electromagnetic incoming scalar bound, charged_SF_new_version.tex:L3403–L3412.
Its constant depends only on the global gap, before coupling, scales,
stopping parameters, and late entry. Both input profiles are discharged. -/
theorem ct_z_charge :
    ∃ C : ℝ, 0 < C ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ δ c Λ F ε : ℝ) (vb g en : ℝ → ℝ),
        a ≤ u₀ →
        Interaction.StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc (vb u) 0,
          ‖radialZEM e S u (vb u) v‖ ≤ (|e| / (gapConstant / 2)) *
              (∫ x in vb u..v, S.lam u x / S.r u x * |S.Q u x| * ‖S.phi u x‖) ∧
            (|e| / (gapConstant / 2)) *
              (∫ x in vb u..v, S.lam u x / S.r u x * |S.Q u x| * ‖S.phi u x‖) ≤
            C * e ^ 2 *
            (Interaction.scalarBackground ui R₀ c F Jstop S) ^ 2 * F * S.r u v ^ 2 := by
  obtain ⟨Cq, hCq, hcharge⟩ := ct_charge_profile
  obtain ⟨C, hC, hbound⟩ := ct_z_charge_chain_of_profiles (gapConstant / 2) Cq
    (by unfold gapConstant; positivity) hCq.le
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hgap⟩ := Gap.late_gap_application ui e S h hs
  obtain ⟨b, hb, hq⟩ := hcharge ui e S h hs Jstop
  refine ⟨max a b, ⟨ha.1.trans_le (le_max_left _ _), max_lt ha.2 hb.2⟩, ?_⟩
  intro u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hbudget u hu v hv
  have hst : ExteriorStops S (exteriorDomain ui u₀ u₁ vb) (gapConstant / 2) c Λ F ε := by
    intro p hp
    have ht := d.stops p hp
    exact ⟨ht.1, (hgap p hp.1 ((le_max_left a b).trans (hau.trans hp.2.1))).1, ht.2.2⟩
  have hseg : outSeg u (vb u) v ⊆ exteriorDomain ui u₀ u₁ vb := by
    rintro ⟨x, y⟩ ⟨hxu, hy⟩
    change x = u at hxu
    subst x
    exact d.row_mem hu ⟨hy.1, hy.2.trans hv.2⟩
  exact hbound e _ F c Λ ε S _ u (vb u) v
    (Local.isSolution_mono h.solution (fun p hp => hp.1)) hst
    (d.rows u hu).2.1 hv.1 hseg
    ((by norm_num : (0 : ℝ) ≤ 1).trans (d.one_le_background h hu)) d.scalar_nonneg
    (fun x hx => ct_m0 h d (u, x) (d.row_mem hu ⟨hx.1, hx.2.trans hv.2⟩))
    (fun x hx => by
      have hxq := hq u₀ u₁ v₀ R₀ δ c Λ F ε vb g en
        ((le_max_right a b).trans hau) d hbudget u hu x ⟨hx.1, hx.2.trans hv.2⟩
      exact hxq.1.trans hxq.2)

/-- [node eq:ct-C-charge]
The explicit electromagnetic curvature primitive has its stated bound,
charged_SF_new_version.tex:L3431–L3431. Its definition retains exactly the two displayed
electromagnetic terms. The mixed `zᵉᵐ j` term stays in the other primitive.
The constant depends only on the full-core gap, before all solution data. -/
theorem ct_c_charge :
    ∃ C : ℝ, 0 < C ∧ ∀ (ui e : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S → ∀ Jstop : ℝ,
      ∃ a ∈ Ioo ui 0, ∀ (u₀ u₁ v₀ R₀ δ c Λ F ε : ℝ) (vb g en : ℝ → ℝ),
        a ≤ u₀ →
        Interaction.StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g →
        (∀ u ∈ Icc u₀ u₁, S.m u (vb u) / S.r u (vb u) ≤ en u ∧ en u ≤ F ^ 2) →
        ∀ u ∈ Icc u₀ u₁, ∀ v ∈ Icc (vb u) 0,
          radialCurvatureEM e S u (vb u) v = (S.r u v : ℂ)⁻¹ *
              (∫ x in vb u..v, ((S.lam u x * S.Q u x ^ 2 / S.r u x ^ 2 : ℝ) : ℂ) -
                I * e * S.Q u x * S.theta u x * starRingEnd ℂ (S.phi u x)) ∧
            ‖radialCurvatureEM e S u (vb u) v‖ ≤ C * e ^ 2 *
            (Interaction.scalarBackground ui R₀ c F Jstop S) ^ 2 * F ^ 2 * S.r u v ^ 2 := by
  obtain ⟨Cq, hCq, hcharge⟩ := ct_charge_profile
  obtain ⟨C, hC, hbound⟩ := ct_c_charge_of_profiles Cq hCq.le
  refine ⟨C, hC, ?_⟩
  intro ui e S h hs Jstop
  obtain ⟨a, ha, hq⟩ := hcharge ui e S h hs Jstop
  refine ⟨a, ha, ?_⟩
  intro u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hbudget u hu v hv
  have hseg : outSeg u (vb u) v ⊆ origDomain ui := by
    rintro ⟨x, y⟩ ⟨hxu, hy⟩
    change x = u at hxu
    subst x
    exact d.core_segment hu ⟨rfl, (d.rows u hu).2.1.le.trans hy.1, hy.2.trans hv.2⟩
  refine ⟨rfl, ?_⟩
  exact hbound e _ F S _ u (vb u) v h.solution (d.rows u hu).2.1 hv.1 hseg
    ((by norm_num : (0 : ℝ) ≤ 1).trans (d.one_le_background h hu)) d.scalar_nonneg
    (fun x hx => ct_m0 h d (u, x) (d.row_mem hu ⟨hx.1, hx.2.trans hv.2⟩))
    (fun x hx => (d.stops (u, x) (d.row_mem hu ⟨hx.1, hx.2.trans hv.2⟩)).2.2.2.2.1)
    (fun x hx => by
      have hxq := hq u₀ u₁ v₀ R₀ δ c Λ F ε vb g en hau d hbudget u hu x
        ⟨hx.1, hx.2.trans hv.2⟩
      exact hxq.1.trans hxq.2)

end EmcsfAcExtension.Global
