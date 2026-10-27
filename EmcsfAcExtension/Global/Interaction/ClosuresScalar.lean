module

public import EmcsfAcExtension.Global.Interaction.BoundaryCharge
public import EmcsfAcExtension.Global.Interaction.Curvature
public import EmcsfAcExtension.Global.Interaction.RadialZ
public import EmcsfAcExtension.Global.Defs.Stages
import EmcsfAcExtension.Global.Gap.LateMain
import EmcsfAcExtension.Global.Terminal.AmplitudeMain
import EmcsfAcExtension.Global.Terminal.OpticalUpper
import EmcsfAcExtension.Global.Renormalized.Curvature
import EmcsfAcExtension.Global.Calculus.Sections

/-! # Scalar background and algebraic interaction closures

The stopped hypotheses and derivative envelope imply the literal exterior
scalar background. The late full-core gap is obtained from the terminal
hypothesis, rather than added to the original data. Source:
`charged_SF_new_version.tex:L3284–L3360`, L3403–L3405.
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global

namespace Interaction

/-- [internal] The terminal-annulus supremum appearing in `M₀`,
charged_SF_new_version.tex:L3317–L3322, expressed in the original terminal label. -/
@[expose] noncomputable def terminalScalarSup (ui R₀ : ℝ) (S : Fields) : ℝ :=
  sSup ((fun u => ‖S.phi u 0‖) ''
    {u | u ∈ Ico ui 0 ∧ R₀ / 2 ≤ S.r u 0 ∧ S.r u 0 ≤ R₀})

/-- [internal] The exact scalar background; only the terminal-annulus
supremum and fixed stopping parameters occur (charged_SF_new_version.tex:L3317–L3322). -/
@[expose] noncomputable def scalarBackground (ui R₀ c F Jstop : ℝ) (S : Fields) : ℝ :=
  1 + terminalScalarSup ui R₀ S + (F + c⁻¹ * Jstop) / (1 - F ^ 2)

private theorem terminal_scalar_bddAbove {ui e R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hR : 0 < R₀) :
    BddAbove ((fun u => ‖S.phi u 0‖) ''
      {u | u ∈ Ico ui 0 ∧ R₀ / 2 ≤ S.r u 0 ∧ S.r u 0 ≤ R₀}) := by
  have ht := Terminal.terminal_radius_collapse h.ui_neg h.solution h.mu
  have hi : ∀ᶠ u : ℝ in 𝓝[<] 0, ui < u :=
    nhdsWithin_le_nhds (Ioi_mem_nhds h.ui_neg)
  have hb0 : ∀ᶠ u : ℝ in 𝓝[<] 0, u < 0 := self_mem_nhdsWithin
  obtain ⟨b, hb0, hbi, hbr⟩ :=
    (hb0.and
      (hi.and (ht.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < R₀ / 2))))).exists
  have hs : inSeg ui b 0 ⊆ origDomain ui := by
    rintro ⟨u, v⟩ ⟨hu, hub, rfl⟩
    exact ⟨hu, hub.trans_lt hb0, (hub.trans_lt hb0).le, le_rfl⟩
  have hb := isCompact_Icc.image_of_continuousOn
    (Calculus.continuousOn_in_section h.solution.cont_phi hs).norm
  apply hb.bddAbove.mono
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨u, ⟨hu.1.1, ?_⟩, rfl⟩
  by_contra hbu
  have hru := (Terminal.terminal_radius_strictAntiOn h.solution).antitoneOn
    ⟨hbi.le, hb0⟩ hu.1 (le_of_not_ge hbu)
  linarith only [hu.2.1, hru, hbr]

/-- [internal] Every terminal point in the stated radius annulus is bounded
by its literal supremum; boundedness follows from radius collapse. -/
theorem terminal_scalar_le_sup {ui e R₀ u : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hR : 0 < R₀) (hu : u ∈ Ico ui 0)
    (hr : R₀ / 2 ≤ S.r u 0 ∧ S.r u 0 ≤ R₀) :
    ‖S.phi u 0‖ ≤ terminalScalarSup ui R₀ S :=
  le_csSup (terminal_scalar_bddAbove h hR) ⟨u, ⟨hu, hr⟩, rfl⟩

/-- [internal] The finite stopped exterior hypotheses used by the profile
nodes. Every field is a source hypothesis: geometry, numerical stops, and
the nonnegative integrable incoming-label envelope with its stopping budget.
No scalar profile, charge profile, or full-core gap is included. -/
structure StoppedProfileData (ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop : ℝ)
    (S : Fields) (vb g : ℝ → ℝ) : Prop where
  /-- Positive entry radius. -/
  radius_pos : 0 < R₀
  /-- Outgoing row geometry and common label interval. -/
  rows : ∀ u ∈ Icc u₀ u₁, ui ≤ u ∧ u < vb u ∧ vb u ≤ 0 ∧ v₀ ≤ vb u
  /-- The stopped terminal-radius annulus. -/
  annulus : ∀ u ∈ Icc u₀ u₁, R₀ / 2 ≤ S.r u 0 ∧ S.r u 0 ≤ R₀
  /-- Positive lower outgoing expansion stop. -/
  expansion_pos : 0 < c
  /-- Nonnegative scalar derivative stop. -/
  scalar_nonneg : 0 ≤ F
  /-- Strict scalar derivative stop. -/
  scalar_lt_one : F < 1
  /-- Exterior field stops, never extended into the core. -/
  stops : ExteriorStops S (exteriorDomain ui u₀ u₁ vb) δ c Λ F ε
  /-- Integrable envelope on the common incoming-label interval. -/
  integrable : IntegrableOn g (Icc v₀ 0)
  /-- Nonnegative envelope. -/
  nonneg : ∀ᵐ v ∂volume.restrict (Icc v₀ 0), 0 ≤ g v
  /-- The source's incoming-label majorant, with a.e. labels before each row. -/
  majorant : ∀ u ∈ Icc u₀ u₁, ∀ᵐ v ∂volume.restrict (Icc v₀ 0),
    vb u ≤ v → ‖weightedJ S u v‖ ≤ g v
  /-- Fixed stopping budget. -/
  budget : (∫ v in v₀..0, g v) ≤ Jstop

end Interaction

/-- [node eq:ct-M0]
The scalar background on the entire stopped exterior,
charged_SF_new_version.tex:L3317–L3324. `M₀` is exactly the terminal-annulus supremum
plus the displayed stopping expression. No core scalar bound is assumed. -/
theorem ct_m0 {ui e u₀ u₁ v₀ R₀ δ c Λ F ε Jstop : ℝ}
    {S : Fields} {vb g : ℝ → ℝ} (h : OriginalData ui e S)
    (d : Interaction.StoppedProfileData ui u₀ u₁ v₀ R₀ δ c Λ F ε Jstop S vb g) :
    ∀ p ∈ exteriorDomain ui u₀ u₁ vb,
      ‖S.phi p.1 p.2‖ ≤ Interaction.scalarBackground ui R₀ c F Jstop S := by
  apply Interaction.scalar_profile_of_stops h d.expansion_pos d.scalar_nonneg d.scalar_lt_one
    d.rows d.stops
  · intro u hu
    obtain ⟨hui, hub, hb0, _⟩ := d.rows u hu
    exact Interaction.terminal_scalar_le_sup h d.radius_pos ⟨hui, hub.trans_le hb0⟩
      (d.annulus u hu)
  · exact d.integrable
  · exact d.nonneg
  · exact d.majorant
  · exact d.budget

namespace Interaction

/-- [node sec:charged-terminal-interaction#relative-charge-amplitude-application]
The exact full-core scaled-amplitude bound and its late smallness consequence,
charged_SF_new_version.tex:L3284–L3293. The gap is the universal `gapConstant / 2`;
the late label may depend on the fixed development and coupling. -/
theorem relative_charge_amplitude_application {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ a ∈ Ioo ui 0,
      (∀ u ∈ Ico a 0, ∀ v ∈ Ioc u 0,
        S.Q u v ^ 2 / S.r u v ^ 2 ≤ (e ^ 2 / (gapConstant / 2)) *
          (sSup ((fun s => S.r u s * ‖S.phi u s‖) '' Ioc u v)) ^ 2 * S.mu u v) ∧
      (∀ p ∈ origDomain ui, a ≤ p.1 →
        S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 ≤ S.mu p.1 p.2 / 2 ∧
        0 ≤ (S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2) /
          (1 - S.mu p.1 p.2)) := by
  obtain ⟨a, ha, hgap⟩ := Gap.late_gap_application ui e S h hs
  have hδ : 0 < gapConstant / 2 := by unfold gapConstant; positivity
  obtain ⟨b, hb, hsmall⟩ := relative_charge_small_of_late_bounds h hδ ha
    (fun p hp hpa => (hgap p hp hpa).1) (charged_rphi_small ui e S h hs).1
  refine ⟨max a b, ⟨ha.1.trans_le (le_max_left _ _), max_lt ha.2 hb.2⟩, ?_, ?_⟩
  · intro u hu v hv
    have hui : ui ≤ u := ha.1.le.trans ((le_max_left a b).trans hu.1)
    have hseg : outSeg u u v ⊆ origDomain ui := by
      rintro ⟨x, y⟩ ⟨rfl, hy⟩
      exact ⟨hui, hu.2, hy.1, hy.2.trans hv.2⟩
    exact relative_charge_amplitude_application_of_gap h.solution hv.1 hseg hδ
      (fun s hs => (hgap (u, s) (hseg ⟨rfl, hs⟩)
        ((le_max_left a b).trans hu.1)).1)
  · intro p hp hlate
    have hq := hsmall p hp ((le_max_right a b).trans hlate)
    refine ⟨hq, div_nonneg ?_ (h.solution.one_sub_mu_pos p hp).le⟩
    linarith only [hq, (h.mu p hp).1]

end Interaction

/-- [node eq:ct-C-reconstruction]
The full complex curvature reconstruction, charged_SF_new_version.tex:L3414–L3425.
The transport premise of the helper is discharged by `eq:ct-C-trans`.
There are no constants or profile hypotheses. -/
theorem ct_c_reconstruction {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) :
    Local.curv S u b = radialCurvatureBoundary S u a b +
      radialCurvatureSource S u a b + radialCurvatureEM e S u a b := by
  apply ct_c_reconstruction_of_transport hS hua hab hs
  convert Renormalized.curvature_out_integralForm hS hua hab hs using 1
  funext v
  ring

end EmcsfAcExtension.Global
