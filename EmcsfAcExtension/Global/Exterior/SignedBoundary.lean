module

public import EmcsfAcExtension.Global.Exterior.TerminalPackage
public import EmcsfAcExtension.Global.Exterior.CylinderTailsClosed
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceIncomingTerminal
public import EmcsfAcExtension.Global.Exterior.FrontierCovariantClosed
public import EmcsfAcExtension.Global.Exterior.VariationTailsCylinder
public import EmcsfAcExtension.Global.Exterior.VariationTailsFrontier

/-! # Signed-terminal exterior consumers

Source: `charged_SF_new_version.tex:L1231–1416`; approved internal project record.
The terminal package is discharged before the quantified geometric objects.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [node c:exterior#frontier-exit-tail]
The signed terminal hypothesis discharges the terminal estimates in
`frontier_exit_tail_of_terminal`. The fixed adaptive profile precedes
all late rows, carriers and endpoints. Numerical coefficients are universal;
remaining constants depend on the development, signed bound and profile. -/
theorem frontier_exit_tail {ui e k₀ R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) (hR : 0 < R₀)
    (hk₀ : 0 < k₀ ∧ k₀ < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k₀) ell (Ioc 0 R₀))
    (hMc : ContinuousOn M (Ioc 0 R₀)) (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (hAfinite : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ c ∈ Ioo ui 0, ∃ t : ℝ → ℝ,
      (∀ u ∈ Ico c 0, u < t u ∧ t u < 0 ∧ S.r u (t u) = ell (S.r u 0)) ∧
      IntegrableOn (fun u => deriv t u * ‖densityRepresentative e S c u (t u)‖) (Ico c 0) ∧
      Tendsto (fun a => ∫ u in a..0, deriv t u * ‖densityRepresentative e S c u (t u)‖)
        (𝓝[<] 0) (𝓝 0) := by
  obtain ⟨C, hC, hcollapse, hphi⟩ := terminal_control h hs
  exact frontier_exit_tail_of_terminal h M ell hR hC hk₀ hLip hMc hM hAfinite hcollapse
    hmass hell hellsmall hsmall hphi

/-- [node c:exterior#frontier-incoming-transport-tail]
[node c:exterior#cylinder-incoming-transport-tail]
The signed terminal hypothesis discharges the terminal estimates in
`incoming_transport_radius_majorant_of_terminal`. The fixed adaptive profile precedes
all late rows, carriers and endpoints. Numerical coefficients are universal;
remaining constants depend on the development, signed bound and profile. -/
theorem incoming_transport_radius_majorant {ui e k₀ R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) (hR : 0 < R₀)
    (hk₀ : 0 < k₀ ∧ k₀ < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k₀) ell (Ioc 0 R₀))
    (hMc : ContinuousOn M (Ioc 0 R₀)) (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (hAfinite : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ C > 0,
    ∃ c ∈ Ioo ui 0, ∃ t SF : ℝ → ℝ,
      (∀ u ∈ Ico c 0, u < t u ∧ t u < 0 ∧ S.r u (t u) = ell (S.r u 0)) ∧
      ContinuousOn t (Ico c 0) ∧ ContinuousOn SF (Ioc 0 (S.r c 0)) ∧
      (∀ u ∈ Ico c 0, SF (S.r u 0) = outgoingFieldSup S t u) ∧
      let L := fun R => (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / R)))
      let T := incomingRadiusWeight e M ell L SF
      IntegrableOn T (Ioc 0 (S.r c 0)) ∧
      Tendsto (fun ρ => ∫ R in Ioc 0 ρ, T R) (𝓝[>] 0) (𝓝 0) ∧
      (∀ a b, c ≤ a → a ≤ b → b < 0 → ∀ V : ℝ → ℝ,
        ContinuousOn V (Icc a b) →
        (∀ u ∈ Icc a b, (u, V u) ∈ adaptiveExterior S ui c ell) →
        (∫ u in a..b, ‖incomingCovariantSource e S u (V u)‖) ≤
          296 * ∫ R in Ioc 0 (S.r a 0), T R) ∧
      (∀ ε > 0, ∃ u₀ ∈ Ioo c 0, ∀ a b, u₀ ≤ a → a ≤ b → b < 0 →
        ∀ V : ℝ → ℝ, ContinuousOn V (Icc a b) →
          (∀ u ∈ Icc a b, (u, V u) ∈ adaptiveExterior S ui c ell) →
          (∫ u in a..b, ‖incomingCovariantSource e S u (V u)‖) ≤ ε) := by
  obtain ⟨C, hC, hcollapse, hphi⟩ := terminal_control h hs
  exact ⟨C, hC, incoming_transport_radius_majorant_of_terminal h M ell hR hC hk₀ hLip hMc
    hM hAfinite hcollapse hmass hell hellsmall hsmall hphi⟩

/-- [node c:exterior#frontier-covariant-variation]
The signed terminal hypothesis discharges the terminal estimates in
`frontier_covariant_variation_of_terminal`. The fixed adaptive profile precedes
all late rows, carriers and endpoints. Numerical coefficients are universal;
remaining constants depend on the development, signed bound and profile. -/
theorem frontier_covariant_variation
    {ui e k₀ R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) (hR : 0 < R₀)
    (hk₀ : 0 < k₀ ∧ k₀ < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k₀) ell (Ioc 0 R₀))
    (hMc : ContinuousOn M (Ioc 0 R₀)) (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (hAfinite : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ c ∈ Ioo ui 0, ∃ t : ℝ → ℝ,
      (∀ u ∈ Ico c 0, u < t u ∧ t u < 0 ∧ S.r u (t u) = ell (S.r u 0)) ∧
      StrictMonoOn t (Ico c 0) ∧ Tendsto t (𝓝[<] 0) (𝓝 0) ∧
      BoundedVariationOn (curveParallel e S S.a id t c) (Ico c 0) ∧
      Tendsto (fun a => eVariationOn (curveParallel e S S.a id t c) (Ico a 0))
        (𝓝[<] 0) (𝓝 0) := by
  obtain ⟨C, hC, hcollapse, hphi⟩ := terminal_control h hs
  exact frontier_covariant_variation_of_terminal h M ell hR hC hk₀ hLip hMc hM hAfinite
    hcollapse hmass hell hellsmall hsmall hphi

/-- [node c:exterior#cylinder-exit-tail]
The signed terminal hypothesis discharges the terminal estimates in
`cylinder_exit_tail_of_terminal`. The fixed adaptive profile precedes
all late rows, carriers and endpoints. Numerical coefficients are universal;
remaining constants depend on the development, signed bound and profile. -/
theorem cylinder_exit_tail {ui e k₀ R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) (hR : 0 < R₀)
    (hk₀ : 0 < k₀ ∧ k₀ < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k₀) ell (Ioc 0 R₀))
    (hMc : ContinuousOn M (Ioc 0 R₀)) (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (hAfinite : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ c ∈ Ioo ui 0, ∃ E : ℝ → ℝ, Tendsto E (𝓝[<] 0) (𝓝 0) ∧
      ∀ (a b ρ : ℝ) (γ : ℝ → ℝ), c ≤ a → a ≤ b → b < 0 →
        ContinuousOn γ (Icc a b) →
        (∀ u ∈ Icc a b, u < γ u ∧ γ u ≤ 0 ∧ S.r u (γ u) = ρ) →
        (∀ u ∈ Icc a b, ell (S.r u 0) ≤ ρ) →
        StrictMonoOn γ (Icc a b) ∧
        (∀ᵐ u ∂volume.restrict (Icc a b),
          HasDerivAt γ (-S.nu u (γ u) / S.lam u (γ u)) u ∧
          deriv γ u = -S.nu u (γ u) / S.lam u (γ u) ∧ 0 < deriv γ u) ∧
        (∫ u in a..b, deriv γ u * ‖densityRepresentative e S a u (γ u)‖) ≤ E a := by
  obtain ⟨C, hC, hcollapse, hphi⟩ := terminal_control h hs
  obtain ⟨c, hc, E, ht, hbound⟩ := cylinder_exit_tail_of_terminal h M ell hR hC
    hk₀ hLip hMc hM hAfinite hcollapse hmass hell hellsmall hsmall hphi
  refine ⟨c, hc, E, ht, ?_⟩
  intro a b ρ γ ha hab hb hγ hroot hinterior
  have hspeed := cylinder_speed_of_graph h (hc.1.le.trans ha) hb hγ hroot
  exact ⟨hspeed.1, hspeed.2, hbound a b ρ γ ha hab hb hγ hroot hinterior⟩

/-- [node c:exterior#cylinder-covariant-variation-tail]
The signed terminal hypothesis discharges the terminal estimates in
`cylinder_covariant_variation_tail_of_terminal`. The fixed adaptive profile precedes
all late rows, carriers and endpoints. Numerical coefficients are universal;
remaining constants depend on the development, signed bound and profile. -/
theorem cylinder_covariant_variation_tail
    {ui e k₀ R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) (hR : 0 < R₀)
    (hk₀ : 0 < k₀ ∧ k₀ < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k₀) ell (Ioc 0 R₀))
    (hMc : ContinuousOn M (Ioc 0 R₀)) (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (hAfinite : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ c ∈ Ioo ui 0, ∀ ε > 0, ∃ u₀ ∈ Ioo c 0,
      ∀ (a b ρ : ℝ) (V : ℝ → ℝ),
        u₀ ≤ a → a ≤ b → b < 0 → ContinuousOn V (Icc a b) →
        (∀ u ∈ Icc a b, u < V u ∧ V u ≤ 0 ∧ S.r u (V u) = ρ) →
        (∀ u ∈ Icc a b, ell (S.r u 0) ≤ ρ) →
        curveCovVar e S S.a id V a b ≤ ENNReal.ofReal ε := by
  obtain ⟨C, hC, hcollapse, hphi⟩ := terminal_control h hs
  exact cylinder_covariant_variation_tail_of_terminal h M ell hR hC hk₀ hLip hMc hM
    hAfinite hcollapse hmass hell hellsmall hsmall hphi

end EmcsfAcExtension.Global.Exterior
