module

public import EmcsfAcExtension.Global.Exterior.TerminalPackage
public import EmcsfAcExtension.Global.Exterior.VariationTailsTerminal
public import EmcsfAcExtension.Global.Exterior.VariationTailsTerminalBounds
public import EmcsfAcExtension.Global.Exterior.VariationTailsTerminalModulusRadial

/-! # Signed-terminal exterior consumers

Source: `charged_SF_new_version.tex:L1231–1416`; approved internal project record.
The terminal package is discharged before the quantified geometric objects.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [node c:exterior#moving-interval-modulus-inequality]
The signed terminal hypothesis discharges the terminal estimates in
`moving_interval_modulus_inequality_radial_of_terminal`. The fixed adaptive profile precedes
all late rows, carriers and endpoints. Numerical coefficients are universal;
remaining constants depend on the development, signed bound and profile. -/
theorem moving_interval_modulus_inequality
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
    ∃ C > 0,
    ∃ c ∈ Ioo ui 0, ∃ t VR : ℝ → ℝ,
      (∀ u ∈ Ico c 0, u < t u ∧ t u < 0 ∧ S.r u (t u) = ell (S.r u 0)) ∧
      ContinuousOn VR (Ioc 0 (S.r c 0)) ∧
      (∀ u ∈ Ico c 0, VR (S.r u 0) =
        (eVariationOn (S.a u) (Icc (t u) 0)).toReal) ∧
      ∀ a b, c ≤ a → a ≤ b → b < 0 →
        (eVariationOn (S.a b) (Icc (t b) 0)).toReal +
          (∫ u in a..b, deriv t u * ‖densityRepresentative e S a u (t u)‖) ≤
        (eVariationOn (S.a a) (Icc (t a) 0)).toReal +
          20744 * (∫ R in S.r b 0..S.r a 0, (M R / ell R ^ 2) * VR R) +
          20744 * (∫ R in S.r b 0..S.r a 0, exteriorForcing e M ell
            (fun R => (C + 2) * (1 + Real.sqrt (Real.log (S.r ui 0 / R)))) R) := by
  obtain ⟨C, hC, hcollapse, hphi⟩ := terminal_control h hs
  exact ⟨C, hC, moving_interval_modulus_inequality_radial_of_terminal h M ell hR hC hk₀
    hLip hMc hM hAfinite hcollapse hmass hell hellsmall hsmall hphi⟩

/-- [node c:exterior#outgoing-variation-bound]
The signed terminal hypothesis discharges the terminal estimates in
`outgoing_variation_bound_of_terminal`. The fixed adaptive profile precedes
all late rows, carriers and endpoints. Numerical coefficients are universal;
remaining constants depend on the development, signed bound and profile. -/
theorem outgoing_variation_bound {ui e k₀ R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (M ell : ℝ → ℝ) (hR : 0 < R₀)
    (hk₀ : 0 < k₀ ∧ k₀ < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k₀) ell (Ioc 0 R₀))
    (hMc : ContinuousOn M (Ioc 0 R₀)) (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (hAfinite : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ c ∈ Ioo ui 0, ∃ t : ℝ → ℝ, ∃ KV ≥ 0,
      (∀ u ∈ Ico c 0, u < t u ∧ t u < 0 ∧ S.r u (t u) = ell (S.r u 0)) ∧
      (∀ u ∈ Ico c 0, (eVariationOn (S.a u) (Icc (t u) 0)).toReal ≤ KV) := by
  obtain ⟨C, hC, hcollapse, hphi⟩ := terminal_control h hs
  exact outgoing_variation_bound_of_terminal h M ell hR hC hk₀ hLip hMc hM hAfinite
    hcollapse hmass hell hellsmall hsmall hphi

/-- [node c:exterior#outgoing-variation-decay]
[node c:exterior#outgoing-field-decay]
The signed terminal hypothesis discharges the terminal estimates in
`variation_and_boundary_exit_tails_of_terminal`. The fixed adaptive profile precedes
all late rows, carriers and endpoints. Numerical coefficients are universal;
remaining constants depend on the development, signed bound and profile. -/
theorem variation_and_boundary_exit_tails
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
    ∃ c ∈ Ioo ui 0, ∃ t E : ℝ → ℝ,
      (∀ u ∈ Ico c 0, u < t u ∧ t u < 0 ∧ S.r u (t u) = ell (S.r u 0)) ∧
      StrictMonoOn t (Ico c 0) ∧ Tendsto t (𝓝[<] 0) (𝓝 0) ∧
      Tendsto (fun u => (eVariationOn (S.a u) (Icc (t u) 0)).toReal) (𝓝[<] 0) (𝓝 0) ∧
      (∀ ε > 0, ∀ᶠ u in 𝓝[<] (0 : ℝ), ∀ v ∈ Icc (t u) 0,
        ‖S.theta u v / (S.lam u v : ℂ)‖ < ε) ∧
      (∀ a b, c ≤ a → a ≤ b → b < 0 → ∃ K L : ℝ≥0,
        LipschitzOnWith K t (uIcc a b) ∧
        AntilipschitzWith L ((uIcc a b).domRestrict t)) ∧
      Tendsto E (𝓝[<] 0) (𝓝 0) ∧
      ∀ (a b : ℝ) (γ : ℝ → ℝ) (K L : ℝ≥0),
        c ≤ a → a ≤ b → b < 0 → LipschitzOnWith K γ (uIcc a b) →
        MonotoneOn γ (uIcc a b) → AntilipschitzWith L ((uIcc a b).domRestrict γ) →
        (∀ u ∈ Icc a b, t u ≤ γ u ∧ γ u ≤ 0) →
        (∫ u in a..b, deriv γ u * ‖densityRepresentative e S a u (γ u)‖) ≤ E a := by
  obtain ⟨C, hC, hcollapse, hphi⟩ := terminal_control h hs
  exact variation_and_boundary_exit_tails_of_terminal h M ell hR hC hk₀ hLip hMc hM
    hAfinite hcollapse hmass hell hellsmall hsmall hphi

end EmcsfAcExtension.Global.Exterior
