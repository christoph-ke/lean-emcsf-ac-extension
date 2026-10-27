module

public import EmcsfAcExtension.Global.Exterior.FrontierTransport
public import EmcsfAcExtension.Global.Exterior.FrontierTails
public import EmcsfAcExtension.Global.Exterior.DerivativeSourceForcingTerminal
public import EmcsfAcExtension.Global.Exterior.VariationTailsRadius

/-! # Uniform incoming transport tails

The common majorant is constructed on the entire adaptive exterior before
any boundary is selected. Thus the cutoff is uniform in cylinder radius,
boundary, and admissible final time. Source: `charged_SF_new_version.tex:L1356–L1360`,
L1405–L1408; approved internal project record (I2).
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The incoming covariant source is continuous along every continuous proper
boundary. This fact supplies its proper-interval integrability independently
of any terminal estimate. No constants occur. -/
theorem continuousOn_covariant_incoming_source
    {ui e : ℝ} {S : Fields} {V : ℝ → ℝ} {s : Set ℝ}
    (hS : IsSolution e S (origDomain ui))
    (hV : ContinuousOn V s)
    (hmem : ∀ u ∈ s, (u, V u) ∈ origDomain ui)
    (hp : ∀ u ∈ s, u < V u) :
    ContinuousOn (fun u =>
      (-S.nu u (V u) / ((1 - S.mu u (V u)) * S.r u (V u)) : ℝ) *
        ((S.mu u (V u) - S.Q u (V u) ^ 2 / S.r u (V u) ^ 2 : ℝ) *
          (S.theta u (V u) / (S.lam u (V u) : ℂ)) +
          I * e * S.Q u (V u) * S.phi u (V u))) s := by
  have hc : ContinuousOn (fun u : ℝ => (u, V u)) s :=
    continuousOn_id.prodMk hV
  have hm : MapsTo (fun u : ℝ => (u, V u)) s
      (origDomain ui ∩ {p | p.1 < p.2}) := fun u hu => ⟨hmem u hu, hp u hu⟩
  have hG := (Calculus.continuousOn_normalized_incoming_source
    (K := origDomain ui ∩ {p | p.1 < p.2}) hS Subset.rfl).comp hc hm
  have hA₀ := hS.cont_A.comp hc hmem
  have hA : ContinuousOn (fun u => S.A u (V u)) s := hA₀
  have hf₀ := (Calculus.continuousOn_a hS).comp hc hmem
  have hf : ContinuousOn (fun u => S.a u (V u)) s := hf₀
  have hh := hG.add (((Complex.continuous_ofReal.comp_continuousOn hA).const_mul
    (I * e)).mul hf)
  apply hh.congr
  intro u _
  dsimp only [Function.comp_apply, Pi.add_apply, Pi.mul_apply]
  simp only [Fields.a]
  ring

/-- [internal]
Uniform tail extraction from the common incoming-source majorant. The
functions `A,Q` are fixed integrable time weights and `B` is a fixed field
bound. The numerical coefficients are `264` and `32`; the late cutoff is
chosen before the boundary and final time. The terminal consumer below
constructs and discharges every majorant premise. -/
theorem incoming_transport_tail_of_common_majorant
    {ui e c B : ℝ} {S : Fields} {ell A Q : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui)) (hc : c < 0)
    (hA : IntegrableOn A (Ico c 0)) (hQ : IntegrableOn Q (Ico c 0))
    (hbound : ∀ p ∈ adaptiveExterior S ui c ell,
      ‖(-S.nu p.1 p.2 / ((1 - S.mu p.1 p.2) * S.r p.1 p.2) : ℝ) *
        ((S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 : ℝ) *
          (S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)) +
          I * e * S.Q p.1 p.2 * S.phi p.1 p.2)‖ ≤ 264 * B * A p.1 + 32 * Q p.1)
    (hproper : ∀ p ∈ adaptiveExterior S ui c ell, p.1 < p.2) :
    ∀ ε > 0, ∃ u₀ ∈ Ioo c 0, ∀ a b : ℝ, u₀ ≤ a → a ≤ b → b < 0 →
      ∀ V : ℝ → ℝ, ContinuousOn V (Icc a b) →
        (∀ u ∈ Icc a b, (u, V u) ∈ adaptiveExterior S ui c ell) →
        (∫ u in a..b,
          ‖(-S.nu u (V u) / ((1 - S.mu u (V u)) * S.r u (V u)) : ℝ) *
            ((S.mu u (V u) - S.Q u (V u) ^ 2 / S.r u (V u) ^ 2 : ℝ) *
              (S.theta u (V u) / (S.lam u (V u) : ℂ)) +
              I * e * S.Q u (V u) * S.phi u (V u))‖) ≤ ε := by
  have hG := (hA.const_mul (264 * B)).add (hQ.const_mul 32)
  intro ε hε
  obtain ⟨u₀, hu₀, ht⟩ := uniform_interval_norm_tail_of_integrable_majorant hc hG ε hε
  refine ⟨u₀, hu₀, ?_⟩
  intro a b ha hab hb V hV hm
  have hmem : ∀ u ∈ uIcc a b, (u, V u) ∈ origDomain ui := by
    simpa only [uIcc_of_le hab] using fun u hu => (hm u hu).1
  have hp : ∀ u ∈ uIcc a b, u < V u := by
    simpa only [uIcc_of_le hab] using fun u hu => hproper (u, V u) (hm u hu)
  have hVi : ContinuousOn V (uIcc a b) := by simpa only [uIcc_of_le hab] using hV
  exact ht a b ha hab hb _
    (continuousOn_covariant_incoming_source hS hVi hmem hp).intervalIntegrable
    (fun u hu => hbound (u, V u) (hm u hu))

/-- [internal]
The scalar-charge component is one of the five nonnegative terms of the
approved forcing. The coefficient is exactly one, uniformly in all profiles.
-/
theorem scalar_charge_weight_le_forcing {e R : ℝ} {M ell L : ℝ → ℝ}
    (hM : 0 ≤ M R) (he : 0 < ell R) (hL : 0 ≤ L R) :
    |e| * L R * Real.sqrt (M R / ell R) ≤ exteriorForcing e M ell L R := by
  dsimp only [exteriorForcing]
  have h₁ : 0 ≤ M R / ell R ^ 2 * Real.sqrt (M R / ell R) := by positivity
  have h₂ : 0 ≤ |e| * L R * (M R / ell R) * Real.sqrt (M R / ell R) := by positivity
  have h₃ : 0 ≤ |e| * (M R / ell R) := by positivity
  have h₅ : 0 ≤ e ^ 2 * L R ^ 2 * Real.sqrt (M R * R) := by positivity
  linarith only [h₁, h₂, h₃, h₅]

end EmcsfAcExtension.Global.Exterior
