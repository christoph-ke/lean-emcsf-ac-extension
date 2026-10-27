module

public import EmcsfAcExtension.Global.Exterior.FrontierIncomingTerminal
public import EmcsfAcExtension.Global.Exterior.FrontierIncomingIntegral
public import EmcsfAcExtension.Global.Exterior.VariationTailsTerminalBounds

/-! # Closed terminal incoming-tail consumer

The actual outgoing-variation bound supplies the uniform field bound.
The resulting majorant is fixed before selecting any carrier, and supplies
both complete frontier integrability and uniform proper cylinder tails.
Source: `charged_SF_new_version.tex:L1356–L1362`, L1405–L1408; approved internal project record
(I2).
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
One common majorant gives a finite complete incoming transport integral
on every continuous proper terminal carrier and vanishing complete tails.
Its proper-interval tail cutoff precedes every carrier, cylinder radius,
and final time. The field bound and all forcing integrability are proved
from the original solution and approved terminal inputs. The only numerical
comparison coefficients are `264` and `32`; no cylinder-dependent constant
or desired variation conclusion is an assumption.
-/
theorem incoming_transport_tails_of_terminal
    {ui e C k₀ R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) (hR : 0 < R₀) (hC : 0 < C)
    (hk₀ : 0 < k₀ ∧ k₀ < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k₀) ell (Ioc 0 R₀))
    (hMc : ContinuousOn M (Ioc 0 R₀)) (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (hAfinite : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    let G : ℝ → ℝ → ℂ := fun u v =>
      (-S.nu u v / ((1 - S.mu u v) * S.r u v) : ℝ) *
        ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) *
          (S.theta u v / (S.lam u v : ℂ)) + I * e * S.Q u v * S.phi u v)
    ∃ c ∈ Ioo ui 0, ∃ H : ℝ → ℝ,
      IntegrableOn H (Ico c 0) ∧
      (∀ p ∈ adaptiveExterior S ui c ell, ‖G p.1 p.2‖ ≤ H p.1) ∧
      (∀ V : ℝ → ℝ, ContinuousOn V (Ico c 0) →
        (∀ u ∈ Ico c 0, (u, V u) ∈ adaptiveExterior S ui c ell) →
        (∀ u ∈ Ico c 0, u < V u) →
        IntegrableOn (fun u => G u (V u)) (Ico c 0) ∧
          Tendsto (fun a => ∫ u in Ico a 0, ‖G u (V u)‖) (𝓝[<] 0) (𝓝 0)) ∧
      ∀ ε > 0, ∃ u₀ ∈ Ioo c 0, ∀ a b : ℝ, u₀ ≤ a → a ≤ b → b < 0 →
        ∀ V : ℝ → ℝ, ContinuousOn V (Icc a b) →
          (∀ u ∈ Icc a b, (u, V u) ∈ adaptiveExterior S ui c ell) →
          (∫ u in a..b, ‖G u (V u)‖) ≤ ε := by
  obtain ⟨uf, huf, B, _, hfield⟩ := outgoing_field_bound_of_terminal h M ell hR hC
    hk₀ hLip hMc hM hAfinite hcollapse hmass hell hellsmall hsmall hphi
  obtain ⟨c, hc, H, hHi, hbound, ht⟩ := incoming_transport_tail_of_uniform_field_bound
    h M ell hR hC huf hcollapse hmass hMc hLip.continuousOn hM hell hellsmall hsmall
      hAfinite hphi hfield
  refine ⟨c, hc, H, hHi, hbound, ?_, ht⟩
  intro V hV hmem hp
  have hi := boundary_incoming_integrable_of_majorant h.solution hHi hV hmem hp hbound
  exact ⟨hi, norm_integral_terminal_tail_tendsto hc.2 hi⟩

end EmcsfAcExtension.Global.Exterior
