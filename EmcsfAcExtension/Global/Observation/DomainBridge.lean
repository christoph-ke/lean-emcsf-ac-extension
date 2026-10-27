module

public import EmcsfAcExtension.Global.Observation.CylinderClock
public import EmcsfAcExtension.Global.Api.Domains
import EmcsfAcExtension.Infra.Null.IntegralForm
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Strict source margins for observation comparison

The comparison clock window is strictly inside the source clock window.
This preserves ordinary derivatives at all endpoints of the comparison
sections. Source: charged_SF_new_version.tex:L2741–2781; internal project record internal project
record.
-/

public section

open Set
namespace EmcsfAcExtension.Global.Observation
open Local

/-- [internal]
Ordinary derivatives on a closed comparison interval from integral equations
on a strictly larger source interval. Both travel margins are explicit.
Port of internal project record internal project record, from the original characteristic FTC. -/
theorem ordinary_on_closed_of_margin {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : ℝ → E} {A a b B : ℝ}
    (hAa : A < a) (hbB : b < B) (hg : ContinuousOn g (Ioo A B))
    (heq : ∀ c d, A < c → c ≤ d → d < B → IntegralForm f g c d) :
    ∀ x ∈ Icc a b, HasDerivAt f (g x) x := by
  intro x hx
  exact hasDerivAt_of_integralForm_interior ⟨hAa.trans_le hx.1, hx.2.trans_lt hbB⟩ hg heq

-- A proper inner clock window has strict original-label margins, even if the
-- original outer window meets ui or v=0. This records the domain choice assembly needs.
/-- [internal]
Every point of a strictly inner clock window has strict original-label
margins, even when the source cylinder meets the original boundary.
Port of internal project record internal project record. There are no estimate constants. -/
theorem inner_clock_labels {ui e ρ A a b B : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (γ : ClockCylinder S (origDomain ui) ρ A B)
    (hAa : A < a) (hab : a ≤ b) (hbB : b < B) :
    ∀ τ ∈ Icc a b, ui < γ.U τ ∧ γ.V τ < 0 := by
  have hAB : A ≤ B := hAa.le.trans (hab.trans hbB.le)
  have hA : A ∈ Icc A B := ⟨le_rfl,hAB⟩
  have hB : B ∈ Icc A B := ⟨hAB,le_rfl⟩
  intro τ hτ
  have hτ' : τ ∈ Icc A B := ⟨hAa.le.trans hτ.1,hτ.2.trans hbB.le⟩
  refine ⟨lt_of_le_of_lt (γ.mem A hA).1 ?_, lt_of_lt_of_le ?_ (γ.mem B hB).2.2.2⟩
  · exact γ.strictMonoOn_U hS hA hτ' (hAa.trans_le hτ.1)
  · exact γ.strictMonoOn_V hS hτ' hB (hτ.2.trans_lt hbB)

end EmcsfAcExtension.Global.Observation
