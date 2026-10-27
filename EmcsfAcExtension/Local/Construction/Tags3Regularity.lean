module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
import EmcsfAcExtension.Local.Construction.WireRecovery
import EmcsfAcExtension.Local.Construction.ReconBasic
import EmcsfAcExtension.Local.Calculus.Partials

/-! # Classical C¹ regularity of the local Picard fixed point

The compatible outgoing-jet carrier and the literal fixed-point equations
recover incoming differentiability and all nine classical primary fields on
the original closed wedge. This is the classical C¹ reading specified for
this packet by internal project record.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- [node restart-sec-independent-null-construction#smooth-regularity]
The local fixed point and all nine reconstructed fields are jointly C¹ on
their original closed wedge, charged_SF_new_version.tex:L6086–L6129, in the packet's
classical C¹ reading. Full-system recovery is discharged, including incoming
differentiability; only the literal fixed-point equations, C¹ cone data and
the positive expansion/S1 margins are premises. No smallness or bound for
the initial derivative is added. The datum's first derivative may determine
the already chosen local time; no estimate constant is selected here. -/
theorem Null.smooth_regularity_classical
    {c a L e ℓ κ : ℝ} {lam₀ : ℝ → ℝ} {h₀ : ℝ → ℂ}
    (Z : ContinuationPair c a L) (ha : 0 < a) (haL : a ≤ L)
    (hℓ : 0 < ℓ) (hκ : 0 < κ)
    (cl₀ : ContDiffOn ℝ 1 lam₀ (Icc c (c + L)))
    (ch₀ : ContDiffOn ℝ 1 h₀ (Icc c (c + L)))
    (hb : ∀ p ∈ continuationWedge c a L,
      ℓ ≤ Z.lam p.1 p.2 ∧ κ ≤ 1 - Recon.mu e Z.lam Z.hh p.1 p.2)
    (hfixed : Z.IsFixedPoint e lam₀ h₀) :
    ContDiffOn ℝ 1 (Function.uncurry Z.hh) (continuationWedge c a L) ∧
      IsC1Solution e (Recon.toFields e Z.lam Z.hh) (continuationWedge c a L) := by
  have hS := continuation_recovery_input c a L e ℓ κ lam₀ h₀ Z
    ha haL hℓ hκ cl₀ ch₀ hb hfixed
  refine ⟨hS.c1_a.congr ?_, hS⟩
  intro p hp
  exact (Recon.toFields_a_eq (e := e) ((hℓ.trans_le (hb p hp).1).ne')).symm

end EmcsfAcExtension.Local
