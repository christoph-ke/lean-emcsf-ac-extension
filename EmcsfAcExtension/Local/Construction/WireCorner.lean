module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
public import EmcsfAcExtension.Frozen.Fields.EqOn
import EmcsfAcExtension.Local.Construction.WireShort
import EmcsfAcExtension.Local.Construction.WireRecovery
import EmcsfAcExtension.Local.Construction.CornerAssembly

/-! # The approved C¹ axis-corner route

This export discharges both producer premises of the landed corner fill
and associates the result with internal project record's explicit internal project record route.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- [node restart-sec-independent-null-construction#axis-corner-fill]
[node restart-sec-independent-null-construction#axis-corner-fill#route-bp-c1]
Fill the closed axis corner by the approved C¹ route. The positive time
depends only on `B,ℓ,|e|`, before corner positions, datum and the old/strip
configuration. Both the short-cone and full-system inputs are discharged. -/
theorem c1_axis_corner_fill
    (B ℓ e : ℝ) (hB : 1 ≤ B) (hℓ : 0 < ℓ) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ (c d S b : ℝ) (H : Fields) (h : ℝ → ℂ),
        0 ≤ c → c < d → d < S → S < b → b-c ≤ τ →
        IsC1Solution e H (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) →
        (∀ p ∈ triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b),
          ∀ f ∈ ({H.lam} : Set (ℝ → ℝ → ℝ)),
            ‖f p.1 p.2‖ ≤ 2*B ∧
            ‖fderivWithin ℝ (Function.uncurry f)
              (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) p‖ ≤ 2*B) →
        (∀ p ∈ triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b),
          ∀ f ∈ ({H.phi, H.theta} : Set (ℝ → ℝ → ℂ)),
            ‖f p.1 p.2‖ ≤ 2*B ∧
            ‖fderivWithin ℝ (Function.uncurry f)
              (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) p‖ ≤ 2*B) →
        (∀ p ∈ triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b), ℓ/2 ≤ H.lam p.1 p.2) →
        (∀ v ∈ Icc 0 b, H.r 0 v = v/2 ∧ H.a 0 v = h v) →
        (∀ t ∈ Icc 0 S, H.A t t = 0) →
        ∃ F : Fields, IsC1Solution e F (triangle 0 b) ∧
          IsRestartData F h b ∧
          F.EqOn H (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) := by
  exact c1_axis_corner_fill_of_inputs continuation_short_picard_input
    continuation_recovery_input B ℓ e hB hℓ

end EmcsfAcExtension.Local
