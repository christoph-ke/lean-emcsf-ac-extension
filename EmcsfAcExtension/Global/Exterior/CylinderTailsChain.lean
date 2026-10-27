module

public import EmcsfAcExtension.Global.Exterior.CylinderTailsGeometry
public import EmcsfAcExtension.Global.Exterior.FrontierTails

/-! # Boundary calculus on actual proper cylinders

These consumers discharge the geometric label-change hypotheses from the
radius level equation. All local constants disappear from the resulting
integrability and covariant-variation estimates. Source:
`charged_SF_new_version.tex:L1393–L1409`, L1413–L1416.
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The covariant variation of an actual proper cylinder trace is at most its
incoming transport cost plus its outgoing exit cost. The numerical
coefficient is `1`, uniformly in cylinder radius, proper endpoints,
solution and coupling. Local geometric constants are fully discharged.
-/
theorem cylinder_covariant_variation_le_of_graph
    {ui e a b ρ : ℝ} {S : Fields} {V : ℝ → ℝ}
    (h : OriginalData ui e S) (hia : ui ≤ a) (hab : a < b) (hb : b < 0)
    (hV : ContinuousOn V (Icc a b))
    (hroot : ∀ u ∈ Icc a b, u < V u ∧ V u ≤ 0 ∧ S.r u (V u) = ρ) :
    curveCovVar e S S.a id V a b ≤ ENNReal.ofReal
      ((∫ u in a..b, ‖(-S.nu u (V u) / ((1 - S.mu u (V u)) * S.r u (V u)) : ℝ) *
        ((S.mu u (V u) - S.Q u (V u) ^ 2 / S.r u (V u) ^ 2 : ℝ) *
          (S.theta u (V u) / (S.lam u (V u) : ℂ)) + I * e * S.Q u (V u) * S.phi u (V u))‖) +
      ∫ u in a..b, ‖deriv V u • densityRepresentative e S a u (V u)‖) := by
  obtain ⟨K, hK, m, hm, hVL, hdist, _⟩ :=
    cylinder_bilipschitz_of_graph h hia hab.le hb hV hroot
  have hVL' : LipschitzOnWith (Real.toNNReal K) V (uIcc a b) := by
    simpa only [uIcc_of_le hab.le] using hVL
  have hmono : MonotoneOn V (uIcc a b) := by
    simpa only [uIcc_of_le hab.le] using
      (cylinder_label_strictMono_of_graph h hia hb hroot).monotoneOn
  have hdist' : ∀ u ∈ uIcc a b, ∀ w ∈ uIcc a b,
      m * dist u w ≤ dist (V u) (V w) := by
    simpa only [uIcc_of_le hab.le] using hdist
  apply boundary_covariant_variation_le h.solution hab hVL' hmono
    (boundary_antilipschitz_of_inverse_distance hm hdist')
  · intro u hu
    rw [uIcc_of_le hab.le] at hu
    have hr := hroot u hu
    exact ⟨hia.trans hu.1, hu.2.trans_lt hb, hr.1.le, hr.2.1⟩
  · simpa only [uIcc_of_le hab.le] using fun u hu => (hroot u hu).1

end EmcsfAcExtension.Global.Exterior
