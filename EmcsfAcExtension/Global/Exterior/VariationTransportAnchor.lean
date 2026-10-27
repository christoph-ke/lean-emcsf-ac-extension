module

public import EmcsfAcExtension.Global.Calculus.CurveTrace

/-! # Changing the initial row of the prescribed boundary density

Both initial-row densities occur in the AC chain rule for the same field
trace and give the same weighted value. A countable exhaustion retains
this equality on the complete existing boundary.
Source: `charged_SF_new_version.tex:L1413–L1416`.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [node c:exterior#derivative-ac-representation]
Along every proper increasing bi-Lipschitz boundary, canonical densities
based at two initial rows have the same weighted boundary value almost
everywhere. Both chain rules concern the same field trace. There is no
density hypothesis and no speed-cancellation argument. -/
theorem densityRepresentative_boundary_anchor_weighted_eq
    {ui e c a b : ℝ} {S : Fields} {V : ℝ → ℝ} {K L : ℝ≥0}
    (hS : IsSolution e S (origDomain ui)) (hca : c ≤ a) (hab : a ≤ b)
    (hV : LipschitzOnWith K V (uIcc c b)) (hm : MonotoneOn V (uIcc c b))
    (ha : AntilipschitzWith L ((uIcc c b).domRestrict V))
    (hmem : ∀ u ∈ uIcc c b, (u, V u) ∈ origDomain ui)
    (hproper : ∀ u ∈ uIcc c b, u < V u) :
    ∀ᵐ u ∂volume.restrict (Icc a b),
      deriv V u • densityRepresentative e S c u (V u) =
        deriv V u • densityRepresentative e S a u (V u) := by
  by_cases hab' : a < b
  · have hcb : c < b := hca.trans_lt hab'
    have hsub : uIcc a b ⊆ uIcc c b := by
      rw [uIcc_of_le hab, uIcc_of_le hcb.le]
      exact Icc_subset_Icc hca le_rfl
    have ha' : AntilipschitzWith L ((uIcc a b).domRestrict V) := by
      intro x y
      exact ha ⟨x, hsub x.property⟩ ⟨y, hsub y.property⟩
    have hc := (Calculus.timelike_ac_chain_rule hS hcb
      (LipschitzWith.id.lipschitzOnWith : LipschitzOnWith 1 id (uIcc c b)) hV
      (monotone_id.monotoneOn _) hm (AntilipschitzWith.id.domRestrict (uIcc c b)) ha
      hmem hproper).2
    have hn := (Calculus.timelike_ac_chain_rule hS hab'
      (LipschitzWith.id.lipschitzOnWith : LipschitzOnWith 1 id (uIcc a b)) (hV.mono hsub)
      (monotone_id.monotoneOn _) (hm.mono hsub)
      (AntilipschitzWith.id.domRestrict (uIcc a b)) ha'
      (fun u hu => hmem u (hsub hu)) (fun u hu => hproper u (hsub hu))).2
    rw [uIcc_of_le hcb.le] at hc
    rw [uIcc_of_le hab] at hn
    have hc' := hc.filter_mono (ae_mono (Measure.restrict_mono
      (Icc_subset_Icc hca le_rfl : Icc a b ⊆ Icc c b) le_rfl))
    filter_upwards [hc', hn] with u hcu hau
    simpa only [id_eq, (hasDerivAt_id u).deriv, one_smul, add_left_inj, add_right_inj]
      using hcu.unique hau
  · have haeq : a = b := le_antisymm hab (not_lt.mp hab')
    simp only [haeq, Icc_self, Measure.restrict_singleton, measure_singleton,
      zero_smul, ae_zero, Filter.eventually_bot]

end EmcsfAcExtension.Global.Exterior
