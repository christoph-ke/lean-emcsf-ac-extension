module

public import EmcsfAcExtension.Local.Broad.Setup

/-! # Continuity of the broad mass ratio through the regular axis

The frozen axis limit is combined with the zero quotient on the axis.
The result is joint relative continuity, also on complete triangles.
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Local.Broad

/-- The mass ratio is jointly continuous on the domain of a frozen broad
solution. At the axis its stipulated limit agrees with the total quotient
value. This is qualitative and has no constants or additional premises. -/
theorem continuousOn_mu {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) : ContinuousOn (Function.uncurry S.mu) D := by
  have haxiszero : ∀ p ∈ D ∩ {p : ℝ × ℝ | p.1 = p.2}, S.mu p.1 p.2 = 0 := by
    rintro ⟨u, v⟩ ⟨hp, huv⟩
    change u = v at huv
    subst v
    simp only [Fields.mu, (hS.axis u hp).1, div_zero]
  have caxis : ContinuousOn (Function.uncurry S.mu) (D ∩ {p : ℝ × ℝ | p.1 = p.2}) :=
    continuousOn_const.congr haxiszero
  have hsplit : D = (D ∩ {p : ℝ × ℝ | p.1 < p.2}) ∪
      (D ∩ {p : ℝ × ℝ | p.1 = p.2}) := by
    ext p
    constructor
    · intro hp
      rcases lt_or_eq_of_le (show p.1 ≤ p.2 from hS.subset hp) with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
    · rintro (h | h) <;> exact h.1
  intro p hp
  by_cases hlt : p.1 < p.2
  · exact ((continuousWithinAt_const.mul (hS.cont_m p hp)).div (hS.cont_r p hp)
      (hS.r_pos p hp hlt).ne')
  · have heq : p.1 = p.2 := le_antisymm (show p.1 ≤ p.2 from hS.subset hp) (le_of_not_gt hlt)
    have hz : S.mu p.1 p.2 = 0 := haxiszero p ⟨hp, heq⟩
    have hm : ContinuousWithinAt (Function.uncurry S.mu)
        (D ∩ {p : ℝ × ℝ | p.1 < p.2}) p := by
      rcases p with ⟨u, v⟩
      dsimp only at heq
      subst v
      simpa only [ContinuousWithinAt, Function.uncurry_def, hz] using hS.axis_mu u hp
    rw [hsplit]
    exact hm.union (caxis p ⟨hp, heq⟩)

end EmcsfAcExtension.Local.Broad
