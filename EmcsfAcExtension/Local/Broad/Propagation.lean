module

public import EmcsfAcExtension.Local.Broad.PropagationStep
public import EmcsfAcExtension.Local.Broad.PropagationClosure
public import EmcsfAcExtension.Local.Broad.GeometryInitial

/-! # Broad uniqueness on the common entering cone's complete development

Local axis equality starts the comparison. A first-apex argument using
positive rectangles and local axis triangles carries equality across
the complete closed triangle, including its final edge and apex.
-/

public section

open Set

namespace EmcsfAcExtension.Local

open Broad

/-- [node restart-stab-broad-uniqueness#overlap-uniqueness-propagation]
Two frozen broad solutions with common entering radius and normalized
scalar datum and zero-axis gauges agree on their complete triangle.
This is amendment internal project record, charged_SF_new_version.tex:L5905–5906 and internal
project record
There are no size, envelope, auxiliary hypothesis or domain-shape
premises beyond the literal characteristic development. In particular
`a=0` directly serves the frozen root's complete-triangle uniqueness clause. -/
theorem broad_uniqueness {e a b : ℝ} {S₁ S₂ : Fields} (hab : a < b)
    (hS₁ : IsSolution e S₁ (triangle a b)) (hS₂ : IsSolution e S₂ (triangle a b))
    (hdata : ∀ v ∈ Icc a b, S₁.r a v = S₂.r a v ∧ S₁.a a v = S₂.a a v)
    (hg : ∀ t ∈ Icc a b, S₁.A t t = 0 ∧ S₂.A t t = 0) :
    S₁.EqOn S₂ (triangle a b) := by
  have hconeSub : outSeg a a b ⊆ triangle a b := by
    rintro p ⟨rfl, hv⟩
    exact ⟨le_rfl, hv⟩
  have hcone := common_data_initial_constraint_agreement hS₁ hS₂ hab hconeSub hconeSub
    hdata (hg a ⟨le_rfl, hab.le⟩).1 (hg a ⟨le_rfl, hab.le⟩).2
  obtain ⟨δ, hδ, hlocal⟩ := broad_local_axis_uniqueness_of_compact hS₁ hS₂
    (isCompact_triangle a b) ⟨le_rfl, le_rfl, hab.le⟩
  let η := min δ ((b - a) / 2)
  have hη : 0 < η := lt_min hδ (by linarith)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηb : η ≤ (b - a) / 2 := min_le_right _ _
  have htop : a + η ≤ b := by linarith
  have hstart : S₁.EqOn S₂ (triangle a (a + η)) := by
    apply hlocal η hη hηδ a (by linarith) le_rfl (triangle_mono le_rfl htop)
    · intro v hv
      exact hdata v ⟨hv.1, hv.2.trans htop⟩
    · intro t ht
      exact hg t ⟨ht.1, ht.2.trans htop⟩
  let E : Set ℝ := {t | t ∈ Icc a b ∧ S₁.EqOn S₂ (triangle a t)}
  have hEstart : a + η ∈ E := ⟨⟨by linarith, htop⟩, hstart⟩
  have hEne : E.Nonempty := ⟨a + η, hEstart⟩
  have hEbd : BddAbove E := ⟨b, fun t ht => ht.1.2⟩
  let q := sSup E
  have hqb : q ≤ b := csSup_le hEne (fun t ht => ht.1.2)
  have haq : a < q := (show a < a + η by linarith).trans_le (le_csSup hEbd hEstart)
  have hlimit : S₁.EqOn S₂ (triangle a q) := by
    apply triangle_equality_at_limit_of_below haq hqb hS₁ hS₂
    intro t ht
    obtain ⟨r, hr, htr⟩ := exists_lt_of_lt_csSup hEne ht.2
    exact hr.2.mono (triangle_mono le_rfl htr.le)
  have heq : q = b := by
    apply le_antisymm hqb
    by_contra hn
    have hqb' : q < b := lt_of_not_ge hn
    obtain ⟨r, hqr, hrb, hr⟩ := broad_extend_triangle_equality haq hqb' hS₁ hS₂ hcone hg hlimit
    have hrE : r ∈ E := ⟨⟨haq.le.trans hqr.le, hrb⟩, hr⟩
    exact (not_lt_of_ge (le_csSup hEbd hrE)) hqr
  simpa only [heq] using hlimit

end EmcsfAcExtension.Local
