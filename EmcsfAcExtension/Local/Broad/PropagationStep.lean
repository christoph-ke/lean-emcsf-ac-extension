module

public import EmcsfAcExtension.Local.Broad.AxisUniqueness
public import EmcsfAcExtension.Local.Broad.Rectangle
public import EmcsfAcExtension.Local.Api.EqOn

/-! # Extending equality past a proper apex

A positive rectangle supplies the later part of a nearby entering cone.
Local axis uniqueness then fills the new small axis triangle. Together
with the old triangle these cover the enlarged characteristic development.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- Equality on a proper nondegenerate initial subtriangle extends to a
strictly later apex inside the same complete characteristic development.
The common entering cone and zero-axis gauges are literal data; no
future axis values or arbitrary-domain propagation are assumed. -/
theorem broad_extend_triangle_equality {e a b q : ℝ} {S₁ S₂ : Fields}
    (haq : a < q) (hqb : q < b)
    (hS₁ : IsSolution e S₁ (triangle a b)) (hS₂ : IsSolution e S₂ (triangle a b))
    (hcone : S₁.EqOn S₂ (outSeg a a b))
    (hg : ∀ t ∈ Icc a b, S₁.A t t = 0 ∧ S₂.A t t = 0)
    (hold : S₁.EqOn S₂ (triangle a q)) :
    ∃ q' : ℝ, q < q' ∧ q' ≤ b ∧ S₁.EqOn S₂ (triangle a q') := by
  obtain ⟨δ, hδ, haxis⟩ := broad_local_axis_uniqueness_of_compact hS₁ hS₂
    (isCompact_triangle a b) ⟨haq.le, le_rfl, hqb.le⟩
  let η := min δ ((b - q) / 2)
  have hη : 0 < η := lt_min hδ (by linarith)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηb : η ≤ (b - q) / 2 := min_le_right _ _
  have htop : q + η ≤ b := by linarith
  let s := max a (q - η)
  have has : a ≤ s := le_max_left _ _
  have hsq : s < q := max_lt haq (by linarith)
  have hqs : q - η ≤ s := le_max_right _ _
  have hrsub : Icc a s ×ˢ Icc q (q + η) ⊆ triangle a b := by
    rintro p ⟨hu, hv⟩
    exact ⟨hu.1, hu.2.trans (hsq.le.trans hv.1), hv.2.trans htop⟩
  have hrect : S₁.EqOn S₂ (Icc a s ×ˢ Icc q (q + η)) := by
    apply broad_rectangle_uniqueness has (by linarith) hsq
      (isSolution_mono hS₁ hrsub) (isSolution_mono hS₂ hrsub)
    rintro p (⟨hu, hv⟩ | ⟨hu, hv⟩)
    · change p.1 = a at hu
      exact hcone p ⟨hu, haq.le.trans hv.1, hv.2.trans htop⟩
    · change p.2 = q at hv
      exact hold p ⟨hu.1, hu.2.trans (hsq.le.trans hv.symm.le), hv.le⟩
  have hlocalsub : triangle s (q + η) ⊆ triangle a b := triangle_mono has htop
  have hlocal : S₁.EqOn S₂ (triangle s (q + η)) := by
    apply haxis η hη hηδ s hqs hsq.le hlocalsub
    · intro v hv
      by_cases hvq : v ≤ q
      · have hp : (s, v) ∈ triangle a q := ⟨has, hv.1, hvq⟩
        exact ⟨hold.r hp, hold.a hp⟩
      · have hp : (s, v) ∈ Icc a s ×ˢ Icc q (q + η) :=
          ⟨⟨has, le_rfl⟩, (lt_of_not_ge hvq).le, hv.2⟩
        exact ⟨hrect.r hp, hrect.a hp⟩
    · intro u hu
      exact hg u ⟨has.trans hu.1, hu.2.trans htop⟩
  refine ⟨q + η, by linarith, htop, ?_⟩
  intro p hp
  by_cases hpq : p.2 ≤ q
  · exact hold p ⟨hp.1, hp.2.1, hpq⟩
  · by_cases hps : p.1 ≤ s
    · exact hrect p ⟨⟨hp.1, hps⟩, (lt_of_not_ge hpq).le, hp.2.2⟩
    · exact hlocal p ⟨(lt_of_not_ge hps).le, hp.2⟩

end EmcsfAcExtension.Local
