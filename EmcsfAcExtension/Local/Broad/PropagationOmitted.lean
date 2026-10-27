module

public import EmcsfAcExtension.Local.Broad.Propagation

/-! # Broad uniqueness when the final axis apex is omitted

Proper closed subtriangles give equality below the final outgoing edge.
Positive-radius rectangles then supply that entire edge except the
omitted apex. The common entering cone includes its final endpoint.
-/

public section

open Set

namespace EmcsfAcExtension.Local

open Broad

/-- [node restart-stab-broad-uniqueness#overlap-uniqueness-propagation]
The apex-omitted characteristic development also has broad uniqueness,
as approved in amendment internal project record. Its existing axis
points carry the zero gauge. Equality on every proper compact subdomain
follows by restriction, without an arbitrary-domain propagation claim. -/
theorem broad_uniqueness_apex_omitted {e a b : ℝ} {S₁ S₂ : Fields} (hab : a < b)
    (hS₁ : IsSolution e S₁ (triangle a b \ {(b, b)}))
    (hS₂ : IsSolution e S₂ (triangle a b \ {(b, b)}))
    (hdata : ∀ v ∈ Icc a b, S₁.r a v = S₂.r a v ∧ S₁.a a v = S₂.a a v)
    (hg : ∀ t ∈ Ico a b, S₁.A t t = 0 ∧ S₂.A t t = 0) :
    S₁.EqOn S₂ (triangle a b \ {(b, b)}) := by
  have hproper c (hac : a < c) (hcb : c < b) : S₁.EqOn S₂ (triangle a c) := by
    have hsub : triangle a c ⊆ triangle a b \ {(b, b)} := by
      intro p hp
      refine ⟨⟨hp.1, hp.2.1, hp.2.2.trans hcb.le⟩, ?_⟩
      intro he
      have hv := congrArg Prod.snd he
      change p.2 = b at hv
      linarith [hp.2.2]
    apply broad_uniqueness hac (isSolution_mono hS₁ hsub) (isSolution_mono hS₂ hsub)
    · intro v hv
      exact hdata v ⟨hv.1, hv.2.trans hcb.le⟩
    · intro t ht
      exact hg t ⟨ht.1, ht.2.trans_lt hcb⟩
  have hconeSub : outSeg a a b ⊆ triangle a b \ {(b, b)} := by
    rintro p ⟨hu, hv⟩
    change p.1 = a at hu
    refine ⟨⟨hu.symm.le, hu ▸ hv.1, hv.2⟩, ?_⟩
    intro he
    have he' := congrArg Prod.fst he
    change p.1 = b at he'
    exact hab.ne (hu.symm.trans he')
  have hcone := common_data_initial_constraint_agreement hS₁ hS₂ hab hconeSub hconeSub
    hdata (hg a ⟨le_rfl, hab⟩).1 (hg a ⟨le_rfl, hab⟩).2
  intro p hp
  by_cases hpb : p.2 < b
  · let c := (p.2 + b) / 2
    have hac : a < c := by dsimp [c]; linarith [hp.1.1, hp.1.2.1]
    have hcb : c < b := by dsimp [c]; linarith
    apply hproper c hac hcb p
    exact ⟨hp.1.1, hp.1.2.1, by dsimp [c]; linarith⟩
  · have hvb : p.2 = b := le_antisymm hp.1.2.2 (le_of_not_gt hpb)
    have hub : p.1 < b := by
      apply lt_of_le_of_ne (hp.1.2.1.trans hp.1.2.2)
      intro hu
      exact hp.2 (Prod.ext hu hvb)
    let c := (p.1 + b) / 2
    have huc : p.1 < c := by dsimp [c]; linarith
    have hcb : c < b := by dsimp [c]; linarith
    have hac : a < c := hp.1.1.trans_lt huc
    have hrsub : Icc a p.1 ×ˢ Icc c b ⊆ triangle a b \ {(b, b)} := by
      rintro z ⟨hu, hv⟩
      refine ⟨⟨hu.1, hu.2.trans (huc.le.trans hv.1), hv.2⟩, ?_⟩
      intro he
      have he' := congrArg Prod.fst he
      change z.1 = b at he'
      linarith [hu.2]
    have hrect : S₁.EqOn S₂ (Icc a p.1 ×ˢ Icc c b) := by
      apply broad_rectangle_uniqueness hp.1.1 hcb.le huc
        (isSolution_mono hS₁ hrsub) (isSolution_mono hS₂ hrsub)
      rintro z (⟨hu, hv⟩ | ⟨hu, hv⟩)
      · change z.1 = a at hu
        exact hcone z ⟨hu, hac.le.trans hv.1, hv.2⟩
      · change z.2 = c at hv
        exact hproper c hac hcb z ⟨hu.1, hu.2.trans (huc.le.trans hv.symm.le), hv.le⟩
    apply hrect p
    exact ⟨⟨hp.1.1, le_rfl⟩, by rw [hvb]; exact ⟨hcb.le, le_rfl⟩⟩

end EmcsfAcExtension.Local
