module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
import EmcsfAcExtension.Local.Construction.ConeBounds
import EmcsfAcExtension.Local.Construction.Corner
import EmcsfAcExtension.Local.Construction.Overlap
import EmcsfAcExtension.Local.Construction.CornerGlue
import EmcsfAcExtension.Local.Api.EqOn

import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Filling the axis corner of a classical continuation

The enlarged cone bound fixes the short-cone time before any corner
position is chosen. The constructed corner supplies its own axis gauge;
only the old part of the original configuration has a prescribed gauge.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- An old triangle, a wider strip and a later axis corner cover the
entire capped triangle. The nonstrict overlap condition suffices for
this set identity; differentiation is handled separately. -/
theorem continuation_triangle_corner_cover {c d S b : ℝ}
    (hc : 0 ≤ c) (hcd : c ≤ d) (hdS : d ≤ S) (hSb : S ≤ b) :
    (triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)) ∪ triangle c b = triangle 0 b := by
  ext p
  constructor
  · rintro ((hp | hp) | hp)
    · exact ⟨hp.1, hp.2.1, hp.2.2.trans hSb⟩
    · exact ⟨hp.1.1, hp.1.2.trans (hdS.trans hp.2.1), hp.2.2⟩
    · exact ⟨hc.trans hp.1, hp.2⟩
  · intro hp
    by_cases hv : p.2 ≤ S
    · exact Or.inl (Or.inl ⟨hp.1, hp.2.1, hv⟩)
    · by_cases hu : c ≤ p.1
      · exact Or.inr ⟨hu, hp.2⟩
      · exact Or.inl (Or.inr ⟨⟨hp.1, (le_of_lt (lt_of_not_ge hu)).trans hcd⟩,
          (le_of_lt (lt_of_not_ge hv)), hp.2.2⟩)

/-- [internal]
In the C¹ reading of charged_SF_new_version.tex:L6299–6307 and internal project record,
a completed old/strip solution with
the primary first-jet bounds admits an axis-corner fill. The uniform
time depends only on `B`, `ℓ` and `|e|`, through the exact enlarged cone
bound and the short-cone construction input. It is chosen before the
corner positions, datum and old/strip configuration. No future-axis
gauge of that configuration is assumed. -/
theorem c1_axis_corner_fill_of_inputs
    (hPicard : ContinuationShortPicardInput) (hRecovery : ContinuationRecoveryInput)
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
  let Bc := 1+16*(B+1)*(1+ℓ⁻¹)+64*(B+1)^2*ℓ⁻¹^2
  have hBc : 1 ≤ Bc := by
    have hi : 0 ≤ ℓ⁻¹ := (inv_pos.mpr hℓ).le
    have hb : 0 ≤ B+1 := by linarith
    have h1 : 0 ≤ 16*(B+1)*(1+ℓ⁻¹) := by positivity
    have h2 : 0 ≤ 64*(B+1)^2*ℓ⁻¹^2 := by positivity
    dsimp only [Bc]
    linarith only [h1, h2]
  obtain ⟨τ, hτ, hlocal⟩ := short_cone_solution_of_inputs hPicard hRecovery
    Bc (ℓ/2) e hBc (by positivity)
  refine ⟨τ, hτ, ?_⟩
  intro c d S b H h hc hcd hdS hSb hlength hH hreal hcomplex hmargin hdata hgauge
  have hcs : c < S := hcd.trans hdS
  have hcb : c < b := hcs.trans hSb
  have hS : 0 < S := hc.trans_lt hcs
  have hd : 0 < d := hc.trans_lt hcd
  let A := triangle 0 S ∪ (Icc 0 d ×ˢ Icc S b)
  have hcone : ∀ v ∈ Icc c (c+(b-c)), (c,v) ∈ A := by
    intro v hv
    have hvb : v ≤ b := by linarith [hv.2]
    by_cases hvS : v ≤ S
    · exact Or.inl ⟨hc, hv.1, hvS⟩
    · exact Or.inr ⟨⟨hc, hcd.le⟩, (lt_of_not_ge hvS).le, hvb⟩
  obtain ⟨cl, ch, hbound⟩ := continuation_cone_pair_bound (B := B) hH (by linarith) hℓ
    hreal hcomplex hmargin (by linarith : 0 < b-c) hcone
  obtain ⟨G, hG, hpair, hgaugeG⟩ := hlocal c (b-c) (H.lam c) (H.a c)
    (by linarith) hlength cl ch hbound
  have hsum : c+(b-c) = b := by ring
  rw [hsum] at hG hpair hgaugeG
  have hHG : H.EqOn G (A ∩ triangle c b) :=
    c1_corner_union_overlap hc hcd hdS hSb hH hG
      (fun v hv => ⟨(hpair v hv).1.symm, (hpair v hv).2.symm⟩) hgauge hgaugeG
  have hclosedA : IsClosed A :=
    (isClosed_triangle 0 S).union (isClosed_Icc.prod isClosed_Icc)
  have huniqueA : UniqueDiffOn ℝ A := by
    intro p hp
    rcases hp with hp | hp
    · exact (uniqueDiffOn_triangle hS p hp).mono subset_union_left
    · exact (uniqueDiffOn_rectangle hd hSb p hp).mono subset_union_right
  have hglue := c1_continuationGlue_of_uniqueDiff_overlap hclosedA
    (isClosed_triangle c b) huniqueA (uniqueDiffOn_triangle hcb)
    (continuation_axis_overlap_uniqueDiff hc hcd hdS hSb) hH hG hHG
  have hcover : A ∪ triangle c b = triangle 0 b :=
    continuation_triangle_corner_cover hc hcd.le hdS.le hSb.le
  rw [hcover] at hglue
  let F := continuationGlue A H G
  have hFH : F.EqOn H A := continuationGlue_eqOn_left A H G
  have hFG : F.EqOn G (triangle c b) := continuationGlue_eqOn_right hHG
  refine ⟨F, hglue, ⟨?_, ?_⟩, hFH⟩
  · intro v hv
    have hp : (0,v) ∈ A := by
      by_cases hvS : v ≤ S
      · exact Or.inl ⟨le_rfl, hv.1, hvS⟩
      · exact Or.inr ⟨⟨le_rfl, hd.le⟩, (lt_of_not_ge hvS).le, hv.2⟩
    exact ⟨(hFH.r hp).trans (hdata v hv).1, (hFH.a hp).trans (hdata v hv).2⟩
  · intro t ht
    by_cases htS : t ≤ S
    · have hp : (t,t) ∈ A := Or.inl ⟨ht.1, le_rfl, htS⟩
      exact (hFH.A hp).trans (hgauge t ⟨ht.1, htS⟩)
    · have hct : c ≤ t := hcs.le.trans (lt_of_not_ge htS).le
      have hp : (t,t) ∈ triangle c b := ⟨hct, le_rfl, ht.2⟩
      exact (hFG.A hp).trans (hgaugeG t ⟨hct, ht.2⟩)

end EmcsfAcExtension.Local
