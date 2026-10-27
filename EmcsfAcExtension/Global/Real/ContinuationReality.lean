module

public import EmcsfAcExtension.Global.Real.Restart
public import EmcsfAcExtension.Global.Real.RestartDatum
public import EmcsfAcExtension.Global.Real.RestartReality
public import EmcsfAcExtension.Global.Real.ScalarReality
public import EmcsfAcExtension.Global.Real.MaxwellZero

/-! # Reality of the joint restart and continuation

internal project record R6: increasing null coordinates map the new triangle into the restart
triangle. The real Jacobian factors preserve scalar reality. The original and
new axis gauges then give vanishing Maxwell fields on the glued union.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Real

/-- [internal]
An increasing null relabelling with the prescribed endpoints pulls real scalar
fields back to real scalar fields on the new triangle (internal project record R6, items 1–2).
Only the real Jacobian factors in `nullPullback` are needed. -/
theorem nullPullback_scalar_im_zero {us vp T : ℝ} {F : ℝ ≃o ℝ} {N : Fields}
    (hz : F us = 0) (hend : F vp = T)
    (hreal : ∀ p ∈ triangle 0 T, (N.phi p.1 p.2).im = 0 ∧
      (N.theta p.1 p.2).im = 0 ∧ (N.xi p.1 p.2).im = 0) :
    ∀ p ∈ triangle us vp, ((nullPullback N F F).phi p.1 p.2).im = 0 ∧
      ((nullPullback N F F).theta p.1 p.2).im = 0 ∧
      ((nullPullback N F F).xi p.1 p.2).im = 0 := by
  intro p hp
  have hpF : (F p.1, F p.2) ∈ triangle 0 T :=
    ⟨hz ▸ F.monotone hp.1, F.monotone hp.2.1, hend ▸ F.monotone hp.2.2⟩
  obtain ⟨hphi, htheta, hxi⟩ := hreal _ hpF
  refine ⟨hphi, ?_, ?_⟩ <;>
    simp only [nullPullback, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      htheta, hxi, mul_zero, zero_mul, add_zero]

/-- [internal]
The same joint restart and glued witness extends a real uncharged development
with all scalar fields real and both Maxwell fields zero on the whole union.
The cone input is exactly that of `restart_and_glue_of_cone`; the local theorem
is applied only there (internal project record R4–R6 and Assembly). -/
theorem real_continuation_of_cone (hlocal : LocalTheoremStatement)
    (ui : ℝ) (S : Fields) (hold : OriginalData ui 0 S)
    (hcone : ∀ η : ℝ, 0 < η → ∃ us ∈ Ioo ui 0,
      AbsolutelyContinuousOnInterval (S.a us) us 0 ∧
      eVariationOn (S.a us) (Icc us 0) ≤ ENNReal.ofReal η ∧
      |(0 : ℝ)| * (2 * S.r us 0) *
        (1 + ‖S.phi us us‖ + 10 * (eVariationOn (S.a us) (Icc us 0)).toReal) ≤ η)
    (hreal : ∀ p ∈ origDomain ui, (S.phi p.1 p.2).im = 0) :
    ∃ us vp : ℝ, ∃ S' : Fields, ui < us ∧ us < 0 ∧ 0 < vp ∧
      IsSolution 0 S' (origDomain ui ∪ triangle us vp) ∧
      (∀ t ∈ Icc us vp, S'.A t t = 0) ∧ S'.EqOn S (origDomain ui) ∧
      ∀ p ∈ origDomain ui ∪ triangle us vp,
        (S'.phi p.1 p.2).im = 0 ∧ (S'.theta p.1 p.2).im = 0 ∧
        (S'.xi p.1 p.2).im = 0 ∧ S'.Q p.1 p.2 = 0 ∧ S'.A p.1 p.2 = 0 := by
  have htransport := theta_xi_im_zero_of_phi_im_zero hold.solution hreal
  obtain ⟨us, hus, F, _hF, hz, hL, hnorm, N, hN, hgN, hdN, huniq,
      vp, hvp, hFvp, G, hG, hgG, hGo, hGp⟩ :=
    restart_and_glue_of_cone hlocal ui 0 S hold hcone
  have hdatum := restart_datum_im_zero hus hz hL hnorm hreal
    (fun p hp => (htransport p hp).1)
  have hrestart := (restart_reality_of_unique_real_datum
    (mul_pos (by norm_num) hL) hN hgN hdN hdatum huniq).2
  have hpull := nullPullback_scalar_im_zero hz hFvp hrestart
  have hmaxwell := charge_potential_zero_origDomain_union_triangle hG (by
    intro t ht
    rcases ht with ht | ht
    · rw [hGo.A ht]
      exact hold.gauge t ht.1 ht.2.1
    · exact hgG t ⟨ht.1, ht.2.2⟩)
  refine ⟨us, vp, G, hus.1, hus.2, hvp, hG, hgG, hGo, ?_⟩
  intro p hp
  obtain ⟨hQ, hA⟩ := hmaxwell p hp
  suffices (G.phi p.1 p.2).im = 0 ∧ (G.theta p.1 p.2).im = 0 ∧
      (G.xi p.1 p.2).im = 0 from
    ⟨this.1, this.2.1, this.2.2, hQ, hA⟩
  rcases hp with hp | hp
  · rw [hGo.phi hp, hGo.theta hp, hGo.xi hp]
    exact ⟨hreal p hp, htransport p hp⟩
  · rw [hGp.phi hp, hGp.theta hp, hGp.xi hp]
    exact hpull p hp

end EmcsfAcExtension.Global.Real
