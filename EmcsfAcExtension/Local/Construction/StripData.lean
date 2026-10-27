module

public import EmcsfAcExtension.Local.Broad.RectangleState
public import EmcsfAcExtension.Local.Construction.ContinuationInputs
import EmcsfAcExtension.Local.Broad.RectangleEquations
import EmcsfAcExtension.Local.Construction.StripUniqueness
import EmcsfAcExtension.Local.Construction.ContinuationParameters
import EmcsfAcExtension.Local.Api.EqOn
import EmcsfAcExtension.Local.Api.Mono

/-! # Entering data for positive-radius continuation strips

Broad characteristic integral identities give the literal finite-state
Goursat equations. Uniqueness on a rectangle of zero incoming width
identifies every field on the appended original cone from its entering
block and the single lower corner. No future-axis gauge is prescribed.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

open Broad

/-- A broad solution satisfies the literal Goursat equations for any
entering data agreeing with its incoming left block and outgoing lower
block. The rectangle may have zero width or zero height. -/
theorem broad_rectangle_goursat_eq {e a b c d : ℝ} {S : Fields}
    (_hab : a ≤ b) (_hcd : c ≤ d) (hpos : b < c)
    (hS : IsSolution e S (Icc a b ×ˢ Icc c d))
    {yi : ℝ → RectangleIncoming} {xb : ℝ → RectangleOutgoing}
    (hyi : ∀ v ∈ Icc c d, (rectangle_state S (a, v)).1 = yi v)
    (hxb : ∀ u ∈ Icc a b, (rectangle_state S (u, c)).2 = xb u) :
    (∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (rectangle_state S (u,v)).1 = yi v +
        ∫ s in a..u, rectangle_in_source e (rectangle_state S (s,v))) ∧
    (∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (rectangle_state S (u,v)).2 = xb u +
        ∫ t in c..v, rectangle_out_source e (rectangle_state S (u,t))) := by
  constructor
  · intro u hu v hv
    exact (rectangle_in_integralForm hpos hS hu hv).eq_add_integral.trans
      (congrArg (fun z => z + ∫ s in a..u,
        rectangle_in_source e (rectangle_state S (s,v))) (hyi v hv))
  · intro u hu v hv
    exact (rectangle_out_integralForm hpos hS hu hv).eq_add_integral.trans
      (congrArg (fun z => z + ∫ t in c..v,
        rectangle_out_source e (rectangle_state S (u,t))) (hxb u hu))

/-- The full original entering cone agrees with a broad reference cone
if the prescribed incoming blocks agree and the outgoing blocks agree
at the lower corner. The comparison uses a collapsed-width rectangle,
and does not require C¹ regularity or any future-axis datum. -/
theorem broad_entering_cone_overlap {e T d s b : ℝ} {F₀ New : Fields}
    (hd : 0 ≤ d) (hds : d < s) (hsb : s ≤ b) (hbT : b ≤ T)
    (hF₀ : IsSolution e F₀ (outSeg 0 0 T))
    (hNew : IsSolution e New (Icc 0 d ×ˢ Icc s b))
    (hyi : ∀ v ∈ Icc s b,
      (rectangle_state New (0, v)).1 = (rectangle_state F₀ (0, v)).1)
    (hcorner : (rectangle_state New (0, s)).2 = (rectangle_state F₀ (0, s)).2) :
    New.EqOn F₀ (outSeg 0 s b) := by
  have hs : 0 < s := hd.trans_lt hds
  have hNew' : IsSolution e New (Icc 0 0 ×ˢ Icc s b) :=
    isSolution_mono hNew (by
      intro p hp
      exact ⟨⟨hp.1.1, hp.1.2.trans hd⟩,hp.2⟩)
  have hF₀' : IsSolution e F₀ (Icc 0 0 ×ˢ Icc s b) :=
    isSolution_mono hF₀ (by
      intro p hp
      exact ⟨le_antisymm hp.1.2 hp.1.1,
        hs.le.trans hp.2.1,hp.2.2.trans hbT⟩)
  have heq := broad_rectangle_uniqueness_of_entering_blocks le_rfl hsb hs
    hNew' hF₀' hyi (fun u hu => by
      have hu0 : u = 0 := le_antisymm hu.2 hu.1
      simpa only [hu0] using hcorner)
  intro p hp
  apply heq p
  exact ⟨by simpa only [hp.1] using (show (0 : ℝ) ∈ Icc 0 0 from ⟨le_rfl,le_rfl⟩),hp.2⟩

/-- An appended strip inherits the original radius and normalized
scalar data from the fixed original local wedge. Only the lower corner
is supplied by the old triangle; its complete-cone agreement with the
original wedge determines that corner. No gauge value on a future axis
is assumed or concluded. -/
theorem c1_strip_initial_data {e T a d s b : ℝ} {F₀ Old New : Fields}
    {h : ℝ → ℂ} (ha : 0 < a) (haT : a ≤ T)
    (hd : 0 ≤ d) (hds : d < s) (hsb : s ≤ b) (hbT : b ≤ T)
    (hF₀ : IsC1Solution e F₀ (continuationWedge 0 a T))
    (hOld : IsC1Solution e Old (triangle 0 s))
    (hdata₀ : IsRestartData F₀ h T) (hdataOld : IsRestartData Old h s)
    (hNew : IsSolution e New (Icc 0 d ×ˢ Icc s b))
    (hyi : ∀ v ∈ Icc s b,
      (rectangle_state New (0, v)).1 = (rectangle_state F₀ (0, v)).1)
    (hcorner : (rectangle_state New (0, s)).2 = (rectangle_state Old (0, s)).2) :
    (New.EqOn F₀ (outSeg 0 s b)) ∧
      ∀ v ∈ Icc s b, New.r 0 v = v/2 ∧ New.a 0 v = h v := by
  have hs : 0 < s := hd.trans_lt hds
  have hsT : s ≤ T := hsb.trans hbT
  have hagree := c1_initial_cone_fields_agree ha haT hs hsT hF₀ hOld hdata₀ hdataOld
  have hc : (rectangle_state F₀ (0,s)).2 = (rectangle_state Old (0,s)).2 :=
    congrArg Prod.snd ((rectangle_state_eq_iff F₀ Old (0,s)).mpr
      (hagree (0,s) ⟨rfl,hs.le,le_rfl⟩))
  have heq := broad_entering_cone_overlap hd hds hsb hbT
    (hF₀.toIsSolution_initialCone ha haT) hNew hyi (hcorner.trans hc.symm)
  refine ⟨heq,?_⟩
  intro v hv
  have hp : (0,v) ∈ outSeg 0 s b := ⟨rfl,hv⟩
  have hvt : v ∈ Icc 0 T := ⟨hs.le.trans hv.1,hv.2.trans hbT⟩
  exact ⟨(heq.r hp).trans (hdata₀.1 v hvt).1,
    (heq.a hp).trans (hdata₀.1 v hvt).2⟩

end EmcsfAcExtension.Local
