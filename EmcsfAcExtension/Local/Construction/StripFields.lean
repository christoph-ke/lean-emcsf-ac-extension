module

public import EmcsfAcExtension.Local.Broad.RectangleState
public import EmcsfAcExtension.Local.Defs.C1Class
import EmcsfAcExtension.Local.Construction.StripConstraintsMass
import EmcsfAcExtension.Local.Construction.StripConstraints
import EmcsfAcExtension.Local.Broad.RectangleLipschitz
import EmcsfAcExtension.Local.Construction.StripCharacteristic
import EmcsfAcExtension.Local.Calculus.Partials

/-! # From a finite characteristic state to the full strip solution

The finite-state Goursat equations are the literal frozen source blocks.
This adapter projects their characteristic derivatives and applies the C¹
constraint recovery. Only the outgoing block is prescribed on the old side.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local.Broad

/-- Realize a finite characteristic state function as the nine primary
curried fields, in the exact order used by `rectangle_state`. -/
@[expose] def rectangle_fields (F : ℝ × ℝ → RectangleState) : Fields where
  r := fun u v => (F (u, v)).2.1
  lam := fun u v => (F (u, v)).1.1
  nu := fun u v => (F (u, v)).2.2.1
  m := fun u v => (F (u, v)).2.2.2.1
  Q := fun u v => (F (u, v)).2.2.2.2.1
  A := fun u v => (F (u, v)).2.2.2.2.2.1
  phi := fun u v => (F (u, v)).2.2.2.2.2.2.1
  theta := fun u v => (F (u, v)).1.2
  xi := fun u v => (F (u, v)).2.2.2.2.2.2.2

end EmcsfAcExtension.Local.Broad

namespace EmcsfAcExtension.Local

open Broad

private theorem pdU_eq_of_rectangle_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c d u v : ℝ} {f : ℝ → ℝ → E} {z : E}
    (hab : a < b) (hf : ContDiffOn ℝ 1 (Function.uncurry f) (Icc a b ×ˢ Icc c d))
    (hu : u ∈ Icc a b) (hv : v ∈ Icc c d)
    (hd : HasDerivWithinAt (fun x => f x v) z (Icc a b) u) :
    pdU (Icc a b ×ˢ Icc c d) f u v = z := by
  have hc := hasDerivWithinAt_pdU hf ⟨hu, hv⟩ (fun x hx => ⟨hx, hv⟩)
  exact (hc.derivWithin (uniqueDiffOn_Icc hab u hu)).symm.trans
    (hd.derivWithin (uniqueDiffOn_Icc hab u hu))

private theorem pdV_eq_of_rectangle_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b c d u v : ℝ} {f : ℝ → ℝ → E} {z : E}
    (hcd : c < d) (hf : ContDiffOn ℝ 1 (Function.uncurry f) (Icc a b ×ˢ Icc c d))
    (hu : u ∈ Icc a b) (hv : v ∈ Icc c d)
    (hd : HasDerivWithinAt (f u) z (Icc c d) v) :
    pdV (Icc a b ×ˢ Icc c d) f u v = z := by
  have hc := hasDerivWithinAt_pdV hf ⟨hu, hv⟩ (fun x hx => ⟨hu, hx⟩)
  exact (hc.derivWithin (uniqueDiffOn_Icc hcd v hv)).symm.trans
    (hd.derivWithin (uniqueDiffOn_Icc hcd v hv))

/-- A jointly C¹ finite Goursat state with the literal reduced sources
realizes a full C¹ strip solution. The geometric hypotheses are precisely
positive radius, expansion and mass-gap numerator, and negative incoming
expansion. Only the outgoing old lower data are needed for the missing
constraints; no lower incoming-block matching or defect transport is assumed.
There are no source-box, small-time, or estimate-constant hypotheses. -/
theorem isC1Solution_rectangle_fields_of_goursat
    {a b c d e : ℝ} {F : ℝ × ℝ → RectangleState}
    {old : Fields} {D : Set (ℝ × ℝ)} {yi : ℝ → RectangleIncoming}
    (hab : a < b) (hcd : c < d) (hbc : b < c)
    (hF : ContDiffOn ℝ 1 F (Icc a b ×ˢ Icc c d))
    (hregion : ∀ p ∈ Icc a b ×ˢ Icc c d, F p ∈ rectangle_state_region)
    (hnu : ∀ p ∈ Icc a b ×ˢ Icc c d, (F p).2.2.1 < 0)
    (hold : IsC1Solution e old D)
    (hside : MapsTo (fun u => (u, c)) (Icc a b) D)
    (hYi : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).1 = yi v + ∫ s in a..u, rectangle_in_source e (F (s, v)))
    (hXb : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (F (u, v)).2 = (rectangle_state old (u, c)).2 +
        ∫ t in c..v, rectangle_out_source e (F (u, t))) :
    IsC1Solution e (rectangle_fields F) (Icc a b ×ˢ Icc c d) := by
  let R := Icc a b ×ˢ Icc c d
  let S := rectangle_fields F
  have cr : ContDiffOn ℝ 1 (Function.uncurry S.r) R := hF.snd.fst
  have cl : ContDiffOn ℝ 1 (Function.uncurry S.lam) R := hF.fst.fst
  have cn : ContDiffOn ℝ 1 (Function.uncurry S.nu) R := hF.snd.snd.fst
  have cm : ContDiffOn ℝ 1 (Function.uncurry S.m) R := hF.snd.snd.snd.fst
  have cQ : ContDiffOn ℝ 1 (Function.uncurry S.Q) R := hF.snd.snd.snd.snd.fst
  have cA : ContDiffOn ℝ 1 (Function.uncurry S.A) R := hF.snd.snd.snd.snd.snd.fst
  have cp : ContDiffOn ℝ 1 (Function.uncurry S.phi) R := hF.snd.snd.snd.snd.snd.snd.fst
  have ct : ContDiffOn ℝ 1 (Function.uncurry S.theta) R := hF.fst.snd
  have cx : ContDiffOn ℝ 1 (Function.uncurry S.xi) R := hF.snd.snd.snd.snd.snd.snd.snd
  have hi : ContinuousOn (rectangle_in_source e) (F '' R) := by
    rintro z ⟨p, hp, rfl⟩
    exact (contDiffAt_rectangle_in_source e (hregion p hp)).continuousAt.continuousWithinAt
  have ho : ContinuousOn (rectangle_out_source e) (F '' R) := by
    rintro z ⟨p, hp, rfl⟩
    exact (contDiffAt_rectangle_out_source e (hregion p hp)).continuousAt.continuousWithinAt
  have hd (p : ℝ × ℝ) (hp : p ∈ R) :=
    goursat_characteristic_hasDerivWithinAt hF.continuousOn hi ho hYi hXb hp.1 hp.2
  have hlu : ∀ p ∈ R, pdU R S.lam p.1 p.2 = S.rUV p.1 p.2 := by
    intro p hp
    exact pdU_eq_of_rectangle_deriv hab cl hp.1 hp.2 (hd p hp).1.fst
  have htu : ∀ p ∈ R, pdU R S.theta p.1 p.2 = S.thetaU e p.1 p.2 := by
    intro p hp
    exact pdU_eq_of_rectangle_deriv hab ct hp.1 hp.2 (hd p hp).1.snd
  have hev : ∀ p ∈ R,
      pdV R S.r p.1 p.2 = S.lam p.1 p.2 ∧
      pdV R S.nu p.1 p.2 = S.rUV p.1 p.2 ∧
      pdV R S.m p.1 p.2 = S.mV p.1 p.2 ∧
      pdV R S.Q p.1 p.2 = S.QV e p.1 p.2 ∧
      pdV R S.A p.1 p.2 = S.AV p.1 p.2 ∧
      pdV R S.phi p.1 p.2 = S.phiV p.1 p.2 ∧
      pdV R S.xi p.1 p.2 = S.xiV e p.1 p.2 := by
    intro p hp
    have hx := (hd p hp).2
    exact ⟨pdV_eq_of_rectangle_deriv hcd cr hp.1 hp.2 hx.fst,
      pdV_eq_of_rectangle_deriv hcd cn hp.1 hp.2 hx.snd.fst,
      pdV_eq_of_rectangle_deriv hcd cm hp.1 hp.2 hx.snd.snd.fst,
      pdV_eq_of_rectangle_deriv hcd cQ hp.1 hp.2 hx.snd.snd.snd.fst,
      pdV_eq_of_rectangle_deriv hcd cA hp.1 hp.2 hx.snd.snd.snd.snd.fst,
      pdV_eq_of_rectangle_deriv hcd cp hp.1 hp.2 hx.snd.snd.snd.snd.snd.fst,
      pdV_eq_of_rectangle_deriv hcd cx hp.1 hp.2 hx.snd.snd.snd.snd.snd.snd⟩
  have hmatch (u : ℝ) (hu : u ∈ Icc a b) :
      (F (u, c)).2 = (rectangle_state old (u, c)).2 := by
    simpa using hXb u hu c ⟨le_rfl, hcd.le⟩
  let T : Fields := { S with lam := old.lam, theta := old.theta }
  have heq : T.EqOn old {p | p.1 ∈ Icc a b ∧ p.2 = c} := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    dsimp only at hv
    subst v
    apply (rectangle_state_eq_iff T old (u, c)).mp
    change ((old.lam u c, old.theta u c), (F (u, c)).2) = rectangle_state old (u, c)
    exact Prod.ext rfl (hmatch u hu)
  have hbaseT := rectangle_lower_constraints_of_old hab hcd hbc hold hside heq cr cp cQ cm
  have hbase : ∀ u ∈ Icc a b,
      pdU R S.r u c = S.nu u c ∧ pdU R S.phi u c = S.phiU e u c ∧
      pdU R S.Q u c = S.QU e u c ∧ pdU R S.m u c = S.mU u c := by
    simpa only [T, Fields.phiU, Fields.QU, Fields.mU, Fields.mu] using! hbaseT
  have hg : ∀ p ∈ R, 0 < 1 - S.mu p.1 p.2 := by
    intro p hp
    have hr := (hregion p hp).1
    change 0 < 1 - 2 * (F p).2.2.2.1 / (F p).2.1
    have he : 1 - 2 * (F p).2.2.2.1 / (F p).2.1 =
        ((F p).2.1 - 2 * (F p).2.2.2.1) / (F p).2.1 := by
      field_simp [hr.ne']
    rw [he]
    exact div_pos (hregion p hp).2.2 hr
  exact isC1Solution_rectangle_of_goursat hab hcd hbc cr cl cn cm cQ cp cA ct cx
    (fun p hp => (hregion p hp).1) (fun p hp => (hregion p hp).2.1) hnu hg
    hev hlu htu hbase

end EmcsfAcExtension.Local
