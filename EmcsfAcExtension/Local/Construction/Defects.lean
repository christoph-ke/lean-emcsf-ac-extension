module

public import EmcsfAcExtension.Local.Defs.Recon
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # Zero-data closure of the incoming constraint defects

The analytic last step of `charged_SF_new_version.tex:L6192–6198`, following the approved
internal project record defect-transport section. Differential equations are used only off
the axis. Continuity supplies their zero axis traces; no value of a singular
right side at the axis is needed.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local.Null

private theorem eq_zero_of_hasDerivAt_zero {f : ℝ → ℝ} {a b : ℝ}
    (_hab : a ≤ b) (hc : ContinuousOn f (Icc a b)) (ha : f a = 0)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) : ∀ x ∈ Icc a b, f x = 0 := by
  intro x hx
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    (hc.mono (Icc_subset_Icc le_rfl hx.2))
    (fun y hy => hd y ⟨hy.1, hy.2.trans_le hx.2⟩)
    (intervalIntegrable_const (c := (0 : ℝ)))
  simpa only [intervalIntegral.integral_zero, ha, sub_zero] using h.symm

/-- A continuous real solution of a homogeneous scalar ODE with continuous
coefficient and zero left trace vanishes on the closed interval. Derivatives
are required only in the interior, so the conclusion includes the axis and
the upper endpoint without prescribing exterior jets. There are no constants. -/
theorem eq_zero_of_homogeneous_transport {f k : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (cf : ContinuousOn f (Icc a b)) (ck : ContinuousOn k (Icc a b))
    (ha : f a = 0) (hd : ∀ x ∈ Ioo a b, HasDerivAt f (k x * f x) x) :
    ∀ x ∈ Icc a b, f x = 0 := by
  let p (x : ℝ) := ∫ s in a..x, k s
  let w (x : ℝ) := Real.exp (-p x)
  have cp : ContinuousOn p (Icc a b) :=
    Recon.continuousOn_primitive hab (ck.intervalIntegrable_of_Icc hab)
  have cw : ContinuousOn w (Icc a b) := Real.continuous_exp.comp_continuousOn cp.neg
  have hw : ∀ x ∈ Ioo a b, HasDerivAt w (w x * -k x) x := by
    intro x hx
    exact ((Recon.hasDerivWithinAt_primitive ck ⟨hx.1.le, hx.2.le⟩).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)).neg.exp
  have hz : ∀ x ∈ Ioo a b, HasDerivAt (fun y => w y * f y) 0 x := by
    intro x hx
    convert (hw x hx).mul (hd x hx) using 1
    ring
  have hzero := eq_zero_of_hasDerivAt_zero hab (cw.mul cf) (by simp [ha]) hz
  intro x hx
  exact (mul_eq_zero.mp (hzero x hx)).resolve_left (Real.exp_ne_zero _)

/-- Zero-data uniqueness for a real scalar coefficient acting on any
complete real normed space. This includes the complex scalar transport
used to recover the incoming field's C¹ primitive. -/
theorem eq_zero_of_homogeneous_transport_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {k : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (cf : ContinuousOn f (Icc a b)) (ck : ContinuousOn k (Icc a b))
    (ha : f a = 0) (hd : ∀ x ∈ Ioo a b, HasDerivAt f (k x • f x) x) :
    ∀ x ∈ Icc a b, f x = 0 := by
  let p (x : ℝ) := ∫ s in a..x, k s
  let w (x : ℝ) := Real.exp (-p x)
  have cp : ContinuousOn p (Icc a b) :=
    Recon.continuousOn_primitive hab (ck.intervalIntegrable_of_Icc hab)
  have cw : ContinuousOn w (Icc a b) := Real.continuous_exp.comp_continuousOn cp.neg
  have hw (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt w (w x * -k x) x :=
    ((Recon.hasDerivWithinAt_primitive ck ⟨hx.1.le, hx.2.le⟩).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)).neg.exp
  have hz (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt (fun y => w y • f y) 0 x := by
    convert (hw x hx).smul (hd x hx) using 1
    rw [smul_smul, ← add_smul, show w x * k x + w x * -k x = 0 by ring, zero_smul]
  intro x hx
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    ((cw.smul cf).mono (Icc_subset_Icc le_rfl hx.2))
    (fun y hy => hz y ⟨hy.1, hy.2.trans_le hx.2⟩)
    (intervalIntegrable_const (c := (0 : E)))
  have hzero : w x • f x = 0 := by
    rw [intervalIntegral.integral_zero] at hi
    change (0 : E) = w x • f x - w a • f a at hi
    simpa only [ha, smul_zero, sub_zero] using hi.symm
  exact (smul_eq_zero.mp hzero).resolve_left (Real.exp_ne_zero _)

/-- [node restart-sec-independent-null-construction#incoming-constraint-closure]
Analytic core of the incoming-constraint closure (`charged_SF_new_version.tex:L6192–6198`).
The triangular defect system, with continuous coefficients and zero axis
traces, forces both defects to vanish on the entire outgoing prefix. No sign
condition on either coefficient is needed and there are no estimate constants.
The hypotheses are the conclusions of defect transport and axis evaluation. -/
theorem incoming_constraint_closure_of_transport {Z E k q : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (cZ : ContinuousOn Z (Icc a b)) (cE : ContinuousOn E (Icc a b))
    (ck : ContinuousOn k (Icc a b)) (hZ : Z a = 0) (hE : E a = 0)
    (dZ : ∀ x ∈ Ioo a b, HasDerivAt Z 0 x)
    (dE : ∀ x ∈ Ioo a b, HasDerivAt E (k x * E x + q x * Z x) x) :
    ∀ x ∈ Icc a b, Z x = 0 ∧ E x = 0 := by
  have hz := eq_zero_of_hasDerivAt_zero hab cZ hZ dZ
  have he := eq_zero_of_homogeneous_transport hab cE ck hE (fun x hx => by
    simpa only [hz x ⟨hx.1.le, hx.2.le⟩, mul_zero, add_zero] using dE x hx)
  exact fun x hx => ⟨hz x hx, he x hx⟩

/-- Recover the frozen incoming Maxwell and mass equations from zero defects.
This is an algebraic unpacking of the approved internal defect definitions;
no differentiability or additional equation is assumed. -/
theorem incoming_constraints_iff_defects_zero (e : ℝ) (D : Set (ℝ × ℝ))
    (S : Fields) (u v : ℝ) :
    (defectQ e D S u v = 0 ∧ defectM D S u v = 0) ↔
      (pdU D S.Q u v = S.QU e u v ∧ pdU D S.m u v = S.mU u v) := by
  simp only [defectQ, defectM, sub_eq_zero]

/-- [node restart-sec-independent-null-construction#incoming-constraint-closure]
Recover the frozen incoming Maxwell and mass equations on a closed triangle
from the actual defect transports and zero continuous axis values. The
coefficient is exactly `-‖θ‖²/(λr)`, with no factor of `1-μ`.
The conclusion includes the upper outgoing edge and the axis. There are
no estimate constants and neither incoming equation is a hypothesis. -/
theorem incoming_constraints_of_defect_transport {a b e : ℝ} {S : Fields}
    (cZ : ContinuousOn (Function.uncurry (defectQ e (triangle a b) S)) (triangle a b))
    (cE : ContinuousOn (Function.uncurry (defectM (triangle a b) S)) (triangle a b))
    (ck : ∀ u ∈ Icc a b, ContinuousOn
      (fun v => -(‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v))) (Icc u b))
    (haxis : ∀ t ∈ Icc a b,
      defectQ e (triangle a b) S t t = 0 ∧ defectM (triangle a b) S t t = 0)
    (htransport : ∀ u ∈ Icc a b, ∀ v ∈ Ioo u b,
      HasDerivAt (defectQ e (triangle a b) S u) 0 v ∧
      HasDerivAt (defectM (triangle a b) S u)
        (-(‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)) * defectM (triangle a b) S u v +
          (S.lam u v * S.Q u v / S.r u v ^ 2) * defectQ e (triangle a b) S u v) v) :
    ∀ p ∈ triangle a b,
      pdU (triangle a b) S.Q p.1 p.2 = S.QU e p.1 p.2 ∧
        pdU (triangle a b) S.m p.1 p.2 = S.mU p.1 p.2 := by
  intro p hp
  have hu : p.1 ∈ Icc a b := ⟨hp.1, hp.2.1.trans hp.2.2⟩
  have hs : MapsTo (fun v => (p.1, v)) (Icc p.1 b) (triangle a b) :=
    fun v hv => ⟨hp.1, hv.1, hv.2⟩
  have hz := incoming_constraint_closure_of_transport hu.2
    (cZ.comp (continuousOn_const.prodMk continuousOn_id) hs)
    (cE.comp (continuousOn_const.prodMk continuousOn_id) hs) (ck p.1 hu)
    (haxis p.1 hu).1 (haxis p.1 hu).2
    (fun v hv => (htransport p.1 hu v hv).1)
    (fun v hv => (htransport p.1 hu v hv).2) p.2 ⟨hp.2.1, hp.2.2⟩
  exact (incoming_constraints_iff_defects_zero e (triangle a b) S p.1 p.2).mp hz

/-- [node restart-sec-independent-null-construction#incoming-constraint-closure]
The triangular zero-axis defect system recovers the actual incoming charge
and mass equations on the full construction wedge. Differential transport
is required only off axis; continuity includes the top outgoing edge and
any collapsed section. There are no estimate constants. -/
theorem incoming_constraints_on_wedge_of_defect_transport {a b c e : ℝ} {S : Fields}
    (cZ : ContinuousOn (Function.uncurry
      (defectQ e (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cE : ContinuousOn (Function.uncurry
      (defectM (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ck : ∀ u ∈ Icc a c, ContinuousOn
      (fun v => -(‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v))) (Icc u b))
    (haxis : ∀ t ∈ Icc a c,
      defectQ e (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S t t = 0 ∧
        defectM (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S t t = 0)
    (htransport : ∀ u ∈ Icc a c, ∀ v ∈ Ioo u b,
      HasDerivAt (defectQ e (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S u) 0 v ∧
      HasDerivAt (defectM (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S u)
        (-(‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)) *
            defectM (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S u v +
          (S.lam u v * S.Q u v / S.r u v ^ 2) *
            defectQ e (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S u v) v) :
    ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.Q p.1 p.2 = S.QU e p.1 p.2 ∧
        pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) S.m p.1 p.2 = S.mU p.1 p.2 := by
  intro p hp
  have hu : p.1 ∈ Icc a c := ⟨hp.1.1, hp.2⟩
  have hs : MapsTo (fun v => (p.1, v)) (Icc p.1 b)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :=
    fun v hv => ⟨⟨hp.1.1, hv.1, hv.2⟩, hp.2⟩
  have hz := incoming_constraint_closure_of_transport (hp.1.2.1.trans hp.1.2.2)
    (cZ.comp (continuousOn_const.prodMk continuousOn_id) hs)
    (cE.comp (continuousOn_const.prodMk continuousOn_id) hs) (ck p.1 hu)
    (haxis p.1 hu).1 (haxis p.1 hu).2
    (fun v hv => (htransport p.1 hu v hv).1)
    (fun v hv => (htransport p.1 hu v hv).2) p.2 ⟨hp.1.2.1, hp.1.2.2⟩
  exact (incoming_constraints_iff_defects_zero e _ S p.1 p.2).mp hz


end EmcsfAcExtension.Local.Null
