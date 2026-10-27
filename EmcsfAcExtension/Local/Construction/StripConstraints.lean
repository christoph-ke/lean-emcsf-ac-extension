module

public import EmcsfAcExtension.Local.Defs.C1Class
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.Calculus.MixedWithin
import EmcsfAcExtension.Local.Construction.Defects

/-! # Constraint recovery on positive-radius characteristic rectangles

The C¹ primitive calculus behind internal project record, L1066–1074, and
internal project record's positive-radius-strip construction. Mixed derivatives below
are derived from outgoing primitives; no second field derivative is assumed.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- Matching C¹ traces on a nondegenerate horizontal interval have the
same incoming domain partial, even when the two ambient domains lie on
opposite sides of that interval. This transfers the old lower-side
constraints to the appended rectangle using trace data alone. -/
theorem pdU_eq_of_eqOn_horizontal_trace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D D' : Set (ℝ × ℝ)} {f g : ℝ → ℝ → E} {a b u v : ℝ}
    (hab : a < b) (hu : u ∈ Icc a b)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) D')
    (hs : MapsTo (fun x => (x, v)) (Icc a b) D)
    (hs' : MapsTo (fun x => (x, v)) (Icc a b) D')
    (heq : ∀ x ∈ Icc a b, f x v = g x v) :
    pdU D f u v = pdU D' g u v := by
  have hd := hasDerivWithinAt_pdU hf (hs hu) hs
  have hd' := hasDerivWithinAt_pdU hg (hs' hu) hs'
  have he := (hd'.congr heq (heq u hu)).derivWithin (uniqueDiffOn_Icc hab u hu)
  exact ((hd.derivWithin (uniqueDiffOn_Icc hab u hu)).symm).trans he

/-- Transfer the four missing lower-side constraints from an old full C¹
solution by matching the actual primary traces. Incoming derivatives are
tangential to the common side, so no old transverse jet is required. -/
theorem rectangle_lower_constraints_of_old
    {a b c d e : ℝ} {S F : Fields} {D : Set (ℝ × ℝ)}
    (hab : a < b) (hcd : c < d) (hbc : b < c)
    (hF : IsC1Solution e F D)
    (hside : MapsTo (fun u => (u, c)) (Icc a b) D)
    (heq : S.EqOn F {p | p.1 ∈ Icc a b ∧ p.2 = c})
    (cr : ContDiffOn ℝ 1 (Function.uncurry S.r) (Icc a b ×ˢ Icc c d))
    (cp : ContDiffOn ℝ 1 (Function.uncurry S.phi) (Icc a b ×ˢ Icc c d))
    (cQ : ContDiffOn ℝ 1 (Function.uncurry S.Q) (Icc a b ×ˢ Icc c d))
    (cm : ContDiffOn ℝ 1 (Function.uncurry S.m) (Icc a b ×ˢ Icc c d)) :
    ∀ u ∈ Icc a b,
      pdU (Icc a b ×ˢ Icc c d) S.r u c = S.nu u c ∧
      pdU (Icc a b ×ˢ Icc c d) S.phi u c = S.phiU e u c ∧
      pdU (Icc a b ×ˢ Icc c d) S.Q u c = S.QU e u c ∧
      pdU (Icc a b ×ˢ Icc c d) S.m u c = S.mU u c := by
  have hs : MapsTo (fun u => (u, c)) (Icc a b) (Icc a b ×ˢ Icc c d) :=
    fun _ hu => ⟨hu, le_rfl, hcd.le⟩
  have he (u : ℝ) (hu : u ∈ Icc a b) := heq (u, c) ⟨hu, rfl⟩
  intro u hu
  have hEq := he u hu
  have hr := pdU_eq_of_eqOn_horizontal_trace hab hu cr hF.c1_r hs hside
    (fun u hu => (he u hu).1)
  have hp := pdU_eq_of_eqOn_horizontal_trace hab hu cp hF.c1_phi hs hside
    (fun u hu => (he u hu).2.2.2.2.2.1)
  have hQ := pdU_eq_of_eqOn_horizontal_trace hab hu cQ hF.c1_Q hs hside
    (fun u hu => (he u hu).2.2.2.2.1)
  have hm := pdU_eq_of_eqOn_horizontal_trace hab hu cm hF.c1_m hs hside
    (fun u hu => (he u hu).2.2.2.1)
  have hsourceP : S.phiU e u c = F.phiU e u c := by
    simp only [Fields.phiU, hEq.1, hEq.2.2.2.2.2.2.2.2,
      hEq.2.2.2.2.2.2.1, hEq.2.2.2.2.2.1]
  have hsourceQ : S.QU e u c = F.QU e u c := by
    simp only [Fields.QU, hEq.1, hEq.2.2.2.2.2.1, hEq.2.2.2.2.2.2.2.2]
  have hsourceM : S.mU u c = F.mU u c := by
    simp only [Fields.mU, Fields.mu, hEq.1, hEq.2.2.2.1, hEq.2.2.2.2.1,
      hEq.2.2.1, hEq.2.2.2.2.2.2.2.2]
  have hf := hF.eq_u (u, c) (hside hu) (hu.2.trans_lt hbc)
  exact ⟨hr.trans (hf.1.trans hEq.2.2.1.symm),
    hp.trans (hf.2.2.2.2.1.trans hsourceP.symm),
    hQ.trans (hf.2.2.2.1.trans hsourceQ.symm),
    hm.trans (hf.2.2.1.trans hsourceM.symm)⟩

/-- Recover the outgoing derivative of the incoming first jet from an
outgoing equation on a closed nondegenerate rectangle. Only C¹ regularity
of the field and its outgoing source is required; the conclusion includes
both incoming sides and both outgoing endpoints. There are no constants. -/
theorem hasDerivWithinAt_pdU_of_pdV_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b c d u v : ℝ} {f g : ℝ → ℝ → E}
    (hab : a < b) (hcd : c < d)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (Icc a b ×ˢ Icc c d))
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) (Icc a b ×ˢ Icc c d))
    (heq : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) f p.1 p.2 = g p.1 p.2)
    (hu : u ∈ Icc a b) (hv : v ∈ Icc c d) :
    HasDerivWithinAt (pdU (Icc a b ×ˢ Icc c d) f u)
      (pdU (Icc a b ×ˢ Icc c d) g u v) (Icc c d) v := by
  let D := Icc a b ×ˢ Icc c d
  have hD : UniqueDiffOn ℝ D := (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc hcd)
  have hrep : ∀ y ∈ Icc a b, ∀ x ∈ Icc c d,
      f y x = f y c + ∫ t in c..x, g y t := by
    intro y hy x hx
    have hseg : MapsTo (fun t => (y, t)) (Icc c x) D :=
      fun t ht => ⟨hy, ht.1, ht.2.trans hx.2⟩
    have hi := integralForm_pdV hf hD hx.1 hseg
    have he : ∫ t in c..x, pdV D f y t = ∫ t in c..x, g y t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact heq (y, t) (hseg (by simpa only [uIcc_of_le hx.1] using ht))
    have hi' := hi.2
    rw [he] at hi'
    exact (eq_add_of_sub_eq hi').trans (add_comm _ _)
  have hB := hasDerivWithinAt_pdU hf (show (u, c) ∈ D from ⟨hu, le_rfl, hcd.le⟩)
    (show MapsTo (fun y => (y, c)) (Icc a b) D from
      fun y hy => ⟨hy, le_rfl, hcd.le⟩)
  have hm := (hasDerivWithinAt_mixed_integral_primitive_rectangle hcd hab
    hg.continuousOn (continuousOn_pdU hg hD)
    (fun y hy t ht => hasDerivWithinAt_pdU hg ⟨hy, ht⟩
      (fun z hz => ⟨hz, ht⟩)) hv hu hB).1
  have hj (x : ℝ) (hx : x ∈ Icc c d) :
      derivWithin (fun y => f y c + ∫ t in c..x, g y t) (Icc a b) u =
        pdU D f u x := by
    have hd := hasDerivWithinAt_pdU hf (show (u, x) ∈ D from ⟨hu, hx⟩)
      (show MapsTo (fun y => (y, x)) (Icc a b) D from fun y hy => ⟨hy, hx⟩)
    exact (hd.congr (fun y hy => (hrep y hy x hx).symm)
      (hrep u hu x hx).symm).derivWithin (uniqueDiffOn_Icc hab u hu)
  exact hm.congr (fun x hx => (hj x hx).symm) (hj v hv).symm

/-- Recover the missing incoming radius equation on a C¹ characteristic
rectangle from the outgoing radius equation, equal expansion transports,
and its zero lower-side defect. This is the first constraint step in
internal project record L1070–1074. No C² field or defect transport is assumed. -/
theorem rectangle_radius_constraint
    {a b c d : ℝ} {r lam nu : ℝ → ℝ → ℝ}
    (hab : a < b) (hcd : c < d)
    (cr : ContDiffOn ℝ 1 (Function.uncurry r) (Icc a b ×ˢ Icc c d))
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam) (Icc a b ×ˢ Icc c d))
    (cn : ContDiffOn ℝ 1 (Function.uncurry nu) (Icc a b ×ˢ Icc c d))
    (hrv : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) r p.1 p.2 = lam p.1 p.2)
    (hln : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) lam p.1 p.2 =
        pdV (Icc a b ×ˢ Icc c d) nu p.1 p.2)
    (hbase : ∀ u ∈ Icc a b, pdU (Icc a b ×ˢ Icc c d) r u c = nu u c) :
    ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) r p.1 p.2 = nu p.1 p.2 := by
  let D := Icc a b ×ˢ Icc c d
  have hD : UniqueDiffOn ℝ D := (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc hcd)
  intro p hp
  have hs : MapsTo (fun v => (p.1, v)) (Icc c d) D := fun _ hv => ⟨hp.1, hv⟩
  have hc : ContinuousOn (fun v => pdU D r p.1 v - nu p.1 v) (Icc c d) :=
    ((continuousOn_pdU cr hD).sub cn.continuousOn).comp
      (continuousOn_const.prodMk continuousOn_id) hs
  have hz := Null.eq_zero_of_homogeneous_transport hcd.le hc
    (continuousOn_const (c := (0 : ℝ))) (sub_eq_zero.mpr (hbase p.1 hp.1))
    (fun v hv => by
      have hd := (hasDerivWithinAt_pdU_of_pdV_eq hab hcd cr cl hrv hp.1
        ⟨hv.1.le, hv.2.le⟩).sub
        (hasDerivWithinAt_pdV cn (hs ⟨hv.1.le, hv.2.le⟩) hs)
      rw [hln (p.1, v) (hs ⟨hv.1.le, hv.2.le⟩), sub_self] at hd
      simpa only [zero_mul, Pi.sub_apply] using!
        hd.hasDerivAt (Icc_mem_nhds hv.1 hv.2)) p.2 hp.2
  exact sub_eq_zero.mp hz

private theorem eq_zero_of_deriv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {a b : ℝ} (hc : ContinuousOn f (Icc a b)) (ha : f a = 0)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) : ∀ x ∈ Icc a b, f x = 0 := by
  intro x hx
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    (hc.mono (Icc_subset_Icc le_rfl hx.2))
    (fun y hy => hd y ⟨hy.1, hy.2.trans_le hx.2⟩)
    (intervalIntegrable_const (c := (0 : E)))
  simpa only [intervalIntegral.integral_zero, ha, sub_zero] using h.symm

private theorem scalar_sources_cross (e : ℝ) (S : Fields) (u v : ℝ)
    (hr : S.r u v ≠ 0) (hgap : 1 - S.mu u v ≠ 0) :
    (S.thetaU e u v * (S.r u v : ℂ) - S.theta u v * S.nu u v) /
        (S.r u v : ℂ) ^ 2 -
      ((S.xiV e u v * (S.r u v : ℂ) - S.xi u v * S.lam u v) /
        (S.r u v : ℂ) ^ 2 -
        (Complex.I * e * (S.AV u v : ℂ) * S.phi u v +
          Complex.I * e * S.A u v * S.phiV u v)) = 0 := by
  have hrC : (S.r u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hgC : ((1 - S.mu u v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hgap
  dsimp only [Fields.thetaU, Fields.xiV, Fields.phiV, Fields.waveSource, Fields.AV]
  push_cast
  push_cast at hgC
  field_simp [hrC, hgC]
  ring

/-- Recover the missing incoming scalar equation on a positive-radius C¹
rectangle. The mixed derivative of `φ` is recovered from its outgoing
primitive. After the radius constraint, the derivative of
`φ_u-ξ/r+ieAφ` vanishes by the three charged-source cancellations in
internal project record L1071–1074. No scalar-defect transport or C² field is assumed. -/
theorem rectangle_scalar_constraint
    {a b c d e : ℝ} {S : Fields}
    (hab : a < b) (hcd : c < d)
    (cr : ContDiffOn ℝ 1 (Function.uncurry S.r) (Icc a b ×ˢ Icc c d))
    (cp : ContDiffOn ℝ 1 (Function.uncurry S.phi) (Icc a b ×ˢ Icc c d))
    (ct : ContDiffOn ℝ 1 (Function.uncurry S.theta) (Icc a b ×ˢ Icc c d))
    (cx : ContDiffOn ℝ 1 (Function.uncurry S.xi) (Icc a b ×ˢ Icc c d))
    (cA : ContDiffOn ℝ 1 (Function.uncurry S.A) (Icc a b ×ˢ Icc c d))
    (hr : ∀ p ∈ Icc a b ×ˢ Icc c d, S.r p.1 p.2 ≠ 0)
    (hgap : ∀ p ∈ Icc a b ×ˢ Icc c d, 1 - S.mu p.1 p.2 ≠ 0)
    (hru : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) S.r p.1 p.2 = S.nu p.1 p.2)
    (hrv : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) S.r p.1 p.2 = S.lam p.1 p.2)
    (hpv : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) S.phi p.1 p.2 = S.phiV p.1 p.2)
    (htu : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) S.theta p.1 p.2 = S.thetaU e p.1 p.2)
    (hxv : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) S.xi p.1 p.2 = S.xiV e p.1 p.2)
    (hAv : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) S.A p.1 p.2 = S.AV p.1 p.2)
    (hbase : ∀ u ∈ Icc a b,
      pdU (Icc a b ×ˢ Icc c d) S.phi u c = S.phiU e u c) :
    ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) S.phi p.1 p.2 = S.phiU e p.1 p.2 := by
  let D := Icc a b ×ˢ Icc c d
  have hD : UniqueDiffOn ℝ D := (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc hcd)
  have crC := Complex.ofRealCLM.contDiff.comp_contDiffOn cr
  have cAC := Complex.ofRealCLM.contDiff.comp_contDiffOn cA
  have hrC : ∀ p ∈ D, (S.r p.1 p.2 : ℂ) ≠ 0 :=
    fun p hp => Complex.ofReal_ne_zero.mpr (hr p hp)
  have cV : ContDiffOn ℝ 1 (Function.uncurry S.phiV) D := by
    simpa only [Fields.phiV, Function.uncurry, div_eq_mul_inv] using!
      ct.mul (crC.inv hrC)
  have cU : ContDiffOn ℝ 1 (Function.uncurry (S.phiU e)) D := by
    simpa only [Fields.phiU, Function.uncurry, div_eq_mul_inv] using!
      (cx.mul (crC.inv hrC)).sub ((((contDiffOn_const (c := (Complex.I * e : ℂ))).mul cAC).mul cp))
  have hdV : ∀ p ∈ D, pdU D S.phiV p.1 p.2 =
      (S.thetaU e p.1 p.2 * (S.r p.1 p.2 : ℂ) - S.theta p.1 p.2 * S.nu p.1 p.2) /
        (S.r p.1 p.2 : ℂ) ^ 2 := by
    intro p hp
    have hs : MapsTo (fun x => (x, p.2)) (Icc a b) D := fun _ hx => ⟨hx, hp.2⟩
    have hθ := hasDerivWithinAt_pdU ct hp hs
    have hρ := (hasDerivWithinAt_pdU cr hp hs).ofReal_comp
    rw [htu p hp] at hθ
    rw [hru p hp] at hρ
    have hquot := (hθ.div hρ (hrC p hp)).derivWithin (uniqueDiffOn_Icc hab p.1 hp.1)
    have hex := (hasDerivWithinAt_pdU cV hp hs).derivWithin
      (uniqueDiffOn_Icc hab p.1 hp.1)
    exact hex.symm.trans hquot
  intro p hp
  have hs : MapsTo (fun v => (p.1, v)) (Icc c d) D := fun _ hv => ⟨hp.1, hv⟩
  have hc : ContinuousOn (fun v => pdU D S.phi p.1 v - S.phiU e p.1 v) (Icc c d) :=
    ((continuousOn_pdU cp hD).sub cU.continuousOn).comp
      (continuousOn_const.prodMk continuousOn_id) hs
  have hz := eq_zero_of_deriv_zero hc (sub_eq_zero.mpr (hbase p.1 hp.1))
    (fun v hv => by
      have hpv' := hs ⟨hv.1.le, hv.2.le⟩
      have hρ := (hasDerivWithinAt_pdV cr hpv' hs).ofReal_comp
      have hφ := hasDerivWithinAt_pdV cp hpv' hs
      have hξ := hasDerivWithinAt_pdV cx hpv' hs
      have hA := (hasDerivWithinAt_pdV cA hpv' hs).ofReal_comp
      rw [hrv (p.1, v) hpv'] at hρ
      rw [hpv (p.1, v) hpv'] at hφ
      rw [hxv (p.1, v) hpv'] at hξ
      rw [hAv (p.1, v) hpv'] at hA
      have hU := (hξ.div hρ (hrC (p.1, v) hpv')).sub
        ((hA.const_mul (Complex.I * e)).mul hφ)
      have hmix := hasDerivWithinAt_pdU_of_pdV_eq hab hcd cp cV hpv hp.1
        ⟨hv.1.le, hv.2.le⟩
      rw [hdV (p.1, v) hpv'] at hmix
      have hd := hmix.sub hU
      rw [scalar_sources_cross e S p.1 v (hr (p.1, v) hpv')
        (hgap (p.1, v) hpv')] at hd
      exact hd.hasDerivAt (Icc_mem_nhds hv.1 hv.2)) p.2 hp.2
  exact sub_eq_zero.mp hz

private theorem charge_sources_cross (e : ℝ) (S : Fields) (u v : ℝ)
    (hr : S.r u v ≠ 0) (_hgap : 1 - S.mu u v ≠ 0) :
    -(e * S.nu u v * (starRingEnd ℂ (S.phi u v) * S.theta u v).im +
      e * S.r u v * (starRingEnd ℂ (S.phiU e u v) * S.theta u v +
        starRingEnd ℂ (S.phi u v) * S.thetaU e u v).im) -
    (e * S.lam u v * (starRingEnd ℂ (S.phi u v) * S.xi u v).im +
      e * S.r u v * (starRingEnd ℂ (S.phiV u v) * S.xi u v +
        starRingEnd ℂ (S.phi u v) * S.xiV e u v).im) = 0 := by
  simp only [Fields.phiU, Fields.phiV, Fields.thetaU, Fields.xiV,
    Fields.waveSource, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
  field_simp [hr, _hgap]
  ring

/-- Recover the incoming Maxwell constraint on a positive-radius C¹
rectangle from the full radius and scalar equations, the two wave equations,
and the outgoing Maxwell primitive. The actual charge-defect derivative
is computed from first jets and is zero. No defect transport is assumed. -/
theorem rectangle_charge_constraint
    {a b c d e : ℝ} {S : Fields}
    (hab : a < b) (hcd : c < d)
    (cr : ContDiffOn ℝ 1 (Function.uncurry S.r) (Icc a b ×ˢ Icc c d))
    (cp : ContDiffOn ℝ 1 (Function.uncurry S.phi) (Icc a b ×ˢ Icc c d))
    (ct : ContDiffOn ℝ 1 (Function.uncurry S.theta) (Icc a b ×ˢ Icc c d))
    (cx : ContDiffOn ℝ 1 (Function.uncurry S.xi) (Icc a b ×ˢ Icc c d))
    (cQ : ContDiffOn ℝ 1 (Function.uncurry S.Q) (Icc a b ×ˢ Icc c d))
    (hr : ∀ p ∈ Icc a b ×ˢ Icc c d, S.r p.1 p.2 ≠ 0)
    (hgap : ∀ p ∈ Icc a b ×ˢ Icc c d, 1 - S.mu p.1 p.2 ≠ 0)
    (hru : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) S.r p.1 p.2 = S.nu p.1 p.2)
    (hrv : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) S.r p.1 p.2 = S.lam p.1 p.2)
    (hpu : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) S.phi p.1 p.2 = S.phiU e p.1 p.2)
    (hpv : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) S.phi p.1 p.2 = S.phiV p.1 p.2)
    (htu : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) S.theta p.1 p.2 = S.thetaU e p.1 p.2)
    (hxv : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) S.xi p.1 p.2 = S.xiV e p.1 p.2)
    (hQv : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) S.Q p.1 p.2 = S.QV e p.1 p.2)
    (hbase : ∀ u ∈ Icc a b,
      pdU (Icc a b ×ˢ Icc c d) S.Q u c = S.QU e u c) :
    ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) S.Q p.1 p.2 = S.QU e p.1 p.2 := by
  let D := Icc a b ×ˢ Icc c d
  have hD : UniqueDiffOn ℝ D := (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc hcd)
  have cconj := Complex.conjCLE.contDiff.comp_contDiffOn cp
  have cV : ContDiffOn ℝ 1 (Function.uncurry (S.QV e)) D := by
    simpa only [Fields.QV, Function.uncurry] using!
      (((contDiffOn_const (c := e)).mul cr).mul (Complex.imCLM.contDiff.comp_contDiffOn (cconj.mul
          ct))).neg
  have cU : ContDiffOn ℝ 1 (Function.uncurry (S.QU e)) D := by
    simpa only [Fields.QU, Function.uncurry] using!
      ((contDiffOn_const (c := e)).mul cr).mul (Complex.imCLM.contDiff.comp_contDiffOn (cconj.mul
          cx))
  have hdV : ∀ p ∈ D, pdU D (S.QV e) p.1 p.2 =
      -(e * S.nu p.1 p.2 * (starRingEnd ℂ (S.phi p.1 p.2) * S.theta p.1 p.2).im +
        e * S.r p.1 p.2 * (starRingEnd ℂ (S.phiU e p.1 p.2) * S.theta p.1 p.2 +
          starRingEnd ℂ (S.phi p.1 p.2) * S.thetaU e p.1 p.2).im) := by
    intro p hp
    have hs : MapsTo (fun x => (x, p.2)) (Icc a b) D := fun _ hx => ⟨hx, hp.2⟩
    have hρ := hasDerivWithinAt_pdU cr hp hs
    have hφ := hasDerivWithinAt_pdU cp hp hs
    have hθ := hasDerivWithinAt_pdU ct hp hs
    rw [hru p hp] at hρ
    rw [hpu p hp] at hφ
    rw [htu p hp] at hθ
    have hconj := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt _ hφ
    have hcurrent := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt _ (hconj.mul hθ)
    have hd := ((hρ.const_mul e).mul hcurrent).neg
    have hj := hd.derivWithin (uniqueDiffOn_Icc hab p.1 hp.1)
    have hex := (hasDerivWithinAt_pdU cV hp hs).derivWithin
      (uniqueDiffOn_Icc hab p.1 hp.1)
    exact hex.symm.trans hj
  intro p hp
  have hs : MapsTo (fun v => (p.1, v)) (Icc c d) D := fun _ hv => ⟨hp.1, hv⟩
  have hc : ContinuousOn (fun v => pdU D S.Q p.1 v - S.QU e p.1 v) (Icc c d) :=
    ((continuousOn_pdU cQ hD).sub cU.continuousOn).comp
      (continuousOn_const.prodMk continuousOn_id) hs
  have hz := eq_zero_of_deriv_zero hc (sub_eq_zero.mpr (hbase p.1 hp.1))
    (fun v hv => by
      have hpv' := hs ⟨hv.1.le, hv.2.le⟩
      have hρ := hasDerivWithinAt_pdV cr hpv' hs
      have hφ := hasDerivWithinAt_pdV cp hpv' hs
      have hξ := hasDerivWithinAt_pdV cx hpv' hs
      rw [hrv (p.1, v) hpv'] at hρ
      rw [hpv (p.1, v) hpv'] at hφ
      rw [hxv (p.1, v) hpv'] at hξ
      have hconj := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt _ hφ
      have hcurrent := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt _ (hconj.mul hξ)
      have hU := (hρ.const_mul e).mul hcurrent
      have hmix := hasDerivWithinAt_pdU_of_pdV_eq hab hcd cQ cV hQv hp.1
        ⟨hv.1.le, hv.2.le⟩
      rw [hdV (p.1, v) hpv'] at hmix
      have hd := hmix.sub hU
      change HasDerivWithinAt (fun v => pdU D S.Q p.1 v - S.QU e p.1 v)
        (-(e * S.nu p.1 v * (starRingEnd ℂ (S.phi p.1 v) * S.theta p.1 v).im +
          e * S.r p.1 v * (starRingEnd ℂ (S.phiU e p.1 v) * S.theta p.1 v +
            starRingEnd ℂ (S.phi p.1 v) * S.thetaU e p.1 v).im) -
         (e * S.lam p.1 v * (starRingEnd ℂ (S.phi p.1 v) * S.xi p.1 v).im +
          e * S.r p.1 v * (starRingEnd ℂ (S.phiV p.1 v) * S.xi p.1 v +
            starRingEnd ℂ (S.phi p.1 v) * S.xiV e p.1 v).im)) (Icc c d) v at hd
      rw [charge_sources_cross e S p.1 v (hr (p.1, v) hpv')
        (hgap (p.1, v) hpv')] at hd
      exact hd.hasDerivAt (Icc_mem_nhds hv.1 hv.2)) p.2 hp.2
  exact sub_eq_zero.mp hz

end EmcsfAcExtension.Local
