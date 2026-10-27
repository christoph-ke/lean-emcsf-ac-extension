module

public import EmcsfAcExtension.Local.Defs.C1Class
import EmcsfAcExtension.Local.Construction.StripConstraints
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Construction.Defects

/-! # Incoming mass constraint on a positive-radius C¹ rectangle

internal project record L1073–1074: after radius, scalar and Maxwell recovery,
the actual mass defect obeys a homogeneous scalar transport. Only first
jets and mixed derivatives recovered from a primitive enter the calculation.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

private noncomputable def massJet (H T l Q r h t k q n : ℝ) : ℝ :=
  ((h * T + H * t) * (2 * l) - H * T * (2 * k)) / (2 * l) ^ 2 +
    (((2 * Q * q * l + Q ^ 2 * k) * (2 * r ^ 2) -
      Q ^ 2 * l * (2 * (2 * r * n))) / (2 * r ^ 2) ^ 2)

private noncomputable def gapJet (m r dm dr : ℝ) : ℝ :=
  -((2 * dm) * r - (2 * m) * dr) / r ^ 2

private theorem hasDerivWithinAt_mass_source
    {H T l Q r : ℝ → ℝ} {h t k q n x : ℝ} {s : Set ℝ}
    (hH : HasDerivWithinAt H h s x) (hT : HasDerivWithinAt T t s x)
    (hl : HasDerivWithinAt l k s x) (hQ : HasDerivWithinAt Q q s x)
    (hr : HasDerivWithinAt r n s x) (hl0 : l x ≠ 0) (hr0 : r x ≠ 0) :
    HasDerivWithinAt (fun y => H y * T y / (2 * l y) + Q y ^ 2 * l y / (2 * r y ^ 2))
      (massJet (H x) (T x) (l x) (Q x) (r x) h t k q n) s x := by
  have hd := ((hH.mul hT).div (hl.const_mul 2) (mul_ne_zero (by norm_num) hl0)).add
    (((hQ.pow 2).mul hl).div ((hr.pow 2).const_mul 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0)))
  convert hd using 1
  dsimp only [massJet]
  simp only [Pi.mul_apply, Pi.pow_apply]
  ring

private theorem hasDerivWithinAt_gap
    {m r : ℝ → ℝ} {dm dr x : ℝ} {s : Set ℝ}
    (hm : HasDerivWithinAt m dm s x) (hr : HasDerivWithinAt r dr s x) (hr0 : r x ≠ 0) :
    HasDerivWithinAt (fun y => 1 - 2 * m y / r y)
      (gapJet (m x) (r x) dm dr) s x := by
  simpa only [gapJet, zero_sub, neg_div] using! ((hm.const_mul 2).div hr hr0).const_sub 1

private theorem hasDerivWithinAt_complex_norm_square
    {f : ℝ → ℂ} {z : ℂ} {x : ℝ} {s : Set ℝ} (hf : HasDerivWithinAt f z s x) :
    HasDerivWithinAt (fun y => ‖f y‖ ^ 2)
      (2 * ((f x).re * z.re + (f x).im * z.im)) s x := by
  have hR := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt x hf
  have hI := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt x hf
  have hd := (hR.pow 2).add (hI.pow 2)
  convert hd using 1
  · ext y
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Pi.add_apply, Pi.pow_apply, Function.comp_apply,
      Complex.reCLM_apply, Complex.imCLM_apply]
    ring
  · simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply]
    ring

private theorem theta_norm_source (S : Fields) (e u v : ℝ)
    (hr : S.r u v ≠ 0) (hgap : 1 - S.mu u v ≠ 0) :
    2 * ((S.theta u v).re * (S.thetaU e u v).re +
      (S.theta u v).im * (S.thetaU e u v).im) =
    -2 * S.lam u v * (starRingEnd ℂ (S.theta u v) * S.xi u v).re / S.r u v -
      2 * e * S.Q u v * S.nu u v * S.lam u v *
        (starRingEnd ℂ (S.phi u v) * S.theta u v).im /
        ((1 - S.mu u v) * S.r u v) := by
  simp [Fields.thetaU, Fields.waveSource, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im, Complex.normSq_apply]
  field_simp [hr, hgap]
  ring

private theorem xi_norm_source (S : Fields) (e u v : ℝ)
    (hr : S.r u v ≠ 0) (hgap : 1 - S.mu u v ≠ 0) :
    2 * ((S.xi u v).re * (S.xiV e u v).re +
      (S.xi u v).im * (S.xiV e u v).im) =
    -2 * S.nu u v * (starRingEnd ℂ (S.theta u v) * S.xi u v).re / S.r u v +
      2 * e * S.Q u v * S.nu u v * S.lam u v *
        (starRingEnd ℂ (S.phi u v) * S.xi u v).im /
        ((1 - S.mu u v) * S.r u v) := by
  simp [Fields.xiV, Fields.waveSource, Complex.mul_re, Complex.mul_im,
    Complex.div_re, Complex.div_im, Complex.normSq_apply]
  field_simp [hr, hgap]
  ring

private theorem massJet_defect_transport (r l n m Q T X W Jt Jx e E : ℝ)
    (hr : r ≠ 0) (hl : l ≠ 0) (hn : n ≠ 0) (hg : 1 - 2 * m / r ≠ 0) :
    let H := 1 - 2 * m / r
    let K := n * l / r * ((2 * m / r - Q ^ 2 / r ^ 2) / H)
    let MU := H * X / (2 * n) + Q ^ 2 * n / (2 * r ^ 2)
    let MV := H * T / (2 * l) + Q ^ 2 * l / (2 * r ^ 2)
    let TU := -2 * l * W / r - 2 * e * Q * n * l * Jt / (H * r)
    let XV := -2 * n * W / r + 2 * e * Q * n * l * Jx / (H * r)
    massJet H T l Q r (gapJet m r (MU + E) n) TU K (e * r * Jx) n -
      massJet H X n Q r (gapJet m r MV l) XV K (-(e * r * Jt)) l =
        -(T / (l * r)) * E := by
  have hnum : r - 2 * m ≠ 0 := by
    intro hz
    apply hg
    have hm : 2 * m = r := by linarith
    rw [hm, div_self hr]
    ring
  have hnum' : r - m * 2 ≠ 0 := by simpa only [mul_comm m 2] using hnum
  dsimp only [massJet, gapJet]
  field_simp [hr, hl, hn, hg, hnum, hnum']
  ring

/-- Recover the missing incoming mass constraint on a positive-radius C¹
rectangle after radius, scalar and Maxwell recovery. The outgoing mass
primitive supplies its mixed derivative; explicit first-jet differentiation
then gives the actual homogeneous mass-defect equation. The coefficient is
`-‖θ‖²/(λr)` and there are no estimate constants or assumed defect transports. -/
theorem rectangle_mass_constraint
    {a b c d e : ℝ} {S : Fields}
    (hab : a < b) (hcd : c < d)
    (cr : ContDiffOn ℝ 1 (Function.uncurry S.r) (Icc a b ×ˢ Icc c d))
    (cl : ContDiffOn ℝ 1 (Function.uncurry S.lam) (Icc a b ×ˢ Icc c d))
    (cn : ContDiffOn ℝ 1 (Function.uncurry S.nu) (Icc a b ×ˢ Icc c d))
    (cm : ContDiffOn ℝ 1 (Function.uncurry S.m) (Icc a b ×ˢ Icc c d))
    (cQ : ContDiffOn ℝ 1 (Function.uncurry S.Q) (Icc a b ×ˢ Icc c d))
    (ct : ContDiffOn ℝ 1 (Function.uncurry S.theta) (Icc a b ×ˢ Icc c d))
    (cx : ContDiffOn ℝ 1 (Function.uncurry S.xi) (Icc a b ×ˢ Icc c d))
    (hr : ∀ p ∈ Icc a b ×ˢ Icc c d, S.r p.1 p.2 ≠ 0)
    (hl : ∀ p ∈ Icc a b ×ˢ Icc c d, S.lam p.1 p.2 ≠ 0)
    (hn : ∀ p ∈ Icc a b ×ˢ Icc c d, S.nu p.1 p.2 ≠ 0)
    (hg : ∀ p ∈ Icc a b ×ˢ Icc c d, 1 - S.mu p.1 p.2 ≠ 0)
    (hru : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) S.r p.1 p.2 = S.nu p.1 p.2)
    (hrv : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) S.r p.1 p.2 = S.lam p.1 p.2)
    (hlu : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) S.lam p.1 p.2 = S.rUV p.1 p.2)
    (hnv : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) S.nu p.1 p.2 = S.rUV p.1 p.2)
    (hQu : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) S.Q p.1 p.2 = S.QU e p.1 p.2)
    (hQv : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) S.Q p.1 p.2 = S.QV e p.1 p.2)
    (htu : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) S.theta p.1 p.2 = S.thetaU e p.1 p.2)
    (hxv : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) S.xi p.1 p.2 = S.xiV e p.1 p.2)
    (hmv : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) S.m p.1 p.2 = S.mV p.1 p.2)
    (hbase : ∀ u ∈ Icc a b,
      pdU (Icc a b ×ˢ Icc c d) S.m u c = S.mU u c) :
    ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) S.m p.1 p.2 = S.mU p.1 p.2 := by
  let D := Icc a b ×ˢ Icc c d
  have hD : UniqueDiffOn ℝ D := (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc hcd)
  have cH : ContDiffOn ℝ 1 (fun p => 1 - S.mu p.1 p.2) D :=
    contDiffOn_const.sub (((contDiffOn_const (c := (2 : ℝ))).mul cm).div cr hr)
  have cV : ContDiffOn ℝ 1 (Function.uncurry S.mV) D :=
    ((cH.mul (ct.norm_sq ℂ)).div ((contDiffOn_const (c := (2 : ℝ))).mul cl)
      (fun p hp => mul_ne_zero (by norm_num) (hl p hp))).add
      (((cQ.pow 2).mul cl).div ((contDiffOn_const (c := (2 : ℝ))).mul (cr.pow 2))
        (fun p hp => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hr p hp))))
  have cU : ContDiffOn ℝ 1 (Function.uncurry S.mU) D :=
    ((cH.mul (cx.norm_sq ℂ)).div ((contDiffOn_const (c := (2 : ℝ))).mul cn)
      (fun p hp => mul_ne_zero (by norm_num) (hn p hp))).add
      (((cQ.pow 2).mul cn).div ((contDiffOn_const (c := (2 : ℝ))).mul (cr.pow 2))
        (fun p hp => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hr p hp))))
  let TU (u v : ℝ) := -2 * S.lam u v *
    (starRingEnd ℂ (S.theta u v) * S.xi u v).re / S.r u v -
    2 * e * S.Q u v * S.nu u v * S.lam u v *
      (starRingEnd ℂ (S.phi u v) * S.theta u v).im / ((1 - S.mu u v) * S.r u v)
  let XV (u v : ℝ) := -2 * S.nu u v *
    (starRingEnd ℂ (S.theta u v) * S.xi u v).re / S.r u v +
    2 * e * S.Q u v * S.nu u v * S.lam u v *
      (starRingEnd ℂ (S.phi u v) * S.xi u v).im / ((1 - S.mu u v) * S.r u v)
  have hdV : ∀ p ∈ D, pdU D S.mV p.1 p.2 = massJet
      (1 - S.mu p.1 p.2) (‖S.theta p.1 p.2‖ ^ 2) (S.lam p.1 p.2)
      (S.Q p.1 p.2) (S.r p.1 p.2)
      (gapJet (S.m p.1 p.2) (S.r p.1 p.2) (pdU D S.m p.1 p.2) (S.nu p.1 p.2))
      (TU p.1 p.2) (S.rUV p.1 p.2) (S.QU e p.1 p.2) (S.nu p.1 p.2) := by
    intro p hp
    have hs : MapsTo (fun x => (x, p.2)) (Icc a b) D := fun _ hx => ⟨hx, hp.2⟩
    have hρ := hasDerivWithinAt_pdU cr hp hs
    have hl' := hasDerivWithinAt_pdU cl hp hs
    have hm' := hasDerivWithinAt_pdU cm hp hs
    have hq := hasDerivWithinAt_pdU cQ hp hs
    have ht := hasDerivWithinAt_pdU ct hp hs
    rw [hru p hp] at hρ
    rw [hlu p hp] at hl'
    rw [hQu p hp] at hq
    rw [htu p hp] at ht
    have ht' := hasDerivWithinAt_complex_norm_square ht
    rw [theta_norm_source S e p.1 p.2 (hr p hp) (hg p hp)] at ht'
    have hH := hasDerivWithinAt_gap hm' hρ (hr p hp)
    have hd := hasDerivWithinAt_mass_source hH ht' hl' hq hρ (hl p hp) (hr p hp)
    have hj := hd.derivWithin (uniqueDiffOn_Icc hab p.1 hp.1)
    have hex := (hasDerivWithinAt_pdU cV hp hs).derivWithin
      (uniqueDiffOn_Icc hab p.1 hp.1)
    exact hex.symm.trans hj
  intro p hp
  have hs : MapsTo (fun v => (p.1, v)) (Icc c d) D := fun _ hv => ⟨hp.1, hv⟩
  have hc : ContinuousOn (fun v => pdU D S.m p.1 v - S.mU p.1 v) (Icc c d) :=
    ((continuousOn_pdU cm hD).sub cU.continuousOn).comp
      (continuousOn_const.prodMk continuousOn_id) hs
  have ck : ContinuousOn (fun v => -(‖S.theta p.1 v‖ ^ 2 /
      (S.lam p.1 v * S.r p.1 v))) (Icc c d) :=
    (((ct.continuousOn.norm.pow 2).div (cl.continuousOn.mul cr.continuousOn)
      (fun q hq => mul_ne_zero (hl q hq) (hr q hq))).neg).comp
      (f := fun v : ℝ => (p.1, v))
      (continuousOn_const.prodMk continuousOn_id) hs
  have hz := Null.eq_zero_of_homogeneous_transport hcd.le hc ck
    (sub_eq_zero.mpr (hbase p.1 hp.1)) (fun v hv => by
      have hpv' := hs ⟨hv.1.le, hv.2.le⟩
      have hρ := hasDerivWithinAt_pdV cr hpv' hs
      have hn' := hasDerivWithinAt_pdV cn hpv' hs
      have hm' := hasDerivWithinAt_pdV cm hpv' hs
      have hq := hasDerivWithinAt_pdV cQ hpv' hs
      have hx := hasDerivWithinAt_pdV cx hpv' hs
      rw [hrv (p.1, v) hpv'] at hρ
      rw [hnv (p.1, v) hpv'] at hn'
      rw [hmv (p.1, v) hpv'] at hm'
      rw [hQv (p.1, v) hpv'] at hq
      rw [hxv (p.1, v) hpv'] at hx
      have hx' := hasDerivWithinAt_complex_norm_square hx
      rw [xi_norm_source S e p.1 v (hr (p.1, v) hpv') (hg (p.1, v) hpv')] at hx'
      have hH := hasDerivWithinAt_gap hm' hρ (hr (p.1, v) hpv')
      have hU := hasDerivWithinAt_mass_source hH hx' hn' hq hρ
        (hn (p.1, v) hpv') (hr (p.1, v) hpv')
      have hmix := hasDerivWithinAt_pdU_of_pdV_eq hab hcd cm cV hmv hp.1
        ⟨hv.1.le, hv.2.le⟩
      rw [hdV (p.1, v) hpv'] at hmix
      have hd := hmix.sub hU
      have halg := massJet_defect_transport (S.r p.1 v) (S.lam p.1 v) (S.nu p.1 v)
        (S.m p.1 v) (S.Q p.1 v) (‖S.theta p.1 v‖ ^ 2) (‖S.xi p.1 v‖ ^ 2)
        (starRingEnd ℂ (S.theta p.1 v) * S.xi p.1 v).re
        (starRingEnd ℂ (S.phi p.1 v) * S.theta p.1 v).im
        (starRingEnd ℂ (S.phi p.1 v) * S.xi p.1 v).im e
        (pdU D S.m p.1 v - S.mU p.1 v)
        (hr (p.1, v) hpv') (hl (p.1, v) hpv') (hn (p.1, v) hpv') (hg (p.1, v) hpv')
      change massJet _ _ _ _ _ (gapJet _ _
        (S.mU p.1 v + (pdU D S.m p.1 v - S.mU p.1 v)) _) _ _ _ _ - _ = _ at halg
      have he : S.mU p.1 v + (pdU D S.m p.1 v - S.mU p.1 v) = pdU D S.m p.1 v := by ring
      rw [he] at halg
      convert hd.hasDerivAt (Icc_mem_nhds hv.1 hv.2) using 1
      · rfl
      · exact halg.symm) p.2 hp.2
  exact sub_eq_zero.mp hz

/-- A C¹ solution of the positive-radius Goursat subsystem solves every
frozen field equation when its four missing incoming equations hold on the
lower side. Radius, scalar, Maxwell and mass defects are computed from the
subsystem and then eliminated in that order. The signs are the state-tube
margins. This is the constraint-recovery component of internal project record's
continuation argument (L1070–1074), with no C² premise. -/
theorem isC1Solution_rectangle_of_goursat
    {a b c d e : ℝ} {S : Fields}
    (hab : a < b) (hcd : c < d) (hbc : b < c)
    (cr : ContDiffOn ℝ 1 (Function.uncurry S.r) (Icc a b ×ˢ Icc c d))
    (cl : ContDiffOn ℝ 1 (Function.uncurry S.lam) (Icc a b ×ˢ Icc c d))
    (cn : ContDiffOn ℝ 1 (Function.uncurry S.nu) (Icc a b ×ˢ Icc c d))
    (cm : ContDiffOn ℝ 1 (Function.uncurry S.m) (Icc a b ×ˢ Icc c d))
    (cQ : ContDiffOn ℝ 1 (Function.uncurry S.Q) (Icc a b ×ˢ Icc c d))
    (cp : ContDiffOn ℝ 1 (Function.uncurry S.phi) (Icc a b ×ˢ Icc c d))
    (cA : ContDiffOn ℝ 1 (Function.uncurry S.A) (Icc a b ×ˢ Icc c d))
    (ct : ContDiffOn ℝ 1 (Function.uncurry S.theta) (Icc a b ×ˢ Icc c d))
    (cx : ContDiffOn ℝ 1 (Function.uncurry S.xi) (Icc a b ×ˢ Icc c d))
    (hr : ∀ p ∈ Icc a b ×ˢ Icc c d, 0 < S.r p.1 p.2)
    (hl : ∀ p ∈ Icc a b ×ˢ Icc c d, 0 < S.lam p.1 p.2)
    (hn : ∀ p ∈ Icc a b ×ˢ Icc c d, S.nu p.1 p.2 < 0)
    (hg : ∀ p ∈ Icc a b ×ˢ Icc c d, 0 < 1 - S.mu p.1 p.2)
    (hev : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdV (Icc a b ×ˢ Icc c d) S.r p.1 p.2 = S.lam p.1 p.2 ∧
      pdV (Icc a b ×ˢ Icc c d) S.nu p.1 p.2 = S.rUV p.1 p.2 ∧
      pdV (Icc a b ×ˢ Icc c d) S.m p.1 p.2 = S.mV p.1 p.2 ∧
      pdV (Icc a b ×ˢ Icc c d) S.Q p.1 p.2 = S.QV e p.1 p.2 ∧
      pdV (Icc a b ×ˢ Icc c d) S.A p.1 p.2 = S.AV p.1 p.2 ∧
      pdV (Icc a b ×ˢ Icc c d) S.phi p.1 p.2 = S.phiV p.1 p.2 ∧
      pdV (Icc a b ×ˢ Icc c d) S.xi p.1 p.2 = S.xiV e p.1 p.2)
    (hlu : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) S.lam p.1 p.2 = S.rUV p.1 p.2)
    (htu : ∀ p ∈ Icc a b ×ˢ Icc c d,
      pdU (Icc a b ×ˢ Icc c d) S.theta p.1 p.2 = S.thetaU e p.1 p.2)
    (hbase : ∀ u ∈ Icc a b,
      pdU (Icc a b ×ˢ Icc c d) S.r u c = S.nu u c ∧
      pdU (Icc a b ×ˢ Icc c d) S.phi u c = S.phiU e u c ∧
      pdU (Icc a b ×ˢ Icc c d) S.Q u c = S.QU e u c ∧
      pdU (Icc a b ×ˢ Icc c d) S.m u c = S.mU u c) :
    IsC1Solution e S (Icc a b ×ˢ Icc c d) := by
  have hr0 : ∀ p ∈ Icc a b ×ˢ Icc c d, S.r p.1 p.2 ≠ 0 := fun p hp => (hr p hp).ne'
  have hl0 : ∀ p ∈ Icc a b ×ˢ Icc c d, S.lam p.1 p.2 ≠ 0 := fun p hp => (hl p hp).ne'
  have hn0 : ∀ p ∈ Icc a b ×ˢ Icc c d, S.nu p.1 p.2 ≠ 0 := fun p hp => (hn p hp).ne
  have hg0 : ∀ p ∈ Icc a b ×ˢ Icc c d, 1 - S.mu p.1 p.2 ≠ 0 := fun p hp => (hg p hp).ne'
  have hru := rectangle_radius_constraint hab hcd cr cl cn
    (fun p hp => (hev p hp).1)
    (fun p hp => (hlu p hp).trans (hev p hp).2.1.symm)
    (fun u hu => (hbase u hu).1)
  have hpu := rectangle_scalar_constraint hab hcd cr cp ct cx cA hr0 hg0 hru
    (fun p hp => (hev p hp).1) (fun p hp => (hev p hp).2.2.2.2.2.1) htu
    (fun p hp => (hev p hp).2.2.2.2.2.2) (fun p hp => (hev p hp).2.2.2.2.1)
    (fun u hu => (hbase u hu).2.1)
  have hQu := rectangle_charge_constraint hab hcd cr cp ct cx cQ hr0 hg0 hru
    (fun p hp => (hev p hp).1) hpu (fun p hp => (hev p hp).2.2.2.2.2.1) htu
    (fun p hp => (hev p hp).2.2.2.2.2.2) (fun p hp => (hev p hp).2.2.2.1)
    (fun u hu => (hbase u hu).2.2.1)
  have hmu := rectangle_mass_constraint hab hcd cr cl cn cm cQ ct cx hr0 hl0 hn0 hg0
    hru (fun p hp => (hev p hp).1) hlu (fun p hp => (hev p hp).2.1)
    hQu (fun p hp => (hev p hp).2.2.2.1) htu (fun p hp => (hev p hp).2.2.2.2.2.2)
    (fun p hp => (hev p hp).2.2.1) (fun u hu => (hbase u hu).2.2.2)
  refine ⟨?_, (fun p hp _ => hr p hp), hl, hn, hg, cr, cl, cn, cm, cQ, cp, cA, ct, cx,
    (fun p hp _ => hev p hp), ?_, ?_⟩
  · intro p hp
    exact (hp.1.2.trans_lt (hbc.trans_le hp.2.1)).le
  · intro p hp _
    exact ⟨hru p hp, hlu p hp, hmu p hp, hQu p hp, hpu p hp, htu p hp⟩
  · intro t ht
    exact False.elim ((lt_irrefl t) (ht.1.2.trans_lt (hbc.trans_le ht.2.1)))

end EmcsfAcExtension.Local
