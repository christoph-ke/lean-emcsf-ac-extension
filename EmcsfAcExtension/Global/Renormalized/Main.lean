module

public import EmcsfAcExtension.Global.Renormalized.WeakTransfer

/-! # Exact charged renormalized identities on the original development

This module removes the weight by incoming Raychaudhuri and packages the
common-label AC interpretation. All representatives are the prescribed
fixed-density and unitary representatives; no C¹ solution class is used.
Source: `charged_SF_new_version.tex:L3150–L3260`; approved internal project record.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Renormalized

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

private theorem unweight_source (e : ℝ) (S : Fields) (u v : ℝ)
    (hl : S.lam u v ≠ 0) (hg : 1 - S.mu u v ≠ 0) :
    ((1 - S.mu u v) / S.lam u v : ℝ) * weightedJSource e S u v =
      (S.nu u v : ℂ) * S.theta u v / S.r u v ^ 2 *
        (Local.curv S u v + 2 * starRingEnd ℂ (Local.curv S u v)) +
      Local.emSourceJ e S u v := by
  unfold weightedJSource
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hl,
    show 1 - (S.mu u v : ℂ) ≠ 0 from by exact_mod_cast hg]

/-- [node lem:ct-renormalized#weak-AC-transfer]
Removing the weight from the selected representative gives the incoming
renormalized equation, with the exact Raychaudhuri damping coefficient.
This holds on every fixed label as an AC identity, including endpoints
through its integral form. -/
theorem renormalized_in_section (hS : IsSolution e S D) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D ∩ {p | p.1 < p.2}) :
    ∀ v ∈ Icc c d,
      let J := fun u => ((1 - S.mu u v) / S.lam u v : ℝ) *
        weightedJRepresentative e S a u v
      AbsolutelyContinuousOnInterval J a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt J
        (-(‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v) : ℝ) * J u +
          (S.nu u v : ℂ) * S.theta u v / S.r u v ^ 2 *
            (Local.curv S u v + 2 * starRingEnd ℂ (Local.curv S u v)) +
          Local.emSourceJ e S u v - I * e * S.A u v * J u) u := by
  have hbc : b < c := (hrect (show (b, c) ∈ Icc a b ×ˢ Icc c d from
    ⟨⟨hab.le, le_rfl⟩, ⟨le_rfl, hcd.le⟩⟩)).2
  intro v hv
  have hs : inSeg a b v ⊆ D := by
    rintro ⟨x, y⟩ ⟨hx, hxb, rfl⟩
    exact (hrect ⟨⟨hx, hxb⟩, hv⟩).1
  have hlog := Calculus.raychaudhuri_in_section hS hab.le (hbc.trans_le hv.1) hs
  have hW := weighted_section hS hab hcd hrect v hv
  have hk (u : ℝ) (hu : u ∈ Icc a b) :
      Real.exp (-Real.log (S.lam u v / (1 - S.mu u v))) =
        (1 - S.mu u v) / S.lam u v := by
    have hp : (u, v) ∈ D := hs ⟨hu.1, hu.2, rfl⟩
    rw [Real.exp_neg, Real.exp_log (div_pos (hS.lam_pos (u, v) hp)
      (hS.one_sub_mu_pos (u, v) hp)), inv_div]
  have hac := hlog.1.neg.exp.ofReal.mul_normed_ring hW.1
  refine ⟨hac.congr (fun u hu => by
    dsimp only [Pi.mul_apply, Pi.neg_apply]
    rw [hk u (by simpa [uIcc_of_le hab.le] using hu)]), ?_⟩
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [hlog.2.filter_mono (ae_mono (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)),
    hW.2.filter_mono (ae_mono (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)),
    ae_restrict_mem measurableSet_Ioo] with u hlu hWu hu
  have hp : (u, v) ∈ D := hs ⟨hu.1.le, hu.2.le, rfl⟩
  have hd := hlu.neg.exp.ofReal_comp.mul hWu
  have hd' := hd.congr_of_eventuallyEq
    (f₁ := fun x => ((1 - S.mu x v) / S.lam x v : ℝ) *
      weightedJRepresentative e S a x v) (by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
    dsimp only [Pi.mul_apply, Pi.neg_apply]
    rw [hk x (Ioo_subset_Icc_self hx)])
  simp only [Pi.neg_apply] at hd'
  apply hd'.congr_deriv
  rw [hk u (Ioo_subset_Icc_self hu)]
  have hsrc := unweight_source e S u v (hS.lam_pos (u, v) hp).ne'
    (hS.one_sub_mu_pos (u, v) hp).ne'
  push_cast at hsrc ⊢
  linear_combination hsrc

/-- [node lem:ct-renormalized#weak-AC-transfer]
The unweighted selected representative equals the frozen `jOut` on the
same common full-measure set of labels, simultaneously for every incoming
time. This is the representative used in the incoming equation. -/
theorem renormalized_representation (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ origDomain ui ∩ {p | p.1 < p.2}) :
    ∀ᵐ v ∂volume.restrict (Icc c d), ∀ u ∈ Icc a b,
      jOut S u v = ((1 - S.mu u v) / S.lam u v : ℝ) *
        weightedJRepresentative e S a u v := by
  filter_upwards [Calculus.weighted_representation ui e S h a b c d hab hcd hrect,
    ae_restrict_mem measurableSet_Icc] with v hv hvm u hu
  rw [← hv u hu]
  unfold weightedJ
  have hl := (h.solution.lam_pos (u, v) (hrect ⟨hu, hvm⟩).1).ne'
  have hg := (h.solution.one_sub_mu_pos (u, v) (hrect ⟨hu, hvm⟩).1).ne'
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hl,
    show 1 - (S.mu u v : ℂ) ≠ 0 from by exact_mod_cast hg]

/-- [node lem:ct-renormalized#weak-AC-transfer]
The curvature primitive has the same endpoint integral identity with the
selected representative. Every row and every pair of subsegment endpoints
is allowed, since the exceptional set precedes the quantifier over time. -/
theorem curvature_representative_integralForm (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ origDomain ui ∩ {p | p.1 < p.2})
    {u s t : ℝ} (hu : u ∈ Icc a b) (hs : s ∈ Icc c d) (ht : t ∈ Icc c d)
    (hst : s ≤ t) :
    IntegralForm (fun v => (S.r u v : ℂ) * Local.curv S u v)
      (fun v => S.r u v * starRingEnd ℂ (S.xi u v / S.nu u v) *
        (((1 - S.mu u v) / S.lam u v : ℝ) * weightedJRepresentative e S a u v) +
        (S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) -
        I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v)) s t := by
  have hbc : b < c := (hrect (show (b, c) ∈ Icc a b ×ˢ Icc c d from
    ⟨⟨hab.le, le_rfl⟩, ⟨le_rfl, hcd.le⟩⟩)).2
  have hout := curvature_out_integralForm h.solution
    (hu.2.trans_lt (hbc.trans_le hs.1)) hst (by
      rintro ⟨x, y⟩ ⟨rfl, hy⟩
      exact (hrect ⟨hu, ⟨hs.1.trans hy.1, hy.2.trans ht.2⟩⟩).1)
  have heq := renormalized_representation ui e S h a b c d hab hcd hrect
  have heq' : (fun v => S.r u v * starRingEnd ℂ (S.xi u v / S.nu u v) * jOut S u v +
      (S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) -
      I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v)) =ᵐ[volume.restrict (uIoc s t)]
      (fun v => S.r u v * starRingEnd ℂ (S.xi u v / S.nu u v) *
        (((1 - S.mu u v) / S.lam u v : ℝ) * weightedJRepresentative e S a u v) +
        (S.lam u v * S.Q u v ^ 2 / S.r u v ^ 2 : ℝ) -
        I * e * S.Q u v * S.theta u v * starRingEnd ℂ (S.phi u v)) := by
    apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 heq] with v hv hvm
    rw [uIoc_of_le hst] at hvm
    rw [hv ⟨hs.1.trans hvm.1.le, hvm.2.trans ht.2⟩ u hu]
  refine ⟨hout.1.congr_ae heq', ?_⟩
  rw [hout.2]
  exact intervalIntegral.integral_congr_ae_restrict heq'

/-- [node lem:ct-renormalized#weak-AC-transfer]
Representatives constructed with two different fixed initial rows agree
on their overlap, outside one null set of labels before quantifying over
all common incoming times. Local characteristic identities can therefore
be patched without evaluating arbitrary product-a.e. representatives. -/
theorem weighted_representative_overlap (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) {a b c d a' b' c' d' : ℝ}
    (hab : a < b) (hcd : c < d) (hab' : a' < b') (hcd' : c' < d')
    (hrect : Icc a b ×ˢ Icc c d ⊆ origDomain ui ∩ {p | p.1 < p.2})
    (hrect' : Icc a' b' ×ˢ Icc c' d' ⊆ origDomain ui ∩ {p | p.1 < p.2}) :
    ∀ᵐ v ∂volume.restrict (Icc (max c c') (min d d')),
      ∀ u ∈ Icc (max a a') (min b b'),
        weightedJRepresentative e S a u v = weightedJRepresentative e S a' u v := by
  have h₁ := Calculus.weighted_representation ui e S h a b c d hab hcd hrect
  have h₂ := Calculus.weighted_representation ui e S h a' b' c' d' hab' hcd' hrect'
  apply (ae_restrict_iff' measurableSet_Icc).2
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 h₁,
    (ae_restrict_iff' measurableSet_Icc).1 h₂] with v hv₁ hv₂ hv u hu
  have hv1 : v ∈ Icc c d :=
    ⟨(le_max_left _ _).trans hv.1, hv.2.trans (min_le_left _ _)⟩
  have hv2 : v ∈ Icc c' d' :=
    ⟨(le_max_right _ _).trans hv.1, hv.2.trans (min_le_right _ _)⟩
  have hu1 : u ∈ Icc a b :=
    ⟨(le_max_left _ _).trans hu.1, hu.2.trans (min_le_left _ _)⟩
  have hu2 : u ∈ Icc a' b' :=
    ⟨(le_max_right _ _).trans hu.1, hu.2.trans (min_le_right _ _)⟩
  exact (hv₁ hv1 u hu1).symm.trans (hv₂ hv2 u hu2)

/-- [node lem:ct-renormalized#weak-AC-transfer]
The prescribed weighted representative is jointly a.e. strongly measurable
on each proper rectangle. Its only rough factor is the fixed initial L¹
density; the remaining factors are jointly continuous. -/
theorem aestronglyMeasurable_weighted_representative
    (hS : IsSolution e S D) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D ∩ {p | p.1 < p.2}) :
    AEStronglyMeasurable
      (fun p : ℝ × ℝ => weightedJRepresentative e S a p.1 p.2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  obtain ⟨P, R, hP, hR, hPR, _⟩ := Calculus.exists_density_factors hS hab hcd hrect
  have hD : Icc a b ×ˢ Icc c d ⊆ D := fun p hp => (hrect hp).1
  have hinit := (hS.ac_out a c d hcd.le (by
    rintro ⟨x, y⟩ ⟨rfl, hy⟩
    exact hD ⟨⟨le_rfl, hab.le⟩, hy⟩)).2.2.2.2
  have hw := Density.aestronglyMeasurable_fixedDensity hcd.le hP hR
    hinit.intervalIntegrable_deriv_complex
  have cr := hS.cont_r.mono hD
  have cl := hS.cont_lam.mono hD
  have ct := hS.cont_theta.mono hD
  have hr (p : ℝ × ℝ) (hp : p ∈ Icc a b ×ˢ Icc c d) :=
    (hS.r_pos p (hD hp) (hrect hp).2).ne'
  have hl (p : ℝ × ℝ) (hp : p ∈ Icc a b ×ˢ Icc c d) := (hS.lam_pos p (hD hp)).ne'
  have cy := ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun p hp => Complex.ofReal_ne_zero.mpr (hl p hp))
  have cc := (cl.pow 2).div cr hr
  have ccor : ContinuousOn (fun p : ℝ × ℝ =>
      (S.lam p.1 p.2 ^ 2 / S.r p.1 p.2 : ℝ) *
        (‖S.theta p.1 p.2 / S.lam p.1 p.2‖ : ℂ) ^ 2 *
          (S.theta p.1 p.2 / S.lam p.1 p.2)) (Icc a b ×ˢ Icc c d) :=
    (((Complex.continuous_ofReal.comp_continuousOn cc).mul
      ((Complex.continuous_ofReal.comp_continuousOn cy.norm).pow 2)).mul cy)
  rw [Measure.prod_restrict] at hw ⊢
  have hM := ((Complex.continuous_ofReal.comp_continuousOn cl).aestronglyMeasurable
    (measurableSet_Icc.prod measurableSet_Icc)).mul hw |>.sub
      (ccor.aestronglyMeasurable (measurableSet_Icc.prod measurableSet_Icc))
  apply hM.congr
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  dsimp only [Function.comp_apply, Function.uncurry, Pi.mul_apply, Pi.sub_apply]
  rw [← hPR p.1 hp.1 p.2 hp.2]
  exact weighted_density_eq_representative hS hab hcd hrect p.1 hp.1 p.2 hp.2

/-- [node lem:ct-renormalized#weak-AC-transfer]
The selected unweighted representative is jointly a.e. strongly measurable
on every proper rectangle, using only its continuous weight and the fixed
initial density. -/
theorem aestronglyMeasurable_renormalized_representative
    (hS : IsSolution e S D) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D ∩ {p | p.1 < p.2}) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      ((1 - S.mu p.1 p.2) / S.lam p.1 p.2 : ℝ) *
        weightedJRepresentative e S a p.1 p.2)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  have hD : Icc a b ×ˢ Icc c d ⊆ D := fun p hp => (hrect hp).1
  have cr := hS.cont_r.mono hD
  have cm := hS.cont_m.mono hD
  have cl := hS.cont_lam.mono hD
  have cmu : ContinuousOn (Function.uncurry S.mu) (Icc a b ×ˢ Icc c d) :=
    (continuousOn_const.mul cm).div cr
      (fun p hp => (hS.r_pos p (hD hp) (hrect hp).2).ne')
  have ck : ContinuousOn (fun p : ℝ × ℝ =>
      (((1 - S.mu p.1 p.2) / S.lam p.1 p.2 : ℝ) : ℂ)) (Icc a b ×ˢ Icc c d) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((continuousOn_const.sub cmu).div cl (fun p hp => (hS.lam_pos p (hD hp)).ne'))
  have hW := aestronglyMeasurable_weighted_representative hS hab hcd hrect
  rw [Measure.prod_restrict] at hW ⊢
  exact (ck.aestronglyMeasurable (measurableSet_Icc.prod measurableSet_Icc)).mul hW

/-- [node eq:ct-weighted-j]
The weighted equation in integral form between any two incoming endpoints
of the rectangle, on every selected label. Source integrability is derived
from AC, with no boundary or trace assumption. -/
theorem weighted_integralForm (hS : IsSolution e S D) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D ∩ {p | p.1 < p.2})
    {v s t : ℝ} (hv : v ∈ Icc c d) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (hst : s ≤ t) :
    IntegralForm (fun u => weightedJRepresentative e S a u v)
      (fun u => weightedJSource e S u v - I * e * S.A u v *
        weightedJRepresentative e S a u v) s t := by
  have h := weighted_section hS hab hcd hrect v hv
  have hsub : uIcc s t ⊆ uIcc a b := by
    rw [uIcc_of_le hst, uIcc_of_le hab.le]
    exact Icc_subset_Icc hs.1 ht.2
  apply integralForm_of_ac_of_ae_deriv_eq (h.1.mono hsub)
  apply (ae_restrict_iff' measurableSet_uIcc).2
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 h.2] with u hu hum
  exact (hu (by simpa [uIcc_of_le hab.le] using hsub hum)).deriv

/-- [node lem:ct-renormalized#weak-AC-transfer]
The unweighted incoming equation holds in integral form on every incoming
subsegment and every selected label. The covariant connection is included
in the ordinary source, and integrability follows from AC. -/
theorem renormalized_in_integralForm (hS : IsSolution e S D) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D ∩ {p | p.1 < p.2})
    {v s t : ℝ} (hv : v ∈ Icc c d) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (hst : s ≤ t) :
    let J := fun u => ((1 - S.mu u v) / S.lam u v : ℝ) *
      weightedJRepresentative e S a u v
    IntegralForm J (fun u =>
      -(‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v) : ℝ) * J u +
        (S.nu u v : ℂ) * S.theta u v / S.r u v ^ 2 *
          (Local.curv S u v + 2 * starRingEnd ℂ (Local.curv S u v)) +
        Local.emSourceJ e S u v - I * e * S.A u v * J u) s t := by
  have h := renormalized_in_section hS hab hcd hrect v hv
  have hsub : uIcc s t ⊆ uIcc a b := by
    rw [uIcc_of_le hst, uIcc_of_le hab.le]
    exact Icc_subset_Icc hs.1 ht.2
  apply integralForm_of_ac_of_ae_deriv_eq (h.1.mono hsub)
  apply (ae_restrict_iff' measurableSet_uIcc).2
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 h.2] with u hu hum
  exact (hu (by simpa [uIcc_of_le hab.le] using hsub hum)).deriv

/-- [node lem:ct-renormalized#weak-AC-transfer]
[node eq:ct-weighted-j]
The exact weighted system on every proper rectangle of the original
frozen AC development: one common good-label set and incoming AC transport
on every selected label. The curvature integral identity and unweighted
transport are exported above; all identities have no estimate constants. -/
theorem weak_ac_transfer (ui e : ℝ) (S : Fields) (h : OriginalData ui e S)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ origDomain ui ∩ {p | p.1 < p.2}) :
    (∀ᵐ v ∂volume.restrict (Icc c d), ∀ u ∈ Icc a b,
      weightedJ S u v = weightedJRepresentative e S a u v) ∧
    (∀ v ∈ Icc c d,
      AbsolutelyContinuousOnInterval (fun u => weightedJRepresentative e S a u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt
        (fun x => weightedJRepresentative e S a x v)
        (weightedJSource e S u v - I * e * S.A u v * weightedJRepresentative e S a u v) u) :=
  ⟨Calculus.weighted_representation ui e S h a b c d hab hcd hrect,
    weighted_section h.solution hab hcd hrect⟩

/-- [internal]
Layer interface for the charged renormalized identities. The canonical
weak-class graph closure is `weak_ac_transfer`; the other exact equations
and their endpoint integral forms are exported in this module family. -/
theorem main (ui e : ℝ) (S : Fields) (h : OriginalData ui e S)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ origDomain ui ∩ {p | p.1 < p.2}) :
    (∀ᵐ v ∂volume.restrict (Icc c d), ∀ u ∈ Icc a b,
      weightedJ S u v = weightedJRepresentative e S a u v) ∧
    (∀ v ∈ Icc c d,
      AbsolutelyContinuousOnInterval (fun u => weightedJRepresentative e S a u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt
        (fun x => weightedJRepresentative e S a x v)
        (weightedJSource e S u v - I * e * S.A u v * weightedJRepresentative e S a u v) u) :=
  weak_ac_transfer ui e S h a b c d hab hcd hrect

end EmcsfAcExtension.Global.Renormalized
