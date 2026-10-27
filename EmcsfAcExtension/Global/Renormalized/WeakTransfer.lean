module

public import EmcsfAcExtension.Global.Renormalized.Curvature
public import EmcsfAcExtension.Global.Calculus.DensityRepresentative
public import EmcsfAcExtension.Global.Calculus.Raychaudhuri
import EmcsfAcExtension.Infra.LinearTransport
import EmcsfAcExtension.Local.Calculus.Sections

/-! # The weighted renormalized identity in the frozen AC class

The fixed-density representative is renormalized before taking its incoming
AC derivative. Its ODE and the landed algebra identify the source, and
variation of constants identifies precisely `weightedJRepresentative`.
The common good-label set comes from the fixed-density theorem, never from
evaluating an arbitrary a.e. derivative on a curve.
Source: `charged_SF_new_version.tex:L3170–L3183`, L3254–L3260; approved internal project record.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global.Renormalized

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [internal] The weighted source is jointly continuous on every off-axis
subset of the solution. Its charge derivative is the continuous frozen
right side `QV`; no higher derivative or additional norm bound is assumed. -/
theorem continuousOn_weightedJSource {K : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hK : K ⊆ D ∩ {p | p.1 < p.2}) :
    ContinuousOn (Function.uncurry (weightedJSource e S)) K := by
  have cr := hS.cont_r.mono (fun p hp => (hK hp).1)
  have cl := hS.cont_lam.mono (fun p hp => (hK hp).1)
  have cn := hS.cont_nu.mono (fun p hp => (hK hp).1)
  have cm := hS.cont_m.mono (fun p hp => (hK hp).1)
  have cQ := hS.cont_Q.mono (fun p hp => (hK hp).1)
  have cp := hS.cont_phi.mono (fun p hp => (hK hp).1)
  have ct := hS.cont_theta.mono (fun p hp => (hK hp).1)
  have cx := hS.cont_xi.mono (fun p hp => (hK hp).1)
  have hr (p : ℝ × ℝ) (hp : p ∈ K) := (hS.r_pos p (hK hp).1 (hK hp).2).ne'
  have hl (p : ℝ × ℝ) (hp : p ∈ K) := (hS.lam_pos p (hK hp).1).ne'
  have hn (p : ℝ × ℝ) (hp : p ∈ K) := (hS.nu_neg p (hK hp).1).ne
  have cmu : ContinuousOn (Function.uncurry S.mu) K :=
    (continuousOn_const.mul cm).div cr hr
  have cg : ContinuousOn (fun p : ℝ × ℝ => 1 - S.mu p.1 p.2) K :=
    continuousOn_const.sub cmu
  have hg (p : ℝ × ℝ) (hp : p ∈ K) := (hS.one_sub_mu_pos p (hK hp).1).ne'
  have cy := ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun p hp => Complex.ofReal_ne_zero.mpr (hl p hp))
  have cz := cx.div (Complex.continuous_ofReal.comp_continuousOn cn)
    (fun p hp => Complex.ofReal_ne_zero.mpr (hn p hp))
  have ccurv : ContinuousOn (Function.uncurry (Local.curv S)) K := by
    apply ((Complex.continuous_ofReal.comp_continuousOn cmu).add
      (((Complex.continuous_ofReal.comp_continuousOn cg).mul cy).mul
        (Complex.continuous_conj.comp_continuousOn cz))).congr
    intro p hp
    simpa only [Function.uncurry, Function.comp_apply, Pi.add_apply, Pi.mul_apply,
      Pi.div_apply, Complex.ofReal_sub, Complex.ofReal_one] using! curv_eq S p.1 p.2
  have cq : ContinuousOn (fun p : ℝ × ℝ => S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2) K :=
    (cQ.pow 2).div (cr.pow 2) (fun p hp => pow_ne_zero _ (hr p hp))
  have ccoef := (cl.mul cn.neg).div (cr.pow 2) (fun p hp => pow_ne_zero _ (hr p hp))
  have clg := cl.div cg hg
  have cmult := ((cn.mul cl).div (cg.mul (cr.pow 2))
    (fun p hp => mul_ne_zero (hg p hp) (pow_ne_zero _ (hr p hp))))
  have crC := Complex.continuous_ofReal.comp_continuousOn cr
  have cnC := Complex.continuous_ofReal.comp_continuousOn cn
  have cQC := Complex.continuous_ofReal.comp_continuousOn cQ
  have cqC := Complex.continuous_ofReal.comp_continuousOn cq
  have cqv : ContinuousOn (fun p : ℝ × ℝ => S.QV e p.1 p.2) K := by
    change ContinuousOn (fun p : ℝ × ℝ =>
      -(e * S.r p.1 p.2 * (starRingEnd ℂ (S.phi p.1 p.2) * S.theta p.1 p.2).im)) K
    exact ((continuousOn_const.mul cr).mul
      (Complex.continuous_im.comp_continuousOn
        ((Complex.continuous_conj.comp_continuousOn cp).mul ct))).neg
  have cqvC := Complex.continuous_ofReal.comp_continuousOn cqv
  have cbr : ContinuousOn (fun p : ℝ × ℝ =>
      (5 : ℂ) * (S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2 : ℝ) *
        (S.theta p.1 p.2 / S.lam p.1 p.2) + I * e * S.Q p.1 p.2 *
          (3 * (S.theta p.1 p.2 / S.lam p.1 p.2) + S.phi p.1 p.2)) K :=
    ((continuousOn_const.mul cqC).mul cy).add
      ((continuousOn_const.mul cQC).mul ((continuousOn_const.mul cy).add cp))
  have ctail : ContinuousOn (fun p : ℝ × ℝ =>
      I * e * (-(S.nu p.1 p.2 : ℂ)) * S.QV e p.1 p.2 * S.phi p.1 p.2 /
        (S.r p.1 p.2 : ℂ)) K :=
    (((continuousOn_const.mul cnC.neg).mul cqvC).mul cp).div crC
      (fun p hp => Complex.ofReal_ne_zero.mpr (hr p hp))
  have cem : ContinuousOn (Function.uncurry (Local.emSourceJ e S)) K := by
    apply (((Complex.continuous_ofReal.comp_continuousOn ccoef).mul cbr).add ctail).congr
    intro p hp
    simp only [Function.uncurry, Function.comp_apply, Pi.add_apply, Pi.mul_apply,
      Pi.div_apply, Pi.neg_apply, Pi.pow_apply]
    rw [Local.emSourceJ_def]
    push_cast
    ring
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      (S.nu p.1 p.2 * S.lam p.1 p.2 /
        ((1 - S.mu p.1 p.2) * S.r p.1 p.2 ^ 2) : ℝ) * S.theta p.1 p.2 *
        (Local.curv S p.1 p.2 + 2 * starRingEnd ℂ (Local.curv S p.1 p.2)) +
      (S.lam p.1 p.2 / (1 - S.mu p.1 p.2) : ℝ) * Local.emSourceJ e S p.1 p.2) K := by
    exact (((Complex.continuous_ofReal.comp_continuousOn cmult).mul ct).mul
      (ccurv.add (continuousOn_const.mul
        (Complex.continuous_conj.comp_continuousOn ccurv)))).add
      ((Complex.continuous_ofReal.comp_continuousOn clg).mul cem)
  apply hcont.congr
  intro p hp
  dsimp only [Function.uncurry, weightedJSource]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem ac_weighted_density_of_sections
    {l r : ℝ → ℝ} {y Z : ℝ → ℂ} {a b : ℝ}
    (hl : AbsolutelyContinuousOnInterval l a b)
    (hr : AbsolutelyContinuousOnInterval r a b)
    (hy : AbsolutelyContinuousOnInterval y a b)
    (hZ : AbsolutelyContinuousOnInterval Z a b)
    (hne : ∀ u ∈ uIcc a b, r u ≠ 0) :
    AbsolutelyContinuousOnInterval (fun u => (l u : ℂ) * Z u -
      (l u ^ 2 / r u : ℝ) * (‖y u‖ : ℂ) ^ 2 * y u) a b := by
  have hc : AbsolutelyContinuousOnInterval (fun u => l u ^ 2 / r u) a b := by
    simpa only [pow_two, Pi.mul_apply] using!
      Calculus.ac_div_of_ne_zero (hl.mul hl) hr hne
  have ht : AbsolutelyContinuousOnInterval (fun u => (‖y u‖ : ℂ) ^ 2 * y u) a b := by
    simpa only [Complex.conj_mul'] using ((ac_conj hy).mul_normed_ring hy).mul_normed_ring hy
  simpa only [Pi.sub_apply, Pi.mul_apply, mul_assoc] using!
    (hl.ofReal.mul_normed_ring hZ).sub (hc.ofReal.mul_normed_ring ht)

private theorem hasDerivAt_weighted_density_of_jets
    (e : ℝ) (S : Fields) (v u : ℝ) (Z : ℝ → ℂ)
    (hr : S.r u v ≠ 0) (hl : S.lam u v ≠ 0) (hn : S.nu u v ≠ 0)
    (hg : 1 - S.mu u v ≠ 0)
    (hrd : HasDerivAt (fun x => S.r x v) (S.nu u v) u)
    (hld : HasDerivAt (fun x => S.lam x v) (S.rUV u v) u)
    (hyd : HasDerivAt (fun x => S.theta x v / S.lam x v)
      ((-(S.nu u v : ℂ) / S.r u v) *
        (S.xi u v / S.nu u v +
          ((S.mu u v : ℂ) - S.Q u v ^ 2 / (S.r u v : ℂ) ^ 2) /
            (1 - S.mu u v) * (S.theta u v / S.lam u v) +
          I * e * S.Q u v * S.phi u v / (1 - S.mu u v)) -
        I * e * S.A u v * (S.theta u v / S.lam u v)) u)
    (hZd : HasDerivAt Z
      (((-S.nu u v / ((1 - S.mu u v) * S.r u v) *
        (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) : ℝ) - I * e * S.A u v) * Z u +
        rawDensitySource e S u v) u) :
    let W := fun x => (S.lam x v : ℂ) * Z x - (S.lam x v ^ 2 / S.r x v : ℝ) *
      (‖S.theta x v / S.lam x v‖ : ℂ) ^ 2 * (S.theta x v / S.lam x v)
    HasDerivAt W (weightedJSource e S u v - I * e * S.A u v * W u) u := by
  have dc : HasDerivAt (fun x => S.lam x v ^ 2 / S.r x v)
      ((2 * S.lam u v * S.rUV u v * S.r u v - S.lam u v ^ 2 * S.nu u v) /
        S.r u v ^ 2) u := by
    simpa only [Pi.pow_apply, Pi.div_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat] using!
      (hld.pow 2).div hrd hr
  have hd := (hld.ofReal_comp.mul hZd).sub (dc.ofReal_comp.mul (hasDerivAt_cubic hyd))
  simp only [Pi.mul_def, Pi.sub_def] at hd
  convert hd using 1
  · funext x
    ring
  · have halg := weighted_remainder_evaluation e S u v (Z u) hr hl hn hg
    dsimp only at halg
    linear_combination -1 * halg

/-- [node lem:ct-renormalized#weak-AC-transfer]
Renormalizing the transported density produces an incoming AC function on
*every* fixed label, with the precise weighted covariant source. It agrees
with the raw frozen derivative on the common good-label set proved below. -/
theorem weighted_density_section (hS : IsSolution e S D) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D ∩ {p | p.1 < p.2}) :
    ∀ v ∈ Icc c d,
      let W := fun u => (S.lam u v : ℂ) * densityRepresentative e S a u v -
        (S.lam u v ^ 2 / S.r u v : ℝ) *
          (‖S.theta u v / S.lam u v‖ : ℂ) ^ 2 * (S.theta u v / S.lam u v)
      AbsolutelyContinuousOnInterval W a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt W
        (weightedJSource e S u v - I * e * S.A u v * W u) u := by
  have hbc : b < c := (hrect (show (b, c) ∈ Icc a b ×ˢ Icc c d from
    ⟨⟨hab.le, le_rfl⟩, ⟨le_rfl, hcd.le⟩⟩)).2
  intro v hv
  have hs : inSeg a b v ⊆ D := by
    rintro ⟨x, y⟩ ⟨hx, hxb, rfl⟩
    exact (hrect ⟨⟨hx, hxb⟩, hv⟩).1
  have h := Local.IsSolution.in_section hS hab.le (hbc.trans_le hv.1) hs
  have hy := incoming_ratio_section hS hab.le (hbc.trans_le hv.1) hs
  have hZ := Calculus.weak_outgoing_density_transport hS hab hcd hrect v hv
  have hr (u : ℝ) (hu : u ∈ Icc a b) :=
    (hS.r_pos (u, v) (hs ⟨hu.1, hu.2, rfl⟩) (hu.2.trans_lt (hbc.trans_le hv.1))).ne'
  refine ⟨ac_weighted_density_of_sections h.2.1.1 h.1.1 hy.1 hZ.1
    (fun u hu => hr u (by simpa [uIcc_of_le hab.le] using hu)), ?_⟩
  filter_upwards [h.1.2, h.2.1.2, hy.2, hZ.2, ae_restrict_mem measurableSet_Icc]
    with u hru hlu hyu hZu hu
  have hp : (u, v) ∈ D := hs ⟨hu.1, hu.2, rfl⟩
  exact hasDerivAt_weighted_density_of_jets e S v u (fun x => densityRepresentative e S a x v)
    (hr u hu) (hS.lam_pos (u, v) hp).ne' (hS.nu_neg (u, v) hp).ne
    (hS.one_sub_mu_pos (u, v) hp).ne' hru hlu hyu hZu

/-- [internal] The renormalized fixed density starts with exactly the frozen
weighted derivative. Its initial value is fixed, including at bad labels. -/
theorem weighted_density_initial (e : ℝ) (S : Fields) (a v : ℝ)
    (hl : S.lam a v ≠ 0) (hg : 1 - S.mu a v ≠ 0) :
    (S.lam a v : ℂ) * densityRepresentative e S a a v -
      (S.lam a v ^ 2 / S.r a v : ℝ) *
        (‖S.theta a v / S.lam a v‖ : ℂ) ^ 2 * (S.theta a v / S.lam a v) =
      weightedJ S a v := by
  simp only [densityRepresentative, intervalIntegral.integral_same, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, mul_one, add_zero, div_self hl, Complex.ofReal_one, one_mul]
  unfold weightedJ jOut
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hl,
    show 1 - (S.mu a v : ℂ) ≠ 0 from by exact_mod_cast hg]

/-- [internal] Variation of constants identifies the renormalized density
with the adopted unitary representative at every point, including endpoints
and exceptional labels. No choice of a derivative representative is made. -/
theorem weighted_density_eq_representative (hS : IsSolution e S D) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D ∩ {p | p.1 < p.2}) :
    ∀ u ∈ Icc a b, ∀ v ∈ Icc c d,
      (S.lam u v : ℂ) * densityRepresentative e S a u v -
        (S.lam u v ^ 2 / S.r u v : ℝ) *
          (‖S.theta u v / S.lam u v‖ : ℂ) ^ 2 * (S.theta u v / S.lam u v) =
        weightedJRepresentative e S a u v := by
  intro u hu v hv
  have hs : inSeg a b v ⊆ D := by
    rintro ⟨x, y⟩ ⟨hx, hxb, rfl⟩
    exact (hrect ⟨⟨hx, hxb⟩, hv⟩).1
  have hA : IntervalIntegrable (fun x => S.A x v) volume a b :=
    (Calculus.continuousOn_in_section hS.cont_A hs).intervalIntegrable_of_Icc hab.le
  have hF := (continuousOn_weightedJSource hS hrect).comp
    (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx, hv⟩)
  have hsec := weighted_density_section hS hab hcd hrect v hv
  have hcoeff : IntervalIntegrable (fun x => -I * e * (S.A x v : ℂ)) volume a b :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      (Calculus.continuousOn_in_section hS.cont_A hs))).intervalIntegrable_of_Icc hab.le
  have heq := eq_integratingFactor_of_ac_deriv_eq_complex hab.le hsec.1
    hcoeff (hF.intervalIntegrable_of_Icc hab.le) (by
      filter_upwards [hsec.2] with x hx
      rw [hx.deriv]
      dsimp only [Function.comp_apply, Function.uncurry, id_eq]
      ring) u hu
  rw [weighted_density_initial e S a v
    (hS.lam_pos (a, v) (hs ⟨le_rfl, hab.le, rfl⟩)).ne'
    (hS.one_sub_mu_pos (a, v) (hs ⟨le_rfl, hab.le, rfl⟩)).ne'] at heq
  rw [heq]
  unfold weightedJRepresentative
  simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  rw [mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs'
  rw [uIcc_of_le hu.1] at hs'
  dsimp only [Function.comp_apply, Function.uncurry, id_eq]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  have hi := intervalIntegral.integral_interval_sub_left
    (hA.mono_set (uIcc_subset_uIcc left_mem_uIcc (by simpa [uIcc_of_le hab.le] using hu)))
    (hA.mono_set (by
      rw [uIcc_of_le hs'.1, uIcc_of_le hab.le]
      exact Icc_subset_Icc le_rfl (hs'.2.trans hu.2)))
  have hiC := congrArg (fun x : ℝ => (x : ℂ)) hi
  push_cast at hiC
  linear_combination (-I * e) * hiC

/-- [node eq:ct-weighted-j]
The selected weighted derivative is incoming AC on every label and obeys
exactly the source equation, as an ordinary derivative plus the connection.
The source contains only undifferentiated fields and the frozen `QV`. -/
theorem weighted_section (hS : IsSolution e S D) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D ∩ {p | p.1 < p.2}) :
    ∀ v ∈ Icc c d,
      AbsolutelyContinuousOnInterval (fun u => weightedJRepresentative e S a u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt
        (fun x => weightedJRepresentative e S a x v)
        (weightedJSource e S u v - I * e * S.A u v * weightedJRepresentative e S a u v) u := by
  have heq := weighted_density_eq_representative hS hab hcd hrect
  intro v hv
  have h := weighted_density_section hS hab hcd hrect v hv
  refine ⟨h.1.congr (fun u hu => heq u (by simpa [uIcc_of_le hab.le] using hu) v hv), ?_⟩
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [(h.2).filter_mono (ae_mono (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)),
    ae_restrict_mem measurableSet_Ioo] with u hu hum
  have hd := hu.congr_of_eventuallyEq (by
    filter_upwards [Ioo_mem_nhds hum.1 hum.2] with x hx
    exact (heq x (Ioo_subset_Icc_self hx) v hv).symm)
  rw [heq u (Ioo_subset_Icc_self hum) v hv] at hd
  exact hd

end EmcsfAcExtension.Global.Renormalized

namespace EmcsfAcExtension.Global.Calculus

/-- [node lem:ct-renormalized#weak-AC-transfer]
The adopted weighted representation on one common full-measure set of
labels, before quantifying over every incoming time. This is the exact
Root A architecture template on the original frozen AC development. -/
theorem weighted_representation (ui e : ℝ) (S : Fields)
    (h : OriginalData ui e S) (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ origDomain ui ∩ {p | p.1 < p.2}) :
    ∀ᵐ v ∂volume.restrict (Icc c d), ∀ u ∈ Icc a b,
      weightedJ S u v = weightedJRepresentative e S a u v := by
  have heq := Renormalized.weighted_density_eq_representative h.solution hab hcd hrect
  filter_upwards [fixed_density_representation ui e S h a b c d hab hcd hrect,
    ae_restrict_mem measurableSet_Icc] with v hv hvm u hu
  rw [← heq u hu v hvm, ← (hv u hu).deriv]
  unfold weightedJ jOut
  have hl := (h.solution.lam_pos (u, v) (hrect ⟨hu, hvm⟩).1).ne'
  have hg := (h.solution.one_sub_mu_pos (u, v) (hrect ⟨hu, hvm⟩).1).ne'
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hl,
    show 1 - (S.mu u v : ℂ) ≠ 0 from by exact_mod_cast hg]

end EmcsfAcExtension.Global.Calculus

namespace EmcsfAcExtension.Global

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [node eq:ct-weighted-j]
Canonical graph export of the exact weighted incoming AC equation. The
selected representative has the fixed frozen initial value and agrees with
the raw derivative on the common label set. -/
theorem ct_weighted_j (hS : IsSolution e S D) {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hrect : Icc a b ×ˢ Icc c d ⊆ D ∩ {p | p.1 < p.2}) :
    ∀ v ∈ Icc c d,
      AbsolutelyContinuousOnInterval (fun u => weightedJRepresentative e S a u v) a b ∧
      ∀ᵐ u ∂volume.restrict (Icc a b), HasDerivAt
        (fun x => weightedJRepresentative e S a x v)
        (weightedJSource e S u v - I * e * S.A u v * weightedJRepresentative e S a u v) u :=
  Renormalized.weighted_section hS hab hcd hrect

end EmcsfAcExtension.Global
