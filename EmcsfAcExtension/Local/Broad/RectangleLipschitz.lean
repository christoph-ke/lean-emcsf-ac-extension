module

public import EmcsfAcExtension.Local.Broad.RectangleState

/-! # Local Lipschitz continuity of the full reduced source

The frozen source is smooth on the convex region `r>0`, `λ>0`, `r-2m>0`.
Compact convex subsets therefore have a common finite Lipschitz bound.
-/

public section

open Set Complex
open scoped NNReal

namespace EmcsfAcExtension.Local.Broad

private theorem rectangle_contDiffAt_div {f g : RectangleState → ℂ} {z : RectangleState}
    (hf : ContDiffAt ℝ 1 f z) (hg : ContDiffAt ℝ 1 g z) (hne : g z ≠ 0) :
    ContDiffAt ℝ 1 (fun x => f x / g x) z := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.fun_inv hne)

private theorem rectangle_source_regularities (e : ℝ) {z : RectangleState}
    (hz : z ∈ rectangle_state_region) :
    ContDiffAt ℝ 1 (fun x => (rectangle_in_source e x, rectangle_out_source e x)) z := by
  have hr : z.2.1 ≠ 0 := hz.1.ne'
  have hl : z.1.1 ≠ 0 := hz.2.1.ne'
  have hg : 1 - 2 * z.2.2.2.1 / z.2.1 ≠ 0 := by
    have heq : 1 - 2 * z.2.2.2.1 / z.2.1 = (z.2.1 - 2 * z.2.2.2.1) / z.2.1 := by
      field_simp [hr]
    rw [heq]
    exact (div_pos hz.2.2 hz.1).ne'
  have hrC : (z.2.1 : ℂ) ≠ 0 := by exact_mod_cast hr
  have hgC : 1 - ((2 * z.2.2.2.1 / z.2.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hg
  have cr : ContDiffAt ℝ 1 (fun x : RectangleState => x.2.1) z := by fun_prop
  have cl : ContDiffAt ℝ 1 (fun x : RectangleState => x.1.1) z := by fun_prop
  have cn : ContDiffAt ℝ 1 (fun x : RectangleState => x.2.2.1) z := by fun_prop
  have cm : ContDiffAt ℝ 1 (fun x : RectangleState => x.2.2.2.1) z := by fun_prop
  have cq : ContDiffAt ℝ 1 (fun x : RectangleState => x.2.2.2.2.1) z := by fun_prop
  have ca : ContDiffAt ℝ 1 (fun x : RectangleState => x.2.2.2.2.2.1) z := by fun_prop
  have cφ : ContDiffAt ℝ 1 (fun x : RectangleState => x.2.2.2.2.2.2.1) z := by fun_prop
  have cθ : ContDiffAt ℝ 1 (fun x : RectangleState => x.1.2) z := by fun_prop
  have cξ : ContDiffAt ℝ 1 (fun x : RectangleState => x.2.2.2.2.2.2.2) z := by fun_prop
  have cμ : ContDiffAt ℝ 1 (fun x : RectangleState => 2 * x.2.2.2.1 / x.2.1) z :=
    (contDiffAt_const.mul cm).div cr hr
  have cgap : ContDiffAt ℝ 1 (fun x : RectangleState => 1 - 2 * x.2.2.2.1 / x.2.1) z :=
    contDiffAt_const.sub cμ
  have cast {f : RectangleState → ℝ} (hf : ContDiffAt ℝ 1 f z) :
      ContDiffAt ℝ 1 (fun x => (f x : ℂ)) z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  have crC := cast cr
  have clC := cast cl
  have cnC := cast cn
  have cqC := cast cq
  have caC := cast ca
  have cμC := cast cμ
  have ce : ContDiffAt ℝ 1 (fun _ : RectangleState => I * (e : ℂ)) z := contDiffAt_const
  have cw_num : ContDiffAt ℝ 1 (fun x : RectangleState =>
      I * e * (x.2.2.2.2.1 : ℂ) * x.2.2.2.2.2.2.1 * x.2.2.1 * x.1.1) z :=
    (((ce.mul cqC).mul cφ).mul cnC).mul clC
  have cw_den : ContDiffAt ℝ 1 (fun x : RectangleState =>
      (1 - ((2 * x.2.2.2.1 / x.2.1 : ℝ) : ℂ)) * x.2.1) z :=
    (contDiffAt_const.sub cμC).mul crC
  have cw : ContDiffAt ℝ 1 (fun x : RectangleState =>
      I * e * (x.2.2.2.2.1 : ℂ) * x.2.2.2.2.2.2.1 * x.2.2.1 * x.1.1 /
        ((1 - ((2 * x.2.2.2.1 / x.2.1 : ℝ) : ℂ)) * x.2.1)) z :=
    rectangle_contDiffAt_div cw_num cw_den (mul_ne_zero hgC hrC)
  have crv : ContDiffAt ℝ 1 (fun x : RectangleState =>
      x.2.2.1 * x.1.1 / x.2.1 *
        ((2 * x.2.2.2.1 / x.2.1 - x.2.2.2.2.1 ^ 2 / x.2.1 ^ 2) /
          (1 - 2 * x.2.2.2.1 / x.2.1))) z :=
    ((cn.mul cl).div cr hr).mul
      ((cμ.sub ((cq.pow 2).div (cr.pow 2) (pow_ne_zero 2 hr))).div cgap hg)
  have cθu : ContDiffAt ℝ 1 (fun x : RectangleState =>
      -(I * e * (x.2.2.2.2.2.1 : ℂ) * x.1.2) -
        (x.1.1 : ℂ) * x.2.2.2.2.2.2.2 / x.2.1 -
      I * e * (x.2.2.2.2.1 : ℂ) * x.2.2.2.2.2.2.1 * x.2.2.1 * x.1.1 /
        ((1 - ((2 * x.2.2.2.1 / x.2.1 : ℝ) : ℂ)) * x.2.1)) z :=
    (((ce.mul caC).mul cθ).neg.sub
      (rectangle_contDiffAt_div (clC.mul cξ) crC hrC)).sub cw
  have cθsq : ContDiffAt ℝ 1 (fun x : RectangleState => ‖x.1.2‖ ^ 2) z := by
    simp_rw [Complex.sq_norm, Complex.normSq_apply]
    have cre := Complex.reCLM.contDiff.contDiffAt.comp z cθ
    have cim := Complex.imCLM.contDiff.contDiffAt.comp z cθ
    exact (cre.mul cre).add (cim.mul cim)
  have cmv : ContDiffAt ℝ 1 (fun x : RectangleState =>
      (1 - 2 * x.2.2.2.1 / x.2.1) * ‖x.1.2‖ ^ 2 / (2 * x.1.1) +
        x.2.2.2.2.1 ^ 2 * x.1.1 / (2 * x.2.1 ^ 2)) z :=
    ((cgap.mul cθsq).div (contDiffAt_const.mul cl) (mul_ne_zero (by norm_num) hl)).add
      (((cq.pow 2).mul cl).div (contDiffAt_const.mul (cr.pow 2))
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)))
  have cconj := Complex.conjCLE.contDiff.contDiffAt.comp z cφ
  have cim := Complex.imCLM.contDiff.contDiffAt.comp z (cconj.mul cθ)
  have cqv : ContDiffAt ℝ 1 (fun x : RectangleState =>
      -(e * x.2.1 * (starRingEnd ℂ (x.2.2.2.2.2.2.1) * x.1.2).im)) z :=
    ((contDiffAt_const.mul cr).mul cim).neg
  have cav : ContDiffAt ℝ 1 (fun x : RectangleState =>
      2 * x.2.2.1 * x.1.1 * x.2.2.2.2.1 /
        ((1 - 2 * x.2.2.2.1 / x.2.1) * x.2.1 ^ 2)) z :=
    (((contDiffAt_const.mul cn).mul cl).mul cq).div
      (cgap.mul (cr.pow 2)) (mul_ne_zero hg (pow_ne_zero 2 hr))
  have cφv : ContDiffAt ℝ 1 (fun x : RectangleState => x.1.2 / (x.2.1 : ℂ)) z :=
    rectangle_contDiffAt_div cθ crC hrC
  have cξv : ContDiffAt ℝ 1 (fun x : RectangleState =>
      -((x.2.2.1 : ℂ) * x.1.2 / x.2.1) +
      I * e * (x.2.2.2.2.1 : ℂ) * x.2.2.2.2.2.2.1 * x.2.2.1 * x.1.1 /
        ((1 - ((2 * x.2.2.2.1 / x.2.1 : ℝ) : ℂ)) * x.2.1)) z :=
    (rectangle_contDiffAt_div (cnC.mul cθ) crC hrC).neg.add cw
  unfold rectangle_in_source rectangle_out_source
  dsimp [rectangle_constant_fields, Fields.rUV, Fields.thetaU, Fields.mV, Fields.QV,
    Fields.AV, Fields.phiV, Fields.xiV, Fields.waveSource, Fields.mu]
  exact (crv.prodMk cθu).prodMk
    (cl.prodMk (crv.prodMk (cmv.prodMk (cqv.prodMk (cav.prodMk (cφv.prodMk cξv))))))

/-- The full incoming source is continuously differentiable away from
its actual geometric poles. The coupling is an arbitrary fixed real. -/
theorem contDiffAt_rectangle_in_source (e : ℝ) {z : RectangleState}
    (hz : z ∈ rectangle_state_region) : ContDiffAt ℝ 1 (rectangle_in_source e) z :=
  (rectangle_source_regularities e hz).fst

/-- The outgoing source includes the mass, charge and potential equations
and is continuously differentiable on the same positive state region. -/
theorem contDiffAt_rectangle_out_source (e : ℝ) {z : RectangleState}
    (hz : z ∈ rectangle_state_region) : ContDiffAt ℝ 1 (rectangle_out_source e) z :=
  (rectangle_source_regularities e hz).snd

/-- On a fixed compact convex state set inside the positive region, a
positive common Lipschitz coefficient bounds both source blocks. It may
depend on the coupling and that state set, before any trace comparison. -/
theorem rectangle_sources_lipschitz (e : ℝ) {K : Set RectangleState}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hregion : K ⊆ rectangle_state_region) :
    ∃ L : ℝ≥0, 0 < L ∧ LipschitzOnWith L (rectangle_in_source e) K ∧
      LipschitzOnWith L (rectangle_out_source e) K := by
  have hi : ContDiffOn ℝ 1 (rectangle_in_source e) K :=
    fun z hz => (contDiffAt_rectangle_in_source e (hregion hz)).contDiffWithinAt
  have ho : ContDiffOn ℝ 1 (rectangle_out_source e) K :=
    fun z hz => (contDiffAt_rectangle_out_source e (hregion hz)).contDiffWithinAt
  obtain ⟨Li, hLi⟩ := hi.exists_lipschitzOnWith (by norm_num) hconv hK
  obtain ⟨Lo, hLo⟩ := ho.exists_lipschitzOnWith (by norm_num) hconv hK
  refine ⟨max Li Lo + 1, by positivity, hLi.weaken ?_, hLo.weaken ?_⟩
  · exact (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  · exact (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)

end EmcsfAcExtension.Local.Broad
