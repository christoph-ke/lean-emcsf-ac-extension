module

public import EmcsfAcExtension.Local.Broad.RectangleState
import EmcsfAcExtension.Local.Broad.RectangleLipschitz

/-! # Two state derivatives of the genuine characteristic sources

All differentiability is with respect to the full finite-dimensional
state. Compact convex subsets of the positive-radius state region have
uniform first-derivative size and Lipschitz bounds, before traces or old
apex positions are chosen. This is the state-derivative input to the
positive-radius first-jet comparison in internal project record L1055–L1072.
-/

public section

open Set Complex
open scoped NNReal

namespace EmcsfAcExtension.Local.Broad

/-- The nondegenerate source region is open in the full state space,
so compact source containers have smooth cutoff neighborhoods. -/
theorem isOpen_rectangle_state_region : IsOpen rectangle_state_region := by
  have hr : Continuous (fun z : RectangleState => z.2.1) := by fun_prop
  have hl : Continuous (fun z : RectangleState => z.1.1) := by fun_prop
  have hg : Continuous (fun z : RectangleState => z.2.1-2*z.2.2.2.1) := by fun_prop
  exact (isOpen_lt continuous_const hr).inter
    ((isOpen_lt continuous_const hl).inter (isOpen_lt continuous_const hg))

private theorem strip_contDiffAt_div_two {f g : RectangleState → ℂ} {z : RectangleState}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) (hne : g z ≠ 0) :
    ContDiffAt ℝ 2 (fun x => f x / g x) z := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.fun_inv hne)

private theorem strip_source_regularities_two (e : ℝ) {z : RectangleState}
    (hz : z ∈ rectangle_state_region) :
    ContDiffAt ℝ 2 (fun x => (rectangle_in_source e x, rectangle_out_source e x)) z := by
  have hr : z.2.1 ≠ 0 := hz.1.ne'
  have hl : z.1.1 ≠ 0 := hz.2.1.ne'
  have hg : 1 - 2 * z.2.2.2.1 / z.2.1 ≠ 0 := by
    have heq : 1 - 2 * z.2.2.2.1 / z.2.1 = (z.2.1 - 2 * z.2.2.2.1) / z.2.1 := by
      field_simp [hr]
    rw [heq]
    exact (div_pos hz.2.2 hz.1).ne'
  have hrC : (z.2.1 : ℂ) ≠ 0 := by exact_mod_cast hr
  have hgC : 1 - ((2 * z.2.2.2.1 / z.2.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hg
  have cr : ContDiffAt ℝ 2 (fun x : RectangleState => x.2.1) z := by fun_prop
  have cl : ContDiffAt ℝ 2 (fun x : RectangleState => x.1.1) z := by fun_prop
  have cn : ContDiffAt ℝ 2 (fun x : RectangleState => x.2.2.1) z := by fun_prop
  have cm : ContDiffAt ℝ 2 (fun x : RectangleState => x.2.2.2.1) z := by fun_prop
  have cq : ContDiffAt ℝ 2 (fun x : RectangleState => x.2.2.2.2.1) z := by fun_prop
  have ca : ContDiffAt ℝ 2 (fun x : RectangleState => x.2.2.2.2.2.1) z := by fun_prop
  have cφ : ContDiffAt ℝ 2 (fun x : RectangleState => x.2.2.2.2.2.2.1) z := by fun_prop
  have cθ : ContDiffAt ℝ 2 (fun x : RectangleState => x.1.2) z := by fun_prop
  have cξ : ContDiffAt ℝ 2 (fun x : RectangleState => x.2.2.2.2.2.2.2) z := by fun_prop
  have cμ : ContDiffAt ℝ 2 (fun x : RectangleState => 2 * x.2.2.2.1 / x.2.1) z :=
    (contDiffAt_const.mul cm).div cr hr
  have cgap : ContDiffAt ℝ 2 (fun x : RectangleState => 1 - 2 * x.2.2.2.1 / x.2.1) z :=
    contDiffAt_const.sub cμ
  have cast {f : RectangleState → ℝ} (hf : ContDiffAt ℝ 2 f z) :
      ContDiffAt ℝ 2 (fun x => (f x : ℂ)) z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  have crC := cast cr
  have clC := cast cl
  have cnC := cast cn
  have cqC := cast cq
  have caC := cast ca
  have cμC := cast cμ
  have ce : ContDiffAt ℝ 2 (fun _ : RectangleState => I * (e : ℂ)) z := contDiffAt_const
  have cw_num : ContDiffAt ℝ 2 (fun x : RectangleState =>
      I * e * (x.2.2.2.2.1 : ℂ) * x.2.2.2.2.2.2.1 * x.2.2.1 * x.1.1) z :=
    (((ce.mul cqC).mul cφ).mul cnC).mul clC
  have cw_den : ContDiffAt ℝ 2 (fun x : RectangleState =>
      (1 - ((2 * x.2.2.2.1 / x.2.1 : ℝ) : ℂ)) * x.2.1) z :=
    (contDiffAt_const.sub cμC).mul crC
  have cw : ContDiffAt ℝ 2 (fun x : RectangleState =>
      I * e * (x.2.2.2.2.1 : ℂ) * x.2.2.2.2.2.2.1 * x.2.2.1 * x.1.1 /
        ((1 - ((2 * x.2.2.2.1 / x.2.1 : ℝ) : ℂ)) * x.2.1)) z :=
    strip_contDiffAt_div_two cw_num cw_den (mul_ne_zero hgC hrC)
  have crv : ContDiffAt ℝ 2 (fun x : RectangleState =>
      x.2.2.1 * x.1.1 / x.2.1 *
        ((2 * x.2.2.2.1 / x.2.1 - x.2.2.2.2.1 ^ 2 / x.2.1 ^ 2) /
          (1 - 2 * x.2.2.2.1 / x.2.1))) z :=
    ((cn.mul cl).div cr hr).mul
      ((cμ.sub ((cq.pow 2).div (cr.pow 2) (pow_ne_zero 2 hr))).div cgap hg)
  have cθu : ContDiffAt ℝ 2 (fun x : RectangleState =>
      -(I * e * (x.2.2.2.2.2.1 : ℂ) * x.1.2) -
        (x.1.1 : ℂ) * x.2.2.2.2.2.2.2 / x.2.1 -
      I * e * (x.2.2.2.2.1 : ℂ) * x.2.2.2.2.2.2.1 * x.2.2.1 * x.1.1 /
        ((1 - ((2 * x.2.2.2.1 / x.2.1 : ℝ) : ℂ)) * x.2.1)) z :=
    (((ce.mul caC).mul cθ).neg.sub
      (strip_contDiffAt_div_two (clC.mul cξ) crC hrC)).sub cw
  have cθsq : ContDiffAt ℝ 2 (fun x : RectangleState => ‖x.1.2‖ ^ 2) z := by
    simp_rw [Complex.sq_norm, Complex.normSq_apply]
    have cre := Complex.reCLM.contDiff.contDiffAt.comp z cθ
    have cim := Complex.imCLM.contDiff.contDiffAt.comp z cθ
    exact (cre.mul cre).add (cim.mul cim)
  have cmv : ContDiffAt ℝ 2 (fun x : RectangleState =>
      (1 - 2 * x.2.2.2.1 / x.2.1) * ‖x.1.2‖ ^ 2 / (2 * x.1.1) +
        x.2.2.2.2.1 ^ 2 * x.1.1 / (2 * x.2.1 ^ 2)) z :=
    ((cgap.mul cθsq).div (contDiffAt_const.mul cl) (mul_ne_zero (by norm_num) hl)).add
      (((cq.pow 2).mul cl).div (contDiffAt_const.mul (cr.pow 2))
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)))
  have cconj := Complex.conjCLE.contDiff.contDiffAt.comp z cφ
  have cim := Complex.imCLM.contDiff.contDiffAt.comp z (cconj.mul cθ)
  have cqv : ContDiffAt ℝ 2 (fun x : RectangleState =>
      -(e * x.2.1 * (starRingEnd ℂ (x.2.2.2.2.2.2.1) * x.1.2).im)) z :=
    ((contDiffAt_const.mul cr).mul cim).neg
  have cav : ContDiffAt ℝ 2 (fun x : RectangleState =>
      2 * x.2.2.1 * x.1.1 * x.2.2.2.2.1 /
        ((1 - 2 * x.2.2.2.1 / x.2.1) * x.2.1 ^ 2)) z :=
    (((contDiffAt_const.mul cn).mul cl).mul cq).div
      (cgap.mul (cr.pow 2)) (mul_ne_zero hg (pow_ne_zero 2 hr))
  have cφv : ContDiffAt ℝ 2 (fun x : RectangleState => x.1.2 / (x.2.1 : ℂ)) z :=
    strip_contDiffAt_div_two cθ crC hrC
  have cξv : ContDiffAt ℝ 2 (fun x : RectangleState =>
      -((x.2.2.1 : ℂ) * x.1.2 / x.2.1) +
      I * e * (x.2.2.2.2.1 : ℂ) * x.2.2.2.2.2.2.1 * x.2.2.1 * x.1.1 /
        ((1 - ((2 * x.2.2.2.1 / x.2.1 : ℝ) : ℂ)) * x.2.1)) z :=
    (strip_contDiffAt_div_two (cnC.mul cθ) crC hrC).neg.add cw
  unfold rectangle_in_source rectangle_out_source
  dsimp [rectangle_constant_fields, Fields.rUV, Fields.thetaU, Fields.mV, Fields.QV,
    Fields.AV, Fields.phiV, Fields.xiV, Fields.waveSource, Fields.mu]
  exact (crv.prodMk cθu).prodMk
    (cl.prodMk (crv.prodMk (cmv.prodMk (cqv.prodMk (cav.prodMk (cφv.prodMk cξv))))))

/-- The literal incoming characteristic source has two continuous state
derivatives at every state in the nondegenerate region, for arbitrary coupling. -/
theorem contDiffAt_rectangle_in_source_two (e : ℝ) {z : RectangleState}
    (hz : z ∈ rectangle_state_region) : ContDiffAt ℝ 2 (rectangle_in_source e) z :=
  (strip_source_regularities_two e hz).fst

/-- The full outgoing characteristic source has two continuous state
derivatives on the same nondegenerate state region. -/
theorem contDiffAt_rectangle_out_source_two (e : ℝ) {z : RectangleState}
    (hz : z ∈ rectangle_state_region) : ContDiffAt ℝ 2 (rectangle_out_source e) z :=
  (strip_source_regularities_two e hz).snd

/-- On a fixed compact convex state container, both first state derivatives
have a common finite size and Lipschitz bound. `C` may depend only on the
coupling and container; it is chosen before any traces or apex coordinates. -/
theorem rectangle_source_derivative_bounds (e : ℝ) {K : Set RectangleState}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hregion : K ⊆ rectangle_state_region) :
    ∃ C > 0,
      (∀ z ∈ K, ‖fderiv ℝ (rectangle_in_source e) z‖ ≤ C ∧
        ‖fderiv ℝ (rectangle_out_source e) z‖ ≤ C) ∧
      (∀ x ∈ K, ∀ y ∈ K,
        ‖fderiv ℝ (rectangle_in_source e) x - fderiv ℝ (rectangle_in_source e) y‖ ≤ C*‖x-y‖ ∧
        ‖fderiv ℝ (rectangle_out_source e) x - fderiv ℝ (rectangle_out_source e) y‖ ≤ C*‖x-y‖) := by
  have hi : ContDiffOn ℝ 1 (fderiv ℝ (rectangle_in_source e)) K := fun z hz =>
    ((contDiffAt_rectangle_in_source_two e (hregion hz)).fderiv_right
        (by norm_num)).contDiffWithinAt
  have ho : ContDiffOn ℝ 1 (fderiv ℝ (rectangle_out_source e)) K := fun z hz =>
    ((contDiffAt_rectangle_out_source_two e (hregion hz)).fderiv_right
        (by norm_num)).contDiffWithinAt
  obtain ⟨Li,hLi⟩ := hi.exists_lipschitzOnWith (by norm_num) hconv hK
  obtain ⟨Lo,hLo⟩ := ho.exists_lipschitzOnWith (by norm_num) hconv hK
  obtain ⟨Hi,hHi⟩ := hK.bddAbove_image hi.continuousOn.norm
  obtain ⟨Ho,hHo⟩ := hK.bddAbove_image ho.continuousOn.norm
  let C := 1+|Hi|+|Ho|+(Li : ℝ)+(Lo : ℝ)
  have hC : 0 < C := by dsimp [C]; positivity
  have hHiC : Hi ≤ C := by
    have := le_abs_self Hi
    have := abs_nonneg Ho
    have := Li.coe_nonneg
    have := Lo.coe_nonneg
    dsimp [C]
    linarith
  have hHoC : Ho ≤ C := by
    have := le_abs_self Ho
    have := abs_nonneg Hi
    have := Li.coe_nonneg
    have := Lo.coe_nonneg
    dsimp [C]
    linarith
  have hLiC : (Li : ℝ) ≤ C := by
    have := abs_nonneg Hi
    have := abs_nonneg Ho
    have := Lo.coe_nonneg
    dsimp [C]
    linarith
  have hLoC : (Lo : ℝ) ≤ C := by
    have := abs_nonneg Hi
    have := abs_nonneg Ho
    have := Li.coe_nonneg
    dsimp [C]
    linarith
  refine ⟨C,hC,?_,?_⟩
  · intro z hz
    exact ⟨(hHi (mem_image_of_mem _ hz)).trans hHiC,
      (hHo (mem_image_of_mem _ hz)).trans hHoC⟩
  · intro x hx y hy
    have hi' : ‖fderiv ℝ (rectangle_in_source e) x - fderiv ℝ (rectangle_in_source e) y‖ ≤
        (Li : ℝ)*‖x-y‖ := by simpa only [dist_eq_norm] using hLi.dist_le_mul x hx y hy
    have ho' : ‖fderiv ℝ (rectangle_out_source e) x - fderiv ℝ (rectangle_out_source e) y‖ ≤
        (Lo : ℝ)*‖x-y‖ := by simpa only [dist_eq_norm] using hLo.dist_le_mul x hx y hy
    exact ⟨hi'.trans (mul_le_mul_of_nonneg_right hLiC (norm_nonneg _)),
      ho'.trans (mul_le_mul_of_nonneg_right hLoC (norm_nonneg _))⟩

end EmcsfAcExtension.Local.Broad
