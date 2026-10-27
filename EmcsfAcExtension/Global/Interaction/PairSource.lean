/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Global.Defs.Renormalized
public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Global.Interaction.RadialZ
public import EmcsfAcExtension.Global.Interaction.Curvature
import EmcsfAcExtension.Global.Calculus.Endpoint
import EmcsfAcExtension.Global.Renormalized.Curvature
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Infra.Level.Substitution
import EmcsfAcExtension.Infra.Level.Clock
import Mathlib.Tactic

/-!
# Radial source measure and its label envelope

The source density at `charged_SF_new_version.tex:L3627–L3633` is pulled back by the
actual outgoing radius map. Its inverse is used only on the image of the
closed row. The Jacobian is the frozen expansion `λ`; the majorant is used
almost everywhere on labels, without differentiating it.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
On a proper closed outgoing segment the radius has within derivative `λ`
and is strictly increasing. This follows from the frozen radius equation
on every subsegment and positivity of the outgoing expansion. -/
theorem outgoing_radius_calculus {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u ≤ a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) :
    (∀ v ∈ Icc a b, HasDerivWithinAt (S.r u) (S.lam u v) (Icc a b) v) ∧
      StrictMonoOn (S.r u) (Icc a b) := by
  have hc := Calculus.continuousOn_out_section hS.cont_lam hs
  have hd : ∀ v ∈ Icc a b,
      HasDerivWithinAt (S.r u) (S.lam u v) (Icc a b) v := by
    intro v hv
    have hform (x : ℝ) (hx : x ∈ Icc a b) :=
      (Calculus.out_integralForm hS hua hx.1
        (fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩)).1
    have hder := (Level.hasDerivWithinAt_integralClock hab hc hv).const_add (S.r u a)
    apply hder.congr_of_mem _ hv
    intro x hx
    exact (hform x hx).eq_add_integral
  refine ⟨hd, strictMonoOn_of_hasDerivWithinAt_pos (f' := S.lam u) (convex_Icc a b)
    (Calculus.continuousOn_out_section hS.cont_r hs) ?_ ?_⟩
  · intro v hv
    exact (hd v (interior_subset hv)).mono interior_subset
  · intro v hv
    have hv' := interior_subset hv
    exact hS.lam_pos (u, v) (hs ⟨rfl, hv'.1, hv'.2⟩)

private theorem source_density_algebra {c lam G : ℝ} {W : ℂ}
    (hc : 0 < c) (hlam : c ≤ lam) (hW : ‖W‖ ≤ G) :
    lam * (‖W‖ / lam ^ 2) = ‖W‖ / lam ∧ ‖W‖ / lam ≤ c⁻¹ * G := by
  have hlamp := hc.trans_le hlam
  constructor
  · field_simp
  · calc
      _ ≤ G / lam := div_le_div_of_nonneg_right hW hlamp.le
      _ ≤ G / c := div_le_div_of_nonneg_left ((norm_nonneg W).trans hW) hc hlam
      _ = _ := div_eq_inv_mul _ _

private theorem source_measure_conversion_aux {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b c : ℝ} (hua : u ≤ a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (hc : 0 < c)
    (hlam : ∀ v ∈ Icc a b, c ≤ S.lam u v) {g : ℝ → ℝ} {W : ℝ → ℂ}
    (hg : ∀ᵐ v ∂volume.restrict (Icc a b), ‖W v‖ ≤ g v) :
    let ι := Function.invFunOn (S.r u) (Icc a b)
    (∫⁻ x in (S.r u) '' Icc a b,
        ENNReal.ofReal (‖W (ι x)‖ / S.lam u (ι x) ^ 2)) =
        ∫⁻ v in Icc a b, ENNReal.ofReal (‖W v‖ / S.lam u v) ∧
      (∫⁻ v in Icc a b, ENNReal.ofReal (‖W v‖ / S.lam u v)) ≤
        ENNReal.ofReal c⁻¹ * ∫⁻ v in Icc a b, ENNReal.ofReal (g v) := by
  dsimp only
  obtain ⟨hd, hm⟩ := outgoing_radius_calculus hS hua hab hs
  have hinv := hm.injOn.leftInvOn_invFunOn
  constructor
  · rw [Level.lintegral_image_mono measurableSet_Icc hd hm.monotoneOn]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro v hv
    dsimp only
    rw [hinv hv, ← ENNReal.ofReal_mul (hc.trans_le (hlam v hv)).le]
    congr 1
    field_simp
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hg, ae_restrict_mem measurableSet_Icc] with v hgv hv
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
    exact ENNReal.ofReal_le_ofReal (source_density_algebra hc (hlam v hv) hgv).2

/-- [node prop:ct-interaction#source-measure-conversion]
The actual outgoing-radius substitution converts the radial source measure
`λ⁻² |W| dr` to `λ⁻¹ |W| dv`, bounded by `c⁻¹ g(v) dv`.
The inverse radius is evaluated only on the row image. The coefficient
`c⁻¹` is explicit, uniform in the solution,
row, envelope and physical scales. Both integrals are extended nonnegative
integrals, so no finiteness is assumed before substitution.
Source: `charged_SF_new_version.tex:L3627–L3633`. This is a single outgoing row;
the frozen derivative is used only almost everywhere on that row. -/
theorem source_measure_conversion {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b c : ℝ} (hua : u ≤ a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (hc : 0 < c)
    (hlam : ∀ v ∈ Icc a b, c ≤ S.lam u v) {g : ℝ → ℝ}
    (hg : ∀ᵐ v ∂volume.restrict (Icc a b),
      ‖weightedJ S u v‖ ≤ g v) :
    let W := weightedJ S u
    let ι := Function.invFunOn (S.r u) (Icc a b)
    (∫⁻ x in (S.r u) '' Icc a b,
        ENNReal.ofReal (‖W (ι x)‖ / S.lam u (ι x) ^ 2)) =
        ∫⁻ v in Icc a b, ENNReal.ofReal (‖W v‖ / S.lam u v) ∧
      (∫⁻ v in Icc a b, ENNReal.ofReal (‖W v‖ / S.lam u v)) ≤
        ENNReal.ofReal c⁻¹ * ∫⁻ v in Icc a b, ENNReal.ofReal (g v) := by
  exact source_measure_conversion_aux hS hua hab hs hc hlam hg

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global

/-- [internal]
The bilinear scalar/curvature term in the weighted transport source, with
selected outgoing scalar and curvature summands. Linearity in the curvature
is over the reals because its conjugate is retained.
Source: charged_SF_new_version.tex:L3170–L3176 and internal project record `(Crep)`. -/
@[expose] noncomputable def curvatureScalarSource (S : Fields) (u v : ℝ)
    (Y C : ℂ) : ℂ :=
  (S.nu u v * S.lam u v ^ 2 / ((1 - S.mu u v) * S.r u v ^ 2) : ℝ) *
    Y * (C + 2 * starRingEnd ℂ C)

/-- [internal]
The curvature source primitive selecting an incoming scalar summand `z`.
With `z = ξ/ν` this is literally `radialCurvatureSource`; selecting the
three terms of `ct_z_split_identity` defines its boundary, pair, and mixed
electric pieces. Source: charged_SF_new_version.tex:L3414–L3425. -/
@[expose] noncomputable def radialCurvatureWith (S : Fields) (u a b : ℝ)
    (z : ℝ → ℂ) : ℂ :=
  (S.r u b : ℂ)⁻¹ * ∫ v in a..b,
    (((1 - S.mu u v) * S.r u v / S.lam u v : ℝ) : ℂ) *
      starRingEnd ℂ (z v) * weightedJ S u v

/-- [internal]
The full frozen weighted source is the scalar/curvature source plus the
explicit Maxwell remainder. This identifies the selected multiplier with
the unchanged architecture definition, rather than a new source equation. -/
theorem weightedJSource_eq_curvatureScalarSource (e : ℝ) (S : Fields) (u v : ℝ)
    (hl : S.lam u v ≠ 0) :
    weightedJSource e S u v =
      curvatureScalarSource S u v (S.theta u v / S.lam u v) (Local.curv S u v) +
        ((S.lam u v / (1 - S.mu u v) : ℝ) : ℂ) * Local.emSourceJ e S u v := by
  unfold weightedJSource curvatureScalarSource
  congr 1
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hl]

/-- [node eq:ct-C-reconstruction]
The annular curvature reconstruction with its transport input discharged
by internal project record. It holds at both endpoints in the frozen AC class and has no
additional transport premise or constants. Source: charged_SF_new_version.tex:L3414–L3425. -/
theorem ct_c_reconstruction {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) :
    Local.curv S u b = radialCurvatureBoundary S u a b +
      radialCurvatureSource S u a b + radialCurvatureEM e S u a b := by
  apply ct_c_reconstruction_of_transport hS hua hab hs
  convert Renormalized.curvature_out_integralForm hS hua hab hs using 1
  funext v
  ring

namespace InteractionEstimate

/-- [internal]
The selected incoming source primitive is continuous at all row endpoints.
Its rough outgoing density occurs only inside an integrable primitive. -/
theorem continuousOn_radialZSource_end {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) : ContinuousOn (radialZSource S u a) (Icc a b) := by
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cY := continuousOn_radialYSource_end hS hua hab hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : S.r u v ≠ 0 :=
    (hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
  have hn (v : ℝ) (hv : v ∈ Icc a b) : (S.nu u v : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hS.nu_neg (u, v) (hs ⟨rfl, hv⟩)).ne
  have ci := (Complex.continuous_ofReal.comp_continuousOn ((cn.mul cl).div cr hr)).mul cY
  have cp := intervalIntegral.continuousOn_primitive_interval'
    (ci.intervalIntegrable_of_Icc hab (μ := volume)) left_mem_uIcc
  have cp' : ContinuousOn (fun v => ∫ t in a..v,
      ((S.nu u t * S.lam u t / S.r u t : ℝ) : ℂ) * radialYSource S u a t)
      (Icc a b) := by simpa only [uIcc_of_le hab, Pi.mul_apply, Pi.div_apply, Function.comp_def]
        using! cp
  exact ((Complex.continuous_ofReal.comp_continuousOn cn).inv₀ hn).neg.mul cp'

/-- [internal]
Norm of an actual selected curvature primitive against the row envelope.
The coefficient is exactly `1/c`, uniform in the selected continuous
incoming piece, all solution data, and the row's radius and length. -/
theorem radial_curvature_with_le {e δ c Λ F ε : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (hstop : ExteriorStops S D δ c Λ F ε)
    {u a b : ℝ} (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (hc : 0 < c) (z : ℝ → ℂ) (hz : ContinuousOn z (Icc a b)) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume a b)
    (hmajor : ∀ᵐ v ∂volume.restrict (Icc a b), ‖weightedJ S u v‖ ≤ g v) :
    ‖radialCurvatureWith S u a b z‖ ≤
      (c * S.r u b)⁻¹ * (∫ v in a..b, S.r u v * ‖z v‖ * g v) := by
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v :=
    hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have cm : ContinuousOn (S.mu u) (Icc a b) := by
    simpa only [Fields.mu, Pi.mul_apply, Pi.div_apply] using!
      ((Calculus.continuousOn_out_section hS.cont_m hs).const_mul 2).div cr
        (fun v hv => (hr v hv).ne')
  have hgap (v : ℝ) (hv : v ∈ Icc a b) : 0 < 1 - S.mu u v :=
    hS.one_sub_mu_pos (u, v) (hs ⟨rfl, hv⟩)
  let k := fun v => (((1 - S.mu u v) * S.r u v : ℝ) : ℂ) * starRingEnd ℂ (z v)
  have ck : ContinuousOn k (Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn ((continuousOn_const.sub cm).mul cr)).mul hz.star
  have iw := Interaction.radial_y_source_integrable hS hua hab hs
  have ik := iw.continuousOn_mul (by simpa only [uIcc_of_le hab] using ck)
  have im : IntervalIntegrable (fun v => c⁻¹ * (S.r u v * ‖z v‖ * g v)) volume a b := by
    apply (hg.continuousOn_mul (by
      simpa only [uIcc_of_le hab] using (cr.mul hz.norm).const_mul c⁻¹)).congr
    intro v _
    change (c⁻¹ * (S.r u v * ‖z v‖)) * g v = c⁻¹ * (S.r u v * ‖z v‖ * g v)
    ring
  have hnorm : (∫ v in a..b, ‖k v * (weightedJ S u v / S.lam u v)‖) ≤
      c⁻¹ * (∫ v in a..b, S.r u v * ‖z v‖ * g v) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_ae_restrict hab ik.norm im
    filter_upwards [hmajor, ae_restrict_mem measurableSet_Icc] with v hgv hv
    have hq := (source_density_algebra hc (hstop (u, v) (hs ⟨rfl, hv⟩)).2.2.1 hgv).2
    have hh : 1 - S.mu u v ≤ 1 := by
      linarith only [(hstop (u, v) (hs ⟨rfl, hv⟩)).1]
    change ‖k v * (weightedJ S u v / S.lam u v)‖ ≤ _
    simp only [k, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_conj, abs_of_pos (hgap v hv), abs_of_pos (hr v hv),
      abs_of_pos (hl v hv)]
    calc
      _ ≤ (S.r u v * ‖z v‖) * (c⁻¹ * g v) := by
        apply mul_le_mul _ hq (div_nonneg (norm_nonneg _) (hl v hv).le)
          (mul_nonneg (hr v hv).le (norm_nonneg _))
        nlinarith only [mul_le_mul_of_nonneg_right hh
          (mul_nonneg (hr v hv).le (norm_nonneg (z v)))]
      _ = _ := by ring
  have heq : radialCurvatureWith S u a b z =
      (S.r u b : ℂ)⁻¹ * ∫ v in a..b, k v * (weightedJ S u v / S.lam u v) := by
    unfold radialCurvatureWith
    congr 1
    apply intervalIntegral.integral_congr
    intro v _
    dsimp [k]
    push_cast
    ring
  rw [heq, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hr b ⟨hab, le_rfl⟩)]
  calc
    _ ≤ (S.r u b)⁻¹ * (c⁻¹ * (∫ v in a..b, S.r u v * ‖z v‖ * g v)) :=
      mul_le_mul_of_nonneg_left
        ((intervalIntegral.norm_integral_le_integral_norm hab).trans hnorm)
        (inv_nonneg.mpr (hr b ⟨hab, le_rfl⟩).le)
    _ = _ := by ring

/-- [internal]
Universal norm estimate for a selected scalar/curvature source. Its exact
coefficient is `3 Λ² / δ`, uniform in all solution values and selected pieces.
Only the scalar summand's norm is bounded; its curvature phase is retained. -/
theorem curvature_scalar_source_le (S : Fields) (u v δ Λ F : ℝ) (Y C : ℂ)
    (hδ : 0 < δ) (hr : 0 < S.r u v) (hn : S.nu u v ≤ 0)
    (hl : 0 ≤ S.lam u v) (hΛ : S.lam u v ≤ Λ)
    (hgap : δ ≤ 1 - S.mu u v) (hY : ‖Y‖ ≤ F) :
    ‖curvatureScalarSource S u v Y C‖ ≤
      (3 * Λ ^ 2 * F / δ) * ((-S.nu u v) / S.r u v ^ 2) * ‖C‖ := by
  have hg := hδ.trans_le hgap
  have hn0 := neg_nonneg.mpr hn
  have hF0 := (norm_nonneg Y).trans hY
  have hΛ0 := hl.trans hΛ
  have hC : ‖C + 2 * starRingEnd ℂ C‖ ≤ 3 * ‖C‖ := by
    calc
      _ ≤ ‖C‖ + ‖2 * starRingEnd ℂ C‖ := norm_add_le _ _
      _ = _ := by simp only [norm_mul, Complex.norm_conj]; norm_num; ring
  have hsq : S.lam u v ^ 2 ≤ Λ ^ 2 :=
    (sq_le_sq₀ hl (hl.trans hΛ)).mpr hΛ
  have hcoef : 0 ≤ (-S.nu u v) * S.lam u v ^ 2 /
      ((1 - S.mu u v) * S.r u v ^ 2) := by positivity
  have hnorm : ‖curvatureScalarSource S u v Y C‖ =
      ((-S.nu u v) * S.lam u v ^ 2 / ((1 - S.mu u v) * S.r u v ^ 2)) *
        ‖Y‖ * ‖C + 2 * starRingEnd ℂ C‖ := by
    simp only [curvatureScalarSource, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_div, abs_mul, abs_pow, abs_of_nonpos hn, abs_of_nonneg hl,
      abs_of_pos hg, abs_of_pos hr]
  rw [hnorm]
  calc
    _ ≤ ((-S.nu u v) * Λ ^ 2 / (δ * S.r u v ^ 2)) * F * (3 * ‖C‖) := by
      apply mul_le_mul _ hC (norm_nonneg _)
        (mul_nonneg (by positivity) ((norm_nonneg Y).trans hY))
      apply mul_le_mul _ hY (norm_nonneg Y) (by positivity)
      apply div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hsq (neg_nonneg.mpr hn))
        (by positivity) (mul_le_mul_of_nonneg_right hgap (sq_nonneg _))
    _ = _ := by ring

/-- [node prop:ct-interaction#incoming-source-label-bound]
The incoming source summand retains label separation before integration.
The exact coefficient is `Λ / ((1-F²)c)`, chosen from the fixed stops and
uniform in the solution, row, envelope, and physical scales. The envelope
is used only almost everywhere on its outgoing row.
Source: charged_SF_new_version.tex:L3635–L3640. -/
theorem incoming_source_label_bound {e δ c Λ F ε : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (hstop : ExteriorStops S D δ c Λ F ε)
    {u a b : ℝ} (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (hc : 0 < c) (hF : 0 ≤ F) (hF1 : F < 1) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume a b)
    (hmajor : ∀ᵐ v ∂volume.restrict (Icc a b), ‖weightedJ S u v‖ ≤ g v) :
    S.r u b * ‖radialZSource S u a b‖ ≤
      Λ / ((1 - F ^ 2) * c) * (∫ t in a..b, (b - t) * g t) := by
  let p := 1 - F ^ 2
  have hp : 0 < p := by dsimp [p]; nlinarith only [hF, hF1, sq_nonneg (F - 1)]
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v :=
    hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have iq : IntervalIntegrable (fun v => ‖weightedJ S u v‖ / S.lam u v) volume a b := by
    apply (Interaction.radial_y_source_integrable hS hua hab hs).norm.congr
    intro v hv
    have hv : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hv
    change ‖weightedJ S u v / (S.lam u v : ℂ)‖ = _
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hl v hv)]
  have im := iq.continuousOn_mul (by
    simpa only [uIcc_of_le hab, Pi.sub_apply] using
      (continuousOn_const.sub cr : ContinuousOn (fun v => S.r u b - S.r u v) (Icc a b)))
  have ig := hg.continuousOn_mul (by fun_prop : ContinuousOn (fun t : ℝ => b - t) (uIcc a b))
  have hdiff (t : ℝ) (ht : t ∈ Icc a b) : S.r u b - S.r u t ≤ Λ * (b - t) := by
    have he := (hS.eq_out u t b (hua.trans_le ht.1) ht.2
      (fun z hz => hs ⟨hz.1, ht.1.trans hz.2.1, hz.2.2⟩)).1
    have hi := intervalIntegral.integral_mono_on ht.2 he.1
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Λ) volume t b)
      (fun v hv => (hstop (u, v) (hs ⟨rfl, ht.1.trans hv.1, hv.2⟩)).2.2.2.1)
    rw [intervalIntegral.integral_const, smul_eq_mul, ← he.2] at hi
    simpa only [mul_comm] using hi
  have hi : (∫ t in a..b, (S.r u b - S.r u t) *
      (‖weightedJ S u t‖ / S.lam u t)) ≤
      (Λ / c) * (∫ t in a..b, (b - t) * g t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_ae_restrict hab im (ig.const_mul (Λ / c))
    filter_upwards [hmajor, ae_restrict_mem measurableSet_Icc] with t hgt ht
    have hq := (source_density_algebra hc (hstop (u, t) (hs ⟨rfl, ht⟩)).2.2.1 hgt).2
    have hΛ : 0 ≤ Λ := (hl t ht).le.trans (hstop (u, t) (hs ⟨rfl, ht⟩)).2.2.2.1
    calc
      _ ≤ (Λ * (b - t)) * (c⁻¹ * g t) :=
        mul_le_mul (hdiff t ht) hq
          (div_nonneg (norm_nonneg _) (hl t ht).le) (mul_nonneg hΛ (sub_nonneg.mpr ht.2))
      _ = _ := by ring
  have hz := mul_le_mul_of_nonneg_left (ct_z_source hS hstop hua hab hs hF hF1)
    (hr b ⟨hab, le_rfl⟩).le
  have heq : S.r u b * (p⁻¹ * ∫ t in a..b,
      (S.r u b - S.r u t) / S.r u b * (‖weightedJ S u t‖ / S.lam u t)) =
      p⁻¹ * ∫ t in a..b, (S.r u b - S.r u t) *
        (‖weightedJ S u t‖ / S.lam u t) := by
    rw [mul_left_comm, ← intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    field_simp [(hr b ⟨hab, le_rfl⟩).ne']
  change S.r u b * ‖radialZSource S u a b‖ ≤ _ at hz
  rw [heq] at hz
  calc
    _ ≤ p⁻¹ * (∫ t in a..b, (S.r u b - S.r u t) *
        (‖weightedJ S u t‖ / S.lam u t)) := hz
    _ ≤ p⁻¹ * ((Λ / c) * (∫ t in a..b, (b - t) * g t)) :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hp.le)
    _ = _ := by dsimp [p]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- [internal]
The ordered separation primitive of an `L¹` label density is continuous
on its full closed interval; no square integrability is required. -/
theorem continuousOn_separation_primitive {a b : ℝ} (hab : a ≤ b)
    (g : ℝ → ℝ) (hg : IntervalIntegrable g volume a b) :
    ContinuousOn (fun s => ∫ t in a..s, (s - t) * g t) (Icc a b) := by
  have itg : IntervalIntegrable (fun t => t * g t) volume a b := by
    simpa only [id_eq] using! hg.continuousOn_mul
      (continuousOn_id : ContinuousOn (fun t : ℝ => t) (uIcc a b))
  have cG := intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
  have ctG := intervalIntegral.continuousOn_primitive_interval' itg left_mem_uIcc
  apply ((continuousOn_id.mul (by simpa only [uIcc_of_le hab] using cG)).sub
    (by simpa only [uIcc_of_le hab] using ctG)).congr
  intro s hs
  have hsub : uIcc a s ⊆ uIcc a b := by
    rw [uIcc_of_le hs.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hs.2
  dsimp only [Pi.sub_apply, Pi.mul_apply, id_eq]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
    ((hg.mono_set hsub).const_mul s) (itg.mono_set hsub)]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  ring

/-- [node prop:ct-interaction#pair-source-pointwise]
Pointwise weighted source of the actual curvature primitive selecting `zʲ`.
The exact coefficient `3FΛ³/(δ(1-F²)c²)` depends only on the fixed stops;
it is uniform in the solution, envelope, labels, and physical scales.
The ordered integral retains `(s-t)` and uses the envelope only a.e.
Source: charged_SF_new_version.tex:L3641–L3647; internal project record `(pair)`. -/
theorem pair_source_pointwise {e δ c Λ F ε : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (hstop : ExteriorStops S D δ c Λ F ε)
    {u a b : ℝ} (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (hδ : 0 < δ) (hc : 0 < c) (hF : 0 ≤ F) (hF1 : F < 1) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume a b)
    (hmajor : ∀ᵐ v ∂volume.restrict (Icc a b), ‖weightedJ S u v‖ ≤ g v) :
    ‖curvatureScalarSource S u b (S.theta u b / S.lam u b)
        (radialCurvatureWith S u a b (radialZSource S u a))‖ ≤
      (3 * F * Λ ^ 3 / (δ * (1 - F ^ 2) * c ^ 2)) *
        ((-S.nu u b) / S.r u b ^ 3) *
        (∫ s in a..b, (∫ t in a..s, (s - t) * g t) * g s) := by
  let p := 1 - F ^ 2
  let H := fun s => ∫ t in a..s, (s - t) * g t
  have hp : 0 < p := by dsimp [p]; nlinarith only [hF, hF1, sq_nonneg (F - 1)]
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cZ := continuousOn_radialZSource_end hS hua hab hs
  have cH : ContinuousOn H (Icc a b) := continuousOn_separation_primitive hab g hg
  have iz := hg.continuousOn_mul (by simpa only [uIcc_of_le hab] using cr.mul cZ.norm)
  have iH := hg.continuousOn_mul (by simpa only [uIcc_of_le hab] using cH)
  have hi : (∫ s in a..b, S.r u s * ‖radialZSource S u a s‖ * g s) ≤
      (Λ / (p * c)) * (∫ s in a..b, H s * g s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_ae_restrict hab iz (iH.const_mul (Λ / (p * c)))
    filter_upwards [hmajor, ae_restrict_mem measurableSet_Icc] with s hgs hsmem
    have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc le_rfl hsmem.2
    have hsub' : uIcc a s ⊆ uIcc a b := by
      simpa only [uIcc_of_le hsmem.1, uIcc_of_le hab] using hsub
    have hz := incoming_source_label_bound hS hstop hua hsmem.1
      (fun z hz => hs ⟨hz.1, hz.2.1, hz.2.2.trans hsmem.2⟩) hc hF hF1 g
      (hg.mono_set hsub') (hmajor.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
    have hgs0 : 0 ≤ g s := (norm_nonneg _).trans hgs
    simpa only [mul_assoc, Pi.mul_apply, p, H] using! mul_le_mul_of_nonneg_right hz hgs0
  have hcurv := radial_curvature_with_le hS hstop hua hab hs hc _ cZ g hg hmajor
  have hr := hS.r_pos (u, b) (hs ⟨rfl, hab, le_rfl⟩) (hua.trans_le hab)
  have hcurv' : ‖radialCurvatureWith S u a b (radialZSource S u a)‖ ≤
      (c * S.r u b)⁻¹ * ((Λ / (p * c)) * (∫ s in a..b, H s * g s)) :=
    hcurv.trans (mul_le_mul_of_nonneg_left hi (by positivity))
  have hst := hstop (u, b) (hs ⟨rfl, hab, le_rfl⟩)
  have hn := (hS.nu_neg (u, b) (hs ⟨rfl, hab, le_rfl⟩)).le
  have hn0 := neg_nonneg.mpr hn
  have hl := (hS.lam_pos (u, b) (hs ⟨rfl, hab, le_rfl⟩)).le
  have hΛ : 0 ≤ Λ := hl.trans hst.2.2.2.1
  calc
    _ ≤ (3 * Λ ^ 2 * F / δ) * ((-S.nu u b) / S.r u b ^ 2) *
        ‖radialCurvatureWith S u a b (radialZSource S u a)‖ :=
      curvature_scalar_source_le S u b δ Λ F _ _ hδ hr hn hl hst.2.2.2.1 hst.2.1
        hst.2.2.2.2.1
    _ ≤ (3 * Λ ^ 2 * F / δ) * ((-S.nu u b) / S.r u b ^ 2) *
        ((c * S.r u b)⁻¹ * ((Λ / (p * c)) * (∫ s in a..b, H s * g s))) :=
      mul_le_mul_of_nonneg_left hcurv' (by positivity)
    _ = _ := by dsimp [H, p]; simp only [div_eq_mul_inv, mul_inv_rev]; ring

end InteractionEstimate
end EmcsfAcExtension.Global
