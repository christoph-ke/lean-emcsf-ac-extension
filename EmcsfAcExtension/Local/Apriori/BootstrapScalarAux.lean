module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.Hardy
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Calculus.TriangleDiff
import EmcsfAcExtension.Infra.Calculus.PartialsC1
import EmcsfAcExtension.Infra.AC.Variation

/-! # Scalar reconstruction estimates for bootstrap improvement

The radial moments are bounded by the endpoint radius. The outgoing scalar
oscillation uses its actual axis value, with no change of charged background
(`charged_SF_new_version.tex:L4792–L4800`, approved internal project record (23)).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local

/-- Radius is increasing on every closed outgoing section in the classical
class. This qualitative comparison is uniform in all field parameters. -/
theorem radius_monotone_out {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u : ℝ} (hu : 0 ≤ u) :
    MonotoneOn (S.r u) (Icc u T) := by
  have hs : MapsTo (fun x : ℝ => (u, x)) (Icc u T) (triangle 0 T) :=
    fun x hx => ⟨hu, hx.1, hx.2⟩
  have cr : ContinuousOn (S.r u) (Icc u T) :=
    hS.c1_r.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn hs
  apply monotoneOn_of_deriv_nonneg (convex_Icc u T) cr
  · intro x hx
    rw [interior_Icc] at hx
    exact ((hasDerivWithinAt_uncurry_triangle_v hS.c1_r (hs ⟨hx.1.le, hx.2.le⟩)).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [((hasDerivWithinAt_uncurry_triangle_v hS.c1_r (hs ⟨hx.1.le, hx.2.le⟩)).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)).deriv]
    change 0 ≤ pdV (triangle 0 T) S.r u x
    rw [(hS.eq_v (u, x) (hs ⟨hx.1.le, hx.2.le⟩) hx.1).1]
    exact (hS.lam_pos (u, x) (hs ⟨hx.1.le, hx.2.le⟩)).le

/-- Radius is decreasing on every closed incoming section in the classical
class, including its zero axis endpoint. No estimate constant occurs. -/
theorem radius_antitone_in {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {v : ℝ} (hvT : v ≤ T) :
    AntitoneOn (fun x => S.r x v) (Icc 0 v) := by
  have hs : MapsTo (fun x : ℝ => (x, v)) (Icc 0 v) (triangle 0 T) :=
    fun x hx => ⟨hx.1, hx.2, hvT⟩
  have cr : ContinuousOn (fun x => S.r x v) (Icc 0 v) :=
    hS.c1_r.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hs
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 v) cr
  · intro x hx
    rw [interior_Icc] at hx
    exact ((hasDerivWithinAt_uncurry_triangle_u hS.c1_r (hs ⟨hx.1.le, hx.2.le⟩)).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [((hasDerivWithinAt_uncurry_triangle_u hS.c1_r (hs ⟨hx.1.le, hx.2.le⟩)).hasDerivAt
      (Icc_mem_nhds hx.1 hx.2)).deriv]
    change pdU (triangle 0 T) S.r x v ≤ 0
    rw [(hS.eq_u (x, v) (hs ⟨hx.1.le, hx.2.le⟩) hx.2).1]
    exact (hS.nu_neg (x, v) (hs ⟨hx.1.le, hx.2.le⟩)).le

/-- The pointwise outgoing scalar ratio is bounded by the outgoing normalized
scalar variation. The coefficient one is universal in all parameters. -/
theorem scalar_ratio_out_le_variation {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ‖S.theta u v / S.lam u v‖ ≤ (eVariationOn (S.a u) (Icc u v)).toReal := by
  rcases eq_or_lt_of_le huv with rfl | huv
  · have hz := (hS.axis u ⟨hu, le_rfl, hvT⟩).2.2.2.2.1
    change S.phi u u + S.theta u u / S.lam u u = S.phi u u at hz
    rw [add_eq_left] at hz
    rw [hz, norm_zero]
    exact ENNReal.toReal_nonneg
  have hs : MapsTo (fun x : ℝ => (u, x)) (Icc u v) (triangle 0 T) :=
    fun x hx => ⟨hu, hx.1, hx.2.trans hvT⟩
  have cp : ContinuousOn (fun x => pdV (triangle 0 T) S.a u x) (Icc u v) :=
    (continuousOn_pdV hS.c1_a
    (uniqueDiffOn_triangle (hu.trans_lt (huv.trans_le hvT)))).comp
      (continuous_const.prodMk continuous_id).continuousOn hs
  have cr : ContinuousOn (S.r u) (Icc u v) := hS.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hs
  have hr := hS.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv
  have hi := intervalIntegral.integral_mono_on (μ := volume) huv.le
    ((cr.mul cp.norm).intervalIntegrable_of_Icc huv.le)
    ((cp.norm.const_mul (S.r u v)).intervalIntegrable_of_Icc huv.le)
    (fun x hx => mul_le_mul_of_nonneg_right
      (radius_monotone_out hS hu ⟨hx.1, hx.2.trans hvT⟩ ⟨huv.le, hvT⟩ hx.2)
      (norm_nonneg _))
  calc
    _ ≤ (S.r u v)⁻¹ * (S.r u v * ∫ x in u..v, ‖pdV (triangle 0 T) S.a u x‖) :=
      (bv_hardy_out hS hu huv hvT).trans (mul_le_mul_of_nonneg_left
        (by simpa only [intervalIntegral.integral_const_mul, Pi.mul_apply] using hi)
          (inv_nonneg.mpr hr.le))
    _ = _ := by
      rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul, bv_variation_out hS hu huv.le hvT]

/-- The pointwise incoming scalar ratio is bounded by the integral of the
covariant incoming derivative. The coefficient one is universal and the
potential enters only through its unitary parallel transport. -/
theorem scalar_ratio_in_le_integral {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ‖S.xi u v / S.nu u v‖ ≤ ∫ x in u..v,
      ‖pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v‖ := by
  rcases eq_or_lt_of_le huv with rfl | huv
  · have hz := (hS.axis u ⟨hu, le_rfl, hvT⟩).2.2.2.2.2
    change S.phi u u + S.xi u u / S.nu u u = S.phi u u at hz
    rw [add_eq_left] at hz
    simp only [hz, norm_zero, intervalIntegral.integral_same, le_refl]
  have hs : MapsTo (fun x : ℝ => (x, v)) (Icc u v) (triangle 0 T) :=
    fun x hx => ⟨hu.trans hx.1, hx.2, hvT⟩
  have cb := hS.c1_b.continuousOn
  have cp := continuousOn_pdU hS.c1_b (uniqueDiffOn_triangle (hu.trans_lt (huv.trans_le hvT)))
  have cq : ContinuousOn (fun x =>
      pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v) (Icc u v) :=
    (cp.add (((continuousOn_const (c := I * e)).mul
    (Complex.continuous_ofReal.comp_continuousOn hS.c1_A.continuousOn)).mul cb)).comp
      (continuous_id.prodMk continuous_const).continuousOn hs
  have cr : ContinuousOn (fun x => S.r x v) (Icc u v) := hS.c1_r.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hs
  have hr := hS.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv
  have hi := intervalIntegral.integral_mono_on (μ := volume) huv.le
    ((cr.mul cq.norm).intervalIntegrable_of_Icc huv.le)
    ((cq.norm.const_mul (S.r u v)).intervalIntegrable_of_Icc huv.le)
    (fun x hx => mul_le_mul_of_nonneg_right
      (radius_antitone_in hS hvT ⟨hu, huv.le⟩ ⟨hu.trans hx.1, hx.2⟩ hx.1) (norm_nonneg _))
  calc
    _ ≤ (S.r u v)⁻¹ * (S.r u v * ∫ x in u..v,
        ‖pdU (triangle 0 T) S.b x v + I * e * S.A x v * S.b x v‖) :=
      (bv_hardy_in hS hu huv hvT).trans (mul_le_mul_of_nonneg_left
        (by simpa only [intervalIntegral.integral_const_mul, Pi.mul_apply] using hi)
          (inv_nonneg.mpr hr.le))
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]

/-- Outgoing scalar oscillation from its own axis value is bounded by the
normalized outgoing variation, with universal coefficient one. The identity
uses the actual charged scalar field throughout. -/
theorem scalar_axis_oscillation_le_variation {e T : ℝ} {S : Fields}
    (hT : 0 < T) (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ‖S.phi u v - S.phi u u‖ ≤ (eVariationOn (S.a u) (Icc u v)).toReal := by
  have hs : MapsTo (fun x : ℝ => (u, x)) (Icc u v) (triangle 0 T) :=
    fun x hx => ⟨hu, hx.1, hx.2.trans hvT⟩
  have hf := integralForm_pdV hS.c1_phi (uniqueDiffOn_triangle hT) huv hs
  have hh := bv_hardy_out_integrated hS hu huv hvT
  have heq : (∫ x in u..v, ‖pdV (triangle 0 T) S.phi u x‖) =
      ∫ x in u..v, S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    rw [uIoc_of_le huv] at hx
    have hp := hs ⟨hx.1.le, hx.2⟩
    rw [(hS.eq_v (u, x) hp hx.1).2.2.2.2.2.1]
    simp only [Fields.phiV, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hS.r_pos (u, x) hp hx.1), abs_of_pos (hS.lam_pos (u, x) hp)]
    field_simp [(hS.r_pos (u, x) hp hx.1).ne', (hS.lam_pos (u, x) hp).ne']
  rw [hf.2]
  apply (intervalIntegral.norm_integral_le_integral_norm huv).trans
  rw [heq]
  exact hh.2

end EmcsfAcExtension.Local
