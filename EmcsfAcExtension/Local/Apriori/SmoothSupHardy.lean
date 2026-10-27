module

public import EmcsfAcExtension.Local.Apriori.SmoothSupMoment
public import EmcsfAcExtension.Local.Apriori.SmoothSupRadial
import EmcsfAcExtension.Local.Apriori.SmoothSupKernel
import EmcsfAcExtension.Local.Apriori.TVEnvelopeAux
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Radial moments with a subunit exponent

The opposite-axis weights in internal project record (M2),
`charged_SF_new_version.tex:L4946–4946` and `L6209–6216`. These proofs use only the
classical equations, the definitions of `j,k`, and the standing box.
-/

public section

open Set MeasureTheory Complex Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

private theorem inverse_mass_aux {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {p : ℝ × ℝ} (hp : p ∈ triangle 0 T) :
    (1 - S.mu p.1 p.2)⁻¹ ≤ 2 := by
  have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) (hset.box p hp).2.2.2.2.1
  norm_num at hi
  exact hi

private theorem ratio_damping_aux {ε p : ℝ} {f : ℂ} (_hε : 0 ≤ ε)
    (hf : ‖f‖ ≤ 4 * ε) (hp : p ≤ 1 - 16 * ε ^ 2) : p ≤ 1 - ‖f‖ ^ 2 := by
  have hi := pow_le_pow_left₀ (norm_nonneg _) hf 2
  nlinarith only [hi, hp]

/-- The outgoing radius moment before coordinate comparison.
The exact coefficient `2` is universal in the bootstrap box; `p` is any
positive exponent below the radial damping. This helper carries no node tag. -/
theorem smooth_outgoing_radial_moment_aux {e T ε M p : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hp : 0 < p) (hsmall : p ≤ 1 - 16 * ε ^ 2)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖S.theta u v / S.lam u v‖ ≤
      ∫ x in u..v, (S.r u x / S.r u v) ^ p *
        (2 * (outEnv 0 (jC1 (triangle 0 T) S) x).toReal) := by
  let D := triangle 0 T
  let z := fun x => S.a u x - S.phi u x
  let w := S.lam u
  let c := fun x => 1 - ‖z x‖ ^ 2
  let q := fun x => jC1 D S u x / ((1 - S.mu u x : ℝ) : ℂ)
  let Q := fun x => 2 * (outEnv 0 (jC1 D S) x).toReal
  have hs : MapsTo (fun x => (u, x)) (Icc u v) D :=
    fun _ hx => ⟨hu, hx.1, hx.2.trans hvT⟩
  have hR (x : ℝ) (hx : x ∈ Icc u v) : (∫ s in u..x, w s) = S.r u x :=
    smooth_radius_integral_out_aux hset.c1 hset.pos (hs hx)
  have hz : ContDiffOn ℝ 1 z (Icc u v) :=
    (hset.c1.c1_a.sub hset.c1.c1_phi).comp
      ((contDiffOn_const (c := u)).prodMk contDiffOn_id) hs
  have hw : IntervalIntegrable w volume u v :=
    (hset.c1.c1_lam.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn hs).intervalIntegrable_of_Icc huv.le
  have hiQ : IntervalIntegrable Q volume u v := by
    apply ((apriori_envelopes_integrable hset).1.mono_set ?_).const_mul
    rw [uIcc_of_le huv.le, uIcc_of_le hset.pos.le]
    exact Icc_subset_Icc hu hvT
  have hε : 0 ≤ ε := ENNReal.toReal_nonneg.trans hset.eps
  have hmain := smooth_radial_kernel_of_identity (z := z) (w := w) (c := c)
    (A := fun _ => 0) (Q := Q) (q := q) huv.le hp hw
    (fun x hx => (hset.c1.lam_pos _ (hs hx)).le)
    (by apply ContDiffOn.absolutelyContinuousOnInterval; rwa [uIcc_of_le huv.le])
    (by dsimp [z]; exact sub_eq_zero.mpr (hset.c1.axis u (hs ⟨le_rfl, huv.le⟩)).2.2.2.2.1)
    hiQ (by rw [hR v ⟨huv.le, le_rfl⟩]; exact hset.c1.r_pos _ (hs ⟨huv.le, le_rfl⟩) huv)
    (fun x hx => by
      dsimp [c, z]
      simp only [Fields.a, add_sub_cancel_left]
      exact ratio_damping_aux hε (hset.box _ (hs hx)).2.2.2.2.2.2.1 hsmall)
    (show ∀ᵐ x ∂volume.restrict (Icc u v), ‖q x‖ ≤ Q x from by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hm := hset.c1.one_sub_mu_pos _ (hs hx)
      have hj : ‖jC1 D S u x‖ ≤ (outEnv 0 (jC1 D S) x).toReal := by
        have he := ENNReal.toReal_mono
          (apriori_envelopes_finite hset ⟨hu.trans hx.1, hx.2.trans hvT⟩).1
          (le_iSup₂_of_le u (show u ∈ Icc 0 x from ⟨hu, hx.1⟩) le_rfl :
            ‖jC1 D S u x‖ₑ ≤ outEnv 0 (jC1 D S) x)
        simpa only [toReal_enorm] using he
      dsimp only [q, Q]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm, div_eq_mul_inv]
      calc
        _ ≤ ‖jC1 D S u x‖ * 2 := mul_le_mul_of_nonneg_left
          (inverse_mass_aux hset (hs hx)) (norm_nonneg _)
        _ ≤ _ := by linarith only [hj])
    (show ∀ᵐ x ∂volume.restrict (Icc u v),
        HasDerivAt z
          ((-(w x / (∫ s in u..x, w s) * c x) : ℂ) * z x -
            (I * (0 : ℝ)) * z x + q x) x from by
      rw [← restrict_Ioo_eq_restrict_Icc]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hxb : x ∈ Icc u v := ⟨hx.1.le, hx.2.le⟩
      have ha := (hasDerivWithinAt_pdV hset.c1.c1_a (hs hxb) hs).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)
      have hf := (hasDerivWithinAt_pdV hset.c1.c1_phi (hs hxb) hs).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)
      apply (ha.sub hf).congr_deriv
      change pdV D S.a u x - pdV D S.phi u x = _
      rw [(hset.c1.eq_v _ (hs hxb) hx.1).2.2.2.2.2.1, hR x hxb]
      have hr := Complex.ofReal_ne_zero.mpr (hset.c1.r_pos _ (hs hxb) hx.1).ne'
      have hl := Complex.ofReal_ne_zero.mpr (hset.c1.lam_pos _ (hs hxb)).ne'
      have hm : (1 : ℂ) - (S.mu u x : ℂ) ≠ 0 := by
        simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
          Complex.ofReal_ne_zero.mpr (hset.c1.one_sub_mu_pos _ (hs hxb)).ne'
      dsimp [D, z, w, c, q, jC1, Fields.a, Fields.phiV]
      simp only [add_sub_cancel_left, Complex.ofReal_sub, Complex.ofReal_one,
        Complex.ofReal_pow]
      field_simp [hr, hl, hm]
      ring)
  calc
    ‖S.theta u v / S.lam u v‖ = ‖z v‖ := by simp only [z, Fields.a, add_sub_cancel_left]
    _ ≤ _ := hmain
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le huv.le] at hx
      dsimp only
      rw [hR x hx, hR v ⟨huv.le, le_rfl⟩]

/-- [node restart-sec-independent-null-construction#outgoing-hardykernel]
The outgoing opposite-axis weight of internal project record (M2). The literal coefficient
`8` is universal for `0 < p ≤ 1`, uniformly in the datum, coupling, triangle,
and initial derivative size. The damping margin is the node's own hypothesis;
the canonical background is supplied by `AprioriSetting` (binding note S2). -/
theorem smooth_outgoing_hardy_kernel {e T ε M p : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hp : 0 < p) (hp1 : p ≤ 1)
    (hsmall : p ≤ 1 - 16 * ε ^ 2) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖S.theta u v / S.lam u v‖ ≤
      8 * ∫ x in u..v, ((x - u) / (v - u)) ^ p *
        (outEnv 0 (jC1 (triangle 0 T) S) x).toReal := by
  have hs : MapsTo (fun x => (u, x)) (Icc u v) (triangle 0 T) :=
    fun _ hx => ⟨hu, hx.1, hx.2.trans hvT⟩
  have henv : IntervalIntegrable (fun x => (outEnv 0 (jC1 (triangle 0 T) S) x).toReal)
      volume u v := (apriori_envelopes_integrable hset).1.mono_set (by
        rw [uIcc_of_le huv.le, uIcc_of_le hset.pos.le]
        exact Icc_subset_Icc hu hvT)
  have cr := hset.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hs
  have cw : ContinuousOn (fun x => (S.r u x / S.r u v) ^ p) (Icc u v) :=
    (Real.continuous_rpow_const hp.le).comp_continuousOn (cr.div_const _)
  have cc : ContinuousOn (fun x => ((x - u) / (v - u)) ^ p) (Icc u v) :=
    (Real.continuous_rpow_const hp.le).comp_continuousOn
      ((continuousOn_id.sub continuousOn_const).div_const _)
  calc
    _ ≤ ∫ x in u..v, (S.r u x / S.r u v) ^ p *
        (2 * (outEnv 0 (jC1 (triangle 0 T) S) x).toReal) :=
      smooth_outgoing_radial_moment_aux hset hp hsmall hu huv hvT
    _ ≤ ∫ x in u..v, 8 * (((x - u) / (v - u)) ^ p *
        (outEnv 0 (jC1 (triangle 0 T) S) x).toReal) := by
      apply intervalIntegral.integral_mono_on huv.le
        ((henv.const_mul 2).continuousOn_mul (by rwa [uIcc_of_le huv.le]))
        ((henv.continuousOn_mul (by rwa [uIcc_of_le huv.le])).const_mul 8)
      intro x hx
      have hr : 0 ≤ S.r u x :=
        (div_nonneg (sub_nonneg.mpr hx.1) (by norm_num)).trans
          (smooth_radius_bounds_aux hset (hs hx)).1
      have hc := smooth_radial_ratio_rpow_aux hr
        (hset.c1.r_pos _ (hs ⟨huv.le, le_rfl⟩) huv)
        (sub_nonneg.mpr hx.1) (sub_pos.mpr huv)
        (smooth_radius_bounds_aux hset (hs hx)).2
        (smooth_radius_bounds_aux hset (hs ⟨huv.le, le_rfl⟩)).1 hp.le hp1
      have hi := mul_le_mul_of_nonneg_right hc
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (ENNReal.toReal_nonneg (a := outEnv 0 (jC1 (triangle 0 T) S) x)))
      nlinarith only [hi]
    _ = _ := intervalIntegral.integral_const_mul _ _

end EmcsfAcExtension.Local
