module

public import EmcsfAcExtension.Local.Apriori.SmoothSupHardy
import EmcsfAcExtension.Local.Apriori.TVEnvelopeAux
import EmcsfAcExtension.Local.Apriori.SmoothSupKernel

/-! # Incoming opposite-axis radial averaging

The incoming moment is solved backwards from its own axis endpoint, by the
reflection `x = -u`. Its complex connection is retained in the transport and
has zero real growth. No incoming estimate on a trapezoid is used.
-/

public section

open Set MeasureTheory Complex Filter
open scoped ENNReal Topology

namespace EmcsfAcExtension.Local

/-- Incoming radius moment before coordinate comparison. The exact coefficient
`2` is universal in the box; there is no dependence on smooth data norms.
The exponent is any positive number below the displayed damping margin. -/
theorem smooth_incoming_radial_moment_aux {e T ε M p : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hp : 0 < p) (hsmall : p ≤ 1 - 16 * ε ^ 2)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖S.xi u v / S.nu u v‖ ≤
      ∫ a in u..v, (S.r a v / S.r u v) ^ p *
        (2 * (inEnv T (kC1 e (triangle 0 T) S) a).toReal) := by
  let D := triangle 0 T
  let z := fun x => S.b (-x) v - S.phi (-x) v
  let w := fun x => -S.nu (-x) v
  let c := fun x => 1 - ‖z x‖ ^ 2
  let q := fun x => -(kC1 e D S (-x) v / ((1 - S.mu (-x) v : ℝ) : ℂ))
  let Q := fun x => 2 * (inEnv T (kC1 e D S) (-x)).toReal
  have hab : -v ≤ -u := neg_le_neg huv.le
  have hs : MapsTo (fun x => (x, v)) (Icc u v) D :=
    fun _ hx => ⟨hu.trans hx.1, hx.2, hvT⟩
  have hm : MapsTo Neg.neg (Icc (-v) (-u)) (Icc u v) := by
    intro x hx
    constructor <;> linarith only [hx.1, hx.2]
  have hR (x : ℝ) (hx : x ∈ Icc (-v) (-u)) :
      (∫ s in (-v)..x, w s) = S.r (-x) v := by
    dsimp only [w]
    rw [intervalIntegral.integral_comp_neg (fun s => -S.nu s v), neg_neg]
    exact smooth_radius_integral_in_aux hset.c1 hset.pos (hs (hm hx))
  have hz : ContDiffOn ℝ 1 z (Icc (-v) (-u)) :=
    ((hset.c1.c1_b.sub hset.c1.c1_phi).comp
      (contDiffOn_id.prodMk (contDiffOn_const (c := v))) hs).comp
        (contDiff_id.neg).contDiffOn hm
  have cw : ContinuousOn w (Icc (-v) (-u)) :=
    ((hset.c1.c1_nu.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hs).neg).comp
        continuous_neg.continuousOn hm
  have hiQ : IntervalIntegrable Q volume (-v) (-u) := by
    have hi := ((apriori_envelopes_integrable hset).2.mono_set (show uIcc u v ⊆ uIcc 0 T by
      rw [uIcc_of_le huv.le, uIcc_of_le hset.pos.le]
      exact Icc_subset_Icc hu hvT)).const_mul 2
    simpa only [zero_sub, D, Q] using (hi.comp_sub_left 0).symm
  have hmain := smooth_radial_kernel_of_identity (z := z) (w := w) (c := c)
    (A := fun x => -(e * S.A (-x) v)) (Q := Q) (q := q) hab hp
    (cw.intervalIntegrable_of_Icc hab)
    (fun x hx => neg_nonneg.mpr (hset.c1.nu_neg _ (hs (hm hx))).le)
    (by apply ContDiffOn.absolutelyContinuousOnInterval; rwa [uIcc_of_le hab])
    (by
      dsimp only [z]
      rw [neg_neg]
      exact sub_eq_zero.mpr (hset.c1.axis v ⟨hu.trans huv.le, le_rfl, hvT⟩).2.2.2.2.2)
    hiQ (by rw [hR (-u) ⟨hab, le_rfl⟩, neg_neg]; exact hset.c1.r_pos _ (hs ⟨le_rfl, huv.le⟩) huv)
    (fun x hx => by
      have hb := (hset.box _ (hs (hm hx))).2.2.2.2.2.2.2
      have hi := pow_le_pow_left₀ (norm_nonneg _) hb 2
      dsimp [c, z]
      simp only [Fields.b, add_sub_cancel_left]
      nlinarith only [hi, hsmall])
    (show ∀ᵐ x ∂volume.restrict (Icc (-v) (-u)), ‖q x‖ ≤ Q x from by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hx' := hm hx
      have hmem := hs hx'
      have hmass := hset.c1.one_sub_mu_pos _ hmem
      have hk : ‖kC1 e D S (-x) v‖ ≤ (inEnv T (kC1 e D S) (-x)).toReal := by
        have hi := ENNReal.toReal_mono
          (apriori_envelopes_finite hset ⟨hu.trans hx'.1, hx'.2.trans hvT⟩).2
          (le_iSup₂_of_le v (show v ∈ Icc (-x) T from ⟨hx'.2, hvT⟩) le_rfl :
            ‖kC1 e D S (-x) v‖ₑ ≤ inEnv T (kC1 e D S) (-x))
        simpa only [toReal_enorm] using hi
      have hmassInv : (1 - S.mu (-x) v)⁻¹ ≤ 2 := by
        have hi := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) (hset.box _ hmem).2.2.2.2.1
        norm_num at hi
        exact hi
      dsimp only [q, Q]
      rw [norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmass,
        div_eq_mul_inv]
      calc
        _ ≤ ‖kC1 e D S (-x) v‖ * 2 :=
          mul_le_mul_of_nonneg_left hmassInv (norm_nonneg _)
        _ ≤ _ := by linarith only [hk])
    (show ∀ᵐ x ∂volume.restrict (Icc (-v) (-u)), HasDerivAt z
        ((-(w x / (∫ s in (-v)..x, w s) * c x) : ℂ) * z x -
          (I * (-(e * S.A (-x) v) : ℝ)) * z x + q x) x from by
      rw [← restrict_Ioo_eq_restrict_Icc]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hx' : -x ∈ Ioo u v := by constructor <;> linarith only [hx.1, hx.2]
      have hxmem : x ∈ Icc (-v) (-u) := ⟨hx.1.le, hx.2.le⟩
      have hxb : -x ∈ Icc u v := ⟨hx'.1.le, hx'.2.le⟩
      have hb := (hasDerivWithinAt_pdU hset.c1.c1_b (hs hxb) hs).hasDerivAt
        (Icc_mem_nhds hx'.1 hx'.2)
      have hf := (hasDerivWithinAt_pdU hset.c1.c1_phi (hs hxb) hs).hasDerivAt
        (Icc_mem_nhds hx'.1 hx'.2)
      apply ((hb.sub hf).scomp x (hasDerivAt_neg x)).congr_deriv
      simp only [neg_one_smul]
      change -(pdU D S.b (-x) v - pdU D S.phi (-x) v) = _
      rw [(hset.c1.eq_u _ (hs hxb) hx'.2).2.2.2.2.1, hR x hxmem]
      have hr := Complex.ofReal_ne_zero.mpr (hset.c1.r_pos _ (hs hxb) hx'.2).ne'
      have hn := Complex.ofReal_ne_zero.mpr (hset.c1.nu_neg _ (hs hxb)).ne
      have hd : (1 : ℂ) - (S.mu (-x) v : ℂ) ≠ 0 := by
        simpa only [Complex.ofReal_sub, Complex.ofReal_one] using
          Complex.ofReal_ne_zero.mpr (hset.c1.one_sub_mu_pos _ (hs hxb)).ne'
      dsimp [D, z, w, c, q, kC1, Fields.b, Fields.phiU]
      simp only [add_sub_cancel_left, Complex.ofReal_neg,
        Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]
      field_simp [hr, hn, hd]
      ring)
  calc
    ‖S.xi u v / S.nu u v‖ = ‖z (-u)‖ := by simp only [z, neg_neg, Fields.b, add_sub_cancel_left]
    _ ≤ _ := hmain
    _ = ∫ x in (-v)..(-u), (S.r (-x) v / S.r u v) ^ p *
        (2 * (inEnv T (kC1 e (triangle 0 T) S) (-x)).toReal) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hab] at hx
      dsimp only
      rw [hR x hx, hR (-u) ⟨hab, le_rfl⟩, neg_neg]
    _ = _ := by
      simpa only [neg_neg] using
        (intervalIntegral.integral_comp_neg
          (fun a => (S.r a v / S.r u v) ^ p *
            (2 * (inEnv T (kC1 e (triangle 0 T) S) a).toReal)) (a := -v) (b := -u))

/-- [node restart-sec-independent-area#damped-incoming-radial-moment]
[node restart-null-incoming-hardykernel]
The incoming opposite-axis weight, obtained by solving backwards from `(v,v)`.
The literal coefficient `8` is universal for `0 < p ≤ 1`, uniformly in the
datum, coupling, triangle and initial derivative size. The canonical background
comes from `AprioriSetting` (binding note S2). The positive separation is the
nondegeneracy permitted by internal project record. -/
theorem smooth_incoming_hardy_kernel {e T ε M p : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hp : 0 < p) (hp1 : p ≤ 1)
    (hsmall : p ≤ 1 - 16 * ε ^ 2) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖S.xi u v / S.nu u v‖ ≤
      8 * ∫ a in u..v, ((v - a) / (v - u)) ^ p *
        (inEnv T (kC1 e (triangle 0 T) S) a).toReal := by
  have hs : MapsTo (fun x => (x, v)) (Icc u v) (triangle 0 T) :=
    fun _ hx => ⟨hu.trans hx.1, hx.2, hvT⟩
  have henv : IntervalIntegrable (fun a => (inEnv T (kC1 e (triangle 0 T) S) a).toReal)
      volume u v := (apriori_envelopes_integrable hset).2.mono_set (by
        rw [uIcc_of_le huv.le, uIcc_of_le hset.pos.le]
        exact Icc_subset_Icc hu hvT)
  have cr := hset.c1.c1_r.continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn hs
  have cw : ContinuousOn (fun a => (S.r a v / S.r u v) ^ p) (Icc u v) :=
    (Real.continuous_rpow_const hp.le).comp_continuousOn (cr.div_const _)
  have cc : ContinuousOn (fun a => ((v - a) / (v - u)) ^ p) (Icc u v) :=
    (Real.continuous_rpow_const hp.le).comp_continuousOn
      ((continuousOn_const.sub continuousOn_id).div_const _)
  calc
    _ ≤ ∫ a in u..v, (S.r a v / S.r u v) ^ p *
        (2 * (inEnv T (kC1 e (triangle 0 T) S) a).toReal) :=
      smooth_incoming_radial_moment_aux hset hp hsmall hu huv hvT
    _ ≤ ∫ a in u..v, 8 * (((v - a) / (v - u)) ^ p *
        (inEnv T (kC1 e (triangle 0 T) S) a).toReal) := by
      apply intervalIntegral.integral_mono_on huv.le
        ((henv.const_mul 2).continuousOn_mul (by rwa [uIcc_of_le huv.le]))
        ((henv.continuousOn_mul (by rwa [uIcc_of_le huv.le])).const_mul 8)
      intro a ha
      have hr : 0 ≤ S.r a v :=
        (div_nonneg (sub_nonneg.mpr ha.2) (by norm_num)).trans
          (smooth_radius_bounds_aux hset (hs ha)).1
      have hc := smooth_radial_ratio_rpow_aux hr
        (hset.c1.r_pos _ (hs ⟨le_rfl, huv.le⟩) huv)
        (sub_nonneg.mpr ha.2) (sub_pos.mpr huv)
        (smooth_radius_bounds_aux hset (hs ha)).2
        (smooth_radius_bounds_aux hset (hs ⟨le_rfl, huv.le⟩)).1 hp.le hp1
      have hi := mul_le_mul_of_nonneg_right hc
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          (ENNReal.toReal_nonneg (a := inEnv T (kC1 e (triangle 0 T) S) a)))
      nlinarith only [hi]
    _ = _ := intervalIntegral.integral_const_mul _ _

end EmcsfAcExtension.Local
