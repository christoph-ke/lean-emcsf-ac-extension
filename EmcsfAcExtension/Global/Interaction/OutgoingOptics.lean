/- Copyright (c) 2026. All rights reserved. -/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import EmcsfAcExtension.Global.Interaction.PairSource
import EmcsfAcExtension.Infra.PowerKernel
import EmcsfAcExtension.Global.Renormalized.Radial
import EmcsfAcExtension.Global.Gap.Radial
import EmcsfAcExtension.Infra.AC.Quotient
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-!
# Outgoing optical square kernel

The finite radial kernel at `charged_SF_new_version.tex:L3784–L3793`. The two source
radii remain distinct until after the radial integration. All coefficients
are explicit and independent of physical scales and stage durations.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.InteractionEstimate

private theorem square_kernel_factor {p x y r : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hr : 0 < r) :
    (x / r) ^ p * (y / r) ^ p / r =
      (x / y) ^ p * orderedPowerKernel (2 * p) 0 y r := by
  unfold orderedPowerKernel
  simp only [sub_zero]
  rw [Real.div_rpow hx.le hr.le, Real.div_rpow hy.le hr.le,
    Real.div_rpow hx.le hy.le, show 2 * p = p + p by ring,
    Real.rpow_add hy, Real.rpow_add hr, Real.rpow_add hr, Real.rpow_one]
  have hyr := (Real.rpow_pos_of_pos hy p).ne'
  have hrr := (Real.rpow_pos_of_pos hr p).ne'
  field_simp

/-- [node prop:ct-interaction#outgoing-square-kernel]
The outgoing two-source kernel retains its min/max separation. The exact
constant is `1 / (2 * p)`, depending only on the positive damping exponent,
uniformly in both positive source radii and the finite terminal radius.
Source: `charged_SF_new_version.tex:L3784–L3793`. -/
theorem outgoing_square_kernel {p x y R : ℝ} (hp : 0 < p)
    (hx : 0 < x) (hy : 0 < y) (hR : max x y ≤ R) :
    (∫ r in (max x y)..R, (x / r) ^ p * (y / r) ^ p / r) ≤
        (1 / (2 * p)) * (min x y / max x y) ^ p ∧
      (1 / (2 * p)) * (min x y / max x y) ^ p ≤ 1 / (2 * p) := by
  have hmax : 0 < max x y := hx.trans_le (le_max_left _ _)
  have hmin : 0 < min x y := lt_min hx hy
  have hfactor : ∀ r ∈ uIcc (max x y) R,
      (x / r) ^ p * (y / r) ^ p / r =
        (min x y / max x y) ^ p * orderedPowerKernel (2 * p) 0 (max x y) r := by
    intro r hr
    rw [uIcc_of_le hR] at hr
    have hrr := hmax.trans_le hr.1
    rcases le_total x y with hxy | hyx
    · simpa only [max_eq_right hxy, min_eq_left hxy] using square_kernel_factor hx hy hrr
    · rw [mul_comm ((x / r) ^ p)]
      simpa only [max_eq_left hyx, min_eq_right hyx] using square_kernel_factor hy hx hrr
  have hsep : 0 ≤ (min x y / max x y) ^ p :=
    Real.rpow_nonneg (div_nonneg hmin.le hmax.le) _
  constructor
  · calc
      _ = (min x y / max x y) ^ p *
          ∫ r in (max x y)..R, orderedPowerKernel (2 * p) 0 (max x y) r := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr hfactor
      _ ≤ (min x y / max x y) ^ p * (1 / (2 * p)) :=
        mul_le_mul_of_nonneg_left
          (integral_orderedPowerKernel_le (mul_pos (by norm_num) hp) hmax hR) hsep
      _ = _ := mul_comm _ _
  · have hratio : min x y / max x y ≤ 1 :=
      (div_le_one hmax).mpr min_le_max
    have hpow : (min x y / max x y) ^ p ≤ 1 := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (div_nonneg hmin.le hmax.le) hratio hp.le
    exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans_eq (mul_one _)

end EmcsfAcExtension.Global.InteractionEstimate





namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The outgoing source primitive and full scalar are bounded by the label
mass. The exact coefficient `1/c` is uniform in all fields, envelopes,
radii, and row lengths. This uses the damping power before bounding it
by one. Source: charged_SF_new_version.tex:L3372–L3383. -/
theorem outgoing_scalar_pointwise {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b c F : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u a b ⊆ D) (hc : 0 < c) (hF : 0 ≤ F) (hF1 : F ≤ 1)
    (hlam : ∀ v ∈ Icc a b, c ≤ S.lam u v)
    (hy : ∀ v ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ≤ F)
    (g : ℝ → ℝ) (hg : IntervalIntegrable g volume a b)
    (hmajor : ∀ᵐ v ∂volume.restrict (Icc a b), ‖weightedJ S u v‖ ≤ g v) :
    ‖radialYSource S u a b‖ ≤ c⁻¹ * (∫ v in a..b, g v) ∧
      ‖S.theta u b / S.lam u b‖ ≤ ‖S.theta u a / S.lam u a‖ +
        c⁻¹ * (∫ v in a..b, g v) := by
  let p := 1 - F ^ 2
  have hp : 0 ≤ p := by dsimp [p]; nlinarith only [hF, hF1, sq_nonneg (F - 1)]
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v :=
    hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have hm := (outgoing_radius_calculus hS hua.le hab hs).2.monotoneOn
  have hpow (v : ℝ) (hv : v ∈ Icc a b) : (S.r u v / S.r u b) ^ p ≤ 1 := by
    have hh := (div_le_one (hr b ⟨hab, le_rfl⟩)).mpr
      (hm hv ⟨hab, le_rfl⟩ hv.2)
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (div_nonneg (hr v hv).le (hr b ⟨hab,
      le_rfl⟩).le) hh hp
  have iq : IntervalIntegrable (fun v => ‖weightedJ S u v‖ / S.lam u v) volume a b := by
    apply (Interaction.radial_y_source_integrable hS hua hab hs).norm.congr
    intro v hv
    have hv : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hv
    change ‖weightedJ S u v / (S.lam u v : ℂ)‖ = _
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hl v hv)]
  have cp : ContinuousOn (fun v => (S.r u v / S.r u b) ^ p) (Icc a b) :=
    (cr.div continuousOn_const (fun _ _ => (hr b ⟨hab, le_rfl⟩).ne')).rpow_const
      (fun v hv => Or.inl (div_pos (hr v hv) (hr b ⟨hab, le_rfl⟩)).ne')
  have ip := iq.continuousOn_mul (by simpa only [uIcc_of_le hab] using cp)
  have hi : (∫ v in a..b, (S.r u v / S.r u b) ^ p *
      (‖weightedJ S u v‖ / S.lam u v)) ≤ c⁻¹ * (∫ v in a..b, g v) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_ae_restrict hab ip (hg.const_mul c⁻¹)
    filter_upwards [hmajor, ae_restrict_mem measurableSet_Icc] with v hgv hv
    have hq : ‖weightedJ S u v‖ / S.lam u v ≤ c⁻¹ * g v := by
      calc
        _ ≤ g v / S.lam u v := div_le_div_of_nonneg_right hgv (hl v hv).le
        _ ≤ g v / c := div_le_div_of_nonneg_left ((norm_nonneg _).trans hgv) hc (hlam v hv)
        _ = _ := div_eq_inv_mul _ _
    exact (mul_le_of_le_one_left (div_nonneg (norm_nonneg _) (hl v hv).le)
      (hpow v hv)).trans hq
  have hsplit := ct_y_split hS hua hab hs hF hy
  have hsource := hsplit.2.trans hi
  refine ⟨hsource, ?_⟩
  rw [ct_y_split_identity hS hua hab hs]
  apply (norm_add_le _ _).trans
  apply add_le_add _ hsource
  exact hsplit.1.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (hpow a ⟨le_rfl, hab⟩) (norm_nonneg (S.theta u a / S.lam u a)))

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [node prop:ct-interaction#outgoing-scalar-square]
The outgoing scalar square is controlled by boundary amplitude and squared
label mass. Its positive constant depends only on `c,F`, before the
coupling, solution, row, envelope, radius scale, and duration.
The radial scalar energy identity gives the same source-square estimate
as the two-source kernel, without assuming a square-integrable density.
Source: charged_SF_new_version.tex:L3784–L3796 and the radial system. -/
theorem outgoing_scalar_square (c F : ℝ) (hc : 0 < c) (hF : 0 ≤ F) (hF1 : F < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (u a b : ℝ)
      (g : ℝ → ℝ), IsSolution e S D → u < a → a ≤ b → outSeg u a b ⊆ D →
      (∀ v ∈ Icc a b, c ≤ S.lam u v) →
      (∀ v ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ≤ F) →
      IntervalIntegrable g volume a b →
      (∀ᵐ v ∂volume.restrict (Icc a b), ‖weightedJ S u v‖ ≤ g v) →
      (∫ v in a..b, S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2) ≤
        C * (‖S.theta u a / S.lam u a‖ ^ 2 + (∫ v in a..b, g v) ^ 2) := by
  let p := 1 - F ^ 2
  have hp : 0 < p := by dsimp [p]; nlinarith only [hF, hF1, sq_nonneg (F - 1)]
  refine ⟨(2 + 3 * c⁻¹ ^ 2) / (2 * p), by positivity, ?_⟩
  intro e S D u a b g hS hua hab hs hlam hy hg hmajor
  let y := fun v => S.theta u v / (S.lam u v : ℂ)
  let J := ∫ v in a..b, g v
  let A := ‖y a‖
  let q := fun v => ‖weightedJ S u v‖ / S.lam u v
  have hg0 : ∀ᵐ v ∂volume.restrict (Icc a b), 0 ≤ g v :=
    hmajor.mono fun _ h => (norm_nonneg _).trans h
  have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg_of_ae_restrict hab hg0
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ A + c⁻¹ * J := by positivity
  have hbound (v : ℝ) (hv : v ∈ Icc a b) : ‖y v‖ ≤ A + c⁻¹ * J := by
    have hsub : Icc a v ⊆ Icc a b := Icc_subset_Icc le_rfl hv.2
    have hsub' : uIcc a v ⊆ uIcc a b := by
      simpa only [uIcc_of_le hv.1, uIcc_of_le hab] using hsub
    have hright : uIcc v b ⊆ uIcc a b := by
      rw [uIcc_of_le hv.2, uIcc_of_le hab]
      exact Icc_subset_Icc hv.1 le_rfl
    have hrest := intervalIntegral.integral_nonneg_of_ae_restrict hv.2
      (hg0.filter_mono (ae_mono (Measure.restrict_mono
        (show Icc v b ⊆ Icc a b from Icc_subset_Icc hv.1 le_rfl) le_rfl)))
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hg.mono_set hsub') (hg.mono_set hright)
    have hJ : (∫ t in a..v, g t) ≤ J := by dsimp [J]; linarith only [hrest, hadd]
    exact (outgoing_scalar_pointwise hS hua hv.1
      (fun z hz => hs ⟨hz.1, hz.2.1, hz.2.2.trans hv.2⟩) hc hF hF1.le
      (fun t ht => hlam t (hsub ht)) (fun t ht => hy t (hsub ht)) g (hg.mono_set hsub')
      (hmajor.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))).2.trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr hc.le)))
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v :=
    hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have cy : ContinuousOn y (Icc a b) := ct.div
    (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')
  have iw : IntervalIntegrable (fun v => S.lam u v / S.r u v * ‖y v‖ ^ 2) volume a b :=
    ((cl.div cr (fun v hv => (hr v hv).ne')).mul (cy.norm.pow 2)).intervalIntegrable_of_Icc hab
  have iq : IntervalIntegrable q volume a b := by
    apply (Interaction.radial_y_source_integrable hS hua hab hs).norm.congr
    intro v hv
    have hv : v ∈ Icc a b := by simpa only [uIcc_of_le hab] using uIoc_subset_uIcc hv
    change ‖weightedJ S u v / (S.lam u v : ℂ)‖ = q v
    dsimp [q]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hl v hv)]
  have iforce := iq.continuousOn_mul (by simpa only [uIcc_of_le hab] using cy.norm)
  have hforce : (∫ v in a..b, 2 * (‖y v‖ * q v)) ≤
      2 * (A + c⁻¹ * J) * c⁻¹ * J := by
    have hi : (∫ v in a..b, 2 * (‖y v‖ * q v)) ≤
        ∫ v in a..b, (2 * (A + c⁻¹ * J) * c⁻¹) * g v := by
      apply intervalIntegral.integral_mono_ae_restrict hab (iforce.const_mul 2)
        (hg.const_mul (2 * (A + c⁻¹ * J) * c⁻¹))
      filter_upwards [hmajor, ae_restrict_mem measurableSet_Icc] with v hgv hv
      have hq : q v ≤ c⁻¹ * g v := by
        dsimp [q]
        calc
          _ ≤ g v / S.lam u v := div_le_div_of_nonneg_right hgv (hl v hv).le
          _ ≤ g v / c := div_le_div_of_nonneg_left ((norm_nonneg _).trans hgv) hc (hlam v hv)
          _ = _ := div_eq_inv_mul _ _
      calc
        _ ≤ 2 * ((A + c⁻¹ * J) * (c⁻¹ * g v)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (hbound v hv) hq
              (div_nonneg (norm_nonneg _) (hl v hv).le) hB0) (by norm_num)
        _ = _ := by ring
    simpa only [intervalIntegral.integral_const_mul, J] using hi
  have hyac := Renormalized.radial_out_section hS hua hab hs
  have hnormLip : LipschitzWith 1 (norm : ℂ → ℝ) := lipschitzWith_one_norm
  have hnac : AbsolutelyContinuousOnInterval (fun v => ‖y v‖) a b :=
    hnormLip.comp_absolutelyContinuousOnInterval hyac.1
  have hEac : AbsolutelyContinuousOnInterval (fun v => ‖y v‖ ^ 2) a b := by
    simpa only [pow_two] using! hnac.mul_normed_ring hnac
  have henergy : ∀ᵐ v ∂volume.restrict (Icc a b),
      deriv (fun t => ‖y t‖ ^ 2) v + 2 * p *
        (S.lam u v / S.r u v * ‖y v‖ ^ 2) ≤ 2 * (‖y v‖ * q v) := by
    filter_upwards [hyac.2, ae_restrict_mem measurableSet_Icc] with v hd hv
    have heq : S.lam u v * (jOut S u v / ((1 - S.mu u v) * S.lam u v) -
        (1 - ‖S.theta u v / S.lam u v‖ ^ 2 : ℝ) / S.r u v *
          (S.theta u v / S.lam u v)) = weightedJ S u v / S.lam u v -
          (S.lam u v / S.r u v * (1 - ‖y v‖ ^ 2)) • y v := by
      dsimp [weightedJ, y]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr (hl v hv).ne',
        show 1 - (S.mu u v : ℂ) ≠ 0 from by exact_mod_cast
          (hS.one_sub_mu_pos (u, v) (hs ⟨rfl, hv⟩)).ne']
    have hd' : HasDerivAt y (weightedJ S u v / S.lam u v -
        (S.lam u v / S.r u v * (1 - ‖y v‖ ^ 2)) • y v) v := hd.congr_deriv heq
    rw [hd'.norm_sq.deriv, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    have hinner : inner ℝ (y v) (weightedJ S u v / S.lam u v) ≤ ‖y v‖ * q v := by
      calc
        _ ≤ ‖y v‖ * ‖weightedJ S u v / S.lam u v‖ := real_inner_le_norm _ _
        _ = _ := by
          congr 1
          dsimp [q]
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hl v hv)]
    have hysq : ‖y v‖ ^ 2 ≤ F ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hF).mpr (hy v hv)
    have hdiff : 0 ≤ (S.lam u v / S.r u v) * (F ^ 2 - ‖y v‖ ^ 2) * ‖y v‖ ^ 2 :=
      mul_nonneg (mul_nonneg (div_nonneg (hl v hv).le (hr v hv).le)
        (sub_nonneg.mpr hysq)) (sq_nonneg _)
    dsimp only [p, q]
    nlinarith only [hinner, hdiff]
  have hi := intervalIntegral.integral_mono_ae_restrict hab
    (hEac.intervalIntegrable_deriv.add (iw.const_mul (2 * p))) (iforce.const_mul 2) henergy
  rw [intervalIntegral.integral_add hEac.intervalIntegrable_deriv (iw.const_mul (2 * p)),
    hEac.integral_deriv_eq_sub, intervalIntegral.integral_const_mul] at hi
  have hyoung := sq_nonneg (A - c⁻¹ * J)
  have hfinal : 2 * p * (∫ v in a..b, S.lam u v / S.r u v * ‖y v‖ ^ 2) ≤
      2 * A ^ 2 + 3 * c⁻¹ ^ 2 * J ^ 2 := by
    change ‖y b‖ ^ 2 - ‖y a‖ ^ 2 +
      2 * p * (∫ v in a..b, S.lam u v / S.r u v * ‖y v‖ ^ 2) ≤
        ∫ v in a..b, 2 * (‖y v‖ * q v) at hi
    dsimp only [A] at hyoung ⊢
    nlinarith only [hi, hforce, hyoung, sq_nonneg ‖y b‖]
  change _ ≤ ((2 + 3 * c⁻¹ ^ 2) / (2 * p)) * (A ^ 2 + J ^ 2)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 2 * p)).mpr
  have hpos : 0 ≤ 3 * c⁻¹ ^ 2 * A ^ 2 := by positivity
  nlinarith only [hfinal, hpos, sq_nonneg J]

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global

/-- [internal]
Outgoing optical control under the explicit charge profile and derivative
envelope. The positive constant depends only on `δ,c,F,Cq`, before the
coupling, scalar background, radius scale, solution, row, and envelope.
The ordinary-mass identity is integrated in its equivalent `μ` form;
the outgoing scalar square estimate controls its scalar contribution.
Source: charged_SF_new_version.tex:L3778–L3796. -/
theorem ct_optical_out (δ c F Cq : ℝ) (hδ : 0 < δ) (hc : 0 < c)
    (hF : 0 ≤ F) (hF1 : F < 1) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M R₀ : ℝ) (S : Fields) (D : Set (ℝ × ℝ))
      (u a b : ℝ) (g : ℝ → ℝ), IsSolution e S D → u < a → a ≤ b → outSeg u a b ⊆ D →
      0 ≤ M → 0 ≤ R₀ → S.r u b ≤ R₀ →
      (∀ v ∈ Icc a b, 0 ≤ S.mu u v ∧ δ ≤ 1 - S.mu u v ∧ c ≤ S.lam u v ∧
        ‖S.theta u v / S.lam u v‖ ≤ F) →
      (∀ v ∈ Icc a b, |S.Q u v| / S.r u v ^ 2 ≤ Cq * |e| * M * F) →
      IntervalIntegrable g volume a b →
      (∀ᵐ v ∂volume.restrict (Icc a b), ‖weightedJ S u v‖ ≤ g v) →
      Real.log ((-S.nu u b) / (-S.nu u a)) ≤
        C * (S.m u a / S.r u a + ‖S.theta u a / S.lam u a‖ ^ 2 +
          (∫ v in a..b, g v) ^ 2 + Local.sigma e M (2 * R₀)) := by
  obtain ⟨K, hK, hscalar⟩ := InteractionEstimate.outgoing_scalar_square c F hc hF hF1
  let C := (2 + K + Cq ^ 2 / 2) / δ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro e M R₀ S D u a b g hS hua hab hs hM hR hRb hstop hQ hg hmajor
  let A := Cq * |e| * M * F
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs
  have hr (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.r u v :=
    hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) : 0 < S.lam u v :=
    hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have hmu := Renormalized.radial_mu_section hS hua hab hs
  have cm : ContinuousOn (S.mu u) (Icc a b) := by
    simpa only [uIcc_of_le hab] using hmu.1.continuousOn
  have cy := ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv).ne')
  have cw := cl.div cr (fun v hv => (hr v hv).ne')
  have im := (cw.mul cm).intervalIntegrable_of_Icc (μ := volume) hab
  have iy := (cw.mul (cy.norm.pow 2)).intervalIntegrable_of_Icc (μ := volume) hab
  have ir := (cl.mul cr).intervalIntegrable_of_Icc (μ := volume) hab
  have hdiff : ∀ᵐ v ∂volume.restrict (Icc a b),
      deriv (S.mu u) v + S.lam u v / S.r u v * S.mu u v ≤
        S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2 +
          A ^ 2 * (S.lam u v * S.r u v) := by
    filter_upwards [hmu.2, ae_restrict_mem measurableSet_Icc] with v hd hv
    rw [hd.deriv]
    have hq : S.Q u v ^ 2 / S.r u v ^ 2 ≤ A ^ 2 * S.r u v ^ 2 := by
      have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hA (sq_nonneg _))).mpr
        ((div_le_iff₀ (sq_pos_of_pos (hr v hv))).mp (hQ v hv))
      rw [sq_abs, mul_pow] at hh
      apply (div_le_iff₀ (sq_pos_of_pos (hr v hv))).mpr
      convert hh using 1
      ring
    have hy : (1 - S.mu u v) * ‖S.theta u v / S.lam u v‖ ^ 2 ≤
        ‖S.theta u v / S.lam u v‖ ^ 2 := by
      nlinarith only [mul_nonneg (hstop v hv).1 (sq_nonneg ‖S.theta u v / S.lam u v‖)]
    have hh := mul_le_mul_of_nonneg_left (add_le_add hy hq)
      (div_nonneg (hl v hv).le (hr v hv).le)
    convert hh using 1 <;> field_simp [(hr v hv).ne']
    ring
  have hi := intervalIntegral.integral_mono_ae_restrict hab
    (hmu.1.intervalIntegrable_deriv.add im) (iy.add (ir.const_mul (A ^ 2))) hdiff
  rw [intervalIntegral.integral_add hmu.1.intervalIntegrable_deriv im,
    hmu.1.integral_deriv_eq_sub, intervalIntegral.integral_add iy (ir.const_mul (A ^ 2)),
    intervalIntegral.integral_const_mul] at hi
  have hradius : (∫ v in a..b, S.lam u v * S.r u v) ≤ R₀ ^ 2 / 2 := by
    have hmom := Interaction.radial_moment hS hua hab hs 1
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat, pow_one] at hmom
    rw [hmom]
    have hsquares := (sq_le_sq₀ (hr b ⟨hab, le_rfl⟩).le hR).mpr hRb
    linarith only [hsquares, sq_nonneg (S.r u a)]
  have hys := hscalar e S D u a b g hS hua hab hs
    (fun v hv => (hstop v hv).2.2.1) (fun v hv => (hstop v hv).2.2.2) hg hmajor
  have hmass : (∫ v in a..b, S.lam u v / S.r u v * S.mu u v) ≤
      S.mu u a + K * (‖S.theta u a / S.lam u a‖ ^ 2 + (∫ v in a..b, g v) ^ 2) +
        A ^ 2 * R₀ ^ 2 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hradius (sq_nonneg A)
    change S.mu u b - S.mu u a +
      (∫ v in a..b, S.lam u v / S.r u v * S.mu u v) ≤
      (∫ v in a..b, S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2) +
        A ^ 2 * ∫ v in a..b, S.lam u v * S.r u v at hi
    nlinarith only [hi, hh, hys, (hstop b ⟨hab, le_rfl⟩).1]
  have hn := Gap.log_neg_nu_integralForm hS hua hab hs
  have hlog := intervalIntegral.integral_mono_on hab hn.1 (im.const_mul δ⁻¹)
    (fun v hv => by
      have hgap := hδ.trans_le (hstop v hv).2.1
      have hq0 : 0 ≤ S.Q u v ^ 2 / S.r u v ^ 2 := by positivity
      calc
        _ ≤ (S.lam u v * S.mu u v) / ((1 - S.mu u v) * S.r u v) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (sub_le_self _ hq0) (hl v hv).le)
              (mul_nonneg hgap.le (hr v hv).le)
        _ = (S.lam u v / S.r u v * S.mu u v) / (1 - S.mu u v) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        _ ≤ (S.lam u v / S.r u v * S.mu u v) / δ :=
          div_le_div_of_nonneg_left
            (mul_nonneg (div_nonneg (hl v hv).le (hr v hv).le) (hstop v hv).1)
            hδ (hstop v hv).2.1
        _ = _ := by
          change (S.lam u v / S.r u v * S.mu u v) / δ =
            δ⁻¹ * (S.lam u v / S.r u v * S.mu u v)
          ring)
  rw [intervalIntegral.integral_const_mul, ← hn.2,
    ← Real.log_div (neg_pos.mpr (hS.nu_neg (u, b) (hs ⟨rfl, hab, le_rfl⟩))).ne'
      (neg_pos.mpr (hS.nu_neg (u, a) (hs ⟨rfl, le_rfl, hab⟩))).ne'] at hlog
  have hscaled : A ^ 2 * R₀ ^ 2 / 2 ≤ Cq ^ 2 / 2 * Local.sigma e M (2 * R₀) := by
    rw [ct_zeta]
    have hF2 : F ^ 2 ≤ 1 := by nlinarith only [hF, hF1, sq_nonneg (F - 1)]
    have hh := mul_le_mul_of_nonneg_left hF2
      (show 0 ≤ Cq ^ 2 / 2 * (e ^ 2 * M ^ 2 * R₀ ^ 2) by positivity)
    dsimp [A]
    rw [mul_pow, mul_pow, mul_pow, sq_abs]
    convert hh using 1 <;> ring
  have hζ : 0 ≤ Local.sigma e M (2 * R₀) := by rw [ct_zeta]; positivity
  have hma : 0 ≤ S.m u a / S.r u a := by
    have hh := (hstop a ⟨le_rfl, hab⟩).1
    have heq : S.mu u a = 2 * (S.m u a / S.r u a) := by dsimp [Fields.mu]; ring
    rw [heq] at hh
    linarith only [hh]
  have hμa : S.mu u a = 2 * (S.m u a / S.r u a) := by dsimp [Fields.mu]; ring
  have hc2 : δ⁻¹ * 2 ≤ C := by
    dsimp [C]
    simp only [div_eq_mul_inv]
    nlinarith only [inv_nonneg.mpr hδ.le, hK, sq_nonneg Cq,
      mul_nonneg (inv_nonneg.mpr hδ.le) hK.le,
      mul_nonneg (inv_nonneg.mpr hδ.le) (sq_nonneg Cq)]
  have hcK : δ⁻¹ * K ≤ C := by
    dsimp [C]
    simp only [div_eq_mul_inv]
    nlinarith only [inv_nonneg.mpr hδ.le, hK, sq_nonneg Cq,
      mul_nonneg (inv_nonneg.mpr hδ.le) hK.le,
      mul_nonneg (inv_nonneg.mpr hδ.le) (sq_nonneg Cq)]
  have hcQ : δ⁻¹ * (Cq ^ 2 / 2) ≤ C := by
    dsimp [C]
    simp only [div_eq_mul_inv]
    nlinarith only [inv_nonneg.mpr hδ.le, hK, sq_nonneg Cq,
      mul_nonneg (inv_nonneg.mpr hδ.le) hK.le,
      mul_nonneg (inv_nonneg.mpr hδ.le) (sq_nonneg Cq)]
  calc
    _ ≤ δ⁻¹ * (2 * (S.m u a / S.r u a) +
        K * (‖S.theta u a / S.lam u a‖ ^ 2 + (∫ v in a..b, g v) ^ 2) +
        Cq ^ 2 / 2 * Local.sigma e M (2 * R₀)) :=
      hlog.trans (mul_le_mul_of_nonneg_left
        ((hmass.trans (add_le_add le_rfl hscaled)).trans_eq (by rw [hμa])) (by positivity))
    _ ≤ C * (S.m u a / S.r u a) +
        C * (‖S.theta u a / S.lam u a‖ ^ 2 + (∫ v in a..b, g v) ^ 2) +
        C * Local.sigma e M (2 * R₀) := by
      rw [mul_add, mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hc2 hma)
        (mul_le_mul_of_nonneg_right hcK (by positivity))) (mul_le_mul_of_nonneg_right hcQ hζ)
    _ = _ := by ring

end EmcsfAcExtension.Global
