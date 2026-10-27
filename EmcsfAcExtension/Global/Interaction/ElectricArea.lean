/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Global.Defs.Renormalized
public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Global.Renormalized.Radial
import EmcsfAcExtension.Global.Interaction.PairKernel
public import EmcsfAcExtension.Global.Interaction.PairSource
import EmcsfAcExtension.Infra.Level.Substitution
import Mathlib.Tactic

/-!
# Electromagnetic pointwise sources and spacetime area

The explicit remainder and the duration-independent area bound at
`charged_SF_new_version.tex:L3706–L3728`. Scalar and charge profiles are explicit inputs,
as in internal project record `source_and_optics_of_profiles`; no reconstruction
identity is assumed here. All displayed coefficients are fixed before the
coupling, scalar scale, radius scale, and stage durations.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The outgoing Maxwell right side obeys its pointwise norm bound. The
coefficient is exactly one, uniformly in all fields and scales.
Source: `charged_SF_new_version.tex:L3706`. -/
theorem maxwell_out_abs_le (e : ℝ) (S : Fields) (u v M F : ℝ)
    (hr : 0 ≤ S.r u v) (hl : 0 ≤ S.lam u v)
    (hp : ‖S.phi u v‖ ≤ M) (hy : ‖S.theta u v / S.lam u v‖ ≤ F)
    (hl0 : S.lam u v ≠ 0) :
    |S.QV e u v| ≤ |e| * M * S.r u v * S.lam u v * F := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hp
  have hθ : ‖S.theta u v‖ ≤ S.lam u v * F := by
    have heq : S.theta u v = (S.lam u v : ℂ) *
        (S.theta u v / S.lam u v) := by
      field_simp [Complex.ofReal_ne_zero.mpr hl0]
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
    exact mul_le_mul_of_nonneg_left hy hl
  calc
    |S.QV e u v| = |e| * S.r u v *
        |(starRingEnd ℂ (S.phi u v) * S.theta u v).im| := by
      simp [Fields.QV, abs_mul, abs_of_nonneg hr]
    _ ≤ |e| * S.r u v * (‖S.phi u v‖ * ‖S.theta u v‖) := by
      gcongr
      simpa only [norm_mul, Complex.norm_conj] using
        Complex.abs_im_le_norm (starRingEnd ℂ (S.phi u v) * S.theta u v)
    _ ≤ |e| * S.r u v * (M * (S.lam u v * F)) := by
      gcongr
    _ = _ := by ring

private theorem norm_emSourceJ_le (e : ℝ) (S : Fields) (u v : ℝ)
    (hr : 0 < S.r u v) (hl : 0 ≤ S.lam u v) (hn : 0 ≤ -S.nu u v) :
    ‖Local.emSourceJ e S u v‖ ≤
      (-S.nu u v) * S.lam u v *
        (5 * (|S.Q u v| / S.r u v ^ 2) ^ 2 *
          ‖S.theta u v / S.lam u v‖ +
        |e| * (|S.Q u v| / S.r u v ^ 2) *
          (3 * ‖S.theta u v / S.lam u v‖ + ‖S.phi u v‖)) +
      |e| * (-S.nu u v) * |S.QV e u v| * ‖S.phi u v‖ / S.r u v := by
  have hadd : ‖(3 : ℂ) * (S.theta u v / S.lam u v) + S.phi u v‖ ≤
      3 * ‖S.theta u v / S.lam u v‖ + ‖S.phi u v‖ := by
    simpa only [norm_mul, norm_ofNat] using norm_add_le
      ((3 : ℂ) * (S.theta u v / S.lam u v)) (S.phi u v)
  rw [Renormalized.emSourceJ_eq]
  calc
    _ ≤ ‖((-S.nu u v : ℂ) * S.lam u v / (S.r u v : ℂ) ^ 2)‖ *
        (‖(5 : ℂ) * ((S.Q u v : ℂ) ^ 2 / (S.r u v : ℂ) ^ 2) *
          (S.theta u v / S.lam u v)‖ +
        ‖I * e * S.Q u v * (3 * (S.theta u v / S.lam u v) + S.phi u v)‖) +
        ‖I * e * (-S.nu u v) * S.QV e u v * S.phi u v / S.r u v‖ := by
      calc
        _ ≤ ‖((-S.nu u v : ℂ) * S.lam u v / (S.r u v : ℂ) ^ 2) * _‖ + _ :=
          norm_add_le _ _
        _ = _ := by rw [norm_mul]
        _ ≤ _ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by
      simp only [norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_I, norm_ofNat, one_mul,
        abs_of_pos hr, abs_of_nonneg hl,
        abs_of_nonpos (neg_nonneg.mp hn)] at hadd ⊢
      calc
        _ ≤ ((-S.nu u v) * S.lam u v / S.r u v ^ 2) *
            (5 * (|S.Q u v| ^ 2 / S.r u v ^ 2) * (‖S.theta u v‖ / S.lam u v) +
              |e| * |S.Q u v| *
                (3 * (‖S.theta u v‖ / S.lam u v) + ‖S.phi u v‖)) + _ := by
          gcongr
        _ = _ := by ring

/-- [internal]
The explicit electromagnetic remainder under scalar and charge profiles.
The coefficient `5 Cq² F² + Cq (3 F + 1) + 1` depends only on the fixed
profile coefficient and scalar stop. It is uniform in `e`, `M`, radius,
expansions, and all durations. Source: `charged_SF_new_version.tex:L3706–L3712`. -/
theorem electric_remainder_le (e : ℝ) (S : Fields) (u v M F Cq : ℝ)
    (hr : 0 < S.r u v) (hl : 0 < S.lam u v) (hn : 0 ≤ -S.nu u v)
    (hM : 1 ≤ M) (hF : 0 ≤ F) (hCq : 0 ≤ Cq)
    (hp : ‖S.phi u v‖ ≤ M) (hy : ‖S.theta u v / S.lam u v‖ ≤ F)
    (hQ : |S.Q u v| / S.r u v ^ 2 ≤ Cq * |e| * M * F) :
    ‖Local.emSourceJ e S u v‖ ≤
      (5 * Cq ^ 2 * F ^ 2 + Cq * (3 * F + 1) + 1) *
        e ^ 2 * M ^ 2 * F * (-S.nu u v) * S.lam u v := by
  have hM0 : 0 ≤ M := le_trans (by norm_num) hM
  have hq0 : 0 ≤ |S.Q u v| / S.r u v ^ 2 := div_nonneg (abs_nonneg _) (sq_nonneg _)
  have hmax := maxwell_out_abs_le e S u v M F hr.le hl.le hp hy hl.ne'
  have hsum : 3 * ‖S.theta u v / S.lam u v‖ + ‖S.phi u v‖ ≤
      (3 * F + 1) * M := by
    calc
      _ ≤ 3 * F + M := by gcongr
      _ ≤ _ := by nlinarith
  have hfirst : 5 * (|S.Q u v| / S.r u v ^ 2) ^ 2 *
      ‖S.theta u v / S.lam u v‖ ≤ 5 * (Cq * |e| * M * F) ^ 2 * F := by
    gcongr
  have hsecond : |e| * (|S.Q u v| / S.r u v ^ 2) *
      (3 * ‖S.theta u v / S.lam u v‖ + ‖S.phi u v‖) ≤
      |e| * (Cq * |e| * M * F) * ((3 * F + 1) * M) := by
    gcongr
  calc
    _ ≤ (-S.nu u v) * S.lam u v *
        (5 * (Cq * |e| * M * F) ^ 2 * F +
          |e| * (Cq * |e| * M * F) * ((3 * F + 1) * M)) +
        |e| * (-S.nu u v) * (|e| * M * S.r u v * S.lam u v * F) * M /
          S.r u v := by
      apply (norm_emSourceJ_le e S u v hr hl.le hn).trans
      gcongr
    _ = _ := by
      rw [← sq_abs e]
      field_simp
      ring

end EmcsfAcExtension.Global.InteractionEstimate



namespace EmcsfAcExtension.Global

/-- [internal]
Profile-conditional form of `eq:ct-source-pointwise`.
The weighted electromagnetic source has an explicit coefficient depending
only on the fixed gap `δ`, scalar stop `F`, and profile coefficient `Cq`.
It is independent of the coupling, scalar scale, radius, and durations.
The profiles are supplied in the explicit internal project record form.
Source: `charged_SF_new_version.tex:L3706–L3712`. -/
theorem ct_source_pointwise_of_profiles (δ F Cq : ℝ) (hδ : 0 < δ) (hF : 0 ≤ F)
    (hCq : 0 ≤ Cq) (e : ℝ) (S : Fields) (u v M : ℝ)
    (hr : 0 < S.r u v) (hl : 0 < S.lam u v) (hn : 0 ≤ -S.nu u v)
    (hgap : δ ≤ 1 - S.mu u v) (hM : 1 ≤ M)
    (hp : ‖S.phi u v‖ ≤ M) (hy : ‖S.theta u v / S.lam u v‖ ≤ F)
    (hQ : |S.Q u v| / S.r u v ^ 2 ≤ Cq * |e| * M * F) :
    ‖((S.lam u v / (1 - S.mu u v) : ℝ) : ℂ) * Local.emSourceJ e S u v‖ ≤
      ((5 * Cq ^ 2 * F ^ 2 + Cq * (3 * F + 1) + 1) / δ) *
        e ^ 2 * M ^ 2 * F * (-S.nu u v) * S.lam u v ^ 2 := by
  have hg : 0 < 1 - S.mu u v := hδ.trans_le hgap
  have hK : 0 ≤ 5 * Cq ^ 2 * F ^ 2 + Cq * (3 * F + 1) + 1 := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos hl hg)]
  calc
    _ ≤ (S.lam u v / δ) *
        ((5 * Cq ^ 2 * F ^ 2 + Cq * (3 * F + 1) + 1) *
          e ^ 2 * M ^ 2 * F * (-S.nu u v) * S.lam u v) := by
      exact mul_le_mul (div_le_div_of_nonneg_left hl.le hδ hgap)
        (InteractionEstimate.electric_remainder_le e S u v M F Cq
          hr hl hn hM hF hCq hp hy hQ) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end EmcsfAcExtension.Global



namespace EmcsfAcExtension.Global.InteractionEstimate

private theorem neg_nu_out_le {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (hcharge : ∀ v ∈ Icc a b, S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v) :
    -S.nu u a ≤ -S.nu u b := by
  have he := (hS.eq_out u a b hua hab hs).2.1.2
  have hi := intervalIntegral.integral_nonneg (μ := volume) hab
    (f := fun v => -S.rUV u v) (fun v hv => by
      have hp : (u, v) ∈ D := hs ⟨rfl, hv⟩
      have hn := (hS.nu_neg (u, v) hp).le
      have hl := (hS.lam_pos (u, v) hp).le
      have hr := (hS.r_pos (u, v) hp (hua.trans_le hv.1)).le
      have hg := (hS.one_sub_mu_pos (u, v) hp).le
      exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn hl) hr)
        (div_nonneg (sub_nonneg.mpr (hcharge v hv)) hg)))
  rw [intervalIntegral.integral_neg, ← he] at hi
  linarith only [hi]

/-- [internal]
One outgoing row costs at most its terminal expansion times its terminal
radius. The coefficient is one and has no dependence on the row length.
The nonnegative radial expansion is derived from the charge/gap bound.
Source: `charged_SF_new_version.tex:L3714–L3724`. -/
theorem electric_row_area {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a : ℝ} (hua : u < a) (ha : a ≤ 0)
    (hs : outSeg u a 0 ⊆ D)
    (hcharge : ∀ v ∈ Icc a 0, S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v) :
    (∫⁻ v in Icc a 0, ENNReal.ofReal ((-S.nu u v) * S.lam u v)) ≤
      ENNReal.ofReal ((-S.nu u 0) * S.r u 0) := by
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cp : ContinuousOn (fun v => (-S.nu u v) * S.lam u v) (Icc a 0) := cn.neg.mul cl
  have hν : 0 ≤ -S.nu u 0 :=
    (neg_pos.mpr (hS.nu_neg (u, 0) (hs ⟨rfl, ha, le_rfl⟩))).le
  rw [← ofReal_integral_eq_lintegral_ofReal cp.integrableOn_Icc
    (ae_restrict_of_forall_mem measurableSet_Icc (fun v hv =>
      mul_nonneg (neg_pos.mpr (hS.nu_neg (u, v) (hs ⟨rfl, hv⟩))).le
        (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le))]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha]
  calc
    _ ≤ ∫ v in a..0, (-S.nu u 0) * S.lam u v := by
      apply intervalIntegral.integral_mono_on ha
        (cp.intervalIntegrable_of_Icc ha) ((cl.const_mul _).intervalIntegrable_of_Icc ha)
      intro v hv
      apply mul_le_mul_of_nonneg_right _ (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le
      exact neg_nu_out_le hS (hua.trans_le hv.1) hv.2
        (fun p hp => hs ⟨hp.1, hv.1.trans hp.2.1, hp.2.2⟩)
        (fun w hw => hcharge w ⟨hv.1.trans hw.1, hw.2⟩)
    _ = (-S.nu u 0) * (S.r u 0 - S.r u a) := by
      rw [intervalIntegral.integral_const_mul, ← (hS.eq_out u a 0 hua ha hs).1.2]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_self _
      (hS.r_pos (u, a) (hs ⟨rfl, le_rfl, ha⟩) hua).le) hν

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global

/-- [node eq:ct-area]
The exact radius-coordinate identity for the spacetime area. The inverse
radius is used only on each row's actual radius interval. Combined with
`ct_area`, this gives the change of variables and both uniform area bounds
at `charged_SF_new_version.tex:L3713–L3725`. No finiteness assumption precedes the
nonnegative substitution and no duration constant is introduced. -/
theorem ct_area_radius_identity {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {U : Set ℝ} {vb : ℝ → ℝ}
    (hU : MeasurableSet U)
    (hvb : ∀ u ∈ U, u ≤ vb u ∧ vb u ≤ 0)
    (hrow : ∀ u ∈ U, outSeg u (vb u) 0 ⊆ D) :
    (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
      ENNReal.ofReal ((-S.nu u v) * S.lam u v)) =
    ∫⁻ u in U, ∫⁻ x in Icc (S.r u (vb u)) (S.r u 0),
      ENNReal.ofReal (-S.nu u (Function.invFunOn (S.r u) (Icc (vb u) 0) x)) := by
  apply setLIntegral_congr_fun hU
  intro u hu
  dsimp only
  obtain ⟨hd, hm⟩ := InteractionEstimate.outgoing_radius_calculus hS
    (hvb u hu).1 (hvb u hu).2 (hrow u hu)
  have himage := (Calculus.continuousOn_out_section hS.cont_r (hrow u hu)).image_Icc_of_monotoneOn
    (hvb u hu).2 hm.monotoneOn
  rw [← himage, Level.lintegral_image_mono measurableSet_Icc hd hm.monotoneOn]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro v hv
  dsimp only
  rw [hm.injOn.leftInvOn_invFunOn hv,
    ← ENNReal.ofReal_mul (hS.lam_pos (u, v) (hrow u hu ⟨rfl, hv⟩)).le]
  congr 1
  ring

/-- [node eq:ct-area]
The spacetime area and its extra-`λ` version on arbitrary measurable time
histories of a stopped exterior. The coefficients are exactly `1/2` and
`Λ/2`, uniformly in coupling, scales, history components, and durations.
`vb` gives the actual lower outgoing endpoint; the terminal incoming
segment is contained in the original solution domain.
Source: `charged_SF_new_version.tex:L3713–L3725`. -/
theorem ct_area {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b R₀ Λ : ℝ} {U : Set ℝ} {vb : ℝ → ℝ}
    (hab : a ≤ b) (hb : b ≤ 0) (hterm : inSeg a b 0 ⊆ D)
    (hU : MeasurableSet U) (hsub : U ⊆ Icc a b) (hR : 0 ≤ R₀) (hΛ : 0 ≤ Λ)
    (hvb : ∀ u ∈ U, u < vb u ∧ vb u ≤ 0)
    (hrow : ∀ u ∈ U, outSeg u (vb u) 0 ⊆ D)
    (hcharge : ∀ u ∈ U, ∀ v ∈ Icc (vb u) 0,
      S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v)
    (hupper : ∀ u ∈ U, S.r u 0 ≤ R₀)
    (hlam : ∀ u ∈ U, ∀ v ∈ Icc (vb u) 0, S.lam u v ≤ Λ) :
    (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
      ENNReal.ofReal ((-S.nu u v) * S.lam u v)) ≤ ENNReal.ofReal (R₀ ^ 2 / 2) ∧
    (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
      ENNReal.ofReal ((-S.nu u v) * S.lam u v ^ 2)) ≤
      ENNReal.ofReal (Λ * R₀ ^ 2 / 2) := by
  have harea : (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
      ENNReal.ofReal ((-S.nu u v) * S.lam u v)) ≤ ENNReal.ofReal (R₀ ^ 2 / 2) := by
    calc
      _ ≤ ∫⁻ u in U, ENNReal.ofReal ((-S.nu u 0) * S.r u 0) :=
        lintegral_mono_ae (ae_restrict_of_forall_mem hU (fun u hu =>
          InteractionEstimate.electric_row_area hS (hvb u hu).1 (hvb u hu).2
            (hrow u hu) (hcharge u hu)))
      _ ≤ _ := InteractionEstimate.fixed_label_radius_moment hS hab hb hterm hU hsub hR
        (fun u hu => ⟨(hS.r_pos (u, 0) (hrow u hu ⟨rfl, (hvb u hu).2, le_rfl⟩)
          ((hvb u hu).1.trans_le (hvb u hu).2)).le, hupper u hu⟩)
  refine ⟨harea, ?_⟩
  calc
    _ ≤ ∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal (Λ * ((-S.nu u v) * S.lam u v)) := by
      apply lintegral_mono_ae (ae_restrict_of_forall_mem hU (fun u hu => ?_))
      apply lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc (fun v hv => ?_))
      apply ENNReal.ofReal_le_ofReal
      have hp : (u, v) ∈ D := hrow u hu ⟨rfl, hv.1, hv.2⟩
      have hn := (neg_pos.mpr (hS.nu_neg (u, v) hp)).le
      have hl := (hS.lam_pos (u, v) hp).le
      nlinarith [mul_nonneg hn hl, mul_nonneg hn (mul_nonneg hl (sub_nonneg.mpr (hlam u hu v hv)))]
    _ = ENNReal.ofReal Λ * (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ((-S.nu u v) * S.lam u v)) := by
      simp_rw [ENNReal.ofReal_mul hΛ,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal (R₀ ^ 2 / 2) := by gcongr
    _ = _ := by rw [← ENNReal.ofReal_mul hΛ]; congr 1; ring

end EmcsfAcExtension.Global

namespace EmcsfAcExtension.Global.InteractionEstimate

/-- [internal]
The actual weighted electromagnetic remainder has duration-independent
spacetime cost. The explicit coefficient depends only on `δ`, `F`, `Cq`,
and `Λ`, and is uniform in `e`, `M`, `R₀`, all histories, and all durations.
This is the explicit-remainder part of
`prop:ct-interaction#explicit-electromagnetic-source-cost`; the separate
canonical electromagnetic curvature primitive is not identified here.
Source: `charged_SF_new_version.tex:L3722–L3726`. -/
theorem explicit_electromagnetic_remainder_cost
    (δ F Cq Λ : ℝ) (hδ : 0 < δ) (hF : 0 ≤ F) (hCq : 0 ≤ Cq) (hΛ : 0 ≤ Λ)
    {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    {a b R₀ M : ℝ} {U : Set ℝ} {vb : ℝ → ℝ}
    (hab : a ≤ b) (hb : b ≤ 0) (hterm : inSeg a b 0 ⊆ D)
    (hU : MeasurableSet U) (hsub : U ⊆ Icc a b) (hR : 0 ≤ R₀) (hM : 1 ≤ M)
    (hvb : ∀ u ∈ U, u < vb u ∧ vb u ≤ 0)
    (hrow : ∀ u ∈ U, outSeg u (vb u) 0 ⊆ D)
    (hcharge : ∀ u ∈ U, ∀ v ∈ Icc (vb u) 0,
      S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v)
    (hupper : ∀ u ∈ U, S.r u 0 ≤ R₀)
    (hlam : ∀ u ∈ U, ∀ v ∈ Icc (vb u) 0, S.lam u v ≤ Λ)
    (hgap : ∀ u ∈ U, ∀ v ∈ Icc (vb u) 0, δ ≤ 1 - S.mu u v)
    (hphi : ∀ u ∈ U, ∀ v ∈ Icc (vb u) 0, ‖S.phi u v‖ ≤ M)
    (hy : ∀ u ∈ U, ∀ v ∈ Icc (vb u) 0, ‖S.theta u v / S.lam u v‖ ≤ F)
    (hQ : ∀ u ∈ U, ∀ v ∈ Icc (vb u) 0,
      |S.Q u v| / S.r u v ^ 2 ≤ Cq * |e| * M * F) :
    (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
      ENNReal.ofReal ‖((S.lam u v / (1 - S.mu u v) : ℝ) : ℂ) *
        Local.emSourceJ e S u v‖) ≤
      ENNReal.ofReal (((5 * Cq ^ 2 * F ^ 2 + Cq * (3 * F + 1) + 1) / δ) *
        (Λ / 2) * (|e| * M * R₀) ^ 2 * F) := by
  let K := (5 * Cq ^ 2 * F ^ 2 + Cq * (3 * F + 1) + 1) / δ
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcoef : 0 ≤ K * e ^ 2 * M ^ 2 * F := by positivity
  calc
    _ ≤ ∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
        ENNReal.ofReal ((K * e ^ 2 * M ^ 2 * F) *
          ((-S.nu u v) * S.lam u v ^ 2)) := by
      apply lintegral_mono_ae (ae_restrict_of_forall_mem hU (fun u hu => ?_))
      apply lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc (fun v hv => ?_))
      apply ENNReal.ofReal_le_ofReal
      have hp : (u, v) ∈ D := hrow u hu ⟨rfl, hv⟩
      have hpt := ct_source_pointwise_of_profiles δ F Cq hδ hF hCq e S u v M
        (hS.r_pos (u, v) hp ((hvb u hu).1.trans_le hv.1))
        (hS.lam_pos (u, v) hp) (neg_pos.mpr (hS.nu_neg (u, v) hp)).le
        (hgap u hu v hv) hM (hphi u hu v hv) (hy u hu v hv) (hQ u hu v hv)
      convert hpt using 1
      dsimp [K]
      ring
    _ = ENNReal.ofReal (K * e ^ 2 * M ^ 2 * F) *
        (∫⁻ u in U, ∫⁻ v in Icc (vb u) 0,
          ENNReal.ofReal ((-S.nu u v) * S.lam u v ^ 2)) := by
      simp_rw [ENNReal.ofReal_mul hcoef,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (K * e ^ 2 * M ^ 2 * F) *
        ENNReal.ofReal (Λ * R₀ ^ 2 / 2) := by
      gcongr
      exact (ct_area hS hab hb hterm hU hsub hR hΛ hvb hrow hcharge hupper hlam).2
    _ = _ := by
      rw [← ENNReal.ofReal_mul hcoef]
      congr 1
      rw [mul_pow, mul_pow, sq_abs]
      dsimp [K]
      ring

end EmcsfAcExtension.Global.InteractionEstimate

namespace EmcsfAcExtension.Global

/-- [internal]
The actual weighted Maxwell remainder under the stopped scalar and charge
profiles. Its positive constant depends only on `δ,F,Cq`, before the
coupling, scalar background, fields, and spacetime point.
Source: charged_SF_new_version.tex:L3707–L3712. -/
theorem ct_source_pointwise (δ F Cq : ℝ) (hδ : 0 < δ) (hF : 0 ≤ F)
    (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ (e M : ℝ) (S : Fields) (u v : ℝ),
      0 < S.r u v → 0 < S.lam u v → 0 ≤ -S.nu u v →
      δ ≤ 1 - S.mu u v → 1 ≤ M → ‖S.phi u v‖ ≤ M →
      ‖S.theta u v / S.lam u v‖ ≤ F →
      |S.Q u v| / S.r u v ^ 2 ≤ Cq * |e| * M * F →
      ‖((S.lam u v / (1 - S.mu u v) : ℝ) : ℂ) * Local.emSourceJ e S u v‖ ≤
        C * e ^ 2 * M ^ 2 * F * (-S.nu u v) * S.lam u v ^ 2 := by
  let K := (5 * Cq ^ 2 * F ^ 2 + Cq * (3 * F + 1) + 1) / δ
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro e M S u v hr hl hn hg hM hp hy hQ
  exact ct_source_pointwise_of_profiles δ F Cq hδ hF hCq e S u v M
    hr hl hn hg hM hp hy hQ

end EmcsfAcExtension.Global

namespace EmcsfAcExtension.Global.InteractionEstimate

end EmcsfAcExtension.Global.InteractionEstimate
