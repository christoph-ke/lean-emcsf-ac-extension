module

public import EmcsfAcExtension.Global.Exterior.OpticsCoefficients
import EmcsfAcExtension.Global.Exterior.RadiiProfile
import EmcsfAcExtension.Global.Api.Integrals
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Incoming optical tails in terminal-radius measure

The negative terminal radius derivative is the Jacobian of the incoming
mass weight. Proper substitutions are performed before converting finite
nonnegative integrals to real numbers. No signed integral is exhausted.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
An incoming logarithmic lambda increment is bounded by the adaptive
mass-weight tail in terminal radius. The coefficient `264` is numerical
and uniform in the original data, both rows and the incoming label.
The consumer proves incoming-past invariance and supplies the already
derived pointwise coefficient bound. -/
theorem incoming_log_lam_tail_le_of_majorant {ui e ub s t v R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) (hst : s ≤ t) (htv : t < v)
    (hRs : S.r s 0 ≤ R₀)
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hint : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hcontrolled : ∀ u ∈ Icc s t, (u, v) ∈ adaptiveExterior S ui ub ell)
    (hmajorant : ∀ p ∈ adaptiveExterior S ui ub ell,
      |S.rUV p.1 p.2 / S.lam p.1 p.2| ≤
        264 * (-S.nu p.1 0) * terminalMass S p.1 / ell (terminalRadius S p.1) ^ 2) :
    |Real.log (S.lam t v) - Real.log (S.lam s v)| ≤
      264 * (∫⁻ R in Ioc 0 (S.r s 0), ENNReal.ofReal (M R / ell R ^ 2)).toReal := by
  have hs : inSeg s t v ⊆ origDomain ui := by
    rintro ⟨u, w⟩ ⟨hu₁, hu₂, rfl⟩
    exact (hcontrolled u ⟨hu₁, hu₂⟩).1
  have hs0 : inSeg s t 0 ⊆ origDomain ui := by
    rintro ⟨u, w⟩ ⟨hu₁, hu₂, rfl⟩
    have hp := (hcontrolled u ⟨hu₁, hu₂⟩).1
    exact ⟨hp.1, hp.2.1, hp.2.1.le, le_rfl⟩
  have ht0 : t < 0 := (hcontrolled t ⟨hst, le_rfl⟩).1.2.1
  have cR := Calculus.continuousOn_in_section h.solution.cont_r hs0
  have cnt := Calculus.continuousOn_in_section h.solution.cont_nu hs0
  have hdR (u : ℝ) (hu : u ∈ Ioo s t) :
      HasDerivAt (fun u => S.r u 0) (S.nu u 0) u := by
    apply Local.hasDerivAt_of_integralForm_interior hu (cnt.mono Ioo_subset_Icc_self)
    intro c d hc hcd hd
    exact (h.solution.eq_in c d 0 hcd (hd.trans ht0)
      (fun _ hp => hs0 (inSeg_subset_inSeg hc.le hd.le hp))).1
  have hanti : StrictAntiOn (fun u => S.r u 0) (Icc s t) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc s t) cR
    intro u hu
    rw [interior_Icc] at hu
    rw [(hdR u hu).deriv]
    exact h.solution.nu_neg (u, 0) (hs0 ⟨hu.1.le, hu.2.le, rfl⟩)
  let A := fun R => ENNReal.ofReal (M R / ell R ^ 2)
  have hsub := lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn measurableSet_Ioo
    (fun u hu => (hdR u hu).hasDerivWithinAt)
    (hanti.antitoneOn.mono Ioo_subset_Icc_self) A
  have himage : (fun u => S.r u 0) '' Ioo s t ⊆ Ioc 0 (S.r s 0) := by
    rintro _ ⟨u, hu, rfl⟩
    have hp := hs0 (show (u, 0) ∈ inSeg s t 0 from ⟨hu.1.le, hu.2.le, rfl⟩)
    exact ⟨h.solution.r_pos (u, 0) hp hp.2.1,
      hanti.antitoneOn ⟨le_rfl, hst⟩ ⟨hu.1.le, hu.2.le⟩ hu.1.le⟩
  have hfinite : (∫⁻ R in Ioc 0 (S.r s 0), A R) < ⊤ :=
    (lintegral_mono_set (Ioc_subset_Ioc_right hRs)).trans_lt hint
  have hlog := in_log_lam_integralForm h hst htv hs
  have hi : IntervalIntegrable (fun u => |S.rUV u v / S.lam u v|) volume s t := by
    simpa only [Real.norm_eq_abs] using hlog.1.norm
  have hconvert := ofReal_intervalIntegral_eq_lintegral hst hi
    (Eventually.of_forall fun u => abs_nonneg (S.rUV u v / S.lam u v))
  rw [lintegral_Ico_eq_Icc, ← lintegral_Ioo_eq_Icc] at hconvert
  have hbound : ENNReal.ofReal (∫ u in s..t, |S.rUV u v / S.lam u v|) ≤
      ENNReal.ofReal 264 * ∫⁻ R in Ioc 0 (S.r s 0), A R := by
    rw [hconvert]
    calc
      _ ≤ ∫⁻ u in Ioo s t, ENNReal.ofReal 264 * (ENNReal.ofReal (-S.nu u 0) * A (S.r u 0)) := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro u hu
        have hp := hcontrolled u ⟨hu.1.le, hu.2.le⟩
        have hn := h.solution.nu_neg (u, 0)
          (hs0 ⟨hu.1.le, hu.2.le, rfl⟩)
        have hm := hmass u ⟨hp.1.1, hp.1.2.1⟩
        have hb := hmajorant (u, v) hp
        change |S.rUV u v / S.lam u v| ≤
          264 * (-S.nu u 0) * S.m u 0 / ell (S.r u 0) ^ 2 at hb
        rw [← hm] at hb
        dsimp [A]
        rw [← ENNReal.ofReal_mul (neg_nonneg.mpr hn.le),
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 264)]
        exact ENNReal.ofReal_le_ofReal (by simpa only [div_eq_mul_inv, mul_assoc] using hb)
      _ = ENNReal.ofReal 264 *
          ∫⁻ u in Ioo s t, ENNReal.ofReal (-S.nu u 0) * A (S.r u 0) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal 264 * ∫⁻ R in (fun u => S.r u 0) '' Ioo s t, A R := by rw [← hsub]
      _ ≤ _ := mul_le_mul le_rfl (lintegral_mono_set himage) bot_le bot_le
  have hnonneg : 0 ≤ ∫ u in s..t, |S.rUV u v / S.lam u v| :=
    intervalIntegral.integral_nonneg (μ := volume) hst (fun u _ => abs_nonneg _)
  have hreal : (∫ u in s..t, |S.rUV u v / S.lam u v|) ≤
      264 * (∫⁻ R in Ioc 0 (S.r s 0), A R).toReal := by
    have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite.ne) hbound
    simpa only [ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 264)] using hb
  rw [hlog.2]
  exact (intervalIntegral.abs_integral_le_integral_abs hst).trans hreal

/-- [internal]
The real adaptive optical tail tends to zero. Finiteness is established
in the nonnegative integral before `toReal` is used. The coefficient
`264` is numerical; the mass and profile are fixed before the limit. -/
theorem optical_tail_tendsto_zero {M ell : ℝ → ℝ} {R₀ : ℝ} (hR : 0 < R₀)
    (hint : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤) :
    Tendsto (fun r => 264 * (∫⁻ R in Ioc 0 r, ENNReal.ofReal (M R / ell R ^ 2)).toReal)
      (𝓝[>] 0) (𝓝 0) := by
  have ht := mass_tail_tendsto hR hint
  have hr := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp ht
  simpa only [ENNReal.toReal_zero, mul_zero, Function.comp_apply] using hr.const_mul (264 : ℝ)

end EmcsfAcExtension.Global.Exterior
