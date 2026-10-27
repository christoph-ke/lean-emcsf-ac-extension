module

public import EmcsfAcExtension.Global.Terminal.Charge
public import EmcsfAcExtension.Frozen.SignedExpIntegrand
public import EmcsfAcExtension.Frozen.PositiveExpIntegrand
public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Global.Api.Domains
public import EmcsfAcExtension.Global.Api.Finite
import EmcsfAcExtension.Global.Calculus.Sections

/-! # Terminal exponents on proper truncations

The converse of charged_SF_new_version.tex:L916–930 uses only an inequality of real
integrands on compact positive-radius sections. Extended integrals appear
only for the nonnegative positive integrand; finiteness precedes `toReal`.
The legacy converse retains its literal six-premise interface; the forward
argument uses the landed original-development definitions.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Terminal

/-- [internal] The frozen signed integrand is no greater than the positive
integrand at every positive-radius point of a solution. -/
theorem signed_le_positive {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (hp : (u, v) ∈ D) (huv : u < v) :
    signedExpIntegrand S u v ≤ positiveExpIntegrand S u v := by
  have hn := neg_pos.mpr (hS.nu_neg (u, v) hp)
  have hr := hS.r_pos (u, v) hp huv
  have hg := hS.one_sub_mu_pos (u, v) hp
  apply div_le_div_of_nonneg_right _ (mul_pos hg hr).le
  exact mul_le_mul_of_nonneg_left
    (sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))) hn.le

/-- [internal] The positive exponent is nonnegative when the mass ratio is. -/
theorem positive_integrand_nonneg {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (hp : (u, v) ∈ D) (huv : u < v)
    (hmu : 0 ≤ S.mu u v) : 0 ≤ positiveExpIntegrand S u v := by
  exact div_nonneg (mul_nonneg (neg_nonneg.mpr (hS.nu_neg (u, v) hp).le) hmu)
    (mul_nonneg (hS.one_sub_mu_pos (u, v) hp).le (hS.r_pos (u, v) hp huv).le)

/-- [internal] On a positive-radius section, positive equals signed plus the
literal charge correction of internal project record. -/
theorem positive_eq_signed_add_correction {S : Fields} {u v : ℝ}
    (hr : S.r u v ≠ 0) (hg : 1 - S.mu u v ≠ 0) :
    positiveExpIntegrand S u v = signedExpIntegrand S u v +
      -S.nu u v * S.Q u v ^ 2 / ((1 - S.mu u v) * S.r u v ^ 3) := by
  dsimp [positiveExpIntegrand, signedExpIntegrand]
  field_simp [hr, hg]
  ring

/-- [internal] A proper terminal positive integral has the exact nonnegative
lintegral interpretation. Terminal finiteness is unnecessary for this equality. -/
theorem truncated_positive_integral (ui e : ℝ) (S : Fields)
    (hS : IsSolution e S (origDomain ui))
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (u : ℝ) (hu : u ∈ Ioo ui 0) :
    ENNReal.ofReal (∫ s in ui..u, positiveExpIntegrand S s 0) =
      ∫⁻ s in Icc ui u, ENNReal.ofReal (positiveExpIntegrand S s 0) := by
  have hseg : inSeg ui u 0 ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff hu.1.le).2 ⟨le_rfl, hu.2, hu.2.le, le_rfl⟩
  rw [← lintegral_Ico_eq_Icc]
  apply ofReal_intervalIntegral_eq_lintegral_of_continuousOn hu.1.le
    (incoming_integrands_continuousOn hS hu.2 hseg).2.1
  intro s hs
  have hp : (s, 0) ∈ origDomain ui := hseg ⟨hs.1, hs.2, rfl⟩
  exact positive_integrand_nonneg hS hp (hs.2.trans_lt hu.2) (hmu _ hp).1

/-- [node prop:charged-terminal-equivalence#positive-to-signed]
Finite positive terminal integral bounds every signed partial integral,
charged_SF_new_version.tex:L1026–1031. The bound may depend on this solution's finite
positive integral and is uniform in the proper terminal cutoff. -/
theorem positive_to_signed (ui e : ℝ) (S : Fields) (_hui : ui < 0)
    (hS : IsSolution e S (origDomain ui))
    (_hgauge : ∀ t, ui ≤ t → t < 0 → S.A t t = 0)
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (_hr : ∀ v ∈ Icc ui 0, S.r ui v = (v - ui) / 2)
    (_hdata : AbsolutelyContinuousOnInterval (S.a ui) ui 0)
    (hpos : (∫⁻ u in Ico ui 0, ENNReal.ofReal (positiveExpIntegrand S u 0)) < ⊤) :
    BddAbove ((fun u => ∫ s in ui..u, signedExpIntegrand S s 0) '' Ioo ui 0) := by
  let P := ∫⁻ s in Ico ui 0, ENNReal.ofReal (positiveExpIntegrand S s 0)
  have hP : P ≠ ⊤ := hpos.ne
  refine ⟨P.toReal, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have hseg : inSeg ui u 0 ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff hu.1.le).2 ⟨le_rfl, hu.2, hu.2.le, le_rfl⟩
  have hc := incoming_integrands_continuousOn hS hu.2 hseg
  have hle : (∫ s in ui..u, signedExpIntegrand S s 0) ≤
      ∫ s in ui..u, positiveExpIntegrand S s 0 := by
    apply intervalIntegral.integral_mono_on hu.1.le
      (hc.1.intervalIntegrable_of_Icc hu.1.le) (hc.2.1.intervalIntegrable_of_Icc hu.1.le)
    intro s hs
    exact signed_le_positive hS (hseg ⟨hs.1, hs.2, rfl⟩) (hs.2.trans_lt hu.2)
  have hnonneg : 0 ≤ ∫ s in ui..u, positiveExpIntegrand S s 0 := by
    apply intervalIntegral.integral_nonneg hu.1.le
    intro s hs
    have hp := hseg (show (s, 0) ∈ inSeg ui u 0 from ⟨hs.1, hs.2, rfl⟩)
    exact positive_integrand_nonneg hS hp (hs.2.trans_lt hu.2) (hmu _ hp).1
  have htrunc : ENNReal.ofReal (∫ s in ui..u, positiveExpIntegrand S s 0) ≤ P := by
    rw [truncated_positive_integral ui e S hS hmu u hu]
    exact lintegral_mono_set ((Icc_subset_Ico_iff hu.1.le).mpr ⟨le_rfl, hu.2⟩)
  have hb := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hP).2 htrunc
  rw [ENNReal.toReal_ofReal hnonneg] at hb
  exact hle.trans hb

/-- [internal] Both terminal exponents and the correction are continuous
on the half-open label interval. No value at its missing endpoint is used. -/
theorem terminal_integrands_continuousOn {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) :
    ContinuousOn (fun u => signedExpIntegrand S u 0) (Ico ui 0) ∧
      ContinuousOn (fun u => positiveExpIntegrand S u 0) (Ico ui 0) ∧
      ContinuousOn (fun u => chargeCorrection S u 0) (Ico ui 0) := by
  have hp (u : ℝ) (hu : u ∈ Ico ui 0) : (u, 0) ∈ origDomain ui :=
    ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
  have cr : ContinuousOn (fun u => S.r u 0) (Ico ui 0) :=
    h.solution.cont_r.comp (continuous_id.prodMk continuous_const).continuousOn hp
  have cn : ContinuousOn (fun u => S.nu u 0) (Ico ui 0) :=
    h.solution.cont_nu.comp (continuous_id.prodMk continuous_const).continuousOn hp
  have cm : ContinuousOn (fun u => S.m u 0) (Ico ui 0) :=
    h.solution.cont_m.comp (continuous_id.prodMk continuous_const).continuousOn hp
  have cq : ContinuousOn (fun u => S.Q u 0) (Ico ui 0) :=
    h.solution.cont_Q.comp (continuous_id.prodMk continuous_const).continuousOn hp
  have hr (u : ℝ) (hu : u ∈ Ico ui 0) : S.r u 0 ≠ 0 := (h.solution.r_pos _ (hp u hu) hu.2).ne'
  have hg (u : ℝ) (hu : u ∈ Ico ui 0) : 1 - S.mu u 0 ≠ 0 :=
    (h.solution.one_sub_mu_pos _ (hp u hu)).ne'
  have cμ : ContinuousOn (fun u => S.mu u 0) (Ico ui 0) :=
    (continuousOn_const.mul cm).div cr hr
  have cg : ContinuousOn (fun u => 1 - S.mu u 0) (Ico ui 0) := continuousOn_const.sub cμ
  exact ⟨(cn.neg.mul (cμ.sub ((cq.pow 2).div (cr.pow 2)
      (fun u hu => pow_ne_zero _ (hr u hu))))).div (cg.mul cr)
      (fun u hu => mul_ne_zero (hg u hu) (hr u hu)),
    (cn.neg.mul cμ).div (cg.mul cr) (fun u hu => mul_ne_zero (hg u hu) (hr u hu)),
    (cn.neg.mul (cq.pow 2)).div (cg.mul (cr.pow 3))
      (fun u hu => mul_ne_zero (hg u hu) (pow_ne_zero _ (hr u hu)))⟩

private theorem terminal_charge_cubic_bound {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u ∈ Ico ui 0, S.Q u 0 ^ 2 ≤ K * S.r u 0 ^ 3 := by
  obtain ⟨C, hC, hQ⟩ := terminal_charge_bound h hs
  let T := fun u => ‖S.xi u 0‖ ^ 2 / ((-S.nu u 0) * S.r u 0)
  let E := ∫ u in Ico ui 0, T u
  have hi : IntegrableOn T (Ico ui 0) := terminal_flux_integrable h hs
  have hn : ∀ᵐ u ∂volume.restrict (Ico ui 0), 0 ≤ T u := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
    have hp : (u, 0) ∈ origDomain ui := ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
    exact div_nonneg (sq_nonneg _) (mul_nonneg (neg_pos.mpr (h.solution.nu_neg _ hp)).le
      (h.solution.r_pos _ hp hu.2).le)
  have hEn : 0 ≤ E := integral_nonneg_of_ae hn
  have hRi := h.solution.r_pos (ui, 0) ⟨le_rfl, h.ui_neg, h.ui_neg.le, le_rfl⟩ h.ui_neg
  refine ⟨C * e ^ 2 * E * S.r ui 0, by positivity, ?_⟩
  intro u hu
  have hR := h.solution.r_pos (u, 0) ⟨hu.1, hu.2, hu.2.le, le_rfl⟩ hu.2
  have hF : (∫ s in u..0, T s) ≤ E := by
    rw [intervalIntegral.integral_of_le hu.2.le, restrict_Ioc_eq_restrict_Icc,
      ← restrict_Ico_eq_restrict_Icc]
    exact setIntegral_mono_set hi hn (Eventually.of_forall (Ico_subset_Ico_left hu.1))
  have hL : 0 ≤ 1 + Real.log (S.r ui 0 / S.r u 0) := by
    have hl := Real.log_nonneg ((one_le_div hR).2
      ((terminal_radius_strictAntiOn h.solution).antitoneOn ⟨le_rfl, h.ui_neg⟩ hu hu.1))
    linarith only [hl]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hRi hR)
  calc
    _ ≤ C * e ^ 2 * S.r u 0 ^ 4 * (1 + Real.log (S.r ui 0 / S.r u 0)) *
        (∫ s in u..0, T s) := hQ u hu
    _ ≤ C * e ^ 2 * S.r u 0 ^ 4 * (1 + Real.log (S.r ui 0 / S.r u 0)) * E :=
      mul_le_mul_of_nonneg_left hF (by positivity)
    _ ≤ C * e ^ 2 * S.r u 0 ^ 4 * (S.r ui 0 / S.r u 0) * E := by
      apply mul_le_mul_of_nonneg_right _ hEn
      exact mul_le_mul_of_nonneg_left (by linarith only [hlog]) (by positivity)
    _ = _ := by field_simp [hR.ne']

/-- [internal]
The nonnegative terminal charge correction is integrable on the entire
terminal interval (charged_SF_new_version.tex:L1016–1020). The proof derives its majorant
from the sharp charge estimate and positive terminal gap. -/
theorem terminal_correction_integrable {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    IntegrableOn (fun u => chargeCorrection S u 0) (Ico ui 0) ∧
      (∫⁻ u in Ico ui 0, ENNReal.ofReal (chargeCorrection S u 0)) < ⊤ := by
  obtain ⟨K, hK, hQ⟩ := terminal_charge_cubic_bound h hs
  obtain ⟨δ, hδ, hgap⟩ := (terminal_gap_and_flux ui e S h.ui_neg h.solution h.gauge
    h.mu h.radius h.datumAC hs).1
  have hn (u : ℝ) (hu : u ∈ Ico ui 0) : 0 ≤ chargeCorrection S u 0 := by
    have hp : (u, 0) ∈ origDomain ui := ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
    exact div_nonneg (mul_nonneg (neg_pos.mpr (h.solution.nu_neg _ hp)).le (sq_nonneg _))
      (mul_nonneg (h.solution.one_sub_mu_pos _ hp).le
        (pow_nonneg (h.solution.r_pos _ hp hu.2).le 3))
  have hi : IntegrableOn (fun u => chargeCorrection S u 0) (Ico ui 0) := by
    have hni : IntegrableOn (fun u => -S.nu u 0) (Ico ui 0) := by
      simpa only [pow_zero, mul_one] using
        terminal_radius_power_integrable h.ui_neg h.solution h.mu 0
    apply Integrable.mono' (hni.const_mul (K / δ))
      ((terminal_integrands_continuousOn h).2.2.aestronglyMeasurable measurableSet_Ico)
    filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
    have hp : (u, 0) ∈ origDomain ui := ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
    have hR := h.solution.r_pos _ hp hu.2
    have hnu := neg_pos.mpr (h.solution.nu_neg _ hp)
    have hg := h.solution.one_sub_mu_pos _ hp
    rw [Real.norm_eq_abs, abs_of_nonneg (hn u hu)]
    have hQr := (div_le_iff₀ (pow_pos hR 3)).2 (hQ u hu)
    calc
      _ = ((-S.nu u 0) * (S.Q u 0 ^ 2 / S.r u 0 ^ 3)) / (1 - S.mu u 0) := by
        unfold chargeCorrection
        field_simp
      _ ≤ ((-S.nu u 0) * K) / (1 - S.mu u 0) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hQr hnu.le) hg.le
      _ ≤ ((-S.nu u 0) * K) / δ :=
        div_le_div_of_nonneg_left (mul_nonneg hnu.le hK) hδ (hgap u hu)
      _ = _ := by ring
  refine ⟨hi, ?_⟩
  have he : (fun u => ENNReal.ofReal (chargeCorrection S u 0)) =ᵐ[volume.restrict (Ico ui 0)]
      (fun u => ‖chargeCorrection S u 0‖ₑ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hn u hu)]
  rw [lintegral_congr_ae he]
  exact hi.2

/-- [node prop:charged-terminal-equivalence#signed-to-positive]
A bounded signed terminal exponent implies a finite positive terminal
integral (charged_SF_new_version.tex:L1022–1026). The proof first bounds proper real
truncations, then uses monotone convergence only for the nonnegative integrand. -/
theorem signed_to_positive {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    PositiveTerminalFinite ui S := by
  have hi := (terminal_correction_integrable h hs).1
  have hn : ∀ᵐ u ∂volume.restrict (Ico ui 0), 0 ≤ chargeCorrection S u 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
    have hp : (u, 0) ∈ origDomain ui := ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
    exact div_nonneg (mul_nonneg (neg_pos.mpr (h.solution.nu_neg _ hp)).le (sq_nonneg _))
      (mul_nonneg (h.solution.one_sub_mu_pos _ hp).le
        (pow_nonneg (h.solution.r_pos _ hp hu.2).le 3))
  obtain ⟨B, hB⟩ := hs
  obtain ⟨v, hvmono, hv, hvlim⟩ := exists_seq_strictMono_tendsto' h.ui_neg
  apply lt_top_iff_ne_top.mpr
  apply lintegral_ofReal_Ico_ne_top_of_intervalIntegral_bounds
    (C := B + ∫ u in Ico ui 0, chargeCorrection S u 0)
    hvmono.monotone (fun n => (hv n).2) hvlim (fun n => (hv n).1.le)
  · intro n
    exact (incoming_integrands_continuousOn h.solution (hv n).2
      ((inSeg_subset_origDomain_iff (hv n).1.le).2
        ⟨le_rfl, (hv n).2, (hv n).2.le, le_rfl⟩)).2.1.intervalIntegrable_of_Icc (hv n).1.le
  · intro u hu
    have hp : (u, 0) ∈ origDomain ui := ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
    exact positive_integrand_nonneg h.solution hp hu.2 (h.mu _ hp).1
  intro n
  have hseg : inSeg ui (v n) 0 ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff (hv n).1.le).2
      ⟨le_rfl, (hv n).2, (hv n).2.le, le_rfl⟩
  have hc := incoming_integrands_continuousOn h.solution (hv n).2 hseg
  have he : (∫ u in ui..v n, positiveExpIntegrand S u 0) =
      (∫ u in ui..v n, signedExpIntegrand S u 0) +
        ∫ u in ui..v n, chargeCorrection S u 0 := by
    rw [← intervalIntegral.integral_add (f := fun u => signedExpIntegrand S u 0)
      (g := fun u => chargeCorrection S u 0) (hc.1.intervalIntegrable_of_Icc (hv n).1.le)
      (hc.2.2.intervalIntegrable_of_Icc (hv n).1.le)]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (hv n).1.le] at hu
    have hp := hseg (show (u, 0) ∈ inSeg ui (v n) 0 from ⟨hu.1, hu.2, rfl⟩)
    exact positive_eq_signed_add_correction (h.solution.r_pos _ hp (hu.2.trans_lt (hv n).2)).ne'
      (h.solution.one_sub_mu_pos _ hp).ne'
  have hb := hB (mem_image_of_mem (fun u => ∫ s in ui..u, signedExpIntegrand S s 0) (hv n))
  have hcor : (∫ u in ui..v n, chargeCorrection S u 0) ≤
      ∫ u in Ico ui 0, chargeCorrection S u 0 := by
    rw [intervalIntegral.integral_of_le (hv n).1.le, restrict_Ioc_eq_restrict_Icc,
      ← restrict_Ico_eq_restrict_Icc]
    exact setIntegral_mono_set hi hn
      (Eventually.of_forall (Ico_subset_Ico_right (hv n).2.le))
  linarith only [he, hb, hcor]

/-- [internal] Finite positive terminal flux has an ordinary integral.
Finiteness is supplied before the extended-to-real integral bridge. -/
theorem terminal_positive_integrable_of_finite {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hp : PositiveTerminalFinite ui S) :
    IntegrableOn (fun u => positiveExpIntegrand S u 0) (Ico ui 0) := by
  apply integrableOn_of_lintegral_ofReal_ne_top
    ((terminal_integrands_continuousOn h).2.1.aestronglyMeasurable measurableSet_Ico) ?_ hp.ne
  filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
  have hpoint : (u, 0) ∈ origDomain ui := ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
  exact positive_integrand_nonneg h.solution hpoint hu.2 (h.mu _ hpoint).1

/-- [internal] The signed integrand is absolutely integrable once the positive
integral and charge correction have been proved finite. -/
theorem terminal_signed_integrable {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    IntegrableOn (fun u => signedExpIntegrand S u 0) (Ico ui 0) := by
  apply ((terminal_positive_integrable_of_finite h (signed_to_positive h hs)).sub
    (terminal_correction_integrable h hs).1).congr
  filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
  have hp : (u, 0) ∈ origDomain ui := ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
  have he := positive_eq_signed_add_correction (h.solution.r_pos _ hp hu.2).ne'
    (h.solution.one_sub_mu_pos _ hp).ne'
  change positiveExpIntegrand S u 0 = signedExpIntegrand S u 0 + chargeCorrection S u 0 at he
  change positiveExpIntegrand S u 0 - chargeCorrection S u 0 = signedExpIntegrand S u 0
  linarith only [he]

end EmcsfAcExtension.Global.Terminal

namespace EmcsfAcExtension.Global

/-- [node eq:charged-terminal-correction]
Canonical integrability of the terminal charge correction,
charged_SF_new_version.tex:L1016–1020; no endpoint trace is assumed. -/
theorem charged_terminal_correction {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    IntegrableOn (fun u => chargeCorrection S u 0) (Ico ui 0) ∧
      (∫⁻ u in Ico ui 0, ENNReal.ofReal (chargeCorrection S u 0)) < ⊤ := by
  exact Terminal.terminal_correction_integrable h hs

end EmcsfAcExtension.Global
