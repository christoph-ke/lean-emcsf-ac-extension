module

public import EmcsfAcExtension.Global.Exterior.ScalarEnergy
import EmcsfAcExtension.Global.Exterior.Charge
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Optical coefficients on the adaptive exterior

The signed radius coefficient is bounded using the ordinary mass and
the annular charge estimate (`charged_SF_new_version.tex:L1183–L1200`).
-/

public section

open Set MeasureTheory Filter Topology

namespace EmcsfAcExtension.Global.Exterior

private theorem continuousOn_optical_rhs {r m Q n l : ℝ → ℝ} {I : Set ℝ}
    (cr : ContinuousOn r I) (cm : ContinuousOn m I) (cQ : ContinuousOn Q I)
    (cn : ContinuousOn n I) (cl : ContinuousOn l I)
    (hr : ∀ x ∈ I, r x ≠ 0) (hg : ∀ x ∈ I, 1 - 2 * m x / r x ≠ 0) :
    ContinuousOn (fun x => n x * l x / r x *
      ((2 * m x / r x - Q x ^ 2 / r x ^ 2) / (1 - 2 * m x / r x))) I := by
  have cμ : ContinuousOn (fun x => 2 * m x / r x) I :=
    (continuousOn_const.mul cm).div cr hr
  exact ((cn.mul cl).div cr hr).mul
    ((cμ.sub ((cQ.pow 2).div (cr.pow 2) (fun x hx => pow_ne_zero 2 (hr x hx)))).div
      (continuousOn_const.sub cμ) hg)

private theorem log_integralForm {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (cf : ContinuousOn f (Icc a b)) (cg : ContinuousOn g (Icc a b))
    (hf : ∀ x ∈ Icc a b, 0 < f x)
    (heq : ∀ c ∈ Icc a b, ∀ d ∈ Icc a b, c ≤ d → IntegralForm f g c d) :
    IntegralForm (fun x => Real.log (f x)) (fun x => g x / f x) a b := by
  have hd (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt (fun x => Real.log (f x)) (g x / f x) x := by
    have hdf := Local.hasDerivAt_of_integralForm_interior hx (cg.mono Ioo_subset_Icc_self)
      (fun c d hc hcd hd => heq c ⟨hc.le, hcd.trans hd.le⟩
        d ⟨hc.le.trans hcd, hd.le⟩ hcd)
    exact hdf.log (hf x ⟨hx.1.le, hx.2.le⟩).ne'
  have hi := (cg.div cf (fun x hx => (hf x hx).ne')).intervalIntegrable_of_Icc
    (μ := volume) hab
  exact ⟨hi, (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (cf.log (fun x hx => (hf x hx).ne')) hd hi).symm⟩

/-- [internal]
The exact outgoing logarithmic expansion equation on a proper interval.
The integral form includes integrability of the literal optical density;
it follows from the original AC equations and proper-set positivity. -/
theorem out_log_nu_integralForm {ui e u a : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hua : u < a) (ha : a ≤ 0)
    (hs : outSeg u a 0 ⊆ origDomain ui) :
    IntegralForm (fun v => Real.log (-S.nu u v))
      (fun v => S.lam u v / S.r u v *
        ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v))) a 0 := by
  have hr (v : ℝ) (hv : v ∈ Icc a 0) : S.r u v ≠ 0 :=
    (h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
  have hn (v : ℝ) (hv : v ∈ Icc a 0) : S.nu u v < 0 :=
    h.solution.nu_neg (u, v) (hs ⟨rfl, hv⟩)
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cm := Calculus.continuousOn_out_section h.solution.cont_m hs
  have cQ := Calculus.continuousOn_out_section h.solution.cont_Q hs
  have cn := Calculus.continuousOn_out_section h.solution.cont_nu hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have cg : ContinuousOn (S.rUV u) (Icc a 0) :=
    continuousOn_optical_rhs cr cm cQ cn cl hr
      (fun v hv => (h.solution.one_sub_mu_pos (u, v) (hs ⟨rfl, hv⟩)).ne')
  have heq (c : ℝ) (hc : c ∈ Icc a 0) (d : ℝ) (hd : d ∈ Icc a 0) (hcd : c ≤ d) :
      IntegralForm (fun v => -S.nu u v) (fun v => -S.rUV u v) c d := by
    have hn := (h.solution.eq_out u c d (hua.trans_le hc.1) hcd
      (fun _ hx => hs (outSeg_subset_outSeg hc.1 hd.2 hx))).2.1
    refine ⟨hn.1.neg, ?_⟩
    rw [intervalIntegral.integral_neg, ← hn.2]
    ring
  have hlog := log_integralForm ha cn.neg cg.neg (fun v hv => neg_pos.mpr (hn v hv)) heq
  apply hlog.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIcc] with v hv
  rw [uIcc_of_le ha] at hv
  simp only [Pi.neg_apply]
  unfold Fields.rUV
  field_simp [(hn v hv).ne]

/-- [internal]
The exact incoming logarithmic lambda equation on a proper off-axis
segment. Its density is the literal radius source divided by lambda.
No terminal limit or exterior bound is assumed. -/
theorem in_log_lam_integralForm {ui e a b v : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hab : a ≤ b) (hbv : b < v)
    (hs : inSeg a b v ⊆ origDomain ui) :
    IntegralForm (fun u => Real.log (S.lam u v)) (fun u => S.rUV u v / S.lam u v) a b := by
  have hr (u : ℝ) (hu : u ∈ Icc a b) : S.r u v ≠ 0 :=
    (h.solution.r_pos (u, v) (hs ⟨hu.1, hu.2, rfl⟩) (hu.2.trans_lt hbv)).ne'
  have cr := Calculus.continuousOn_in_section h.solution.cont_r hs
  have cm := Calculus.continuousOn_in_section h.solution.cont_m hs
  have cQ := Calculus.continuousOn_in_section h.solution.cont_Q hs
  have cn := Calculus.continuousOn_in_section h.solution.cont_nu hs
  have cl := Calculus.continuousOn_in_section h.solution.cont_lam hs
  have cg : ContinuousOn (fun u => S.rUV u v) (Icc a b) :=
    continuousOn_optical_rhs cr cm cQ cn cl hr
      (fun u hu => (h.solution.one_sub_mu_pos (u, v) (hs ⟨hu.1, hu.2, rfl⟩)).ne')
  apply log_integralForm hab cl cg
    (fun u hu => h.solution.lam_pos (u, v) (hs ⟨hu.1, hu.2, rfl⟩))
  intro c hc d hd hcd
  exact (h.solution.eq_in c d v hcd (hd.2.trans_lt hbv)
    (fun _ hy => hs (inSeg_subset_inSeg hc.1 hd.2 hy))).2.1

/-- [internal]
The annular charge bound and exterior gap imply the signed optical
coefficient bound. The coefficient `132 = 2(2+64)` is numerical and
uniform in the original solution and every point of its exterior.
The consumer supplies charge from the annular argument and the gap
from `exterior_small_gap_of_terminal`. -/
theorem radial_optical_coefficient_of_charge {ui e u v : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hp : (u, v) ∈ origDomain ui)
    (hr : 0 < S.r u v) (hg : 1 / 2 ≤ 1 - S.mu u v)
    (hQ : S.Q u v ^ 2 / S.r u v ^ 2 ≤ 64 * terminalMass S u / S.r u v) :
    |(S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)| ≤
      132 * terminalMass S u / S.r u v := by
  have hμ := (h.mu (u, v) hp).1
  have hμb := mu_le_terminal_div_radius h hp hr
  have hq : 0 ≤ S.Q u v ^ 2 / S.r u v ^ 2 := by positivity
  have hgap := h.solution.one_sub_mu_pos (u, v) hp
  have hn := abs_sub (S.mu u v) (S.Q u v ^ 2 / S.r u v ^ 2)
  rw [abs_of_nonneg hμ, abs_of_nonneg hq] at hn
  change |S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2| ≤ S.mu u v + S.Q u v ^ 2 / S.r u v ^ 2 at hn
  have hm : 0 ≤ terminalMass S u / S.r u v := div_nonneg (mass_nonneg h
    (show (u, 0) ∈ origDomain ui from ⟨hp.1, hp.2.1, hp.2.1.le, le_rfl⟩)) hr.le
  rw [abs_div, abs_of_pos hgap]
  apply (div_le_iff₀ hgap).mpr
  simp only [mul_div_assoc] at hQ hμb ⊢
  nlinarith only [hn, hμb, hQ, mul_nonneg (sub_nonneg.mpr hg) hm]

/-- [internal]
The absolute incoming logarithmic coefficient is bounded by the
terminal-radius mass weight (`charged_SF_new_version.tex:L1196–L1200`). The coefficient
`264` is numerical and uniform in the solution, row and inner radius.
The row-optics consumer supplies the ratio bound `ν/ν_top ≤ 2`. -/
theorem incoming_optical_majorant_of_radial_bound {ui e u v ℓ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hp : (u, v) ∈ origDomain ui)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ S.r u v)
    (hnu : S.nu u v / S.nu u 0 ≤ 2)
    (hcoef : |(S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)| ≤
      132 * terminalMass S u / S.r u v) :
    |S.rUV u v / S.lam u v| ≤ 264 * (-S.nu u 0) * terminalMass S u / ℓ ^ 2 := by
  have hr := hℓ.trans_le hℓr
  have hl := h.solution.lam_pos (u, v) hp
  have hn : S.nu u v < 0 := h.solution.nu_neg (u, v) hp
  have hp0 : (u, 0) ∈ origDomain ui := ⟨hp.1, hp.2.1, hp.2.1.le, le_rfl⟩
  have hn0 : S.nu u 0 < 0 := h.solution.nu_neg (u, 0) hp0
  have hm : 0 ≤ terminalMass S u := mass_nonneg h hp0
  have hnub : -S.nu u v ≤ 2 * (-S.nu u 0) := by
    have he : S.nu u v / S.nu u 0 = (-S.nu u v) / (-S.nu u 0) := by rw [neg_div_neg_eq]
    rw [he] at hnu
    exact (div_le_iff₀ (neg_pos.mpr hn0)).mp hnu
  have halg : S.rUV u v / S.lam u v = S.nu u v / S.r u v *
      ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)) := by
    unfold Fields.rUV
    field_simp [hl.ne']
  have hb : |S.rUV u v / S.lam u v| ≤
      132 * (-S.nu u v) * terminalMass S u / S.r u v ^ 2 := by
    rw [halg, abs_mul, abs_div, abs_of_neg hn, abs_of_pos hr]
    calc
      _ ≤ (-S.nu u v) / S.r u v * (132 * terminalMass S u / S.r u v) :=
        mul_le_mul_of_nonneg_left hcoef (div_nonneg (neg_nonneg.mpr hn.le) hr.le)
      _ = _ := by ring
  have hnum : 132 * (-S.nu u v) * terminalMass S u ≤
      264 * (-S.nu u 0) * terminalMass S u := by
    nlinarith only [mul_le_mul_of_nonneg_right hnub hm]
  refine hb.trans ((div_le_div_of_nonneg_right hnum (sq_nonneg _)).trans ?_)
  have hN : 0 ≤ 264 * (-S.nu u 0) * terminalMass S u :=
    mul_nonneg (mul_nonneg (by norm_num) (neg_nonneg.mpr hn0.le)) hm
  exact div_le_div_of_nonneg_left hN (sq_pos_of_pos hℓ)
    (pow_le_pow_left₀ hℓ.le hℓr 2)

/-- [internal]
Integrating the signed radial coefficient gives the outgoing optical
comparison (`charged_SF_new_version.tex:L1187–L1191`). The coefficient `132` is
numerical and uniform in all solutions, rows and inner endpoints.
The annular charge consumer supplies the displayed coefficient bound. -/
theorem log_nu_ratio_le_of_radial_bound {ui e u a : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hua : u < a) (ha : a ≤ 0)
    (hs : outSeg u a 0 ⊆ origDomain ui)
    (hcoef : ∀ v ∈ Icc a 0,
      |(S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)| ≤
        132 * terminalMass S u / S.r u v) :
    |Real.log (S.nu u a / S.nu u 0)| ≤ 132 * terminalMass S u / S.r u a := by
  have hr (v : ℝ) (hv : v ∈ Icc a 0) : 0 < S.r u v :=
    h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a 0) : 0 < S.lam u v :=
    h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have hn (v : ℝ) (hv : v ∈ Icc a 0) : S.nu u v < 0 :=
    h.solution.nu_neg (u, v) (hs ⟨rfl, hv⟩)
  have hlog := out_log_nu_integralForm h hua ha hs
  have he : Real.log (S.nu u a / S.nu u 0) =
      -(∫ v in a..0, S.lam u v / S.r u v *
        ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v))) := by
    rw [show S.nu u a / S.nu u 0 = (-S.nu u a) / (-S.nu u 0) by rw [neg_div_neg_eq],
      Real.log_div (neg_pos.mpr (hn a ⟨le_rfl, ha⟩)).ne'
        (neg_pos.mpr (hn 0 ⟨ha, le_rfl⟩)).ne']
    have hf := hlog.2
    change Real.log (-S.nu u 0) - Real.log (-S.nu u a) = _ at hf
    linarith only [hf]
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have hi : IntervalIntegrable (fun v =>
      (132 * terminalMass S u) * (S.lam u v / S.r u v ^ 2)) volume a 0 :=
    ((cl.div (cr.pow 2)
      (fun v hv => pow_ne_zero 2 (hr v hv).ne')).const_mul _).intervalIntegrable_of_Icc ha
  have hpoint (v : ℝ) (hv : v ∈ Icc a 0) :
      ‖S.lam u v / S.r u v *
        ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v))‖ ≤
        (132 * terminalMass S u) * (S.lam u v / S.r u v ^ 2) := by
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (hl v hv), abs_of_pos (hr v hv)]
    calc
      _ ≤ S.lam u v / S.r u v * (132 * terminalMass S u / S.r u v) :=
        mul_le_mul_of_nonneg_left (hcoef v hv) (div_nonneg (hl v hv).le (hr v hv).le)
      _ = _ := by ring
  have hM : 0 ≤ terminalMass S u := mass_nonneg h (hs ⟨rfl, ha, le_rfl⟩)
  rw [he, abs_neg, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ v in a..0, ‖S.lam u v / S.r u v *
        ((S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v))‖ :=
      intervalIntegral.norm_integral_le_integral_norm ha
    _ ≤ ∫ v in a..0, (132 * terminalMass S u) * (S.lam u v / S.r u v ^ 2) :=
      intervalIntegral.integral_mono_on ha hlog.1.norm hi hpoint
    _ = (132 * terminalMass S u) * ((S.r u a)⁻¹ - (S.r u 0)⁻¹) := by
      rw [intervalIntegral.integral_const_mul, inverse_radius_moment h hua ha hs]
    _ ≤ (132 * terminalMass S u) * (S.r u a)⁻¹ :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (inv_nonneg.mpr (hr 0 ⟨ha, le_rfl⟩).le))
        (mul_nonneg (by norm_num) hM)
    _ = _ := by rw [div_eq_mul_inv]

/-- [internal]
Conditional terminal consumer for `c:exterior#radial-optical-coefficient`.
The annular charge estimate and the small exterior gap are discharged
by their terminal consumers. The coefficient `132` is numerical and
uniform in all data; the cutoff depends on the fixed terminal inputs. -/
theorem radial_optical_coefficient_of_terminal {ui e C : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      0 < ell (terminalRadius S p.1) ∧ 1 / 2 ≤ 1 - S.mu p.1 p.2 ∧
      |(S.mu p.1 p.2 - S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2) / (1 - S.mu p.1 p.2)| ≤
        132 * terminalMass S p.1 / S.r p.1 p.2 := by
  obtain ⟨ug, hug, hg⟩ := exterior_small_gap_of_terminal h M ell hR
    (by norm_num : (0 : ℝ) < 1 / 4) hcollapse hmass hell hsmall
  obtain ⟨uq, huq, hq⟩ := charged_exterior_charge_pointwise_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi
  refine ⟨max ug uq, ⟨lt_max_of_lt_left hug.1, max_lt hug.2 huq.2⟩, ?_⟩
  intro p hp
  have hpg : p ∈ adaptiveExterior S ui ug ell :=
    ⟨hp.1, (le_max_left ug uq).trans hp.2.1, hp.2.2⟩
  have hpq : p ∈ adaptiveExterior S ui uq ell :=
    ⟨hp.1, (le_max_right ug uq).trans hp.2.1, hp.2.2⟩
  have hgap : 1 / 2 ≤ 1 - S.mu p.1 p.2 := by
    have hb := (hg p hpg).2.1.trans (hg p hpg).2.2
    linarith
  refine ⟨(hg p hpg).1, hgap, radial_optical_coefficient_of_charge h hp.1
    ((hg p hpg).1.trans_le hp.2.2) hgap ?_⟩
  simpa only [mul_div_assoc] using (hq p hpq).2

end EmcsfAcExtension.Global.Exterior

namespace EmcsfAcExtension.Global

open Exterior

/-- [internal]
Conditional terminal consumer for `eq:charged-exterior-optics`,
`charged_SF_new_version.tex:L1187–L1191`. The coefficient `132` is numerical and
uniform in all data. Only the late cutoff depends on the fixed terminal
inputs and adaptive radius. All radial coefficient hypotheses of the
proper-row logarithmic identity are discharged here. -/
theorem charged_exterior_optics_of_terminal {ui e C : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      0 < ell (terminalRadius S p.1) ∧
      |Real.log (S.nu p.1 p.2 / S.nu p.1 0)| ≤
        132 * terminalMass S p.1 / ell (terminalRadius S p.1) := by
  obtain ⟨u₀, hu₀, hcoef⟩ := radial_optical_coefficient_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi
  refine ⟨u₀, hu₀, ?_⟩
  intro p hp
  have hc := hcoef p hp
  have hr : 0 < S.r p.1 p.2 := hc.1.trans_le hp.2.2
  have huv : p.1 < p.2 := by
    rcases hp.1.2.2.1.eq_or_lt with heq | hlt
    · have hpaxis : (p.1, p.1) ∈ origDomain ui :=
        ⟨hp.1.1, hp.1.2.1, le_rfl, hp.1.2.1.le⟩
      rw [← heq, (h.solution.axis p.1 hpaxis).1] at hr
      exact False.elim (lt_irrefl _ hr)
    · exact hlt
  have hs : outSeg p.1 p.2 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hp.1.2.2.2).2 ⟨hp.1.1, hp.1.2.1, huv.le, le_rfl⟩
  have hbound := log_nu_ratio_le_of_radial_bound h huv hp.1.2.2.2 hs (fun v hv => by
    apply (hcoef (p.1, v) _).2.2
    refine ⟨hs ⟨rfl, hv⟩, hp.2.1, ?_⟩
    exact hp.2.2.trans (outgoing_radius_mono h huv.le hv.1
      (fun _ hx => hs (outSeg_subset_outSeg le_rfl hv.2 hx))))
  refine ⟨hc.1, hbound.trans ?_⟩
  have hM : 0 ≤ terminalMass S p.1 := mass_nonneg h
    ⟨hp.1.1, hp.1.2.1, hp.1.2.1.le, le_rfl⟩
  exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hM) hc.1 hp.2.2

namespace Exterior

/-- [internal]
Uniformly vanishing logarithmic row control implies uniform convergence
of the incoming expansion ratio. The terminal radius collapse and mass
characterization are explicit. The consumer discharges the logarithmic
bound using `charged_exterior_optics_of_terminal`. -/
theorem uniform_nu_ratio_of_log_bound {ui e ub : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) (hub : ub ∈ Ioo ui 0)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hlog : ∀ p ∈ adaptiveExterior S ui ub ell,
      |Real.log (S.nu p.1 p.2 / S.nu p.1 0)| ≤
        132 * terminalMass S p.1 / ell (terminalRadius S p.1)) :
    ∀ ε : ℝ, 0 < ε → ∃ u₀ ∈ Ioo ub 0,
      ∀ p ∈ adaptiveExterior S ui u₀ ell, |S.nu p.1 p.2 / S.nu p.1 0 - 1| < ε := by
  have hrpos : ∀ᶠ u in 𝓝[<] (0 : ℝ), 0 < S.r u 0 := by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    exact h.solution.r_pos (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩ hu.2
  have hRt : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcollapse, hrpos⟩
  have hlimit := (hsmall.comp hRt).const_mul (132 : ℝ)
  simp only [mul_zero] at hlimit
  intro ε hε
  have hcont : ContinuousAt Real.exp (0 : ℝ) := Real.continuous_exp.continuousAt
  obtain ⟨η, hη, hηb⟩ := Metric.continuousAt_iff.mp hcont ε hε
  have he : ∀ᶠ u in 𝓝[<] (0 : ℝ),
      u ∈ Ioo ub 0 ∧ 132 * (M (S.r u 0) / ell (S.r u 0)) < η := by
    filter_upwards [Ioo_mem_nhdsLT hub.2, hlimit.eventually (Iio_mem_nhds hη)]
      with u hu hb
    exact ⟨hu, hb⟩
  obtain ⟨d, hd, hdb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
  let u₀ := max d ub / 2
  have hu₀ : u₀ ∈ Ioo ub 0 := by
    have hm0 := max_lt hd hub.2
    dsimp [u₀]
    constructor <;> linarith [le_max_right d ub]
  refine ⟨u₀, hu₀, ?_⟩
  intro p hp
  have hup : p.1 ∈ Ioo d 0 := by
    refine ⟨?_, hp.1.2.1⟩
    have hb := hp.2.1
    dsimp [u₀] at hb
    have hm0 := max_lt hd hub.2
    linarith [le_max_left d ub]
  have hb := (hdb hup).2
  have hmt := hmass p.1 ⟨hp.1.1, hp.1.2.1⟩
  have hraw : 132 * terminalMass S p.1 / ell (terminalRadius S p.1) < η := by
    dsimp [terminalMass, terminalRadius]
    rw [← hmt, mul_div_assoc]
    exact hb
  have hlog' := (hlog p ⟨hp.1, hu₀.1.le.trans hp.2.1, hp.2.2⟩).trans_lt hraw
  have hdist : dist (Real.log (S.nu p.1 p.2 / S.nu p.1 0)) 0 < η := by
    simpa only [Real.dist_eq, sub_zero] using hlog'
  have hn : S.nu p.1 p.2 < 0 := h.solution.nu_neg p hp.1
  have hnt : S.nu p.1 0 < 0 := h.solution.nu_neg (p.1, 0)
    ⟨hp.1.1, hp.1.2.1, hp.1.2.1.le, le_rfl⟩
  have hp_ratio : 0 < S.nu p.1 p.2 / S.nu p.1 0 := div_pos_of_neg_of_neg hn hnt
  simpa only [Real.exp_log hp_ratio, Real.exp_zero, Real.dist_eq] using hηb hdist

/-- [internal]
The incoming part of `c:exterior#uniform-optical-limits`, with all row
logarithmic bounds discharged by the terminal optics consumer. No
positive terminal lambda limit is needed for this ratio conclusion. -/
theorem uniform_nu_ratio_of_terminal {ui e C : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∀ ε : ℝ, 0 < ε → ∃ u₀ ∈ Ioo ui 0,
      ∀ p ∈ adaptiveExterior S ui u₀ ell, |S.nu p.1 p.2 / S.nu p.1 0 - 1| < ε := by
  obtain ⟨ub, hub, hlog⟩ := charged_exterior_optics_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi
  intro ε hε
  obtain ⟨u₀, hu₀, hb⟩ := uniform_nu_ratio_of_log_bound h M ell hub hcollapse hmass hsmall
    (fun p hp => (hlog p hp).2) ε hε
  exact ⟨u₀, ⟨hub.1.trans hu₀.1, hu₀.2⟩, hb⟩

/-- [internal]
Conditional terminal consumer for `c:exterior#incoming-optical-majorant`.
The radial coefficient and the optical ratio hypotheses are discharged
by their proved terminal consumers. The coefficient `264` is numerical
and uniform in all data; the late cutoff depends on the fixed inputs. -/
theorem incoming_optical_majorant_of_terminal {ui e C : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      0 < ell (terminalRadius S p.1) ∧
      |S.rUV p.1 p.2 / S.lam p.1 p.2| ≤
        264 * (-S.nu p.1 0) * terminalMass S p.1 / ell (terminalRadius S p.1) ^ 2 := by
  obtain ⟨ur, hur, hradial⟩ := radial_optical_coefficient_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi
  obtain ⟨un, hun, hnu⟩ := uniform_nu_ratio_of_terminal h M ell hR hC
    hcollapse hmass hell hellsmall hsmall hphi (1 / 2) (by norm_num)
  refine ⟨max ur un, ⟨lt_max_of_lt_left hur.1, max_lt hur.2 hun.2⟩, ?_⟩
  intro p hp
  have hr := hradial p ⟨hp.1, (le_max_left ur un).trans hp.2.1, hp.2.2⟩
  have hn := hnu p ⟨hp.1, (le_max_right ur un).trans hp.2.1, hp.2.2⟩
  refine ⟨hr.1, incoming_optical_majorant_of_radial_bound h hp.1 hr.1 hp.2.2 ?_ hr.2.2⟩
  have hb := (abs_lt.mp hn).2
  linarith

end Exterior

end EmcsfAcExtension.Global
