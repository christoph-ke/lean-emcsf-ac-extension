module

public import EmcsfAcExtension.Global.Terminal.Flux
public import EmcsfAcExtension.Global.Terminal.Mass
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Infra.AC.Quotient

/-! # Incoming optical identity and global expansion bounds

Raychaudhuri is obtained here by subtracting the logarithmic mass-gap
identity from the logarithmic expansion equation on proper incoming
sections. Radius collapse and nonnegative terminal substitution give exact
polynomial moments on every tail. This uses the original frozen AC class only.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Terminal

/-- [internal] The incoming logarithmic expansion equation on a proper
positive-radius section, with the frozen signed integrand. -/
theorem incoming_log_lambda_integralForm {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg a b v ⊆ D) :
    IntegralForm (fun s => Real.log (S.lam s v))
      (fun s => -signedExpIntegrand S s v) a b := by
  have cl := Calculus.continuousOn_in_section hS.cont_lam hseg
  have hl : ∀ s ∈ Icc a b, 0 < S.lam s v := fun s hs =>
    hS.lam_pos (s, v) (hseg ⟨hs.1, hs.2, rfl⟩)
  obtain ⟨c, hc, hcl⟩ := isCompact_Icc.exists_forall_le' cl hl
  have hs := Local.IsSolution.in_section hS hab hbv hseg
  have hac := hs.2.1.1.log_of_pos_le hc (by simpa only [uIcc_of_le hab] using hcl)
  have hi := ((incoming_integrands_continuousOn hS hbv hseg).1.neg).intervalIntegrable_of_Icc
    (μ := volume) hab
  apply integralForm_of_ac_of_ae_hasDerivAt hac hi
  rw [uIcc_of_le hab]
  apply (ae_restrict_iff' measurableSet_Icc).mp
  filter_upwards [hs.2.1.2, ae_restrict_mem measurableSet_Icc] with s hdl hmem
  have hp := hseg (show (s, v) ∈ inSeg a b v from ⟨hmem.1, hmem.2, rfl⟩)
  have hr := (hS.r_pos (s, v) hp (hmem.2.trans_lt hbv)).ne'
  have hg := (hS.one_sub_mu_pos (s, v) hp).ne'
  have hder := hdl.log (hl s hmem).ne'
  apply hder.congr_deriv
  change S.rUV s v / S.lam s v = -signedExpIntegrand S s v
  dsimp [Fields.rUV, signedExpIntegrand]
  field_simp [hr, hg, (hl s hmem).ne']

/-- [internal] Integrated incoming Raychaudhuri in the original AC class.
No separate optical or local-theory hypothesis is used. -/
theorem incoming_raychaudhuri {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v : ℝ} (hab : a ≤ b) (hbv : b < v)
    (hseg : inSeg a b v ⊆ D) :
    Real.log (S.lam b v / (1 - S.mu b v)) -
      Real.log (S.lam a v / (1 - S.mu a v)) =
        -(∫ s in a..b, ‖S.xi s v‖ ^ 2 / ((-S.nu s v) * S.r s v)) := by
  have hl := (incoming_log_lambda_integralForm hS hab hbv hseg).2
  rw [intervalIntegral.integral_neg] at hl
  have hf := incoming_flux_identity hS hab hbv hseg
  have ha := hseg (show (a, v) ∈ inSeg a b v from ⟨le_rfl, hab, rfl⟩)
  have hb := hseg (show (b, v) ∈ inSeg a b v from ⟨hab, le_rfl, rfl⟩)
  rw [Real.log_div (hS.lam_pos (b, v) hb).ne' (hS.one_sub_mu_pos (b, v) hb).ne',
    Real.log_div (hS.lam_pos (a, v) ha).ne' (hS.one_sub_mu_pos (a, v) ha).ne']
  linarith only [hl, hf]

/-- [internal]
The expansion divided by the gap, and the expansion itself, have a global
positive upper bound at all original positive-radius points. The witness
depends only on the fixed solution's initial cone and is uniform in both
null labels. Existing axis points follow by continuous outgoing traces. -/
theorem lambda_gap_upper {ui e : ℝ} {S : Fields} (hui : ui < 0)
    (hS : IsSolution e S (origDomain ui))
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1) :
    ∃ C : ℝ, 0 < C ∧
      (∀ p ∈ origDomain ui, p.1 < p.2 → S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ C) ∧
      (∀ p ∈ origDomain ui, S.lam p.1 p.2 ≤ C) := by
  have hi : outSeg ui ui 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hui.le).2 ⟨le_rfl, hui, le_rfl, le_rfl⟩
  have cg : ContinuousOn (fun v => 1 - S.mu ui v) (Icc ui 0) :=
    continuousOn_const.sub (Local.continuousOn_mu_out hS hui hi)
  have cl := Calculus.continuousOn_out_section hS.cont_lam hi
  have cq := cl.div cg (fun v hv => (hS.one_sub_mu_pos (ui, v) (hi ⟨rfl, hv.1, hv.2⟩)).ne')
  obtain ⟨x, hx, hxmax⟩ := isCompact_Icc.exists_isMaxOn ⟨ui, le_rfl, hui.le⟩ cq
  let C := max 1 (S.lam ui x / (1 - S.mu ui x))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbound (p : ℝ × ℝ) (hp : p ∈ origDomain ui) (huv : p.1 < p.2) :
      S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ C := by
    have hs : inSeg ui p.1 p.2 ⊆ origDomain ui :=
      (inSeg_subset_origDomain_iff hp.1).2 ⟨le_rfl, hp.2.1, huv.le, hp.2.2.2⟩
    have he := incoming_raychaudhuri hS hp.1 huv hs
    have hf : 0 ≤ ∫ s in ui..p.1, ‖S.xi s p.2‖ ^ 2 / ((-S.nu s p.2) * S.r s p.2) := by
      apply intervalIntegral.integral_nonneg hp.1
      intro s hsp
      have hq := hs (show (s, p.2) ∈ inSeg ui p.1 p.2 from ⟨hsp.1, hsp.2, rfl⟩)
      exact div_nonneg (sq_nonneg _) (mul_nonneg (neg_pos.mpr (hS.nu_neg _ hq)).le
        (hS.r_pos _ hq (hsp.2.trans_lt huv)).le)
    have hip := hs (show (ui, p.2) ∈ inSeg ui p.1 p.2 from ⟨le_rfl, hp.1, rfl⟩)
    have hh := (Real.log_le_log_iff
      (div_pos (hS.lam_pos _ hp) (hS.one_sub_mu_pos _ hp))
      (div_pos (hS.lam_pos _ hip) (hS.one_sub_mu_pos _ hip))).mp
      (show Real.log (S.lam p.1 p.2 / (1 - S.mu p.1 p.2)) ≤
        Real.log (S.lam ui p.2 / (1 - S.mu ui p.2)) by linarith only [he, hf])
    exact hh.trans ((hxmax ⟨hp.1.trans hp.2.2.1, hp.2.2.2⟩).trans (le_max_right _ _))
  refine ⟨C, hC, hbound, ?_⟩
  intro p hp
  have hs : outSeg p.1 p.1 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hp.2.1.le).2 ⟨hp.1, hp.2.1, le_rfl, le_rfl⟩
  have hh : ∀ v ∈ Ioo p.1 0, S.lam p.1 v ≤ C := by
    intro v hv
    have hq : (p.1, v) ∈ origDomain ui := hs ⟨rfl, hv.1.le, hv.2.le⟩
    have hb := (div_le_iff₀ (hS.one_sub_mu_pos _ hq)).mp (hbound _ hq hv.1)
    have hμ := (hmu _ hq).1
    have hprod := mul_le_mul_of_nonneg_left (show 1 - S.mu p.1 v ≤ 1 by linarith only [hμ]) hC.le
    exact hb.trans (by simpa only [mul_one] using hprod)
  have cc := Calculus.continuousOn_out_section hS.cont_lam hs
  apply le_on_closure hh
  · simpa only [closure_Ioo hp.2.1.ne] using cc
  · exact continuousOn_const
  · rw [closure_Ioo hp.2.1.ne]
    exact ⟨hp.2.2.1, hp.2.2.2⟩

/-- [internal] The global optical bound controls the radius by label distance,
by integration from the existing axis. The supplied constant is uniform in
the original point. -/
theorem radius_le_of_lambda_upper {ui e C : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (hC : ∀ p ∈ origDomain ui, S.lam p.1 p.2 ≤ C) {u v : ℝ}
    (hp : (u, v) ∈ origDomain ui) : S.r u v ≤ C * (v - u) := by
  have hs : outSeg u u v ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hp.2.2.1).2 ⟨hp.1, hp.2.1, le_rfl, hp.2.2.2⟩
  have he := (Calculus.out_integralForm hS le_rfl hp.2.2.1 hs).1.2
  have hb := intervalIntegral.integral_mono_on hp.2.2.1
    ((Calculus.out_integralForm hS le_rfl hp.2.2.1 hs).1.1)
    (intervalIntegrable_const (c := C)) (fun s hs' => hC (u, s) (hs ⟨rfl, hs'.1, hs'.2⟩))
  rw [← he, (hS.axis u (hs ⟨rfl, le_rfl, hp.2.2.1⟩)).1, sub_zero,
    intervalIntegral.integral_const] at hb
  simpa only [smul_eq_mul, mul_comm] using hb

/-- [internal]
The terminal radius tends to zero, with no signed or positive terminal
premise (charged_SF_new_version.tex:L967–970). -/
theorem terminal_radius_collapse {ui e : ℝ} {S : Fields} (hui : ui < 0)
    (hS : IsSolution e S (origDomain ui))
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1) :
    Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0) := by
  obtain ⟨C, _, _, hC⟩ := lambda_gap_upper hui hS hmu
  have ht : Tendsto (fun u : ℝ => C * (0 - u)) (𝓝[<] 0) (𝓝 0) := by
    simpa only [id_eq, sub_self, mul_zero] using
      ((tendsto_const_nhds.mul (tendsto_const_nhds.sub
        (continuous_id.tendsto 0))).mono_left nhdsWithin_le_nhds :
        Tendsto (fun u : ℝ => C * (0 - u)) (𝓝[<] 0) (𝓝 (C * (0 - 0))))
  apply squeeze_zero' ?_ ?_ ht
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hui)] with u hu hui'
    exact (hS.r_pos (u, 0) ⟨hui'.le, hu, hu.le, le_rfl⟩ hu).le
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hui)] with u hu hui'
    exact radius_le_of_lambda_upper hS hC ⟨hui'.le, hu, hu.le, le_rfl⟩

/-- [node prop:charged-terminal-equivalence#terminal-radius-collapse]
Radius is bounded by distance to the existing axis and the terminal radius
tends to zero (charged_SF_new_version.tex:L969–970). The positive constant depends on
the fixed development, uniformly in both original labels. -/
theorem terminal_radius_collapse_with_bound {ui e : ℝ} {S : Fields} (hui : ui < 0)
    (hS : IsSolution e S (origDomain ui))
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1) :
    (∃ C > 0, ∀ p ∈ origDomain ui, S.r p.1 p.2 ≤ C * (p.2 - p.1)) ∧
      Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0) := by
  obtain ⟨C, hC, _, hlam⟩ := lambda_gap_upper hui hS hmu
  exact ⟨⟨C, hC, fun _ hp => radius_le_of_lambda_upper hS hlam hp⟩,
    terminal_radius_collapse hui hS hmu⟩

/-- [internal] The terminal radius is strictly decreasing on its entire
half-open original label interval. -/
theorem terminal_radius_strictAntiOn {ui e : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) :
    StrictAntiOn (fun u => S.r u 0) (Ico ui 0) := by
  intro a ha b hb hab
  have hseg : inSeg a b 0 ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff hab.le).2 ⟨ha.1, hb.2, hb.2.le, le_rfl⟩
  have cn := Calculus.continuousOn_in_section hS.cont_nu hseg
  have hn (s : ℝ) (hs : s ∈ Icc a b) : 0 < -S.nu s 0 :=
    neg_pos.mpr (hS.nu_neg (s, 0) (hseg ⟨hs.1, hs.2, rfl⟩))
  have hi := intervalIntegral.integral_pos hab cn.neg
    (fun s hs => (hn s ⟨hs.1.le, hs.2⟩).le) ⟨a, ⟨le_rfl, hab.le⟩, hn a ⟨le_rfl, hab.le⟩⟩
  change 0 < ∫ s in a..b, -S.nu s 0 at hi
  rw [intervalIntegral.integral_neg, ← (hS.eq_in a b 0 hab.le hb.2 hseg).1.2] at hi
  linarith only [hi]

/-- [internal] The ordinary incoming radius derivative holds at every
interior terminal label, as required by one-dimensional change of variables. -/
theorem terminal_radius_hasDerivAt {ui e : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) {u : ℝ} (hu : u ∈ Ioo ui 0) :
    HasDerivAt (fun s => S.r s 0) (S.nu u 0) u := by
  have cn : ContinuousOn (fun s => S.nu s 0) (Ioo ui 0) :=
    hS.cont_nu.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs.1.le, hs.2, hs.2.le, le_rfl⟩)
  apply Local.hasDerivAt_of_integralForm_interior hu cn
  intro a b ha hab hb
  exact (hS.eq_in a b 0 hab hb
    ((inSeg_subset_origDomain_iff hab).2 ⟨ha.le, hb, hb.le, le_rfl⟩)).1

/-- [internal] The open terminal label interval has exactly the open positive
radius interval as image; there is no assumed trace at the missing vertex. -/
theorem terminal_radius_image_Ioo {ui e : ℝ} {S : Fields} (hui : ui < 0)
    (hS : IsSolution e S (origDomain ui))
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1) :
    (fun u => S.r u 0) '' Ioo ui 0 = Ioo 0 (S.r ui 0) := by
  have ha := terminal_radius_strictAntiOn hS
  have ht := terminal_radius_collapse hui hS hmu
  ext q
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨hS.r_pos (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩ hu.2,
      ha ⟨le_rfl, hui⟩ ⟨hu.1.le, hu.2⟩ hu.1⟩
  · intro hq
    have hbiEv : ∀ᶠ b : ℝ in 𝓝[<] 0, ui < b := nhdsWithin_le_nhds (Ioi_mem_nhds hui)
    have hb0Ev : ∀ᶠ b : ℝ in 𝓝[<] 0, b < 0 := self_mem_nhdsWithin
    have hh := hbiEv.and (ht.eventually (Iio_mem_nhds hq.1))
    obtain ⟨b, hb0, hbi, hbq⟩ := (hb0Ev.and hh).exists
    have hs : inSeg ui b 0 ⊆ origDomain ui :=
      (inSeg_subset_origDomain_iff hbi.le).2 ⟨le_rfl, hb0, hb0.le, le_rfl⟩
    obtain ⟨u, hu, heq⟩ := intermediate_value_Icc' hbi.le
      (Calculus.continuousOn_in_section hS.cont_r hs) ⟨hbq.le, hq.2.le⟩
    have hui' : ui < u := by
      apply lt_of_le_of_ne hu.1
      intro he
      subst u
      exact hq.2.ne heq.symm
    exact ⟨u, ⟨hui', hu.2.trans_lt hb0⟩, heq⟩

/-- [internal] Terminal radius substitution for arbitrary nonnegative extended
integrands. It first uses the open intervals and then removes null endpoints;
neither finiteness nor a real-valued conversion is assumed. -/
theorem lintegral_terminal_radius {ui e : ℝ} {S : Fields} (hui : ui < 0)
    (hS : IsSolution e S (origDomain ui))
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ R in Ioc 0 (S.r ui 0), f R) =
      ∫⁻ u in Ico ui 0, ENNReal.ofReal (-S.nu u 0) * f (S.r u 0) := by
  calc
    _ = ∫⁻ R in Ioo 0 (S.r ui 0), f R := by
      rw [restrict_Ioc_eq_restrict_Icc, restrict_Ioo_eq_restrict_Icc]
    _ = ∫⁻ u in Ioo ui 0, ENNReal.ofReal (-S.nu u 0) * f (S.r u 0) := by
      rw [← terminal_radius_image_Ioo hui hS hmu]
      exact lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn measurableSet_Ioo
        (fun u hu => (terminal_radius_hasDerivAt hS hu).hasDerivWithinAt)
        ((terminal_radius_strictAntiOn hS).antitoneOn.mono Ioo_subset_Ico_self) f
    _ = _ := by rw [restrict_Ioo_eq_restrict_Icc, restrict_Ico_eq_restrict_Icc]

/-- [internal] Radius substitution on any terminal tail uses the restricted
original solution. It never assigns a field value to the missing endpoint. -/
theorem lintegral_terminal_radius_tail {ui e a : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui))
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (ha : a ∈ Ico ui 0) (f : ℝ → ℝ≥0∞) :
    (∫⁻ R in Ioc 0 (S.r a 0), f R) =
      ∫⁻ u in Ico a 0, ENNReal.ofReal (-S.nu u 0) * f (S.r u 0) := by
  have hsub : origDomain a ⊆ origDomain ui := fun p hp =>
    ⟨ha.1.trans hp.1, hp.2⟩
  exact lintegral_terminal_radius ha.2 (Local.isSolution_mono hS hsub)
    (fun p hp => hmu p (hsub hp)) f

/-- [internal] Every nonnegative integer radius moment has finite mass in
the terminal label measure. The Jacobian is the actual incoming expansion;
no bound on that expansion at the missing endpoint is assumed. -/
theorem terminal_radius_power_integrable {ui e : ℝ} {S : Fields}
    (hui : ui < 0) (hS : IsSolution e S (origDomain ui))
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (n : ℕ) :
    IntegrableOn (fun u => (-S.nu u 0) * S.r u 0 ^ n) (Ico ui 0) := by
  have hp (u : ℝ) (hu : u ∈ Ico ui 0) : (u, 0) ∈ origDomain ui :=
    ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
  have cr : ContinuousOn (fun u => S.r u 0) (Ico ui 0) :=
    hS.cont_r.comp (continuous_id.prodMk continuous_const).continuousOn hp
  have cn : ContinuousOn (fun u => S.nu u 0) (Ico ui 0) :=
    hS.cont_nu.comp (continuous_id.prodMk continuous_const).continuousOn hp
  have hr := hS.r_pos (ui, 0) (hp ui ⟨le_rfl, hui⟩) hui
  have he := ofReal_intervalIntegral_eq_lintegral_of_continuousOn hr.le
    (continuous_id.pow n).continuousOn
    (fun R hR => pow_nonneg hR.1 n)
  simp only [Pi.pow_apply, id_eq] at he
  have hf : (∫⁻ R in Ioc 0 (S.r ui 0), ENNReal.ofReal (R ^ n)) ≠ ⊤ := by
    rw [restrict_Ioc_eq_restrict_Icc, ← restrict_Ico_eq_restrict_Icc, ← he]
    exact ENNReal.ofReal_ne_top
  rw [lintegral_terminal_radius hui hS hmu] at hf
  apply integrableOn_of_lintegral_ofReal_ne_top
    ((cn.neg.mul (cr.pow n)).aestronglyMeasurable measurableSet_Ico)
    ((ae_restrict_iff' measurableSet_Ico).2 (Eventually.of_forall fun u hu =>
      mul_nonneg (neg_pos.mpr (hS.nu_neg _ (hp u hu))).le
        (pow_nonneg (hS.r_pos _ (hp u hu) hu.2).le n)))
  convert hf using 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
  exact ENNReal.ofReal_mul (neg_pos.mpr (hS.nu_neg _ (hp u hu))).le

/-- [internal] Exact polynomial terminal moments, with the universal
coefficient `1/(n+1)`, uniformly in every terminal starting label. -/
theorem terminal_radius_power_integral {ui e a : ℝ} {S : Fields}
    (hui : ui < 0) (hS : IsSolution e S (origDomain ui))
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1)
    (ha : a ∈ Ico ui 0) (n : ℕ) :
    (∫ u in a..0, (-S.nu u 0) * S.r u 0 ^ n) = S.r a 0 ^ (n + 1) / (n + 1) := by
  have hi := (terminal_radius_power_integrable hui hS hmu n).mono_set
    (show Ico a 0 ⊆ Ico ui 0 from Ico_subset_Ico_left ha.1)
  have hn (u : ℝ) (hu : u ∈ Ico a 0) : 0 ≤ (-S.nu u 0) * S.r u 0 ^ n := by
    have hp : (u, 0) ∈ origDomain ui := ⟨ha.1.trans hu.1, hu.2, hu.2.le, le_rfl⟩
    exact mul_nonneg (neg_pos.mpr (hS.nu_neg _ hp)).le
      (pow_nonneg (hS.r_pos _ hp hu.2).le n)
  have he := lintegral_terminal_radius_tail hS hmu ha (fun R => ENNReal.ofReal (R ^ n))
  have he' : (∫⁻ u in Ico a 0, ENNReal.ofReal ((-S.nu u 0) * S.r u 0 ^ n)) =
      ∫⁻ R in Ioc 0 (S.r a 0), ENNReal.ofReal (R ^ n) := by
    rw [he]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
    exact ENNReal.ofReal_mul (neg_pos.mpr (hS.nu_neg (u, 0)
      ⟨ha.1.trans hu.1, hu.2, hu.2.le, le_rfl⟩)).le
  have hR := hS.r_pos (a, 0) ⟨ha.1, ha.2, ha.2.le, le_rfl⟩ ha.2
  have hp := ofReal_intervalIntegral_eq_lintegral_of_continuousOn hR.le
    (continuous_id.pow n).continuousOn (fun R hR => pow_nonneg hR.1 n)
  simp only [Pi.pow_apply, id_eq] at hp
  rw [restrict_Ioc_eq_restrict_Icc, ← restrict_Ico_eq_restrict_Icc, ← hp] at he'
  have hreal := integral_eq_lintegral_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ico).2 (Eventually.of_forall hn)) hi.aestronglyMeasurable
  rw [intervalIntegral.integral_of_le ha.2.le, restrict_Ioc_eq_restrict_Icc,
    ← restrict_Ico_eq_restrict_Icc, hreal, he', ENNReal.toReal_ofReal
      (intervalIntegral.integral_nonneg hR.le (fun R hR => pow_nonneg hR.1 n)),
    integral_pow]
  simp

/-- [node prop:charged-terminal-equivalence#lambda-gap-upper-bound]
Canonical global optical upper bound, charged_SF_new_version.tex:L962–970. The witness
depends on the initial cone of the fixed solution, uniformly in both labels. -/
theorem lambda_gap_upper_bound {ui e : ℝ} {S : Fields} (hui : ui < 0)
    (hS : IsSolution e S (origDomain ui))
    (hmu : ∀ p ∈ origDomain ui, 0 ≤ S.mu p.1 p.2 ∧ S.mu p.1 p.2 < 1) :
    ∃ C : ℝ, 0 < C ∧
      (∀ p ∈ origDomain ui, p.1 < p.2 → S.lam p.1 p.2 / (1 - S.mu p.1 p.2) ≤ C) ∧
      (∀ p ∈ origDomain ui, S.lam p.1 p.2 ≤ C) := by
  exact lambda_gap_upper hui hS hmu

end EmcsfAcExtension.Global.Terminal
