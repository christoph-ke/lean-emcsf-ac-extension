module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Global.Calculus.Endpoint
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Mass comparison on an adaptive outgoing exterior

All radial integrals are written in the original outgoing label with their
Jacobian `λ`. In particular, no radial inverse or pointwise trace of a rough
derivative is introduced. Source: `charged_SF_new_version.tex:L1140–L1154`.
-/

public section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Exterior

variable {ui e : ℝ} {S : Fields}

private theorem mass_density_nonneg (h : OriginalData ui e S) {u v : ℝ}
    (hp : (u, v) ∈ origDomain ui) : 0 ≤ S.mV u v := by
  have hl := (h.solution.lam_pos (u, v) hp).le
  have hg := (h.solution.one_sub_mu_pos (u, v) hp).le
  exact add_nonneg (div_nonneg (mul_nonneg hg (sq_nonneg _)) (by positivity))
    (div_nonneg (mul_nonneg (sq_nonneg _) hl) (by positivity))

/-- [internal]
The original nonnegative mass ratio gives nonnegative mass, including
the existing axis. No exterior gap or terminal estimate is assumed. -/
theorem mass_nonneg (h : OriginalData ui e S) {u v : ℝ}
    (hp : (u, v) ∈ origDomain ui) : 0 ≤ S.m u v := by
  rcases hp.2.2.1.eq_or_lt with huv | huv
  · change u = v at huv
    subst v
    rw [(h.solution.axis u hp).2.1]
  · have hr := h.solution.r_pos (u, v) hp huv
    have hm := (h.mu (u, v) hp).1
    unfold Fields.mu at hm
    have hb := (le_div_iff₀ hr).mp hm
    linarith

/-- [internal]
Outgoing mass monotonicity compares every original point to its terminal
point. The endpoint calculus includes the existing axis when `v = u`. -/
theorem mass_le_terminal (h : OriginalData ui e S) {u v : ℝ}
    (hp : (u, v) ∈ origDomain ui) : S.m u v ≤ terminalMass S u := by
  have hs : outSeg u v 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hp.2.2.2).2 ⟨hp.1, hp.2.1, hp.2.2.1, le_rfl⟩
  have hm := (Calculus.out_integralForm h.solution hp.2.2.1 hp.2.2.2 hs).2.2.1
  have hn := intervalIntegral.integral_nonneg (μ := volume) hp.2.2.2
    (fun v hv => mass_density_nonneg h (hs ⟨rfl, hv.1, hv.2⟩))
  rw [← hm.2] at hn
  exact sub_nonneg.mp hn

/-- [internal]
Radius increases on every outgoing row, so its terminal value is the
upper radius throughout the adaptive exterior. -/
theorem radius_le_terminal (h : OriginalData ui e S) {u v : ℝ}
    (hp : (u, v) ∈ origDomain ui) : S.r u v ≤ terminalRadius S u := by
  have hs : outSeg u v 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hp.2.2.2).2 ⟨hp.1, hp.2.1, hp.2.2.1, le_rfl⟩
  have hr := (Calculus.out_integralForm h.solution hp.2.2.1 hp.2.2.2 hs).1
  have hn := intervalIntegral.integral_nonneg (μ := volume) hp.2.2.2
    (fun v hv => (h.solution.lam_pos (u, v) (hs ⟨rfl, hv.1, hv.2⟩)).le)
  rw [← hr.2] at hn
  exact sub_nonneg.mp hn

/-- [internal]
At positive radius, the mass ratio is bounded by the terminal mass
divided by the same local radius. The coefficient `2` is universal. -/
theorem mu_le_terminal_div_radius (h : OriginalData ui e S) {u v : ℝ}
    (hp : (u, v) ∈ origDomain ui) (hr : 0 < S.r u v) :
    S.mu u v ≤ 2 * terminalMass S u / S.r u v := by
  unfold Fields.mu
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mass_le_terminal h hp) (by norm_num)) hr.le

/-- [internal]
The terminal radius collapse and the adaptive mass-to-radius limit give
the small exterior gap of `charged_SF_new_version.tex:L1140–L1141`. The terminal inputs
are explicit: radius collapse and a terminal radial mass function. The
profile limits and positivity are supplied by the adaptive construction.
The coefficient `2` is universal; the cutoff depends on all fixed inputs. -/
theorem exterior_small_gap_of_terminal (h : OriginalData ui e S)
    (M ell : ℝ → ℝ) {R₀ ε : ℝ} (hR : 0 < R₀) (hε : 0 < ε)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      0 < ell (terminalRadius S p.1) ∧
      S.mu p.1 p.2 ≤ 2 * terminalMass S p.1 / ell (terminalRadius S p.1) ∧
      2 * terminalMass S p.1 / ell (terminalRadius S p.1) ≤ ε := by
  have hrpos : ∀ᶠ u in 𝓝[<] (0 : ℝ), 0 < S.r u 0 := by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    exact h.solution.r_pos (u, 0) ⟨hu.1.le, hu.2, hu.2.le, le_rfl⟩ hu.2
  have ht : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcollapse, hrpos⟩
  have he : ∀ᶠ u in 𝓝[<] (0 : ℝ),
      u ∈ Ioo ui 0 ∧ S.r u 0 < R₀ ∧ M (S.r u 0) / ell (S.r u 0) < ε / 2 := by
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg, hcollapse.eventually (Iio_mem_nhds hR),
      (hsmall.comp ht).eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < ε / 2))]
      with u hu hr hm
    exact ⟨hu, hr, hm⟩
  obtain ⟨a, ha, hab⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp he
  let u₀ := max a ui / 2
  have hm0 : max a ui < 0 := max_lt ha h.ui_neg
  have hu₀ : u₀ ∈ Ioo ui 0 := by dsimp [u₀]; constructor <;> linarith [le_max_right a ui]
  refine ⟨u₀, hu₀, ?_⟩
  intro p hp
  have hup : p.1 ∈ Ioo a 0 := ⟨by
    have hb := hp.2.1
    dsimp [u₀] at hb
    linarith [le_max_left a ui], hp.1.2.1⟩
  have hb := hab hup
  have hRt : 0 < S.r p.1 0 := h.solution.r_pos (p.1, 0)
    ⟨hp.1.1, hp.1.2.1, hp.1.2.1.le, le_rfl⟩ hp.1.2.1
  have hl := hell _ ⟨hRt, hb.2.1.le⟩
  have hr : 0 < S.r p.1 p.2 := hl.trans_le hp.2.2
  have hm : 0 ≤ terminalMass S p.1 := mass_nonneg h
    ⟨hp.1.1, hp.1.2.1, hp.1.2.1.le, le_rfl⟩
  refine ⟨hl, (mu_le_terminal_div_radius h hp.1 hr).trans ?_, ?_⟩
  · exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hm) hl hp.2.2
  · have hmt := hmass p.1 ⟨hb.1.1.le, hb.1.2⟩
    dsimp [terminalMass, terminalRadius]
    rw [← hmt]
    have hv := hb.2.2
    rw [mul_div_assoc]
    linarith

private theorem scalar_density_le_four_mass (h : OriginalData ui e S) {u v : ℝ}
    (hp : (u, v) ∈ origDomain ui) (hg : 1 / 2 ≤ 1 - S.mu u v) :
    ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v ≤ 4 * S.mV u v := by
  have hl := h.solution.lam_pos (u, v) hp
  have halg : ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v =
      ‖S.theta u v‖ ^ 2 / S.lam u v := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl, div_pow]
    field_simp
  have he : 0 ≤ S.Q u v ^ 2 * S.lam u v / (2 * S.r u v ^ 2) := by positivity
  have hs : 0 ≤ ‖S.theta u v‖ ^ 2 / S.lam u v := by positivity
  have hm : S.mV u v = (1 - S.mu u v) / 2 *
      (‖S.theta u v‖ ^ 2 / S.lam u v) +
      S.Q u v ^ 2 * S.lam u v / (2 * S.r u v ^ 2) := by
    unfold Fields.mV
    ring
  rw [halg, hm]
  nlinarith only [he, mul_nonneg (sub_nonneg.mpr hg) hs]

/-- [internal]
On a proper exterior segment with gap at least `1/2`, its radial scalar
energy is at most four times the terminal mass. The constant `4` is
numerical, uniform in the solution, coupling, row and inner endpoint.
The consumer establishes the gap by `exterior_small_gap_of_terminal`. -/
theorem scalar_energy_le_of_gap (h : OriginalData ui e S) {u a : ℝ}
    (hua : u < a) (ha : a ≤ 0) (hs : outSeg u a 0 ⊆ origDomain ui)
    (hg : ∀ v ∈ Icc a 0, 1 / 2 ≤ 1 - S.mu u v) :
    (∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤
      4 * terminalMass S u := by
  have hl : ∀ v ∈ Icc a 0, S.lam u v ≠ 0 :=
    fun v hv => (h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)).ne'
  have hc := ((Calculus.continuousOn_out_section h.solution.cont_theta hs).div
    ((Complex.continuous_ofReal.comp_continuousOn
      (Calculus.continuousOn_out_section h.solution.cont_lam hs)))
    (fun v hv => Complex.ofReal_ne_zero.mpr (hl v hv))).norm.pow 2
  have hi := (hc.mul
    (Calculus.continuousOn_out_section h.solution.cont_lam hs)).intervalIntegrable_of_Icc
    (μ := volume) ha
  have hm := (h.solution.eq_out u a 0 hua ha hs).2.2.1
  have hb := intervalIntegral.integral_mono_on ha hi (hm.1.const_mul 4)
    (fun v hv => scalar_density_le_four_mass h (hs ⟨rfl, hv⟩) (hg v hv))
  rw [intervalIntegral.integral_const_mul, ← hm.2] at hb
  have hn := mass_nonneg h (hs ⟨rfl, le_rfl, ha⟩)
  dsimp [terminalMass]
  change (∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤
    4 * (S.m u 0 - S.m u a) at hb
  linarith

/-- [internal]
The exact inverse-radius moment on a proper outgoing interval. This
identity is uniform in the solution and interval and has no constant.
It uses the ordinary derivative of the radius, not a rough scalar trace. -/
theorem inverse_radius_moment (h : OriginalData ui e S) {u a : ℝ}
    (hua : u < a) (ha : a ≤ 0) (hs : outSeg u a 0 ⊆ origDomain ui) :
    (∫ v in a..0, S.lam u v / S.r u v ^ 2) =
      (S.r u a)⁻¹ - (S.r u 0)⁻¹ := by
  have hp := hs (show (u, 0) ∈ outSeg u a 0 from ⟨rfl, ha, le_rfl⟩)
  have hs' : outSeg u u 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff hp.2.2.1).2 ⟨hp.1, hp.2.1, le_rfl, le_rfl⟩
  have hr (v : ℝ) (hv : v ∈ Icc a 0) : S.r u v ≠ 0 :=
    (h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have hd (v : ℝ) (hv : v ∈ Ioo a 0) :
      HasDerivAt (fun v => -(S.r u v)⁻¹) (S.lam u v / S.r u v ^ 2) v := by
    convert ((Local.IsSolution.hasDerivAt_radius_out h.solution hs'
      ⟨hua.trans hv.1, hv.2⟩).inv (hr v ⟨hv.1.le, hv.2.le⟩)).neg using 1
    ring
  have hi := (cl.div (cr.pow 2) (fun v hv => pow_ne_zero 2 (hr v hv))).intervalIntegrable_of_Icc
    (μ := volume) ha
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha
    (cr.inv₀ hr).neg hd hi
  simpa only [Pi.neg_apply, Pi.inv_apply, neg_sub_neg] using hf

/-- [internal]
Cauchy–Schwarz on a proper closed label interval. All coefficients are
numerical and independent of the functions and interval. -/
theorem integral_cauchy_schwarz {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b)) :
    (∫ x in a..b, f x * g x) ^ 2 ≤
      (∫ x in a..b, f x ^ 2) * (∫ x in a..b, g x ^ 2) := by
  have iff : IntervalIntegrable (fun x => f x ^ 2) volume a b :=
    (hf.pow 2).intervalIntegrable_of_Icc (μ := volume) hab
  have ifg : IntervalIntegrable (fun x => f x * g x) volume a b :=
    (hf.mul hg).intervalIntegrable_of_Icc (μ := volume) hab
  have igg : IntervalIntegrable (fun x => g x ^ 2) volume a b :=
    (hg.pow 2).intervalIntegrable_of_Icc (μ := volume) hab
  have hn (t : ℝ) : 0 ≤ (∫ x in a..b, g x ^ 2) * (t * t) +
      (2 * ∫ x in a..b, f x * g x) * t + ∫ x in a..b, f x ^ 2 := by
    have hp := intervalIntegral.integral_nonneg (μ := volume) hab
      (fun x _ => sq_nonneg (f x + t * g x))
    have he : (∫ x in a..b, (f x + t * g x) ^ 2) =
        (∫ x in a..b, f x ^ 2) + 2 * t * (∫ x in a..b, f x * g x) +
          t ^ 2 * (∫ x in a..b, g x ^ 2) := by
      calc
        _ = ∫ x in a..b, (f x ^ 2 + (2 * t) * (f x * g x)) + t ^ 2 * g x ^ 2 :=
          intervalIntegral.integral_congr (fun x _ => by ring)
        _ = _ := by
          rw [intervalIntegral.integral_add (iff.add (ifg.const_mul (2 * t)))
            (igg.const_mul (t ^ 2)),
            intervalIntegral.integral_add iff (ifg.const_mul (2 * t))]
          simp only [intervalIntegral.integral_const_mul]
    rw [he] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero hn
  dsimp [discrim] at hd
  nlinarith only [hd]

/-- [internal]
The scalar variation bound on a proper outgoing segment with gap at
least `1/2`. The coefficient `2` is numerical and uniform in all data.
The lower radius is the actual radius at the inner endpoint. -/
theorem scalar_variation_le_of_gap (h : OriginalData ui e S) {u a : ℝ}
    (hua : u < a) (ha : a ≤ 0) (hs : outSeg u a 0 ⊆ origDomain ui)
    (hg : ∀ v ∈ Icc a 0, 1 / 2 ≤ 1 - S.mu u v) :
    eVariationOn (S.phi u) (Icc a 0) ≤
      ENNReal.ofReal (2 * Real.sqrt (terminalMass S u / S.r u a)) := by
  have hr (v : ℝ) (hv : v ∈ Icc a 0) : 0 < S.r u v :=
    h.solution.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a 0) : 0 < S.lam u v :=
    h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)
  have cr := Calculus.continuousOn_out_section h.solution.cont_r hs
  have cl := Calculus.continuousOn_out_section h.solution.cont_lam hs
  have ct := Calculus.continuousOn_out_section h.solution.cont_theta hs
  let f := fun v => ‖S.theta u v‖ / Real.sqrt (S.lam u v)
  let g := fun v => Real.sqrt (S.lam u v) / S.r u v
  have hf : ContinuousOn f (Icc a 0) := ct.norm.div cl.sqrt
    (fun v hv => (Real.sqrt_pos.mpr (hl v hv)).ne')
  have hgc : ContinuousOn g (Icc a 0) := cl.sqrt.div cr (fun v hv => (hr v hv).ne')
  have hc := integral_cauchy_schwarz ha hf hgc
  have heq : (∫ v in a..0, f v ^ 2) =
      ∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc a 0 := by simpa only [uIcc_of_le ha] using hv
    dsimp [f]
    rw [div_pow, Real.sq_sqrt (hl v hv').le,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hl v hv'), div_pow]
    field_simp [(hl v hv').ne']
  have hgeq : (∫ v in a..0, g v ^ 2) = ∫ v in a..0, S.lam u v / S.r u v ^ 2 := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc a 0 := by simpa only [uIcc_of_le ha] using hv
    dsimp [g]
    rw [div_pow, Real.sq_sqrt (hl v hv').le]
  have hfg : (∫ v in a..0, f v * g v) = ∫ v in a..0, ‖S.phiV u v‖ := by
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc a 0 := by simpa only [uIcc_of_le ha] using hv
    dsimp [f, g, Fields.phiV]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr v hv')]
    field_simp [(Real.sqrt_pos.mpr (hl v hv')).ne', (hr v hv').ne']
  rw [heq, hgeq, hfg] at hc
  have hE := scalar_energy_le_of_gap h hua ha hs hg
  have hB := inverse_radius_moment h hua ha hs
  have hBnonneg : 0 ≤ ∫ v in a..0, S.lam u v / S.r u v ^ 2 :=
    intervalIntegral.integral_nonneg (μ := volume) ha
      (fun v hv => div_nonneg (hl v hv).le (sq_nonneg _))
  have htop := hr 0 ⟨ha, le_rfl⟩
  have hBlo : (∫ v in a..0, S.lam u v / S.r u v ^ 2) ≤ (S.r u a)⁻¹ := by
    rw [hB]
    exact sub_le_self _ (inv_nonneg.mpr htop.le)
  have hM : 0 ≤ terminalMass S u := mass_nonneg h (hs ⟨rfl, ha, le_rfl⟩)
  have hprod := mul_le_mul hE hBlo hBnonneg (mul_nonneg (by norm_num) hM)
  have hsq : (∫ v in a..0, ‖S.phiV u v‖) ^ 2 ≤
      (2 * Real.sqrt (terminalMass S u / S.r u a)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (div_nonneg hM (hr a ⟨le_rfl, ha⟩).le),
      show (2 : ℝ) ^ 2 = 4 by norm_num]
    simpa [div_eq_mul_inv, mul_assoc] using hc.trans hprod
  have hfinal : (∫ v in a..0, ‖S.phiV u v‖) ≤
      2 * Real.sqrt (terminalMass S u / S.r u a) := by
    nlinarith only [hsq, Real.sqrt_nonneg (terminalMass S u / S.r u a)]
  have hp := (h.solution.eq_out u a 0 hua ha hs).2.2.2.2.2.1
  rw [hp.1.eVariationOn_eq_integral_norm_of_eq_integral ha (fun v hv =>
    ((h.solution.eq_out u a v hua hv.1
      (fun _ hx => hs (outSeg_subset_outSeg le_rfl hv.2 hx))).2.2.2.2.2.1).eq_add_integral)]
  exact ENNReal.ofReal_le_ofReal hfinal

/-- [internal]
Radius is nondecreasing on every outgoing subinterval in the original
development. The identity at an existing axis endpoint is included. -/
theorem outgoing_radius_mono (h : OriginalData ui e S) {u a b : ℝ}
    (hua : u ≤ a) (hab : a ≤ b) (hs : outSeg u a b ⊆ origDomain ui) :
    S.r u a ≤ S.r u b := by
  have hr := (Calculus.out_integralForm h.solution hua hab hs).1
  have hn := intervalIntegral.integral_nonneg (μ := volume) hab
    (fun v hv => (h.solution.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le)
  rw [← hr.2] at hn
  exact sub_nonneg.mp hn

end EmcsfAcExtension.Global.Exterior

namespace EmcsfAcExtension.Global

open Exterior

/-- [internal]
Conditional consumer for `eq:charged-exterior-scalar-energy`,
`charged_SF_new_version.tex:L1141–L1147`. The terminal radius collapse and radial mass
function are explicit terminal inputs. The profile facts come from the
adaptive construction. The energy coefficient `4` and variation
coefficient `2` are numerical and uniform in every solution and row;
the late cutoff depends on the fixed terminal and profile inputs. -/
theorem charged_exterior_scalar_energy_of_terminal {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0)) :
    ∃ u₀ ∈ Ioo ui 0, ∀ u a, (u, a) ∈ adaptiveExterior S ui u₀ ell →
      (∫ v in a..0, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤
        4 * terminalMass S u ∧
      eVariationOn (S.phi u) (Icc a 0) ≤
        ENNReal.ofReal (2 * Real.sqrt (terminalMass S u / ell (terminalRadius S u))) := by
  obtain ⟨u₀, hu₀, hcut⟩ := exterior_small_gap_of_terminal h M ell hR
    (by norm_num : (0 : ℝ) < 1 / 4) hcollapse hmass hell hsmall
  refine ⟨u₀, hu₀, ?_⟩
  intro u a hp
  have hc := hcut (u, a) hp
  have hr : 0 < S.r u a := hc.1.trans_le hp.2.2
  have hua : u < a := by
    rcases hp.1.2.2.1.eq_or_lt with heq | hlt
    · change u = a at heq
      subst a
      rw [(h.solution.axis u hp.1).1] at hr
      exact False.elim (lt_irrefl _ hr)
    · exact hlt
  have ha := hp.1.2.2.2
  have hs : outSeg u a 0 ⊆ origDomain ui :=
    (outSeg_subset_origDomain_iff ha).2 ⟨hp.1.1, hp.1.2.1, hua.le, le_rfl⟩
  have hg (v : ℝ) (hv : v ∈ Icc a 0) : 1 / 2 ≤ 1 - S.mu u v := by
    have hrv := outgoing_radius_mono h hua.le hv.1
      (fun _ hx => hs (outSeg_subset_outSeg le_rfl hv.2 hx))
    have hvp : (u, v) ∈ adaptiveExterior S ui u₀ ell :=
      ⟨hs ⟨rfl, hv⟩, hp.2.1, hp.2.2.trans hrv⟩
    have hμ := (hcut (u, v) hvp).2.1.trans (hcut (u, v) hvp).2.2
    linarith
  refine ⟨scalar_energy_le_of_gap h hua ha hs hg,
    (scalar_variation_le_of_gap h hua ha hs hg).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.sqrt_le_sqrt
  have hM : 0 ≤ terminalMass S u := mass_nonneg h (hs ⟨rfl, ha, le_rfl⟩)
  exact div_le_div_of_nonneg_left hM hc.1 hp.2.2

namespace Exterior

/-- [internal]
Conditional consumer for `c:exterior#scalar-log-envelope`,
`charged_SF_new_version.tex:L1148–L1154`. The terminal logarithmic estimate is taken
in the exact original-label form of internal project record. The resulting
constant is `C+2`, depending only on that terminal constant; the late
cutoff may depend on the fixed solution and adaptive construction. -/
theorem scalar_log_envelope_of_terminal {ui e C : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) {R₀ : ℝ} (hR : 0 < R₀) (hC : 0 < C)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    0 < C + 2 ∧ ∃ u₀ ∈ Ioo ui 0, ∀ p ∈ adaptiveExterior S ui u₀ ell,
      ‖S.phi p.1 p.2‖ ≤ (C + 2) *
        (1 + Real.sqrt (Real.log (S.r ui 0 / S.r p.1 0))) := by
  obtain ⟨ug, hug, hgap⟩ := exterior_small_gap_of_terminal h M ell hR
    (by norm_num : (0 : ℝ) < 1 / 4) hcollapse hmass hell hsmall
  obtain ⟨ue, hue, henergy⟩ := charged_exterior_scalar_energy_of_terminal h M ell hR
    hcollapse hmass hell hsmall
  refine ⟨by linarith, max ug ue, ⟨lt_max_of_lt_left hug.1, max_lt hug.2 hue.2⟩, ?_⟩
  intro p hp
  have hpg : p ∈ adaptiveExterior S ui ug ell :=
    ⟨hp.1, (le_max_left ug ue).trans hp.2.1, hp.2.2⟩
  have hpe : p ∈ adaptiveExterior S ui ue ell :=
    ⟨hp.1, (le_max_right ug ue).trans hp.2.1, hp.2.2⟩
  have hg := hgap p hpg
  have hratio : terminalMass S p.1 / ell (terminalRadius S p.1) ≤ 1 := by
    have hq := hg.2.2
    rw [mul_div_assoc] at hq
    linarith
  have hsqrt : Real.sqrt (terminalMass S p.1 / ell (terminalRadius S p.1)) ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hratio
  have hvar := (henergy p.1 p.2 hpe).2
  have hd := (eVariationOn.edist_le (S.phi p.1)
    (show p.2 ∈ Icc p.2 0 from ⟨le_rfl, hp.1.2.2.2⟩)
    (show (0 : ℝ) ∈ Icc p.2 0 from ⟨hp.1.2.2.2, le_rfl⟩)).trans hvar
  rw [edist_dist] at hd
  have hdr : dist (S.phi p.1 p.2) (S.phi p.1 0) ≤
      2 * Real.sqrt (terminalMass S p.1 / ell (terminalRadius S p.1)) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hd
  have hd2 : ‖S.phi p.1 p.2 - S.phi p.1 0‖ ≤ 2 := by
    rw [dist_eq_norm] at hdr
    linarith only [hdr, hsqrt]
  calc
    ‖S.phi p.1 p.2‖ = ‖(S.phi p.1 p.2 - S.phi p.1 0) + S.phi p.1 0‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖S.phi p.1 p.2 - S.phi p.1 0‖ + ‖S.phi p.1 0‖ := norm_add_le _ _
    _ ≤ 2 + C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r p.1 0))) :=
      add_le_add hd2 (hphi p.1 ⟨hp.1.1, hp.1.2.1⟩)
    _ ≤ _ := by nlinarith only [Real.sqrt_nonneg (Real.log (S.r ui 0 / S.r p.1 0))]

/-- [internal]
For fixed coupling, scalar-envelope coefficient and positive initial
radius, the squared charged logarithmic scale vanishes at zero.
The constants are fixed before the radius tends to zero. -/
theorem logarithmic_scale_tendsto_zero (Ri C e : ℝ) (hRi : 0 < Ri) :
    Tendsto (fun R => e ^ 2 *
      (C * (1 + Real.sqrt (Real.log (Ri / R)))) ^ 2 * R ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hx : Tendsto (fun R : ℝ => R) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)
  have hlogR : Tendsto (fun R : ℝ => R ^ 2 * Real.log R) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_two, mul_comm] using
      tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 2)
  have hlog : Tendsto (fun R => R ^ 2 * Real.log (Ri / R)) (𝓝[>] 0) (𝓝 0) := by
    have hh := ((hx.pow 2).mul_const (Real.log Ri)).sub hlogR
    simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with R hRp
    rw [Real.log_div hRi.ne' hRp.ne']
    ring
  have hroot : Tendsto (fun R => R * Real.sqrt (Real.log (Ri / R)))
      (𝓝[>] 0) (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hlog
    simp only [Real.sqrt_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with R hRp
    change Real.sqrt (R ^ 2 * Real.log (Ri / R)) = R * Real.sqrt (Real.log (Ri / R))
    rw [Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq_eq_abs, abs_of_pos hRp]
  have hh := (((hx.add hroot).const_mul C).pow 2).const_mul (e ^ 2)
  simp only [add_zero, mul_zero, zero_pow (by decide : 2 ≠ 0)] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun R => by ring)

end Exterior

end EmcsfAcExtension.Global
