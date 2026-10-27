module

public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Global.Defs.Observation
import EmcsfAcExtension.Global.Interaction.Profiles
import EmcsfAcExtension.Global.Interaction.ConnectorScalar
import EmcsfAcExtension.Global.Interaction.ConnectorMass
import EmcsfAcExtension.Global.Renormalized.Incoming
import EmcsfAcExtension.Global.Terminal.Mass
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Infra.Gronwall

/-! # Multiplicative connector budgets

Ratified reading internal project record, `charged_SF_new_version.tex:L3835–L3837`, and approved
internal project record.
The squared scalar norm removes the unitary connection before applying
the AC integrating-factor inequality. Its electric forcing is proportional
to the preceding budget, including when that budget vanishes.
-/

public section

open Set MeasureTheory Complex
open scoped ComplexConjugate

namespace EmcsfAcExtension.Global.Interaction

private theorem scalar_square_algebra (y z q : ℂ) (k A w : ℝ) :
    2 * (conj y * ((w : ℂ) * (z + (k : ℂ) * y + q) - I * A * y)).re =
      w * (2 * k * ‖y‖ ^ 2 + 2 * (conj y * z).re + 2 * (conj y * q).re) := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

private theorem scalar_square_le (y z q : ℂ) {k ε w A D E : ℝ}
    (hw : 0 ≤ w) (hk : k ≤ ε) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hq : ‖q‖ ≤ D * Real.sqrt E) :
    2 * (conj y * ((w : ℂ) * (z + (k : ℂ) * y + q) - I * A * y)).re ≤
      ((2 * ε + 2) * ‖y‖ ^ 2 + ‖z‖ ^ 2 + D ^ 2 * E) * w := by
  rw [scalar_square_algebra]
  have hz : 2 * (conj y * z).re ≤ ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
    have hn := (Complex.re_le_norm (conj y * z)).trans_eq
      (by rw [norm_mul, norm_conj])
    nlinarith only [hn, sq_nonneg (‖y‖ - ‖z‖)]
  have hq2 : ‖q‖ ^ 2 ≤ D ^ 2 * E := by
    simpa only [mul_pow, Real.sq_sqrt hE] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (Real.sqrt_nonneg E))).mpr hq
  have he : 2 * (conj y * q).re ≤ ‖y‖ ^ 2 + D ^ 2 * E := by
    have hn := (Complex.re_le_norm (conj y * q)).trans_eq
      (by rw [norm_mul, norm_conj])
    nlinarith only [hn, hq2, sq_nonneg (‖y‖ - ‖q‖)]
  have hk' := mul_le_mul_of_nonneg_right hk (sq_nonneg ‖y‖)
  nlinarith only [mul_le_mul_of_nonneg_left (show
    2 * k * ‖y‖ ^ 2 + 2 * (conj y * z).re + 2 * (conj y * q).re ≤
      (2 * ε + 2) * ‖y‖ ^ 2 + ‖z‖ ^ 2 + D ^ 2 * E by
        linarith only [hk', hz, he]) hw]

private theorem connector_clock_bound {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v B ρ : ℝ}
    (hab : a ≤ b) (hbv : b < v) (hs : inSeg a b v ⊆ D)
    (hB : 0 < B) (hρ : 0 < ρ) (hstart : S.r a v = B)
    (hrange : ∀ u ∈ Icc a b, ρ * B ≤ S.r u v) :
    (∀ u ∈ Icc a b, S.r u v ≤ B) ∧
      (∫ u in a..b, (-S.nu u v) / S.r u v) ≤ 1 / ρ := by
  have hp (u : ℝ) (hu : u ∈ Icc a b) : (u, v) ∈ D := hs ⟨hu.1, hu.2, rfl⟩
  have cr := Calculus.continuousOn_in_section hS.cont_r hs
  have cn := Calculus.continuousOn_in_section hS.cont_nu hs
  have hr u (hu : u ∈ Icc a b) := hS.r_pos _ (hp u hu) (hu.2.trans_lt hbv)
  have hrad (u : ℝ) (hu : u ∈ Icc a b) :
      S.r u v - S.r a v = ∫ x in a..u, S.nu x v :=
    (Calculus.in_integralForm hS hu.1 (hu.2.trans hbv.le)
      (fun p hh => hs ⟨hh.1, hh.2.1.trans hu.2, hh.2.2⟩)).1.2
  have hupper : ∀ u ∈ Icc a b, S.r u v ≤ B := by
    intro u hu
    have hn := intervalIntegral.integral_nonneg hu.1 (μ := volume)
      (fun x hx => (neg_pos.mpr (hS.nu_neg _ (hp x ⟨hx.1, hx.2.trans hu.2⟩))).le)
    rw [intervalIntegral.integral_neg, ← hrad u hu, hstart] at hn
    linarith only [hn]
  refine ⟨hupper, ?_⟩
  have hi := intervalIntegral.integral_mono_on hab
    ((cn.neg.div cr (fun u hu => (hr u hu).ne')).intervalIntegrable_of_Icc (μ := volume) hab)
    ((cn.neg.div_const (ρ * B)).intervalIntegrable_of_Icc (μ := volume) hab)
    (fun u hu => div_le_div_of_nonneg_left
      (neg_pos.mpr (hS.nu_neg _ (hp u hu))).le (mul_pos hρ hB) (hrange u hu))
  dsimp only [Pi.div_apply, Pi.neg_apply] at hi
  rw [intervalIntegral.integral_div, intervalIntegral.integral_neg,
    ← hrad b ⟨hab, le_rfl⟩, hstart] at hi
  calc
    _ ≤ (B - S.r b v) / (ρ * B) := by simpa only [neg_sub] using hi
    _ ≤ B / (ρ * B) := div_le_div_of_nonneg_right
      (sub_le_self _ (hr b ⟨hab, le_rfl⟩).le) (mul_pos hρ hB).le
    _ = 1 / ρ := by field_simp

/-- [internal] The scalar square along a connector from its derived scalar
profile. The consumer `connector_budget` discharges that profile premise.
The constant depends only on `δ, ρ, ε`, before all solution data and scales.
The squared norm eliminates the real gauge connection exactly. -/
theorem connector_scalar_square_of_scalar_bound (δ ρ ε : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) (hε : 0 ≤ ε) :
    ∃ K > 0, ∀ (ui e M₀ : ℝ) (S : Fields),
      IsSolution e S (origDomain ui) → 1 ≤ M₀ →
      ∀ (a b v B E : ℝ), a ≤ b → b < v →
      inSeg a b v ⊆ origDomain ui → 0 < B → 0 ≤ E → S.r a v = B →
      S.m a v / B + ‖S.theta a v / S.lam a v‖ ^ 2 ≤ E →
      (∀ u ∈ Icc a b, ρ * B ≤ S.r u v) →
      (∀ u ∈ Icc a b, ∀ w ∈ Icc u v, δ ≤ 1 - S.mu u w) →
      (∀ u ∈ Icc a b, (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
        (1 - S.mu u v) ≤ ε) →
      (∀ u ∈ Icc a b, ‖S.phi u v‖ ≤ M₀) → e ^ 2 * M₀ ^ 2 * B ^ 2 ≤ 1 →
      ∀ u ∈ Icc a b, ‖S.theta u v / S.lam u v‖ ^ 2 ≤ K * E := by
  obtain ⟨C, hC, hcharge⟩ := connector_charge_of_scalar_bound δ ρ hδ hδ1 hρ
  let D := C / δ
  let K := (1 + 2 / (δ * ρ) + D ^ 2 / ρ) * Real.exp ((2 * ε + 2) / ρ)
  refine ⟨K, by dsimp only [K, D]; positivity, ?_⟩
  intro ui e M₀ S hS hM a b v B E hab hbv hs hB hE hstart hbudget hrange hcore hκ hphi hscale
  have hp (u : ℝ) (hu : u ∈ Icc a b) : (u, v) ∈ origDomain ui := hs ⟨hu.1, hu.2, rfl⟩
  have hr u (hu : u ∈ Icc a b) := hS.r_pos _ (hp u hu) (hu.2.trans_lt hbv)
  have hm0 := (Terminal.mass_monotonicity hS _ (hp a ⟨le_rfl, hab⟩)).1
  have hmass : S.m a v / B ≤ E := by linarith only [hbudget, sq_nonneg ‖S.theta a v / S.lam a v‖]
  have hy0 : ‖S.theta a v / S.lam a v‖ ^ 2 ≤ E := by
    linarith only [hbudget, div_nonneg hm0 hB.le]
  have hgap u (hu : u ∈ Icc a b) := hcore u hu v ⟨(hu.2.trans_lt hbv).le, le_rfl⟩
  have hflux := connector_mass_and_flux hδ hρ hS hab hbv hs hB hE hstart hmass hrange hgap
  have hcharge' := hcharge ui e M₀ S hS hM a b v B E hab hbv hs hB hE
    hstart hmass hrange hcore hphi
  obtain ⟨hupper, hclock⟩ := connector_clock_bound hS hab hbv hs hB hρ hstart hrange
  let y := fun u => S.theta u v / (S.lam u v : ℂ)
  let z := fun u => S.xi u v / (S.nu u v : ℂ)
  let f := fun u => ‖y u‖ ^ 2
  let w := fun u => (-S.nu u v) / S.r u v
  let k := fun u => (2 * ε + 2) * w u
  let q := fun u => (‖z u‖ ^ 2 + D ^ 2 * E) * w u
  have cr := Calculus.continuousOn_in_section hS.cont_r hs
  have cn := Calculus.continuousOn_in_section hS.cont_nu hs
  have cx := Calculus.continuousOn_in_section hS.cont_xi hs
  have cw : ContinuousOn w (Icc a b) := cn.neg.div cr (fun u hu => (hr u hu).ne')
  have cz : ContinuousOn z (Icc a b) := cx.div (continuous_ofReal.comp_continuousOn cn)
    (fun u hu => Complex.ofReal_ne_zero.mpr (hS.nu_neg _ (hp u hu)).ne)
  have ik : IntervalIntegrable k volume a b :=
    (cw.const_mul (2 * ε + 2)).intervalIntegrable_of_Icc (μ := volume) hab
  have iq : IntervalIntegrable q volume a b :=
    (((cz.norm.pow 2).add continuousOn_const).mul cw).intervalIntegrable_of_Icc
    (μ := volume) hab
  have hw0 u (hu : u ∈ Icc a b) : 0 ≤ w u :=
    div_nonneg (neg_pos.mpr (hS.nu_neg _ (hp u hu))).le (hr u hu).le
  have hy := Renormalized.incoming_ratio_section hS hab hbv hs
  have hn := lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hy.1
  have hf : AbsolutelyContinuousOnInterval f a b := by
    simpa only [f, y, pow_two, Pi.mul_apply, Function.comp_apply] using hn.mul_normed_ring hn
  have hderiv : ∀ᵐ u ∂volume.restrict (Icc a b), deriv f u ≤ k u * f u + q u := by
    filter_upwards [hy.2, ae_restrict_mem measurableSet_Icc] with u hdu hu
    let κ := (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) / (1 - S.mu u v)
    let em := I * (e : ℂ) * S.Q u v * S.phi u v / (1 - S.mu u v)
    have hem : ‖em‖ ≤ D * Real.sqrt E := by
      have he := electric_forcing_of_profiles hδ hC.le (by linarith only [hM] : 0 ≤ M₀)
        (hr u hu) (hgap u hu) (hphi u hu) (hcharge' u hu)
      have he' : ‖em‖ ≤ D * e ^ 2 * M₀ ^ 2 * Real.sqrt E * S.r u v ^ 2 := by
        have hid : em = (I * (e : ℂ) * S.Q u v * S.phi u v /
            (((1 - S.mu u v) * S.r u v : ℝ) : ℂ)) * (S.r u v : ℂ) := by
          dsimp only [em]
          push_cast
          field_simp [Complex.ofReal_ne_zero.mpr (hr u hu).ne']
        rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr u hu)]
        convert mul_le_mul_of_nonneg_right he (hr u hu).le using 1
        ring
      have hrsq := pow_le_pow_left₀ (hr u hu).le (hupper u hu) 2
      have hes : e ^ 2 * M₀ ^ 2 * S.r u v ^ 2 ≤ 1 :=
        (mul_le_mul_of_nonneg_left hrsq (mul_nonneg (sq_nonneg e) (sq_nonneg M₀))).trans hscale
      have hh := mul_le_mul_of_nonneg_left hes
        (mul_nonneg (by positivity : 0 ≤ D) (Real.sqrt_nonneg E))
      nlinarith only [he', hh]
    have hd : HasDerivAt y
        ((w u : ℂ) * (z u + (κ : ℂ) * y u + em) - I * (e * S.A u v : ℝ) * y u) u := by
      convert hdu using 1
      dsimp only [y, z, w, κ, em]
      push_cast
      ring
    have hsq : HasDerivAt f
        (2 * (conj (y u) * ((w u : ℂ) * (z u + (κ : ℂ) * y u + em) -
          I * (e * S.A u v : ℝ) * y u)).re) u := by
      simpa only [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply', RCLike.re_to_complex]
        using hd.norm_sq
    rw [hsq.deriv]
    have hh := scalar_square_le (A := e * S.A u v) (y u) (z u) em (hw0 u hu) (hκ u hu)
      (by positivity : 0 ≤ D) hE hem
    convert hh using 1
    dsimp only [k, f, q]
    ring
  have hineq : ∀ t ∈ Icc a b,
      f t ≤ (f a + ∫ u in a..t, q u) + ∫ u in a..t, k u * f u := by
    intro t ht
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    have ikf := ik.mul_continuousOn (by simpa only [uIcc_of_le hab] using hf.continuousOn)
    have hi := intervalIntegral.integral_mono_ae_restrict ht.1
      (hf.intervalIntegrable_deriv.mono_set hsub) ((ikf.add iq).mono_set hsub)
      (hderiv.filter_mono (ae_mono (Measure.restrict_mono
        (Icc_subset_Icc le_rfl ht.2) le_rfl)))
    rw [(hf.mono hsub).integral_deriv_eq_sub,
      intervalIntegral.integral_add (ikf.mono_set hsub) (iq.mono_set hsub)] at hi
    linarith only [hi]
  have hg := le_exp_integral_of_le_integral_forcing hab
    (by simpa only [uIcc_of_le hab] using hf.continuousOn) ik iq
    (ae_restrict_of_forall_mem measurableSet_Icc (fun u hu =>
      mul_nonneg (by positivity : 0 ≤ 2 * ε + 2) (hw0 u hu)))
    (ae_restrict_of_forall_mem measurableSet_Icc (fun u hu => by
      dsimp only [q]; exact mul_nonneg (by positivity) (hw0 u hu))) hineq
  intro t ht
  have hs' : inSeg a t v ⊆ origDomain ui := fun p hh => hs ⟨hh.1, hh.2.1.trans ht.2, hh.2.2⟩
  have hclock' := (connector_clock_bound hS ht.1 (ht.2.trans_lt hbv) hs' hB hρ hstart
    (fun u hu => hrange u ⟨hu.1, hu.2.trans ht.2⟩)).2
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]; exact Icc_subset_Icc le_rfl ht.2
  have hqint : (∫ u in a..t, q u) ≤ (2 / (δ * ρ) + D ^ 2 / ρ) * E := by
    have iz : IntervalIntegrable (fun u => ‖z u‖ ^ 2 * w u) volume a b :=
      ((cz.norm.pow 2).mul cw).intervalIntegrable_of_Icc (μ := volume) hab
    have iw := cw.intervalIntegrable_of_Icc (μ := volume) hab
    have heq : (∫ u in a..t, q u) =
        (∫ u in a..t, ‖z u‖ ^ 2 * (-S.nu u v) / S.r u v) +
          D ^ 2 * E * (∫ u in a..t, w u) := by
      simp only [q, add_mul]
      rw [intervalIntegral.integral_add (iz.mono_set hsub)
        ((iw.const_mul (D ^ 2 * E)).mono_set hsub), intervalIntegral.integral_const_mul]
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only [w]; ring
    have hh := mul_le_mul_of_nonneg_left hclock' (by positivity : 0 ≤ D ^ 2 * E)
    calc
      _ = _ := heq
      _ ≤ 2 * E / (δ * ρ) + D ^ 2 * E * (1 / ρ) := add_le_add (hflux t ht).2.2.1 hh
      _ = _ := by ring
  have hkint : (∫ u in a..t, k u) ≤ (2 * ε + 2) / ρ := by
    rw [intervalIntegral.integral_const_mul]
    convert mul_le_mul_of_nonneg_left hclock' (by positivity : 0 ≤ 2 * ε + 2) using 1
    ring
  have hsum : f a + (∫ u in a..t, q u) ≤ (1 + 2 / (δ * ρ) + D ^ 2 / ρ) * E := by
    dsimp only [f, y]
    nlinarith only [hy0, hqint]
  calc
    _ ≤ _ := hg t ht
    _ ≤ ((1 + 2 / (δ * ρ) + D ^ 2 / ρ) * E) * Real.exp ((2 * ε + 2) / ρ) :=
      mul_le_mul hsum (Real.exp_le_exp.mpr hkint) (Real.exp_pos _).le (by positivity)
    _ = K * E := by dsimp only [K]; ring

/-- [node sec:charged-terminal-interaction#connector-budget]
Ratified internal project record: the pointwise mass/scalar budget, integrated quadratic
budget, and the next cylinder's observation energy, at every partial
endpoint. The source scalar envelope is derived from its stopped row data.
The positive constant is chosen from `δ, ρ, ε` before the solution,
coupling, scalar background, scales, energy and duration. Every error
multiplies the preceding budget, including when that budget is zero. -/
theorem connector_budget (δ ρ ε : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hρ : 0 < ρ) (hε : 0 ≤ ε) :
    ∃ C > 0, ∀ (c Λ F : ℝ), 0 < c → 0 ≤ F → F < 1 →
      ∀ (ui e a b v B E H Jstop R₀ : ℝ) (S : Fields) (g : ℝ → ℝ),
      OriginalData ui e S → a ≤ b → ui ≤ a → b < v → v ≤ 0 →
      0 ≤ Jstop → 0 < B → B ≤ R₀ → 0 ≤ E → S.r a v = B →
      S.m a v / B + ‖S.theta a v / S.lam a v‖ ^ 2 ≤ E →
      (∀ u ∈ Icc a b, ρ * B ≤ S.r u v) →
      ExteriorStops S (exteriorDomain ui a b (fun _ => v)) δ c Λ F ε →
      (∀ u ∈ Icc a b, ∀ w ∈ Icc u 0, δ ≤ 1 - S.mu u w) →
      (∀ u ∈ Icc a b, ‖S.phi u 0‖ ≤ H) →
      IntegrableOn g (Icc v 0) →
      (∀ᵐ w ∂volume.restrict (Icc v 0), 0 ≤ g w) →
      (∀ u ∈ Icc a b, ∀ᵐ w ∂volume.restrict (Icc v 0), ‖weightedJ S u w‖ ≤ g w) →
      (∫ w in v..0, g w) ≤ Jstop →
      let M₀ := 1 + H + (F + c⁻¹ * Jstop) / (1 - F ^ 2)
      e ^ 2 * M₀ ^ 2 * R₀ ^ 2 ≤ 1 →
      ∀ x ∈ Icc a b,
        (S.m x v / S.r x v + ‖S.theta x v / S.lam x v‖ ^ 2 ≤ C * E) ∧
        ((∫ u in a..x, (‖S.theta u v / S.lam u v‖ ^ 2 +
          ‖S.xi u v / S.nu u v‖ ^ 2 + S.mu u v ^ 2) *
            (-S.nu u v) / S.r u v) ≤ C * E) ∧
        (cylinderEnergy S (S.r x v) x v / S.r x v ≤ C * E) := by
  obtain ⟨K, hK, hscalar⟩ := connector_scalar_square_of_scalar_bound δ ρ ε hδ hδ1 hρ hε
  let C := 1 + (1 / ρ + K) + (K / ρ + 2 / (δ * ρ) + 2 / ρ ^ 2) +
    (K / 2 + 1 / (δ * ρ))
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro c Λ F hc hF hF1 ui e a b v B E H Jstop R₀ S g h hab hia hbv hv hJstop hB hBR hE
    hstart hbudget hrange hstop hcore hterm hg hg0 hmajor hJ
  dsimp only
  intro hscale
  let M₀ := 1 + H + (F + c⁻¹ * Jstop) / (1 - F ^ 2)
  obtain ⟨hM, hphi⟩ := connector_scalar_profile h hab hia hbv hv hc hF hF1
    hJstop hstop hterm hg hg0 hmajor hJ
  have hs : inSeg a b v ⊆ origDomain ui := by
    rintro ⟨u, w⟩ ⟨hu, hub, rfl⟩
    exact ⟨hia.trans hu, (hub.trans_lt hbv).trans_le hv, (hub.trans_lt hbv).le, hv⟩
  have hp (u : ℝ) (hu : u ∈ Icc a b) : (u, v) ∈ origDomain ui := hs ⟨hu.1, hu.2, rfl⟩
  have hpe u (hu : u ∈ Icc a b) : (u, v) ∈ exteriorDomain ui a b (fun _ => v) :=
    ⟨hp u hu, hu.1, hu.2, le_rfl⟩
  have hκ u (hu : u ∈ Icc a b) :=
    (radial_expansion_coefficient_of_stops hstop (hpe u hu)
      (h.solution.one_sub_mu_pos _ (hp u hu))).2
  have hgap u (hu : u ∈ Icc a b) := hcore u hu v ⟨(hu.2.trans_lt hbv).le, hv⟩
  have hmass : S.m a v / B ≤ E := by
    linarith only [hbudget, sq_nonneg ‖S.theta a v / S.lam a v‖]
  have hscaleB : e ^ 2 * M₀ ^ 2 * B ^ 2 ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB.le hBR 2)
      (mul_nonneg (sq_nonneg e) (sq_nonneg M₀))).trans hscale
  have hy := hscalar ui e M₀ S h.solution hM a b v B E hab hbv hs hB hE hstart hbudget
    hrange (fun u hu w hw => hcore u hu w ⟨hw.1, hw.2.trans hv⟩) hκ hphi hscaleB
  have hm := connector_mass_and_flux hδ hρ h.solution hab hbv hs hB hE hstart hmass hrange hgap
  have cr := Calculus.continuousOn_in_section h.solution.cont_r hs
  have cn := Calculus.continuousOn_in_section h.solution.cont_nu hs
  have ct := Calculus.continuousOn_in_section h.solution.cont_theta hs
  have cl := Calculus.continuousOn_in_section h.solution.cont_lam hs
  have cx := Calculus.continuousOn_in_section h.solution.cont_xi hs
  have cm := Calculus.continuousOn_in_section h.solution.cont_m hs
  have hr u (hu : u ∈ Icc a b) := h.solution.r_pos _ (hp u hu) (hu.2.trans_lt hbv)
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl)
    (fun u hu => Complex.ofReal_ne_zero.mpr (h.solution.lam_pos _ (hp u hu)).ne')
  have cz := cx.div (continuous_ofReal.comp_continuousOn cn)
    (fun u hu => Complex.ofReal_ne_zero.mpr (h.solution.nu_neg _ (hp u hu)).ne)
  have cμ : ContinuousOn (fun u => S.mu u v) (Icc a b) :=
    (continuousOn_const.mul cm).div cr (fun u hu => (hr u hu).ne')
  have cw := cn.neg.div cr (fun u hu => (hr u hu).ne')
  intro x hx
  have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
  have hsx : inSeg a x v ⊆ origDomain ui := fun p hh => hs ⟨hh.1, hh.2.1.trans hx.2, hh.2.2⟩
  have hclock := (connector_clock_bound h.solution hx.1 (hx.2.trans_lt hbv) hsx hB hρ hstart
    (fun u hu => hrange u (hsub hu))).2
  have hw u (hu : u ∈ Icc a b) : 0 ≤ (-S.nu u v) / S.r u v :=
    div_nonneg (neg_pos.mpr (h.solution.nu_neg _ (hp u hu))).le (hr u hu).le
  have hμ u (hu : u ∈ Icc a b) : S.mu u v ^ 2 ≤ 2 * E / ρ := by
    have h01 := h.mu _ (hp u hu)
    have hη := (hm u hu).2.1.2
    have hsq : S.mu u v ^ 2 ≤ S.mu u v := by
      nlinarith only [mul_le_mul_of_nonneg_left h01.2.le h01.1]
    have heq : S.mu u v = 2 * (S.m u v / S.r u v) := by simp only [Fields.mu]; ring
    calc
      _ ≤ S.mu u v := hsq
      _ = 2 * (S.m u v / S.r u v) := heq
      _ ≤ 2 * (E / ρ) := mul_le_mul_of_nonneg_left hη (by norm_num)
      _ = _ := by ring
  have iy : (∫ u in a..x, ‖S.theta u v / S.lam u v‖ ^ 2 *
      ((-S.nu u v) / S.r u v)) ≤ K / ρ * E := by
    have hh := intervalIntegral.integral_mono_on hx.1
      (((cy.norm.pow 2).mul cw).mono hsub |>.intervalIntegrable_of_Icc (μ := volume) hx.1)
      ((cw.const_mul (K * E)).mono hsub |>.intervalIntegrable_of_Icc (μ := volume) hx.1)
      (fun u hu => mul_le_mul_of_nonneg_right (hy u (hsub hu)) (hw u (hsub hu)))
    rw [intervalIntegral.integral_const_mul] at hh
    calc
      _ ≤ (K * E) * (∫ u in a..x, (-S.nu u v) / S.r u v) := by
        simpa only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, Pi.neg_apply,
          Function.comp_apply] using hh
      _ ≤ (K * E) * (1 / ρ) := mul_le_mul_of_nonneg_left hclock (mul_nonneg hK.le hE)
      _ = _ := by ring
  have im : (∫ u in a..x, S.mu u v ^ 2 * ((-S.nu u v) / S.r u v)) ≤ 2 / ρ ^ 2 * E := by
    have hh := intervalIntegral.integral_mono_on hx.1
      (((cμ.pow 2).mul cw).mono hsub |>.intervalIntegrable_of_Icc (μ := volume) hx.1)
      ((cw.const_mul (2 * E / ρ)).mono hsub |>.intervalIntegrable_of_Icc (μ := volume) hx.1)
      (fun u hu => mul_le_mul_of_nonneg_right (hμ u (hsub hu)) (hw u (hsub hu)))
    rw [intervalIntegral.integral_const_mul] at hh
    have hh' := mul_le_mul_of_nonneg_left hclock (div_nonneg (by positivity : 0 ≤ 2 * E) hρ.le)
    have heq : (2 * E / ρ) * (1 / ρ) = 2 / ρ ^ 2 * E := by ring
    rw [heq] at hh'
    exact hh.trans hh'
  have iz := (hm x hx).2.2.1
  have ibudget : (∫ u in a..x, (‖S.theta u v / S.lam u v‖ ^ 2 +
      ‖S.xi u v / S.nu u v‖ ^ 2 + S.mu u v ^ 2) * (-S.nu u v) / S.r u v) ≤
        (K / ρ + 2 / (δ * ρ) + 2 / ρ ^ 2) * E := by
    have heq : (∫ u in a..x, (‖S.theta u v / S.lam u v‖ ^ 2 +
        ‖S.xi u v / S.nu u v‖ ^ 2 + S.mu u v ^ 2) * (-S.nu u v) / S.r u v) =
        (∫ u in a..x, ‖S.theta u v / S.lam u v‖ ^ 2 * ((-S.nu u v) / S.r u v)) +
        (∫ u in a..x, ‖S.xi u v / S.nu u v‖ ^ 2 * ((-S.nu u v) / S.r u v)) +
        (∫ u in a..x, S.mu u v ^ 2 * ((-S.nu u v) / S.r u v)) := by
      simp_rw [add_mul, add_div, mul_div_assoc]
      have iY : IntervalIntegrable (fun u => ‖S.theta u v / S.lam u v‖ ^ 2 *
          ((-S.nu u v) / S.r u v)) volume a x :=
        (((cy.norm.pow 2).mul cw).mono hsub).intervalIntegrable_of_Icc (μ := volume) hx.1
      have iZ : IntervalIntegrable (fun u => ‖S.xi u v / S.nu u v‖ ^ 2 *
          ((-S.nu u v) / S.r u v)) volume a x :=
        (((cz.norm.pow 2).mul cw).mono hsub).intervalIntegrable_of_Icc (μ := volume) hx.1
      have iM : IntervalIntegrable (fun u => S.mu u v ^ 2 *
          ((-S.nu u v) / S.r u v)) volume a x :=
        (((cμ.pow 2).mul cw).mono hsub).intervalIntegrable_of_Icc (μ := volume) hx.1
      rw [intervalIntegral.integral_add (iY.add iZ) iM, intervalIntegral.integral_add iY iZ]
    rw [heq]
    have iz' : (∫ u in a..x, ‖S.xi u v / S.nu u v‖ ^ 2 *
        ((-S.nu u v) / S.r u v)) ≤ 2 * E / (δ * ρ) := by
      simpa only [mul_div_assoc] using iz
    calc
      _ ≤ K / ρ * E + 2 * E / (δ * ρ) + 2 / ρ ^ 2 * E := add_le_add (add_le_add iy iz') im
      _ = _ := by ring
  have hlog : -Real.log (1 - S.mu x v) ≤ 2 * E / (δ * ρ) := by
    have h01 := h.mu _ (hp x hx)
    have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr (h.solution.one_sub_mu_pos _ (hp x hx)))
    rw [Real.log_inv] at hh
    have heq : (1 - S.mu x v)⁻¹ - 1 = S.mu x v / (1 - S.mu x v) := by
      field_simp [(h.solution.one_sub_mu_pos _ (hp x hx)).ne']
      ring
    rw [heq] at hh
    have hdiv := div_le_div_of_nonneg_left h01.1 hδ (hgap x hx)
    have hη := (hm x hx).2.1.2
    have heq' : S.mu x v = 2 * (S.m x v / S.r x v) := by simp only [Fields.mu]; ring
    have hbound := div_le_div_of_nonneg_right hη hδ.le
    calc
      _ ≤ S.mu x v / (1 - S.mu x v) := hh
      _ ≤ S.mu x v / δ := hdiv
      _ = 2 * (S.m x v / S.r x v / δ) := by rw [heq']; ring
      _ ≤ 2 * (E / ρ / δ) := mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = _ := by ring
  have hobs : cylinderEnergy S (S.r x v) x v / S.r x v ≤
      (K / 2 + 1 / (δ * ρ)) * E := by
    have heq : cylinderEnergy S (S.r x v) x v / S.r x v =
        (‖S.theta x v / S.lam x v‖ ^ 2 - Real.log (1 - S.mu x v)) / 2 := by
      dsimp only [cylinderEnergy]
      field_simp [(hr x hx).ne']
    rw [heq]
    calc
      _ ≤ (K * E + 2 * E / (δ * ρ)) / 2 :=
        div_le_div_of_nonneg_right (by linarith only [hy x hx, hlog]) (by norm_num)
      _ = _ := by ring
  have hp₁ : 0 ≤ 1 / ρ + K := by positivity
  have hp₂ : 0 ≤ K / ρ + 2 / (δ * ρ) + 2 / ρ ^ 2 := by positivity
  have hp₃ : 0 ≤ K / 2 + 1 / (δ * ρ) := by positivity
  have hC₁ : 1 / ρ + K ≤ C := by dsimp only [C]; linarith only [hp₂, hp₃]
  have hC₂ : K / ρ + 2 / (δ * ρ) + 2 / ρ ^ 2 ≤ C := by dsimp only [C]; linarith only [hp₁, hp₃]
  have hC₃ : K / 2 + 1 / (δ * ρ) ≤ C := by dsimp only [C]; linarith only [hp₁, hp₂]
  refine ⟨?_, ibudget.trans (mul_le_mul_of_nonneg_right hC₂ hE),
    hobs.trans (mul_le_mul_of_nonneg_right hC₃ hE)⟩
  calc
    _ ≤ E / ρ + K * E := add_le_add (hm x hx).2.1.2 (hy x hx)
    _ = (1 / ρ + K) * E := by ring
    _ ≤ C * E := mul_le_mul_of_nonneg_right hC₁ hE

end EmcsfAcExtension.Global.Interaction
