module

public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Defs.Domains
public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Interaction.WrappersProfiles
import EmcsfAcExtension.Global.Closure.CutoffContinuity
import EmcsfAcExtension.Global.Interaction.ClosuresFinite
import EmcsfAcExtension.Global.Interaction.ForcingRepresentative
import EmcsfAcExtension.Global.Interaction.Profiles
import EmcsfAcExtension.Global.Terminal.OpticalUpper
import EmcsfAcExtension.Global.Gap.Radial
import EmcsfAcExtension.Global.Exterior.ScalarEnergy
import EmcsfAcExtension.Global.Renormalized.WeakTransfer
import EmcsfAcExtension.Global.Api.Integrals
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Profiles on a finite stopped exterior

The core estimate uses the independent gap and ordinary Hawking mass; it
places no amplitude bootstrap on the core. The incoming envelope retains
the initial density on its fixed label set.
Source: `charged_SF_new_version.tex:L3935–L4026`.
-/

public section

open Set MeasureTheory Complex Filter
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Unitary transport majorizes the canonical incoming representative by its
fixed initial density plus the absolute source history. This estimate is
valid before proving finiteness; it never takes the real value of an
unbounded extended integral. The representative is the characterized
weighted derivative, not an arbitrary trace of a product-a.e. derivative. -/
theorem representative_le_incoming_envelope (e : ℝ) (S : Fields)
    (D : Set (ℝ × ℝ)) {a u v : ℝ} (hau : a ≤ u)
    (hs : inSeg a u v ⊆ D) :
    ‖weightedJRepresentative e S a u v‖ₑ ≤ incomingEnvelope e S D a v := by
  have hexp (s t : ℝ) :
      ‖Complex.exp (-I * e * ∫ x in s..t, S.A x v)‖ₑ = 1 := by
    rw [← ofReal_norm]
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  unfold weightedJRepresentative incomingEnvelope
  calc
    _ ≤ ‖Complex.exp (-I * e * ∫ s in a..u, S.A s v) * weightedJ S a v‖ₑ +
        ‖∫ s in a..u, Complex.exp (-I * e * ∫ t in s..u, S.A t v) *
          weightedJSource e S s v‖ₑ := enorm_add_le _ _
    _ ≤ ‖weightedJ S a v‖ₑ + ∫⁻ s in Ioc a u, ‖weightedJSource e S s v‖ₑ := by
      rw [enorm_mul, hexp, one_mul, intervalIntegral.integral_of_le hau]
      gcongr
      calc
        _ ≤ ∫⁻ s in Ioc a u,
            ‖Complex.exp (-I * e * ∫ t in s..u, S.A t v) * weightedJSource e S s v‖ₑ :=
          enorm_integral_le_lintegral_enorm _
        _ = _ := by simp_rw [enorm_mul, hexp, one_mul]
    _ ≤ _ := by
      gcongr
      intro s hs'
      exact hs ⟨hs'.1.le, hs'.2, rfl⟩

/-- [internal]
The energy-only square-root inequality bounds the current unfinished
cylinder by `2ε + σ²`, before using observation or integrated budgets.
This is the noncircular initialization step required at
`charged_SF_new_version.tex:L4016–L4026`. All coefficients are universal. -/
theorem current_energy_of_square_root {Q ε σ : ℝ} (hQ : 0 ≤ Q) (he : 0 ≤ ε)
    (hσ : 0 ≤ σ) (hroot : Real.sqrt Q ≤ Real.sqrt ε + (1 / Real.sqrt 2) * σ) :
    Q ≤ 2 * ε + σ ^ 2 := by
  have hk : 0 ≤ (1 / Real.sqrt 2 : ℝ) := by positivity
  have hs := (sq_le_sq₀ (Real.sqrt_nonneg Q)
    (add_nonneg (Real.sqrt_nonneg ε) (mul_nonneg hk hσ))).mpr hroot
  have hks : ((1 / Real.sqrt 2) * σ) ^ 2 = σ ^ 2 / 2 := by
    rw [mul_pow, div_pow]
    norm_num
    ring
  nlinarith only [hs, hks, Real.sq_sqrt hQ, Real.sq_sqrt he,
    sq_nonneg (Real.sqrt ε - (1 / Real.sqrt 2) * σ)]

private theorem radial_scalar_energy {e δ : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u u b ⊆ D) (hδ : 0 < δ)
    (hgap : ∀ v ∈ Icc a b, δ ≤ 1 - S.mu u v) :
    (∫ v in a..b, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤
      2 * S.m u b / δ := by
  have hs' : outSeg u a b ⊆ D := fun p hp =>
    hs ⟨hp.1, hua.le.trans hp.2.1, hp.2.2⟩
  have hl (v : ℝ) (hv : v ∈ Icc a b) := hS.lam_pos (u, v) (hs' ⟨rfl, hv⟩)
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs'
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs'
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl)
    (fun v hv => ofReal_ne_zero.mpr (hl v hv).ne')
  have hi := ((cy.norm.pow 2).mul cl).intervalIntegrable_of_Icc (μ := volume) hab
  change IntervalIntegrable
    (fun v => ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) volume a b at hi
  have hm := (hS.eq_out u a b hua hab hs').2.2.1
  have hmono := intervalIntegral.integral_mono_on hab (hi.const_mul δ)
    (hm.1.const_mul 2) (fun v hv => ?_)
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      ← hm.2] at hmono
    change δ * (∫ v in a..b, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤
      2 * (S.m u b - S.m u a) at hmono
    have hmass := Gap.mass_out_le hS le_rfl hua.le
      (fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hab⟩)
    rw [(hS.axis u (hs ⟨rfl, le_rfl, hua.le.trans hab⟩)).2.1] at hmass
    apply (le_div_iff₀ hδ).mpr
    nlinarith only [hmono, hmass]
  · have heq := Local.RelCharge.radial_mass_equation hS (hs' ⟨rfl, hv⟩)
    change δ * (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v) ≤ 2 * S.mV u v
    have hq : 0 ≤ S.Q u v ^ 2 / S.r u v ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hh := mul_le_mul_of_nonneg_right (hgap v hv)
      (sq_nonneg ‖S.theta u v / (S.lam u v : ℂ)‖)
    have hh' := mul_le_mul_of_nonneg_left (hh.trans (le_add_of_nonneg_right hq))
      (hl v hv).le
    have heq' := (div_eq_iff (hl v hv).ne').mp heq
    nlinarith only [hh', heq']

private theorem inverse_radius_moment {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u u b ⊆ D) :
    (∫ v in a..b, S.lam u v / S.r u v ^ 2) =
      (S.r u a)⁻¹ - (S.r u b)⁻¹ := by
  have hs' : outSeg u a b ⊆ D := fun p hp =>
    hs ⟨hp.1, hua.le.trans hp.2.1, hp.2.2⟩
  have hr (v : ℝ) (hv : v ∈ Icc a b) :=
    hS.r_pos (u, v) (hs' ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have cr := Calculus.continuousOn_out_section hS.cont_r hs'
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs'
  have hi := (cl.div (cr.pow 2) (fun v hv => pow_ne_zero 2 (hr v hv).ne')).intervalIntegrable_of_Icc
    (μ := volume) hab
  have hd (v : ℝ) (hv : v ∈ Ioo a b) :
      HasDerivAt (fun v => -(S.r u v)⁻¹) (S.lam u v / S.r u v ^ 2) v := by
    convert ((Local.IsSolution.hasDerivAt_radius_out hS hs
      ⟨hua.trans hv.1, hv.2⟩).inv (hr v ⟨hv.1.le, hv.2.le⟩).ne').neg using 1
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (cr.inv₀ (fun v hv => (hr v hv).ne')).neg hd hi
  simpa only [Pi.neg_apply, Pi.inv_apply, neg_sub_neg] using he

/-- [node sec:charged-closure#core-scalar-profile]
Inside a boundary sphere, the independent gap gives the mass-dependent
scalar profile with its exact coefficient `2`. The formula uses the actual
radius `S.r u a`, and applies to every positive inner radius. There is no
constant depending on the stage, coupling, amplitude or physical scale. -/
theorem core_scalar_profile {e δ : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b : ℝ} (hua : u < a) (hab : a ≤ b)
    (hs : outSeg u u b ⊆ D) (hδ : 0 < δ)
    (hgap : ∀ v ∈ Icc a b, δ ≤ 1 - S.mu u v) :
    ‖S.phi u a‖ ≤ ‖S.phi u b‖ + Real.sqrt (2 * S.m u b / (δ * S.r u a)) := by
  have hs' : outSeg u a b ⊆ D := fun p hp =>
    hs ⟨hp.1, hua.le.trans hp.2.1, hp.2.2⟩
  have hr (v : ℝ) (hv : v ∈ Icc a b) :=
    hS.r_pos (u, v) (hs' ⟨rfl, hv⟩) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) := hS.lam_pos (u, v) (hs' ⟨rfl, hv⟩)
  have cr := Calculus.continuousOn_out_section hS.cont_r hs'
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs'
  have ct := Calculus.continuousOn_out_section hS.cont_theta hs'
  let f := fun v => ‖S.theta u v‖ / Real.sqrt (S.lam u v)
  let g := fun v => Real.sqrt (S.lam u v) / S.r u v
  have hf : ContinuousOn f (Icc a b) := ct.norm.div cl.sqrt
    (fun v hv => (Real.sqrt_pos.mpr (hl v hv)).ne')
  have hg : ContinuousOn g (Icc a b) := cl.sqrt.div cr (fun v hv => (hr v hv).ne')
  have hcs := Exterior.integral_cauchy_schwarz hab hf hg
  have heq : (∫ v in a..b, f v ^ 2) =
      ∫ v in a..b, ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 * S.lam u v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hab] at hv
    dsimp [f]
    rw [div_pow, Real.sq_sqrt (hl v hv).le, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hl v hv), div_pow]
    field_simp [(hl v hv).ne']
  have hgeq : (∫ v in a..b, g v ^ 2) = ∫ v in a..b, S.lam u v / S.r u v ^ 2 := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hab] at hv
    dsimp [g]
    rw [div_pow, Real.sq_sqrt (hl v hv).le]
  have hfg : (∫ v in a..b, f v * g v) = ∫ v in a..b, ‖S.phiV u v‖ := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hab] at hv
    dsimp [f, g, Fields.phiV]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr v hv)]
    field_simp [(Real.sqrt_pos.mpr (hl v hv)).ne', (hr v hv).ne']
  rw [heq, hgeq, hfg] at hcs
  have hmass : 0 ≤ S.m u b := by
    have hh := Gap.mass_out_le hS le_rfl (hua.le.trans hab) hs
    simpa only [(hS.axis u (hs ⟨rfl, le_rfl, hua.le.trans hab⟩)).2.1] using hh
  have hE := radial_scalar_energy hS hua hab hs hδ hgap
  have hB := inverse_radius_moment hS hua hab hs
  have hBn : 0 ≤ ∫ v in a..b, S.lam u v / S.r u v ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun v hv =>
      div_nonneg (hl v hv).le (sq_nonneg _))
  have hBlo : (∫ v in a..b, S.lam u v / S.r u v ^ 2) ≤ (S.r u a)⁻¹ := by
    rw [hB]
    exact sub_le_self _ (inv_nonneg.mpr (hr b ⟨hab, le_rfl⟩).le)
  have hprod := mul_le_mul hE hBlo hBn (div_nonneg (by positivity) hδ.le)
  have hsq : (∫ v in a..b, ‖S.phiV u v‖) ^ 2 ≤ 2 * S.m u b / (δ * S.r u a) := by
    simpa only [div_mul_eq_div_div, div_eq_mul_inv, mul_inv_rev, mul_assoc,
      mul_left_comm, mul_comm] using hcs.trans hprod
  have hbound : (∫ v in a..b, ‖S.phiV u v‖) ≤
      Real.sqrt (2 * S.m u b / (δ * S.r u a)) := by
    have hn : 0 ≤ 2 * S.m u b / (δ * S.r u a) :=
      div_nonneg (mul_nonneg (by norm_num) hmass) (mul_nonneg hδ.le (hr a ⟨le_rfl, hab⟩).le)
    nlinarith only [hsq, Real.sq_sqrt hn, Real.sqrt_nonneg (2 * S.m u b / (δ * S.r u a))]
  have hp := (hS.eq_out u a b hua hab hs').2.2.2.2.2.1
  have hnorm : ‖S.phi u b - S.phi u a‖ ≤ ∫ v in a..b, ‖S.phiV u v‖ := by
    rw [hp.2]
    exact intervalIntegral.norm_integral_le_integral_norm hab
  calc
    _ = ‖S.phi u b - (S.phi u b - S.phi u a)‖ := by congr 1; abel
    _ ≤ ‖S.phi u b‖ + ‖S.phi u b - S.phi u a‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add le_rfl (hnorm.trans hbound)

/-- [node sec:charged-closure#boundary-charge-profile]
The boundary charge follows from the core mass profile and Maxwell
Cauchy–Schwarz. The coefficient depends only on the positive independent
gap and is chosen before the coupling, fields, boundary sphere and scalar
background. There is no core scalar amplitude assumption. -/
theorem boundary_charge_profile (δ : ℝ) (hδ : 0 < δ) :
    ∃ Cδ > 0, ∀ (e : ℝ) (S : Fields) (D : Set (ℝ × ℝ)),
      IsSolution e S D → ∀ (u b M : ℝ), u < b → outSeg u u b ⊆ D →
      (∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v) → ‖S.phi u b‖ ≤ M →
      |S.Q u b| / S.r u b ^ 2 ≤
        Cδ * |e| * (M * Real.sqrt (S.m u b / S.r u b) + S.m u b / S.r u b) := by
  let Cδ := 4 * (1 + δ⁻¹)
  have hd : 0 < δ⁻¹ := inv_pos.mpr hδ
  refine ⟨Cδ, by dsimp [Cδ]; positivity, ?_⟩
  intro e S D hS u b M hub hs hgap hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hrb := hS.r_pos (u, b) (hs ⟨rfl, hub.le, le_rfl⟩) hub
  have hm : 0 ≤ S.m u b := by
    have hh := Gap.mass_out_le hS le_rfl hub.le hs
    simpa only [(hS.axis u (hs ⟨rfl, le_rfl, hub.le⟩)).2.1] using hh
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cp := Calculus.continuousOn_out_section hS.cont_phi hs
  have cg := (continuousOn_const (c := (1 : ℝ))).sub (Local.continuousOn_mu_out hS hub hs)
  have hg (v : ℝ) (hv : v ∈ Icc u b) : 0 < 1 - S.mu u v := hδ.trans_le (hgap v hv)
  have hweighted (v : ℝ) (hv : v ∈ Icc u b) :
      S.r u v ^ 2 * ‖S.phi u v‖ ^ 2 ≤
        2 * M ^ 2 * S.r u v ^ 2 + 4 * S.m u b / δ * S.r u v := by
    rcases eq_or_lt_of_le hv.1 with rfl | huv
    · simp only [(hS.axis u (hs ⟨rfl, le_rfl, hub.le⟩)).1, zero_pow (by decide : 2 ≠ 0),
        zero_mul, mul_zero, add_zero, le_refl]
    · have hr := hS.r_pos (u, v) (hs ⟨rfl, hv⟩) huv
      have hcore := core_scalar_profile hS huv hv.2 hs hδ
        (fun s hs' => hgap s ⟨hv.1.trans hs'.1, hs'.2⟩)
      have hprofile : ‖S.phi u v‖ ≤ M + Real.sqrt (2 * S.m u b / (δ * S.r u v)) :=
        hcore.trans (add_le_add hM le_rfl)
      have hn : 0 ≤ 2 * S.m u b / (δ * S.r u v) := by positivity
      have hsq := (sq_le_sq₀ (norm_nonneg _) (add_nonneg hM0 (Real.sqrt_nonneg _))).mpr hprofile
      have hsquare : ‖S.phi u v‖ ^ 2 ≤ 2 * M ^ 2 + 4 * S.m u b / (δ * S.r u v) := by
        calc
          _ ≤ (M + Real.sqrt (2 * S.m u b / (δ * S.r u v))) ^ 2 := hsq
          _ ≤ 2 * M ^ 2 + 2 * Real.sqrt (2 * S.m u b / (δ * S.r u v)) ^ 2 := by
            nlinarith only [sq_nonneg (M - Real.sqrt (2 * S.m u b / (δ * S.r u v)))]
          _ = _ := by rw [Real.sq_sqrt hn]; ring
      have hh := mul_le_mul_of_nonneg_left hsquare (sq_nonneg (S.r u v))
      convert hh using 1
      field_simp [hδ.ne', hr.ne']
  have iB := (((cl.mul (cr.pow 2)).mul (cp.norm.pow 2)).div cg
    (fun v hv => (hg v hv).ne')).intervalIntegrable_of_Icc (μ := volume) hub.le
  change IntervalIntegrable (fun v => S.lam u v * S.r u v ^ 2 * ‖S.phi u v‖ ^ 2 /
    (1 - S.mu u v)) volume u b at iB
  have iR₂ := (cl.mul (cr.pow 2)).intervalIntegrable_of_Icc (μ := volume) hub.le
  have iR₁ := (cl.mul cr).intervalIntegrable_of_Icc (μ := volume) hub.le
  change IntervalIntegrable (fun v => S.lam u v * S.r u v ^ 2) volume u b at iR₂
  change IntervalIntegrable (fun v => S.lam u v * S.r u v) volume u b at iR₁
  have hi := intervalIntegral.integral_mono_on hub.le iB
    ((iR₂.const_mul (2 * M ^ 2 / δ)).add (iR₁.const_mul (4 * S.m u b / δ ^ 2)))
    (fun v hv => ?_)
  · rw [intervalIntegral.integral_add (iR₂.const_mul _) (iR₁.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      Local.outgoing_radius_moment hS hub.le hs 2,
      show (∫ v in u..b, S.lam u v * S.r u v) = S.r u b ^ 2 / 2 by
        have hmoment := Local.outgoing_radius_moment hS hub.le hs 1
        norm_num at hmoment
        exact hmoment] at hi
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hi
    have hflux := Local.RelCharge.mass_controls_radial_flux hS hub hs
    have hBn : 0 ≤ ∫ v in u..b,
        S.lam u v * S.r u v ^ 2 * ‖S.phi u v‖ ^ 2 / (1 - S.mu u v) :=
      intervalIntegral.integral_nonneg hub.le (fun v hv => div_nonneg
        (mul_nonneg (mul_nonneg (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le
          (sq_nonneg _)) (sq_nonneg _)) (hg v hv).le)
    have hprod := mul_le_mul hflux hi hBn (show 0 ≤ 2 * S.m u b by positivity)
    have hQ := (Local.RelCharge.maxwell_cauchy_schwarz hS hub hs).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod (sq_nonneg e))
    let t := S.m u b / S.r u b
    have ht : 0 ≤ t := div_nonneg hm hrb.le
    have hQ' : S.Q u b ^ 2 ≤ e ^ 2 * S.r u b ^ 4 *
        ((4 / 3 : ℝ) * δ⁻¹ * M ^ 2 * t + 4 * δ⁻¹ ^ 2 * t ^ 2) := by
      convert hQ using 1
      dsimp only [t]
      field_simp [hδ.ne', hrb.ne']
      ring
    have hcoef₁ : (4 / 3 : ℝ) * δ⁻¹ ≤ Cδ ^ 2 := by
      dsimp only [Cδ]
      nlinarith only [hd.le, sq_nonneg δ⁻¹]
    have hcoef₂ : 4 * δ⁻¹ ^ 2 ≤ Cδ ^ 2 := by
      dsimp only [Cδ]
      nlinarith only [hd.le, sq_nonneg δ⁻¹]
    have hcoeff := add_le_add
      (mul_le_mul_of_nonneg_right hcoef₁ (mul_nonneg (sq_nonneg M) ht))
      (mul_le_mul_of_nonneg_right hcoef₂ (sq_nonneg t))
    have hcross : 0 ≤ 2 * M * Real.sqrt t * t := by positivity
    have hpoly : (4 / 3 : ℝ) * δ⁻¹ * M ^ 2 * t + 4 * δ⁻¹ ^ 2 * t ^ 2 ≤
        Cδ ^ 2 * (M * Real.sqrt t + t) ^ 2 := by
      apply le_trans (by simpa only [mul_assoc] using hcoeff)
      have hh : M ^ 2 * t + t ^ 2 ≤ (M * Real.sqrt t + t) ^ 2 := by
        have hMsq : (M * Real.sqrt t) ^ 2 = M ^ 2 * t := by rw [mul_pow, Real.sq_sqrt ht]
        nlinarith only [hMsq, hcross]
      nlinarith only [mul_le_mul_of_nonneg_left hh (sq_nonneg Cδ)]
    have hQabs : |S.Q u b| ≤ Cδ * |e| * (M * Real.sqrt t + t) * S.r u b ^ 2 := by
      apply (sq_le_sq₀ (abs_nonneg _) (by dsimp only [Cδ]; positivity)).mp
      rw [sq_abs]
      calc
        _ ≤ e ^ 2 * S.r u b ^ 4 *
            ((4 / 3 : ℝ) * δ⁻¹ * M ^ 2 * t + 4 * δ⁻¹ ^ 2 * t ^ 2) := hQ'
        _ ≤ e ^ 2 * S.r u b ^ 4 * (Cδ ^ 2 * (M * Real.sqrt t + t) ^ 2) := by gcongr
        _ = _ := by simp only [mul_pow, sq_abs]; ring
    exact (div_le_iff₀ (sq_pos_of_pos hrb)).mpr hQabs
  · have hl := hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
    change S.lam u v * S.r u v ^ 2 * ‖S.phi u v‖ ^ 2 / (1 - S.mu u v) ≤
      (2 * M ^ 2 / δ) * (S.lam u v * S.r u v ^ 2) +
        (4 * S.m u b / δ ^ 2) * (S.lam u v * S.r u v)
    have hnum : 0 ≤ S.r u v ^ 2 * ‖S.phi u v‖ ^ 2 := by positivity
    have hh := (div_le_div_of_nonneg_left hnum hδ (hgap v hv)).trans
      (div_le_div_of_nonneg_right (hweighted v hv) hδ.le)
    have hh' := mul_le_mul_of_nonneg_left hh hl.le
    convert hh' using 1 <;> field_simp [hδ.ne']

/-- [node sec:charged-closure#incoming-envelope]
On each actual proper finite boundary the source envelope is a nonnegative
real L¹ density. One label-null set precedes every incoming row and controls
both the canonical representative and the raw weighted derivative. Its
integral is exactly the finite interaction norm. Finiteness is proved from
compact source continuity and the initial AC density, before `toReal`.
There are no estimate constants or smallness hypotheses. -/
theorem incoming_envelope {ui e a b v₀ ρ : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) :
    let K := exteriorDomain ui a b vb
    let g := fun v => (incomingEnvelope e S K a v).toReal
    interactionNorm e S K a v₀ < ⊤ ∧
      IntegrableOn g (Icc v₀ 0) ∧ (∀ v, 0 ≤ g v) ∧
      (∀ᵐ v ∂volume.restrict (Icc v₀ 0), ∀ u ∈ Icc a b, vb u ≤ v →
        ‖weightedJRepresentative e S a u v‖ ≤ g v ∧ ‖weightedJ S u v‖ ≤ g v) ∧
      (∫ v in v₀..0, g v) = (interactionNorm e S K a v₀).toReal ∧
      interactionNorm e S K a v₀ = initialInteraction S a v₀ + sourceInteraction e S K v₀ := by
  dsimp only
  have hab : a ≤ b := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have hia := (B.mem a ⟨le_rfl, hab⟩).1
  have hb := (B.mem b ⟨hab, le_rfl⟩).2.1
  have hproper (u : ℝ) (hu : u ∈ Icc a b) : u < vb u ∧ vb u ≤ 0 :=
    ⟨B.off_axis u hu, (B.mem u hu).2.2.2⟩
  have hv₀ : v₀ ≤ 0 := by simpa only [B.entry_label] using (hproper a ⟨le_rfl, hab⟩).2
  have hav₀ : a < v₀ := by simpa only [B.entry_label] using B.off_axis a ⟨le_rfl, hab⟩
  have hentry : outSeg a v₀ 0 ⊆ origDomain ui := by
    rintro ⟨u, v⟩ ⟨rfl, hv⟩
    exact ⟨hia, hav₀.trans_le hv₀, hav₀.le.trans hv.1, hv.2⟩
  let K := exteriorDomain ui a b vb
  have hK : IsCompact K := isCompact_exteriorDomain hab hia hb B.cont B.mono hproper
  have hKproper : K ⊆ origDomain ui ∩ {p | p.1 < p.2} := by
    intro p hp
    exact ⟨hp.1, (B.off_axis p.1 ⟨hp.2.1, hp.2.2.1⟩).trans_le hp.2.2.2⟩
  obtain ⟨_, hi, _, hsource, _, hsum, hfin⟩ :=
    Interaction.finite_cutoff_envelope_finiteness h hav₀ hv₀ hentry hK hKproper
  let f : ℝ × ℝ → ℂ := K.indicator (Function.uncurry (weightedJSource e S))
  have hif : Integrable f (volume.prod volume) :=
    (integrable_indicator_iff hK.measurableSet).mpr hsource
  have hsection (v : ℝ) :
      (∫⁻ u in {u | (u, v) ∈ K}, ‖weightedJSource e S u v‖ₑ) =
        ∫⁻ u, ‖f (u, v)‖ₑ := by
    have hm : MeasurableSet {u | (u, v) ∈ K} :=
      hK.measurableSet.preimage (measurable_id.prodMk measurable_const)
    rw [← lintegral_indicator hm]
    apply lintegral_congr
    intro u
    simp only [f, enorm_indicator_eq_indicator_enorm]
    rfl
  have hmeas : AEMeasurable (incomingEnvelope e S K a) (volume.restrict (Icc v₀ 0)) := by
    unfold incomingEnvelope
    simp_rw [hsection]
    exact hi.enorm.aemeasurable.add (hif.enorm.aemeasurable.lintegral_prod_left'.mono_measure
      Measure.restrict_le_self)
  have hae : ∀ᵐ v ∂volume.restrict (Icc v₀ 0), incomingEnvelope e S K a v < ⊤ :=
    ae_lt_top' hmeas hfin.ne
  have hg := integrable_toReal_of_lintegral_ne_top hmeas hfin.ne
  have hrep := ae_restrict_of_ae (s := Icc v₀ 0)
    (Interaction.ae_weighted_representation_on_orig h hia)
  refine ⟨hfin, hg, fun _ => ENNReal.toReal_nonneg, ?_, ?_, hsum⟩
  · filter_upwards [hae, hrep, ae_restrict_mem measurableSet_Icc] with v hv hrv hvm
    intro u hu huv
    have hseg : inSeg a u v ⊆ K := by
      rintro ⟨s, w⟩ ⟨has, hsu, rfl⟩
      have hs : s ∈ Icc a b := ⟨has, hsu.trans hu.2⟩
      have hsv := hsu.trans_lt ((B.off_axis u hu).trans_le huv)
      exact ⟨⟨hia.trans has, hsv.trans_le hvm.2, hsv.le, hvm.2⟩,
        has, hs.2, (B.mono hs hu hsu).trans huv⟩
    have hbound := representative_le_incoming_envelope e S K hu.1 hseg
    have hr : ‖weightedJRepresentative e S a u v‖ ≤ (incomingEnvelope e S K a v).toReal := by
      have hh := ENNReal.toReal_mono hv.ne hbound
      simpa only [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm] using hh
    refine ⟨hr, ?_⟩
    rwa [hrv hvm.2 u hu.1 ((B.off_axis u hu).trans_le huv)]
  · rw [intervalIntegral.integral_of_le hv₀, ← integral_Icc_eq_integral_Ioc]
    exact integral_toReal hmeas hae

/-- [internal]
Radial variation on every row of the actual stopped exterior, with the
actual accumulated interaction norm. The incoming envelope and its L¹
properties are derived above. All coefficients are the displayed fixed
stops `c,F`, independent of stage number, duration and shrinking scales. -/
theorem radial_variation {ui e a b v₀ ρ δ c Λ F ε : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (hc : 0 < c) (hF : 0 ≤ F)
    (hstop : ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F ε) :
    ∀ u ∈ Icc a b,
      (1 - F ^ 2) * (eVariationOn (S.a u) (Icc (vb u) 0)).toReal ≤
        c⁻¹ * (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal +
          F ^ 2 * ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ := by
  obtain ⟨_, hg, hg0, hmajor, hJ, _⟩ := incoming_envelope h B
  let g := fun v => (incomingEnvelope e S (exteriorDomain ui a b vb) a v).toReal
  intro u hu
  have hvb := (B.mem u hu).2.2.2
  have hv₀ : v₀ ≤ vb u := by
    rw [← B.entry_label]
    exact B.mono ⟨le_rfl, hu.1.trans hu.2⟩ hu hu.1
  have hs : outSeg u (vb u) 0 ⊆ origDomain ui := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    change x = u at hx
    subst x
    exact ⟨(B.mem u hu).1, (B.mem u hu).2.1,
      (B.off_axis u hu).le.trans hv.1, hv.2⟩
  have hE (v : ℝ) (hv : v ∈ Icc (vb u) 0) :
      (u, v) ∈ exteriorDomain ui a b vb := ⟨hs ⟨rfl, hv⟩, hu.1, hu.2, hv.1⟩
  have hgfull : IntervalIntegrable g volume v₀ 0 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hv₀.trans hvb)).mpr hg
  have hgrow : IntervalIntegrable g volume (vb u) 0 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hvb).mpr
      (hg.mono_set (Icc_subset_Icc hv₀ le_rfl))
  have hm : ∀ᵐ v ∂volume.restrict (Icc (vb u) 0), ‖weightedJ S u v‖ ≤ g v := by
    have hm := hmajor.filter_mono (ae_mono
      (Measure.restrict_mono (Icc_subset_Icc hv₀ le_rfl) le_rfl))
    filter_upwards [hm, ae_restrict_mem measurableSet_Icc] with v hv hvm
    exact (hv u hu hvm.1).2
  have hh := Interaction.row_variation_absorption h.solution (B.off_axis u hu) hvb hs hc hF
    (fun v hv => (hstop (u, v) (hE v hv)).2.2.1)
    (fun v hv => (hstop (u, v) (hE v hv)).2.2.2.2.1) g hgrow hm
  have hi : (∫ v in vb u..0, g v) ≤
      (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal := by
    rw [← hJ]
    exact intervalIntegral.integral_mono_interval hv₀ hvb le_rfl
      (Eventually.of_forall hg0) hgfull
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hc.le)) le_rfl)

/-- [internal]
Build the interaction profile setting from the actual finite boundary and
the literal weak stops. Its L¹ density, common-label majorant and terminal
upper radius are derived, rather than additional analytic inputs. The
consumer supplies the fixed box, terminal lower stop and interaction stop.
Constants have exactly the scope of the fixed numerical box. -/
theorem stopped_profile_data {ui e a b v₀ ρ R₀ δ c Λ F ε Jstop : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (hbox : ExteriorBox δ c Λ F ε ρ)
    (hstop : ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F ε)
    (hR₀ : S.r a 0 = R₀) (hR : ∀ u ∈ Icc a b, R₀ / 2 ≤ S.r u 0)
    (hJ : (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal ≤ Jstop) :
    Interaction.StoppedProfileData ui a b v₀ R₀ δ c Λ F ε Jstop S vb
      (fun v => (incomingEnvelope e S (exteriorDomain ui a b vb) a v).toReal) := by
  obtain ⟨_, hg, hg0, hmajor, hint, _⟩ := incoming_envelope h B
  have hab : a ≤ b := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have hrows (u : ℝ) (hu : u ∈ Icc a b) :
      ui ≤ u ∧ u < vb u ∧ vb u ≤ 0 ∧ v₀ ≤ vb u := by
    refine ⟨(B.mem u hu).1, B.off_axis u hu, (B.mem u hu).2.2.2, ?_⟩
    rw [← B.entry_label]
    exact B.mono ⟨le_rfl, hab⟩ hu hu.1
  have hpa : (a, 0) ∈ origDomain ui := by
    have hp := B.mem a ⟨le_rfl, hab⟩
    exact ⟨hp.1, hp.2.1, hp.2.1.le, le_rfl⟩
  refine ⟨?_, hrows, ?_, hbox.2.2.1, hbox.2.2.2.2.1, hbox.2.2.2.2.2.1,
    hstop, hg, Eventually.of_forall hg0, ?_, hint.trans_le hJ⟩
  · rw [← hR₀]
    exact h.solution.r_pos _ hpa hpa.2.1
  · intro u hu
    refine ⟨hR u hu, ?_⟩
    rw [← hR₀]
    exact (Terminal.terminal_radius_strictAntiOn h.solution).antitoneOn
      ⟨hpa.1, hpa.2.1⟩ ⟨(hrows u hu).1, (B.mem u hu).2.1⟩ hu.1
  · intro u hu
    filter_upwards [hmajor] with v hv huv
    exact (hv u hu huv).2

/-- [node sec:charged-closure#radial-variation]
All three row conclusions from the actual weak stops: the radial scalar
integral, the variation inequality, and the canonical exterior amplitude.
The real incoming envelope is constructed from the finite source history;
its norm and stopping budget are not extra profile assumptions. The
coefficients are exactly the fixed stops, uniform in all physical scales.
Source: charged_SF_new_version.tex:L3955–L4002. -/
theorem stopped_radial_variation {ui e a b v₀ ρ R₀ δ c Λ F ε Jstop : ℝ} {S : Fields}
    (h : OriginalData ui e S) {vb : ℝ → ℝ} {N : ℕ}
    (B : FiniteBoundary S ui a b v₀ ρ vb N) (hbox : ExteriorBox δ c Λ F ε ρ)
    (hstop : ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F ε)
    (hR₀ : S.r a 0 = R₀) (hR : ∀ u ∈ Icc a b, R₀ / 2 ≤ S.r u 0)
    (hJ : (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal ≤ Jstop) :
    ∀ u ∈ Icc a b,
      (∫ v in vb u..0, S.lam u v / S.r u v * ‖S.theta u v / (S.lam u v : ℂ)‖) ≤
        ‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ +
          (eVariationOn (S.a u) (Icc (vb u) 0)).toReal ∧
      (eVariationOn (S.a u) (Icc (vb u) 0)).toReal ≤
        c⁻¹ * (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal +
          F ^ 2 * (‖S.theta u (vb u) / (S.lam u (vb u) : ℂ)‖ +
            (eVariationOn (S.a u) (Icc (vb u) 0)).toReal) ∧
      (∀ v ∈ Icc (vb u) 0, ‖S.phi u v‖ ≤ Interaction.scalarBackground ui R₀ c F Jstop S) := by
  have d := stopped_profile_data h B hbox hstop hR₀ hR hJ
  intro u hu
  have hb0 := (B.mem u hu).2.2.2
  have hs : outSeg u (vb u) 0 ⊆ origDomain ui := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    change x = u at hx
    subst x
    exact ⟨(B.mem u hu).1, (B.mem u hu).2.1, (B.off_axis u hu).le.trans hv.1, hv.2⟩
  refine ⟨Interaction.row_scalar_integral_le h.solution (B.off_axis u hu) hb0 hs, ?_, ?_⟩
  · have hh := radial_variation h B hbox.2.2.1 hbox.2.2.2.2.1 hstop u hu
    linarith only [hh]
  · intro v hv
    exact ct_m0 h d (u, v) (d.row_mem hu hv)

end EmcsfAcExtension.Global.Closure
