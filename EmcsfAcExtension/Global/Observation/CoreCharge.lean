module

public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Global.Observation.Scaling
import EmcsfAcExtension.Global.Terminal.Mass
import EmcsfAcExtension.Global.Terminal.Scalar
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Energy on full outgoing sections

All integrals use the original null label, with the radial Jacobian `λ`.
In particular the existing regular axis belongs to the section; no inverse
of a normalized label at the axis is needed.
Source: charged_SF_new_version.tex:L2091–2093, L2110–2133; internal project record, (R1).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

/-- [internal]
Mass on a full outgoing section lies between zero and its boundary mass.
The proof uses the existing axis and the original frozen solution. -/
theorem Observation.mass_bounds_on_full_section {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v x : ℝ} (huv : u ≤ v)
    (hseg : outSeg u u v ⊆ D) (hx : x ∈ Icc u v) :
    0 ≤ S.m u x ∧ S.m u x ≤ S.m u v := by
  have haxis := (hS.axis u (hseg ⟨rfl, le_rfl, huv⟩)).2.1
  constructor
  · rw [← haxis]
    exact Terminal.mass_mono_out hS le_rfl hx.1
      (fun p hp => hseg ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩)
  · exact Terminal.mass_mono_out hS hx.1 hx.2
      (fun p hp => hseg ⟨hp.1, hx.1.trans hp.2.1, hp.2.2⟩)

/-- [internal]
The scalar energy is bounded by `2 m_b / δ`, with the exact coefficient.
The coefficient depends only on the positive gap `δ`, uniformly in the
coupling, section size, scalar background and solution. The radial measure
is expressed as `dr = λ dv` in the original labels. -/
theorem Observation.radial_scalar_energy {e δ : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hδ : 0 < δ) {u v : ℝ} (huv : u < v)
    (hseg : outSeg u u v ⊆ D) (hgap : ∀ x ∈ Icc u v, δ ≤ 1 - S.mu u x) :
    (∫ x in u..v, S.lam u x * ‖S.theta u x / S.lam u x‖ ^ 2) ≤ 2 * S.m u v / δ := by
  have cl := Calculus.continuousOn_out_section hS.cont_lam hseg
  have ct := Calculus.continuousOn_out_section hS.cont_theta hseg
  have cg : ContinuousOn (fun x => 1 - S.mu u x) (Icc u v) :=
    continuousOn_const.sub (Local.continuousOn_mu_out hS huv hseg)
  have cy := ct.div (Complex.continuous_ofReal.comp_continuousOn cl) (fun x hx => by
    change (S.lam u x : ℂ) ≠ 0
    exact_mod_cast (hS.lam_pos (u, x) (hseg ⟨rfl, hx⟩)).ne')
  have hi := (cl.mul (cy.norm.pow 2)).intervalIntegrable_of_Icc (μ := volume) huv.le
  have hig := ((cl.mul cg).mul (cy.norm.pow 2)).intervalIntegrable_of_Icc (μ := volume) huv.le
  have he := intervalIntegral.integral_mono_on huv.le (hi.const_mul δ) hig
    (fun x hx => by
      have hp : 0 ≤ S.lam u x * ‖S.theta u x / S.lam u x‖ ^ 2 :=
        mul_nonneg (hS.lam_pos (u, x) (hseg ⟨rfl, hx⟩)).le (sq_nonneg _)
      simpa only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Function.comp_apply,
        mul_assoc, mul_left_comm, mul_comm] using!
        mul_le_mul_of_nonneg_right (hgap x hx) hp)
  rw [intervalIntegral.integral_const_mul] at he
  apply (le_div_iff₀ hδ).mpr
  simpa only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply, Function.comp_apply, mul_comm] using!
    he.trans (Local.RelCharge.mass_controls_radial_flux hS huv hseg)

/-- [internal]
On any positive-radius tail of a full outgoing section, Cauchy–Schwarz
bounds the squared scalar difference by radial energy times the exact
inverse-radius integral. The universal coefficient is one. -/
theorem Observation.scalar_difference_sq_le {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a v : ℝ} (hua : u < a) (hav : a ≤ v)
    (hseg : outSeg u u v ⊆ D) :
    ‖S.phi u v - S.phi u a‖ ^ 2 ≤
      (∫ x in a..v, S.lam u x * ‖S.theta u x / S.lam u x‖ ^ 2) *
        ((S.r u a)⁻¹ - (S.r u v)⁻¹) := by
  have htail : outSeg u a v ⊆ D := fun p hp =>
    hseg ⟨hp.1, hua.le.trans hp.2.1, hp.2.2⟩
  have cl := Calculus.continuousOn_out_section hS.cont_lam htail
  have cr := Calculus.continuousOn_out_section hS.cont_r htail
  have ct := Calculus.continuousOn_out_section hS.cont_theta htail
  have hl (x : ℝ) (hx : x ∈ Icc a v) := hS.lam_pos (u, x) (htail ⟨rfl, hx⟩)
  have hr (x : ℝ) (hx : x ∈ Icc a v) :=
    hS.r_pos (u, x) (htail ⟨rfl, hx⟩) (hua.trans_le hx.1)
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl) (fun x hx => by
    change (S.lam u x : ℂ) ≠ 0
    exact_mod_cast (hl x hx).ne')
  let f : ℝ → ℝ := fun x => Real.sqrt (S.lam u x) * ‖S.theta u x / S.lam u x‖
  let g : ℝ → ℝ := fun x => Real.sqrt (S.lam u x) / S.r u x
  have cf : ContinuousOn f (Icc a v) := cl.sqrt.mul cy.norm
  have cg : ContinuousOn g (Icc a v) := cl.sqrt.div cr (fun x hx => (hr x hx).ne')
  have hfg (x : ℝ) (hx : x ∈ Icc a v) :
      ‖S.phiV u x‖ = f x * g x := by
    dsimp [Fields.phiV, f, g]
    rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr x hx), abs_of_pos (hl x hx)]
    calc
      ‖S.theta u x‖ / S.r u x =
          S.lam u x * ‖S.theta u x‖ / (S.lam u x * S.r u x) := by
            field_simp [(hl x hx).ne', (hr x hx).ne']
      _ = Real.sqrt (S.lam u x) ^ 2 * ‖S.theta u x‖ /
          (S.lam u x * S.r u x) := by rw [Real.sq_sqrt (hl x hx).le]
      _ = _ := by ring
  have hfsq (x : ℝ) (hx : x ∈ Icc a v) :
      f x ^ 2 = S.lam u x * ‖S.theta u x / S.lam u x‖ ^ 2 := by
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt (hl x hx).le]
  have hgsq (x : ℝ) (hx : x ∈ Icc a v) : g x ^ 2 = S.lam u x / S.r u x ^ 2 := by
    dsimp [g]
    rw [div_pow, Real.sq_sqrt (hl x hx).le]
  have hinv : (∫ x in a..v, S.lam u x / S.r u x ^ 2) =
      (S.r u a)⁻¹ - (S.r u v)⁻¹ := by
    have hd : ∀ x ∈ Ioo a v, HasDerivAt (fun x => -(S.r u x)⁻¹)
        (S.lam u x / S.r u x ^ 2) x := by
      intro x hx
      simpa only [Pi.neg_apply, Pi.inv_apply, neg_div, neg_neg] using!
        ((Local.IsSolution.hasDerivAt_radius_out hS hseg
          ⟨hua.trans hx.1, hx.2⟩).inv (hr x (Ioo_subset_Icc_self hx)).ne').neg
    simpa only [Pi.neg_apply, Pi.inv_apply, neg_sub_neg] using!
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hav
        (cr.inv₀ (fun x hx => (hr x hx).ne')).neg hd
        ((cl.div (cr.pow 2) (fun x hx => pow_ne_zero 2 (hr x hx).ne')).intervalIntegrable_of_Icc
          hav)
  have hφ := (hS.eq_out u a v hua hav htail).2.2.2.2.2.1
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := S.phiV u) hav
  have hn : ‖S.phi u v - S.phi u a‖ ≤ ∫ x in a..v, f x * g x := by
    rw [← hφ.2, intervalIntegral.integral_congr (fun x hx => hfg x (by
      simpa only [uIcc_of_le hav] using hx))] at hnorm
    exact hnorm
  have hnonneg : 0 ≤ ∫ x in a..v, f x * g x := (norm_nonneg _).trans hn
  have hcs := Terminal.integral_cauchy_schwarz hav cf cg
  rw [intervalIntegral.integral_congr (fun x hx => hfsq x (by
      simpa only [uIcc_of_le hav] using hx)),
    intervalIntegral.integral_congr (fun x hx => hgsq x (by
      simpa only [uIcc_of_le hav] using hx)), hinv] at hcs
  exact ((sq_le_sq₀ (norm_nonneg _) hnonneg).mpr hn).trans hcs

/-- [internal]
The physical radial scalar estimate, before any lower bound for the
normalized radius is known. The coefficient is exactly `sqrt (2 m_b / δ)`;
it is uniform in the scalar background and does not use a central supremum. -/
theorem Observation.physical_radial_scalar_bound
    {e δ : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hδ : 0 < δ) {u a v : ℝ} (hua : u < a) (hav : a ≤ v)
    (hseg : outSeg u u v ⊆ D) (hgap : ∀ x ∈ Icc u v, δ ≤ 1 - S.mu u x) :
    ‖S.phi u a‖ ≤ ‖S.phi u v‖ + Real.sqrt (2 * S.m u v / δ) / Real.sqrt (S.r u a) := by
  have huv := hua.trans_le hav
  have hr := hS.r_pos (u, a) (hseg ⟨rfl, hua.le, hav⟩) hua
  have hrv := hS.r_pos (u, v) (hseg ⟨rfl, huv.le, le_rfl⟩) huv
  have hm := (Observation.mass_bounds_on_full_section hS huv.le hseg ⟨huv.le, le_rfl⟩).1
  have cl := Calculus.continuousOn_out_section hS.cont_lam hseg
  have ct := Calculus.continuousOn_out_section hS.cont_theta hseg
  have cy := ct.div (continuous_ofReal.comp_continuousOn cl) (fun x hx => by
    change (S.lam u x : ℂ) ≠ 0
    exact_mod_cast (hS.lam_pos (u, x) (hseg ⟨rfl, hx⟩)).ne')
  have hi := (cl.mul (cy.norm.pow 2)).intervalIntegrable_of_Icc (μ := volume) huv.le
  have hnonneg : ∀ x ∈ Icc u v, 0 ≤ S.lam u x * ‖S.theta u x / S.lam u x‖ ^ 2 :=
    fun x hx => mul_nonneg (hS.lam_pos (u, x) (hseg ⟨rfl, hx⟩)).le (sq_nonneg _)
  have htail := intervalIntegral.integral_mono_interval hua.le hav le_rfl
    ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => hnonneg x ⟨hx.1.le, hx.2⟩) hi
  have henergy := htail.trans (Observation.radial_scalar_energy hS hδ huv hseg hgap)
  have ht0 : 0 ≤ ∫ x in a..v, S.lam u x * ‖S.theta u x / S.lam u x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hav (fun x hx => hnonneg x ⟨hua.le.trans hx.1, hx.2⟩)
  have hsq := (Observation.scalar_difference_sq_le hS hua hav hseg).trans
    ((mul_le_mul_of_nonneg_left (sub_le_self _ (inv_nonneg.mpr hrv.le)) ht0).trans
      (mul_le_mul_of_nonneg_right henergy (inv_nonneg.mpr hr.le)))
  rw [← div_eq_mul_inv] at hsq
  have hsqrt := Real.le_sqrt_of_sq_le hsq
  rw [Real.sqrt_div (div_nonneg (mul_nonneg (by norm_num) hm) hδ.le)] at hsqrt
  calc
    ‖S.phi u a‖ ≤ ‖S.phi u v‖ + ‖S.phi u v - S.phi u a‖ :=
      norm_le_insert (S.phi u v) (S.phi u a)
    _ ≤ _ := add_le_add_right hsqrt _

private theorem scalar_weighted_square {r p H B : ℝ} (hr : 0 < r)
    (hp : 0 ≤ p) (hH : 0 ≤ H) (hB : 0 ≤ B)
    (h : p ≤ H + B / Real.sqrt r) :
    r ^ 2 * p ^ 2 ≤ 2 * H ^ 2 * r ^ 2 + 2 * B ^ 2 * r := by
  calc
    r ^ 2 * p ^ 2 ≤ r ^ 2 * (H + B / Real.sqrt r) ^ 2 :=
      mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ hp (add_nonneg hH (div_nonneg hB (Real.sqrt_nonneg _)))).mpr h)
        (sq_nonneg _)
    _ ≤ r ^ 2 * (2 * H ^ 2 + 2 * (B / Real.sqrt r) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      nlinarith only [sq_nonneg (H - B / Real.sqrt r)]
    _ = _ := by
      rw [div_pow, Real.sq_sqrt hr.le]
      field_simp

/-- [internal]
The weighted Maxwell factor is integrable and has an explicit radial
moment bound under a `r⁻¹/²` scalar envelope. The exact coefficients depend
only on the positive gap and the envelope coefficient `B`; no central
scalar supremum enters this estimate. -/
theorem Observation.maxwell_factor_le_of_scalar_envelope
    {e δ H B : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hδ : 0 < δ) (hH : 0 ≤ H) (hB : 0 ≤ B)
    {u v : ℝ} (huv : u < v) (hseg : outSeg u u v ⊆ D)
    (hgap : ∀ x ∈ Icc u v, δ ≤ 1 - S.mu u x)
    (hφ : ∀ x ∈ Ioc u v, ‖S.phi u x‖ ≤ H + B / Real.sqrt (S.r u x)) :
    (∫ x in u..v, S.lam u x * S.r u x ^ 2 * ‖S.phi u x‖ ^ 2 / (1 - S.mu u x)) ≤
      2 * H ^ 2 * S.r u v ^ 3 / (3 * δ) + B ^ 2 * S.r u v ^ 2 / δ := by
  have cl := Calculus.continuousOn_out_section hS.cont_lam hseg
  have cr := Calculus.continuousOn_out_section hS.cont_r hseg
  have cp := Calculus.continuousOn_out_section hS.cont_phi hseg
  have cg : ContinuousOn (fun x => 1 - S.mu u x) (Icc u v) :=
    continuousOn_const.sub (Local.continuousOn_mu_out hS huv hseg)
  have hg (x : ℝ) (hx : x ∈ Icc u v) := hS.one_sub_mu_pos (u, x) (hseg ⟨rfl, hx⟩)
  have ig := (((cl.mul (cr.pow 2)).mul (cp.norm.pow 2)).div cg
    (fun x hx => (hg x hx).ne')).intervalIntegrable_of_Icc (μ := volume) huv.le
  have i₂ := (cl.mul (cr.pow 2)).intervalIntegrable_of_Icc (μ := volume) huv.le
  have i₁ := (cl.mul cr).intervalIntegrable_of_Icc (μ := volume) huv.le
  have hp : ∀ x ∈ Icc u v,
      S.lam u x * S.r u x ^ 2 * ‖S.phi u x‖ ^ 2 / (1 - S.mu u x) ≤
        (2 * H ^ 2 / δ) * (S.lam u x * S.r u x ^ 2) +
        (2 * B ^ 2 / δ) * (S.lam u x * S.r u x) := by
    intro x hx
    have hl := hS.lam_pos (u, x) (hseg ⟨rfl, hx⟩)
    by_cases hxu : x = u
    · subst x
      simp [(hS.axis u (hseg ⟨rfl, le_rfl, huv.le⟩)).1]
    · have hux : u < x := lt_of_le_of_ne hx.1 (Ne.symm hxu)
      have hr := hS.r_pos (u, x) (hseg ⟨rfl, hx⟩) hux
      have hs := scalar_weighted_square hr (norm_nonneg _) hH hB (hφ x ⟨hux, hx.2⟩)
      calc
        _ = S.lam u x * (S.r u x ^ 2 * ‖S.phi u x‖ ^ 2 / (1 - S.mu u x)) := by ring
        _ ≤ S.lam u x * ((2 * H ^ 2 * S.r u x ^ 2 + 2 * B ^ 2 * S.r u x) / δ) := by
          apply mul_le_mul_of_nonneg_left _ hl.le
          exact (div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg _) (sq_nonneg _))
            hδ (hgap x hx)).trans (div_le_div_of_nonneg_right hs hδ.le)
        _ = _ := by ring
  have hi := intervalIntegral.integral_mono_on huv.le ig
    ((i₂.const_mul _).add (i₁.const_mul _)) hp
  rw [intervalIntegral.integral_add (i₂.const_mul _) (i₁.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.div_apply] at hi
  have hm₁ := Local.outgoing_radius_moment hS huv.le hseg 1
  have hm₂ := Local.outgoing_radius_moment hS huv.le hseg 2
  norm_num at hm₁ hm₂
  rw [hm₂, hm₁] at hi
  convert hi using 1
  ring

/-- [internal]
Combining the exact Maxwell Cauchy–Schwarz inequality with the scalar
envelope gives the core-charge estimate with explicit coefficients.
The coefficients depend only on `δ` and `B`, uniformly in the coupling,
background, section size and solution. -/
theorem Observation.core_charge_of_scalar_envelope
    {e δ H B : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hδ : 0 < δ) (hH : 0 ≤ H) (hB : 0 ≤ B)
    {u v : ℝ} (huv : u < v) (hseg : outSeg u u v ⊆ D)
    (hgap : ∀ x ∈ Icc u v, δ ≤ 1 - S.mu u x)
    (hφ : ∀ x ∈ Ioc u v, ‖S.phi u x‖ ≤ H + B / Real.sqrt (S.r u x)) :
    S.Q u v ^ 2 ≤ e ^ 2 * (2 * S.m u v) *
      (2 * H ^ 2 * S.r u v ^ 3 / (3 * δ) + B ^ 2 * S.r u v ^ 2 / δ) := by
  have hpositive : 0 ≤ ∫ x in u..v,
      S.lam u x * S.r u x ^ 2 * ‖S.phi u x‖ ^ 2 / (1 - S.mu u x) :=
    intervalIntegral.integral_nonneg huv.le (fun x hx =>
      div_nonneg (mul_nonneg
        (mul_nonneg (hS.lam_pos (u, x) (hseg ⟨rfl, hx⟩)).le (sq_nonneg _))
        (sq_nonneg _)) (hS.one_sub_mu_pos (u, x) (hseg ⟨rfl, hx⟩)).le)
  have hm := (Observation.mass_bounds_on_full_section hS huv.le hseg ⟨huv.le, le_rfl⟩).1
  calc
    _ ≤ _ := Local.RelCharge.maxwell_cauchy_schwarz hS huv hseg
    _ ≤ e ^ 2 * (2 * S.m u v) *
        (∫ x in u..v, S.lam u x * S.r u x ^ 2 * ‖S.phi u x‖ ^ 2 / (1 - S.mu u x)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Local.RelCharge.mass_controls_radial_flux hS huv hseg)
          (sq_nonneg e)) hpositive
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Observation.maxwell_factor_le_of_scalar_envelope hS hδ hH hB huv hseg hgap hφ)
      (mul_nonneg (sq_nonneg e) (mul_nonneg (by norm_num) hm))

/-- [node prop:charged-observation#physical-radial-charge-bound]
The physical boundary charge estimate with explicit coefficient `2 / δ²`.
The coefficient depends only on the gap `0 < δ < 1`, uniformly in radius,
coupling, scalar background and solution. This is proved before any
assumption that the normalized outer radius is large. -/
theorem Observation.physical_radial_charge_bound {e δ : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hδ : 0 < δ) (hδ1 : δ < 1)
    {u v : ℝ} (huv : u < v) (hseg : outSeg u u v ⊆ D)
    (hgap : ∀ x ∈ Icc u v, δ ≤ 1 - S.mu u x) :
    S.Q u v ^ 2 / S.r u v ^ 2 ≤
      (2 / δ ^ 2) * e ^ 2 * S.r u v ^ 2 * S.mu u v *
        (‖S.phi u v‖ ^ 2 + S.mu u v) := by
  have hm := (Observation.mass_bounds_on_full_section hS huv.le hseg ⟨huv.le, le_rfl⟩).1
  have hr := hS.r_pos (u, v) (hseg ⟨rfl, huv.le, le_rfl⟩) huv
  have hE : 0 ≤ 2 * S.m u v / δ := div_nonneg (mul_nonneg (by norm_num) hm) hδ.le
  have hφ : ∀ x ∈ Ioc u v, ‖S.phi u x‖ ≤
      ‖S.phi u v‖ + Real.sqrt (2 * S.m u v / δ) / Real.sqrt (S.r u x) :=
    fun x hx => Observation.physical_radial_scalar_bound hS hδ hx.1 hx.2 hseg hgap
  have hq := Observation.core_charge_of_scalar_envelope hS hδ (norm_nonneg _)
    (Real.sqrt_nonneg _) huv hseg hgap hφ
  rw [Real.sq_sqrt hE] at hq
  have hsharp : S.Q u v ^ 2 / S.r u v ^ 2 ≤
      (e ^ 2 * S.r u v ^ 2 * S.mu u v) *
        ((2 / (3 * δ)) * ‖S.phi u v‖ ^ 2 + S.mu u v / δ ^ 2) := by
    apply (div_le_div_of_nonneg_right hq (sq_nonneg _)).trans_eq
    dsimp [Fields.mu]
    field_simp
  have hcoef : 2 / (3 * δ) ≤ 2 / δ ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
    have hd := mul_nonneg hδ.le (sub_nonneg.mpr hδ1.le)
    nlinarith only [hd, hδ]
  have hμ : 0 ≤ S.mu u v := by
    exact div_nonneg (mul_nonneg (by norm_num) hm) hr.le
  have hbracket : (2 / (3 * δ)) * ‖S.phi u v‖ ^ 2 + S.mu u v / δ ^ 2 ≤
      (2 / δ ^ 2) * (‖S.phi u v‖ ^ 2 + S.mu u v) := by
    calc
      _ ≤ (2 / δ ^ 2) * ‖S.phi u v‖ ^ 2 + (2 / δ ^ 2) * S.mu u v := by
        apply add_le_add (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
        calc
          _ ≤ 2 * (S.mu u v / δ ^ 2) := by
            nlinarith only [div_nonneg hμ (sq_nonneg δ)]
          _ = _ := by ring
      _ = _ := by ring
  have he := mul_le_mul_of_nonneg_left hbracket
    (mul_nonneg (mul_nonneg (sq_nonneg e) (sq_nonneg (S.r u v))) hμ)
  exact hsharp.trans (by simpa only [mul_assoc, mul_comm, mul_left_comm] using he)

/-- [internal]
At the central point the physical charge bound is at most
`(2 / δ) η sqrt μ`. The coefficient depends only on the gap, uniformly in
all physical data. The hypothesis `hcharge` is discharged by
`Observation.physical_radial_charge_bound`. -/
theorem Observation.central_charge_of_physical_charge
    {δ e r μ q : ℝ} {φ y H : ℂ} (hδ : 0 < δ) (hr : 0 < r) (hμ : 0 ≤ μ)
    (hsmall : μ + ‖y‖ ≤ 1) (hH : H = φ + y)
    (hcharge : q ^ 2 / r ^ 2 ≤ (2 / δ ^ 2) * e ^ 2 * r ^ 2 * μ * (‖φ‖ ^ 2 + μ)) :
    |q| / r ≤ (2 / δ) * (|e| * r * (1 + ‖H‖)) * Real.sqrt μ := by
  have hφ : ‖φ‖ ≤ 1 + ‖H‖ := by
    have he : φ = H - y := by rw [hH]; abel
    rw [he]
    have ht := norm_sub_le H y
    linarith
  have hb : ‖φ‖ ^ 2 + μ ≤ 2 * (1 + ‖H‖) ^ 2 := by
    have hp := (sq_le_sq₀ (norm_nonneg φ) (by positivity : 0 ≤ 1 + ‖H‖)).mpr hφ
    have hμ1 : μ ≤ 1 := by linarith [norm_nonneg y]
    nlinarith only [hp, hμ1, norm_nonneg H]
  have hq := hcharge.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  apply (sq_le_sq₀ (div_nonneg (abs_nonneg _) hr.le) (by positivity)).mp
  convert hq using 1 <;> simp only [mul_pow, div_pow, sq_abs, Real.sq_sqrt hμ]
  ring

/-- [node eq:co-normalization-large]
After fixing the positive gap, charged threshold `η` and required radius
`L₀`, choose physical smallness `δ` before quantifying over any solution,
coupling, section or scalar background. In the positive-scale branch the
normalized outer radius is at least `L₀`. The charge bound is derived on
the full original section, without presupposing this conclusion. -/
theorem co_normalization_large {δ₀ η L₀ : ℝ}
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ < 1) (hη : 0 ≤ η) (hL₀ : 0 < L₀) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (e : ℝ) (S : Fields) (D : Set (ℝ × ℝ)), IsSolution e S D →
      ∀ (u v : ℝ) (H : ℂ), u < v → outSeg u u v ⊆ D →
        (∀ x ∈ Icc u v, δ₀ ≤ 1 - S.mu u x) →
        H = S.phi u v + S.theta u v / S.lam u v →
        S.mu u v + ‖S.theta u v / S.lam u v‖ ≤ δ →
        |e| * S.r u v * (1 + ‖H‖) ≤ η →
        0 < S.m u v + S.r u v * ‖S.theta u v / S.lam u v‖ + |S.Q u v| →
        L₀ ≤ S.r u v /
          (S.m u v + S.r u v * ‖S.theta u v / S.lam u v‖ + |S.Q u v|) := by
  obtain ⟨δ, hδ, hδ1, hδprop⟩ := co_normalization_large_of_physical_charge
    (show 0 ≤ 2 / δ₀ by positivity) hη hL₀
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro e S D hS u v H huv hseg hgap hH hsmall hcharged hscale
  have hr := hS.r_pos (u, v) (hseg ⟨rfl, huv.le, le_rfl⟩) huv
  have hm := (Observation.mass_bounds_on_full_section hS huv.le hseg ⟨huv.le, le_rfl⟩).1
  have hμ : 0 ≤ S.mu u v := by dsimp [Fields.mu]; positivity
  have hq := Observation.central_charge_of_physical_charge hδ₀ hr hμ (hsmall.trans hδ1) hH
    (Observation.physical_radial_charge_bound hS hδ₀ hδ₀1 huv hseg hgap)
  apply hδprop (S.r u v) (S.m u v) (S.Q u v) (S.theta u v / S.lam u v) hr hm hscale
  · exact hsmall
  · exact hq.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcharged (show 0 ≤ 2 / δ₀ by positivity)) (Real.sqrt_nonneg _))

/-- [internal]
The original radius on a full outgoing section is at most its boundary
radius, directly from the positive outgoing radius density. -/
theorem Observation.radius_le_boundary {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v x : ℝ} (hseg : outSeg u u v ⊆ D)
    (hx : x ∈ Icc u v) : S.r u x ≤ S.r u v := by
  have htail : outSeg u x v ⊆ D := fun p hp => hseg ⟨hp.1, hx.1.trans hp.2.1, hp.2.2⟩
  have he := (Calculus.out_integralForm hS hx.1 hx.2 htail).1
  have hi : 0 ≤ ∫ y in x..v, S.lam u y :=
    intervalIntegral.integral_nonneg hx.2 (fun y hy => (hS.lam_pos (u, y) (htail ⟨rfl, hy⟩)).le)
  rw [← he.2] at hi
  exact sub_nonneg.mp hi

end EmcsfAcExtension.Global
