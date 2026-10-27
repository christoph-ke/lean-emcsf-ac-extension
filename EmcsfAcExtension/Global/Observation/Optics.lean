module

public import Mathlib
public import EmcsfAcExtension.Frozen.IsSolution
import EmcsfAcExtension.Global.Terminal.OpticalUpper
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Infra.AC.Quotient
import EmcsfAcExtension.Infra.AC.Intervals

/-! # Truncated optical integrals for observation

These estimates concern a positive-radius radial path with the original
mass and charge profiles. The logarithmic expansion formulas are used only
on such a path. No limit toward the regular axis is taken.
Source: charged_SF_new_version.tex:L2140–2162; internal project record, co-expansions.
-/

public section

open Set MeasureTheory Filter

namespace EmcsfAcExtension.Global

/-- [internal]
An optical logarithmic integral bounded by `A` yields the normalized
expansion bounds, with the exact boundary value `1/2`. -/
theorem co_expansions_of_log_integral {x I A : ℝ} (hI : 0 ≤ I) (hIA : I ≤ A)
    (hx : x = (1 / 2 : ℝ) * Real.exp (-I)) :
    (1 / 2 : ℝ) * Real.exp (-A) ≤ x ∧ x ≤ 1 / 2 := by
  rw [hx]
  constructor
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hIA)) (by norm_num)
  · have h := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (neg_nonpos.mpr hI)) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    simpa using h

/-- [internal]
The inverse-radius kernel is exact for a positive AC radius and its actual
a.e. density. No monotonicity or inverse coordinate is assumed. The
coefficient is exactly one, uniformly in both functions and the interval. -/
theorem Observation.integral_inverse_radius_of_ac {r w : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hr : AbsolutelyContinuousOnInterval r a b)
    (_hw : ContinuousOn w (Icc a b)) (hp : ∀ x ∈ Icc a b, 0 < r x)
    (hd : ∀ᵐ x ∂volume.restrict (Icc a b), HasDerivAt r (w x) x) :
    (∫ x in a..b, w x / r x ^ 2) = (r a)⁻¹ - (r b)⁻¹ := by
  have cr : ContinuousOn r (Icc a b) := by simpa only [uIcc_of_le hab] using hr.continuousOn
  obtain ⟨c, hc, hcl⟩ := isCompact_Icc.exists_forall_le' cr hp
  have hi := hr.inv_of_le_norm hc (fun x hx => by
    rw [uIcc_of_le hab] at hx
    exact (hcl x hx).trans (le_abs_self _))
  have hd' : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt (fun x => (r x)⁻¹) (-w x / r x ^ 2) x := by
    have hdg := (ae_restrict_iff' measurableSet_Icc).mp hd
    filter_upwards [hdg] with x hx hmem
    have hxm : x ∈ Icc a b := by simpa only [uIcc_of_le hab] using hmem
    simpa only [Pi.inv_apply] using! (hx hxm).inv (hp x hxm).ne'
  have he := hi.integral_eq_sub_of_ae_hasDerivAt_real hd'
  rw [show (fun x => -w x / r x ^ 2) = (fun x => -(w x / r x ^ 2)) by
    funext x; ring, intervalIntegral.integral_neg] at he
  linarith only [he]

private theorem density_continuousOn {r m q w : ℝ → ℝ} {a b : ℝ}
    (cr : ContinuousOn r (Icc a b)) (cm : ContinuousOn m (Icc a b))
    (cq : ContinuousOn q (Icc a b)) (cw : ContinuousOn w (Icc a b))
    (hr : ∀ x ∈ Icc a b, 0 < r x) (hg : ∀ x ∈ Icc a b, 0 < 1 - 2 * m x / r x) :
    ContinuousOn (fun x => w x * (2 * m x / r x - q x ^ 2 / r x ^ 2) /
      ((1 - 2 * m x / r x) * r x)) (Icc a b) := by
  have cμ : ContinuousOn (fun x => 2 * m x / r x) (Icc a b) :=
    (continuousOn_const.mul cm).div cr (fun x hx => (hr x hx).ne')
  exact (cw.mul (cμ.sub ((cq.pow 2).div (cr.pow 2)
    (fun x hx => pow_ne_zero 2 (hr x hx).ne')))).div
    ((continuousOn_const.sub cμ).mul cr)
    (fun x hx => (mul_pos (hg x hx) (hr x hx)).ne')

/-- [internal]
The logarithmic incoming expansion on an original outgoing section is an
AC primitive of the frozen optical density. This derives the representative
from the original integral equations, including every proper subsegment. -/
theorem Observation.outgoing_log_neg_nu_integralForm
    {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    {u a b : ℝ} (hua : u < a) (hab : a ≤ b) (hseg : outSeg u a b ⊆ D) :
    IntegralForm (fun v => Real.log (-S.nu u v))
      (fun v => S.lam u v * (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
        ((1 - S.mu u v) * S.r u v)) a b := by
  have cn := Calculus.continuousOn_out_section hS.cont_nu hseg
  have cr := Calculus.continuousOn_out_section hS.cont_r hseg
  have cm := Calculus.continuousOn_out_section hS.cont_m hseg
  have cq := Calculus.continuousOn_out_section hS.cont_Q hseg
  have cl := Calculus.continuousOn_out_section hS.cont_lam hseg
  have hp (v : ℝ) (hv : v ∈ Icc a b) := hseg (show (u, v) ∈ outSeg u a b from ⟨rfl, hv⟩)
  have hr (v : ℝ) (hv : v ∈ Icc a b) := hS.r_pos (u, v) (hp v hv) (hua.trans_le hv.1)
  have hg (v : ℝ) (hv : v ∈ Icc a b) := hS.one_sub_mu_pos (u, v) (hp v hv)
  have hn (v : ℝ) (hv : v ∈ Icc a b) := neg_pos.mpr (hS.nu_neg (u, v) (hp v hv))
  obtain ⟨c, hc, hcl⟩ := isCompact_Icc.exists_forall_le' cn.neg hn
  have hs := Local.IsSolution.out_section hS hua hab hseg
  have hac := hs.2.1.1.neg.log_of_pos_le hc (by simpa only [uIcc_of_le hab] using hcl)
  have hdensity : ContinuousOn (fun v => S.lam u v * (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
      ((1 - S.mu u v) * S.r u v)) (Icc a b) :=
    density_continuousOn cr cm cq cl hr hg
  apply integralForm_of_ac_of_ae_hasDerivAt hac (hdensity.intervalIntegrable_of_Icc hab)
  rw [uIcc_of_le hab]
  apply (ae_restrict_iff' measurableSet_Icc).mp
  filter_upwards [hs.2.1.2, ae_restrict_mem measurableSet_Icc] with v hv hmem
  have he := (hv.neg).log (hn v hmem).ne'
  apply he.congr_deriv
  change (-S.rUV u v) / (-S.nu u v) = _
  dsimp [Fields.rUV]
  field_simp [(hr v hmem).ne', (hg v hmem).ne', (hS.nu_neg (u, v) (hp v hmem)).ne]

/-- [internal]
A logarithmic increment from an interior value to the boundary value
`1/2` gives its exact exponentially damped expansion. There are no
constants and no hypothesis on the original-coordinate optical size. -/
theorem Observation.expansion_eq_of_log_increment {f₀ f₁ c I : ℝ}
    (h₀ : 0 < f₀) (h₁ : 0 < f₁) (hlog : Real.log f₁ - Real.log f₀ = I)
    (hb : c * f₁ = 1 / 2) : c * f₀ = (1 / 2 : ℝ) * Real.exp (-I) := by
  have he : f₀ = f₁ * Real.exp (-I) := by
    calc
      _ = Real.exp (Real.log f₀) := (Real.exp_log h₀).symm
      _ = Real.exp (Real.log f₁ + -I) := congrArg Real.exp (by linarith only [hlog])
      _ = _ := by rw [Real.exp_add, Real.exp_log h₁]
  rw [he, ← mul_assoc, hb]

/-- [internal]
With mass at most `M`, the optical density is at most `2M/(δr²)`.
The coefficient depends only on `M` and the positive gap, uniformly in
radius and charge. It is used with the physical bound `M = 2s`. -/
theorem Observation.optical_density_bounds_of_mass_bound {m q r δ M : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hM : 0 ≤ M) (hm : m ≤ M)
    (hgap : δ ≤ 1 - 2 * m / r) (hcharge : q ^ 2 / r ^ 2 ≤ 2 * m / r) :
    0 ≤ (2 * m / r - q ^ 2 / r ^ 2) / ((1 - 2 * m / r) * r) ∧
      (2 * m / r - q ^ 2 / r ^ 2) / ((1 - 2 * m / r) * r) ≤ 2 * M / (δ * r ^ 2) := by
  have hg := hδ.trans_le hgap
  have hden := mul_pos hg hr
  refine ⟨div_nonneg (sub_nonneg.mpr hcharge) hden.le, ?_⟩
  calc
    _ ≤ (2 * m / r) / ((1 - 2 * m / r) * r) :=
      div_le_div_of_nonneg_right
        (sub_le_self _ (div_nonneg (sq_nonneg _) (sq_nonneg _))) hden.le
    _ ≤ (2 * M / r) / ((1 - 2 * m / r) * r) := div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num)) hr.le) hden.le
    _ ≤ (2 * M / r) / (δ * r) := div_le_div_of_nonneg_left (by positivity)
      (mul_pos hδ hr) (mul_le_mul_of_nonneg_right hgap hr.le)
    _ = _ := by ring

/-- [internal]
The outgoing optical integral is controlled directly in the original null
label, with physical mass bound `2s` and physical radius cutoff `sρ`.
Its coefficient `4/(δρ)` depends only on the gap and normalized cutoff,
uniformly in the coupling, scale, original optical sizes and solution. -/
theorem Observation.outgoing_truncated_optics_of_mass_charge_bounds
    {e δ ρ s : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hs : 0 < s)
    {u a b : ℝ} (hua : u < a) (hab : a ≤ b) (hseg : outSeg u a b ⊆ D)
    (hcut : s * ρ ≤ S.r u a)
    (hm : ∀ v ∈ Icc a b, S.m u v ≤ 2 * s)
    (hgap : ∀ v ∈ Icc a b, δ ≤ 1 - S.mu u v)
    (hcharge : ∀ v ∈ Icc a b, S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v) :
    0 ≤ (∫ v in a..b, S.lam u v * (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
      ((1 - S.mu u v) * S.r u v)) ∧
    (∫ v in a..b, S.lam u v * (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
      ((1 - S.mu u v) * S.r u v)) ≤ 4 / (δ * ρ) := by
  have hp (v : ℝ) (hv : v ∈ Icc a b) := hseg (show (u, v) ∈ outSeg u a b from ⟨rfl, hv⟩)
  have hr (v : ℝ) (hv : v ∈ Icc a b) := hS.r_pos (u, v) (hp v hv) (hua.trans_le hv.1)
  have hl (v : ℝ) (hv : v ∈ Icc a b) := hS.lam_pos (u, v) (hp v hv)
  have cr := Calculus.continuousOn_out_section hS.cont_r hseg
  have cm := Calculus.continuousOn_out_section hS.cont_m hseg
  have cq := Calculus.continuousOn_out_section hS.cont_Q hseg
  have cl := Calculus.continuousOn_out_section hS.cont_lam hseg
  have cf := density_continuousOn cr cm cq cl hr (fun v hv => hS.one_sub_mu_pos _ (hp v hv))
  have ik := (cl.div (cr.pow 2) (fun v hv => pow_ne_zero 2 (hr v hv).ne')).intervalIntegrable_of_Icc
    (μ := volume) hab
  have hpoint (v : ℝ) (hv : v ∈ Icc a b) :
      0 ≤ S.lam u v * (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
        ((1 - S.mu u v) * S.r u v) ∧
      S.lam u v * (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
        ((1 - S.mu u v) * S.r u v) ≤ (4 * s / δ) * (S.lam u v / S.r u v ^ 2) := by
    have hd := Observation.optical_density_bounds_of_mass_bound
      (m := S.m u v) (q := S.Q u v) (r := S.r u v) (M := 2 * s)
      (hr v hv) hδ (by positivity) (hm v hv) (hgap v hv) (hcharge v hv)
    constructor
    · convert mul_nonneg (hl v hv).le hd.1 using 1
      dsimp [Fields.mu]
      ring
    · convert mul_le_mul_of_nonneg_left hd.2 (hl v hv).le using 1 <;> dsimp [Fields.mu] <;> ring
  have hi := intervalIntegral.integral_mono_on hab (cf.intervalIntegrable_of_Icc hab)
    (ik.const_mul (4 * s / δ)) (fun v hv => (hpoint v hv).2)
  have hsection := Local.IsSolution.out_section hS hua hab hseg
  have hk := Observation.integral_inverse_radius_of_ac hab hsection.1.1 cl hr hsection.1.2
  rw [intervalIntegral.integral_const_mul] at hi
  simp only [Pi.div_apply, Pi.pow_apply] at hi
  rw [hk] at hi
  refine ⟨intervalIntegral.integral_nonneg hab (fun v hv => (hpoint v hv).1), ?_⟩
  calc
    _ ≤ (4 * s / δ) * ((S.r u a)⁻¹ - (S.r u b)⁻¹) := hi
    _ ≤ (4 * s / δ) * (S.r u a)⁻¹ := mul_le_mul_of_nonneg_left
      (sub_le_self _ (inv_nonneg.mpr (hr b ⟨hab, le_rfl⟩).le)) (by positivity)
    _ = 4 * s / (δ * S.r u a) := by ring
    _ ≤ 4 * s / (δ * (s * ρ)) := div_le_div_of_nonneg_left (by positivity)
      (by positivity) (mul_le_mul_of_nonneg_left hcut hδ.le)
    _ = _ := by field_simp

/-- [internal]
The incoming optical integral has the same cutoff bound as the outgoing
one, with the exact original density `-ν`. The coefficient depends only
on the gap and normalized cutoff, not on original-coordinate expansions. -/
theorem Observation.incoming_truncated_optics_of_mass_charge_bounds
    {e δ ρ s : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hs : 0 < s)
    {a b v : ℝ} (hab : a ≤ b) (hbv : b < v) (hseg : inSeg a b v ⊆ D)
    (hcut : s * ρ ≤ S.r b v)
    (hm : ∀ u ∈ Icc a b, S.m u v ≤ 2 * s)
    (hgap : ∀ u ∈ Icc a b, δ ≤ 1 - S.mu u v)
    (hcharge : ∀ u ∈ Icc a b, S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v) :
    0 ≤ (∫ u in a..b, -S.nu u v * (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
      ((1 - S.mu u v) * S.r u v)) ∧
    (∫ u in a..b, -S.nu u v * (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
      ((1 - S.mu u v) * S.r u v)) ≤ 4 / (δ * ρ) := by
  have hp (u : ℝ) (hu : u ∈ Icc a b) :=
    hseg (show (u, v) ∈ inSeg a b v from ⟨hu.1, hu.2, rfl⟩)
  have hr (u : ℝ) (hu : u ∈ Icc a b) := hS.r_pos (u, v) (hp u hu) (hu.2.trans_lt hbv)
  have hn (u : ℝ) (hu : u ∈ Icc a b) := neg_pos.mpr (hS.nu_neg (u, v) (hp u hu))
  have cr := Calculus.continuousOn_in_section hS.cont_r hseg
  have cm := Calculus.continuousOn_in_section hS.cont_m hseg
  have cq := Calculus.continuousOn_in_section hS.cont_Q hseg
  have cn := Calculus.continuousOn_in_section hS.cont_nu hseg
  have cf := density_continuousOn cr cm cq cn.neg hr (fun u hu => hS.one_sub_mu_pos _ (hp u hu))
  have ik :=
    (cn.neg.div (cr.pow 2) (fun u hu => pow_ne_zero 2 (hr u hu).ne')).intervalIntegrable_of_Icc
    (μ := volume) hab
  have hpoint (u : ℝ) (hu : u ∈ Icc a b) :
      0 ≤ -S.nu u v * (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
        ((1 - S.mu u v) * S.r u v) ∧
      -S.nu u v * (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
        ((1 - S.mu u v) * S.r u v) ≤ (4 * s / δ) * (-S.nu u v / S.r u v ^ 2) := by
    have hd := Observation.optical_density_bounds_of_mass_bound
      (m := S.m u v) (q := S.Q u v) (r := S.r u v) (M := 2 * s)
      (hr u hu) hδ (by positivity) (hm u hu) (hgap u hu) (hcharge u hu)
    constructor
    · convert mul_nonneg (hn u hu).le hd.1 using 1
      dsimp [Fields.mu]
      ring
    · convert mul_le_mul_of_nonneg_left hd.2 (hn u hu).le using 1 <;> dsimp [Fields.mu] <;> ring
  have hi := intervalIntegral.integral_mono_on hab (cf.intervalIntegrable_of_Icc hab)
    (ik.const_mul (4 * s / δ)) (fun u hu => (hpoint u hu).2)
  have hsection := Local.IsSolution.in_section hS hab hbv hseg
  have hk := Observation.integral_inverse_radius_of_ac hab hsection.1.1 cn hr hsection.1.2
  have hk' : (∫ u in a..b, -S.nu u v / S.r u v ^ 2) = (S.r b v)⁻¹ - (S.r a v)⁻¹ := by
    rw [show (fun u => -S.nu u v / S.r u v ^ 2) =
      (fun u => -(S.nu u v / S.r u v ^ 2)) by funext u; ring,
      intervalIntegral.integral_neg, hk]
    ring
  rw [intervalIntegral.integral_const_mul] at hi
  simp only [Pi.div_apply, Pi.pow_apply, Pi.neg_apply] at hi
  rw [hk'] at hi
  refine ⟨intervalIntegral.integral_nonneg hab (fun u hu => (hpoint u hu).1), ?_⟩
  calc
    _ ≤ (4 * s / δ) * ((S.r b v)⁻¹ - (S.r a v)⁻¹) := hi
    _ ≤ (4 * s / δ) * (S.r b v)⁻¹ := mul_le_mul_of_nonneg_left
      (sub_le_self _ (inv_nonneg.mpr (hr a ⟨le_rfl, hab⟩).le)) (by positivity)
    _ = 4 * s / (δ * S.r b v) := by ring
    _ ≤ 4 * s / (δ * (s * ρ)) := div_le_div_of_nonneg_left (by positivity)
      (by positivity) (mul_le_mul_of_nonneg_left hcut hδ.le)
    _ = _ := by field_simp

/-- [internal]
The normalized incoming expansion on an original outgoing section lies
between `exp(-4/(δρ))/2` and `1/2`. The normalization multiplier is fixed
on that section and is constrained only at its outer-cylinder endpoint. -/
theorem Observation.outgoing_expansion_bounds_of_mass_charge_bounds
    {e δ ρ s c : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hs : 0 < s)
    {u a b : ℝ} (hua : u < a) (hab : a ≤ b) (hseg : outSeg u a b ⊆ D)
    (hcut : s * ρ ≤ S.r u a)
    (hm : ∀ v ∈ Icc a b, S.m u v ≤ 2 * s)
    (hgap : ∀ v ∈ Icc a b, δ ≤ 1 - S.mu u v)
    (hcharge : ∀ v ∈ Icc a b, S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v)
    (hnorm : c * (-S.nu u b) = 1 / 2) :
    (1 / 2 : ℝ) * Real.exp (-(4 / (δ * ρ))) ≤ c * (-S.nu u a) ∧
      c * (-S.nu u a) ≤ 1 / 2 := by
  have hi := Observation.outgoing_truncated_optics_of_mass_charge_bounds
    hS hδ hρ hs hua hab hseg hcut hm hgap hcharge
  have he := Observation.expansion_eq_of_log_increment
    (neg_pos.mpr (hS.nu_neg (u, a) (hseg ⟨rfl, le_rfl, hab⟩)))
    (neg_pos.mpr (hS.nu_neg (u, b) (hseg ⟨rfl, hab, le_rfl⟩)))
    (Observation.outgoing_log_neg_nu_integralForm hS hua hab hseg).2 hnorm
  exact co_expansions_of_log_integral hi.1 hi.2 he

/-- [internal]
The normalized outgoing expansion on an original incoming section has the
same cutoff bound. Its normalization multiplier is fixed along that
section; no lower bound on either original expansion is required. -/
theorem Observation.incoming_expansion_bounds_of_mass_charge_bounds
    {e δ ρ s c : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hs : 0 < s)
    {a b v : ℝ} (hab : a ≤ b) (hbv : b < v) (hseg : inSeg a b v ⊆ D)
    (hcut : s * ρ ≤ S.r b v)
    (hm : ∀ u ∈ Icc a b, S.m u v ≤ 2 * s)
    (hgap : ∀ u ∈ Icc a b, δ ≤ 1 - S.mu u v)
    (hcharge : ∀ u ∈ Icc a b, S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v)
    (hnorm : c * S.lam a v = 1 / 2) :
    (1 / 2 : ℝ) * Real.exp (-(4 / (δ * ρ))) ≤ c * S.lam b v ∧
      c * S.lam b v ≤ 1 / 2 := by
  have hi := Observation.incoming_truncated_optics_of_mass_charge_bounds
    hS hδ hρ hs hab hbv hseg hcut hm hgap hcharge
  have hl := (Terminal.incoming_log_lambda_integralForm hS hab hbv hseg).2
  rw [intervalIntegral.integral_neg] at hl
  dsimp [signedExpIntegrand] at hl
  have hlog : Real.log (S.lam a v) - Real.log (S.lam b v) =
      ∫ u in a..b, -S.nu u v * (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
        ((1 - S.mu u v) * S.r u v) := by linarith only [hl]
  have he := Observation.expansion_eq_of_log_increment
    (hS.lam_pos (b, v) (hseg ⟨hab, le_rfl, rfl⟩))
    (hS.lam_pos (a, v) (hseg ⟨le_rfl, hab, rfl⟩)) hlog hnorm
  exact co_expansions_of_log_integral hi.1 hi.2 he

/-- [internal]
Both normalized expansion bounds at a point follow from its two original
characteristic sections reaching the cylinder. The constant depends only
on `δ,ρ`, uniformly in the physical scale, original solution, coupling and
coordinate multipliers. The original solution and both sections are kept. -/
theorem co_expansions_of_original_segments
    {e δ ρ s cNu cLam : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (hδ : 0 < δ) (hρ : 0 < ρ) (hs : 0 < s)
    {a u v b : ℝ} (hau : a ≤ u) (huv : u < v) (hvb : v ≤ b)
    (hin : inSeg a u v ⊆ D) (hout : outSeg u v b ⊆ D) (hcut : s * ρ ≤ S.r u v)
    (hmi : ∀ x ∈ Icc a u, S.m x v ≤ 2 * s)
    (hmo : ∀ x ∈ Icc v b, S.m u x ≤ 2 * s)
    (hgi : ∀ x ∈ Icc a u, δ ≤ 1 - S.mu x v)
    (hgo : ∀ x ∈ Icc v b, δ ≤ 1 - S.mu u x)
    (hqi : ∀ x ∈ Icc a u, S.Q x v ^ 2 / S.r x v ^ 2 ≤ S.mu x v)
    (hqo : ∀ x ∈ Icc v b, S.Q u x ^ 2 / S.r u x ^ 2 ≤ S.mu u x)
    (hnormNu : cNu * (-S.nu u b) = 1 / 2) (hnormLam : cLam * S.lam a v = 1 / 2) :
    ((1 / 2 : ℝ) * Real.exp (-(4 / (δ * ρ))) ≤ cNu * (-S.nu u v) ∧
      cNu * (-S.nu u v) ≤ 1 / 2) ∧
    ((1 / 2 : ℝ) * Real.exp (-(4 / (δ * ρ))) ≤ cLam * S.lam u v ∧
      cLam * S.lam u v ≤ 1 / 2) :=
  ⟨Observation.outgoing_expansion_bounds_of_mass_charge_bounds
      hS hδ hρ hs huv hvb hout hcut hmo hgo hqo hnormNu,
    Observation.incoming_expansion_bounds_of_mass_charge_bounds
      hS hδ hρ hs hau huv hin hcut hmi hgi hqi hnormLam⟩

private theorem outgoing_radius_le {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u a b x : ℝ} (hua : u < a)
    (hseg : outSeg u a b ⊆ D) (hx : x ∈ Icc a b) : S.r u a ≤ S.r u x := by
  have hsub : outSeg u a x ⊆ D := fun p hp => hseg ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩
  have he := (hS.eq_out u a x hua hx.1 hsub).1
  have hi : 0 ≤ ∫ y in a..x, S.lam u y :=
    intervalIntegral.integral_nonneg hx.1 (fun y hy => (hS.lam_pos (u, y) (hsub ⟨rfl, hy⟩)).le)
  rw [← he.2] at hi
  exact sub_nonneg.mp hi

private theorem incoming_radius_le {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {a b v x : ℝ} (hbv : b < v)
    (hseg : inSeg a b v ⊆ D) (hx : x ∈ Icc a b) : S.r b v ≤ S.r x v := by
  have hsub : inSeg x b v ⊆ D := fun p hp => hseg ⟨hx.1.trans hp.1, hp.2.1, hp.2.2⟩
  have he := (hS.eq_in x b v hx.2 hbv hsub).1
  have hi : 0 ≤ ∫ y in x..b, -S.nu y v :=
    intervalIntegral.integral_nonneg hx.2 (fun y hy =>
      (neg_pos.mpr (hS.nu_neg (y, v) (hsub ⟨hy.1, hy.2, rfl⟩))).le)
  rw [intervalIntegral.integral_neg, ← he.2] at hi
  linarith only [hi]

private theorem gap_half_of_mass_radius {m r s L₀ : ℝ} (hs : 0 < s)
    (hL₀ : 8 ≤ L₀) (hm : m ≤ 2 * s) (hr : s * L₀ ≤ r) : 1 / 2 ≤ 1 - 2 * m / r := by
  have hLs : 0 < L₀ := (by norm_num : (0 : ℝ) < 8).trans_le hL₀
  have hr0 : 0 < r := (mul_pos hs hLs).trans_le hr
  have hr8 : 8 * s ≤ r := by
    simpa only [mul_comm] using (mul_le_mul_of_nonneg_left hL₀ hs.le).trans hr
  have hμ : 2 * m / r ≤ 1 / 2 := (div_le_iff₀ hr0).mpr (by nlinarith only [hm, hr8])
  linarith only [hμ]

/-- [internal]
On the fixed outer annulus `L₀ ≥ 8`, the original mass bound improves the
gap to `1/2` and gives the sharper exponent `8/L₀`. The bound is uniform
in the scale, solution, coupling and both coordinate normalizers. -/
theorem co_expansions_outer_of_original_segments
    {e L₀ s cNu cLam : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (hL₀ : 8 ≤ L₀) (hs : 0 < s)
    {a u v b : ℝ} (hau : a ≤ u) (huv : u < v) (hvb : v ≤ b)
    (hin : inSeg a u v ⊆ D) (hout : outSeg u v b ⊆ D) (hcut : s * L₀ ≤ S.r u v)
    (hmi : ∀ x ∈ Icc a u, S.m x v ≤ 2 * s)
    (hmo : ∀ x ∈ Icc v b, S.m u x ≤ 2 * s)
    (hqi : ∀ x ∈ Icc a u, S.Q x v ^ 2 / S.r x v ^ 2 ≤ S.mu x v)
    (hqo : ∀ x ∈ Icc v b, S.Q u x ^ 2 / S.r u x ^ 2 ≤ S.mu u x)
    (hnormNu : cNu * (-S.nu u b) = 1 / 2) (hnormLam : cLam * S.lam a v = 1 / 2) :
    ((1 / 2 : ℝ) * Real.exp (-(8 / L₀)) ≤ cNu * (-S.nu u v) ∧ cNu * (-S.nu u v) ≤ 1 / 2) ∧
    ((1 / 2 : ℝ) * Real.exp (-(8 / L₀)) ≤ cLam * S.lam u v ∧ cLam * S.lam u v ≤ 1 / 2) := by
  have hgi (x : ℝ) (hx : x ∈ Icc a u) : (1 / 2 : ℝ) ≤ 1 - S.mu x v :=
    gap_half_of_mass_radius hs hL₀ (hmi x hx) (hcut.trans (incoming_radius_le hS huv hin hx))
  have hgo (x : ℝ) (hx : x ∈ Icc v b) : (1 / 2 : ℝ) ≤ 1 - S.mu u x :=
    gap_half_of_mass_radius hs hL₀ (hmo x hx) (hcut.trans (outgoing_radius_le hS huv hout hx))
  have he := co_expansions_of_original_segments hS (show (0 : ℝ) < 1 / 2 by norm_num)
    ((by norm_num : (0 : ℝ) < 8).trans_le hL₀) hs hau huv hvb hin hout hcut
    hmi hmo hgi hgo hqi hqo hnormNu hnormLam
  have hf : (4 : ℝ) / ((1 / 2) * L₀) = 8 / L₀ := by ring
  simpa only [hf] using he

end EmcsfAcExtension.Global
