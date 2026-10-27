module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Terminal.Scalar
public import EmcsfAcExtension.Global.Terminal.OpticalUpper
import EmcsfAcExtension.Global.Terminal.Mass

/-! # Terminal Maxwell primitive and charge estimates

The literal incoming equations and finite scalar flux give absolute
integrability of the Maxwell source. Its finite charge limit vanishes by
the positive electric mass density. The tail primitive and weighted
Cauchy–Schwarz then prove the logarithmic charge estimate of
`charged_SF_new_version.tex:L991–1016`, following approved internal project record T4–T5.
-/

public section

open Complex Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Terminal

/-- [internal] The exact incoming Maxwell density divided by the radial
Jacobian. This is the algebra in charged_SF_new_version.tex:L992–995; a radial
coordinate theorem must separately justify differentiation in that coordinate. -/
theorem incoming_maxwell_radial_density {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.QU e u v / S.nu u v = e * S.r u v *
      (starRingEnd ℂ (S.phi u v) * (S.xi u v / (S.nu u v : ℂ))).im := by
  have hn := (hS.nu_neg (u, v) hp).ne
  rw [← mul_div_assoc, Complex.div_ofReal_im]
  dsimp [Fields.QU]
  field_simp [hn]

/-- [internal] The exact ordinary incoming mass density divided by the
radial Jacobian, charged_SF_new_version.tex:L1000–1004. No radial inverse is assumed. -/
theorem incoming_mass_radial_density {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (hp : (u, v) ∈ D) :
    2 * S.mU u v / S.nu u v =
      (1 - S.mu u v) * ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 +
        S.Q u v ^ 2 / S.r u v ^ 2 := by
  have hn := (hS.nu_neg (u, v) hp).ne
  simp only [Fields.mU, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  by_cases hr : S.r u v = 0
  · simp only [hr, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
      add_zero]
    field_simp [hn]
    simp
  · field_simp [hn, hr]

/-- [internal] The positive radial mass density controls its electric part,
with the exact universal coefficient `1/2`. -/
theorem incoming_mass_radial_electric_le {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.Q u v ^ 2 / S.r u v ^ 2 ≤ 2 * S.mU u v / S.nu u v := by
  rw [incoming_mass_radial_density hS hp]
  exact le_add_of_nonneg_left (mul_nonneg (hS.one_sub_mu_pos (u, v) hp).le (sq_nonneg _))

/-- [internal] The two terminal scalar-flux conventions agree exactly,
including the frozen totalization at zero radius. -/
theorem incoming_scalar_flux_eq {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (hp : (u, v) ∈ D) :
    ‖S.xi u v‖ ^ 2 / ((-S.nu u v) * S.r u v) =
      (-S.nu u v) * ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2 / S.r u v := by
  have hn := (hS.nu_neg (u, v) hp).ne
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  by_cases hr : S.r u v = 0
  · simp [hr]
  · field_simp [hn, hr]

/-- [internal] Absolute Maxwell current is bounded by the product of the
scalar modulus and its covariant incoming derivative. The coefficient is
exactly the absolute coupling, independent of the solution. -/
theorem incoming_maxwell_abs_le {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (hp : (u, v) ∈ D) (huv : u < v) :
    |S.QU e u v| ≤ |e| * S.r u v * ‖S.phi u v‖ * ‖S.xi u v‖ := by
  have hr := hS.r_pos (u, v) hp huv
  dsimp [Fields.QU]
  rw [abs_mul, abs_mul, abs_of_pos hr]
  calc
    _ ≤ |e| * S.r u v * ‖starRingEnd ℂ (S.phi u v) * S.xi u v‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (mul_nonneg (abs_nonneg _) hr.le)
    _ = _ := by rw [norm_mul, Complex.norm_conj]; ring

/-- [internal] Young's inequality bounds the current by the scalar flux
and its complementary radius moment, with the universal coefficient `1/2`.
This estimate is used only to establish absolute integrability. -/
theorem incoming_maxwell_young {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (hp : (u, v) ∈ D) (huv : u < v) :
    |S.QU e u v| ≤ |e| / 2 *
      (‖S.xi u v‖ ^ 2 / ((-S.nu u v) * S.r u v) +
        (-S.nu u v) * S.r u v ^ 3 * ‖S.phi u v‖ ^ 2) := by
  have hr := hS.r_pos (u, v) hp huv
  have hn := neg_pos.mpr (hS.nu_neg (u, v) hp)
  have hy : 2 * (S.r u v * ‖S.phi u v‖ * ‖S.xi u v‖) ≤
      ‖S.xi u v‖ ^ 2 / ((-S.nu u v) * S.r u v) +
        (-S.nu u v) * S.r u v ^ 3 * ‖S.phi u v‖ ^ 2 := by
    have hh := div_nonneg
      (sq_nonneg (‖S.xi u v‖ - (-S.nu u v) * S.r u v ^ 2 * ‖S.phi u v‖))
      (mul_pos hn hr).le
    have he : (‖S.xi u v‖ - (-S.nu u v) * S.r u v ^ 2 * ‖S.phi u v‖) ^ 2 /
        ((-S.nu u v) * S.r u v) =
        ‖S.xi u v‖ ^ 2 / ((-S.nu u v) * S.r u v) +
          (-S.nu u v) * S.r u v ^ 3 * ‖S.phi u v‖ ^ 2 -
            2 * (S.r u v * ‖S.phi u v‖ * ‖S.xi u v‖) := by
      field_simp [(hS.nu_neg (u, v) hp).ne, hr.ne']
      ring
    rw [he] at hh
    linarith only [hh]
  calc
    _ ≤ |e| * (S.r u v * ‖S.phi u v‖ * ‖S.xi u v‖) := by
      simpa only [mul_assoc] using incoming_maxwell_abs_le hS hp huv
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hy (abs_nonneg e)]

private theorem scalar_radius_sq_bound {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ Ico ui 0, S.r u 0 * ‖S.phi u 0‖ ^ 2 ≤ C := by
  obtain ⟨C, hC, hbound⟩ := scalar_log_bound ui e S h.ui_neg h.solution h.gauge
    h.mu h.radius h.datumAC hs
  have hRi := h.solution.r_pos (ui, 0) ⟨le_rfl, h.ui_neg, h.ui_neg.le, le_rfl⟩ h.ui_neg
  refine ⟨2 * C ^ 2 * S.r ui 0, by positivity, ?_⟩
  intro u hu
  have hp : (u, 0) ∈ origDomain ui := ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
  have hR := h.solution.r_pos (u, 0) hp hu.2
  have hle := (terminal_radius_strictAntiOn h.solution).antitoneOn
    ⟨le_rfl, h.ui_neg⟩ hu hu.1
  have hL : 0 ≤ Real.log (S.r ui 0 / S.r u 0) :=
    Real.log_nonneg ((one_le_div hR).2 hle)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hRi hR)
  have hsqrt := Real.sq_sqrt hL
  have hquad : (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))) ^ 2 ≤
      2 * (S.r ui 0 / S.r u 0) := by
    nlinarith only [hsqrt, hlog,
      sq_nonneg (Real.sqrt (Real.log (S.r ui 0 / S.r u 0)) - 1)]
  have hsq := sq_le_sq₀ (norm_nonneg (S.phi u 0))
    (mul_nonneg hC.le (by positivity)) |>.2 (hbound u hu)
  have hmul := mul_le_mul_of_nonneg_left hquad (sq_nonneg C)
  rw [mul_pow] at hsq
  have hh : ‖S.phi u 0‖ ^ 2 ≤ 2 * C ^ 2 * S.r ui 0 / S.r u 0 := by
    calc
      _ ≤ C ^ 2 * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))) ^ 2 := hsq
      _ ≤ C ^ 2 * (2 * (S.r ui 0 / S.r u 0)) := hmul
      _ = _ := by ring
  have hh' := (le_div_iff₀ hR).1 hh
  simpa only [mul_comm (S.r u 0)] using hh'

/-- [internal] The complementary scalar radius moment is absolutely integrable.
Its majorant depends on the fixed development and signed terminal bound;
the asserted integrability includes the entire missing-endpoint tail. -/
theorem terminal_scalar_moment_integrable {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    IntegrableOn (fun u => (-S.nu u 0) * S.r u 0 ^ 3 * ‖S.phi u 0‖ ^ 2)
      (Ico ui 0) := by
  obtain ⟨C, hC, hb⟩ := scalar_radius_sq_bound h hs
  have hp (u : ℝ) (hu : u ∈ Ico ui 0) : (u, 0) ∈ origDomain ui :=
    ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
  have cr : ContinuousOn (fun u => S.r u 0) (Ico ui 0) :=
    h.solution.cont_r.comp (continuous_id.prodMk continuous_const).continuousOn hp
  have cn : ContinuousOn (fun u => S.nu u 0) (Ico ui 0) :=
    h.solution.cont_nu.comp (continuous_id.prodMk continuous_const).continuousOn hp
  have cp : ContinuousOn (fun u => S.phi u 0) (Ico ui 0) :=
    h.solution.cont_phi.comp (continuous_id.prodMk continuous_const).continuousOn hp
  apply Integrable.mono' ((terminal_radius_power_integrable h.ui_neg h.solution h.mu 2).const_mul C)
    ((((cn.neg.mul (cr.pow 3)).mul (cp.norm.pow 2)).aestronglyMeasurable measurableSet_Ico))
  filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
  have hn := neg_pos.mpr (h.solution.nu_neg _ (hp u hu))
  have hR := h.solution.r_pos _ (hp u hu) hu.2
  change ‖(-S.nu u 0) * S.r u 0 ^ 3 * ‖S.phi u 0‖ ^ 2‖ ≤ C * ((-S.nu u 0) * S.r u 0 ^ 2)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ = ((-S.nu u 0) * S.r u 0 ^ 2) * (S.r u 0 * ‖S.phi u 0‖ ^ 2) := by ring
    _ ≤ ((-S.nu u 0) * S.r u 0 ^ 2) * C :=
      mul_le_mul_of_nonneg_left (hb u hu) (by positivity)
    _ = _ := by ring

/-- [internal] The nonnegative terminal scalar flux has an ordinary integral
after its extended integral has been proved finite. -/
theorem terminal_flux_integrable {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    IntegrableOn (fun u => ‖S.xi u 0‖ ^ 2 / ((-S.nu u 0) * S.r u 0)) (Ico ui 0) := by
  have hp (u : ℝ) (hu : u ∈ Ico ui 0) : (u, 0) ∈ origDomain ui :=
    ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
  have cr := h.solution.cont_r.comp (continuous_id.prodMk continuous_const).continuousOn hp
  have cn := h.solution.cont_nu.comp (continuous_id.prodMk continuous_const).continuousOn hp
  have cx := h.solution.cont_xi.comp (continuous_id.prodMk continuous_const).continuousOn hp
  have cT : ContinuousOn (fun u => ‖S.xi u 0‖ ^ 2 / ((-S.nu u 0) * S.r u 0))
      (Ico ui 0) := (cx.norm.pow 2).div (cn.neg.mul cr) (fun u hu =>
        mul_ne_zero (neg_pos.mpr (h.solution.nu_neg _ (hp u hu))).ne'
          (h.solution.r_pos _ (hp u hu) hu.2).ne')
  have hT := integrableOn_of_lintegral_ofReal_ne_top
    (cT.aestronglyMeasurable measurableSet_Ico)
    ((ae_restrict_iff' measurableSet_Ico).2 (Eventually.of_forall fun u hu =>
      div_nonneg (sq_nonneg _) (mul_nonneg
        (neg_pos.mpr (h.solution.nu_neg _ (hp u hu))).le
        (h.solution.r_pos _ (hp u hu) hu.2).le)))
    (terminal_gap_and_flux ui e S h.ui_neg h.solution h.gauge h.mu h.radius h.datumAC hs).2.ne
  exact hT

/-- [internal] The terminal Maxwell source is absolutely integrable under
the signed terminal bound (charged_SF_new_version.tex:L991–998, internal project record T4).
This is proved before asserting any terminal charge value. -/
theorem terminal_maxwell_integrable {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    IntegrableOn (fun u => S.QU e u 0) (Ico ui 0) := by
  have hp (u : ℝ) (hu : u ∈ Ico ui 0) : (u, 0) ∈ origDomain ui :=
    ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
  have cr := h.solution.cont_r.comp (continuous_id.prodMk continuous_const).continuousOn hp
  have cn := h.solution.cont_nu.comp (continuous_id.prodMk continuous_const).continuousOn hp
  have cx := h.solution.cont_xi.comp (continuous_id.prodMk continuous_const).continuousOn hp
  have cp := h.solution.cont_phi.comp (continuous_id.prodMk continuous_const).continuousOn hp
  have hT := terminal_flux_integrable h hs
  have cQ : ContinuousOn (fun u => S.QU e u 0) (Ico ui 0) := by
    exact continuousOn_const.mul cr |>.mul
      (Complex.continuous_im.comp_continuousOn (cp.star.mul cx))
  apply Integrable.mono' ((hT.add (terminal_scalar_moment_integrable h hs)).const_mul (|e| / 2))
    (cQ.aestronglyMeasurable measurableSet_Ico)
  filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
  exact incoming_maxwell_young h.solution (hp u hu) hu.2

/-- [node prop:charged-terminal-equivalence#terminal-charge-finite-limit]
The terminal Maxwell density is absolutely integrable and the charge has a
finite limit at the missing vertex (charged_SF_new_version.tex:L996–998). -/
theorem terminal_charge_finite_limit {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    IntegrableOn (fun u => S.QU e u 0) (Ico ui 0) ∧
      ∃ q : ℝ, Tendsto (fun u => S.Q u 0) (𝓝[<] 0) (𝓝 q) := by
  have hi := terminal_maxwell_integrable h hs
  have hi' : IntegrableOn (fun u => S.QU e u 0) (uIcc ui 0) := by
    simpa only [uIcc_of_le h.ui_neg.le, IntegrableOn, restrict_Ico_eq_restrict_Icc] using hi
  let q := S.Q ui 0 + ∫ s in ui..0, S.QU e s 0
  refine ⟨hi, q, ?_⟩
  have ht : Tendsto (fun u => S.Q ui 0 + ∫ s in ui..u, S.QU e s 0)
      (𝓝[Icc ui 0] 0) (𝓝 q) := by
    apply ContinuousWithinAt.add continuousWithinAt_const
    simpa only [uIcc_of_le h.ui_neg.le] using
      intervalIntegral.continuousOn_primitive_interval hi' 0
        (by simp [h.ui_neg.le])
  have hin : Tendsto (id : ℝ → ℝ) (𝓝[<] 0) (𝓝[Icc ui 0] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    exact ⟨hu.1.le, hu.2.le⟩
  apply (ht.comp hin).congr'
  filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
  have he := (h.solution.eq_in ui u 0 hu.1.le hu.2
    ((inSeg_subset_origDomain_iff hu.1.le).2 ⟨le_rfl, hu.2, hu.2.le, le_rfl⟩)).2.2.2.1.2
  dsimp only [Function.comp_apply, id_eq]
  linarith only [he]

/-- [internal] The reciprocal-radius primitive on a proper terminal segment.
The coefficient is exactly one, with no endpoint or expansion bound. -/
theorem incoming_radius_inv {ui e a b : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (ha : ui ≤ a) (hab : a ≤ b) (hb : b < 0) :
    (∫ u in a..b, (-S.nu u 0) / S.r u 0 ^ 2) = (S.r b 0)⁻¹ - (S.r a 0)⁻¹ := by
  have hseg : inSeg a b 0 ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff hab).2 ⟨ha, hb, hb.le, le_rfl⟩
  have cr := Calculus.continuousOn_in_section hS.cont_r hseg
  have cn := Calculus.continuousOn_in_section hS.cont_nu hseg
  have hr (u : ℝ) (hu : u ∈ Icc a b) : S.r u 0 ≠ 0 :=
    (hS.r_pos (u, 0) (hseg ⟨hu.1, hu.2, rfl⟩) (hu.2.trans_lt hb)).ne'
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (cr.inv₀ hr) ?_
    ((cn.neg.div (cr.pow 2) (fun u hu => pow_ne_zero _ (hr u hu))).intervalIntegrable_of_Icc hab)
  intro u hu
  exact (terminal_radius_hasDerivAt hS ⟨ha.trans_lt hu.1, hu.2.trans hb⟩).inv
    (hr u ⟨hu.1.le, hu.2.le⟩)

private theorem electric_lower_bound {ui e a b c : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (ha : ui ≤ a) (hab : a ≤ b) (hb : b < 0)
    (hc : ∀ u ∈ Icc a b, c ^ 2 ≤ S.Q u 0 ^ 2) :
    c ^ 2 * ((S.r b 0)⁻¹ - (S.r a 0)⁻¹) ≤ 2 * (S.m a 0 - S.m b 0) := by
  have hseg : inSeg a b 0 ⊆ origDomain ui :=
    (inSeg_subset_origDomain_iff hab).2 ⟨ha, hb, hb.le, le_rfl⟩
  have cr := Calculus.continuousOn_in_section hS.cont_r hseg
  have cn := Calculus.continuousOn_in_section hS.cont_nu hseg
  have hme := (hS.eq_in a b 0 hab hb hseg).2.2.1
  have hr (u : ℝ) (hu : u ∈ Icc a b) : 0 < S.r u 0 :=
    hS.r_pos (u, 0) (hseg ⟨hu.1, hu.2, rfl⟩) (hu.2.trans_lt hb)
  have hni : IntervalIntegrable (fun u => (-S.nu u 0) / S.r u 0 ^ 2) volume a b :=
    (cn.neg.div (cr.pow 2) (fun u hu => pow_ne_zero _ (hr u hu).ne')).intervalIntegrable_of_Icc hab
  have hi := intervalIntegral.integral_mono_on hab (hni.const_mul (c ^ 2))
    (hme.1.const_mul (-2)) (fun u hu => ?_)
  · rw [intervalIntegral.integral_const_mul, incoming_radius_inv hS ha hab hb,
      intervalIntegral.integral_const_mul, ← hme.2] at hi
    linarith only [hi]
  have hp := hseg (show (u, 0) ∈ inSeg a b 0 from ⟨hu.1, hu.2, rfl⟩)
  have hn := neg_pos.mpr (hS.nu_neg _ hp)
  have hl := mul_le_mul_of_nonneg_left (incoming_mass_radial_electric_le hS hp) hn.le
  have he : (-S.nu u 0) * (2 * S.mU u 0 / S.nu u 0) = -2 * S.mU u 0 := by
    field_simp [(hS.nu_neg _ hp).ne]
  rw [he] at hl
  calc
    c ^ 2 * ((-S.nu u 0) / S.r u 0 ^ 2) ≤
        (-S.nu u 0) * (S.Q u 0 ^ 2 / S.r u 0 ^ 2) := by
      have hh := mul_le_mul_of_nonneg_left (hc u hu)
        (div_nonneg hn.le (sq_nonneg (S.r u 0)))
      convert hh using 1 <;> ring
    _ ≤ _ := hl

/-- [node prop:charged-terminal-equivalence#terminal-charge-zero-limit]
The finite terminal charge limit vanishes. The electric part of the mass
equation and nonnegative mass exclude any nonzero limit; no regular-axis
trace is assigned to the missing vertex (charged_SF_new_version.tex:L998–1006). -/
theorem terminal_charge_zero_limit {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    Tendsto (fun u => S.Q u 0) (𝓝[<] 0) (𝓝 0) := by
  obtain ⟨q, hq⟩ := (terminal_charge_finite_limit h hs).2
  suffices q = 0 by simpa only [this] using hq
  by_contra hq0
  have hc : 0 < |q| / 2 := by positivity
  have hev : ∀ᶠ u in 𝓝[<] (0 : ℝ), (|q| / 2) ^ 2 ≤ S.Q u 0 ^ 2 := by
    have he := hq.abs.eventually (Ioi_mem_nhds (show |q| / 2 < |q| by
      linarith only [abs_pos.mpr hq0]))
    filter_upwards [he] with u hu
    simpa only [sq_abs] using pow_le_pow_left₀ hc.le hu.le 2
  obtain ⟨d, hd, hsmall⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset h.ui_neg).mp hev
  obtain ⟨a, ha⟩ := exists_between hd.2
  have haui : ui < a := hd.1.trans_lt ha.1
  have hcharge (u : ℝ) (hu : u ∈ Ico a 0) : (|q| / 2) ^ 2 ≤ S.Q u 0 ^ 2 := by
    exact hsmall ⟨ha.1.trans_le hu.1, hu.2⟩
  have hR := h.solution.r_pos (a, 0) ⟨haui.le, ha.2, ha.2.le, le_rfl⟩ ha.2
  have hbound : ∀ᶠ b : ℝ in 𝓝[<] 0,
      (|q| / 2) ^ 2 ≤ (2 * S.m a 0 + (|q| / 2) ^ 2 / S.r a 0) * S.r b 0 := by
    filter_upwards [Ioo_mem_nhdsLT ha.2] with b hb
    have hh := electric_lower_bound h.solution haui.le hb.1.le hb.2
      (fun u hu => hcharge u ⟨hu.1, hu.2.trans_lt hb.2⟩)
    have hm := (mass_monotonicity h.solution (b, 0)
      ⟨haui.le.trans hb.1.le, hb.2, hb.2.le, le_rfl⟩).1
    have hRb := h.solution.r_pos (b, 0)
      ⟨haui.le.trans hb.1.le, hb.2, hb.2.le, le_rfl⟩ hb.2
    have hh' : (|q| / 2) ^ 2 / S.r b 0 ≤ 2 * S.m a 0 + (|q| / 2) ^ 2 / S.r a 0 := by
      simp only [div_eq_mul_inv] at *
      linarith only [hh, hm]
    exact (div_le_iff₀ hRb).1 hh'
  have hlim : Tendsto (fun b => (2 * S.m a 0 + (|q| / 2) ^ 2 / S.r a 0) * S.r b 0)
      (𝓝[<] 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (terminal_radius_collapse h.ui_neg h.solution h.mu)
  have hz := ge_of_tendsto hlim hbound
  exact (sq_pos_of_pos hc).not_ge hz

/-- [internal] The terminal charge is the tail Maxwell primitive with zero
integration constant, proved after absolute integrability and the zero limit. -/
theorem terminal_charge_primitive {ui e a : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (ha : a ∈ Ico ui 0) :
    S.Q a 0 = -(∫ u in a..0, S.QU e u 0) := by
  have hi : IntervalIntegrable (fun u => S.QU e u 0) volume ui 0 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le h.ui_neg.le,
      IntegrableOn, ← restrict_Ico_eq_restrict_Icc]
    exact terminal_maxwell_integrable h hs
  have hc := intervalIntegral.continuousOn_primitive_interval' (a := a) hi
    (show a ∈ uIcc ui 0 by simpa only [uIcc_of_le h.ui_neg.le] using ⟨ha.1, ha.2.le⟩)
  have ht : Tendsto (fun b => ∫ u in a..b, S.QU e u 0) (𝓝[<] 0)
      (𝓝 (∫ u in a..0, S.QU e u 0)) := by
    apply (show Tendsto (fun b => ∫ u in a..b, S.QU e u 0)
      (𝓝[uIcc ui 0] 0) (𝓝 (∫ u in a..0, S.QU e u 0)) from hc 0 right_mem_uIcc).comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT h.ui_neg] with u hu
    simpa only [uIcc_of_le h.ui_neg.le] using ⟨hu.1.le, hu.2.le⟩
  have hq := (terminal_charge_zero_limit h hs).sub (tendsto_const_nhds (x := S.Q a 0))
  have he : (fun b => S.Q b 0 - S.Q a 0) =ᶠ[𝓝[<] 0]
      (fun b => ∫ u in a..b, S.QU e u 0) := by
    filter_upwards [Ioo_mem_nhdsLT ha.2] with b hb
    exact (h.solution.eq_in a b 0 hb.1.le hb.2
      ((inSeg_subset_origDomain_iff hb.1.le).2 ⟨ha.1, hb.2, hb.2.le, le_rfl⟩)).2.2.2.1.2
  have hh := tendsto_nhds_unique (hq.congr' he) ht
  linarith only [hh]

/-- [internal] Weighted Maxwell Cauchy–Schwarz on a complete terminal tail.
The coefficient is exactly `e²`; both real tail integrals have already
been proved absolutely integrable before this estimate is applied. -/
theorem terminal_charge_cauchy_schwarz {ui e a : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (ha : a ∈ Ico ui 0) :
    S.Q a 0 ^ 2 ≤ e ^ 2 *
      (∫ u in a..0, ‖S.xi u 0‖ ^ 2 / ((-S.nu u 0) * S.r u 0)) *
      (∫ u in a..0, (-S.nu u 0) * S.r u 0 ^ 3 * ‖S.phi u 0‖ ^ 2) := by
  let T := fun u => ‖S.xi u 0‖ ^ 2 / ((-S.nu u 0) * S.r u 0)
  let W := fun u => (-S.nu u 0) * S.r u 0 ^ 3 * ‖S.phi u 0‖ ^ 2
  have hsub : Ico a 0 ⊆ Ico ui 0 := Ico_subset_Ico_left ha.1
  have hTi : IntegrableOn T (Ico a 0) := (terminal_flux_integrable h hs).mono_set hsub
  have hWi : IntegrableOn W (Ico a 0) := (terminal_scalar_moment_integrable h hs).mono_set hsub
  have hQi := (terminal_maxwell_integrable h hs).mono_set hsub
  have hp (u : ℝ) (hu : u ∈ Ico a 0) : (u, 0) ∈ origDomain ui :=
    ⟨ha.1.trans hu.1, hu.2, hu.2.le, le_rfl⟩
  have hTn (u : ℝ) (hu : u ∈ Ico a 0) : 0 ≤ T u :=
    div_nonneg (sq_nonneg _) (mul_nonneg
      (neg_pos.mpr (h.solution.nu_neg _ (hp u hu))).le
      (h.solution.r_pos _ (hp u hu) hu.2).le)
  have hWn (u : ℝ) (hu : u ∈ Ico a 0) : 0 ≤ W u := by
    dsimp [W]
    exact mul_nonneg (mul_nonneg (neg_pos.mpr (h.solution.nu_neg _ (hp u hu))).le
      (pow_nonneg (h.solution.r_pos _ (hp u hu) hu.2).le 3)) (sq_nonneg _)
  have hcs := sqrt_cauchy_schwarz hTi hWi
    ((ae_restrict_iff' measurableSet_Ico).2 (Eventually.of_forall hTn))
    ((ae_restrict_iff' measurableSet_Ico).2 (Eventually.of_forall hWn))
  have hb : ∀ᵐ u ∂volume.restrict (Ico a 0), |S.QU e u 0| ≤
      |e| * (Real.sqrt (T u) * Real.sqrt (W u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
    have hn := (h.solution.nu_neg _ (hp u hu)).ne
    have hr := h.solution.r_pos _ (hp u hu) hu.2
    have he : (S.r u 0 * ‖S.phi u 0‖ * ‖S.xi u 0‖) ^ 2 = T u * W u := by
      dsimp [T, W]
      field_simp [hn, hr.ne']
    have he' : (Real.sqrt (T u) * Real.sqrt (W u)) ^ 2 = T u * W u := by
      rw [mul_pow, Real.sq_sqrt (hTn u hu), Real.sq_sqrt (hWn u hu)]
    have hh : S.r u 0 * ‖S.phi u 0‖ * ‖S.xi u 0‖ ≤ Real.sqrt (T u) * Real.sqrt (W u) :=
      (sq_le_sq₀ (by positivity) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).1
        (he.trans he'.symm).le
    exact (incoming_maxwell_abs_le h.solution (hp u hu) hu.2).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (abs_nonneg e))
  have hI : |S.Q a 0| ≤ |e| * ∫ u in Ico a 0, Real.sqrt (T u) * Real.sqrt (W u) := by
    rw [terminal_charge_primitive h hs ha, abs_neg, intervalIntegral.integral_of_le ha.2.le,
      restrict_Ioc_eq_restrict_Icc, ← restrict_Ico_eq_restrict_Icc]
    calc
      _ ≤ ∫ u in Ico a 0, |S.QU e u 0| := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (f := fun u => S.QU e u 0)
            (μ := volume.restrict (Ico a 0)))
      _ ≤ ∫ u in Ico a 0, |e| * (Real.sqrt (T u) * Real.sqrt (W u)) :=
        integral_mono_ae hQi.norm (hcs.1.const_mul |e|) hb
      _ = _ := integral_const_mul _ _
  have hIn : 0 ≤ ∫ u in Ico a 0, Real.sqrt (T u) * Real.sqrt (W u) :=
    integral_nonneg (fun _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  simp only [intervalIntegral.integral_of_le ha.2.le,
    restrict_Ioc_eq_restrict_Icc, ← restrict_Ico_eq_restrict_Icc]
  calc
    _ = |S.Q a 0| ^ 2 := (sq_abs _).symm
    _ ≤ (|e| * ∫ u in Ico a 0, Real.sqrt (T u) * Real.sqrt (W u)) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (abs_nonneg _) hIn)).2 hI
    _ = e ^ 2 * (∫ u in Ico a 0, Real.sqrt (T u) * Real.sqrt (W u)) ^ 2 := by
      rw [mul_pow, sq_abs]
    _ ≤ e ^ 2 * ((∫ u in Ico a 0, T u) * ∫ u in Ico a 0, W u) :=
      mul_le_mul_of_nonneg_left hcs.2 (sq_nonneg e)
    _ = _ := by dsimp [T, W]; ring

private theorem scalar_moment_bound_of_log_bound {ui e a C : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) (ha : a ∈ Ico ui 0)
    (hC : 0 < C) (hbound : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    (∫ u in a..0, (-S.nu u 0) * S.r u 0 ^ 3 * ‖S.phi u 0‖ ^ 2) ≤
      2 * C ^ 2 * S.r a 0 ^ 4 * (1 + Real.log (S.r ui 0 / S.r a 0)) := by
  have hp (u : ℝ) (hu : u ∈ Ico a 0) : (u, 0) ∈ origDomain ui :=
    ⟨ha.1.trans hu.1, hu.2, hu.2.le, le_rfl⟩
  have hRa := h.solution.r_pos (a, 0) (hp a ⟨le_rfl, ha.2⟩) ha.2
  have hRi := h.solution.r_pos (ui, 0) ⟨le_rfl, h.ui_neg, h.ui_neg.le, le_rfl⟩ h.ui_neg
  have hLa : 0 ≤ Real.log (S.r ui 0 / S.r a 0) := Real.log_nonneg
    ((one_le_div hRa).2 ((terminal_radius_strictAntiOn h.solution).antitoneOn
      ⟨le_rfl, h.ui_neg⟩ ha ha.1))
  have hsub : Ico a 0 ⊆ Ico ui 0 := Ico_subset_Ico_left ha.1
  have hW := (terminal_scalar_moment_integrable h hs).mono_set hsub
  have hP₂ := (terminal_radius_power_integrable h.ui_neg h.solution h.mu 2).mono_set hsub
  have hP₃ := (terminal_radius_power_integrable h.ui_neg h.solution h.mu 3).mono_set hsub
  have hm := integral_mono_ae hW
    (((hP₃.const_mul (1 + Real.log (S.r ui 0 / S.r a 0))).add
      (hP₂.const_mul (S.r a 0))).const_mul (2 * C ^ 2)) ?_
  · rw [integral_const_mul] at hm
    simp only [Pi.add_apply] at hm
    rw [integral_add
      (f := fun u => (1 + Real.log (S.r ui 0 / S.r a 0)) * ((-S.nu u 0) * S.r u 0 ^ 3))
      (g := fun u => S.r a 0 * ((-S.nu u 0) * S.r u 0 ^ 2))
      (hP₃.const_mul _) (hP₂.const_mul _), integral_const_mul, integral_const_mul] at hm
    have he₂ := terminal_radius_power_integral h.ui_neg h.solution h.mu ha 2
    have he₃ := terminal_radius_power_integral h.ui_neg h.solution h.mu ha 3
    rw [intervalIntegral.integral_of_le ha.2.le, restrict_Ioc_eq_restrict_Icc,
      ← restrict_Ico_eq_restrict_Icc] at he₂ he₃ ⊢
    rw [he₂, he₃] at hm
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hm
    calc
      _ ≤ 2 * C ^ 2 * ((1 + Real.log (S.r ui 0 / S.r a 0)) * (S.r a 0 ^ 4 / 4) +
          S.r a 0 * (S.r a 0 ^ 3 / 3)) := hm
      _ = 2 * C ^ 2 * S.r a 0 ^ 4 *
          ((1 + Real.log (S.r ui 0 / S.r a 0)) / 4 + 1 / 3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hLa]) (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
  have hR := h.solution.r_pos _ (hp u hu) hu.2
  have hn := neg_pos.mpr (h.solution.nu_neg _ (hp u hu))
  have hL : 0 ≤ Real.log (S.r ui 0 / S.r u 0) := Real.log_nonneg
    ((one_le_div hR).2 ((terminal_radius_strictAntiOn h.solution).antitoneOn
      ⟨le_rfl, h.ui_neg⟩ (hsub hu) (hsub hu).1))
  have hlog : Real.log (S.r ui 0 / S.r u 0) = Real.log (S.r ui 0 / S.r a 0) +
      Real.log (S.r a 0 / S.r u 0) := by
    rw [Real.log_div hRi.ne' hR.ne', Real.log_div hRi.ne' hRa.ne', Real.log_div hRa.ne' hR.ne']
    ring
  have hlog' := Real.log_le_sub_one_of_pos (div_pos hRa hR)
  have hquad : (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0))) ^ 2 ≤
      2 * ((1 + Real.log (S.r ui 0 / S.r a 0)) + S.r a 0 / S.r u 0) := by
    nlinarith only [Real.sq_sqrt hL,
      sq_nonneg (Real.sqrt (Real.log (S.r ui 0 / S.r u 0)) - 1), hlog, hlog']
  have hsq := (sq_le_sq₀ (norm_nonneg (S.phi u 0))
    (mul_nonneg hC.le (by positivity))).2 (hbound u (hsub hu))
  rw [mul_pow] at hsq
  have hphi := hsq.trans (mul_le_mul_of_nonneg_left hquad (sq_nonneg C))
  have hh := mul_le_mul_of_nonneg_left hphi
    (show 0 ≤ (-S.nu u 0) * S.r u 0 ^ 3 by positivity)
  convert hh using 1
  dsimp only [Pi.add_apply, Pi.mul_apply]
  field_simp [hR.ne']
  ring

/-- [internal]
The sharp charge estimate of charged_SF_new_version.tex:L1006–1016, in original labels.
The positive constant depends only on the fixed development and its signed
bound and is uniform in the entire terminal tail, including its starting label. -/
theorem terminal_charge_bound {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Ico ui 0, S.Q a 0 ^ 2 ≤
      C * e ^ 2 * S.r a 0 ^ 4 * (1 + Real.log (S.r ui 0 / S.r a 0)) *
        (∫ u in a..0, ‖S.xi u 0‖ ^ 2 / ((-S.nu u 0) * S.r u 0)) := by
  obtain ⟨C, hC, hbound⟩ := scalar_log_bound ui e S h.ui_neg h.solution h.gauge
    h.mu h.radius h.datumAC hs
  refine ⟨2 * C ^ 2, by positivity, ?_⟩
  intro a ha
  have hf : 0 ≤ ∫ u in a..0, ‖S.xi u 0‖ ^ 2 / ((-S.nu u 0) * S.r u 0) := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict ha.2.le
    rw [← restrict_Ico_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
    have hp : (u, 0) ∈ origDomain ui := ⟨ha.1.trans hu.1, hu.2, hu.2.le, le_rfl⟩
    exact div_nonneg (sq_nonneg _) (mul_nonneg (neg_pos.mpr (h.solution.nu_neg _ hp)).le
      (h.solution.r_pos _ hp hu.2).le)
  calc
    _ ≤ e ^ 2 * (∫ u in a..0, ‖S.xi u 0‖ ^ 2 / ((-S.nu u 0) * S.r u 0)) *
        (∫ u in a..0, (-S.nu u 0) * S.r u 0 ^ 3 * ‖S.phi u 0‖ ^ 2) :=
      terminal_charge_cauchy_schwarz h hs ha
    _ ≤ e ^ 2 * (∫ u in a..0, ‖S.xi u 0‖ ^ 2 / ((-S.nu u 0) * S.r u 0)) *
        (2 * C ^ 2 * S.r a 0 ^ 4 * (1 + Real.log (S.r ui 0 / S.r a 0))) :=
      mul_le_mul_of_nonneg_left (scalar_moment_bound_of_log_bound h hs ha hC hbound)
        (mul_nonneg (sq_nonneg _) hf)
    _ = _ := by ring

end EmcsfAcExtension.Global.Terminal

namespace EmcsfAcExtension.Global

/-- [node eq:charged-terminal-charge]
Canonical sharp charge estimate, charged_SF_new_version.tex:L1006–1016. Its positive
constant depends on the fixed development and signed bound, uniformly in the label. -/
theorem charged_terminal_charge {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S) :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Ico ui 0, S.Q a 0 ^ 2 ≤
      C * e ^ 2 * S.r a 0 ^ 4 * (1 + Real.log (S.r ui 0 / S.r a 0)) *
        (∫ u in a..0, ‖S.xi u 0‖ ^ 2 / ((-S.nu u 0) * S.r u 0)) := by
  exact Terminal.terminal_charge_bound h hs

end EmcsfAcExtension.Global
