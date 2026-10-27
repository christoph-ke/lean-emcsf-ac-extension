module

public import EmcsfAcExtension.Global.Observation.WaveDifference
public import EmcsfAcExtension.Global.Observation.Domains
public import EmcsfAcExtension.Frozen.Fields.NormalizedOut
import EmcsfAcExtension.Infra.LinearTransport

/-! # Scalar comparison on the outer sideways triangles

The comparison derivative, boundary data and electric kernels retain the
moving outer endpoint. In particular a single incoming integration retains
its logarithm. Source: `charged_SF_new_version.tex:L2463–L2495`, approved internal project record
(V1)–(Y).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

/-- [internal]
Outgoing differentiation of the literal comparison scalar. The radial
static input is the derivative of `r*phiStar`, not a scalar shift symmetry. -/
theorem scalar_comparison_out_deriv_of_normalization
    {S : Fields} {H : ℂ} {u v : ℝ} (phiStar yStar : ℝ → ℂ)
    (hr : S.r u v ≠ 0)
    (hR : HasDerivAt (S.r u) (S.lam u v) v)
    (hphi : HasDerivAt (S.phi u) (S.theta u v / (S.r u v : ℂ)) v)
    (hstatic : HasDerivAt (fun r : ℝ => (r : ℂ) * phiStar r)
      (phiStar (S.r u v) + yStar (S.r u v)) (S.r u v)) :
    HasDerivAt (scalarComparison S H phiStar u)
      ((S.lam u v : ℂ) *
        (S.phi u v - H - (phiStar (S.r u v) + yStar (S.r u v))) + S.theta u v) v := by
  convert (shifted_rphi_out_deriv_of_normalization hr hR hphi).sub
    (hstatic.scomp v hR) using 1
  · rfl
  · simp only [Complex.real_smul]
    ring

/-- [internal]
The exact reconstruction in (Y), with the sharper mass power available
for the subsequent estimate. The two nonzero denominators are the
positive-radius and outgoing optical conditions supplied by normalization. -/
theorem outer_y_reconstruction (S : Fields) (H : ℂ) (phiStar yStar : ℝ → ℂ)
    {u v : ℝ} (hr : S.r u v ≠ 0) (hlam : S.lam u v ≠ 0) :
    S.theta u v / (S.lam u v : ℂ) - yStar (S.r u v) =
      ((S.lam u v : ℂ) *
          (S.phi u v - H - (phiStar (S.r u v) + yStar (S.r u v))) + S.theta u v) /
        (S.lam u v : ℂ) - scalarComparison S H phiStar u v / (S.r u v : ℂ) := by
  dsimp only [scalarComparison, shiftedRphi]
  field_simp [Complex.ofReal_ne_zero.mpr hr, Complex.ofReal_ne_zero.mpr hlam]
  ring

/-- [internal]
The actual normalized diagonal boundary supplies both difference data.
The value coefficient `B` is the fixed boundary closeness coefficient,
chosen upstream before the solution data. The derivative has exact
coefficient `1/2`; no constants depend on the outer radius or background.
The static inputs are its two matching boundary conditions. -/
theorem Observation.outer_boundary_difference_data_of_normalization
    (S : Fields) (H P : ℂ) (phiStar yStar : ℝ → ℂ)
    {L t B epsilon : ℝ} (hL : 0 < L)
    (hr : S.r t t = L) (hlam : S.lam t t = 1 / 2)
    (hstatic : phiStar L = P / (L : ℂ))
    (hstatic' : phiStar L + yStar L = 0)
    (hphi : ‖S.phi t t - H - P / (L : ℂ)‖ ≤ B * epsilon / L)
    (ha : ‖S.a t t - H‖ ≤ epsilon / L) :
    ‖scalarComparison S H phiStar t t‖ ≤ B * epsilon ∧
      ((S.lam t t : ℂ) *
        (S.phi t t - H - (phiStar (S.r t t) + yStar (S.r t t))) + S.theta t t) =
        (S.a t t - H) / 2 ∧
      ‖(S.a t t - H) / 2‖ ≤ epsilon / (2 * L) := by
  refine ⟨?_, ?_, ?_⟩
  · have heq : scalarComparison S H phiStar t t =
        (L : ℂ) * (S.phi t t - H - P / (L : ℂ)) := by
      simp only [scalarComparison, shiftedRphi, hr, hstatic]
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    calc
      _ ≤ L * (B * epsilon / L) := mul_le_mul_of_nonneg_left hphi hL.le
      _ = B * epsilon := by field_simp
  · simp only [hr, hstatic', sub_zero, Fields.a, hlam]
    push_cast
    ring
  · rw [norm_div, Complex.norm_ofNat]
    exact (div_le_div_of_nonneg_right ha (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

/-- [internal]
The electric logarithm has its finite-endpoint primitive. -/
theorem integral_outer_log {r L : ℝ} (hr : 0 < r) (hrL : r ≤ L) :
    (∫ s in r..L, Real.log (L / s)) = L - r - r * Real.log (L / r) := by
  have hL : 0 < L := hr.trans_le hrL
  have hs (s : ℝ) (hs : s ∈ Icc r L) : 0 < s := hr.trans_le hs.1
  have hlog : ContinuousOn (fun s => Real.log (L / s)) (Icc r L) :=
    (continuousOn_const.div continuousOn_id (fun s h => (hs s h).ne')).log
      (fun s h => (div_pos hL (hs s h)).ne')
  have hd (s : ℝ) (h : s ∈ uIcc r L) :
      HasDerivAt (fun t => t * Real.log (L / t) + t) (Real.log (L / s)) s := by
    have hsp : 0 < s := hs s (by simpa only [uIcc_of_le hrL] using h)
    have hld : HasDerivAt (fun t => Real.log (L / t)) (-1 / s) s := by
      convert ((hasDerivAt_const s L).div (hasDerivAt_id s) hsp.ne').log
        (div_ne_zero hL.ne' hsp.ne') using 1
      · rfl
      · dsimp only [Pi.div_apply, id_eq]
        field_simp
        ring
    convert ((hasDerivAt_id s).mul hld).add (hasDerivAt_id s) using 1
    · rfl
    · dsimp only [id_eq]
      field_simp
      ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hlog.intervalIntegrable_of_Icc hrL : IntervalIntegrable _ volume r L)
  simp only [div_self hL.ne', Real.log_one, mul_zero, zero_add] at hi
  linarith only [hi]

/-- [internal]
The normalized outgoing integral of the incoming electric logarithm has
the universal bound `1`, uniformly in both positive radii. -/
theorem integral_outer_log_le {r L : ℝ} (hr : 0 < r) (hrL : r ≤ L) :
    (1 / L) * (∫ s in r..L, Real.log (L / s)) ≤ 1 := by
  have hL := hr.trans_le hrL
  have hlog : 0 ≤ Real.log (L / r) := Real.log_nonneg ((one_le_div hr).mpr hrL)
  rw [integral_outer_log hr hrL]
  rw [show 1 / L * (L - r - r * Real.log (L / r)) =
    (L - r - r * Real.log (L / r)) / L by ring]
  apply (div_le_one hL).mpr
  nlinarith only [mul_nonneg hr.le hlog, hr.le]

/-- [internal]
The neutral incoming inverse-cube kernel, with its exact outer endpoint. -/
theorem integral_inv_cube_outer {r L : ℝ} (hr : 0 < r) (hrL : r ≤ L) :
    (∫ s in r..L, 1 / s ^ 3) = 1 / (2 * r ^ 2) - 1 / (2 * L ^ 2) := by
  have h := integral_zpow (a := r) (b := L) (n := (-3 : ℤ))
    (Or.inr ⟨by norm_num, notMem_uIcc_of_lt hr (hr.trans_le hrL)⟩)
  norm_num only [Int.reduceAdd, Int.cast_neg, Int.cast_ofNat, zpow_neg,
    zpow_ofNat, one_div] at h ⊢
  linear_combination h

/-- [internal]
The electric incoming inverse-fourth-power kernel, with exact outer endpoint. -/
theorem integral_inv_four_outer {r L : ℝ} (hr : 0 < r) (hrL : r ≤ L) :
    (∫ s in r..L, 1 / s ^ 4) = 1 / (3 * r ^ 3) - 1 / (3 * L ^ 3) := by
  have h := integral_zpow (a := r) (b := L) (n := (-4 : ℤ))
    (Or.inr ⟨by norm_num, notMem_uIcc_of_lt hr (hr.trans_le hrL)⟩)
  norm_num only [Int.reduceAdd, Int.cast_neg, Int.cast_ofNat, zpow_neg,
    zpow_ofNat, one_div] at h ⊢
  linear_combination h

/-- [internal]
The two electric radial source kernels have a uniform first integral;
the logarithm is retained. Numerical constants `1/3` and `1` are universal
and independent of the window, outer radius, charge and scalar background. -/
theorem Observation.electric_source_integrals {r L eta : ℝ}
    (hr : 0 < r) (hrL : r ≤ L) (heta : 0 ≤ eta) :
    (∫ s in r..L, eta / s ^ 4 + eta / (L * s)) ≤
      eta / (3 * r ^ 3) + eta / L * Real.log (L / r) ∧
    (eta / L) * (∫ s in r..L, Real.log (L / s)) ≤ eta := by
  have hL : 0 < L := hr.trans_le hrL
  have hc (n : ℕ) : ContinuousOn (fun s : ℝ => 1 / s ^ n) (Icc r L) :=
    continuousOn_const.div (continuousOn_id.pow n)
      (fun s hs => pow_ne_zero n (hr.trans_le hs.1).ne')
  have hfour := ((hc 4).intervalIntegrable_of_Icc hrL : IntervalIntegrable _ volume r L)
  have hone : IntervalIntegrable (fun s : ℝ => 1 / s) volume r L := by
    simpa only [pow_one] using
      ((hc 1).intervalIntegrable_of_Icc hrL : IntervalIntegrable _ volume r L)
  refine ⟨?_, ?_⟩
  · simp_rw [show ∀ s : ℝ, eta / s ^ 4 + eta / (L * s) =
        eta * (1 / s ^ 4) + (eta / L) * (1 / s) by intro s; ring]
    rw [intervalIntegral.integral_add (hfour.const_mul eta)
        (hone.const_mul (eta / L)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_inv_four_outer hr hrL, integral_one_div_of_pos hr hL]
    have hnonneg : 0 ≤ eta * (1 / (3 * L ^ 3)) := by positivity
    simp only [div_eq_mul_inv, one_mul, mul_sub] at hnonneg ⊢
    linarith only [hnonneg]
  · have hh := mul_le_mul_of_nonneg_left (integral_outer_log_le hr hrL) heta
    simpa only [mul_one, one_mul, div_eq_mul_inv, mul_assoc] using hh

/-- [internal]
Unitary incoming transport has numerical coefficient `1`, uniformly in
the real connection and interval. This is the AC integrating factor used
for the exact covariant comparison equation. -/
theorem unitary_transport_norm_le {w F : ℝ → ℂ} {B : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hw : AbsolutelyContinuousOnInterval w a b)
    (hB : IntervalIntegrable B volume a b) (hF : IntervalIntegrable F volume a b)
    (heq : ∀ᵐ s ∂volume.restrict (Icc a b),
      deriv w s = -I * (B s : ℂ) * w s + F s) :
    ‖w b‖ ≤ ‖w a‖ + ∫ s in a..b, ‖F s‖ := by
  let c : ℝ → ℂ := fun s => -I * (B s : ℂ)
  have hc : IntervalIntegrable c volume a b :=
    (show IntervalIntegrable (fun s => (B s : ℂ)) volume a b from
      ⟨hB.1.ofReal, hB.2.ofReal⟩).const_mul (-I)
  have hphase (t : ℝ) (ht : t ∈ Icc a b) :
      ‖Complex.exp (∫ s in a..t, c s)‖ = 1 ∧
      ‖Complex.exp (-(∫ s in a..t, c s))‖ = 1 := by
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    have hre := Complex.reCLM.intervalIntegral_comp_comm (hc.mono_set hsub)
    change (∫ s in a..t, (c s).re) = (∫ s in a..t, c s).re at hre
    have hzero : (∫ s in a..t, c s).re = 0 := by
      simpa only [c, Complex.neg_re, Complex.mul_re, Complex.neg_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        neg_zero, neg_mul, mul_zero, zero_mul, zero_sub,
        intervalIntegral.integral_zero] using hre.symm
    simp only [Complex.norm_exp, Complex.neg_re, hzero, neg_zero, Real.exp_zero,
      and_self]
  have hformula := EmcsfAcExtension.eq_integratingFactor_of_ac_deriv_eq_complex
    hab hw hc hF heq b ⟨hab, le_rfl⟩
  rw [hformula, norm_mul, (hphase b ⟨hab, le_rfl⟩).1, one_mul]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  apply intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall (fun s hs => ?_)) hF.norm
  rw [norm_mul, (hphase s (Ioc_subset_Icc_self hs)).2, one_mul]



/-- [internal]
Change of variables along a genuine null section. The sign `σ` records its
orientation; the numerical factor `8` is universal. No inverse radius map
or extension of the section is required. -/
theorem radial_section_integral_le {R d f : ℝ → ℝ} {a b ρ L σ : ℝ}
    (hab : a ≤ b) (hR : ∀ s ∈ Icc a b, HasDerivAt R (d s) s)
    (hd : ContinuousOn d (Icc a b)) (hbound : ∀ s ∈ Icc a b, R s ∈ Icc ρ L)
    (hf : ContinuousOn f (Icc ρ L)) (hf0 : ∀ r ∈ Icc ρ L, 0 ≤ f r)
    (hspeed : ∀ s ∈ Icc a b, 1 ≤ 8 * σ * d s) :
    (∫ s in a..b, f (R s)) ≤ 8 * σ * (∫ r in R a..R b, f r) := by
  have hRc : ContinuousOn R (Icc a b) := fun s hs => (hR s hs).continuousAt.continuousWithinAt
  have hfc : ContinuousOn (fun s => f (R s)) (Icc a b) := hf.comp hRc hbound
  have hsub := intervalIntegral.integral_comp_mul_deriv' (a := a) (b := b)
    (fun s hs => hR s (by simpa only [uIcc_of_le hab] using hs))
    (by simpa only [uIcc_of_le hab] using hd)
    (hf.mono (by rintro r ⟨s, hs, rfl⟩; exact hbound s (by simpa only [uIcc_of_le hab] using hs)))
  have hm := intervalIntegral.integral_mono_on hab
    (hfc.intervalIntegrable_of_Icc (μ := volume) hab)
    (((hfc.mul hd).const_mul (8 * σ)).intervalIntegrable_of_Icc (μ := volume) hab)
    (fun s hs => by
      have hh := mul_le_mul_of_nonneg_right (hspeed s hs) (hf0 (R s) (hbound s hs))
      simpa only [Pi.mul_apply, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using hh)
  rw [intervalIntegral.integral_const_mul] at hm
  exact hm.trans_eq (congrArg (fun z => 8 * σ * z) hsub)

/-- [internal]
The incoming neutral and electric radial kernels, retaining the finite
outer endpoint in the logarithm. Coefficients are universal. -/
theorem incoming_kernel_integral {A E r L : ℝ} (hr : 0 < r) (hrL : r ≤ L)
    (hA : 0 ≤ A) (hE : 0 ≤ E) :
    (∫ s in r..L, A / s^3 + E / s^4 + E / (L*s)) ≤
      A / r^2 + E / r^3 + E / L * Real.log (L/r) := by
  have hL : 0 < L := hr.trans_le hrL
  have hc (n : ℕ) : ContinuousOn (fun s : ℝ => 1 / s^n) (Icc r L) :=
    continuousOn_const.div (continuousOn_id.pow n) (fun s hs => pow_ne_zero n (hr.trans_le
        hs.1).ne')
  have h3 : IntervalIntegrable (fun s : ℝ => 1 / s^3) volume r L := (hc 3).intervalIntegrable_of_Icc
      hrL
  have h4 : IntervalIntegrable (fun s : ℝ => 1 / s^4) volume r L := (hc 4).intervalIntegrable_of_Icc
      hrL
  have h1 : IntervalIntegrable (fun s : ℝ => 1 / s) volume r L := by
    simpa using (hc 1).intervalIntegrable_of_Icc (μ := volume) hrL
  simp_rw [show ∀ s : ℝ, A / s^3 + E / s^4 + E / (L*s) =
    A * (1/s^3) + E * (1/s^4) + (E/L) * (1/s) by intro s; ring]
  rw [intervalIntegral.integral_add ((h3.const_mul A).add (h4.const_mul E)) (h1.const_mul (E/L)),
    intervalIntegral.integral_add (h3.const_mul A) (h4.const_mul E),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_inv_cube_outer hr hrL,
    integral_inv_four_outer hr hrL, integral_one_div_of_pos hr (hr.trans_le hrL)]
  have hn3 : 0 ≤ A / (2 * L^2) := by positivity
  have hn4 : 0 ≤ E / (3 * L^3) := by positivity
  have hp3 : 0 ≤ A / r^2 := by positivity
  have hp4 : 0 ≤ E / r^3 := by positivity
  linear_combination hn3 + hn4 + hp3 / 2 + 2 * hp4 / 3

/-- [internal]
Incoming AC transport with the actual radius derivative. The universal
optical lower bound `1/8` gives coefficient `8`, uniformly in the real
connection, the radius, and all source and boundary parameters. -/
theorem incoming_comparison_bound {w F : ℝ → ℂ} {B R d : ℝ → ℝ}
    {a b ρ L A E epsilon : ℝ} (hab : a ≤ b) (hρ : 0 < ρ)
    (hR : ∀ s ∈ Icc a b, HasDerivAt R (d s) s)
    (hd : ContinuousOn d (Icc a b)) (hbound : ∀ s ∈ Icc a b, R s ∈ Icc ρ L)
    (hspeed : ∀ s ∈ Icc a b, d s ≤ -(1 / 8)) (hRa : R a = L)
    (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hw : AbsolutelyContinuousOnInterval w a b)
    (hB : IntervalIntegrable B volume a b) (hF : IntervalIntegrable F volume a b)
    (heq : ∀ᵐ s ∂volume.restrict (Icc a b), deriv w s = -I * (B s : ℂ) * w s + F s)
    (hinit : ‖w a‖ ≤ epsilon / (2 * L))
    (hsource : ∀ s ∈ Icc a b, ‖F s‖ ≤ A / (R s) ^ 3 + E / (R s) ^ 4 + E / (L * R s)) :
    ‖w b‖ ≤ epsilon / (2*L) + 8*A/(R b)^2 + 8*E/(R b)^3 +
      8*E/L * Real.log (L/R b) := by
  let f : ℝ → ℝ := fun r => A/r^3 + E/r^4 + E/(L*r)
  have hL : 0 < L := hρ.trans_le (hbound b ⟨hab, le_rfl⟩).1 |>.trans_le (hbound b ⟨hab, le_rfl⟩).2
  have hf : ContinuousOn f (Icc ρ L) := by
    apply ContinuousOn.add
    · exact (continuousOn_const.div (continuousOn_id.pow 3)
        (fun s hs => pow_ne_zero 3 (hρ.trans_le hs.1).ne')).add
        (continuousOn_const.div (continuousOn_id.pow 4)
        (fun s hs => pow_ne_zero 4 (hρ.trans_le hs.1).ne'))
    · exact continuousOn_const.div (continuousOn_const.mul continuousOn_id)
        (fun s hs => mul_ne_zero hL.ne' (hρ.trans_le hs.1).ne')
  have hc : ContinuousOn R (Icc a b) := fun s hs => (hR s hs).continuousAt.continuousWithinAt
  have hm := intervalIntegral.integral_mono_on hab hF.norm
    ((hf.comp hc hbound).intervalIntegrable_of_Icc hab) hsource
  have hr := radial_section_integral_le (σ := -1) hab hR hd hbound hf
    (fun s hs => by dsimp [f]; have hp := hρ.trans_le hs.1; positivity)
    (fun s hs => by linarith only [hspeed s hs])
  rw [hRa, intervalIntegral.integral_symm (a := R b) (b := L)] at hr
  have hk := incoming_kernel_integral (hρ.trans_le (hbound b ⟨hab, le_rfl⟩).1)
    (hbound b ⟨hab, le_rfl⟩).2 hA hE
  have hu := unitary_transport_norm_le hab hw hB hF heq
  change (∫ s in R b..L, f s) ≤ _ at hk
  have hr' : (∫ s in a..b, f (R s)) ≤ 8 * (∫ s in R b..L, f s) := by
    convert hr using 1; ring
  exact (hu.trans (add_le_add hinit (hm.trans (hr'.trans
    (mul_le_mul_of_nonneg_left hk (by norm_num)))))).trans_eq (by ring)

/-- [internal]
The second radial integral has coefficients `1/2`, `8`, and `12`,
uniformly in the outer radius and in every inner radius at least `1`. -/
theorem outgoing_kernel_integral {A E epsilon r L : ℝ}
    (hr : 1 ≤ r) (hrL : r ≤ L) (hA : 0 ≤ A) (hE : 0 ≤ E) (he : 0 ≤ epsilon) :
    (∫ s in r..L, epsilon/(2*L) + 8*A/s^2 + 8*E/s^3 +
      8*E/L * Real.log (L/s)) ≤ epsilon/2 + 8*A/r + 12*E := by
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hL : 0 < L := hrp.trans_le hrL
  have hc (n : ℕ) : ContinuousOn (fun s : ℝ => 1 / s^n) (Icc r L) :=
    continuousOn_const.div (continuousOn_id.pow n)
      (fun s hs => pow_ne_zero n (hrp.trans_le hs.1).ne')
  have h2 : IntervalIntegrable (fun s : ℝ => 1/s^2) volume r L :=
    (hc 2).intervalIntegrable_of_Icc hrL
  have h3 : IntervalIntegrable (fun s : ℝ => 1/s^3) volume r L :=
    (hc 3).intervalIntegrable_of_Icc hrL
  have hlog : IntervalIntegrable (fun s : ℝ => Real.log (L/s)) volume r L :=
    ((continuousOn_const.div continuousOn_id (fun s hs => (hrp.trans_le hs.1).ne')).log
      (fun s hs => (div_pos hL (hrp.trans_le hs.1)).ne')).intervalIntegrable_of_Icc hrL
  have hi2 : (∫ s in r..L, 1/s^2) = 1/r - 1/L := by
    have h := integral_zpow (a := r) (b := L) (n := (-2 : ℤ))
      (Or.inr ⟨by norm_num, notMem_uIcc_of_lt hrp hL⟩)
    norm_num only [Int.reduceAdd, Int.cast_neg, Int.cast_one, zpow_neg,
      zpow_one, zpow_ofNat, one_div] at h ⊢
    linear_combination h
  simp_rw [show ∀ s : ℝ, epsilon/(2*L) + 8*A/s^2 + 8*E/s^3 +
    8*E/L * Real.log (L/s) = epsilon/(2*L) + (8*A)*(1/s^2) +
      (8*E)*(1/s^3) + (8*E/L)*Real.log (L/s) by intro s; ring]
  rw [intervalIntegral.integral_add
      (((intervalIntegrable_const).add (h2.const_mul (8*A))).add (h3.const_mul (8*E)))
      (hlog.const_mul (8*E/L)),
    intervalIntegral.integral_add ((intervalIntegrable_const).add (h2.const_mul (8*A)))
      (h3.const_mul (8*E)),
    intervalIntegral.integral_add intervalIntegrable_const (h2.const_mul (8*A)),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hi2, integral_inv_cube_outer hrp hrL]
  have hlogb := mul_le_mul_of_nonneg_left (integral_outer_log_le hrp hrL) (show 0 ≤ 8*E
      by positivity)
  have hconst : (L-r) * (epsilon/(2*L)) ≤ epsilon/2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 2*L by positivity)).mpr
    nlinarith only [mul_nonneg hrp.le he]
  have hneutral : 8*A*(1/r - 1/L) ≤ 8*A/r := by
    have hh : 0 ≤ 8*A/L := by positivity
    linear_combination hh
  have helec : 8*E*(1/(2*r^2)-1/(2*L^2)) ≤ 4*E := by
    have hrr : 1 ≤ r^2 := by nlinarith only [sq_nonneg (r-1), hr]
    have hh : 0 ≤ 8*E/(2*L^2) := by positivity
    have hfrac : 8*E/(2*r^2) ≤ 4*E := by
      apply (div_le_iff₀ (by positivity : 0 < 2*r^2)).mpr
      nlinarith only [mul_nonneg hE (sub_nonneg.mpr hrr)]
    linear_combination hfrac + hh
  simp only [smul_eq_mul] at *
  have hlogb' : (8*E/L) * (∫ s in r..L, Real.log (L/s)) ≤ 8*E := by
    convert hlogb using 1 <;> ring
  exact (add_le_add (add_le_add (add_le_add hconst hneutral) helec) hlogb').trans_eq (by ring)


/-- [internal]
Outgoing integration from the diagonal cylinder. The coefficients `4`,
`64`, and `96` are universal; only `Ct` comes from the boundary value. -/
theorem outgoing_comparison_bound {w wV : ℝ → ℂ} {R d : ℝ → ℝ}
    {a b ρ L A E epsilon Ct : ℝ} (hab : a ≤ b) (hρ : 1 ≤ ρ)
    (hR : ∀ s ∈ Icc a b, HasDerivAt R (d s) s)
    (hd : ContinuousOn d (Icc a b)) (hbound : ∀ s ∈ Icc a b, R s ∈ Icc ρ L)
    (hspeed : ∀ s ∈ Icc a b, 1 / 8 ≤ d s) (hRb : R b = L)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (he : 0 ≤ epsilon)
    (hw : ∀ s ∈ Icc a b, HasDerivAt w (wV s) s)
    (hwV : IntervalIntegrable wV volume a b)
    (hinit : ‖w b‖ ≤ Ct * epsilon)
    (hV : ∀ s ∈ Icc a b, ‖wV s‖ ≤ epsilon / (2 * L) + 8 * A / (R s) ^ 2 +
      8 * E / (R s) ^ 3 + 8 * E / L * Real.log (L / R s)) :
    ‖w a‖ ≤ (Ct+4)*epsilon + 64*A/(R a) + 96*E := by
  have hρp : 0 < ρ := zero_lt_one.trans_le hρ
  have hL : 0 < L := hρp.trans_le (hbound a ⟨le_rfl, hab⟩).1 |>.trans_le (hbound a ⟨le_rfl, hab⟩).2
  let f : ℝ → ℝ := fun r => epsilon/(2*L) + 8*A/r^2 + 8*E/r^3 + 8*E/L * Real.log (L/r)
  have hf : ContinuousOn f (Icc ρ L) := by
    apply ContinuousOn.add
    · exact (continuousOn_const.add (continuousOn_const.div (continuousOn_id.pow 2)
        (fun s hs => pow_ne_zero 2 (hρp.trans_le hs.1).ne'))).add
        (continuousOn_const.div (continuousOn_id.pow 3)
        (fun s hs => pow_ne_zero 3 (hρp.trans_le hs.1).ne'))
    · exact ((continuousOn_const.div continuousOn_id
        (fun s hs => (hρp.trans_le hs.1).ne')).log
        (fun s hs => (div_pos hL (hρp.trans_le hs.1)).ne')).const_mul _
  have hc : ContinuousOn R (Icc a b) := fun s hs => (hR s hs).continuousAt.continuousWithinAt
  have hm := intervalIntegral.integral_mono_on hab hwV.norm
    ((hf.comp hc hbound).intervalIntegrable_of_Icc hab) hV
  have hr := radial_section_integral_le (σ := 1) hab hR hd hbound hf
    (fun s hs => by
      dsimp [f]; have hp := hρp.trans_le hs.1
      have hlog := Real.log_nonneg ((one_le_div hp).mpr hs.2)
      positivity)
    (fun s hs => by linarith only [hspeed s hs])
  rw [hRb] at hr
  have hk := outgoing_kernel_integral (hρ.trans (hbound a ⟨le_rfl, hab⟩).1)
    (hbound a ⟨le_rfl, hab⟩).2 hA hE he
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
    (fun s hs => hw s (by simpa only [uIcc_of_le hab] using hs)) hwV
  have hn : ‖w a‖ ≤ ‖w b‖ + (∫ s in a..b, ‖wV s‖) := by
    calc
      ‖w a‖ = ‖w b - (w b - w a)‖ := by congr 1; abel
      _ ≤ ‖w b‖ + ‖w b-w a‖ := norm_sub_le _ _
      _ ≤ ‖w b‖ + (∫ s in a..b, ‖wV s‖) := by
        rw [← hftc]; exact add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm (f :=
            wV) (μ := volume) hab)
  have hr' : (∫ s in a..b, f (R s)) ≤ 8 * (∫ s in R a..L, f s) := by simpa using hr
  exact (hn.trans (add_le_add hinit (hm.trans (hr'.trans
    (mul_le_mul_of_nonneg_left hk (by norm_num)))))).trans_eq (by ring)


/-- [internal]
Exact scalar reconstruction from the incoming estimate proved above.
The boundary coefficient is the universal number `4`; the neutral
coefficient is `64*Cn+1`, and the electric coefficient is `64*Ce`.
These constants are fixed before the actual fields and are uniform in
radius, background, coupling, and solution; `Ce` retains only its upstream
window/gap dependence. The mass term keeps its sharper inverse-square
power, and the electric logarithm is retained. -/
theorem co_outer_y_of_incoming_estimate
    (Cn Ce : ℝ) (hCn : 0 ≤ Cn)
    {S : Fields} {H : ℂ} {phiStar yStar : ℝ → ℂ} {u v : ℝ}
    {L Nphi Nm epsilon eta : ℝ} {wV : ℂ}
    (hr : 1 ≤ S.r u v) (hlam : 1 / 8 ≤ S.lam u v) (hNp : 0 ≤ Nphi)
    (hw : ‖scalarComparison S H phiStar u v‖ ≤ Nphi)
    (hident : (S.lam u v : ℂ) *
      (S.phi u v - H - (phiStar (S.r u v) + yStar (S.r u v))) + S.theta u v = wV)
    (hV : ‖wV‖ ≤ epsilon / (2 * L) + 8 * (Cn * (Nphi + Nm)) / (S.r u v) ^ 2 +
      8 * (Ce * eta) / (S.r u v) ^ 3 + 8 * (Ce * eta) / L * Real.log (L / S.r u v)) :
    ‖S.theta u v/(S.lam u v : ℂ)-yStar (S.r u v)‖ ≤
      4*epsilon/L + (64*Cn+1)*Nphi/(S.r u v) + 64*Cn*Nm/(S.r u v)^2 +
        64*Ce*eta/(S.r u v)^3 + 64*Ce*eta/L * Real.log (L/S.r u v) := by
  have hrp : 0 < S.r u v := zero_lt_one.trans_le hr
  have hlp : 0 < S.lam u v := (by norm_num : (0:ℝ) < 1/8).trans_le hlam
  rw [outer_y_reconstruction S H phiStar yStar hrp.ne' hlp.ne', hident]
  have hdiv : ‖wV‖ / S.lam u v ≤ 8*‖wV‖ := by
    apply (div_le_iff₀ hlp).mpr
    have hh := mul_le_mul_of_nonneg_left hlam (norm_nonneg wV)
    nlinarith only [hh]
  have hnorm : ‖wV/(S.lam u v : ℂ)-scalarComparison S H phiStar u v/(S.r u v : ℂ)‖ ≤
      8*‖wV‖ + Nphi/(S.r u v) := by
    apply (norm_sub_le _ _).trans
    rw [norm_div, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlp, abs_of_pos hrp]
    exact add_le_add hdiv (div_le_div_of_nonneg_right hw hrp.le)
  have hrr : S.r u v ≤ (S.r u v)^2 := by
    nlinarith only [mul_nonneg hrp.le (sub_nonneg.mpr hr)]
  have hneutral := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ 64*Cn*Nphi) hrp hrr
  calc
    _ ≤ 8*(epsilon/(2*L) + 8*(Cn*(Nphi+Nm))/(S.r u v)^2 +
      8*(Ce*eta)/(S.r u v)^3 + 8*(Ce*eta)/L * Real.log (L/S.r u v)) + Nphi/(S.r u v) :=
      hnorm.trans (add_le_add (mul_le_mul_of_nonneg_left hV (by norm_num)) le_rfl)
    _ = 4*epsilon/L + (64*Cn*Nphi/(S.r u v)^2 + Nphi/(S.r u v)) +
      64*Cn*Nm/(S.r u v)^2 + 64*Ce*eta/(S.r u v)^3 +
        64*Ce*eta/L * Real.log (L/S.r u v) := by ring
    _ ≤ _ := by linear_combination hneutral

/-- [internal]
Incoming-then-outgoing integration of the previous source envelope on the
literal positive-radius sideways truncation. All characteristic segments
stay in this same set, so the source uses the same `Nphi` and `Nm`.
The constants are fixed before the actual fields: the boundary coefficient
becomes `Ct+4`, the universal neutral coefficient becomes `64*Cn`, and the
window/gap electric coefficient becomes `96*Ce`. They are uniform in the
outer radius, truncation, scalar background, coupling, and solution.
The first conclusion retains the single-integration electric logarithm.
The third conclusion applies exact scalar reconstruction to this proved
incoming estimate, retaining the sharper mass power and the logarithm. -/
theorem co_outer_sup_of_source_envelope
    (Ct Cn Ce : ℝ) (hCt : 0 ≤ Ct) (hCn : 0 ≤ Cn) (hCe : 0 ≤ Ce)
    {S : Fields} {D : Set (ℝ × ℝ)} {H : ℂ} {phiStar yStar : ℝ → ℂ}
    {a b ρ L L₀ Nphi Nm epsilon eta : ℝ}
    (wV F : ℝ → ℝ → ℂ) (B : ℝ → ℝ → ℝ)
    (hL₀ : 1 ≤ L₀) (hρ : L₀ ≤ ρ)
    (hNp : 0 ≤ Nphi) (hNm : 0 ≤ Nm) (he : 0 ≤ epsilon) (heta : 0 ≤ eta)
    (hsub : ∀ p ∈ sidewaysTruncation S D a b ρ L,
      sidewaysTriangle p.2 p.1 ⊆ sidewaysTruncation S D a b ρ L)
    (hrin : ∀ p ∈ sidewaysTruncation S D a b ρ L,
      HasDerivAt (fun s => S.r s p.2) (S.nu p.1 p.2) p.1)
    (hrout : ∀ p ∈ sidewaysTruncation S D a b ρ L,
      HasDerivAt (S.r p.1) (S.lam p.1 p.2) p.2)
    (hopt : ∀ p ∈ sidewaysTruncation S D a b ρ L,
      ContinuousOn (fun s => S.nu s p.2) (Icc p.2 p.1) ∧
      ContinuousOn (S.lam p.1) (Icc p.2 p.1))
    (hspeed : ∀ p ∈ sidewaysTruncation S D a b ρ L,
      S.nu p.1 p.2 ≤ -(1 / 8) ∧ 1 / 8 ≤ S.lam p.1 p.2)
    (hboundary : ∀ t, (t, t) ∈ sidewaysTruncation S D a b ρ L →
      S.r t t = L ∧ ‖scalarComparison S H phiStar t t‖ ≤ Ct * epsilon ∧
      ‖wV t t‖ ≤ epsilon / (2 * L))
    (hac : ∀ p ∈ sidewaysTruncation S D a b ρ L,
      AbsolutelyContinuousOnInterval (fun s => wV s p.2) p.2 p.1)
    (hiB : ∀ p ∈ sidewaysTruncation S D a b ρ L,
      IntervalIntegrable (fun s => B s p.2) volume p.2 p.1)
    (hiF : ∀ p ∈ sidewaysTruncation S D a b ρ L,
      IntervalIntegrable (fun s => F s p.2) volume p.2 p.1)
    (heq : ∀ p ∈ sidewaysTruncation S D a b ρ L,
      ∀ᵐ s ∂volume.restrict (Icc p.2 p.1),
        deriv (fun s => wV s p.2) s = -I * (B s p.2 : ℂ) * wV s p.2 + F s p.2)
    (hw : ∀ p ∈ sidewaysTruncation S D a b ρ L,
      HasDerivAt (scalarComparison S H phiStar p.1) (wV p.1 p.2) p.2)
    (hiV : ∀ p ∈ sidewaysTruncation S D a b ρ L,
      IntervalIntegrable (wV p.1) volume p.2 p.1)
    (hscalar : ∀ p ∈ sidewaysTruncation S D a b ρ L,
      ‖scalarComparison S H phiStar p.1 p.2‖ ≤ Nphi)
    (hident : ∀ p ∈ sidewaysTruncation S D a b ρ L,
      (S.lam p.1 p.2 : ℂ) * (S.phi p.1 p.2 - H -
        (phiStar (S.r p.1 p.2) + yStar (S.r p.1 p.2))) + S.theta p.1 p.2 = wV p.1 p.2)
    (hsource : ∀ p ∈ sidewaysTruncation S D a b ρ L,
      ‖F p.1 p.2‖ ≤ Cn * (Nphi + Nm) / (S.r p.1 p.2) ^ 3 +
        Ce * (eta / (S.r p.1 p.2) ^ 4 + eta / (L * S.r p.1 p.2))) :
    (∀ p ∈ sidewaysTruncation S D a b ρ L,
      ‖wV p.1 p.2‖ ≤ epsilon/(2*L) + 8*(Cn*(Nphi+Nm))/(S.r p.1 p.2)^2 +
        8*(Ce*eta)/(S.r p.1 p.2)^3 + 8*(Ce*eta)/L * Real.log (L/S.r p.1 p.2)) ∧
    comparisonNorm (sidewaysTruncation S D a b ρ L) (scalarComparison S H phiStar) ≤
      ENNReal.ofReal ((Ct+4)*epsilon + 64*(Cn*(Nphi+Nm))/L₀ + 96*(Ce*eta)) ∧
    (∀ p ∈ sidewaysTruncation S D a b ρ L,
      ‖S.theta p.1 p.2/(S.lam p.1 p.2 : ℂ)-yStar (S.r p.1 p.2)‖ ≤
        4*epsilon/L + (64*Cn+1)*Nphi/(S.r p.1 p.2) + 64*Cn*Nm/(S.r p.1 p.2)^2 +
          64*Ce*eta/(S.r p.1 p.2)^3 + 64*Ce*eta/L * Real.log (L/S.r p.1 p.2)) := by
  have hρp : 0 < ρ := zero_lt_one.trans_le (hL₀.trans hρ)
  have hA : 0 ≤ Cn*(Nphi+Nm) := by positivity
  have hE : 0 ≤ Ce*eta := by positivity
  have hV (p) (hp : p ∈ sidewaysTruncation S D a b ρ L) :
      ‖wV p.1 p.2‖ ≤ epsilon/(2*L) + 8*(Cn*(Nphi+Nm))/(S.r p.1 p.2)^2 +
        8*(Ce*eta)/(S.r p.1 p.2)^3 + 8*(Ce*eta)/L * Real.log (L/S.r p.1 p.2) := by
    have hpath := (sidewaysTruncation_paths (hsub p hp)).1
    have huv := hp.1.2.2.1
    apply incoming_comparison_bound huv hρp
      (fun s hs => hrin (s,p.2) (hpath s hs)) (hopt p hp).1
      (fun s hs => (hpath s hs).2) (fun s hs => (hspeed (s,p.2) (hpath s hs)).1)
      (hboundary p.2 (hpath p.2 ⟨le_rfl, huv⟩)).1 hA hE
      (hac p hp) (hiB p hp) (hiF p hp) (heq p hp)
      (hboundary p.2 (hpath p.2 ⟨le_rfl, huv⟩)).2.2
    intro s hs
    convert hsource (s,p.2) (hpath s hs) using 1; ring
  refine ⟨hV, comparisonNorm_le_of_bound (by positivity) ?_, ?_⟩
  · intro p hp
    have hpath := (sidewaysTruncation_paths (hsub p hp)).2
    have huv := hp.1.2.2.1
    have hb := outgoing_comparison_bound huv (hL₀.trans hρ)
      (fun s hs => hrout (p.1,s) (hpath s hs)) (hopt p hp).2
      (fun s hs => (hpath s hs).2) (fun s hs => (hspeed (p.1,s) (hpath s hs)).2)
      (hboundary p.1 (hpath p.1 ⟨huv, le_rfl⟩)).1 hA hE he
      (fun s hs => hw (p.1,s) (hpath s hs)) (hiV p hp)
      (hboundary p.1 (hpath p.1 ⟨huv, le_rfl⟩)).2.1
      (fun s hs => hV (p.1,s) (hpath s hs))
    exact hb.trans (add_le_add (add_le_add le_rfl
      (div_le_div_of_nonneg_left (by positivity : 0 ≤ 64*(Cn*(Nphi+Nm)))
        (zero_lt_one.trans_le hL₀) (hρ.trans hp.2.1))) le_rfl)
  · intro p hp
    exact co_outer_y_of_incoming_estimate Cn Ce hCn
      (hL₀.trans (hρ.trans hp.2.1)) (hspeed p hp).2 hNp
      (hscalar p hp) (hident p hp) (hV p hp)

end EmcsfAcExtension.Global
