module

public import EmcsfAcExtension.Global.Observation.Domains
public import EmcsfAcExtension.Frozen.Fields.PhiV
public import EmcsfAcExtension.Frozen.Fields.ChargeV
public import EmcsfAcExtension.Frozen.Fields.MassV

/-! # Maxwell's outward-anchored primitive

The imaginary part is simplified before a derivative is estimated. The
primitive is anchored at the outer cylinder and retains the factor two in
the scalar-background term. Source: `charged_SF_new_version.tex:L2359–L2389` and the
approved internal project record section `eq:co-maxwell-ibp`.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

/-- [internal]
The pointwise imaginary-part cancellation in the shifted Maxwell integrand.
The removed term is real, so this identity needs no radius denominator. -/
theorem maxwell_shifted_imaginary_part (s : ℝ) (H phi y : ℂ) :
    s * (starRingEnd ℂ phi * y).im =
      (starRingEnd ℂ H *
        ((s : ℂ) * (phi - H + y) - (s : ℂ) * (phi - H)) +
        starRingEnd ℂ ((s : ℂ) * (phi - H)) * (phi - H + y)).im := by
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.add_re]
  ring

/-- [internal]
Cancel the real contribution before bounding the quadratic Maxwell term.
In particular no bound on the full derivative of the shifted scalar is used. -/
theorem maxwell_quadratic_imaginary_part (s : ℝ) (H phi y : ℂ) :
    (starRingEnd ℂ ((s : ℂ) * (phi - H)) * (phi - H + y)).im =
      (starRingEnd ℂ ((s : ℂ) * (phi - H)) * y).im := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im]
  ring

/-- [internal]
The actual shifted scalar has radial derivative `φ-H+y`. The input is the
normalized outgoing scalar equation, rather than a charged shift symmetry. -/
theorem shifted_radial_deriv_of_normalization {phi : ℝ → ℂ} {H y : ℂ} {s : ℝ}
    (hs : s ≠ 0) (hphi : HasDerivAt phi (y / (s : ℂ)) s) :
    HasDerivAt (fun (t : ℝ) => (t : ℂ) * (phi t - H)) (phi s - H + y) s := by
  have h : HasDerivAt (fun (t : ℝ) => (t : ℂ) * (phi t - H))
      (phi s - H + (s : ℂ) * (y / (s : ℂ))) s := by
    simpa only [Pi.mul_apply, id_eq, Complex.ofReal_one, one_mul] using!
      (hasDerivAt_id s).ofReal_comp.mul (hphi.sub_const H)
  apply h.congr_deriv
  field_simp [Complex.ofReal_ne_zero.mpr hs]

/-- [internal]
Exact Maxwell integration by parts on any positive-radius outgoing section.
There are no constants. Normalization inputs are the continuous radial
scalar/normalized scalar and charge on the closed interval, and their scalar
and Maxwell equations in its interior. The boundary value is `Q L`.
The two field equations come from the normalization packet; the section
inclusions are proved in `Domains.lean`. -/
theorem co_maxwell_ibp_of_normalization
    (e r L : ℝ) (H : ℂ) (phi y : ℝ → ℂ) (Q : ℝ → ℝ)
    (hr : 0 < r) (hrL : r ≤ L)
    (hcphi : ContinuousOn phi (Icc r L)) (hcy : ContinuousOn y (Icc r L))
    (hcQ : ContinuousOn Q (Icc r L))
    (hphi : ∀ s ∈ Ioo r L, HasDerivAt phi (y s / (s : ℂ)) s)
    (hQ : ∀ s ∈ Ioo r L,
      HasDerivAt Q (-e * (s * (starRingEnd ℂ (phi s) * y s).im)) s) :
    let psi : ℝ → ℂ := fun s => (s : ℂ) * (phi s - H)
    Q r = Q L + e *
      (starRingEnd ℂ H *
          ((L : ℂ) * psi L - (r : ℂ) * psi r - 2 * ∫ s in r..L, psi s) +
        ∫ s in r..L, starRingEnd ℂ (psi s) * deriv psi s).im := by
  dsimp only
  let psi : ℝ → ℂ := fun s => (s : ℂ) * (phi s - H)
  let dpsi : ℝ → ℂ := fun s => phi s - H + y s
  have hcpsi : ContinuousOn psi (Icc r L) :=
    Complex.continuous_ofReal.continuousOn.mul (hcphi.sub continuousOn_const)
  have hcdpsi : ContinuousOn dpsi (Icc r L) :=
    (hcphi.sub continuousOn_const).add hcy
  have hdpsi (s) (hs : s ∈ Ioo r L) : HasDerivAt psi (dpsi s) s :=
    shifted_radial_deriv_of_normalization (ne_of_gt (hr.trans hs.1)) (hphi s hs)
  have hpsi : IntervalIntegrable psi volume r L := hcpsi.intervalIntegrable_of_Icc hrL
  have hdpsii : IntervalIntegrable dpsi volume r L := hcdpsi.intervalIntegrable_of_Icc hrL
  have hprod : IntervalIntegrable (fun s => (s : ℂ) * dpsi s) volume r L :=
    (Complex.continuous_ofReal.continuousOn.mul hcdpsi).intervalIntegrable_of_Icc hrL
  have hquad : IntervalIntegrable (fun s => starRingEnd ℂ (psi s) * dpsi s) volume r L :=
    (hcpsi.star.mul hcdpsi).intervalIntegrable_of_Icc hrL
  have hlin : ContinuousOn (fun (s : ℝ) => (s : ℂ) * dpsi s - psi s) (Icc r L) := by
    simpa only [Pi.sub_apply, Pi.mul_apply] using!
      (Complex.continuous_ofReal.continuousOn.mul hcdpsi).sub hcpsi
  have hall : ContinuousOn
      (fun (s : ℝ) => starRingEnd ℂ H * ((s : ℂ) * dpsi s - psi s) +
        starRingEnd ℂ (psi s) * dpsi s) (Icc r L) :=
    (continuousOn_const.mul hlin).add (hcpsi.star.mul hcdpsi)
  have hibp : (∫ s in r..L, (s : ℂ) * dpsi s) =
      (L : ℂ) * psi L - (r : ℂ) * psi r - ∫ s in r..L, psi s := by
    have h := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
      Complex.continuous_ofReal.continuousOn
      (by simpa only [uIcc_of_le hrL] using hcpsi)
      (fun s _ => (hasDerivAt_id s).ofReal_comp)
      (fun s hs => hdpsi s (by simpa only [min_eq_left hrL, max_eq_right hrL] using hs))
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume r L)
      hdpsii
    simp only [Complex.ofReal_one, one_mul] at h
    rw [intervalIntegral.integral_add hpsi hprod] at h
    linear_combination h
  have hint : (∫ s in r..L, s * (starRingEnd ℂ (phi s) * y s).im) =
      (starRingEnd ℂ H *
          ((L : ℂ) * psi L - (r : ℂ) * psi r - 2 * ∫ s in r..L, psi s) +
        ∫ s in r..L, starRingEnd ℂ (psi s) * dpsi s).im := by
    calc
      _ = ∫ s in r..L,
          (starRingEnd ℂ H * ((s : ℂ) * dpsi s - psi s) +
            starRingEnd ℂ (psi s) * dpsi s).im := by
        apply intervalIntegral.integral_congr
        intro s _
        exact maxwell_shifted_imaginary_part s H (phi s) (y s)
      _ = _ := by
        have halli : IntervalIntegrable
            (fun (s : ℝ) => starRingEnd ℂ H * ((s : ℂ) * dpsi s - psi s) +
              starRingEnd ℂ (psi s) * dpsi s) volume r L :=
          hall.intervalIntegrable_of_Icc hrL
        have him := Complex.imCLM.intervalIntegral_comp_comm halli
        change (∫ s in r..L,
            (starRingEnd ℂ H * ((s : ℂ) * dpsi s - psi s) +
              starRingEnd ℂ (psi s) * dpsi s).im) =
          (∫ s in r..L, starRingEnd ℂ H * ((s : ℂ) * dpsi s - psi s) +
            starRingEnd ℂ (psi s) * dpsi s).im at him
        rw [him,
          intervalIntegral.integral_add
            ((hlin.intervalIntegrable_of_Icc hrL).const_mul _) hquad,
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub hprod hpsi, hibp]
        congr 2
        ring
  have hqi : IntervalIntegrable
      (fun s => -e * (s * (starRingEnd ℂ (phi s) * y s).im)) volume r L := by
    exact (continuousOn_const.mul
      (continuousOn_id.mul (Complex.continuous_im.comp_continuousOn
        (hcphi.star.mul hcy)))).intervalIntegrable_of_Icc hrL
  have hq := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrL hcQ hQ hqi
  rw [intervalIntegral.integral_const_mul, hint] at hq
  have heq : (∫ s in r..L, starRingEnd ℂ (psi s) * deriv psi s) =
      ∫ s in r..L, starRingEnd ℂ (psi s) * dpsi s := by
    apply intervalIntegral.integral_congr_uIoo
    intro s hs
    dsimp only
    rw [(hdpsi s (by simpa only [uIoo_of_le hrL] using hs)).deriv]
  change Q r = Q L + e *
    (starRingEnd ℂ H *
        ((L : ℂ) * psi L - (r : ℂ) * psi r - 2 * ∫ s in r..L, psi s) +
      ∫ s in r..L, starRingEnd ℂ (psi s) * deriv psi s).im
  rw [heq]
  linarith only [hq]

/-- [internal]
The radial scalar energy bounds its first moment by `5 √L`, with a universal
coefficient. The radius interval may degenerate; no estimate depends on its
outer endpoint. Young's inequality supplies the Cauchy–Schwarz bound. -/
theorem integral_norm_le_sqrt_outer {y : ℝ → ℂ} {r L : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ L) (hL : 0 < L)
    (hy : ContinuousOn y (Icc r L))
    (henergy : (∫ s in r..L, ‖y s‖ ^ 2) ≤ 8) :
    (∫ s in r..L, ‖y s‖) ≤ 5 * Real.sqrt L := by
  have hyi : IntervalIntegrable (fun s => ‖y s‖) volume r L :=
    hy.norm.intervalIntegrable_of_Icc hrL
  have hy2i : IntervalIntegrable (fun s => ‖y s‖ ^ 2) volume r L :=
    (hy.norm.pow 2).intervalIntegrable_of_Icc hrL
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  have hsq := Real.sq_sqrt hL.le
  have hpoint (s : ℝ) : 2 * Real.sqrt L * ‖y s‖ ≤ L * ‖y s‖ ^ 2 + 1 := by
    have hh := sq_nonneg (Real.sqrt L * ‖y s‖ - 1)
    nlinarith only [hh, hsq]
  have hint := intervalIntegral.integral_mono_on hrL
    (hyi.const_mul (2 * Real.sqrt L))
    ((hy2i.const_mul L).add intervalIntegrable_const) (fun s _ => hpoint s)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (hy2i.const_mul L) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hint
  simp only [smul_eq_mul, mul_one] at hint
  have hbound := mul_le_mul_of_nonneg_left henergy hL.le
  have hh : 2 * Real.sqrt L * (∫ s in r..L, ‖y s‖) ≤ 9 * L := by
    nlinarith only [hint, hbound, hr]
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * Real.sqrt L by positivity)).mp
  nlinarith only [hh, hsq, hL]

/-- [internal]
The improved charge estimate on an outward radial section. The positive
constant is chosen after the fixed shifted-scalar bound `K` and boundary
charge coefficient `B`, before every field, radius, coupling and scalar
background. These two upstream bounds depend only on the fixed window and
gap. Normalization supplies the two radial equations and the physical
identity for `eta`; the temporary bootstrap supplies the bound on `psi`.
The imaginary quadratic cancellation precedes every derivative estimate. -/
theorem co_charge_improved_of_normalization (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (e eta r L qStar : ℝ) (H : ℂ) (phi y : ℝ → ℂ) (Q : ℝ → ℝ),
        0 < r → r ≤ L → 1 ≤ L →
        |e| * L * (1 + ‖H‖) = eta →
        ContinuousOn phi (Icc r L) → ContinuousOn y (Icc r L) →
        ContinuousOn Q (Icc r L) →
        (∀ s ∈ Ioo r L, HasDerivAt phi (y s / (s : ℂ)) s) →
        (∀ s ∈ Ioo r L,
          HasDerivAt Q (-e * (s * (starRingEnd ℂ (phi s) * y s).im)) s) →
        (∀ s ∈ Icc r L, ‖(s : ℂ) * (phi s - H)‖ ≤ K) →
        (∫ s in r..L, ‖y s‖ ^ 2) ≤ 8 →
        |Q L - qStar| ≤ B * eta → |qStar| ≤ 1 → C * eta ≤ 1 →
        |Q r - qStar| ≤ C * eta ∧ |Q r| ≤ 2 := by
  refine ⟨B + 9 * K + 1, by positivity, ?_⟩
  intro e eta r L qStar H phi y Q hr hrL hL heta hcphi hcy hcQ hphi hQ
    hpsi henergy hboundary hq hsmall
  let psi : ℝ → ℂ := fun s => (s : ℂ) * (phi s - H)
  let dpsi : ℝ → ℂ := fun s => phi s - H + y s
  have hcpsi : ContinuousOn psi (Icc r L) :=
    Complex.continuous_ofReal.continuousOn.mul (hcphi.sub continuousOn_const)
  have hcdpsi : ContinuousOn dpsi (Icc r L) :=
    (hcphi.sub continuousOn_const).add hcy
  have hdpsi (s : ℝ) (hs : s ∈ Ioo r L) : HasDerivAt psi (dpsi s) s :=
    shifted_radial_deriv_of_normalization (hr.trans hs.1).ne' (hphi s hs)
  have hquad : IntervalIntegrable (fun s => starRingEnd ℂ (psi s) * dpsi s) volume r L :=
    (hcpsi.star.mul hcdpsi).intervalIntegrable_of_Icc hrL
  have hquadY : IntervalIntegrable (fun s => starRingEnd ℂ (psi s) * y s) volume r L :=
    (hcpsi.star.mul hcy).intervalIntegrable_of_Icc hrL
  have hquad_eq :
      (∫ s in r..L, starRingEnd ℂ (psi s) * deriv psi s).im =
      (∫ s in r..L, starRingEnd ℂ (psi s) * y s).im := by
    have heq : (∫ s in r..L, starRingEnd ℂ (psi s) * deriv psi s) =
        ∫ s in r..L, starRingEnd ℂ (psi s) * dpsi s := by
      apply intervalIntegral.integral_congr_uIoo
      intro s hs
      dsimp only
      rw [(hdpsi s (by simpa only [uIoo_of_le hrL] using hs)).deriv]
    have hid : (∫ s in r..L, starRingEnd ℂ (psi s) * dpsi s).im =
        ∫ s in r..L, (starRingEnd ℂ (psi s) * dpsi s).im :=
      (Complex.imCLM.intervalIntegral_comp_comm hquad).symm
    have hiy : (∫ s in r..L, starRingEnd ℂ (psi s) * y s).im =
        ∫ s in r..L, (starRingEnd ℂ (psi s) * y s).im :=
      (Complex.imCLM.intervalIntegral_comp_comm hquadY).symm
    rw [heq, hid, hiy]
    apply intervalIntegral.integral_congr
    intro s _
    exact maxwell_quadratic_imaginary_part s H (phi s) (y s)
  have hintpsi : ‖∫ s in r..L, psi s‖ ≤ K * (L - r) := by
    simpa only [abs_of_nonneg (sub_nonneg.mpr hrL)] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := r) (b := L)
        (fun s hs => hpsi s (Ioc_subset_Icc_self (by simpa only [uIoc_of_le hrL] using hs)))
  have hlin : ‖(L : ℂ) * psi L - (r : ℂ) * psi r - 2 * ∫ s in r..L, psi s‖ ≤
      4 * K * L := by
    calc
      _ ≤ ‖(L : ℂ) * psi L‖ + ‖(r : ℂ) * psi r‖ +
          ‖(2 : ℂ) * ∫ s in r..L, psi s‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ L * K + r * K + 2 * (K * (L - r)) := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ L by linarith only [hL]), abs_of_pos hr,
          Complex.norm_ofNat]
        exact add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left (hpsi L ⟨hrL, le_rfl⟩) (by positivity))
            (mul_le_mul_of_nonneg_left (hpsi r ⟨le_rfl, hrL⟩) hr.le))
          (mul_le_mul_of_nonneg_left hintpsi (by norm_num))
      _ ≤ 4 * K * L := by
        nlinarith only [mul_nonneg hK hr.le, mul_nonneg hK (zero_le_one.trans hL)]
  have hquad_bound : |(∫ s in r..L, starRingEnd ℂ (psi s) * deriv psi s).im| ≤
      5 * K * Real.sqrt L := by
    rw [hquad_eq]
    calc
      _ ≤ ‖∫ s in r..L, starRingEnd ℂ (psi s) * y s‖ := Complex.abs_im_le_norm _
      _ ≤ ∫ s in r..L, K * ‖y s‖ := by
        apply intervalIntegral.norm_integral_le_of_norm_le hrL
          (Filter.Eventually.of_forall (fun s hs => ?_))
          ((hcy.norm.intervalIntegrable_of_Icc hrL).const_mul K)
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (hpsi s (Ioc_subset_Icc_self hs)) (norm_nonneg _)
      _ = K * ∫ s in r..L, ‖y s‖ := intervalIntegral.integral_const_mul _ _
      _ ≤ 5 * K * Real.sqrt L := by
        have h := mul_le_mul_of_nonneg_left
          (integral_norm_le_sqrt_outer hr.le hrL (by linarith only [hL]) hcy henergy) hK
        linarith only [h]
  have hprimitive := co_maxwell_ibp_of_normalization e r L H phi y Q hr hrL
    hcphi hcy hcQ hphi hQ
  change Q r = Q L + e * (starRingEnd ℂ H *
      ((L : ℂ) * psi L - (r : ℂ) * psi r - 2 * ∫ s in r..L, psi s) +
      ∫ s in r..L, starRingEnd ℂ (psi s) * deriv psi s).im at hprimitive
  have hcharge : |Q r - qStar| ≤ B * eta +
      |e| * (‖H‖ * (4 * K * L) + 5 * K * Real.sqrt L) := by
    rw [hprimitive]
    calc
      _ ≤ |Q L - qStar| + |e| * |(starRingEnd ℂ H *
          ((L : ℂ) * psi L - (r : ℂ) * psi r - 2 * ∫ s in r..L, psi s) +
          ∫ s in r..L, starRingEnd ℂ (psi s) * deriv psi s).im| := by
        rw [add_sub_right_comm]
        exact (abs_add_le _ _).trans_eq (by rw [abs_mul])
      _ ≤ B * eta + |e| * (‖H‖ * (4 * K * L) + 5 * K * Real.sqrt L) := by
        apply add_le_add hboundary
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg e)
        apply (abs_add_le _ _).trans
        apply add_le_add ?_ hquad_bound
        exact (Complex.abs_im_le_norm _).trans
          (by simpa only [norm_mul, Complex.norm_conj] using
            mul_le_mul_of_nonneg_left hlin (norm_nonneg H))
  have hsqrt : Real.sqrt L ≤ L := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨zero_le_one.trans hL, ?_⟩
    nlinarith only [mul_nonneg (zero_le_one.trans hL) (sub_nonneg.mpr hL)]
  have heta0 : 0 ≤ eta := by rw [← heta]; positivity
  have hfinal : |Q r - qStar| ≤ (B + 9 * K + 1) * eta := by
    apply hcharge.trans
    have hmajor : ‖H‖ * (4 * K * L) + 5 * K * Real.sqrt L ≤
        9 * K * (L * (1 + ‖H‖)) := by
      have hh := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 5 * K by positivity)
      have hprod := mul_nonneg (mul_nonneg hK (show 0 ≤ L by linarith only [hL]))
        (norm_nonneg H)
      nlinarith only [hh, hprod, mul_nonneg hK (zero_le_one.trans hL)]
    have hh := mul_le_mul_of_nonneg_left hmajor (abs_nonneg e)
    have he : |e| * (9 * K * (L * (1 + ‖H‖))) = 9 * K * eta := by
      rw [← heta]; ring
    rw [he] at hh
    nlinarith only [hh, heta0]
  refine ⟨hfinal, ?_⟩
  have := (abs_add_le (Q r - qStar) qStar).trans (add_le_add (hfinal.trans hsmall) hq)
  simpa only [sub_add_cancel, show (1 : ℝ) + 1 = 2 by norm_num] using this

/-- [internal]
The universal radial scalar-energy bound `8` follows from the normalized
ordinary mass equation, the outer gap `1/2`, and mass in `[0,2]`.
It requires no axis endpoint or incoming scalar derivative. -/
theorem radial_scalar_energy_of_normalization {r L : ℝ}
    {m Q : ℝ → ℝ} {y : ℝ → ℂ} (hr : 0 < r) (hrL : r ≤ L)
    (hm : ContinuousOn m (Icc r L)) (hQ : ContinuousOn Q (Icc r L))
    (hy : ContinuousOn y (Icc r L))
    (hd : ∀ s ∈ Ioo r L, HasDerivAt m
      ((1 - 2 * m s / s) * ‖y s‖ ^ 2 / 2 + Q s ^ 2 / (2 * s ^ 2)) s)
    (hbox : ∀ s ∈ Icc r L, m s ∈ Icc 0 2 ∧ 1 / 2 ≤ 1 - 2 * m s / s) :
    (∫ s in r..L, ‖y s‖ ^ 2) ≤ 8 := by
  have hpos (s : ℝ) (hs : s ∈ Icc r L) : 0 < s := hr.trans_le hs.1
  have hf : ContinuousOn
      (fun s => (1 - 2 * m s / s) * ‖y s‖ ^ 2 / 2 + Q s ^ 2 / (2 * s ^ 2))
      (Icc r L) := by
    have hgap : ContinuousOn (fun s => 1 - 2 * m s / s) (Icc r L) :=
      continuousOn_const.sub ((continuousOn_const.mul hm).div
      continuousOn_id (fun s hs => (hpos s hs).ne'))
    exact ((hgap.mul (hy.norm.pow 2)).div_const 2).add
      ((hQ.pow 2).div (continuousOn_const.mul (continuousOn_id.pow 2))
        (fun s hs => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hpos s hs).ne')))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrL hm hd
    (hf.intervalIntegrable_of_Icc hrL)
  have hpoint (s : ℝ) (hs : s ∈ Icc r L) : ‖y s‖ ^ 2 / 4 ≤
      (1 - 2 * m s / s) * ‖y s‖ ^ 2 / 2 + Q s ^ 2 / (2 * s ^ 2) := by
    have hscalar := mul_le_mul_of_nonneg_right (hbox s hs).2 (sq_nonneg ‖y s‖)
    have helectric : 0 ≤ Q s ^ 2 / (2 * s ^ 2) := by positivity
    linarith only [hscalar, helectric]
  have hyint : IntervalIntegrable (fun s => ‖y s‖ ^ 2) volume r L :=
    (hy.norm.pow 2).intervalIntegrable_of_Icc hrL
  have hbound := intervalIntegral.integral_mono_on hrL (hyint.div_const 4)
    (hf.intervalIntegrable_of_Icc hrL) hpoint
  have hnormInt : (∫ s in r..L, ‖y s‖ ^ 2 / 4) = (∫ s in r..L, ‖y s‖ ^ 2) / 4 := by
    simp only [div_eq_mul_inv, intervalIntegral.integral_mul_const]
  rw [hnormInt, hi] at hbound
  have hmL := (hbox L ⟨hrL, le_rfl⟩).1.2
  have hmr := (hbox r ⟨le_rfl, hrL⟩).1.1
  linarith only [hbound, hmL, hmr]

/-- [internal]
The radial charge improvement applies to the actual normalized outgoing
section ending on the diagonal cylinder. The inverse radius chart is
constructed here, and its scalar energy is derived from the mass equation.
The fixed coefficients `K,B` precede every normalized field and all physical
data. The section may degenerate; no travel outside it is invoked. -/
theorem co_charge_improved_on_outgoing_of_normalization
    (K B : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Fields) (e eta L u v qStar : ℝ) (H : ℂ),
        v ≤ u → 0 < S.r u v → 1 ≤ L → S.r u u = L →
        |e| * L * (1 + ‖H‖) = eta →
        ContinuousOn (S.r u) (Icc v u) → ContinuousOn (S.lam u) (Icc v u) →
        ContinuousOn (S.phi u) (Icc v u) → ContinuousOn (S.theta u) (Icc v u) →
        ContinuousOn (S.Q u) (Icc v u) → ContinuousOn (S.m u) (Icc v u) →
        (∀ t ∈ Ioo v u, HasDerivAt (S.r u) (S.lam u t) t) →
        (∀ t ∈ Ioo v u, HasDerivAt (S.phi u) (S.phiV u t) t) →
        (∀ t ∈ Ioo v u, HasDerivAt (S.Q u) (S.QV e u t) t) →
        (∀ t ∈ Ioo v u, HasDerivAt (S.m u) (S.mV u t) t) →
        (∀ t ∈ Icc v u, 0 < S.lam u t ∧ S.m u t ∈ Icc 0 2 ∧
          1 / 2 ≤ 1 - S.mu u t) →
        (∀ t ∈ Icc v u, ‖shiftedRphi S H u t‖ ≤ K) →
        |S.Q u u - qStar| ≤ B * eta → |qStar| ≤ 1 → C * eta ≤ 1 →
        |S.Q u v - qStar| ≤ C * eta ∧ |S.Q u v| ≤ 2 := by
  obtain ⟨C, hC, hbound⟩ := co_charge_improved_of_normalization K B hK hB
  refine ⟨C, hC, ?_⟩
  intro S e eta L u v qStar H hvu hr hL hRL heta hcR hcl hcphi hct hcQ hcm
    hdR hdphi hdQ hdm hbox hpsi hboundary hq hsmall
  obtain ⟨inv, hmono, hci, hmem, hi, hleft, hright, hdi⟩ :=
    radial_section_inverse_of_normalization hvu hcR hdR
      (fun t ht => (hbox t (Ioo_subset_Icc_self ht)).1)
  simp only [hRL] at hi hright hdi
  have hrL : S.r u v ≤ L := by
    rw [← hRL]
    exact hmono.monotoneOn ⟨le_rfl, hvu⟩ ⟨hvu, le_rfl⟩ hvu
  let phi : ℝ → ℂ := fun s => S.phi u (inv s)
  let y : ℝ → ℂ := fun s => S.theta u (inv s) / (S.lam u (inv s) : ℂ)
  let Q : ℝ → ℝ := fun s => S.Q u (inv s)
  let m : ℝ → ℝ := fun s => S.m u (inv s)
  have hpc : ContinuousOn phi (Icc (S.r u v) L) :=
    hcphi.comp hci.continuousOn (fun t _ => hmem t)
  have hQc : ContinuousOn Q (Icc (S.r u v) L) :=
    hcQ.comp hci.continuousOn (fun t _ => hmem t)
  have hmc : ContinuousOn m (Icc (S.r u v) L) :=
    hcm.comp hci.continuousOn (fun t _ => hmem t)
  have hyl : ContinuousOn y (Icc (S.r u v) L) :=
    (hct.comp hci.continuousOn (fun t _ => hmem t)).div
      (Complex.continuous_ofReal.comp_continuousOn
        (hcl.comp hci.continuousOn (fun t _ => hmem t)))
      (fun t _ => Complex.ofReal_ne_zero.mpr (hbox (inv t) (hmem t)).1.ne')
  have hpd (s : ℝ) (hs : s ∈ Ioo (S.r u v) L) :
      HasDerivAt phi (y s / (s : ℂ)) s := by
    have hl := (hbox (inv s) (hmem s)).1.ne'
    convert (hdphi (inv s) (hdi s hs).1).scomp s (hdi s hs).2 using 1
    · rfl
    · dsimp only [Fields.phiV, y]
      rw [hi s ⟨hs.1.le, hs.2.le⟩]
      simp only [Complex.real_smul]
      push_cast
      field_simp
  have hQd (s : ℝ) (hs : s ∈ Ioo (S.r u v) L) :
      HasDerivAt Q (-e * (s * (starRingEnd ℂ (phi s) * y s).im)) s := by
    convert (hdQ (inv s) (hdi s hs).1).scomp s (hdi s hs).2 using 1
    · rfl
    · dsimp only [Fields.QV, phi, y]
      rw [hi s ⟨hs.1.le, hs.2.le⟩]
      simp only [smul_eq_mul, div_eq_mul_inv, ← mul_assoc, ← Complex.ofReal_inv,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero]
      ring
  have hmd (s : ℝ) (hs : s ∈ Ioo (S.r u v) L) :
      HasDerivAt m ((1 - 2 * m s / s) * ‖y s‖ ^ 2 / 2 + Q s ^ 2 / (2 * s ^ 2)) s := by
    have hl := (hbox (inv s) (hmem s)).1.ne'
    convert (hdm (inv s) (hdi s hs).1).scomp s (hdi s hs).2 using 1
    · rfl
    · dsimp only [Fields.mV, Fields.mu, m, Q, y]
      rw [hi s ⟨hs.1.le, hs.2.le⟩]
      simp only [smul_eq_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
        div_pow, sq_abs]
      field_simp
  have henergy := radial_scalar_energy_of_normalization hr hrL hmc hQc hyl hmd
    (fun s hs => ⟨(hbox (inv s) (hmem s)).2.1, by
      have h := (hbox (inv s) (hmem s)).2.2
      simpa only [Fields.mu, hi s hs, m] using h⟩)
  have hresult := hbound e eta (S.r u v) L qStar H phi y Q hr hrL hL heta
    hpc hyl hQc hpd hQd (fun s hs => by
      have h := hpsi (inv s) (hmem s)
      simpa only [shiftedRphi, hi s hs, phi] using h)
    henergy (by simpa only [Q, hright] using hboundary) hq hsmall
  simpa only [Q, hleft] using hresult

/-- [internal]
The rational geometric coefficient difference, with its mass and electric
parts separated exactly. The reference mass may be negative. -/
theorem geometric_coefficient_difference {mu muStar q qStar : ℝ}
    (hg : 1 - mu ≠ 0) (hgStar : 1 - muStar ≠ 0) :
    (mu - q) / (1 - mu) - (muStar - qStar) / (1 - muStar) =
      (mu - muStar) * (1 - qStar) / ((1 - mu) * (1 - muStar)) -
        (q - qStar) / (1 - mu) := by
  field_simp
  ring

/-- [internal]
The actual outer geometric coefficient has the universal bound `16/r`.
Only the normalized mass, charge and gap bounds are used. -/
theorem outer_geometric_coefficient_bound {r m Q : ℝ}
    (hr : 1 ≤ r) (hm : |m| ≤ 2) (hQ : |Q| ≤ 2)
    (hg : 1 / 2 ≤ 1 - 2 * m / r) :
    |(2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r)| ≤ 16 / r := by
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hgp : 0 < 1 - 2 * m / r := by linarith only [hg]
  have hm' : |2 * m / r| ≤ 4 / r := by
    rw [abs_div, abs_mul, abs_of_pos hrp]
    norm_num only [show |(2 : ℝ)| = 2 by norm_num]
    exact div_le_div_of_nonneg_right (by linarith only [hm]) hrp.le
  have hQ2 : Q ^ 2 ≤ 4 := by
    have := (sq_le_sq₀ (abs_nonneg Q) (by norm_num : (0 : ℝ) ≤ 2)).mpr hQ
    simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using this
  have hq' : |Q ^ 2 / r ^ 2| ≤ 4 / r := by
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    calc
      _ ≤ 4 / r ^ 2 := div_le_div_of_nonneg_right hQ2 (sq_nonneg r)
      _ ≤ 4 / r := div_le_div_of_nonneg_left (by norm_num) hrp
        (by nlinarith only [mul_nonneg hrp.le (sub_nonneg.mpr hr)])
  rw [abs_div, abs_of_pos hgp]
  apply (div_le_iff₀ hgp).mpr
  have hnum : |2 * m / r - Q ^ 2 / r ^ 2| ≤ 8 / r := by
    exact (abs_sub _ _).trans ((add_le_add hm' hq').trans_eq (by ring))
  have hden := mul_le_mul_of_nonneg_left hg (show 0 ≤ 16 / r by positivity)
  exact hnum.trans ((by ring : 8 / r = 16 / r * (1 / 2)).le.trans hden)

/-- [internal]
The exact rational coefficient difference has universal neutral coefficient
`16` and electric coefficient `6`. The latter multiplies the fixed prior
charge comparison coefficient `B`. All bounds are uniform in outer radius,
background scalar and coupling. -/
theorem outer_geometric_difference_bound {r m mStar Q qStar Nm B eta : ℝ}
    (hr : 1 ≤ r) (hg : 1 / 2 ≤ 1 - 2 * m / r)
    (hgStar : 1 / 2 ≤ 1 - 2 * mStar / r)
    (hm : |m - mStar| ≤ Nm) (hQ : |Q| ≤ 2) (hq : |qStar| ≤ 1)
    (hcharge : |Q - qStar| ≤ B * eta) :
    |(2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r) -
      (2 * mStar / r - qStar ^ 2 / r ^ 2) / (1 - 2 * mStar / r)| ≤
        16 * Nm / r + 6 * B * eta / r ^ 2 := by
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hgp : 0 < 1 - 2 * m / r := by linarith only [hg]
  have hgs : 0 < 1 - 2 * mStar / r := by linarith only [hgStar]
  have hNm : 0 ≤ Nm := (abs_nonneg _).trans hm
  have hBe : 0 ≤ B * eta := (abs_nonneg _).trans hcharge
  have hmu : |2 * m / r - 2 * mStar / r| ≤ 2 * Nm / r := by
    rw [show 2 * m / r - 2 * mStar / r = 2 * (m - mStar) / r by ring,
      abs_div, abs_mul, abs_of_pos hrp]
    norm_num only [show |(2 : ℝ)| = 2 by norm_num]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hm (by norm_num)) hrp.le
  have hq2 : qStar ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg qStar) zero_le_one).mpr hq
  have hqFrac : |1 - qStar ^ 2 / r ^ 2| ≤ 2 := by
    have hfrac : |qStar ^ 2 / r ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ qStar ^ 2 / r ^ 2)]
      apply (div_le_one (sq_pos_of_pos hrp)).mpr
      exact hq2.trans (by nlinarith only [mul_nonneg hrp.le (sub_nonneg.mpr hr), hr])
    exact (abs_sub _ _).trans (by norm_num only [abs_one]; linarith only [hfrac])
  have hcharge2 : |Q ^ 2 - qStar ^ 2| ≤ 3 * (B * eta) := by
    rw [show Q ^ 2 - qStar ^ 2 = (Q - qStar) * (Q + qStar) by ring, abs_mul]
    have hsum : |Q + qStar| ≤ 3 := (abs_add_le _ _).trans (by linarith only [hQ, hq])
    exact (mul_le_mul hcharge hsum (abs_nonneg _) hBe).trans_eq (by ring)
  have hqDiff : |Q ^ 2 / r ^ 2 - qStar ^ 2 / r ^ 2| ≤ 3 * (B * eta) / r ^ 2 := by
    rw [← sub_div, abs_div, abs_of_pos (sq_pos_of_pos hrp)]
    exact div_le_div_of_nonneg_right hcharge2 (sq_nonneg r)
  rw [geometric_coefficient_difference hgp.ne' hgs.ne']
  apply (abs_sub _ _).trans
  apply add_le_add
  · rw [abs_div, abs_mul, abs_of_pos (mul_pos hgp hgs)]
    apply (div_le_iff₀ (mul_pos hgp hgs)).mpr
    have hnum := mul_le_mul hmu hqFrac (abs_nonneg _) (by positivity : 0 ≤ 2 * Nm / r)
    have hden : 1 / 4 ≤ (1 - 2 * m / r) * (1 - 2 * mStar / r) := by
      have := mul_le_mul hg hgStar (by norm_num : (0 : ℝ) ≤ 1 / 2) hgp.le
      norm_num at this ⊢
      exact this
    have hprod := mul_le_mul_of_nonneg_left hden (show 0 ≤ 16 * Nm / r by positivity)
    exact hnum.trans ((by ring : 2 * Nm / r * 2 = 16 * Nm / r * (1 / 4)).le.trans hprod)
  · rw [abs_div, abs_of_pos hgp]
    apply (div_le_iff₀ hgp).mpr
    have hprod := mul_le_mul_of_nonneg_left hg (show 0 ≤ 6 * B * eta / r ^ 2 by
      simpa only [mul_assoc] using
        div_nonneg (mul_nonneg (show (0 : ℝ) ≤ 6 by norm_num) hBe) (sq_nonneg r))
    exact hqDiff.trans ((by ring : 3 * (B * eta) / r ^ 2 =
      6 * B * eta / r ^ 2 * (1 / 2)).le.trans hprod)

end EmcsfAcExtension.Global
