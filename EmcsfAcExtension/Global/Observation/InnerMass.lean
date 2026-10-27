module

public import Mathlib
import EmcsfAcExtension.Global.Terminal.Scalar
public import EmcsfAcExtension.Global.Observation.OuterMass
import EmcsfAcExtension.Infra.Null.IntegralForm
import EmcsfAcExtension.Infra.LinearTransport

/-! # Inner boundary trace and radial mass algebra

The boundary term is estimated in the clock measure, with its actual
interior weight. Source: charged_SF_new_version.tex:L2652–L2726; internal project record (I2).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

/-- [node prop:charged-observation#inner-L2-boundary-integral]
The retained incoming trace contributes at most `sqrt (d / 2) * eXi`.
Here `w = -nu` on the characteristic, its integral is the radial depth,
and `h` is the same-label boundary representative in the normalized
inner clock. The only trace input is its squared L² integral on the
full boundary window. All coefficients are exact and universal.
The interval and its boundary-containing window may be degenerate. -/
theorem Observation.inner_l2_boundary_integral
    {h : ℝ → ℂ} {w : ℝ → ℝ} {a b s t d eXi : ℝ}
    (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hh : ContinuousOn h (Icc a b)) (hw : ContinuousOn w (Icc s t))
    (hw0 : ∀ x ∈ Icc s t, 0 ≤ w x)
    (hwHalf : ∀ x ∈ Icc s t, w x ≤ 1 / 2)
    (hdepth : (∫ x in s..t, w x) = d) (heXi : 0 ≤ eXi)
    (htrace : (∫ x in a..b, ‖h x‖ ^ 2) ≤ eXi ^ 2) :
    (∫ x in s..t, w x * ‖h x‖) ≤ Real.sqrt (d / 2) * eXi := by
  have hab : a ≤ b := has.trans (hst.trans htb)
  have hh' := hh.mono (Icc_subset_Icc has htb)
  have hsqrt : ContinuousOn (fun x => Real.sqrt (w x)) (Icc s t) :=
    Real.continuous_sqrt.comp_continuousOn hw
  have hcs := Terminal.integral_cauchy_schwarz hst hsqrt (hsqrt.mul hh'.norm)
  change (∫ x in s..t, Real.sqrt (w x) * (Real.sqrt (w x) * ‖h x‖)) ^ 2 ≤
    (∫ x in s..t, Real.sqrt (w x) ^ 2) *
      (∫ x in s..t, (Real.sqrt (w x) * ‖h x‖) ^ 2) at hcs
  have hprod : (∫ x in s..t, Real.sqrt (w x) * (Real.sqrt (w x) * ‖h x‖)) =
      ∫ x in s..t, w x * ‖h x‖ := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hst] at hx
    change Real.sqrt (w x) * (Real.sqrt (w x) * ‖h x‖) = w x * ‖h x‖
    rw [← mul_assoc, ← sq, Real.sq_sqrt (hw0 x hx)]
  have hsq : (∫ x in s..t, Real.sqrt (w x) ^ 2) = d := by
    rw [← hdepth]
    exact intervalIntegral.integral_congr (fun x hx =>
      Real.sq_sqrt (hw0 x (by simpa only [uIcc_of_le hst] using hx)))
  have hsqprod : (∫ x in s..t, (Real.sqrt (w x) * ‖h x‖) ^ 2) =
      ∫ x in s..t, w x * ‖h x‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hst] at hx
    change (Real.sqrt (w x) * ‖h x‖) ^ 2 = w x * ‖h x‖ ^ 2
    rw [mul_pow, Real.sq_sqrt (hw0 x hx)]
  rw [hprod, hsq, hsqprod] at hcs
  have hdi : 0 ≤ d := by
    rw [← hdepth]
    exact intervalIntegral.integral_nonneg hst hw0
  have hi := (hh.norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hab
  have hsub := intervalIntegral.integral_mono_interval has hst htb
    ((ae_restrict_mem measurableSet_Ioc).mono fun x _ => sq_nonneg ‖h x‖) hi
  have hweighted := intervalIntegral.integral_mono_on hst
    ((hw.mul (hh'.norm.pow 2)).intervalIntegrable_of_Icc (μ := volume) hst)
    ((hh'.norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hst |>.const_mul (1 / 2 : ℝ))
    (fun x hx => mul_le_mul_of_nonneg_right (hwHalf x hx) (sq_nonneg ‖h x‖))
  rw [intervalIntegral.integral_const_mul] at hweighted
  simp only [Pi.mul_apply, Pi.pow_apply] at hweighted
  have hweighted' : (∫ x in s..t, w x * ‖h x‖ ^ 2) ≤ eXi ^ 2 / 2 := by
    linarith only [hweighted, hsub.trans htrace]
  have hbound := mul_le_mul_of_nonneg_left hweighted' hdi
  have hsquare : (Real.sqrt (d / 2) * eXi) ^ 2 = d * (eXi ^ 2 / 2) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ d / 2)]
    ring
  have hnonneg : 0 ≤ ∫ x in s..t, w x * ‖h x‖ :=
    intervalIntegral.integral_nonneg hst (fun x hx => mul_nonneg (hw0 x hx) (norm_nonneg _))
  apply (sq_le_sq₀ hnonneg (mul_nonneg (Real.sqrt_nonneg _) heXi)).mp
  rw [hsquare]
  exact hcs.trans hbound

/-- [internal]
Under the scalar stop, the inner mass source is linear in the outgoing
scalar error and the electric square error. The coefficients depend
only on the reference bounds `G,K`; no actual scalar supremum or
incoming scalar value occurs. -/
theorem Observation.inner_mass_source_bound
    {gStar electric G K eta : ℝ} {y yStar : ℂ}
    (hG : 0 ≤ G) (_hK : 0 ≤ K) (hg : |gStar| ≤ G)
    (hyStar : ‖yStar‖ ≤ K) (hstop : ‖y - yStar‖ ≤ 1)
    (helectric : |electric| ≤ eta) :
    |gStar * (starRingEnd ℂ yStar * (y - yStar)).re +
      gStar / 2 * ‖y - yStar‖ ^ 2 + electric| ≤
      G * (K + 1) * ‖y - yStar‖ + eta := by
  have hprod : |(starRingEnd ℂ yStar * (y - yStar)).re| ≤ K * ‖y - yStar‖ := by
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right hyStar (norm_nonneg _)
  have hlinear := mul_le_mul hg hprod (abs_nonneg _) hG
  have hquadratic : ‖y - yStar‖ ^ 2 ≤ ‖y - yStar‖ := by
    nlinarith only [mul_nonneg (norm_nonneg (y - yStar)) (sub_nonneg.mpr hstop)]
  have hquad := mul_le_mul_of_nonneg_right hg (sq_nonneg ‖y - yStar‖)
  calc
    _ ≤ |gStar * (starRingEnd ℂ yStar * (y - yStar)).re| +
        |gStar / 2 * ‖y - yStar‖ ^ 2| + |electric| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ G * (K * ‖y - yStar‖) + G / 2 * ‖y - yStar‖ ^ 2 + eta := by
      simp only [abs_mul, abs_div,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (sq_nonneg ‖y - yStar‖)]
      exact add_le_add (add_le_add hlinear (by linarith only [hquad])) helectric
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hquadratic hG
      have hn := mul_nonneg hG (norm_nonneg (y - yStar))
      nlinarith only [h, hn]

/-- [internal]
The positive backward mass factor is bounded on any fixed finite annulus
by its explicit coefficient bound. The constant depends only on `A,Lzero`,
uniformly in the radial coefficient and the selected member's depth. -/
theorem Observation.inner_backward_factor_bound
    {a : ℝ → ℝ} {r Lzero A : ℝ} (hr : 0 ≤ r) (_hrL : r ≤ Lzero)
    (hA : 0 ≤ A) (ha : ContinuousOn a (Icc r Lzero))
    (hbound : ∀ s ∈ Icc r Lzero, a s ≤ A) :
    ∀ s ∈ Icc r Lzero,
      Real.exp (∫ t in r..s, a t) ≤ Real.exp (A * Lzero) := by
  intro s hs
  have hsub : Icc r s ⊆ Icc r Lzero := Icc_subset_Icc le_rfl hs.2
  have hi := intervalIntegral.integral_mono_on hs.1
    ((ha.mono hsub).intervalIntegrable_of_Icc (μ := volume) hs.1)
    intervalIntegrable_const (fun t ht => hbound t (hsub ht))
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  exact Real.exp_le_exp.mpr (hi.trans (by nlinarith only [hs.2, hr, hA]))

/-- [internal]
Radial mass Volterra bound from the actual and reference mass equations.
The explicit exponential depends only on `rStar,Lzero,K,G,E`, uniformly
in the scalar background, coupling, fields and chosen radial endpoint.
The electric input is the electric square difference source obtained
from inner charge comparison. The scalar stop is used only here. -/
theorem Observation.inner_mass_volterra_on_ray_of_charge_bound
    {m mStar Q : ℝ → ℝ} {y yStar : ℝ → ℂ}
    {rStar Lzero r qStar K G E eta : ℝ}
    (hrStar : 0 < rStar) (hr : rStar ≤ r) (hrL : r ≤ Lzero)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hE : 0 ≤ E) (heta : 0 ≤ eta)
    (hm : ContinuousOn m (Icc r Lzero)) (hms : ContinuousOn mStar (Icc r Lzero))
    (hQ : ContinuousOn Q (Icc r Lzero))
    (hy : ContinuousOn y (Icc r Lzero)) (hys : ContinuousOn yStar (Icc r Lzero))
    (hdm : ∀ s ∈ Ioo r Lzero, HasDerivAt m
      ((1 - 2 * m s / s) * ‖y s‖ ^ 2 / 2 + Q s ^ 2 / (2 * s ^ 2)) s)
    (hdms : ∀ s ∈ Ioo r Lzero, HasDerivAt mStar
      ((1 - 2 * mStar s / s) * ‖yStar s‖ ^ 2 / 2 + qStar ^ 2 / (2 * s ^ 2)) s)
    (hbox : ∀ s ∈ Icc r Lzero,
      ‖yStar s‖ ≤ K ∧ ‖y s - yStar s‖ ≤ 1 ∧ |1 - 2 * mStar s / s| ≤ G ∧
      |(Q s ^ 2 - qStar ^ 2) / (2 * s ^ 2)| ≤ E * eta) :
    |m r - mStar r| ≤ Real.exp ((K + 1) ^ 2 / rStar * Lzero) *
      (|m Lzero - mStar Lzero| + E * eta * Lzero +
        G * (K + 1) * ∫ s in r..Lzero, ‖y s - yStar s‖) := by
  let D := fun s => m s - mStar s
  let a := fun s => ‖y s‖ ^ 2 / s
  let source := fun s =>
    (1 - 2 * mStar s / s) * (starRingEnd ℂ (yStar s) * (y s - yStar s)).re +
      (1 - 2 * mStar s / s) / 2 * ‖y s - yStar s‖ ^ 2 +
        (Q s ^ 2 - qStar ^ 2) / (2 * s ^ 2)
  have hpos (s : ℝ) (hs : s ∈ Icc r Lzero) : 0 < s := hrStar.trans_le (hr.trans hs.1)
  have ha : ContinuousOn a (Icc r Lzero) :=
    (hy.norm.pow 2).div continuousOn_id (fun s hs => (hpos s hs).ne')
  have hgap : ContinuousOn (fun s => 1 - 2 * mStar s / s) (Icc r Lzero) :=
    continuousOn_const.sub ((continuousOn_const.mul hms).div continuousOn_id
      (fun s hs => (hpos s hs).ne'))
  have hs : ContinuousOn source (Icc r Lzero) :=
    ((hgap.mul (Complex.continuous_re.comp_continuousOn
      (hys.star.mul (hy.sub hys)))).add
      ((hgap.div_const 2).mul ((hy.sub hys).norm.pow 2))).add
      (((hQ.pow 2).sub continuousOn_const).div
        (continuousOn_const.mul (continuousOn_id.pow 2))
        (fun s ht => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hpos s ht).ne')))
  have hd (s : ℝ) (hs : s ∈ Ioo r Lzero) :
      HasDerivAt D (-a s * D s + source s) s := by
    convert (hdm s hs).sub (hdms s hs) using 1
    dsimp only [D, a, source]
    linear_combination
      -(mass_difference_algebra s (m s) (mStar s) (Q s) qStar 1 (y s) (yStar s))
  have hderc : ContinuousOn (fun s => -a s * D s + source s) (Icc r Lzero) :=
    (ha.neg.mul (hm.sub hms)).add hs
  have hac : AbsolutelyContinuousOnInterval D r Lzero := by
    apply absolutelyContinuousOnInterval_of_integralForm_on
      (g := fun s => -a s * D s + source s) hrL
    intro s ht
    have hsub : Icc r s ⊆ Icc r Lzero := Icc_subset_Icc le_rfl ht.2
    have hi := (hderc.mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    exact ⟨hi, (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      ((hm.sub hms).mono hsub) (fun t ht' => hd t ⟨ht'.1, ht'.2.trans_le ht.2⟩) hi).symm⟩
  have hcoeff (s : ℝ) (hs : s ∈ Icc r Lzero) : a s ≤ (K + 1) ^ 2 / rStar := by
    have hybound : ‖y s‖ ≤ K + 1 := by
      have hn := norm_le_insert (yStar s) (y s)
      rw [norm_sub_rev] at hn
      linarith only [hn, (hbox s hs).1, (hbox s hs).2.1]
    exact (div_le_div_of_nonneg_right
      ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hybound) (hpos s hs).le).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) hrStar (hr.trans hs.1))
  have hfactor := Observation.inner_backward_factor_bound (hrStar.trans_le hr).le hrL
    (by positivity : 0 ≤ (K + 1) ^ 2 / rStar) ha hcoeff
  have heq : ∀ᵐ s ∂volume.restrict (Icc r Lzero), deriv D s = -a s * D s + source s := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun s ht => (hd s ht).deriv)
  have hback := backward_mass_abs_le hrL hac (ha.intervalIntegrable_of_Icc hrL)
    (hs.intervalIntegrable_of_Icc hrL) heq hfactor
  have hsource (s : ℝ) (hs : s ∈ Icc r Lzero) :
      |source s| ≤ G * (K + 1) * ‖y s - yStar s‖ + E * eta :=
    Observation.inner_mass_source_bound hG hK (hbox s hs).2.2.1
      (hbox s hs).1 (hbox s hs).2.1 (hbox s hs).2.2.2
  have hyInt : IntervalIntegrable (fun s => ‖y s - yStar s‖) volume r Lzero := by
    simpa only [Pi.sub_apply] using
      (hy.sub hys).norm.intervalIntegrable_of_Icc (μ := volume) hrL
  have hi := intervalIntegral.integral_mono_on hrL
    (hs.abs.intervalIntegrable_of_Icc (μ := volume) hrL)
    ((hyInt.const_mul (G * (K + 1))).add intervalIntegrable_const) hsource
  rw [intervalIntegral.integral_add (hyInt.const_mul (G * (K + 1)))
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hi
  have hel := mul_nonneg (mul_nonneg hE heta) (hrStar.trans_le hr).le
  apply hback.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  dsimp only [D]
  linarith only [hi, hel]

/-- [internal]
The outgoing comparison derivative is bounded uniformly after the
outer scalar stop is removed. The explicit bound depends only on the
prior neutral/electric coefficients `Cn,Ce`, before the radius, outer
scale, errors and scalar background. The logarithm keeps its finite
endpoint and is bounded through the outer logarithmic kernel lemma. -/
theorem Observation.outgoing_derivative_uniform_of_outer
    {wV : ℂ} {r L Cn Ce Nphi Nm epsilon eta : ℝ}
    (hr : 1 ≤ r) (hrL : r ≤ L) (hCn : 0 ≤ Cn) (hCe : 0 ≤ Ce)
    (hNp : 0 ≤ Nphi) (hNp1 : Nphi ≤ 1) (hNm : 0 ≤ Nm) (hNm4 : Nm ≤ 4)
    (hepsilon : epsilon ≤ 1) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hV : ‖wV‖ ≤ epsilon / (2 * L) + 8 * (Cn * (Nphi + Nm)) / r ^ 2 +
      8 * (Ce * eta) / r ^ 3 + 8 * (Ce * eta) / L * Real.log (L / r)) :
    ‖wV‖ ≤ 1 + 40 * Cn + 16 * Ce := by
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hL : 1 ≤ L := hr.trans hrL
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hb : epsilon / (2 * L) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * L)).mpr
    linarith only [hepsilon, hL]
  have hn : 8 * (Cn * (Nphi + Nm)) / r ^ 2 ≤ 40 * Cn := by
    apply (div_le_self (by positivity : 0 ≤ 8 * (Cn * (Nphi + Nm)))
      (one_le_pow₀ hr)).trans
    have hh := mul_le_mul_of_nonneg_left (show Nphi + Nm ≤ 5 by linarith only [hNp1, hNm4]) hCn
    linarith only [hh]
  have he : 8 * (Ce * eta) / r ^ 3 ≤ 8 * Ce := by
    apply (div_le_self (by positivity : 0 ≤ 8 * (Ce * eta)) (one_le_pow₀ hr)).trans
    have hh := mul_le_mul_of_nonneg_left heta1 hCe
    linarith only [hh]
  have hlog : Real.log (L / r) / L ≤ 1 :=
    (outer_log_div_bounds hrp hrL).1.trans (by
      simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one hr)
  have helog := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 8 * (Ce * eta) by positivity)
  have hh := mul_le_mul_of_nonneg_left heta1 hCe
  have helog' : 8 * (Ce * eta) / L * Real.log (L / r) ≤ 8 * (Ce * eta) := by
    convert helog using 1 <;> ring
  linarith only [hV, hb, hn, he, helog', hh]

/-- [internal]
The actual depth supremum of mass error obeys the inner Volterra bound.
Constants depend only on the fixed annulus and reference/source bounds
`rStar,Lzero,K,G,E`, before every field, selected depth and boundary error.
The scalar profile is the literal maximum on the same sideways
truncations. Its continuity and its pointwise envelope are proved here;
the mass feedback is removed by the exact backward factor. -/
theorem Observation.inner_mass_volterra_of_charge_bound
    (rStar Lzero K G E : ℝ) (hrStar : 0 < rStar) (hLzero : rStar ≤ Lzero)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hE : 0 ≤ E) :
    ∃ C > 0, ∀ (rho : ℝ) (S : Fields) (D : Set (ℝ × ℝ)) (yStar : ℝ → ℂ) (mStar : ℝ → ℝ)
      (a b qStar eta em d : ℝ),
    let R := sidewaysTruncation S D a b rho Lzero
    let Y := fun u v => S.theta u v / (S.lam u v : ℂ) - yStar (S.r u v)
    let F := fun d => sSup ((fun p : ℝ × ℝ => ‖Y p.1 p.2‖) ''
      sidewaysTruncation S D a b (Lzero - d) Lzero)
    let N := fun d => sSup ((fun p : ℝ × ℝ => ‖massComparison S mStar p.1 p.2‖) ''
      sidewaysTruncation S D a b (Lzero - d) Lzero)
    rStar ≤ rho → rho ≤ Lzero → 0 ≤ eta → 0 ≤ em → d ∈ Icc 0 (Lzero - rho) → IsCompact R →
    ContinuousOn (Function.uncurry S.r) R → ContinuousOn (Function.uncurry S.lam) R →
    ContinuousOn (Function.uncurry S.theta) R → ContinuousOn (Function.uncurry S.m) R →
    ContinuousOn (Function.uncurry S.Q) R →
    ContinuousOn yStar (Icc rho Lzero) → ContinuousOn mStar (Icc rho Lzero) →
    (∀ s ∈ Ioo rho Lzero, HasDerivAt mStar
      ((1 - 2 * mStar s / s) * ‖yStar s‖ ^ 2 / 2 + qStar ^ 2 / (2 * s ^ 2)) s) →
    (∃ p ∈ R, S.r p.1 p.2 = Lzero) →
    (∀ p ∈ R, sidewaysTriangle p.2 p.1 ⊆ R) →
    (∀ p ∈ R, HasDerivAt (fun u => S.r u p.2) (S.nu p.1 p.2) p.1) →
    (∀ p ∈ R, S.nu p.1 p.2 < 0) →
    (∀ p ∈ R, HasDerivAt (S.r p.1) (S.lam p.1 p.2) p.2 ∧
      HasDerivAt (S.m p.1) (S.mV p.1 p.2) p.2) →
    (∀ p ∈ R, 0 < S.lam p.1 p.2 ∧ ‖yStar (S.r p.1 p.2)‖ ≤ K ∧
      |1 - 2 * mStar (S.r p.1 p.2) / S.r p.1 p.2| ≤ G ∧
      |(S.Q p.1 p.2 ^ 2 - qStar ^ 2) / (2 * S.r p.1 p.2 ^ 2)| ≤ E * eta) →
    (∀ t, (t, t) ∈ R → S.r t t = Lzero ∧ |massComparison S mStar t t| ≤ em) →
    (∀ s ∈ Icc 0 d, F s ≤ 1) →
    N d ≤ C * em + C * eta + C * ∫ s in 0..d, F s := by
  let A := (K + 1) ^ 2 / rStar
  let B := G * (K + 1)
  let EE := Real.exp (A * Lzero)
  let C := EE * (1 + E * Lzero + B)
  have hLz : 0 < Lzero := hrStar.trans_le hLzero
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hEE : 0 < EE := Real.exp_pos _
  have hC : 0 < C := by dsimp [C]; positivity
  have hCE : EE ≤ C := by
    have hh := mul_nonneg hEE.le (add_nonneg (mul_nonneg hE hLz.le) hB)
    dsimp only [C]
    nlinarith only [hh]
  have hCEta : EE * E * Lzero ≤ C := by
    have hh := mul_nonneg hEE.le (add_nonneg zero_le_one hB)
    dsimp only [C]
    nlinarith only [hh]
  have hCY : EE * B ≤ C := by
    have hh := mul_nonneg hEE.le (add_nonneg zero_le_one (mul_nonneg hE hLz.le))
    dsimp only [C]
    nlinarith only [hh]
  refine ⟨C, hC, ?_⟩
  intro rho S D yStar mStar a b qStar eta em d
  dsimp only
  intro hrho _hrhoL heta hem hd hcompact cr cl ct cm cq cys cms hdms
    hbase htri hri hn hdo hbox hb hstop
  let R := sidewaysTruncation S D a b rho Lzero
  let Y := fun u v => S.theta u v / (S.lam u v : ℂ) - yStar (S.r u v)
  let F := fun d => sSup ((fun p : ℝ × ℝ => ‖Y p.1 p.2‖) ''
    sidewaysTruncation S D a b (Lzero - d) Lzero)
  have cY : ContinuousOn (Function.uncurry Y) R :=
    (ct.div (Complex.continuous_ofReal.comp_continuousOn cl)
      (fun p hp => Complex.ofReal_ne_zero.mpr (hbox p hp).1.ne')).sub
      (cys.comp cr (fun p hp => hp.2))
  have hmax := continuousOn_outer_radius_maximum hcompact cr cY hbase htri
    (fun p hp => (hb p.2 (htri p hp (sidewaysTriangle_incoming ⟨le_rfl, hp.1.2.2.1⟩))).1) hri hn
  have hF0 (s : ℝ) : 0 ≤ F s := Real.sSup_nonneg (by
    rintro _ ⟨p, hp, rfl⟩
    exact norm_nonneg _)
  have hF := hmax.1.mono (Icc_subset_Icc le_rfl hd.2)
  have hFI : 0 ≤ ∫ s in 0..d, F s :=
    intervalIntegral.integral_nonneg hd.1 (fun s _ => hF0 s)
  have hpoint (p) (hp : p ∈ sidewaysTruncation S D a b (Lzero - d) Lzero) :
      ‖massComparison S mStar p.1 p.2‖ ≤ C * em + C * eta + C * ∫ s in 0..d, F s := by
    have hpR : p ∈ R := sidewaysTruncation_mono_radius S D a b Lzero
      (by linarith only [hd.2]) hp
    have hpath := (sidewaysTruncation_paths (htri p hpR)).2
    have hsec {T : Type} [TopologicalSpace T] {f : ℝ → ℝ → T}
        (hc : ContinuousOn (Function.uncurry f) R) :=
      continuousOn_outgoing_of_subtriangle hc (htri p hpR)
    have hrp : 0 < S.r p.1 p.2 := hrStar.trans_le (hrho.trans hpR.2.1)
    obtain ⟨inv, hmono, ci, himem, hi, hleft, hright, hdi⟩ :=
      radial_section_inverse_of_normalization hp.1.2.2.1 (hsec cr)
        (fun s hs => (hdo (p.1, s) (hpath s (Ioo_subset_Icc_self hs))).1)
        (fun s hs => (hbox (p.1, s) (hpath s (Ioo_subset_Icc_self hs))).1)
    have hRL := (hb p.1 (hpath p.1 ⟨hp.1.2.2.1, le_rfl⟩)).1
    simp only [hRL] at hi hright hdi
    let y := fun s => S.theta p.1 (inv s) / (S.lam p.1 (inv s) : ℂ)
    let m := fun s => S.m p.1 (inv s)
    let Q := fun s => S.Q p.1 (inv s)
    have hrL : S.r p.1 p.2 ≤ Lzero := hpR.2.2
    have hrad (s : ℝ) (hs : s ∈ Icc (S.r p.1 p.2) Lzero) : s ∈ Icc rho Lzero :=
      ⟨hpR.2.1.trans hs.1, hs.2⟩
    have hmem (s : ℝ) : (p.1, inv s) ∈ R := hpath (inv s) (himem s)
    have cym : ContinuousOn y (Icc (S.r p.1 p.2) Lzero) :=
      ((hsec ct).comp ci.continuousOn (fun s _ => himem s)).div
        (Complex.continuous_ofReal.comp_continuousOn
          ((hsec cl).comp ci.continuousOn (fun s _ => himem s)))
        (fun s _ => Complex.ofReal_ne_zero.mpr (hbox (p.1, inv s) (hmem s)).1.ne')
    have cmm : ContinuousOn m (Icc (S.r p.1 p.2) Lzero) :=
      (hsec cm).comp ci.continuousOn (fun s _ => himem s)
    have cqm : ContinuousOn Q (Icc (S.r p.1 p.2) Lzero) :=
      (hsec cq).comp ci.continuousOn (fun s _ => himem s)
    have hdm (s : ℝ) (hs : s ∈ Ioo (S.r p.1 p.2) Lzero) : HasDerivAt m
        ((1 - 2 * m s / s) * ‖y s‖ ^ 2 / 2 + Q s ^ 2 / (2 * s ^ 2)) s := by
      have hl := (hbox (p.1, inv s) (hmem s)).1.ne'
      convert ((hdo (p.1, inv s) (hmem s)).2).scomp s (hdi s hs).2 using 1
      · rfl
      · dsimp only [m, y, Q, Fields.mV, Fields.mu]
        rw [hi s (Ioo_subset_Icc_self hs)]
        simp only [smul_eq_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
        field_simp
    have hprof (s : ℝ) (hs : s ∈ Icc (S.r p.1 p.2) Lzero) : ‖y s - yStar s‖ ≤ F (Lzero - s) := by
      have hdep : Lzero - s ∈ Icc 0 (Lzero - rho) :=
        ⟨sub_nonneg.mpr hs.2, sub_le_sub_left (hrad s hs).1 Lzero⟩
      have hpointMem : (p.1, inv s) ∈ sidewaysTruncation S D a b s Lzero :=
        ⟨(hmem s).1, by
          change s ≤ S.r p.1 (inv s) ∧ S.r p.1 (inv s) ≤ Lzero
          rw [hi s hs]
          exact ⟨le_rfl, hs.2⟩⟩
      have hnorm := norm_le_of_comparisonNorm_le (hF0 (Lzero - s))
        (show (p.1, inv s) ∈ sidewaysTruncation S D a b (Lzero - (Lzero - s)) Lzero by
          simpa only [sub_sub_cancel] using hpointMem)
        ((hmax.2.2 (Lzero - s) hdep).le)
      simpa only [Y, y, hi s hs] using hnorm
    have hboxRad (s : ℝ) (hs : s ∈ Icc (S.r p.1 p.2) Lzero) :
        ‖yStar s‖ ≤ K ∧ ‖y s - yStar s‖ ≤ 1 ∧ |1 - 2 * mStar s / s| ≤ G ∧
          |(Q s ^ 2 - qStar ^ 2) / (2 * s ^ 2)| ≤ E * eta := by
      have hbp := hbox (p.1, inv s) (hmem s)
      rw [hi s hs] at hbp
      refine ⟨hbp.2.1, (hprof s hs).trans (hstop (Lzero - s) ?_), hbp.2.2.1, hbp.2.2.2⟩
      exact ⟨sub_nonneg.mpr hs.2, by linarith only [hp.2.1, hs.1]⟩
    have hmass :=
      Observation.inner_mass_volterra_on_ray_of_charge_bound hrStar (hrho.trans hpR.2.1) hrL
      hK hG hE heta cmm (cms.mono (fun s hs => hrad s hs)) cqm cym
      (cys.mono (fun s hs => hrad s hs)) hdm
      (fun s hs => hdms s ⟨lt_of_le_of_lt hpR.2.1 hs.1, hs.2⟩) hboxRad
    have hsub : Icc (S.r p.1 p.2) Lzero ⊆ Icc rho Lzero := Icc_subset_Icc hpR.2.1 le_rfl
    have hFc : ContinuousOn (fun s => F (Lzero - s)) (Icc (S.r p.1 p.2) Lzero) :=
      hmax.1.comp (continuous_const.sub continuous_id).continuousOn
        (fun s hs => ⟨sub_nonneg.mpr hs.2, sub_le_sub_left (hsub hs).1 Lzero⟩)
    have hiY := intervalIntegral.integral_mono_on hrL
      ((cym.sub (cys.mono hsub)).norm.intervalIntegrable_of_Icc (μ := volume) hrL)
      (hFc.intervalIntegrable_of_Icc hrL) hprof
    rw [intervalIntegral.integral_comp_sub_left, sub_self] at hiY
    have hdepth : Lzero - S.r p.1 p.2 ≤ d := by linarith only [hp.2.1]
    have hiF := intervalIntegral.integral_mono_interval (show (0 : ℝ) ≤ 0 by rfl)
      (sub_nonneg.mpr hrL) hdepth (Filter.Eventually.of_forall hF0)
      (hF.intervalIntegrable_of_Icc (μ := volume) hd.1)
    have hyBound := hiY.trans hiF
    have hbnd := (hb p.1 (hpath p.1 ⟨hp.1.2.2.1, le_rfl⟩)).2
    simp only [m, hleft, hright, hRL, Real.norm_eq_abs, massComparison] at hmass hbnd ⊢
    have hyB := mul_le_mul_of_nonneg_left hyBound (mul_nonneg hEE.le hB)
    have hbd := mul_le_mul_of_nonneg_left hbnd hEE.le
    have hce := mul_le_mul_of_nonneg_right hCE hem
    have hct := mul_le_mul_of_nonneg_right hCEta heta
    have hcy := mul_le_mul_of_nonneg_right hCY hFI
    change |S.m p.1 p.2 - mStar (S.r p.1 p.2)| ≤ _
    change |S.m p.1 p.2 - mStar (S.r p.1 p.2)| ≤ EE *
      (|S.m p.1 p.1 - mStar Lzero| + E * eta * Lzero + B *
        ∫ s in (S.r p.1 p.2)..Lzero, ‖y s - yStar s‖) at hmass
    simp only [Pi.sub_apply] at hyB
    linarith only [hmass, hyB, hbd, hce, hct, hcy]
  exact Real.sSup_le (by rintro _ ⟨p, hp, rfl⟩; exact hpoint p hp)
    (by positivity)

/-- [internal]
Exact backward variation of constants for a complex unknown with real
linear coefficient. This uses only AC sections and an almost everywhere
equation. Its exponential factor is real and positive. -/
theorem Observation.backward_complex_solution
    {Z source : ℝ → ℂ} {a : ℝ → ℝ} {r L : ℝ}
    (hrL : r ≤ L) (hZ : AbsolutelyContinuousOnInterval Z r L)
    (ha : IntervalIntegrable a volume r L) (hs : IntervalIntegrable source volume r L)
    (heq : ∀ᵐ s ∂volume.restrict (Icc r L),
      deriv Z s = -(a s : ℂ) * Z s + source s) :
    Z r = (Real.exp (∫ s in r..L, a s) : ℂ) * Z L -
      ∫ s in r..L, (Real.exp (∫ t in r..s, a t) : ℂ) * source s := by
  let A := fun x => ∫ s in r..x, a s
  let w := fun x => (Real.exp (A x) : ℂ)
  have hA := ha.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hw : AbsolutelyContinuousOnInterval w r L := hA.exp.ofReal
  have hp := hw.mul_normed_ring hZ
  have hi : IntervalIntegrable (fun s => w s * source s) volume r L :=
    hs.continuousOn_mul hw.continuousOn
  have hd : ∀ᵐ s, s ∈ uIcc r L →
      HasDerivAt (fun x => w x * Z x) (w s * source s) s := by
    have heq' := (ae_restrict_iff' measurableSet_Icc).mp heq
    filter_upwards [ha.ae_hasDerivAt_integral, hZ.ae_differentiableAt_of_mem_uIcc, heq']
      with s hs hZs heqs hmem
    have hdw : HasDerivAt w ((Real.exp (A s) * a s : ℝ) : ℂ) s :=
      (hs hmem r left_mem_uIcc).exp.ofReal_comp
    have hprod := hdw.mul (hZs hmem).hasDerivAt
    rw [heqs (by rwa [uIcc_of_le hrL] at hmem)] at hprod
    convert hprod using 1
    dsimp only [w]
    push_cast
    ring
  have h := hp.integral_eq_sub_of_ae_hasDerivAt_complex hi hd
  simp only [w, A, intervalIntegral.integral_same, Real.exp_zero,
    Complex.ofReal_one, one_mul] at h
  linear_combination h

/-- [internal]
A uniform bound for the backward real factor controls complex transport.
The coefficient is exactly that factor bound, independently of the
boundary datum and source; the boundary label is unchanged. -/
theorem Observation.backward_complex_norm_le
    {Z source : ℝ → ℂ} {a : ℝ → ℝ} {r L E : ℝ}
    (hrL : r ≤ L) (hZ : AbsolutelyContinuousOnInterval Z r L)
    (ha : IntervalIntegrable a volume r L) (hs : IntervalIntegrable source volume r L)
    (heq : ∀ᵐ s ∂volume.restrict (Icc r L),
      deriv Z s = -(a s : ℂ) * Z s + source s)
    (hE : ∀ s ∈ Icc r L, Real.exp (∫ t in r..s, a t) ≤ E) :
    ‖Z r‖ ≤ E * (‖Z L‖ + ∫ s in r..L, ‖source s‖) := by
  have hA := ha.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hw := hA.exp.ofReal
  have hi : IntervalIntegrable
      (fun s => (Real.exp (∫ t in r..s, a t) : ℂ) * source s) volume r L :=
    hs.continuousOn_mul hw.continuousOn
  rw [Observation.backward_complex_solution hrL hZ ha hs heq]
  calc
    _ ≤ ‖(Real.exp (∫ s in r..L, a s) : ℂ) * Z L‖ +
        ‖∫ s in r..L, (Real.exp (∫ t in r..s, a t) : ℂ) * source s‖ := norm_sub_le _ _
    _ ≤ E * ‖Z L‖ + E * (∫ s in r..L, ‖source s‖) := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hE L ⟨hrL, le_rfl⟩) (norm_nonneg _)
      · apply (intervalIntegral.norm_integral_le_integral_norm hrL).trans
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_mono_on hrL hi.norm (hs.norm.const_mul E)
        intro s hs
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hE s hs) (norm_nonneg _)
    _ = _ := by ring

/-- [internal]
The electromagnetic reconstruction correction on the outer annulus.
Its coefficient depends only on the fixed shifted scalar and potential
bounds `K,Cp`, uniformly in the radius, outer scale, background and
coupling. The potential premise is the charged conclusion of the outer
potential theorem, and the scalar premise is its literal shifted field. -/
theorem Observation.incoming_connection_correction_of_outer
    {S : Fields} {H : ℂ} {e u v K Cp eta L : ℝ}
    (hK : 0 ≤ K) (hr : 1 ≤ S.r u v) (hL : 0 < L)
    (heta : 0 ≤ eta) (hCp : 0 ≤ Cp) (hnu : 1 / 8 ≤ |S.nu u v|)
    (hpsi : ‖shiftedRphi S H u v‖ ≤ K)
    (hpotential : |e * S.A u v| * (1 + ‖H‖) ≤ Cp * eta / (L * S.r u v)) :
    ‖I * e * S.A u v * S.r u v * S.phi u v / S.nu u v‖ ≤
      8 * (K + 1) * Cp * eta / L := by
  have hrp : 0 < S.r u v := zero_lt_one.trans_le hr
  have hnp : 0 < |S.nu u v| := (by norm_num : (0 : ℝ) < 1 / 8).trans_le hnu
  have hphi : ‖(S.r u v : ℂ) * S.phi u v‖ ≤
      (K + 1) * S.r u v * (1 + ‖H‖) := by
    calc
      _ = ‖shiftedRphi S H u v + (S.r u v : ℂ) * H‖ := by
        congr 1
        dsimp only [shiftedRphi]
        ring
      _ ≤ K + S.r u v * ‖H‖ := by
        apply (norm_add_le _ _).trans
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrp] using
          add_le_add hpsi (le_refl ‖(S.r u v : ℂ) * H‖)
      _ ≤ _ := by
        have hk := mul_le_mul_of_nonneg_left hr hK
        have hh := mul_nonneg (mul_nonneg hK hrp.le) (norm_nonneg H)
        nlinarith only [hk, hh, hrp.le]
  have hp := mul_le_mul_of_nonneg_left hpotential
    (show 0 ≤ (K + 1) * S.r u v by positivity)
  have hp' : |e * S.A u v| * ‖(S.r u v : ℂ) * S.phi u v‖ ≤
      (K + 1) * Cp * eta / L := by
    calc
      _ ≤ |e * S.A u v| * ((K + 1) * S.r u v * (1 + ‖H‖)) :=
        mul_le_mul_of_nonneg_left hphi (abs_nonneg _)
      _ ≤ ((K + 1) * S.r u v) * (Cp * eta / (L * S.r u v)) := by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hp
      _ = _ := by field_simp
  have hn := mul_le_mul_of_nonneg_left hnu
    (show 0 ≤ 8 * ((K + 1) * Cp * eta / L) by positivity)
  have hnorm : ‖I * e * S.A u v * S.r u v * S.phi u v / S.nu u v‖ =
      |e * S.A u v| * ‖(S.r u v : ℂ) * S.phi u v‖ / |S.nu u v| := by
    simp only [norm_div, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul,
      abs_mul, mul_assoc]
  rw [hnorm]
  apply (div_le_iff₀ hnp).mpr
  calc
    _ ≤ (K + 1) * Cp * eta / L := hp'
    _ ≤ (8 * (K + 1) * Cp * eta / L) * |S.nu u v| := by
      convert hn using 1 <;> ring

end EmcsfAcExtension.Global
