module

public import EmcsfAcExtension.Global.Observation.OuterScalar
public import EmcsfAcExtension.Frozen.Fields.MassV
public import EmcsfAcExtension.Infra.AC.Intervals
import EmcsfAcExtension.Infra.Gronwall

/-! # The outer mass difference

The exact negative linear coefficient is retained before integrating
backward. The five scalar kernels yield the outer mass polynomial with
neutral constants chosen before boundary and electric constants. Source:
`charged_SF_new_version.tex:L2497–L2531`, approved internal project record (M).
-/

public section

open Set MeasureTheory Complex Filter

namespace EmcsfAcExtension.Global

/-- [internal]
The exact complex quadratic expansion needed in the mass subtraction. -/
theorem scalar_norm_sq_difference (y yStar : ℂ) :
    ‖y‖ ^ 2 - ‖yStar‖ ^ 2 =
      2 * (starRingEnd ℂ yStar * (y - yStar)).re + ‖y - yStar‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- [internal]
Pointwise mass subtraction with the feedback coefficient kept exact.
No positivity of the reference mass is required. -/
theorem mass_difference_algebra (r m mStar Q qStar lam : ℝ) (y yStar : ℂ) :
    lam * ((1 - 2 * m / r) * ‖y‖ ^ 2 / 2 + Q ^ 2 / (2 * r ^ 2)) -
      lam * ((1 - 2 * mStar / r) * ‖yStar‖ ^ 2 / 2 + qStar ^ 2 / (2 * r ^ 2)) =
    -(lam / r) * ‖y‖ ^ 2 * (m - mStar) +
      lam * (Q ^ 2 - qStar ^ 2) / (2 * r ^ 2) +
      lam * (1 - 2 * mStar / r) * (starRingEnd ℂ yStar * (y - yStar)).re +
      lam * (1 - 2 * mStar / r) / 2 * ‖y - yStar‖ ^ 2 := by
  linear_combination lam * (1 - 2 * mStar / r) / 2 * scalar_norm_sq_difference y yStar

/-- [internal]
The outgoing derivative of the literal mass comparison. Normalization
supplies the actual outgoing radius and mass equations; the static packet
supplies its radial mass equation. No constants or smallness assumptions
occur, and the reference mass may be negative. -/
theorem co_mass_difference_of_normalization
    {S : Fields} {u v qStar : ℝ} (mStar : ℝ → ℝ) (yStar : ℝ → ℂ)
    (hr : S.r u v ≠ 0) (hlam : S.lam u v ≠ 0)
    (hR : HasDerivAt (S.r u) (S.lam u v) v)
    (hM : HasDerivAt (S.m u) (S.mV u v) v)
    (hstatic : HasDerivAt mStar
      ((1 - 2 * mStar (S.r u v) / S.r u v) * ‖yStar (S.r u v)‖ ^ 2 / 2 +
        qStar ^ 2 / (2 * S.r u v ^ 2)) (S.r u v)) :
    let y := S.theta u v / (S.lam u v : ℂ)
    let Y := y - yStar (S.r u v)
    HasDerivAt (massComparison S mStar u)
      (-(S.lam u v / S.r u v) * ‖y‖ ^ 2 * massComparison S mStar u v +
        S.lam u v * (S.Q u v ^ 2 - qStar ^ 2) / (2 * S.r u v ^ 2) +
        S.lam u v * (1 - 2 * mStar (S.r u v) / S.r u v) *
          (starRingEnd ℂ (yStar (S.r u v)) * Y).re +
        S.lam u v * (1 - 2 * mStar (S.r u v) / S.r u v) / 2 * ‖Y‖ ^ 2) v := by
  have hmV : S.mV u v = S.lam u v *
      ((1 - 2 * S.m u v / S.r u v) *
        ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 / 2 +
        S.Q u v ^ 2 / (2 * S.r u v ^ 2)) := by
    simp only [Fields.mV, Fields.mu, norm_div, Complex.norm_real,
      Real.norm_eq_abs, div_pow, sq_abs]
    field_simp
  convert hM.sub (hstatic.scomp v hR) using 1
  · rfl
  · rw [hmV]
    simpa only [massComparison, smul_eq_mul] using
      (mass_difference_algebra (S.r u v) (S.m u v) (mStar (S.r u v))
        (S.Q u v) qStar (S.lam u v)
        (S.theta u v / (S.lam u v : ℂ)) (yStar (S.r u v))).symm

/-- [internal]
Every backward mass integrating factor is bounded by `exp (8/r)` from
the radial scalar energy alone. The numerical coefficient is universal;
no profile, outer radius or scalar background enters it. -/
theorem Observation.backward_mass_integrating_factor_of_normalization
    {y : ℝ → ℂ} {r L : ℝ} (hr : 0 < r) (hrL : r ≤ L)
    (hy : ContinuousOn y (Icc r L))
    (henergy : (∫ s in r..L, ‖y s‖ ^ 2) ≤ 8) :
    ∀ s ∈ Icc r L,
      Real.exp (∫ t in r..s, ‖y t‖ ^ 2 / t) ≤ Real.exp (8 / r) := by
  have hc : ContinuousOn (fun s => ‖y s‖ ^ 2 / s) (Icc r L) :=
    (hy.norm.pow 2).div continuousOn_id (fun s hs => (hr.trans_le hs.1).ne')
  have hi : IntervalIntegrable (fun s => ‖y s‖ ^ 2 / s) volume r L :=
    hc.intervalIntegrable_of_Icc hrL
  have hyi : IntervalIntegrable (fun s => ‖y s‖ ^ 2) volume r L :=
    (hy.norm.pow 2).intervalIntegrable_of_Icc hrL
  have hpoint (s : ℝ) (hs : s ∈ Icc r L) : ‖y s‖ ^ 2 / s ≤ ‖y s‖ ^ 2 / r :=
    div_le_div_of_nonneg_left (sq_nonneg _) hr hs.1
  have htotal : (∫ s in r..L, ‖y s‖ ^ 2 / s) ≤ 8 / r := by
    calc
      _ ≤ ∫ s in r..L, ‖y s‖ ^ 2 / r :=
        intervalIntegral.integral_mono_on hrL hi (hyi.div_const r) hpoint
      _ = (∫ s in r..L, ‖y s‖ ^ 2) / r := by
        simp only [div_eq_mul_inv, intervalIntegral.integral_mul_const]
      _ ≤ 8 / r := div_le_div_of_nonneg_right henergy hr.le
  intro s hs
  apply Real.exp_le_exp.mpr
  apply le_trans ?_ htotal
  exact intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall
      (fun t ht => div_nonneg (sq_nonneg _) (hr.le.trans ht.1.le)))) hi

/-- [internal]
The electric mass error is integrable with the universal coefficient `3`,
chosen before all charge profiles, radii and error sizes. The hypotheses
are exactly the prior charge comparison and its uniform charge bounds.
The lower radius is positive, and the interval may degenerate. -/
theorem co_electric_mass_error :
    ∃ C : ℝ, 0 < C ∧ ∀ (r L B eta qStar : ℝ) (Q : ℝ → ℝ),
      0 < r → r ≤ L → 0 ≤ B → 0 ≤ eta → |qStar| ≤ 1 →
      ContinuousOn Q (Icc r L) →
      (∀ s ∈ Icc r L, |Q s| ≤ 2 ∧ |Q s - qStar| ≤ B * eta) →
      (∫ s in r..L, |Q s ^ 2 - qStar ^ 2| / s ^ 2) ≤ C * B * eta / r := by
  refine ⟨3, by norm_num, ?_⟩
  intro r L B eta qStar Q hr hrL hB heta hq hc hQ
  have hpos (s : ℝ) (hs : s ∈ Icc r L) : 0 < s := hr.trans_le hs.1
  have hf : IntervalIntegrable (fun s => |Q s ^ 2 - qStar ^ 2| / s ^ 2) volume r L :=
    (((hc.pow 2).sub continuousOn_const).abs.div (continuousOn_id.pow 2)
      (fun s hs => pow_ne_zero 2 (hpos s hs).ne')).intervalIntegrable_of_Icc hrL
  have hk : IntervalIntegrable (fun s : ℝ => (3 * B * eta) * (1 / s ^ 2)) volume r L :=
    (continuousOn_const.mul (continuousOn_const.div (continuousOn_id.pow 2)
      (fun s hs => pow_ne_zero 2 (hpos s hs).ne'))).intervalIntegrable_of_Icc hrL
  calc
    _ ≤ ∫ s in r..L, (3 * B * eta) * (1 / s ^ 2) := by
      apply intervalIntegral.integral_mono_on hrL hf hk
      intro s hs
      have hsum : |Q s + qStar| ≤ 3 :=
        (abs_add_le _ _).trans (by linarith only [(hQ s hs).1, hq])
      have hdiff : |Q s ^ 2 - qStar ^ 2| ≤ 3 * B * eta := by
        rw [show Q s ^ 2 - qStar ^ 2 = (Q s - qStar) * (Q s + qStar) by ring, abs_mul]
        exact (mul_le_mul (hQ s hs).2 hsum (abs_nonneg _) (by positivity)).trans_eq (by ring)
      simpa only [mul_one_div] using div_le_div_of_nonneg_right hdiff (sq_nonneg s)
    _ = (3 * B * eta) * (1 / r - 1 / L) := by
      rw [intervalIntegral.integral_const_mul, integral_inv_sq_outer hr hrL]
    _ ≤ 3 * B * eta / r := by
      have hL : 0 < L := hr.trans_le hrL
      have hnonneg : 0 ≤ 3 * B * eta := by positivity
      calc
        _ ≤ (3 * B * eta) * (1 / r) :=
          mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) hnonneg
        _ = _ := by ring


/-- [internal] Exact backward solution of real AC transport. -/
theorem backward_mass_solution {D a F : ℝ → ℝ} {r L : ℝ}
    (hrL : r ≤ L) (hD : AbsolutelyContinuousOnInterval D r L)
    (ha : IntervalIntegrable a volume r L) (_hF : IntervalIntegrable F volume r L)
    (heq : ∀ᵐ s ∂volume.restrict (Icc r L), deriv D s = -a s * D s + F s) :
    D r = Real.exp (∫ s in r..L, a s) * D L -
      ∫ s in r..L, Real.exp (∫ t in r..s, a t) * F s := by
  let A := fun x => ∫ s in r..x, a s
  let w := fun x => Real.exp (A x)
  have hA := ha.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hw : AbsolutelyContinuousOnInterval w r L := hA.exp
  have hp := hw.mul_normed_ring hD
  have hd : ∀ᵐ s, s ∈ uIcc r L →
      HasDerivAt (fun x => w x * D x) (w s * F s) s := by
    have heq' := (ae_restrict_iff' measurableSet_Icc).mp heq
    filter_upwards [ha.ae_hasDerivAt_integral, hD.ae_differentiableAt, heq']
      with s hs hDs heqs hmem
    have hdw : HasDerivAt w (w s * a s) s := (hs hmem r left_mem_uIcc).exp
    have hprod := hdw.mul (hDs hmem).hasDerivAt
    rw [heqs (by rwa [uIcc_of_le hrL] at hmem)] at hprod
    convert hprod using 1
    ring
  have h := hp.integral_eq_sub_of_ae_hasDerivAt_real hd
  simp only [w, A, intervalIntegral.integral_same, Real.exp_zero, one_mul] at h
  linarith only [h]

/-- [internal] A uniform upper bound for the positive backward factor bounds the solution. -/
theorem backward_mass_abs_le {D a F : ℝ → ℝ} {r L E : ℝ}
    (hrL : r ≤ L) (hD : AbsolutelyContinuousOnInterval D r L)
    (ha : IntervalIntegrable a volume r L) (hF : IntervalIntegrable F volume r L)
    (heq : ∀ᵐ s ∂volume.restrict (Icc r L), deriv D s = -a s * D s + F s)
    (hE : ∀ s ∈ Icc r L, Real.exp (∫ t in r..s, a t) ≤ E) :
    |D r| ≤ E * (|D L| + ∫ s in r..L, |F s|) := by
  have hA := ha.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hw := hA.exp
  have hwi : IntervalIntegrable (fun s => Real.exp (∫ t in r..s, a t) * F s)
      volume r L := hF.continuousOn_mul hw.continuousOn
  rw [backward_mass_solution hrL hD ha hF heq]
  calc
    _ ≤ |Real.exp (∫ s in r..L, a s) * D L| +
        |∫ s in r..L, Real.exp (∫ t in r..s, a t) * F s| :=
            by simpa only [Real.norm_eq_abs] using norm_sub_le (Real.exp (∫ s in r..L, a s) * D L)
                 (∫ s in r..L, Real.exp (∫ t in r..s, a t) * F s)
    _ ≤ E * |D L| + E * (∫ s in r..L, |F s|) := by
      apply add_le_add
      · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hE L ⟨hrL, le_rfl⟩) (abs_nonneg _)
      · apply (intervalIntegral.abs_integral_le_integral_abs hrL).trans
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_mono_on hrL hwi.abs (hF.abs.const_mul E)
        intro s hs
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hE s hs) (abs_nonneg _)
    _ = _ := by ring

/-- [internal] The logarithm and its square divided by the outer radius are uniform. -/
theorem outer_log_div_bounds {r L : ℝ} (hr : 0 < r) (hrL : r ≤ L) :
    Real.log (L / r) / L ≤ 1 / r ∧
      Real.log (L / r) ^ 2 / L ≤ 4 / r := by
  have hL := hr.trans_le hrL
  have hx : 0 ≤ L / r := by positivity
  have hl : 0 ≤ Real.log (L / r) := Real.log_nonneg ((one_le_div hr).mpr hrL)
  have hs : Real.log (L / r) ≤ 2 * Real.sqrt (L / r) := by
    have h := Real.log_le_self (Real.sqrt_nonneg (L / r))
    rw [Real.log_sqrt hx] at h
    linarith only [h]
  have hsq : Real.log (L / r) ^ 2 ≤ 4 * (L / r) := by
    have h := (sq_le_sq₀ hl (by positivity : 0 ≤ 2 * Real.sqrt (L / r))).mpr hs
    nlinarith only [h, Real.sq_sqrt hx]
  constructor
  · exact (div_le_div_of_nonneg_right (Real.log_le_self hx) hL.le).trans_eq (by field_simp)
  · exact (div_le_div_of_nonneg_right hsq hL.le).trans_eq (by field_simp)

/-- [internal] Primitive of the electric logarithm divided by radius. -/
theorem integral_outer_log_div {r L : ℝ} (hr : 0 < r) (hrL : r ≤ L) :
    (∫ s in r..L, Real.log (L / s) / s) = Real.log (L / r) ^ 2 / 2 := by
  have hL := hr.trans_le hrL
  have hs (s : ℝ) (hs : s ∈ Icc r L) : 0 < s := hr.trans_le hs.1
  have hc : ContinuousOn (fun s => Real.log (L / s) / s) (Icc r L) :=
    ((continuousOn_const.div continuousOn_id (fun s h => (hs s h).ne')).log
      (fun s h => (div_pos hL (hs s h)).ne')).div continuousOn_id
        (fun s h => (hs s h).ne')
  have hd (s : ℝ) (h : s ∈ uIcc r L) :
      HasDerivAt (fun t => -(Real.log (L / t) ^ 2 / 2)) (Real.log (L / s) / s) s := by
    have hsp := hs s (by simpa only [uIcc_of_le hrL] using h)
    have hld : HasDerivAt (fun t => Real.log (L / t)) (-1 / s) s := by
      convert ((hasDerivAt_const s L).div (hasDerivAt_id s) hsp.ne').log
        (div_ne_zero hL.ne' hsp.ne') using 1
      · rfl
      · dsimp only [Pi.div_apply, id_eq]
        field_simp
        ring
    convert ((hld.fun_pow 2).div_const 2).neg using 1
    norm_num
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable_of_Icc hrL : IntervalIntegrable _ volume r L)
  simpa only [div_self hL.ne', Real.log_one, zero_pow (by decide : 2 ≠ 0), zero_div,
    neg_zero, zero_sub, neg_neg] using hi

/-- [internal] Square logarithmic radial kernel, with universal coefficient two. -/
theorem integral_outer_log_sq_le {r L : ℝ} (hr : 0 < r) (hrL : r ≤ L) :
    (∫ s in r..L, Real.log (L / s) ^ 2) ≤ 2 * L := by
  have hL := hr.trans_le hrL
  have hs (s : ℝ) (hs : s ∈ Icc r L) : 0 < s := hr.trans_le hs.1
  have hc : ContinuousOn (fun s => Real.log (L / s) ^ 2) (Icc r L) :=
    ((continuousOn_const.div continuousOn_id (fun s h => (hs s h).ne')).log
      (fun s h => (div_pos hL (hs s h)).ne')).pow 2
  have hd (s : ℝ) (h : s ∈ uIcc r L) :
      HasDerivAt (fun t => t * (Real.log (L / t) ^ 2 + 2 * Real.log (L / t) + 2))
        (Real.log (L / s) ^ 2) s := by
    have hsp := hs s (by simpa only [uIcc_of_le hrL] using h)
    have hld : HasDerivAt (fun t => Real.log (L / t)) (-1 / s) s := by
      convert ((hasDerivAt_const s L).div (hasDerivAt_id s) hsp.ne').log
        (div_ne_zero hL.ne' hsp.ne') using 1
      · rfl
      · dsimp only [Pi.div_apply, id_eq]
        field_simp
        ring
    convert (hasDerivAt_id s).mul (((hld.fun_pow 2).add (hld.const_mul 2)).add_const 2)
      using 1
    · rfl
    · dsimp only [Pi.add_apply, id_eq]
      norm_num
      field_simp
      ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable_of_Icc hrL : IntervalIntegrable _ volume r L)
  have hl : 0 ≤ Real.log (L / r) := Real.log_nonneg ((one_le_div hr).mpr hrL)
  simp only [div_self hL.ne', Real.log_one, zero_pow (by decide : 2 ≠ 0),
    mul_zero, zero_add] at hi
  nlinarith only [hi, mul_nonneg hr.le (sq_nonneg (Real.log (L / r))), mul_nonneg hr.le hl, hr.le]

/-- [internal] The five-term scalar expansion has a universal quadratic bound. -/
theorem sum_five_sq_le (a b c d e : ℝ) :
    (a+b+c+d+e)^2 ≤ 5*(a^2+b^2+c^2+d^2+e^2) := by
  linarith only [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (a-d), sq_nonneg (a-e),
    sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (b-e), sq_nonneg (c-d),
    sq_nonneg (c-e), sq_nonneg (d-e)]

/-- [internal]
The exact five scalar kernels give separate linear and quadratic mass costs.
All numerical coefficients are universal, uniformly in the interval and amplitudes. -/
theorem outer_scalar_mass_kernels {Y : ℝ → ℂ} {r L b p m e : ℝ}
    (hr : 1 ≤ r) (hrL : r ≤ L) (hb : 0 ≤ b) (hp : 0 ≤ p) (hm : 0 ≤ m) (he : 0 ≤ e)
    (hY : ContinuousOn Y (Icc r L))
    (hbound : ∀ s ∈ Icc r L,
      ‖Y s‖ ≤ b / L + p / s + m / s ^ 2 + e / s ^ 3 + e / L * Real.log (L / s)) :
    (∫ s in r..L, ‖Y s‖ / s) ≤ (b + p + 3 * e) / r + m / r ^ 2 ∧
    (∫ s in r..L, ‖Y s‖ ^ 2) ≤ 5 * (b ^ 2 + p ^ 2 + 3 * e ^ 2) / r + 5 * m ^ 2 / r ^ 3 := by
  have hrp : 0 < r := by linarith
  have hL : 0 < L := hrp.trans_le hrL
  have hs (s : ℝ) (h : s ∈ Icc r L) : 0 < s := hrp.trans_le h.1
  have hpow (n : ℕ) : IntervalIntegrable (fun s : ℝ => 1/s^n) volume r L :=
    (continuousOn_const.div (continuousOn_id.pow n)
      (fun s h => pow_ne_zero n (hs s h).ne')).intervalIntegrable_of_Icc hrL
  have hi1 : IntervalIntegrable (fun s : ℝ => 1/s) volume r L := by simpa using hpow 1
  have hlog : ContinuousOn (fun s => Real.log (L/s)) (Icc r L) :=
    (continuousOn_const.div continuousOn_id (fun s h => (hs s h).ne')).log
      (fun s h => (div_pos hL (hs s h)).ne')
  have hl : ∀ s ∈ Icc r L, 0 ≤ Real.log (L/s) :=
    fun s h => Real.log_nonneg ((one_le_div (hs s h)).mpr h.2)
  have hcoarse (s : ℝ) (h : s ∈ Icc r L) :
      ‖Y s‖ ≤ b/L+p/s+m/s^2+e/s+e/L*Real.log (L/s) := by
    have hs1 : 1 ≤ s := hr.trans h.1
    have hs3 : s ≤ s^3 := by
      have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hs1 (n := 2)) (hs s h).le
      nlinarith only [hh]
    linarith only [hbound s h, div_le_div_of_nonneg_left he (hs s h) hs3]
  have hiLog : IntervalIntegrable (fun s => Real.log (L/s)/s) volume r L := (hlog.div
      continuousOn_id (fun s h => (hs s h).ne')).intervalIntegrable_of_Icc hrL
  have hiSq : IntervalIntegrable (fun s => Real.log (L/s)^2) volume r L := (hlog.pow
      2).intervalIntegrable_of_Icc hrL
  have hi2 := hpow 2
  have hi3 := hpow 3
  have hi4 := hpow 4
  have hiY : IntervalIntegrable (fun s => ‖Y s‖/s) volume r L := (hY.norm.div continuousOn_id (fun s
      h => (hs s h).ne')).intervalIntegrable_of_Icc hrL
  have h1 := hi1.const_mul (b/L)
  have h2 := hi2.const_mul (p+e)
  have h3 := hi3.const_mul m
  have h4 := hiLog.const_mul (e/L)
  have hlin := ((h1.add h2).add h3).add h4
  have j0 : IntervalIntegrable (fun _ : ℝ => b^2/L^2) volume r L := intervalIntegrable_const
  have j1 := hi2.const_mul (p^2)
  have j2 := hi4.const_mul (m^2)
  have j3 := hi2.const_mul (e^2)
  have j4 := hiSq.const_mul ((e/L)^2)
  have hsq := (((j0.add j1).add j2).add j3).add j4
  have hinv2 : (∫ s in r..L, 1/s^2) ≤ 1/r := by
    rw [integral_inv_sq_outer hrp hrL]
    exact sub_le_self _ (by positivity)
  have hinv3 : (∫ s in r..L, 1/s^3) ≤ 1/r^2 := by
    rw [integral_inv_cube_outer hrp hrL]
    have hh : 1/(2*r^2) ≤ 1/r^2 :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg r])
    exact (sub_le_self _ (by positivity)).trans hh
  have hinv4 : (∫ s in r..L, 1/s^4) ≤ 1/r^3 := by
    rw [integral_inv_four_outer hrp hrL]
    have hh : 1/(3*r^3) ≤ 1/r^3 :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [pow_pos hrp 3])
    exact (sub_le_self _ (by positivity)).trans hh
  have hlogb := outer_log_div_bounds hrp hrL
  constructor
  · calc
      _ ≤ ∫ s in r..L, (b/L)*(1/s)+(p+e)*(1/s^2)+m*(1/s^3)+(e/L)*(Real.log (L/s)/s) := by
        apply intervalIntegral.integral_mono_on hrL hiY hlin
        intro s h
        convert div_le_div_of_nonneg_right (hcoarse s h) (hs s h).le using 1
        ring
      _ = b*(Real.log (L/r)/L)+(p+e)*(∫ s in r..L, 1/s^2)+
          m*(∫ s in r..L, 1/s^3)+e/2*(Real.log (L/r)^2/L) := by
        rw [intervalIntegral.integral_add ((h1.add h2).add h3) h4,
          intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          integral_one_div_of_pos hrp hL, integral_outer_log_div hrp hrL]
        ring
      _ ≤ b*(1/r)+(p+e)*(1/r)+m*(1/r^2)+e/2*(4/r) := by
        exact add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left hlogb.1 hb)
          (mul_le_mul_of_nonneg_left hinv2 (by positivity)))
          (mul_le_mul_of_nonneg_left hinv3 hm))
          (mul_le_mul_of_nonneg_left hlogb.2 (by positivity))
      _ = _ := by ring
  · calc
      _ ≤ 5 * (∫ s in r..L, b^2/L^2+p^2*(1/s^2)+m^2*(1/s^4)+e^2*(1/s^2)+
          (e/L)^2*Real.log (L/s)^2) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_mono_on hrL
          ((hY.norm.pow 2).intervalIntegrable_of_Icc hrL) (hsq.const_mul 5)
        intro s h
        have hc := hcoarse s h
        have hnonneg : 0 ≤ b/L+p/s+m/s^2+e/s+e/L*Real.log (L/s) := by
          have := hl s h
          have := hs s h
          positivity
        have hh := (sq_le_sq₀ (norm_nonneg _) hnonneg).mpr hc
        have hfive := sum_five_sq_le (b/L) (p/s) (m/s^2) (e/s) (e/L*Real.log (L/s))
        convert hh.trans hfive using 1
        simp only [div_pow, mul_pow]
        ring
      _ = 5 * ((L-r)*(b^2/L^2)+p^2*(∫ s in r..L, 1/s^2)+m^2*(∫ s in r..L, 1/s^4)+
          e^2*(∫ s in r..L, 1/s^2)+(e/L)^2*(∫ s in r..L, Real.log (L/s)^2)) := by
        rw [intervalIntegral.integral_add (((j0.add j1).add j2).add j3) j4,
          intervalIntegral.integral_add ((j0.add j1).add j2) j3,
          intervalIntegral.integral_add (j0.add j1) j2, intervalIntegral.integral_add j0 j1,
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, smul_eq_mul]
      _ ≤ 5 * (b^2/r+p^2*(1/r)+m^2*(1/r^3)+e^2*(1/r)+2*e^2/r) := by
        have hconst : (L-r)*(b^2/L^2) ≤ b^2/r := by
          calc
            _ ≤ L*(b^2/L^2) := mul_le_mul_of_nonneg_right (sub_le_self _ hrp.le) (by positivity)
            _ = b^2/L := by field_simp
            _ ≤ b^2/r := div_le_div_of_nonneg_left (sq_nonneg _) hrp hrL
        have hlogs : (e/L)^2*(∫ s in r..L, Real.log (L/s)^2) ≤ 2*e^2/r := by
          calc
            _ ≤ (e/L)^2*(2*L) := mul_le_mul_of_nonneg_left (integral_outer_log_sq_le hrp hrL)
                (sq_nonneg _)
            _ = 2*e^2/L := by field_simp
            _ ≤ 2*e^2/r := div_le_div_of_nonneg_left (by positivity) hrp hrL
        exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add
          (add_le_add hconst (mul_le_mul_of_nonneg_left hinv2 (sq_nonneg _)))
          (mul_le_mul_of_nonneg_left hinv4 (sq_nonneg _)))
          (mul_le_mul_of_nonneg_left hinv2 (sq_nonneg _))) hlogs) (by norm_num)
      _ = _ := by ring

/-- [internal]
Radial mass improvement from the prior scalar estimate and the exact normalized
mass equation. The neutral constant is chosen after the fixed bounds `K,Cn`;
the boundary and electric constants are chosen after `Ct,Ce,B`. Every constant
precedes all radii, errors and profiles, uniformly in the outer radius and fields.
The caller takes the regional supremum using the full outward sections. -/
theorem co_outer_mass_of_scalar_estimate (K Cn : ℝ) (hK : 0 ≤ K) (hCn : 0 ≤ Cn) :
    ∃ Cneutral : ℝ, 0 < Cneutral ∧ ∀ (Ct Ce B : ℝ),
      0 ≤ Ct → 0 ≤ Ce → 0 ≤ B → ∃ Cboundary Celectric : ℝ,
      0 < Cboundary ∧ 0 < Celectric ∧
      ∀ (L0 r L epsilon eta Nphi Nm qStar : ℝ)
        (D gStar Q : ℝ → ℝ) (y yStar : ℝ → ℂ),
      1 ≤ L0 → L0 ≤ r → r ≤ L → 0 ≤ epsilon → epsilon ≤ 1 →
      0 ≤ eta → eta ≤ 1 → 0 ≤ Nphi → 0 ≤ Nm → |qStar| ≤ 1 →
      AbsolutelyContinuousOnInterval D r L →
      ContinuousOn y (Icc r L) → ContinuousOn yStar (Icc r L) →
      ContinuousOn gStar (Icc r L) → ContinuousOn Q (Icc r L) →
      (∫ s in r..L, ‖y s‖^2) ≤ 8 → |D L| ≤ Ct*epsilon/L →
      (∀ s ∈ Icc r L, ‖yStar s‖ ≤ K/s ∧ |gStar s| ≤ 2 ∧
        |Q s| ≤ 2 ∧ |Q s-qStar| ≤ B*eta) →
      (∀ s ∈ Icc r L, ‖y s-yStar s‖ ≤ Ct*epsilon/L+Cn*Nphi/s+Cn*Nm/s^2+
        Ce*eta/s^3+Ce*eta/L*Real.log (L/s)) →
      (∀ᵐ s ∂volume.restrict (Icc r L), deriv D s = -(‖y s‖^2/s)*D s+
        ((Q s^2-qStar^2)/(2*s^2)+gStar s*(starRingEnd ℂ (yStar s)*(y s-yStar s)).re+
          gStar s/2*‖y s-yStar s‖^2)) →
      |D r| ≤ (Cboundary*epsilon+Celectric*eta)/L0+
        (Cneutral/L0)*(Nphi+Nphi^2)+(Cneutral/L0^2)*Nm+(Cneutral/L0^3)*Nm^2 := by
  obtain ⟨Cq, hCq, hcharge⟩ := co_electric_mass_error
  let E := Real.exp 8
  let A := 2*K*Cn+5*Cn^2+1
  refine ⟨E*A, by dsimp [E,A]; positivity, ?_⟩
  intro Ct Ce B hCt hCe hB
  let Tb := Ct+2*K*Ct+5*Ct^2+1
  let Te := 6*K*Ce+15*Ce^2+Cq*B+1
  refine ⟨E*Tb, E*Te, by dsimp [E,Tb]; positivity, by dsimp [E,Te]; positivity, ?_⟩
  intro L0 r L epsilon eta Nphi Nm qStar D gStar Q y yStar hL0 hL0r hrL
    heps heps1 heta heta1 hphi hm hq hD hy hys hg hQ henergy hboundary hstatic hscalar heq
  have hr : 1 ≤ r := hL0.trans hL0r
  have hrp : 0 < r := by linarith
  have hL : 0 < L := hrp.trans_le hrL
  have hs (s : ℝ) (h : s ∈ Icc r L) : 0 < s := hrp.trans_le h.1
  let Y := fun s => y s-yStar s
  let F := fun s => (Q s^2-qStar^2)/(2*s^2)+
    gStar s*(starRingEnd ℂ (yStar s)*Y s).re+gStar s/2*‖Y s‖^2
  have hY : ContinuousOn Y (Icc r L) := hy.sub hys
  have hchargeC : ContinuousOn (fun s => |Q s^2-qStar^2|/s^2) (Icc r L) :=
    ((hQ.pow 2).sub continuousOn_const).abs.div (continuousOn_id.pow 2)
      (fun s h => pow_ne_zero 2 (hs s h).ne')
  have hFc : ContinuousOn F (Icc r L) :=
    (((hQ.pow 2).sub continuousOn_const).div (continuousOn_const.mul (continuousOn_id.pow 2))
      (fun s h => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hs s h).ne'))).add
      (hg.mul (Complex.continuous_re.comp_continuousOn (hys.star.mul hY))) |>.add ((hg.div_const
          2).mul (hY.norm.pow 2))
  have hFi : IntervalIntegrable F volume r L := hFc.intervalIntegrable_of_Icc hrL
  have ha : IntervalIntegrable (fun s => ‖y s‖^2/s) volume r L :=
    ((hy.norm.pow 2).div continuousOn_id (fun s h => (hs s h).ne')).intervalIntegrable_of_Icc hrL
  have hfactor (s : ℝ) (h : s ∈ Icc r L) :
      Real.exp (∫ t in r..s, ‖y t‖^2/t) ≤ E := by
    apply (Observation.backward_mass_integrating_factor_of_normalization hrp hrL hy henergy s
        h).trans
    exact Real.exp_le_exp.mpr ((div_le_iff₀ hrp).mpr (by nlinarith only [hr]))
  have hmass := backward_mass_abs_le hrL hD ha hFi heq hfactor
  have hforce (s : ℝ) (h : s ∈ Icc r L) :
      |F s| ≤ |Q s^2-qStar^2|/s^2+2*K*(‖Y s‖/s)+‖Y s‖^2 := by
    obtain ⟨hysb,hgb,_,_⟩ := hstatic s h
    have hsp := hs s h
    have hre := Complex.abs_re_le_norm (starRingEnd ℂ (yStar s)*Y s)
    rw [norm_mul, Complex.norm_conj] at hre
    have hlin : |gStar s*(starRingEnd ℂ (yStar s)*Y s).re| ≤ 2*K*(‖Y s‖/s) := by
      rw [abs_mul]
      calc
        _ ≤ 2*(‖yStar s‖*‖Y s‖) := mul_le_mul hgb hre (abs_nonneg _) (by norm_num)
        _ ≤ 2*((K/s)*‖Y s‖) := by gcongr
        _ = _ := by ring
    have hquad : |gStar s/2*‖Y s‖^2| ≤ ‖Y s‖^2 := by
      rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg (sq_nonneg ‖Y s‖)]
      exact (mul_le_mul_of_nonneg_right ((div_le_one (by norm_num)).mpr hgb)
        (sq_nonneg _)).trans_eq (one_mul _)
    have hqc : |(Q s^2-qStar^2)/(2*s^2)| ≤ |Q s^2-qStar^2|/s^2 := by
      rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg (sq_nonneg s)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (le_mul_of_one_le_left
          (sq_nonneg s) (by norm_num))
    exact (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add hqc hlin)) hquad)
  have hiY : IntervalIntegrable (fun s => ‖Y s‖/s) volume r L :=
    (hY.norm.div continuousOn_id (fun s h => (hs s h).ne')).intervalIntegrable_of_Icc hrL
  have hiY2 : IntervalIntegrable (fun s => ‖Y s‖^2) volume r L :=
    (hY.norm.pow 2).intervalIntegrable_of_Icc hrL
  have hforcing : (∫ s in r..L, |F s|) ≤ Cq*B*eta/r+
      2*K*((Ct*epsilon+Cn*Nphi+3*(Ce*eta))/r+(Cn*Nm)/r^2)+
      (5*((Ct*epsilon)^2+(Cn*Nphi)^2+3*(Ce*eta)^2)/r+5*(Cn*Nm)^2/r^3) := by
    have hker := outer_scalar_mass_kernels hr hrL (by positivity : 0 ≤ Ct*epsilon)
      (by positivity : 0 ≤ Cn*Nphi) (by positivity : 0 ≤ Cn*Nm)
      (by positivity : 0 ≤ Ce*eta) hY hscalar
    have hiC : IntervalIntegrable (fun s => |Q s^2-qStar^2|/s^2) volume r L :=
        hchargeC.intervalIntegrable_of_Icc hrL
    calc
      _ ≤ ∫ s in r..L, |Q s^2-qStar^2|/s^2+2*K*(‖Y s‖/s)+‖Y s‖^2 :=
        intervalIntegral.integral_mono_on hrL hFi.abs ((hiC.add (hiY.const_mul (2*K))).add hiY2)
            hforce
      _ = (∫ s in r..L, |Q s^2-qStar^2|/s^2)+2*K*(∫ s in r..L, ‖Y s‖/s)+
          (∫ s in r..L, ‖Y s‖^2) := by
        rw [intervalIntegral.integral_add (hiC.add (hiY.const_mul (2*K))) hiY2,
          intervalIntegral.integral_add hiC (hiY.const_mul (2*K)),
              intervalIntegral.integral_const_mul]
      _ ≤ _ := add_le_add (add_le_add (hcharge r L B eta qStar Q hrp hrL hB heta hq hQ
          (fun s h => ⟨(hstatic s h).2.2.1, (hstatic s h).2.2.2⟩))
          (mul_le_mul_of_nonneg_left hker.1 (by positivity))) hker.2
  have hb2 : (Ct*epsilon)^2 ≤ Ct^2*epsilon := by
    calc
      (Ct*epsilon)^2 = Ct^2 * (epsilon*epsilon) := by ring
      _ ≤ Ct^2 * epsilon :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_right heps heps1) (sq_nonneg Ct)
  have he2 : (Ce*eta)^2 ≤ Ce^2*eta := by
    calc
      (Ce*eta)^2 = Ce^2 * (eta*eta) := by ring
      _ ≤ Ce^2 * eta :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_right heta heta1) (sq_nonneg Ce)
  have hpoly : |D L|+(∫ s in r..L, |F s|) ≤
      (Tb*epsilon+Te*eta)/r+(A/r)*(Nphi+Nphi^2)+(A/r^2)*Nm+(A/r^3)*Nm^2 := by
    calc
      _ ≤ Ct*epsilon/r+Cq*B*eta/r+
          2*K*((Ct*epsilon+Cn*Nphi+3*(Ce*eta))/r+(Cn*Nm)/r^2)+
          (5*(Ct^2*epsilon+(Cn*Nphi)^2+3*(Ce^2*eta))/r+5*(Cn*Nm)^2/r^3) := by
        have hbd := hboundary.trans (div_le_div_of_nonneg_left (by positivity) hrp hrL)
        have hsq : 5*((Ct*epsilon)^2+(Cn*Nphi)^2+3*(Ce*eta)^2)/r ≤
            5*(Ct^2*epsilon+(Cn*Nphi)^2+3*(Ce^2*eta))/r := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hb2 le_rfl)
            (mul_le_mul_of_nonneg_left he2 (by norm_num))) (by norm_num : (0:ℝ) ≤ 5)) hrp.le
        linarith only [hbd, hforcing, hsq]
      _ ≤ _ := by
        apply le_of_sub_nonneg
        dsimp [A,Tb,Te]
        ring_nf
        positivity
  have hpoint : |D r| ≤ (E*Tb*epsilon+E*Te*eta)/r+
      (E*A/r)*(Nphi+Nphi^2)+(E*A/r^2)*Nm+(E*A/r^3)*Nm^2 := by
    apply hmass.trans
    convert mul_le_mul_of_nonneg_left hpoly (Real.exp_pos 8).le using 1
    dsimp [E]
    ring
  apply hpoint.trans
  gcongr
end EmcsfAcExtension.Global
