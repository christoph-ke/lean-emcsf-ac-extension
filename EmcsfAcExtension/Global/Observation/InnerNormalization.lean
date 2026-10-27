module

public import EmcsfAcExtension.Global.Api.Definitions
import EmcsfAcExtension.Global.Observation.BoundaryCharts
import EmcsfAcExtension.Global.Observation.Potential

/-! # The inner clock chart retains the boundary-parallel gauge

Both null coordinates are reparametrized by twice the cylinder clock.
The potential is pulled back as a covector, without a new gauge change.
Source: charged_SF_new_version.tex:L2587–L2608; internal project record (N0).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Global

/-- [internal]
At an inner-clock point the pullback has the two normalized expansions,
invariant scalar ratios and the exact incoming potential Jacobian.
The potential is retained, with no zero-potential premise. -/
theorem Observation.inner_normalization_at_of_clock_rates
    (S : Fields) (U V : ℝ → ℝ) {t : ℝ}
    (hn : S.nu (U t) (V t) < 0) (hl : 0 < S.lam (U t) (V t))
    (hU : HasDerivAt U (1 / (-2 * S.nu (U t) (V t))) t)
    (hV : HasDerivAt V (1 / (2 * S.lam (U t) (V t))) t) :
    let P := nullPullback S U V
    P.nu t t = -1 / 2 ∧ P.lam t t = 1 / 2 ∧
      P.A t t = S.A (U t) (V t) / (-2 * S.nu (U t) (V t)) ∧
      P.theta t t / P.lam t t = S.theta (U t) (V t) / S.lam (U t) (V t) ∧
      P.xi t t / P.nu t t = S.xi (U t) (V t) / S.nu (U t) (V t) := by
  have hu0 : 1 / (-2 * S.nu (U t) (V t)) ≠ 0 :=
    div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) hn.ne)
  have hv0 : 1 / (2 * S.lam (U t) (V t)) ≠ 0 :=
    div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) hl.ne')
  obtain ⟨hy, hz⟩ := Observation.nullPullback_ratios S U V hU hV hu0 hv0
  refine ⟨?_, ?_, ?_, hy, hz⟩
  · dsimp only [nullPullback]
    rw [hU.deriv]
    field_simp [hn.ne]
  · dsimp only [nullPullback]
    rw [hV.deriv]
    field_simp [hl.ne']
  · dsimp only [nullPullback]
    rw [hU.deriv]
    ring

/-- [internal]
Construct the two global C¹ inner-clock maps and their C¹ inverses from
the actual clock derivatives on a closed window. The old fields need
only their continuous positive expansions along that cylinder. This
construction applies to an observation chart whose diagonal is not an
axis and therefore introduces no transformed `IsSolution` premise. -/
theorem Observation.inner_c1_maps_of_clock_rates
    (S : Fields) {u₀ v₀ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn u₀ (Icc a b)) (hv : ContinuousOn v₀ (Icc a b))
    (hnu : ContinuousOn (fun t => S.nu (u₀ t) (v₀ t)) (Icc a b))
    (hlam : ContinuousOn (fun t => S.lam (u₀ t) (v₀ t)) (Icc a b))
    (hn : ∀ t ∈ Icc a b, S.nu (u₀ t) (v₀ t) < 0)
    (hl : ∀ t ∈ Icc a b, 0 < S.lam (u₀ t) (v₀ t))
    (hdu : ∀ t ∈ Ioo a b,
      HasDerivAt u₀ (1 / (-2 * S.nu (u₀ t) (v₀ t))) t)
    (hdv : ∀ t ∈ Ioo a b,
      HasDerivAt v₀ (1 / (2 * S.lam (u₀ t) (v₀ t))) t) :
    ∃ U V : ℝ ≃o ℝ,
      ContDiff ℝ 1 (U : ℝ → ℝ) ∧ ContDiff ℝ 1 (V : ℝ → ℝ) ∧
      ContDiff ℝ 1 (U.symm : ℝ → ℝ) ∧ ContDiff ℝ 1 (V.symm : ℝ → ℝ) ∧
      (∀ x, 0 < deriv (U : ℝ → ℝ) x) ∧ (∀ x, 0 < deriv (V : ℝ → ℝ) x) ∧
      (∀ t ∈ Icc a b, U t = u₀ t ∧ V t = v₀ t) ∧
      (∀ t ∈ Icc a b, HasDerivAt (U : ℝ → ℝ)
        (1 / (-2 * S.nu (U t) (V t))) t) ∧
      (∀ t ∈ Icc a b, HasDerivAt (V : ℝ → ℝ)
        (1 / (2 * S.lam (U t) (V t))) t) ∧
      ∀ t ∈ Icc a b,
        (nullPullback S U V).nu t t = -1 / 2 ∧
        (nullPullback S U V).lam t t = 1 / 2 ∧
        (nullPullback S U V).A t t = S.A (U t) (V t) / (-2 * S.nu (U t) (V t)) := by
  have hnu0 (t : ℝ) (ht : t ∈ Icc a b) : -2 * S.nu (u₀ t) (v₀ t) ≠ 0 :=
    mul_ne_zero (by norm_num) (hn t ht).ne
  have hlam0 (t : ℝ) (ht : t ∈ Icc a b) : 2 * S.lam (u₀ t) (v₀ t) ≠ 0 :=
    mul_ne_zero (by norm_num) (hl t ht).ne'
  obtain ⟨U, hU, hUi, hUeq, hUd, hUp⟩ :=
    Observation.c1_orderIso_of_positive_clock hab hu
      (continuousOn_const.div (hnu.const_mul (-2)) hnu0)
      (fun t ht => div_pos zero_lt_one (mul_pos_of_neg_of_neg (by norm_num) (hn t ht))) hdu
  obtain ⟨V, hV, hVi, hVeq, hVd, hVp⟩ :=
    Observation.c1_orderIso_of_positive_clock hab hv
      (continuousOn_const.div (hlam.const_mul 2) hlam0)
      (fun t ht => div_pos zero_lt_one (mul_pos (by norm_num) (hl t ht))) hdv
  have hdU (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (U : ℝ → ℝ)
      (1 / (-2 * S.nu (U t) (V t))) t := by
    simpa only [hUeq t ht, hVeq t ht, Pi.div_apply] using hUd t ht
  have hdV (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (V : ℝ → ℝ)
      (1 / (2 * S.lam (U t) (V t))) t := by
    simpa only [hUeq t ht, hVeq t ht, Pi.div_apply] using hVd t ht
  refine ⟨U, V, hU, hV, hUi, hVi, hUp, hVp,
    fun t ht => ⟨hUeq t ht, hVeq t ht⟩, hdU, hdV, ?_⟩
  intro t ht
  have hn' : S.nu (U t) (V t) < 0 := by simpa only [hUeq t ht, hVeq t ht] using hn t ht
  have hl' : 0 < S.lam (U t) (V t) := by simpa only [hUeq t ht, hVeq t ht] using hl t ht
  have h := Observation.inner_normalization_at_of_clock_rates S U V hn' hl' (hdU t ht) (hdV t ht)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- [internal]
The inverse clock Jacobian is bounded using only the fixed optical lower
bound. The coefficients are exact and independent of the old chart,
scalar background, coupling and length scale. -/
theorem Observation.inner_clock_jacobian_bounds {c x : ℝ}
    (hc : 0 < c) (hlow : c ≤ x) (hhigh : x ≤ 1 / 2) :
    1 ≤ 1 / (2 * x) ∧ 1 / (2 * x) ≤ 1 / (2 * c) := by
  have hx : 0 < x := hc.trans_le hlow
  constructor
  · exact (le_div_iff₀ (mul_pos (by norm_num) hx)).mpr (by linarith only [hhigh])
  · exact one_div_le_one_div_of_le (mul_pos (by norm_num) hc)
      (mul_le_mul_of_nonneg_left hlow (by norm_num))

/-- [node prop:charged-observation#inner-null-normalization]
Construct the inner null chart with both quantitative inverse Jacobians,
the original gauge potential and invariant scalar ratios. All bounds
depend only on the displayed positive optical bound `c`; they are uniform
in the radius, scalar background, coupling and clock-window length.
The trace measure is the same clock parameter on the new diagonal.
The maps and inverse maps are globally C¹, including window endpoints. -/
theorem Observation.inner_null_normalization_of_clock_rates
    (S : Fields) {u₀ v₀ : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hu : ContinuousOn u₀ (Icc a b)) (hv : ContinuousOn v₀ (Icc a b))
    (hnu : ContinuousOn (fun t => S.nu (u₀ t) (v₀ t)) (Icc a b))
    (hlam : ContinuousOn (fun t => S.lam (u₀ t) (v₀ t)) (Icc a b))
    (hopt : ∀ t ∈ Icc a b,
      -S.nu (u₀ t) (v₀ t) ∈ Icc c (1 / 2) ∧ S.lam (u₀ t) (v₀ t) ∈ Icc c (1 / 2))
    (hdu : ∀ t ∈ Ioo a b,
      HasDerivAt u₀ (1 / (-2 * S.nu (u₀ t) (v₀ t))) t)
    (hdv : ∀ t ∈ Ioo a b,
      HasDerivAt v₀ (1 / (2 * S.lam (u₀ t) (v₀ t))) t) :
    ∃ U V : ℝ ≃o ℝ,
      ContDiff ℝ 1 (U : ℝ → ℝ) ∧ ContDiff ℝ 1 (V : ℝ → ℝ) ∧
      ContDiff ℝ 1 (U.symm : ℝ → ℝ) ∧ ContDiff ℝ 1 (V.symm : ℝ → ℝ) ∧
      (∀ x, 0 < deriv (U : ℝ → ℝ) x) ∧ (∀ x, 0 < deriv (V : ℝ → ℝ) x) ∧
      (∀ t ∈ Icc a b, U t = u₀ t ∧ V t = v₀ t) ∧
      ∀ t ∈ Icc a b,
        deriv (U : ℝ → ℝ) t ∈ Icc 1 (1 / (2 * c)) ∧
        deriv (V : ℝ → ℝ) t ∈ Icc 1 (1 / (2 * c)) ∧
        deriv (U.symm : ℝ → ℝ) (U t) ∈ Icc (2 * c) 1 ∧
        deriv (V.symm : ℝ → ℝ) (V t) ∈ Icc (2 * c) 1 ∧
        (nullPullback S U V).nu t t = -1 / 2 ∧
        (nullPullback S U V).lam t t = 1 / 2 ∧
        (nullPullback S U V).A t t = S.A (U t) (V t) / (-2 * S.nu (U t) (V t)) ∧
        (nullPullback S U V).theta t t / (nullPullback S U V).lam t t =
          S.theta (U t) (V t) / S.lam (U t) (V t) ∧
        (nullPullback S U V).xi t t / (nullPullback S U V).nu t t =
          S.xi (U t) (V t) / S.nu (U t) (V t) := by
  have hn (t : ℝ) (ht : t ∈ Icc a b) : S.nu (u₀ t) (v₀ t) < 0 := by
    linarith only [(hopt t ht).1.1, hc]
  have hl (t : ℝ) (ht : t ∈ Icc a b) : 0 < S.lam (u₀ t) (v₀ t) :=
    hc.trans_le (hopt t ht).2.1
  obtain ⟨U, V, hU, hV, hUi, hVi, hUp, hVp, heq, hdU, hdV, _⟩ :=
    Observation.inner_c1_maps_of_clock_rates S hab hu hv hnu hlam hn hl hdu hdv
  refine ⟨U, V, hU, hV, hUi, hVi, hUp, hVp, heq, ?_⟩
  intro t ht
  have hn' : S.nu (U t) (V t) < 0 := by
    simpa only [(heq t ht).1, (heq t ht).2] using hn t ht
  have hl' : 0 < S.lam (U t) (V t) := by
    simpa only [(heq t ht).1, (heq t ht).2] using hl t ht
  have hop : -S.nu (U t) (V t) ∈ Icc c (1 / 2) ∧
      S.lam (U t) (V t) ∈ Icc c (1 / 2) := by
    simpa only [(heq t ht).1, (heq t ht).2] using hopt t ht
  have hUd := hdU t ht
  have hVd := hdV t ht
  have hUinv : HasDerivAt (U.symm : ℝ → ℝ) (-2 * S.nu (U t) (V t)) (U t) := by
    have hd : HasDerivAt (U : ℝ → ℝ) (1 / (-2 * S.nu (U t) (V t)))
        (U.symm (U t)) := by simpa only [U.symm_apply_apply] using hUd
    simpa only [one_div, inv_inv] using
      hd.of_local_left_inverse U.symm.continuous.continuousAt
        (one_div_ne_zero (mul_ne_zero (by norm_num) hn'.ne))
        (Filter.Eventually.of_forall U.apply_symm_apply)
  have hVinv : HasDerivAt (V.symm : ℝ → ℝ) (2 * S.lam (U t) (V t)) (V t) := by
    have hd : HasDerivAt (V : ℝ → ℝ) (1 / (2 * S.lam (U t) (V t)))
        (V.symm (V t)) := by simpa only [V.symm_apply_apply] using hVd
    simpa only [one_div, inv_inv] using
      hd.of_local_left_inverse V.symm.continuous.continuousAt
        (one_div_ne_zero (mul_ne_zero (by norm_num) hl'.ne'))
        (Filter.Eventually.of_forall V.apply_symm_apply)
  refine ⟨?_, ?_, ?_, ?_,
    Observation.inner_normalization_at_of_clock_rates S U V hn' hl' hUd hVd⟩
  · rw [hUd.deriv]
    simpa only [mem_Icc, mul_neg, neg_mul] using
      Observation.inner_clock_jacobian_bounds hc hop.1.1 hop.1.2
  · rw [hVd.deriv]
    exact Observation.inner_clock_jacobian_bounds hc hop.2.1 hop.2.2
  · rw [hUinv.deriv]
    constructor <;> linarith only [hop.1.1, hop.1.2]
  · rw [hVinv.deriv]
    constructor <;> linarith only [hop.2.1, hop.2.2]

/-- [internal]
The radial scalar energy on a positive-radius annulus follows directly
from mass in `[0,2]` and the gap `delta`. The coefficient is exactly
`4/delta`, uniformly in the scalar, charge and interval endpoints. -/
theorem Observation.inner_radial_energy_of_equations
    {r L delta : ℝ} {m Q : ℝ → ℝ} {y : ℝ → ℂ}
    (hr : 0 < r) (hrL : r ≤ L) (hdelta : 0 < delta)
    (hm : ContinuousOn m (Icc r L)) (hQ : ContinuousOn Q (Icc r L))
    (hy : ContinuousOn y (Icc r L))
    (hd : ∀ s ∈ Ioo r L, HasDerivAt m
      ((1 - 2 * m s / s) * ‖y s‖ ^ 2 / 2 + Q s ^ 2 / (2 * s ^ 2)) s)
    (hbox : ∀ s ∈ Icc r L, m s ∈ Icc 0 2 ∧ delta ≤ 1 - 2 * m s / s) :
    (∫ s in r..L, ‖y s‖ ^ 2) ≤ 4 / delta := by
  have hpos (s : ℝ) (hs : s ∈ Icc r L) : 0 < s := hr.trans_le hs.1
  have hf : ContinuousOn
      (fun s => (1 - 2 * m s / s) * ‖y s‖ ^ 2 / 2 + Q s ^ 2 / (2 * s ^ 2))
      (Icc r L) :=
    (((continuousOn_const.sub ((continuousOn_const.mul hm).div continuousOn_id
      (fun s hs => (hpos s hs).ne'))).mul (hy.norm.pow 2)).div_const 2).add
      ((hQ.pow 2).div (continuousOn_const.mul (continuousOn_id.pow 2))
        (fun s hs => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hpos s hs).ne')))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrL hm hd
    (hf.intervalIntegrable_of_Icc hrL)
  have hp (s : ℝ) (hs : s ∈ Icc r L) : delta / 2 * ‖y s‖ ^ 2 ≤
      (1 - 2 * m s / s) * ‖y s‖ ^ 2 / 2 + Q s ^ 2 / (2 * s ^ 2) := by
    have h := mul_le_mul_of_nonneg_right (hbox s hs).2 (sq_nonneg ‖y s‖)
    have hq : 0 ≤ Q s ^ 2 / (2 * s ^ 2) := by positivity
    linarith only [h, hq]
  have hb := intervalIntegral.integral_mono_on hrL
    ((hy.norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hrL |>.const_mul (delta / 2))
    (hf.intervalIntegrable_of_Icc hrL) hp
  rw [intervalIntegral.integral_const_mul, hi] at hb
  apply (le_div_iff₀ hdelta).mpr
  have hmL := (hbox L ⟨hrL, le_rfl⟩).1.2
  have hmr := (hbox r ⟨le_rfl, hrL⟩).1.1
  simp only [Pi.pow_apply] at hb
  linarith only [hb, hmL, hmr]

/-- [node prop:charged-observation#inner-scalar-charge-control]
On the fixed positive-radius annulus the scalar envelope and Maxwell
variation follow from the radial component equations and scalar mass
energy. Constants are fixed after `rStar,Lzero,delta,B` alone, before all
fields, scalar backgrounds, couplings and outer scales. Here `B` is the
outer scalar boundary coefficient at `Lzero`. Only a boundary value of
the scalar, rather than any incoming supremum, is used. -/
theorem Observation.inner_scalar_charge_of_radial_equations
    (rStar Lzero delta B : ℝ) (hrStar : 0 < rStar)
    (hLzero : rStar ≤ Lzero) (hdelta : 0 < delta) (hB : 0 ≤ B) :
    ∃ Cphi Ccharge : ℝ, 0 < Cphi ∧ 0 < Ccharge ∧
      ∀ (m Q : ℝ → ℝ) (phi y : ℝ → ℂ) (H : ℂ) (e eta L r : ℝ),
      r ∈ Icc rStar Lzero → 0 < L → |e| * L * (1 + ‖H‖) = eta →
      ContinuousOn m (Icc r Lzero) → ContinuousOn Q (Icc r Lzero) →
      ContinuousOn phi (Icc r Lzero) → ContinuousOn y (Icc r Lzero) →
      (∀ s ∈ Ioo r Lzero, HasDerivAt m
        ((1 - 2 * m s / s) * ‖y s‖ ^ 2 / 2 + Q s ^ 2 / (2 * s ^ 2)) s) →
      (∀ s ∈ Ioo r Lzero, HasDerivAt phi (y s / (s : ℂ)) s) →
      (∀ s ∈ Ioo r Lzero,
        HasDerivAt Q (-e * s * (starRingEnd ℂ (phi s) * y s).im) s) →
      (∀ s ∈ Icc r Lzero, m s ∈ Icc 0 2 ∧ delta ≤ 1 - 2 * m s / s) →
      ‖phi Lzero - H‖ ≤ B →
      (∀ s ∈ Icc r Lzero, ‖phi s‖ ≤ ‖H‖ + Cphi) ∧
        |Q r - Q Lzero| ≤ Ccharge * eta / L := by
  let M := (4 / delta + Lzero) / 2
  let Cphi := B + M / rStar + 1
  let Ccharge := Lzero * (Cphi + 1) * M + 1
  have hLz : 0 < Lzero := hrStar.trans_le hLzero
  have hM : 0 < M := by dsimp [M]; positivity
  have hCp : 0 < Cphi := by dsimp [Cphi]; positivity
  have hCq : 0 < Ccharge := by dsimp [Ccharge]; positivity
  refine ⟨Cphi, Ccharge, hCp, hCq, ?_⟩
  intro m Q phi y H e eta L r hr hL hscale hm hQ hphi hy hdm hdphi hdQ hbox hb
  have hrp : 0 < r := hrStar.trans_le hr.1
  have henergy := Observation.inner_radial_energy_of_equations hrp hr.2 hdelta hm hQ hy hdm hbox
  have hyi : IntervalIntegrable (fun s => ‖y s‖) volume r Lzero :=
    hy.norm.intervalIntegrable_of_Icc hr.2
  have hy2i : IntervalIntegrable (fun s => ‖y s‖ ^ 2) volume r Lzero :=
    (hy.norm.pow 2).intervalIntegrable_of_Icc hr.2
  have hl1 : (∫ s in r..Lzero, ‖y s‖) ≤ M := by
    have hi := intervalIntegral.integral_mono_on hr.2 (hyi.const_mul 2)
      (hy2i.add intervalIntegrable_const) (fun s _ => by
        change 2 * ‖y s‖ ≤ ‖y s‖ ^ 2 + 1
        nlinarith only [sq_nonneg (‖y s‖ - 1)])
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hy2i intervalIntegrable_const,
      intervalIntegral.integral_const] at hi
    simp only [smul_eq_mul, mul_one] at hi
    dsimp only [M]
    linarith only [hi, henergy, hrp.le]
  have hphib : ‖phi Lzero‖ ≤ ‖H‖ + B := by
    calc
      _ = ‖(phi Lzero - H) + H‖ := by rw [sub_add_cancel]
      _ ≤ ‖phi Lzero - H‖ + ‖H‖ := norm_add_le _ _
      _ ≤ _ := by linarith only [hb]
  have hp (s : ℝ) (hs : s ∈ Icc r Lzero) : ‖phi s‖ ≤ ‖H‖ + Cphi := by
    have hsub : Icc s Lzero ⊆ Icc r Lzero := Icc_subset_Icc hs.1 le_rfl
    have hderc : ContinuousOn (fun t => y t / (t : ℂ)) (Icc s Lzero) :=
      (hy.mono hsub).div Complex.continuous_ofReal.continuousOn
        (fun t ht => Complex.ofReal_ne_zero.mpr (hrp.trans_le (hsub ht).1).ne')
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.2
      (hphi.mono hsub) (fun t ht => hdphi t ⟨hs.1.trans_lt ht.1, ht.2⟩)
      (hderc.intervalIntegrable_of_Icc hs.2)
    have htail := intervalIntegral.integral_mono_interval hs.1 hs.2 le_rfl
      (Filter.Eventually.of_forall (fun t => norm_nonneg (y t))) hyi
    have hiNorm : ‖phi Lzero - phi s‖ ≤ M / rStar := by
      rw [← hi]
      apply (intervalIntegral.norm_integral_le_integral_norm hs.2).trans
      have hi' := intervalIntegral.integral_mono_on hs.2
        (hderc.norm.intervalIntegrable_of_Icc (μ := volume) hs.2)
        ((hy.norm.mono hsub).intervalIntegrable_of_Icc (μ := volume) hs.2 |>.div_const rStar)
        (fun t ht => by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (hrp.trans_le (hsub ht).1)]
          exact div_le_div_of_nonneg_left (norm_nonneg _) hrStar
            (hr.1.trans (hsub ht).1))
      rw [intervalIntegral.integral_div] at hi'
      exact hi'.trans (div_le_div_of_nonneg_right (htail.trans hl1) hrStar.le)
    have hn := norm_le_insert (phi Lzero) (phi s)
    dsimp only [Cphi]
    linarith only [hn, hiNorm, hphib]
  refine ⟨hp, ?_⟩
  have hFc : ContinuousOn (fun s => -e * s * (starRingEnd ℂ (phi s) * y s).im)
      (Icc r Lzero) :=
    (continuousOn_const.mul continuousOn_id).mul
      (Complex.continuous_im.comp_continuousOn (hphi.star.mul hy))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.2 hQ hdQ
    (hFc.intervalIntegrable_of_Icc hr.2)
  have hs (s : ℝ) (hs : s ∈ Icc r Lzero) :
      |-e * s * (starRingEnd ℂ (phi s) * y s).im| ≤
        (|e| * Lzero * (‖H‖ + Cphi)) * ‖y s‖ := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos (hrp.trans_le hs.1)]
    calc
      _ ≤ (|e| * Lzero) * ((‖H‖ + Cphi) * ‖y s‖) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hs.2 (abs_nonneg _)
        · exact (Complex.abs_im_le_norm _).trans (by
            rw [norm_mul, Complex.norm_conj]
            exact mul_le_mul_of_nonneg_right (hp s hs) (norm_nonneg _))
        · exact abs_nonneg _
        · positivity
      _ = _ := by ring
  have hcharge : |Q r - Q Lzero| ≤ |e| * Lzero * (‖H‖ + Cphi) * M := by
    rw [abs_sub_comm, ← hFTC]
    apply (intervalIntegral.abs_integral_le_integral_abs hr.2).trans
    have hi := intervalIntegral.integral_mono_on hr.2
      (hFc.abs.intervalIntegrable_of_Icc (μ := volume) hr.2)
      (hyi.const_mul (|e| * Lzero * (‖H‖ + Cphi))) hs
    rw [intervalIntegral.integral_const_mul] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left hl1 (by positivity))
  have herr : |e| * (1 + ‖H‖) = eta / L := by
    rw [← hscale]
    field_simp
  have hH : ‖H‖ + Cphi ≤ (Cphi + 1) * (1 + ‖H‖) := by
    have hh := mul_nonneg hCp.le (norm_nonneg H)
    nlinarith only [hh]
  calc
    _ ≤ |e| * Lzero * (‖H‖ + Cphi) * M := hcharge
    _ ≤ |e| * Lzero * ((Cphi + 1) * (1 + ‖H‖)) * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH (by positivity)) hM.le
    _ = (Lzero * (Cphi + 1) * M) * (eta / L) := by rw [← herr]; ring
    _ ≤ Ccharge * eta / L := by
      have he : 0 ≤ eta / L := by rw [← herr]; positivity
      have h := mul_le_mul_of_nonneg_right
        (show Lzero * (Cphi + 1) * M ≤ Ccharge by dsimp [Ccharge]; linarith) he
      simpa only [mul_div_assoc] using h

/-- [internal]
A bounded clock Jacobian transfers squared trace errors without an
incoming supremum. The coefficient `2` is universal, uniform in the
functions, interval, Jacobian and two error bounds. `w` is precisely the
density of the inner-clock measure relative to the old incoming label.
The two terms on the right use an unweighted boundary square integral
and the actual inner-clock length, respectively. -/
theorem Observation.incoming_trace_square_of_pointwise
    {z g : ℝ → ℂ} {w : ℝ → ℝ} {a b A B : ℝ}
    (hab : a ≤ b) (hz : ContinuousOn z (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw0 : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hw1 : ∀ x ∈ Icc a b, w x ≤ 1)
    (hpoint : ∀ x ∈ Icc a b, ‖z x‖ ≤ A * ‖g x‖ + B) :
    (∫ x in a..b, w x * ‖z x‖ ^ 2) ≤
      2 * A ^ 2 * (∫ x in a..b, ‖g x‖ ^ 2) +
        2 * B ^ 2 * (∫ x in a..b, w x) := by
  have hleft := (hw.mul (hz.norm.pow 2)).intervalIntegrable_of_Icc (μ := volume) hab
  have hright := (((hg.norm.pow 2).const_mul (2 * A ^ 2)).add
    (hw.const_mul (2 * B ^ 2))).intervalIntegrable_of_Icc (μ := volume) hab
  have hle := intervalIntegral.integral_mono_on hab hleft hright (fun x hx => by
    change w x * ‖z x‖ ^ 2 ≤ 2 * A ^ 2 * ‖g x‖ ^ 2 + 2 * B ^ 2 * w x
    have hz0 := norm_nonneg (z x)
    have hg0 := norm_nonneg (g x)
    have hsum0 : 0 ≤ A * ‖g x‖ + B := add_nonneg (mul_nonneg hA hg0) hB
    have hs := (sq_le_sq₀ hz0 hsum0).mpr (hpoint x hx)
    have hs' : ‖z x‖ ^ 2 ≤ 2 * A ^ 2 * ‖g x‖ ^ 2 + 2 * B ^ 2 := by
      nlinarith only [hs, sq_nonneg (A * ‖g x‖ - B)]
    have hmul := mul_le_mul_of_nonneg_left hs' (hw0 x hx)
    have hfirst := mul_le_mul_of_nonneg_right (hw1 x hx)
      (show 0 ≤ 2 * A ^ 2 * ‖g x‖ ^ 2 by positivity)
    nlinarith only [hmul, hfirst])
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at hle
  have hpow : (fun x => ‖g x‖) ^ 2 = (fun x => ‖g x‖ ^ 2) := by
    funext x
    simp only [Pi.pow_apply]
  have hig := (hg.norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hab
  rw [hpow] at hig
  have hiw : IntervalIntegrable w volume a b := hw.intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_add (hig.const_mul (2 * A ^ 2))
    (hiw.const_mul (2 * B ^ 2)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hle
  exact hle

/-- [internal]
The squared boundary trace in the inner clock is exactly its old-label
integral with the clock Jacobian. This is a substitution identity for
the same representative, rather than an additional trace assumption.
For the observation clock the density is `deriv tau = 2 * (-nu)`.
The coefficient is one, uniformly in the chart and the representative. -/
theorem Observation.incoming_trace_clock_integral
    (tau : ℝ ≃o ℝ) (htau : ContDiff ℝ 1 (tau : ℝ → ℝ))
    (hpos : ∀ x, 0 ≤ deriv (tau : ℝ → ℝ) x)
    (h : ℝ → ℂ) (a b : ℝ) :
    (∫ t in tau a..tau b, ‖h (tau.symm t)‖ ^ 2) =
      ∫ u in a..b, deriv (tau : ℝ → ℝ) u * ‖h u‖ ^ 2 := by
  have he := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := a) (b := b)
    (f := (tau : ℝ → ℝ)) (f' := deriv (tau : ℝ → ℝ))
    (g := fun t => ‖h (tau.symm t)‖ ^ 2) htau.continuous.continuousOn
    (fun x _ => ((contDiff_one_iff_deriv.mp htau).1 x).hasDerivAt)
    (fun x _ => hpos x)
  simpa only [Function.comp_apply, tau.symm_apply_apply, smul_eq_mul] using he.symm

/-- [internal]
The clock-weighted incoming square trace is uniformly small once its
pointwise remainder and full outer square trace have been obtained.
The explicit coefficient depends only on `A,B,K`, before all errors,
fields, clock densities and label intervals. No incoming supremum is
required. This helper preserves the clock Jacobian in the conclusion. -/
theorem Observation.incoming_l2_trace_of_pointwise
    (A B K : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ C > 0, ∀ (z g : ℝ → ℂ) (w : ℝ → ℝ) (a b epsilon eta : ℝ),
      a ≤ b → ContinuousOn z (Icc a b) → ContinuousOn g (Icc a b) →
      ContinuousOn w (Icc a b) → 0 ≤ epsilon → 0 ≤ eta →
      (∀ x ∈ Icc a b, 0 ≤ w x ∧ w x ≤ 1) →
      (∫ x in a..b, w x) ≤ K →
      (∫ x in a..b, ‖g x‖ ^ 2) ≤ epsilon ^ 2 →
      (∀ x ∈ Icc a b, ‖z x‖ ≤ A * ‖g x‖ + B * (epsilon + eta)) →
      (∫ x in a..b, w x * ‖z x‖ ^ 2) ≤ (C * (epsilon + eta)) ^ 2 := by
  let C := 2 * (A + B * (K + 1) + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro z g w a b epsilon eta hab hz hg hw he heta hweight hlength htrace hpoint
  have herr : 0 ≤ epsilon + eta := add_nonneg he heta
  have hi := Observation.incoming_trace_square_of_pointwise hab hz hg hw hA
    (mul_nonneg hB herr) (fun x hx => (hweight x hx).1)
    (fun x hx => (hweight x hx).2) hpoint
  have hfirst := mul_le_mul_of_nonneg_left htrace (show 0 ≤ 2 * A ^ 2 by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hlength
    (show 0 ≤ 2 * (B * (epsilon + eta)) ^ 2 by positivity)
  have hesq : epsilon ^ 2 ≤ (epsilon + eta) ^ 2 :=
    (sq_le_sq₀ he herr).mpr (le_add_of_nonneg_right heta)
  have hAsq := mul_le_mul_of_nonneg_left hesq (show 0 ≤ 2 * A ^ 2 by positivity)
  have hcoeff : 2 * A ^ 2 + 2 * B ^ 2 * K ≤ C ^ 2 := by
    have hab : 0 ≤ A * (B * (K + 1)) := by positivity
    have hab' : 0 ≤ A + B * (K + 1) := by positivity
    have hbk : 0 ≤ B ^ 2 * (K ^ 2 + 1) := by positivity
    dsimp only [C]
    nlinarith only [hab, hab', hbk, sq_nonneg A, sq_nonneg (B * (K + 1))]
  have hlast := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (epsilon + eta))
  calc
    _ ≤ 2 * A ^ 2 * epsilon ^ 2 + 2 * (B * (epsilon + eta)) ^ 2 * K :=
      hi.trans (add_le_add hfirst hsecond)
    _ ≤ (2 * A ^ 2 + 2 * B ^ 2 * K) * (epsilon + eta) ^ 2 := by
      nlinarith only [hAsq]
    _ ≤ (C * (epsilon + eta)) ^ 2 := by
      simpa only [mul_pow] using hlast

/-- [node prop:charged-observation#inner-scalar-charge-control]
The inner scalar envelope and charge comparison with the outer static
charge. Constants depend only on the fixed annulus, gap and two boundary
coefficients, before all radial fields, physical scales and backgrounds.
The preceding radial energy/Maxwell theorem discharges charge variation. -/
theorem Observation.inner_scalar_charge_of_outer_boundary
    (rStar Lzero delta Bphi Bcharge : ℝ) (hrStar : 0 < rStar)
    (hLzero : rStar ≤ Lzero) (hdelta : 0 < delta) (hBp : 0 ≤ Bphi) (hBq : 0 ≤ Bcharge) :
    ∃ Cphi Cq : ℝ, 0 < Cphi ∧ 0 < Cq ∧
    ∀ (m Q : ℝ → ℝ) (phi y : ℝ → ℂ) (H : ℂ) (e eta L r qStar : ℝ),
    r ∈ Icc rStar Lzero → 1 ≤ L → eta ∈ Icc 0 1 → |qStar| ≤ 1 →
    |e| * L * (1 + ‖H‖) = eta →
    ContinuousOn m (Icc r Lzero) → ContinuousOn Q (Icc r Lzero) →
    ContinuousOn phi (Icc r Lzero) → ContinuousOn y (Icc r Lzero) →
    (∀ s ∈ Ioo r Lzero, HasDerivAt m
      ((1 - 2 * m s / s) * ‖y s‖ ^ 2 / 2 + Q s ^ 2 / (2 * s ^ 2)) s) →
    (∀ s ∈ Ioo r Lzero, HasDerivAt phi (y s / (s : ℂ)) s) →
    (∀ s ∈ Ioo r Lzero,
      HasDerivAt Q (-e * s * (starRingEnd ℂ (phi s) * y s).im) s) →
    (∀ s ∈ Icc r Lzero, m s ∈ Icc 0 2 ∧ delta ≤ 1 - 2 * m s / s) →
    ‖phi Lzero - H‖ ≤ Bphi → |Q Lzero - qStar| ≤ Bcharge * eta →
    (∀ s ∈ Icc r Lzero, ‖phi s‖ ≤ ‖H‖ + Cphi) ∧
      |Q r - qStar| ≤ Cq * eta ∧ |Q r| ≤ Cq + 1 := by
  obtain ⟨Cphi, Cv, hCp, hCv, hvariation⟩ :=
    Observation.inner_scalar_charge_of_radial_equations rStar Lzero delta Bphi
      hrStar hLzero hdelta hBp
  refine ⟨Cphi, Cv + Bcharge + 1, hCp, by positivity, ?_⟩
  intro m Q phi y H e eta L r qStar hr hL heta hq hscale cm cq cp cy hdm hdp hdq hbox hb hqb
  have hv := hvariation m Q phi y H e eta L r hr (zero_lt_one.trans_le hL) hscale
    cm cq cp cy hdm hdp hdq hbox hb
  have hvar : |Q r - Q Lzero| ≤ Cv * eta :=
    hv.2.trans (div_le_self (mul_nonneg hCv.le heta.1) hL)
  have hclose : |Q r - qStar| ≤ (Cv + Bcharge + 1) * eta := by
    have ht := abs_sub_le (Q r) (Q Lzero) qStar
    nlinarith only [ht, hvar, hqb, heta.1]
  refine ⟨hv.1, hclose, ?_⟩
  have ht : |Q r| ≤ |Q r - qStar| + |qStar| := by
    simpa only [sub_add_cancel] using abs_add_le (Q r - qStar) qStar
  have hh := mul_le_mul_of_nonneg_left heta.2
    (show 0 ≤ Cv + Bcharge + 1 by positivity)
  linarith only [ht, hq, hclose, hh]

end EmcsfAcExtension.Global
