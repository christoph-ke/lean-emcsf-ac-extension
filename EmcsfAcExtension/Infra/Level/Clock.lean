module

public import EmcsfAcExtension.Infra.Level.OrderIso
public import EmcsfAcExtension.Infra.AC.Primitive
public import EmcsfAcExtension.Infra.AC.Relabel
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Positive integral clocks

The cylinder clock is obtained by setting `w u = -ν u (v_b u)`.
An integrable density bounded between the explicit constants `m > 0` and `M`
gives an AC, increasing, bi-Lipschitz clock on the compact interval. Its inverse
is an order-isomorphism inverse on the clock interval, including its endpoints.
The bounds are uniform in the density for the stated `m` and `M`.
-/

public section

open Set MeasureTheory Filter
open scoped NNReal

namespace EmcsfAcExtension.Global.Level

/-- [internal] A positive continuous density has positive lower and finite upper
bounds on a compact interval. These constants may depend on the density and
the interval; they are uniform in the point of evaluation. -/
theorem exists_pos_bounds_of_continuousOn {w : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn w (Icc a b))
    (hp : ∀ x ∈ Icc a b, 0 < w x) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ x ∈ Icc a b, m ≤ w x ∧ w x ≤ M := by
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hc
  obtain ⟨y, hy, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc
  exact ⟨w x, w y, hp x hx, hp y hy, fun z hz => ⟨hmin hz, hmax hz⟩⟩

/-- [internal] Integral clock with base label `a`. -/
@[expose] noncomputable def integralClock (w : ℝ → ℝ) (a u : ℝ) : ℝ := ∫ s in a..u, w s

/-- [internal] The clock starts at zero. -/
@[simp] theorem integralClock_self (w : ℝ → ℝ) (a : ℝ) : integralClock w a a = 0 := by
  simp [integralClock]

/-- [internal] An integrable clock density gives an absolutely continuous clock. -/
theorem absolutelyContinuousOnInterval_integralClock {w : ℝ → ℝ} {a b : ℝ}
    (hw : IntervalIntegrable w volume a b) :
    AbsolutelyContinuousOnInterval (integralClock w a) a b := by
  unfold integralClock
  exact hw.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc

/-- [internal] A continuous density differentiates the clock at every point of
the closed interval, using within derivatives at its endpoints. -/
theorem hasDerivWithinAt_integralClock {w : ℝ → ℝ} {a b x : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn w (Icc a b)) (hx : x ∈ Icc a b) :
    HasDerivWithinAt (integralClock w a) (w x) (Icc a b) x := by
  let : Fact (x ∈ Icc a b) := ⟨hx⟩
  have hw : IntervalIntegrable w volume a x :=
    (hc.intervalIntegrable_of_Icc hab).mono_set
      (uIcc_subset_uIcc left_mem_uIcc (by rwa [uIcc_of_le hab]))
  unfold integralClock
  exact intervalIntegral.integral_hasDerivWithinAt_right hw
    (hc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x) (hc x hx)

/-- [internal] The clock increment is the integral on the intervening labels. -/
theorem integralClock_sub {w : ℝ → ℝ} {a b x y : ℝ}
    (hw : IntervalIntegrable w volume a b) (hx : x ∈ uIcc a b) (hy : y ∈ uIcc a b) :
    integralClock w a y - integralClock w a x = ∫ s in x..y, w s := by
  unfold integralClock
  exact intervalIntegral.integral_interval_sub_left
    (hw.mono_set (uIcc_subset_uIcc left_mem_uIcc hy))
    (hw.mono_set (uIcc_subset_uIcc left_mem_uIcc hx))

/-- [internal] Explicit two-sided increment estimate. The constants are exactly
the density bounds and are uniform in `w`, `x`, and `y`. -/
theorem integralClock_sub_bounds {w : ℝ → ℝ} {a b x y m M : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b)
    (hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    m * (y - x) ≤ integralClock w a y - integralClock w a x ∧
      integralClock w a y - integralClock w a x ≤ M * (y - x) := by
  rw [integralClock_sub hw (by rwa [uIcc_of_le hab]) (by rwa [uIcc_of_le hab])]
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hxyw : IntervalIntegrable w volume x y :=
    hw.mono_set (by simpa [uIcc_of_le hab, uIcc_of_le hxy] using hsub)
  have hb' := hb.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  constructor
  · simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using
      intervalIntegral.integral_mono_ae_restrict hxy (intervalIntegrable_const) hxyw
        (hb'.mono fun _ h => h.1)
  · simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using
      intervalIntegral.integral_mono_ae_restrict hxy hxyw (intervalIntegrable_const)
        (hb'.mono fun _ h => h.2)

/-- [internal] A positive lower density bound makes the clock strictly increasing. -/
theorem strictMonoOn_integralClock {w : ℝ → ℝ} {a b m M : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b) (hm : 0 < m)
    (hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M) :
    StrictMonoOn (integralClock w a) (Icc a b) := by
  intro x hx y hy hxy
  have h := (integralClock_sub_bounds hab hw hb hx hy hxy.le).1
  exact sub_pos.mp ((mul_pos hm (sub_pos.mpr hxy)).trans_le h)

/-- [internal] The terminal clock value is nonnegative on an ordered interval. -/
theorem integralClock_nonneg_end {w : ℝ → ℝ} {a b m M : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b) (hm : 0 < m)
    (hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M) :
    0 ≤ integralClock w a b := by
  simpa only [integralClock_self] using
    (strictMonoOn_integralClock hab hw hm hb).monotoneOn
      (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab

/-- [internal] Canonical clock interval isomorphism. The inverse is defined only
on the actual clock range, including its two endpoints. -/
noncomputable def clockOrderIso {w : ℝ → ℝ} {a b m M : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b) (hm : 0 < m)
    (hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M) :
    Icc a b ≃o Icc 0 (integralClock w a b) :=
  (intervalOrderIso hab
    (by simpa only [uIcc_of_le hab] using
      (absolutelyContinuousOnInterval_integralClock hw).continuousOn)
    (strictMonoOn_integralClock hab hw hm hb)).trans
    (Set.orderIsoOfEq _ _ (by rw [integralClock_self]))

/-- [internal] The clock isomorphism agrees with integration. -/
@[simp] theorem clockOrderIso_apply {w : ℝ → ℝ} {a b m M : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b) (hm : 0 < m)
    (hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M) (x : Icc a b) :
    (clockOrderIso hab hw hm hb x : ℝ) = integralClock w a x := by
  simp [clockOrderIso]

/-- [internal] The real inverse clock, with the canonical constant endpoint
extension. Its values on the image are exactly the order-isomorphism inverse. -/
@[expose] noncomputable def clockInverse {w : ℝ → ℝ} {a b m M : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b) (hm : 0 < m)
    (hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M) : ℝ → ℝ :=
  intervalInverse (clockOrderIso hab hw hm hb) (integralClock_nonneg_end hab hw hm hb)

/-- [internal] Exact derivative of the inverse clock, including its endpoints.
Continuous positivity is pointwise here, as required for the C¹ inverse rule. -/
theorem hasDerivWithinAt_clockInverse {w : ℝ → ℝ} {a b m M t : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b) (hm : 0 < m)
    (hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M)
    (hc : ContinuousOn w (Icc a b)) (hp : ∀ x ∈ Icc a b, 0 < w x)
    (ht : t ∈ Icc 0 (integralClock w a b)) :
    HasDerivWithinAt (clockInverse hab hw hm hb)
      (w (clockInverse hab hw hm hb t))⁻¹
      (Icc 0 (integralClock w a b)) t := by
  unfold clockInverse
  apply hasDerivWithinAt_intervalInverse_of_deriv _ _ (clockOrderIso_apply hab hw hm hb) ht
  · exact hasDerivWithinAt_integralClock hab hc (intervalInverse_mem _ _ t)
  · exact ne_of_gt (hp _ (intervalInverse_mem _ _ t))

/-- [internal] The canonical inverse clock is C¹ on its nondegenerate compact
image. Its reciprocal-density derivative is continuous up to both endpoints. -/
theorem contDiffOn_clockInverse {w : ℝ → ℝ} {a b m M : ℝ}
    (hab : a < b) (hw : IntervalIntegrable w volume a b) (hm : 0 < m)
    (hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M)
    (hc : ContinuousOn w (Icc a b)) (hp : ∀ x ∈ Icc a b, 0 < w x) :
    ContDiffOn ℝ 1 (clockInverse hab.le hw hm hb)
      (Icc 0 (integralClock w a b)) := by
  let e := clockOrderIso hab.le hw hm hb
  let hτ := integralClock_nonneg_end hab.le hw hm hb
  let U := clockInverse hab.le hw hm hb
  have hpos : 0 < integralClock w a b := by
    have h := strictMonoOn_integralClock hab.le hw hm hb
      (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
    simpa only [integralClock_self] using h
  have hd : ∀ t ∈ Icc 0 (integralClock w a b),
      HasDerivWithinAt U (w (U t))⁻¹ (Icc 0 (integralClock w a b)) t :=
    fun t ht => hasDerivWithinAt_clockInverse hab.le hw hm hb hc hp ht
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hpos)).mpr
  constructor
  · intro t ht
    exact (hd t ht).differentiableWithinAt
  · have hcomp : ContinuousOn (fun t => w (U t)) (Icc 0 (integralClock w a b)) :=
      hc.comp (continuous_intervalInverse e hτ).continuousOn
        (fun t _ => intervalInverse_mem e hτ t)
    apply (hcomp.inv₀ (fun t _ => ne_of_gt (hp _ (intervalInverse_mem e hτ t)))).congr
    intro t ht
    exact (hd t ht).derivWithin (uniqueDiffOn_Icc hpos t ht)

/-- [internal] The real inverse clock takes values in the original label interval. -/
theorem clockInverse_mem {w : ℝ → ℝ} {a b m M t : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b) (hm : 0 < m)
    (hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M) :
    clockInverse hab hw hm hb t ∈ Icc a b :=
  intervalInverse_mem _ _ t

/-- [internal] Clock inversion recovers every original label, including endpoints. -/
@[simp] theorem clockInverse_integralClock {w : ℝ → ℝ} {a b m M x : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b) (hm : 0 < m)
    (hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M) (hx : x ∈ Icc a b) :
    clockInverse hab hw hm hb (integralClock w a x) = x := by
  simpa only [clockInverse, clockOrderIso_apply] using
    intervalInverse_apply_apply (clockOrderIso hab hw hm hb)
      (integralClock_nonneg_end hab hw hm hb) ⟨x, hx⟩

/-- [internal] Integration recovers every point in the closed clock image. -/
@[simp] theorem integralClock_clockInverse {w : ℝ → ℝ} {a b m M t : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b) (hm : 0 < m)
    (hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M)
    (ht : t ∈ Icc 0 (integralClock w a b)) :
    integralClock w a (clockInverse hab hw hm hb t) = t := by
  unfold clockInverse
  change integralClock w a
    (intervalInverse (clockOrderIso hab hw hm hb) _ (⟨t, ht⟩ : Icc 0 (integralClock w a b))) = t
  rw [intervalInverse_apply]
  simpa only [clockOrderIso_apply] using
    congrArg Subtype.val ((clockOrderIso hab hw hm hb).apply_symm_apply ⟨t, ht⟩)

/-- [internal] The inverse clock starts at the original initial label. -/
@[simp] theorem clockInverse_zero {w : ℝ → ℝ} {a b m M : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b) (hm : 0 < m)
    (hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M) :
    clockInverse hab hw hm hb 0 = a := by
  simpa only [integralClock_self] using
    clockInverse_integralClock hab hw hm hb (left_mem_Icc.mpr hab)

/-- [internal] The inverse clock ends at the original final label. -/
@[simp] theorem clockInverse_end {w : ℝ → ℝ} {a b m M : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b) (hm : 0 < m)
    (hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M) :
    clockInverse hab hw hm hb (integralClock w a b) = b :=
  clockInverse_integralClock hab hw hm hb (right_mem_Icc.mpr hab)

/-- [internal] A level label with speed `w / lam` has speed `lam⁻¹` in clock
time. This is the second derivative identity required for a clock cylinder. -/
theorem hasDerivWithinAt_curve_clock {v w lam : ℝ → ℝ} {a b m M t : ℝ}
    (hab : a ≤ b) (hw : IntervalIntegrable w volume a b) (hm : 0 < m)
    (hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M)
    (hc : ContinuousOn w (Icc a b)) (hp : ∀ x ∈ Icc a b, 0 < w x)
    (hv : ∀ x ∈ Icc a b, HasDerivWithinAt v (w x / lam x) (Icc a b) x)
    (ht : t ∈ Icc 0 (integralClock w a b)) :
    HasDerivWithinAt (fun t => v (clockInverse hab hw hm hb t))
      (lam (clockInverse hab hw hm hb t))⁻¹ (Icc 0 (integralClock w a b)) t := by
  have hU := hasDerivWithinAt_clockInverse hab hw hm hb hc hp ht
  have hd := (hv _ (clockInverse_mem hab hw hm hb)).scomp t hU
    (fun _ _ => clockInverse_mem hab hw hm hb)
  have hne : w (clockInverse hab hw hm hb t) ≠ 0 :=
    ne_of_gt (hp _ (clockInverse_mem hab hw hm hb))
  convert hd using 1 <;>
    simp only [Function.comp_def, smul_eq_mul, div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ hne, one_mul]

/-- [internal] A C¹ level label remains C¹ after clock parametrization. Together
with `hasDerivWithinAt_curve_clock` and `hasDerivWithinAt_clockInverse`, this
supplies the C¹ and rate fields of a clock-cylinder construction. -/
theorem contDiffOn_curve_clock {v w : ℝ → ℝ} {a b m M : ℝ}
    (hab : a < b) (hw : IntervalIntegrable w volume a b) (hm : 0 < m)
    (hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M)
    (hc : ContinuousOn w (Icc a b)) (hp : ∀ x ∈ Icc a b, 0 < w x)
    (hv : ContDiffOn ℝ 1 v (Icc a b)) :
    ContDiffOn ℝ 1 (fun t => v (clockInverse hab.le hw hm hb t))
      (Icc 0 (integralClock w a b)) := by
  simpa only [Function.comp_def] using hv.comp
    (contDiffOn_clockInverse hab hw hm hb hc hp) (fun _ _ => clockInverse_mem hab.le hw hm hb)

/-- [internal] A C¹ level graph admits clock parametrizations with exactly the
two cylinder rates and both endpoint identities. Compact density bounds are
derived, not assumed. No constants are required uniformly beyond this compact
graph. A graph theorem supplies `hv`, `hr`, and `hspeed` to this helper. -/
theorem exists_clockParametrization_of_levelGraph
    {r nu lam : ℝ → ℝ → ℝ} {v : ℝ → ℝ} {a b ρ : ℝ}
    (hab : a < b) (hv : ContDiffOn ℝ 1 v (Icc a b))
    (hr : ∀ u ∈ Icc a b, r u (v u) = ρ)
    (hc : ContinuousOn (fun u => -nu u (v u)) (Icc a b))
    (hn : ∀ u ∈ Icc a b, nu u (v u) < 0)
    (hspeed : ∀ u ∈ Icc a b,
      HasDerivWithinAt v (-nu u (v u) / lam u (v u)) (Icc a b) u) :
    ∃ T > 0, T = integralClock (fun u => -nu u (v u)) a b ∧
      ∃ U V : ℝ → ℝ, ContDiffOn ℝ 1 U (Icc 0 T) ∧ ContDiffOn ℝ 1 V (Icc 0 T) ∧
        U 0 = a ∧ U T = b ∧ V 0 = v a ∧ V T = v b ∧
        ∀ t ∈ Icc 0 T, U t ∈ Icc a b ∧ V t = v (U t) ∧ r (U t) (V t) = ρ ∧
          HasDerivWithinAt U (-nu (U t) (V t))⁻¹ (Icc 0 T) t ∧
          HasDerivWithinAt V (lam (U t) (V t))⁻¹ (Icc 0 T) t := by
  let w := fun u => -nu u (v u)
  have hp : ∀ u ∈ Icc a b, 0 < w u := fun u hu => neg_pos.mpr (hn u hu)
  obtain ⟨m, M, hm, -, hbnd⟩ := exists_pos_bounds_of_continuousOn hab.le hc hp
  have hw : IntervalIntegrable w volume a b := hc.intervalIntegrable_of_Icc hab.le
  have hb : ∀ᵐ s ∂volume.restrict (Icc a b), m ≤ w s ∧ w s ≤ M :=
    ae_restrict_of_forall_mem measurableSet_Icc hbnd
  let T := integralClock w a b
  let U := clockInverse hab.le hw hm hb
  let V := fun t => v (U t)
  have hT : 0 < T := by
    have h := strictMonoOn_integralClock hab.le hw hm hb
      (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
    simpa only [integralClock_self] using h
  have hU₀ : U 0 = a := clockInverse_zero hab.le hw hm hb
  have hUT : U T = b := clockInverse_end hab.le hw hm hb
  refine ⟨T, hT, rfl, U, V, contDiffOn_clockInverse hab hw hm hb hc hp,
    contDiffOn_curve_clock hab hw hm hb hc hp hv, hU₀, hUT, ?_, ?_, ?_⟩
  · exact congrArg v hU₀
  · exact congrArg v hUT
  · intro t ht
    have hmem : U t ∈ Icc a b := clockInverse_mem hab.le hw hm hb
    refine ⟨hmem, rfl, hr _ hmem, ?_, ?_⟩
    · exact hasDerivWithinAt_clockInverse hab.le hw hm hb hc hp ht
    · exact hasDerivWithinAt_curve_clock hab.le hw hm hb hc hp hspeed ht

end EmcsfAcExtension.Global.Level
