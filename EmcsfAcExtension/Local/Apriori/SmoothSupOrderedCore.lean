module

public import EmcsfAcExtension.Local.Apriori.SmoothSupKernel

/-! # Positive ordered characteristic kernels

Local analytic forms of the ordered-kernel arguments for the Apriori layer.
Only nonnegative integrals are exchanged; infinite input masses are permitted.
The radius factor is retained until the characteristic order has been integrated.
The analytic proofs agree with the landed Stability kernels, without importing
that downstream layer (internal project record).
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The radial moment keeps the vanishing factor when multiplied by its
primitive radius. The coefficient is exactly one, uniformly for `0 ≤ p ≤ 1`.
All radii and separation bounds are explicit. -/
theorem smooth_radius_power_product_aux {r s L a p : ℝ}
    (hr : 0 < r) (hrL : r ≤ L) (hs : 0 ≤ s) (hsa : s ≤ a)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    r * (s / r) ^ p ≤ L ^ (1 - p) * a ^ p := by
  have heq : r * (s / r) ^ p = r ^ (1 - p) * s ^ p := by
    rw [Real.div_rpow hs hr.le, Real.rpow_sub hr 1 p, Real.rpow_one]
    ring
  rw [heq]
  exact mul_le_mul
    (Real.rpow_le_rpow hr.le hrL (sub_nonneg.mpr hp1))
    (Real.rpow_le_rpow hs hsa hp0) (Real.rpow_nonneg hs p)
    (Real.rpow_nonneg (hr.le.trans hrL) (1 - p))

/-- Exact power arithmetic in the scalar-source coefficient.
The constants `64`, `4`, and `256` are universal and the length power is
`-2-p`, as required by scaling. -/
theorem smooth_ordered_coefficient_aux {L ε p : ℝ} (hL : 0 < L) :
    (64 * ε / L ^ 3) * 4 * L ^ (1 - p) = 256 * ε * L ^ (-p - 2) := by
  have hp : L ^ (1 - p) / L ^ (3 : ℝ) = L ^ (-p - 2) := by
    rw [← Real.rpow_sub hL]
    congr 1
    ring
  norm_num at hp
  calc
    _ = 256 * ε * (L ^ (1 - p) / L ^ 3) := by ring
    _ = _ := by rw [hp]

/-- A moment majorant retains its ordered kernel after multiplication by
the primitive radius and a second label function. The exact coefficient
is `4 * B`, with no dependence on the functions, sets, or interval lengths.
This is an internal analytic helper, not a graph-node theorem. -/
theorem smooth_integral_moment_product_aux
    {I : Set ℝ} {E : ℝ → Set ℝ} {R : ℝ → ℝ} {q P : ℝ → ℝ → ℝ}
    {y : ℝ → ℂ} {K J : ℝ → ℝ≥0∞} {B : ℝ}
    (hI : MeasurableSet I) (hE : ∀ w ∈ I, MeasurableSet (E w)) (hB : 0 ≤ B)
    (hR : ∀ w ∈ I, 0 ≤ R w)
    (_hq : ∀ w ∈ I, ∀ s ∈ E w, 0 ≤ q w s)
    (_hP : ∀ w ∈ I, ∀ s ∈ E w, 0 ≤ P w s)
    (hk : ∀ w ∈ I, AEMeasurable (fun s => ENNReal.ofReal (q w s) * K s)
      (volume.restrict (E w)))
    (hmoment : ∀ w ∈ I, ENNReal.ofReal ‖y w‖ ≤
      ENNReal.ofReal 4 * ∫⁻ s in E w, ENNReal.ofReal (q w s) * K s)
    (hpower : ∀ w ∈ I, ∀ s ∈ E w, R w * q w s ≤ B * P w s) :
    (∫⁻ w in I, ENNReal.ofReal (R w) * ENNReal.ofReal ‖y w‖ * J w) ≤
      ENNReal.ofReal (4 * B) * ∫⁻ w in I, ∫⁻ s in E w,
        ENNReal.ofReal (P w s) * K s * J w := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' hI
  intro w hw
  have hcm : (∫⁻ s in E w,
      (ENNReal.ofReal (R w) * ENNReal.ofReal 4) *
        (ENNReal.ofReal (q w s) * K s) * J w) =
      (ENNReal.ofReal (R w) * ENNReal.ofReal 4) *
        (∫⁻ s in E w, ENNReal.ofReal (q w s) * K s) * J w := by
    have hmeas : AEMeasurable (fun s => (ENNReal.ofReal (R w) * ENNReal.ofReal 4) *
        (ENNReal.ofReal (q w s) * K s)) (volume.restrict (E w)) := by
      simpa only [Pi.mul_apply] using! aemeasurable_const.mul (hk w hw)
    rw [lintegral_mul_const'' _ hmeas,
      lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  calc
    _ ≤ ENNReal.ofReal (R w) *
        (ENNReal.ofReal 4 * ∫⁻ s in E w, ENNReal.ofReal (q w s) * K s) * J w :=
      mul_le_mul' (mul_le_mul' le_rfl (hmoment w hw)) le_rfl
    _ = ∫⁻ s in E w, (ENNReal.ofReal (R w) * ENNReal.ofReal 4) *
        (ENNReal.ofReal (q w s) * K s) * J w := by rw [hcm]; ac_rfl
    _ ≤ ∫⁻ s in E w, ENNReal.ofReal (4 * B) *
        (ENNReal.ofReal (P w s) * K s * J w) := by
      apply setLIntegral_mono' (hE w hw)
      intro s hs
      have hpow := ENNReal.ofReal_le_ofReal (hpower w hw s hs)
      rw [ENNReal.ofReal_mul (hR w hw), ENNReal.ofReal_mul hB] at hpow
      calc
        _ = ENNReal.ofReal 4 * (ENNReal.ofReal (R w) * ENNReal.ofReal (q w s)) *
            K s * J w := by ac_rfl
        _ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal B * ENNReal.ofReal (P w s)) * K s * J w :=
          mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hpow) le_rfl) le_rfl
        _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]; ac_rfl
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The positive ordered area kernel before either outer integration.
The numerator has the natural primitive order `u ≤ s ≤ w ≤ v`. -/
@[expose] noncomputable def smoothOrderedKernel (p : ℝ) (K J : ℝ → ℝ≥0∞) (u v : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((v - u) ^ (-p - 2)) * ∫⁻ w in Icc u v, ∫⁻ s in Icc u w,
    ENNReal.ofReal ((w - s) ^ p) * K s * J w

private theorem measurable_ordered_inner (p v : ℝ) {K J : ℝ → ℝ≥0∞}
    (hK : Measurable K) (hJ : Measurable J) :
    Measurable (fun s => ∫⁻ w in Icc s v, ENNReal.ofReal ((w - s) ^ p) * K s * J w) := by
  have hset : MeasurableSet {q : ℝ × ℝ | q.1 ≤ q.2 ∧ q.2 ≤ v} :=
    (measurableSet_le measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hbase : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal ((q.2 - q.1) ^ p) * K q.1 * J q.2) := by fun_prop
  have hm := hbase.indicator hset
  convert hm.lintegral_prod_right' (ν := (volume : Measure ℝ)) using 1
  funext s
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro w
  rfl

/-- Swapping the two inner ordered variables preserves the positive kernel.
No finiteness assumption on either input is needed. -/
theorem smooth_ordered_inner_swap_aux {p u v : ℝ} {K J : ℝ → ℝ≥0∞}
    (hK : Measurable K) (hJ : Measurable J) :
    (∫⁻ w in Icc u v, ∫⁻ s in Icc u w,
      ENNReal.ofReal ((w - s) ^ p) * K s * J w) =
    ∫⁻ s in Icc u v, ∫⁻ w in Icc s v,
      ENNReal.ofReal ((w - s) ^ p) * K s * J w := by
  exact (lintegral_lintegral_swap_triangle
    (F := fun q => ENNReal.ofReal ((q.2 - q.1) ^ p) * K q.1 * J q.2)
    (a := u) (b := v) (by fun_prop)).symm

/-- The landed density agrees with its local triangular integral when
`0 ≤ v ≤ T`. The outer truncation introduces no additional terms. -/
theorem smooth_ordered_density_eq_triangle_aux {p T v : ℝ} {K J : ℝ → ℝ≥0∞}
    (hK : Measurable K) (hJ : Measurable J) (_hv : 0 ≤ v) (hvT : v ≤ T) :
    orderedKernelDensity p T K J univ v =
      ∫⁻ s in Icc 0 v, ∫⁻ w in Icc s v,
        K s * J w * ENNReal.ofReal (orderedPowerKernel p s w v) := by
  let F := fun q : ℝ × ℝ => K q.1 * J q.2 *
    ENNReal.ofReal (orderedPowerKernel p q.1 q.2 v)
  have hF : Measurable F := by unfold F orderedPowerKernel; fun_prop
  have hsub : triangle 0 v ⊆ Icc 0 T ×ˢ Icc 0 T := by
    intro q hq
    exact ⟨⟨hq.1, hq.2.1.trans (hq.2.2.trans hvT)⟩,
      ⟨hq.1.trans hq.2.1, hq.2.2.trans hvT⟩⟩
  unfold orderedKernelDensity
  simp only [inter_univ]
  change (∫⁻ s in Icc 0 T, ∫⁻ w in Icc 0 T, (triangle 0 v).indicator F (s, w)) = _
  rw [← lintegral_prod _ ((hF.indicator (measurableSet_triangle 0 v)).aemeasurable),
    Measure.prod_restrict, lintegral_indicator (measurableSet_triangle 0 v),
    Measure.restrict_restrict (measurableSet_triangle 0 v), inter_eq_left.mpr hsub]
  exact lintegral_triangle_eq_lintegral_lintegral hF

private theorem lintegral_lower_outer_power_le {p s v : ℝ} (hp : 0 ≤ p)
    (hs : 0 ≤ s) (hsv : s < v) :
    (∫⁻ u in Icc 0 s, ENNReal.ofReal ((v - u) ^ (-p - 2))) ≤
      ENNReal.ofReal ((v - s) ^ (-(1 + p))) := by
  have hp' : -1 < p := lt_of_lt_of_le (by norm_num) hp
  have hc : ContinuousOn (fun u : ℝ => (v - u) ^ (-p - 2)) (uIcc 0 s) := by
    apply (continuousOn_const.sub continuousOn_id).rpow_const
    intro u hu
    rw [uIcc_of_le hs] at hu
    exact Or.inl (sub_pos.mpr (hu.2.trans_lt hsv)).ne'
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hs).1
    (hc.intervalIntegrable (μ := volume))
  have hn : 0 ≤ᵐ[volume.restrict (Icc 0 s)] (fun u : ℝ => (v - u) ^ (-p - 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact Real.rpow_nonneg (sub_nonneg.mpr (hu.2.trans hsv.le)) _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hs]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_reflected_rpow_eq hp' hs hsv]
  have htail : 0 ≤ (v - 0) ^ (-(p + 1)) :=
    Real.rpow_nonneg (sub_nonneg.mpr (hs.trans hsv.le)) _
  have hhead : 0 ≤ (v - s) ^ (-(p + 1)) := Real.rpow_nonneg (sub_nonneg.mpr hsv.le) _
  calc
    _ ≤ (v - s) ^ (-(p + 1)) / (p + 1) :=
      div_le_div_of_nonneg_right (sub_le_self _ htail) (by linarith only [hp])
    _ ≤ (v - s) ^ (-(p + 1)) := div_le_self hhead (by linarith only [hp])
    _ = _ := by rw [add_comm p 1]

/-- Integrating the lower outer endpoint of the full kernel is bounded by
the landed ordered density. The exact discarded factor `1/(1+p)` is at
most one for `p ≥ 0`; the bound is uniform in all endpoints and inputs. -/
theorem smooth_ordered_kernel_slice_aux {p T v : ℝ} {K J : ℝ → ℝ≥0∞}
    (hp : 0 ≤ p) (hK : Measurable K) (hJ : Measurable J)
    (hv : 0 ≤ v) (hvT : v ≤ T) :
    (∫⁻ u in Icc 0 v, smoothOrderedKernel p K J u v) ≤
      orderedKernelDensity p T K J univ v := by
  let H := fun s => ∫⁻ w in Icc s v, ENNReal.ofReal ((w - s) ^ p) * K s * J w
  have hH : Measurable H := measurable_ordered_inner p v hK hJ
  have hweight : Measurable (fun u : ℝ => ENNReal.ofReal ((v - u) ^ (-p - 2))) := by
    fun_prop
  have hswap := lintegral_lintegral_swap_triangle (a := 0) (b := v)
    (F := fun q => ENNReal.ofReal ((v - q.1) ^ (-p - 2)) * H q.2)
    (by fun_prop)
  have heq : (∫⁻ u in Icc 0 v, smoothOrderedKernel p K J u v) =
      ∫⁻ s in Icc 0 v, ∫⁻ u in Icc 0 s,
        ENNReal.ofReal ((v - u) ^ (-p - 2)) * H s := by
    rw [← hswap]
    apply lintegral_congr
    intro u
    rw [smoothOrderedKernel, smooth_ordered_inner_swap_aux hK hJ]
    dsimp only [Prod.fst, Prod.snd]
    exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
  rw [heq, smooth_ordered_density_eq_triangle_aux hK hJ hv hvT]
  have hne : ∀ᵐ s : ℝ, s ≠ v := by simp [ae_iff, measure_singleton]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with s hs hne
  have hsv : s < v := lt_of_le_of_ne hs.2 hne
  calc
    _ = (∫⁻ u in Icc 0 s, ENNReal.ofReal ((v - u) ^ (-p - 2))) * H s :=
      lintegral_mul_const'' _ hweight.aemeasurable
    _ ≤ ENNReal.ofReal ((v - s) ^ (-(1 + p))) * H s :=
      mul_le_mul' (lintegral_lower_outer_power_le hp hs.1 hsv) le_rfl
    _ = ∫⁻ w in Icc s v, K s * J w *
        ENNReal.ofReal (orderedPowerKernel p s w v) := by
      dsimp only [H]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro w
      have hpow : (v - s) ^ (-(1 + p)) * (w - s) ^ p =
          orderedPowerKernel p s w v := by
        rw [orderedPowerKernel, Real.rpow_neg (sub_nonneg.mpr hsv.le)]
        ring
      calc
        _ = (ENNReal.ofReal ((v - s) ^ (-(1 + p))) *
            ENNReal.ofReal ((w - s) ^ p)) * K s * J w := by ac_rfl
        _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (sub_nonneg.mpr hsv.le) _), hpow]
          ac_rfl

/-- The truncated incoming integration keeps its precise reflected cutoff.
Only the middle input is bounded by `B`; the opposite label is kept under
the integral. The coefficient is exactly one, uniformly in all endpoints,
inputs and positive `p`. The sup bound `B` is finite; no label integral
is assumed finite. -/
theorem smooth_ordered_reflected_cutoff_aux {p T u v : ℝ} (hp : 0 < p)
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T)
    {K J : ℝ → ℝ≥0∞} {B : ℝ≥0∞} (hK : Measurable K) (hJ : Measurable J)
    (hJB : ∀ w ∈ Icc 0 T, J w ≤ B) (hB : B ≠ ⊤) :
    (∫⁻ s in Icc 0 u, smoothOrderedKernel p K J s v) ≤
      (∫⁻ a in Icc 0 v, K a * ENNReal.ofReal ((v - a) ^ (p + 1) *
        ∫ s in 0..min u a, (v - s) ^ (-p - 2))) * B := by
  classical
  let W := fun s : ℝ => ENNReal.ofReal ((v - s) ^ (-p - 2))
  let H := fun a : ℝ => ∫⁻ w in Icc a v,
    ENNReal.ofReal ((w - a) ^ p) * K a * J w
  have hW : Measurable W := by dsimp only [W]; fun_prop
  have hH : Measurable H := measurable_ordered_inner p v hK hJ
  have hHb (a : ℝ) (ha : a ∈ Icc 0 v) :
      H a ≤ K a * ENNReal.ofReal ((v - a) ^ (p + 1)) * B := by
    rcases eq_or_lt_of_le ha.2 with rfl | hav
    · simp [H, Real.zero_rpow (by linarith only [hp] : p + 1 ≠ 0)]
    have hpow : (v - a) ^ p * (v - a) = (v - a) ^ (p + 1) := by
      rw [Real.rpow_add (sub_pos.mpr hav), Real.rpow_one]
    calc
      H a ≤ ∫⁻ w in Icc a v, ENNReal.ofReal ((v - a) ^ p) * K a * B := by
        apply setLIntegral_mono' measurableSet_Icc
        intro w hw
        apply mul_le_mul'
          (mul_le_mul' (ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow (sub_nonneg.mpr hw.1)
              (sub_le_sub_right hw.2 a) hp.le)) le_rfl)
          (hJB w ⟨ha.1.trans hw.1, hw.2.trans hvT⟩)
      _ = _ := by
        rw [setLIntegral_const, Real.volume_Icc]
        calc
          _ = K a * (ENNReal.ofReal ((v - a) ^ p) * ENNReal.ofReal (v - a)) * B :=
            by ac_rfl
          _ = _ := by rw [← ENNReal.ofReal_mul
            (Real.rpow_nonneg (sub_nonneg.mpr hav.le) _), hpow]
  have heq : (∫⁻ s in Icc 0 u, smoothOrderedKernel p K J s v) =
      ∫⁻ a in Icc 0 v, ∫⁻ s in Icc 0 a, (Icc 0 u).indicator
        (fun s => W s * H a) s := by
    rw [← lintegral_lintegral_swap_triangle
      (F := fun q : ℝ × ℝ => (Icc 0 u).indicator (fun s => W s * H q.2) q.1)
      (by
        have hm : Measurable (fun q : ℝ × ℝ => W q.1 * H q.2) := by fun_prop
        exact hm.indicator (measurableSet_Icc.preimage measurable_fst))]
    calc
      _ = ∫⁻ s in Icc 0 u, W s * ∫⁻ a in Icc s v, H a := by
        apply lintegral_congr
        intro s
        rw [smoothOrderedKernel, smooth_ordered_inner_swap_aux hK hJ]
      _ = ∫⁻ s in Icc 0 v, (Icc 0 u).indicator
          (fun s => W s * ∫⁻ a in Icc s v, H a) s := by
        rw [lintegral_indicator measurableSet_Icc,
          Measure.restrict_restrict measurableSet_Icc,
          inter_eq_left.mpr (Icc_subset_Icc le_rfl huv)]
      _ = _ := by
        apply lintegral_congr
        intro s
        by_cases hs : s ∈ Icc 0 u
        · simp only [indicator_of_mem hs]
          exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
        · simp only [indicator_of_notMem hs, lintegral_zero]
  rw [heq]
  have hne : ∀ᵐ a ∂volume.restrict (Icc 0 v), a ≠ v :=
    ae_restrict_of_ae (by simp [ae_iff])
  calc
    _ ≤ ∫⁻ a in Icc 0 v, K a * ENNReal.ofReal ((v - a) ^ (p + 1) *
        ∫ s in 0..min u a, (v - s) ^ (-p - 2)) * B := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, hne] with a ha hav
      have hm : 0 ≤ min u a := le_min hu ha.1
      have hmv : min u a < v := (min_le_right u a).trans_lt (lt_of_le_of_ne ha.2 hav)
      have hi : IntegrableOn (fun s : ℝ => (v - s) ^ (-p - 2)) (Icc 0 (min u a)) :=
        (ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id)
          (fun s hs => Or.inl (sub_pos.mpr (hs.2.trans_lt hmv)).ne')).integrableOn_Icc
      rw [lintegral_indicator measurableSet_Icc,
        Measure.restrict_restrict measurableSet_Icc]
      have hinter : Icc 0 u ∩ Icc 0 a = Icc 0 (min u a) := by ext s; simp; tauto
      rw [hinter, lintegral_mul_const'' _ hW.aemeasurable]
      apply (mul_le_mul' le_rfl (hHb a ha)).trans_eq
      have hwint : (∫⁻ s in Icc 0 (min u a), W s) =
          ENNReal.ofReal (∫ s in 0..min u a, (v - s) ^ (-p - 2)) := by
        rw [intervalIntegral.integral_of_le hm, restrict_Ioc_eq_restrict_Icc]
        apply (ofReal_integral_eq_lintegral_ofReal hi ?_).symm
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        exact Real.rpow_nonneg (sub_nonneg.mpr (hs.2.trans hmv.le)) _
      rw [hwint, ENNReal.ofReal_mul
        (Real.rpow_nonneg (sub_nonneg.mpr ha.2) _)]
      ac_rfl
    _ = _ := lintegral_mul_const' _ _ hB

end EmcsfAcExtension.Local
