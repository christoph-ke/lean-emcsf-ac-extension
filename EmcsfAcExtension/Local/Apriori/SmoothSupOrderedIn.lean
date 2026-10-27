module

public import EmcsfAcExtension.Local.Apriori.SmoothSupOrdered
public import EmcsfAcExtension.Local.Apriori.SmoothSupHardy
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Incoming curvature with the outgoing radial moment

The scalar primitive for the `k` transport runs from the point to its
incoming axis endpoint. Its positive ordered kernel is reflected with both
label functions, retaining the outgoing weight of internal project record (M3–M5).
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The reflected ordered kernel before outer integration. Its inner
order is `u ≤ s ≤ a ≤ v`, with the outgoing label at `a`. -/
@[expose] noncomputable def smoothIncomingOrderedKernel
    (p : ℝ) (J K : ℝ → ℝ≥0∞) (u v : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((v - u) ^ (-p - 2)) * ∫⁻ s in Icc u v, ∫⁻ a in Icc s v,
    ENNReal.ofReal ((a - s) ^ p) * J a * K s

/-- The incoming scalar curvature density has the universal ordered
coefficient `1024 ε`. The constant is independent of all fields, data,
derivative sizes and positive exponents in the stated damping range. -/
theorem smooth_incoming_ordered_pointwise_aux
    {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h)
    {p u v : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 - 16 * ε ^ 2)
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖(S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
      curvScalarIn e (triangle 0 T) S u v‖ₑ ≤
      ENNReal.ofReal (1024 * ε) * smoothIncomingOrderedKernel p
        ((Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S)))
        ((Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S))) u v := by
  classical
  let J := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))
  let K := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S))
  have hJ : Measurable J := measurable_indicator_outEnv
    (continuousOn_jC1_aux hset.pos hset.c1)
  have hp1 : p ≤ 1 := hp.trans (sub_le_self _ (by positivity : 0 ≤ 16 * ε ^ 2))
  have hε := hset.eps_nonneg
  have hL : 0 < v - u := sub_pos.mpr huv
  have hR (s : ℝ) (hs : s ∈ Ico u v) : 0 < S.r s v ∧ S.r s v ≤ v - u :=
    ⟨hset.c1.r_pos (s, v) ⟨hu.trans hs.1, hs.2.le, hvT⟩ hs.2,
      ((smooth_radius_bounds_aux hset ⟨hu.trans hs.1, hs.2.le, hvT⟩).2).trans
        (sub_le_sub_left hs.1 v)⟩
  have hρ (s : ℝ) (hs : s ∈ Ico u v) (a : ℝ) (ha : a ∈ Icc s v) :
      0 ≤ S.r s a ∧ S.r s a ≤ a - s := by
    have hb := smooth_radius_bounds_aux hset ⟨hu.trans hs.1, ha.1, ha.2.trans hvT⟩
    exact ⟨(div_nonneg (sub_nonneg.mpr ha.1) (by norm_num)).trans hb.1, hb.2⟩
  have hj (s : ℝ) (hs : s ∈ Ico u v) :
      AEMeasurable (fun a => ENNReal.ofReal ((S.r s a / S.r s v) ^ p) * J a)
        (volume.restrict (Icc s v)) := by
    have hrr : ContinuousOn (fun a => S.r s a / S.r s v) (Icc s v) :=
      (hset.c1.c1_r.continuousOn.comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun a ha => ⟨hu.trans hs.1, ha.1, ha.2.trans hvT⟩)).div_const _
    exact ((ENNReal.continuous_ofReal.comp_continuousOn
      ((Real.continuous_rpow_const hp0.le).comp_continuousOn hrr)).aemeasurable
        measurableSet_Icc).mul hJ.aemeasurable.restrict
  have hmoment (s : ℝ) (hs : s ∈ Ico u v) :
      ENNReal.ofReal ‖S.theta s v / (S.lam s v : ℂ)‖ ≤
        ENNReal.ofReal 4 * ∫⁻ a in Icc s v,
          ENNReal.ofReal ((S.r s a / S.r s v) ^ p) * J a := by
    have hm := ENNReal.ofReal_le_ofReal
      (smooth_outgoing_radial_moment_aux hset hp0 hp (hu.trans hs.1) hs.2 hvT)
    rw [intervalIntegral.integral_of_le hs.2.le] at hm
    have hnorm := enorm_integral_le_lintegral_enorm
      (fun a => (S.r s a / S.r s v) ^ p *
        (2 * (outEnv 0 (jC1 (triangle 0 T) S) a).toReal))
      (μ := volume.restrict (Ioc s v))
    have hnonneg : 0 ≤ ∫ a in Ioc s v,
        (S.r s a / S.r s v) ^ p *
          (2 * (outEnv 0 (jC1 (triangle 0 T) S) a).toReal) := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      exact mul_nonneg
        (Real.rpow_nonneg (div_nonneg (hρ s hs a ⟨ha.1.le, ha.2⟩).1 (hR s hs).1.le) _)
        (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hnorm
    apply (hm.trans hnorm).trans
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      restrict_Ioc_eq_restrict_Icc]
    apply setLIntegral_mono' measurableSet_Icc
    intro a ha
    have hq : 0 ≤ (S.r s a / S.r s v) ^ p :=
      Real.rpow_nonneg (div_nonneg (hρ s hs a ha).1 (hR s hs).1.le) _
    have haT : a ∈ Icc 0 T := ⟨hu.trans (hs.1.trans ha.1), ha.2.trans hvT⟩
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hq (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)),
      ENNReal.ofReal_mul hq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_toReal (outEnv_ne_top_of_continuousOn
        (continuousOn_jC1_aux hset.pos hset.c1) haT)]
    dsimp only [J]
    rw [indicator_of_mem haT]
    calc
      _ ≤ ENNReal.ofReal ((S.r s a / S.r s v) ^ p) *
          (ENNReal.ofReal 4 * outEnv 0 (jC1 (triangle 0 T) S) a) :=
        mul_le_mul' le_rfl (mul_le_mul' (by norm_num) le_rfl)
      _ = _ := by ac_rfl
  have hm := smooth_integral_moment_product_aux
    (I := Ico u v) (E := fun s => Icc s v) (R := fun s => S.r s v)
    (q := fun s a => (S.r s a / S.r s v) ^ p) (P := fun s a => (a - s) ^ p)
    (y := fun s => S.theta s v / (S.lam s v : ℂ)) (K := J) (J := K)
    (B := (v - u) ^ (1 - p)) measurableSet_Ico (fun _ _ => measurableSet_Icc)
    (Real.rpow_nonneg hL.le _) (fun s hs => (hR s hs).1.le)
    (fun s hs a ha => Real.rpow_nonneg (div_nonneg (hρ s hs a ha).1 (hR s hs).1.le) p)
    (fun _ _ _ ha => Real.rpow_nonneg (sub_nonneg.mpr ha.1) p) hj hmoment
    (fun s hs a ha => smooth_radius_power_product_aux (hR s hs).1 (hR s hs).2
      (hρ s hs a ha).1 (hρ s hs a ha).2 hp0.le hp1)
  let c := ((S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2) * (S.r u v : ℂ)⁻¹
  have hc : ‖c‖ₑ ≤ ENNReal.ofReal (256 * ε / (v - u) ^ 3) := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (smooth_scalar_primitive_coefficients_aux hset hu huv hvT).2
  have hprimitive : ‖(S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
      curvScalarIn e (triangle 0 T) S u v‖ₑ ≤
      ‖c‖ₑ * ∫⁻ s in Ico u v, ENNReal.ofReal (S.r s v) *
        ENNReal.ofReal ‖S.theta s v / (S.lam s v : ℂ)‖ * K s := by
    rw [curvScalarIn, mul_neg, enorm_neg, intervalIntegral.integral_of_le huv.le,
      ← mul_assoc, enorm_mul, restrict_Ioc_eq_restrict_Icc,
      ← restrict_Ico_eq_restrict_Icc]
    apply mul_le_mul' le_rfl
    apply (enorm_integral_le_lintegral_enorm _).trans
    apply setLIntegral_mono' measurableSet_Ico
    intro s hs
    rw [← ofReal_norm, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hR s hs).1, RCLike.norm_conj]
    rw [ENNReal.ofReal_mul (mul_nonneg (hR s hs).1.le (norm_nonneg _)),
      ENNReal.ofReal_mul (hR s hs).1.le]
    apply mul_le_mul' le_rfl
    dsimp only [K]
    rw [indicator_of_mem (show s ∈ Icc 0 T from
      ⟨hu.trans hs.1, hs.2.le.trans hvT⟩), ofReal_norm]
    exact le_iSup₂_of_le v ⟨hs.2.le, hvT⟩ le_rfl
  apply hprimitive.trans
  apply (mul_le_mul' hc hm).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 256 * ε / (v - u) ^ 3)]
  have hcoeff : (256 * ε / (v - u) ^ 3) * (4 * (v - u) ^ (1 - p)) =
      1024 * ε * (v - u) ^ (-p - 2) := by
    rw [← mul_assoc]
    have he := smooth_ordered_coefficient_aux (ε := 4 * ε) (p := p) hL
    convert he using 1 <;> ring
  rw [hcoeff, ENNReal.ofReal_mul (mul_nonneg (by norm_num) hset.eps_nonneg),
    smoothIncomingOrderedKernel, restrict_Ico_eq_restrict_Icc]
  dsimp only [K, J]
  ac_rfl

/-- Reflection of a nonnegative interval integral, including infinite
integrals. The change of labels has unit Jacobian and exact coefficient one. -/
theorem smooth_lintegral_reflect_aux (f : ℝ → ℝ≥0∞) (a b c : ℝ) :
    (∫⁻ x in Icc (c - b) (c - a), f (c - x)) = ∫⁻ x in Icc a b, f x := by
  have himage : (fun x : ℝ => c - x) '' Icc (c - b) (c - a) = Icc a b := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      constructor <;> linarith only [hx.1, hx.2]
    · intro hy
      refine ⟨c - y, ⟨by linarith only [hy.2], by linarith only [hy.1]⟩, ?_⟩
      ring
  simpa only [himage] using
    (Measure.measurePreserving_sub_left (volume : Measure ℝ) c).setLIntegral_comp_emb
      (Homeomorph.subLeft c).measurableEmbedding f (Icc (c - b) (c - a))

/-- Reflection exchanges both labels in the two ordered kernels. In
particular it does not replace an incoming moment by an outgoing moment
on the same carrier. This identity has no finiteness or constant premise. -/
theorem smooth_incoming_ordered_reflect_aux (p T u v : ℝ) (J K : ℝ → ℝ≥0∞) :
    smoothIncomingOrderedKernel p J K u v =
      smoothOrderedKernel p (fun a => J (T - a)) (fun s => K (T - s))
        (T - v) (T - u) := by
  unfold smoothIncomingOrderedKernel smoothOrderedKernel
  rw [show T - u - (T - v) = v - u by ring]
  congr 1
  rw [← smooth_lintegral_reflect_aux (fun s => ∫⁻ a in Icc s v,
    ENNReal.ofReal ((a - s) ^ p) * J a * K s) u v T]
  apply lintegral_congr
  intro w
  rw [← smooth_lintegral_reflect_aux (fun a =>
    ENNReal.ofReal ((a - (T - w)) ^ p) * J a * K (T - w)) (T - w) v T]
  simp only [sub_sub_cancel]
  apply lintegral_congr
  intro s
  rw [show T - s - (T - w) = w - s by ring]

/-- Integrating the incoming ordered kernel leaves the outgoing L¹
mass and the incoming supremum. The exact coefficient is `1/(1+p)`,
uniform in endpoints and label functions; infinite masses are allowed. -/
theorem smooth_incoming_ordered_sup_aux {p T u : ℝ} (hp : 0 < p)
    (hu : 0 ≤ u) (huT : u ≤ T) {J K : ℝ → ℝ≥0∞} {B : ℝ≥0∞}
    (hJ : Measurable J) (hK : Measurable K)
    (hKB : ∀ s ∈ Icc 0 T, K s ≤ B) :
    (∫⁻ v in Icc u T, smoothIncomingOrderedKernel p J K u v) ≤
      ENNReal.ofReal (1 / (1 + p)) * (∫⁻ a in Icc 0 T, J a) * B := by
  let Jr := fun a => J (T - a)
  let Kr := fun s => K (T - s)
  have hJr : Measurable Jr := by dsimp only [Jr]; fun_prop
  have hKr : Measurable Kr := by dsimp only [Kr]; fun_prop
  have hbound : ∀ s ∈ Icc 0 T, Kr s ≤ B := by
    intro s hs
    apply hKB
    constructor <;> linarith only [hs.1, hs.2]
  have heq : (∫⁻ v in Icc u T, smoothIncomingOrderedKernel p J K u v) =
      ∫⁻ s in Icc 0 (T - u), smoothOrderedKernel p Jr Kr s (T - u) := by
    rw [← smooth_lintegral_reflect_aux (fun v =>
      smoothIncomingOrderedKernel p J K u v) u T T]
    simp only [sub_self]
    apply lintegral_congr
    intro s
    rw [smooth_incoming_ordered_reflect_aux p T u (T - s), sub_sub_cancel]
  rw [heq]
  have hb := (smooth_ordered_kernel_slice_aux hp.le hJr hKr
    (sub_nonneg.mpr huT) (sub_le_self T hu)).trans
      (smooth_ordered_kernel_sup_aux hp hJr.aemeasurable hbound)
  have hmass : (∫⁻ a in Icc 0 T, Jr a) = ∫⁻ a in Icc 0 T, J a := by
    simpa only [sub_self, sub_zero] using smooth_lintegral_reflect_aux J 0 T T
  rwa [hmass] at hb

/-- Scalar curvature in the outgoing `k` transport has the universal
sup estimate `C ε ‖J‖₁ ‖K‖∞/(1+p)`. The literal constant `1024` is
independent of all data, parameters and positive damping exponents.
This helper supplies the reflected calculation of internal project record (M3–M5). -/
theorem smooth_incoming_curvature_sup_aux {e T ε M p : ℝ}
    {S : Fields} {h : ℝ → ℂ} (hset : AprioriSetting e T ε M S h)
    (hp : 0 < p) (hsmall : p ≤ 1 - 16 * ε ^ 2) {u : ℝ} (hu : u ∈ Icc 0 T) :
    (∫⁻ v in Icc u T,
      ‖S.lam u v * S.xi u v / S.r u v ^ 2 *
        curvScalarIn e (triangle 0 T) S u v‖ₑ) ≤
      ENNReal.ofReal (1024 * ε / (1 + p)) *
        (∫⁻ a in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) a) *
        (⨆ q ∈ triangle 0 T, ‖kC1 e (triangle 0 T) S q.1 q.2‖ₑ) := by
  classical
  let J := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))
  let K := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S))
  let B := ⨆ q ∈ triangle 0 T, ‖kC1 e (triangle 0 T) S q.1 q.2‖ₑ
  have hε := hset.eps_nonneg
  have hJ : Measurable J := measurable_indicator_outEnv
    (continuousOn_jC1_aux hset.pos hset.c1)
  have hK : Measurable K := measurable_indicator_inEnv
    (continuousOn_kC1_aux hset.pos hset.c1)
  have hKB : ∀ a ∈ Icc 0 T, K a ≤ B := by
    intro a ha
    dsimp only [K]
    rw [indicator_of_mem ha]
    apply iSup₂_le
    intro v hv
    exact le_iSup₂_of_le (a, v) ⟨ha.1, hv.1, hv.2⟩ le_rfl
  calc
    _ ≤ ∫⁻ v in Icc u T,
        ENNReal.ofReal (1024 * ε) * smoothIncomingOrderedKernel p J K u v := by
      apply lintegral_mono_ae
      have hne : ∀ᵐ v ∂volume.restrict (Icc u T), u ≠ v :=
        ae_restrict_of_ae (by simp [ae_iff])
      filter_upwards [ae_restrict_mem measurableSet_Icc, hne] with v hv huv
      exact smooth_incoming_ordered_pointwise_aux hset hp hsmall hu.1
        (lt_of_le_of_ne hv.1 huv) hv.2
    _ = ENNReal.ofReal (1024 * ε) *
        ∫⁻ v in Icc u T, smoothIncomingOrderedKernel p J K u v :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (1024 * ε) *
        (ENNReal.ofReal (1 / (1 + p)) * (∫⁻ a in Icc 0 T, J a) * B) :=
      mul_le_mul' le_rfl (smooth_incoming_ordered_sup_aux hp hu.1 hu.2 hJ hK hKB)
    _ = _ := by
      have hmass : (∫⁻ a in Icc 0 T, J a) =
          ∫⁻ a in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) a := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro a ha
        exact indicator_of_mem ha _
      rw [hmass, ← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1024 * ε), mul_one_div]

end EmcsfAcExtension.Local
