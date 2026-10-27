module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import EmcsfAcExtension.Infra.Triangle
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Separated radial exponents on a positive-radius interval

The inner integral of the two moment kernels costs `1 / (q - p)`.
In particular `p = 1/2`, `q = 3/4` costs `4`, without a logarithm of
the minimum radius. This auxiliary calculation is the annular part of K1
in the approved internal project record kernel toolkit.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The two-exponent convolution kernel has the exact universal cost
`1/(q-p)`, independently of the endpoints, weight and minimum radius.
The radius is positive on this annulus; axis endpoints are handled by
the later nonnegative Tonelli integral. -/
theorem stab_separated_radial_kernel_integral_le
    {r w : ℝ → ℝ} {s v p q : ℝ} (hsv : s ≤ v) (hpq : p < q)
    (hr : ContinuousOn r (Icc s v)) (hw : ContinuousOn w (Icc s v))
    (hr0 : ∀ t ∈ Icc s v, 0 < r t)
    (hd : ∀ t ∈ Ioo s v, HasDerivAt r (w t) t) :
    (∫ t in s..v, (r s / r t) ^ q * (r t / r v) ^ p * (w t / r t)) ≤
      (r s / r v) ^ p / (q - p) := by
  have hrs := hr0 s (left_mem_Icc.mpr hsv)
  have hrv := hr0 v (right_mem_Icc.mpr hsv)
  have hq : 0 < q - p := sub_pos.mpr hpq
  have hc := hr.rpow_const (p := p - q) (fun t ht => Or.inl (hr0 t ht).ne')
  have hc' := hr.rpow_const (p := p - q - 1) (fun t ht => Or.inl (hr0 t ht).ne')
  have hi : IntervalIntegrable (fun t => w t * (r t) ^ (p - q - 1)) volume s v :=
    ContinuousOn.intervalIntegrable_of_Icc hsv (hw.mul hc')
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hsv hc
    (fun t ht => (hd t ht).rpow_const (Or.inl (hr0 t ⟨ht.1.le, ht.2.le⟩).ne'))
    (ContinuousOn.intervalIntegrable_of_Icc hsv ((hw.mul continuousOn_const).mul hc'))
  have hFTC' : (p - q) * (∫ t in s..v, w t * (r t) ^ (p - q - 1)) =
      (r v) ^ (p - q) - (r s) ^ (p - q) := by
    rw [← intervalIntegral.integral_const_mul]
    convert hFTC using 1
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have hbound : (∫ t in s..v, w t * (r t) ^ (p - q - 1)) ≤
      (r s) ^ (p - q) / (q - p) := by
    rw [le_div_iff₀ hq]
    have hv0 := Real.rpow_nonneg hrv.le (p - q)
    nlinarith only [hFTC', hv0]
  have heq : (∫ t in s..v,
      (r s / r t) ^ q * (r t / r v) ^ p * (w t / r t)) =
      (r s) ^ q / (r v) ^ p * (∫ t in s..v, w t * (r t) ^ (p - q - 1)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc s v := by simpa only [uIcc_of_le hsv] using ht
    have hrt := hr0 t ht'
    dsimp only
    rw [Real.div_rpow hrs.le hrt.le, Real.div_rpow hrt.le hrv.le,
      Real.rpow_sub hrt, Real.rpow_sub hrt, Real.rpow_one]
    field_simp
  rw [heq]
  calc
    _ ≤ (r s) ^ q / (r v) ^ p * ((r s) ^ (p - q) / (q - p)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (r s / r v) ^ p / (q - p) := by
      rw [Real.div_rpow hrs.le hrv.le]
      have hm : (r s) ^ q * (r s) ^ (p - q) = (r s) ^ p := by
        rw [← Real.rpow_add hrs]
        congr 1
        ring
      field_simp
      exact hm

private theorem lintegral_separated_kernel_le_aux
    {r w : ℝ → ℝ} {s v p q : ℝ} (hsv : s ≤ v) (hpq : p < q)
    (hr : ContinuousOn r (Icc s v)) (hw : ContinuousOn w (Icc s v))
    (hr0 : ∀ t ∈ Icc s v, 0 < r t) (hw0 : ∀ t ∈ Icc s v, 0 ≤ w t)
    (hd : ∀ t ∈ Ioo s v, HasDerivAt r (w t) t) :
    (∫⁻ t in Icc s v, ENNReal.ofReal
      ((r s / r t) ^ q * (r t / r v) ^ p * (w t / r t))) ≤
      ENNReal.ofReal ((r s / r v) ^ p / (q - p)) := by
  let k := fun t : ℝ => (r s / r t) ^ q * (r t / r v) ^ p * (w t / r t)
  have hpos_s := hr0 s ⟨le_rfl, hsv⟩
  have hpos_v := hr0 v ⟨hsv, le_rfl⟩
  have c₁ := (continuousOn_const.div hr (fun t ht => (hr0 t ht).ne')).rpow_const
    (p := q) (fun t ht => Or.inl (div_ne_zero hpos_s.ne' (hr0 t ht).ne'))
  have c₂ := (hr.div_const (r v)).rpow_const (p := p)
    (fun t ht => Or.inl (div_ne_zero (hr0 t ht).ne' hpos_v.ne'))
  have hc : ContinuousOn k (Icc s v) :=
    (c₁.mul c₂).mul (hw.div hr (fun t ht => (hr0 t ht).ne'))
  have hki : IntegrableOn k (Icc s v) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hsv).mp
      (ContinuousOn.intervalIntegrable_of_Icc hsv hc)
  have hk0 : 0 ≤ᵐ[volume.restrict (Icc s v)] k := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (div_nonneg hpos_s.le (hr0 t ht).le) q)
        (Real.rpow_nonneg (div_nonneg (hr0 t ht).le hpos_v.le) p))
      (div_nonneg (hw0 t ht) (hr0 t ht).le)
  have heq : (∫⁻ t in Icc s v, ENNReal.ofReal (k t)) =
      ENNReal.ofReal (∫ t in s..v, k t) := by
    rw [intervalIntegral.integral_of_le hsv, ← integral_Icc_eq_integral_Ioc]
    exact (ofReal_integral_eq_lintegral_ofReal hki hk0).symm
  rw [heq]
  exact ENNReal.ofReal_le_ofReal
    (stab_separated_radial_kernel_integral_le hsv hpq hr hw hr0 hd)

private theorem measurable_separated_kernel_aux {r w : ℝ → ℝ} (b p q : ℝ)
    (hrm : Measurable r) (hwm : Measurable w) :
    Measurable (fun z : ℝ × ℝ => ENNReal.ofReal
      ((r z.1 / r z.2) ^ q * (r z.2 / r b) ^ p * (w z.2 / r z.2))) := by
  have h₁ : Measurable (fun z : ℝ × ℝ => r z.1) := hrm.comp measurable_fst
  have h₂ : Measurable (fun z : ℝ × ℝ => r z.2) := hrm.comp measurable_snd
  have h₃ : Measurable (fun z : ℝ × ℝ => w z.2) := hwm.comp measurable_snd
  exact ENNReal.measurable_ofReal.comp
    ((((h₁.div h₂).pow_const q).mul ((h₂.div_const (r b)).pow_const p)).mul (h₃.div h₂))

private theorem separated_kernel_swap_aux
    {r w : ℝ → ℝ} {J : ℝ → ℝ≥0∞} {a b p q : ℝ}
    (hrm : Measurable r) (hwm : Measurable w) (hJ : Measurable J)
    (hr0 : ∀ t ∈ Icc a b, 0 ≤ r t) (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t) :
    (∫⁻ t in Icc a b, ENNReal.ofReal ((r t / r b) ^ p * (w t / r t)) *
      ∫⁻ s in Icc a t, ENNReal.ofReal ((r s / r t) ^ q) * J s) =
      ∫⁻ s in Icc a b, ∫⁻ t in Icc s b,
        ENNReal.ofReal ((r s / r t) ^ q * (r t / r b) ^ p * (w t / r t)) * J s := by
  let k := fun s t : ℝ => (r s / r t) ^ q * (r t / r b) ^ p * (w t / r t)
  have hkm := measurable_separated_kernel_aux b p q hrm hwm
  have hJ₁ : Measurable (fun z : ℝ × ℝ => J z.1) := hJ.comp measurable_fst
  have hF := hkm.mul hJ₁
  have hsplit : (∫⁻ t in Icc a b,
      ENNReal.ofReal ((r t / r b) ^ p * (w t / r t)) *
        ∫⁻ s in Icc a t, ENNReal.ofReal ((r s / r t) ^ q) * J s) =
      ∫⁻ t in Icc a b, ∫⁻ s in Icc a t, ENNReal.ofReal (k s t) * J s := by
    apply setLIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Icc
    intro s hs
    dsimp only
    have hout : 0 ≤ (r t / r b) ^ p * (w t / r t) :=
      mul_nonneg (Real.rpow_nonneg (div_nonneg (hr0 t ht)
        (hr0 b ⟨ht.1.trans ht.2, le_rfl⟩)) p) (div_nonneg (hw0 t ht) (hr0 t ht))
    rw [← mul_assoc, ← ENNReal.ofReal_mul hout]
    congr 2
    dsimp only [k]
    ring
  exact hsplit.trans (lintegral_lintegral_swap_triangle hF).symm

private theorem separated_kernel_tail_le_aux
    {r w : ℝ → ℝ} {a b s p q : ℝ} (c : ℝ≥0∞)
    (hs : s ∈ Ioc a b) (hpq : p < q) (hrm : Measurable r) (hwm : Measurable w)
    (hr : ContinuousOn r (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hrp : ∀ t ∈ Ioc a b, 0 < r t) (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt r (w t) t) :
    (∫⁻ t in Icc s b,
      ENNReal.ofReal ((r s / r t) ^ q * (r t / r b) ^ p * (w t / r t)) * c) ≤
      ENNReal.ofReal (1 / (q - p)) * (ENNReal.ofReal ((r s / r b) ^ p) * c) := by
  have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc hs.1.le le_rfl
  have hpos : ∀ t ∈ Icc s b, 0 < r t :=
    fun t ht => hrp t ⟨hs.1.trans_le ht.1, ht.2⟩
  have hle := lintegral_separated_kernel_le_aux hs.2 hpq
    (hr.mono hsub) (hw.mono hsub) hpos
    (fun t ht => hw0 t (hsub ht)) (fun t ht => hd t ⟨hs.1.trans ht.1, ht.2⟩)
  have hpair : Measurable (fun t : ℝ => (s, t)) := measurable_const.prodMk measurable_id
  have hcompose := (measurable_separated_kernel_aux b p q hrm hwm).comp hpair
  have hks : Measurable (fun t : ℝ => ENNReal.ofReal
      ((r s / r t) ^ q * (r t / r b) ^ p * (w t / r t))) := by
    simpa only [Function.comp_def] using hcompose
  have hmul := lintegral_mul_const (μ := volume.restrict (Icc s b)) c hks
  rw [hmul]
  have heqrhs : ENNReal.ofReal ((r s / r b) ^ p / (q - p)) =
      ENNReal.ofReal ((r s / r b) ^ p) * ENNReal.ofReal ((q - p)⁻¹) := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul
      (Real.rpow_nonneg (div_nonneg (hpos s ⟨le_rfl, hs.2⟩).le
        (hpos b ⟨hs.2, le_rfl⟩).le) p)]
  rw [heqrhs] at hle
  calc
    _ ≤ (ENNReal.ofReal ((r s / r b) ^ p) * ENNReal.ofReal ((q - p)⁻¹)) * c :=
      mul_le_mul' hle le_rfl
    _ = _ := by rw [one_div]; ac_rfl

/-- Tonelli's nonnegative form of the separated radial convolution.
The exact cost is `1/(q-p)`, uniformly in the radius, minimum radius,
weight, forcing, endpoints and their integrability sizes. The forcing
may have infinite integral; the assertion introduces no finiteness premise. -/
theorem stab_separated_radial_convolution_le
    {r w : ℝ → ℝ} {J : ℝ → ℝ≥0∞} {a b p q : ℝ}
    (hpq : p < q) (hrm : Measurable r) (hwm : Measurable w) (hJ : Measurable J)
    (hr : ContinuousOn r (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hr0 : ∀ t ∈ Icc a b, 0 ≤ r t) (hrp : ∀ t ∈ Ioc a b, 0 < r t)
    (hw0 : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hd : ∀ t ∈ Ioo a b, HasDerivAt r (w t) t) :
    (∫⁻ t in Icc a b, ENNReal.ofReal ((r t / r b) ^ p * (w t / r t)) *
      ∫⁻ s in Icc a t, ENNReal.ofReal ((r s / r t) ^ q) * J s) ≤
      ENNReal.ofReal (1 / (q - p)) *
        ∫⁻ s in Icc a b, ENNReal.ofReal ((r s / r b) ^ p) * J s := by
  rw [separated_kernel_swap_aux hrm hwm hJ hr0 hw0]
  have hne : ∀ᵐ s : ℝ, s ≠ a := by simp [ae_iff, measure_singleton]
  calc
    _ ≤ ∫⁻ s in Icc a b,
        ENNReal.ofReal (1 / (q - p)) * (ENNReal.ofReal ((r s / r b) ^ p) * J s) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne]
        with s hs hsne
      exact separated_kernel_tail_le_aux (J s)
        ⟨lt_of_le_of_ne hs.1 hsne.symm, hs.2⟩ hpq hrm hwm hr hw hrp hw0 hd
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end EmcsfAcExtension.Local
