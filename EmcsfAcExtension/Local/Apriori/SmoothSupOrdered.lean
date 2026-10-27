module

public import EmcsfAcExtension.Local.Apriori.SmoothSupIncoming
public import EmcsfAcExtension.Local.Apriori.SmoothSupOrderedCore
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Ordered outgoing scalar curvature in the sup norm

The radius factor in the curvature primitive is kept inside the incoming
moment before applying the ordered positive kernel. This is the source
calculation of `charged_SF_new_version.tex:L6218–6230`, with the literal bootstrap box.
No downstream Stability or Construction module is imported.
-/

public section

open Set MeasureTheory Filter Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The scalar curvature primitive has coefficients at most `256 ε/(v-u)³`
in either transport direction. The constant is universal, independently of
`T,e,M`, the fields, and all derivative suprema. -/
theorem smooth_scalar_primitive_coefficients_aux
    {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖((S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2) * (S.r u v : ℂ)⁻¹‖ ≤
        256 * ε / (v - u) ^ 3 ∧
    ‖((S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2) * (S.r u v : ℂ)⁻¹‖ ≤
        256 * ε / (v - u) ^ 3 := by
  have hpt : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := hset.c1.r_pos (u, v) hpt huv
  have hl := hset.c1.lam_pos (u, v) hpt
  have hn := hset.c1.nu_neg (u, v) hpt
  have hb := hset.box (u, v) hpt
  have hε := hset.eps_nonneg
  have hx : ‖S.theta u v‖ ≤ 4 * ε :=
    (hset.theta_norm_le hpt).trans (by
      have hi := mul_le_mul_of_nonneg_left hb.2.1 (by positivity : 0 ≤ 4 * ε)
      simpa only [mul_one] using hi)
  have hy : ‖S.xi u v‖ ≤ 4 * ε :=
    (hset.xi_norm_le hpt).trans (by
      have hi := mul_le_mul_of_nonneg_left hb.2.2.2.1 (by positivity : 0 ≤ 4 * ε)
      simpa only [mul_one] using hi)
  have heq (a : ℝ) (z : ℂ) :
      ‖((a : ℂ) * z / (S.r u v : ℂ) ^ 2) * (S.r u v : ℂ)⁻¹‖ =
        |a| * ‖z‖ / S.r u v ^ 3 := by
    simp only [norm_mul, norm_div, norm_pow, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
    field_simp
  have hr3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (v - u) / 4)
    (smooth_radius_bounds_aux hset hpt).1 3
  have htail : 4 * ε / S.r u v ^ 3 ≤ 256 * ε / (v - u) ^ 3 := by
    calc
      _ ≤ (4 * ε) / ((v - u) / 4) ^ 3 := div_le_div_of_nonneg_left (by positivity)
        (by positivity) hr3
      _ = _ := by
        field_simp
        ring
  constructor
  · rw [heq, abs_of_neg hn]
    apply le_trans _ htail
    exact div_le_div_of_nonneg_right
      ((mul_le_mul hb.2.2.2.1 hx (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
      (pow_nonneg hr.le 3)
  · rw [heq, abs_of_pos hl]
    apply le_trans _ htail
    exact div_le_div_of_nonneg_right
      ((mul_le_mul hb.2.1 hy (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
      (pow_nonneg hr.le 3)

/-- Outgoing scalar-curvature source from the incoming radial moment.
The exact coefficient `1024` is universal: independent of
`T,e,ε,M,S,h,p` for `0 < p ≤ 1 - 16ε²`. The two inputs are the actual
characteristic envelopes, extended by zero outside `[0,T]`. -/
theorem smooth_ordered_pointwise_aux
    {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h)
    {p u v : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 - 16 * ε ^ 2)
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖(S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2 *
      curvScalar (triangle 0 T) S u v‖ₑ ≤
      ENNReal.ofReal (1024 * ε) * smoothOrderedKernel p
        ((Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S)))
        ((Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))) u v := by
  classical
  let K := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S))
  let J := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))
  have hK : Measurable K := measurable_indicator_inEnv
    (continuousOn_kC1_aux hset.pos hset.c1)
  have hp' : 0 < p := hp0
  have hp1 : p ≤ 1 := hp.trans (sub_le_self _ (by positivity : 0 ≤ 16 * ε ^ 2))
  have hL : 0 < v - u := sub_pos.mpr huv
  have hr := hset.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv
  have hR (w : ℝ) (hw : w ∈ Ioc u v) : 0 < S.r u w ∧ S.r u w ≤ v - u :=
    ⟨hset.c1.r_pos (u, w) ⟨hu, hw.1.le, hw.2.trans hvT⟩ hw.1,
      ((smooth_radius_bounds_aux hset ⟨hu, hw.1.le, hw.2.trans hvT⟩).2).trans
        (sub_le_sub_right hw.2 u)⟩
  have hρ (w : ℝ) (hw : w ∈ Ioc u v) (s : ℝ) (hs : s ∈ Icc u w) :
      0 ≤ S.r s w ∧ S.r s w ≤ w - s := by
    have hb := smooth_radius_bounds_aux hset ⟨hu.trans hs.1, hs.2, hw.2.trans hvT⟩
    exact ⟨(div_nonneg (sub_nonneg.mpr hs.2) (by norm_num : (0 : ℝ) ≤ 4)).trans hb.1, hb.2⟩
  have hk (w : ℝ) (hw : w ∈ Ioc u v) :
      AEMeasurable (fun s => ENNReal.ofReal ((S.r s w / S.r u w) ^ p) * K s)
        (volume.restrict (Icc u w)) := by
    have hrr : ContinuousOn (fun s => S.r s w / S.r u w) (Icc u w) :=
      (hset.c1.c1_r.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hu.trans hs.1, hs.2, hw.2.trans hvT⟩)).div_const _
    exact ((ENNReal.continuous_ofReal.comp_continuousOn
      ((Real.continuous_rpow_const hp'.le).comp_continuousOn hrr)).aemeasurable
        measurableSet_Icc).mul hK.aemeasurable.restrict
  have hmoment (w : ℝ) (hw : w ∈ Ioc u v) :
      ENNReal.ofReal ‖S.xi u w / (S.nu u w : ℂ)‖ ≤
        ENNReal.ofReal 4 * ∫⁻ s in Icc u w,
          ENNReal.ofReal ((S.r s w / S.r u w) ^ p) * K s := by
    have hm := ENNReal.ofReal_le_ofReal
      (smooth_incoming_radial_moment_aux hset hp' hp hu hw.1 (hw.2.trans hvT))
    rw [intervalIntegral.integral_of_le hw.1.le] at hm
    have hnorm := enorm_integral_le_lintegral_enorm
      (fun s => (S.r s w / S.r u w) ^ p *
        (2 * (inEnv T (kC1 e (triangle 0 T) S) s).toReal))
      (μ := volume.restrict (Ioc u w))
    have hnonneg : 0 ≤ ∫ s in Ioc u w,
        (S.r s w / S.r u w) ^ p *
          (2 * (inEnv T (kC1 e (triangle 0 T) S) s).toReal) := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact mul_nonneg
        (Real.rpow_nonneg (div_nonneg (hρ w hw s ⟨hs.1.le, hs.2⟩).1 (hR w hw).1.le) _)
        (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hnorm
    apply (hm.trans hnorm).trans
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      restrict_Ioc_eq_restrict_Icc]
    apply setLIntegral_mono' measurableSet_Icc
    intro s hs
    have hq : 0 ≤ (S.r s w / S.r u w) ^ p :=
      Real.rpow_nonneg (div_nonneg (hρ w hw s hs).1 (hR w hw).1.le) _
    have hsT : s ∈ Icc 0 T := ⟨hu.trans hs.1, hs.2.trans (hw.2.trans hvT)⟩
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hq (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)),
      ENNReal.ofReal_mul hq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_toReal (inEnv_ne_top_of_continuousOn
        (continuousOn_kC1_aux hset.pos hset.c1) hsT)]
    dsimp only [K]
    rw [indicator_of_mem hsT]
    have hi : ENNReal.ofReal 2 ≤ ENNReal.ofReal 4 := by norm_num
    calc
      _ ≤ ENNReal.ofReal ((S.r s w / S.r u w) ^ p) *
          (ENNReal.ofReal 4 * inEnv T (kC1 e (triangle 0 T) S) s) :=
        mul_le_mul' le_rfl (mul_le_mul' hi le_rfl)
      _ = _ := by ac_rfl
  have hm := smooth_integral_moment_product_aux
    (I := Ioc u v) (E := fun w => Icc u w) (R := S.r u)
    (q := fun w s => (S.r s w / S.r u w) ^ p) (P := fun w s => (w - s) ^ p)
    (y := fun w => S.xi u w / (S.nu u w : ℂ)) (K := K) (J := J)
    (B := (v - u) ^ (1 - p)) measurableSet_Ioc (fun _ _ => measurableSet_Icc)
    (Real.rpow_nonneg hL.le _) (fun w hw => (hR w hw).1.le)
    (fun w hw s hs => Real.rpow_nonneg (div_nonneg (hρ w hw s hs).1 (hR w hw).1.le) p)
    (fun w hw s hs => Real.rpow_nonneg (sub_nonneg.mpr hs.2) p) hk hmoment
    (fun w hw s hs => smooth_radius_power_product_aux (hR w hw).1 (hR w hw).2
      (hρ w hw s hs).1 (hρ w hw s hs).2 hp'.le hp1)
  have hε := hset.eps_nonneg
  let c := ((S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2) * (S.r u v : ℂ)⁻¹
  have hc : ‖c‖ₑ ≤ ENNReal.ofReal (256 * ε / (v - u) ^ 3) := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (smooth_scalar_primitive_coefficients_aux hset hu huv hvT).1
  have hprimitive : ‖(S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2 *
      curvScalar (triangle 0 T) S u v‖ₑ ≤
      ‖c‖ₑ * ∫⁻ w in Ioc u v, ENNReal.ofReal (S.r u w) *
        ENNReal.ofReal ‖S.xi u w / (S.nu u w : ℂ)‖ * J w := by
    rw [curvScalar, intervalIntegral.integral_of_le huv.le, ← mul_assoc, enorm_mul]
    apply mul_le_mul' le_rfl
    apply (enorm_integral_le_lintegral_enorm _).trans
    apply setLIntegral_mono' measurableSet_Ioc
    intro w hw
    rw [← ofReal_norm, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hR w hw).1, RCLike.norm_conj]
    rw [ENNReal.ofReal_mul (mul_nonneg (hR w hw).1.le (norm_nonneg _)),
      ENNReal.ofReal_mul (hR w hw).1.le]
    apply mul_le_mul' le_rfl
    dsimp only [J]
    rw [indicator_of_mem (show w ∈ Icc 0 T from ⟨hu.trans hw.1.le, hw.2.trans hvT⟩),
      ofReal_norm]
    exact enorm_le_normEnvelope (jC1 (triangle 0 T) S) ⟨hu, hw.1.le⟩
  apply hprimitive.trans
  apply (mul_le_mul' hc hm).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 256 * ε / (v - u) ^ 3)]
  have hcoeff : (256 * ε / (v - u) ^ 3) * (4 * (v - u) ^ (1 - p)) =
      1024 * ε * (v - u) ^ (-p - 2) := by
    rw [← mul_assoc]
    have he := smooth_ordered_coefficient_aux (ε := 4 * ε) (p := p) hL
    convert he using 1 <;> ring
  rw [hcoeff, ENNReal.ofReal_mul (mul_nonneg (by norm_num) hε), smoothOrderedKernel,
    restrict_Ioc_eq_restrict_Icc]
  dsimp only [K, J]
  ac_rfl

private theorem curvature_sum_enorm_aux (a z : ℂ) :
    ‖a * (z + 2 * starRingEnd ℂ z)‖ₑ ≤ 3 * ‖a * z‖ₑ := by
  have hs : ‖z + 2 * starRingEnd ℂ z‖ ≤ 3 * ‖z‖ := by
    calc
      _ ≤ ‖z‖ + ‖(2 : ℂ)‖ * ‖starRingEnd ℂ z‖ := by
        simpa only [norm_mul] using norm_add_le z (2 * starRingEnd ℂ z)
      _ = _ := by simp; ring
  have hi := mul_le_mul_of_nonneg_left hs (norm_nonneg a)
  have he : ‖a * (z + 2 * starRingEnd ℂ z)‖ ≤ 3 * ‖a * z‖ := by
    simpa only [norm_mul, mul_left_comm] using hi
  simpa only [ofReal_norm, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
    ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal he

/-- [node restart-sec-independent-null-construction#ordered-sup-curvature]
The scalar curvature forcing integrated in the incoming direction is bounded
by `C ε ‖K‖₁ ‖J‖∞/(1+p)` (`charged_SF_new_version.tex:L6218–6230`). The universal
choice `C = 3072` is independent of all data, endpoints and `p` in the
displayed range. The ordered radius weight is integrated before applying the
sup bound; the terminal singleton is removed in the positive-kernel estimate.
The proof works on the classical C¹ class by the integral route (internal project record).
This is the final sup bound; no field transport identity is assumed. -/
theorem Null.ordered_sup_curvature :
    ∃ C : ℝ, 0 < C ∧ ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      AprioriSetting e T ε M S h → ∀ p : ℝ, 0 < p → p ≤ 1 - 16 * ε ^ 2 →
      ∀ u v, 0 ≤ u → u ≤ v → v ≤ T →
      (∫⁻ a in Icc 0 u,
        ‖(S.nu a v * S.theta a v / S.r a v ^ 2) *
          (curvScalar (triangle 0 T) S a v +
            2 * starRingEnd ℂ (curvScalar (triangle 0 T) S a v))‖ₑ) ≤
      ENNReal.ofReal (C * ε / (1 + p)) *
        (∫⁻ a in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) a) *
        (⨆ q ∈ triangle 0 T, ‖jC1 (triangle 0 T) S q.1 q.2‖ₑ) := by
  refine ⟨3072, by norm_num, ?_⟩
  intro e T ε M S h hset p hp hsmall u v hu huv hvT
  classical
  let K := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S))
  let J := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))
  let B := ⨆ q ∈ triangle 0 T, ‖jC1 (triangle 0 T) S q.1 q.2‖ₑ
  have hK : Measurable K := measurable_indicator_inEnv
    (continuousOn_kC1_aux hset.pos hset.c1)
  have hJ : Measurable J := measurable_indicator_outEnv
    (continuousOn_jC1_aux hset.pos hset.c1)
  have hJB (w : ℝ) (hw : w ∈ Icc 0 T) : J w ≤ B := by
    dsimp only [J]
    rw [indicator_of_mem hw]
    apply iSup₂_le
    intro a ha
    exact le_iSup₂_of_le (a, w) ⟨ha.1, ha.2, hw.2⟩ le_rfl
  have hε := hset.eps_nonneg
  calc
    _ ≤ ∫⁻ a in Icc 0 v,
        ‖(S.nu a v * S.theta a v / S.r a v ^ 2) *
          (curvScalar (triangle 0 T) S a v +
            2 * starRingEnd ℂ (curvScalar (triangle 0 T) S a v))‖ₑ :=
      lintegral_mono_set (Icc_subset_Icc le_rfl huv)
    _ ≤ ∫⁻ a in Icc 0 v, 3 * ENNReal.ofReal (1024 * ε) *
        smoothOrderedKernel p K J a v := by
      apply lintegral_mono_ae
      have hne : ∀ᵐ a ∂volume.restrict (Icc 0 v), a ≠ v :=
        ae_restrict_of_ae (by simp [ae_iff])
      filter_upwards [ae_restrict_mem measurableSet_Icc, hne] with a ha hav
      apply (curvature_sum_enorm_aux _ _).trans
      rw [mul_assoc]
      exact mul_le_mul' le_rfl (smooth_ordered_pointwise_aux hset hp hsmall
        ha.1 (lt_of_le_of_ne ha.2 hav) hvT)
    _ = (3 * ENNReal.ofReal (1024 * ε)) *
        ∫⁻ a in Icc 0 v, smoothOrderedKernel p K J a v := by
      rw [lintegral_const_mul' _ _ (by finiteness)]
    _ ≤ (3 * ENNReal.ofReal (1024 * ε)) * orderedKernelDensity p T K J univ v :=
      mul_le_mul' le_rfl (smooth_ordered_kernel_slice_aux hp.le hK hJ (hu.trans huv) hvT)
    _ ≤ (3 * ENNReal.ofReal (1024 * ε)) *
        (ENNReal.ofReal (1 / (1 + p)) * (∫⁻ a in Icc 0 T, K a) * B) :=
      mul_le_mul' le_rfl (smooth_ordered_kernel_sup_aux hp hK.aemeasurable hJB)
    _ = _ := by
      have hKi : (∫⁻ a in Icc 0 T, K a) =
          ∫⁻ a in Icc 0 T, inEnv T (kC1 e (triangle 0 T) S) a := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro a ha
        exact indicator_of_mem ha _
      rw [hKi, ← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 3 * (1024 * ε))]
      congr 2
      ring_nf

/-- [node restart-sec-independent-null-construction#ordered-sup-curvature]
The more precise reflected-cutoff form of the outgoing scalar-curvature
sup estimate (`charged_SF_new_version.tex:L6223–6230`). Its exact coefficient `3072`
is universal, independent of every parameter and positive exponent in the
displayed damping range. The endpoint cutoff is `min u a`; no incoming
weight is exchanged with an outgoing weight. Together with
`smooth_reflected_curvature_sup_aux` this gives the final finite bound. -/
theorem Null.ordered_sup_curvature_cutoff {e T ε M p : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : AprioriSetting e T ε M S h) (hp : 0 < p) (hsmall : p ≤ 1 - 16 * ε ^ 2)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (∫⁻ s in Icc 0 u,
      ‖(S.nu s v * S.theta s v / S.r s v ^ 2) *
        (curvScalar (triangle 0 T) S s v +
          2 * starRingEnd ℂ (curvScalar (triangle 0 T) S s v))‖ₑ) ≤
      ENNReal.ofReal (3072 * ε) *
        (∫⁻ a in Icc 0 v, inEnv T (kC1 e (triangle 0 T) S) a *
          ENNReal.ofReal ((v - a) ^ (p + 1) *
            ∫ s in 0..min u a, (v - s) ^ (-p - 2))) *
        (⨆ q ∈ triangle 0 T, ‖jC1 (triangle 0 T) S q.1 q.2‖ₑ) := by
  classical
  let K := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S))
  let J := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))
  let B := ⨆ q ∈ triangle 0 T, ‖jC1 (triangle 0 T) S q.1 q.2‖ₑ
  have hK : Measurable K := measurable_indicator_inEnv
    (continuousOn_kC1_aux hset.pos hset.c1)
  have hJ : Measurable J := measurable_indicator_outEnv
    (continuousOn_jC1_aux hset.pos hset.c1)
  have hJB (w : ℝ) (hw : w ∈ Icc 0 T) : J w ≤ B := by
    dsimp only [J]
    rw [indicator_of_mem hw]
    apply iSup₂_le
    intro a ha
    exact le_iSup₂_of_le (a, w) ⟨ha.1, ha.2, hw.2⟩ le_rfl
  have hB : B ≠ ⊤ := by
    obtain ⟨C, hC⟩ := (isCompact_triangle 0 T).bddAbove_image
      (continuousOn_jC1_aux hset.pos hset.c1).norm
    apply ne_top_of_le_ne_top (show ENNReal.ofReal C ≠ ⊤ from ENNReal.ofReal_ne_top)
    apply iSup₂_le
    intro q hq
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC (mem_image_of_mem _ hq))
  have hε := hset.eps_nonneg
  calc
    _ ≤ ∫⁻ s in Icc 0 u, 3 * ENNReal.ofReal (1024 * ε) *
        smoothOrderedKernel p K J s v := by
      apply lintegral_mono_ae
      have hne : ∀ᵐ s ∂volume.restrict (Icc 0 u), s ≠ v :=
        ae_restrict_of_ae (by simp [ae_iff])
      filter_upwards [ae_restrict_mem measurableSet_Icc, hne] with s hs hsv
      apply (curvature_sum_enorm_aux _ _).trans
      rw [mul_assoc]
      exact mul_le_mul' le_rfl (smooth_ordered_pointwise_aux hset hp hsmall
        hs.1 (lt_of_le_of_ne (hs.2.trans huv) hsv) hvT)
    _ = (3 * ENNReal.ofReal (1024 * ε)) *
        ∫⁻ s in Icc 0 u, smoothOrderedKernel p K J s v := by
      rw [lintegral_const_mul' _ _ (by finiteness)]
    _ ≤ (3 * ENNReal.ofReal (1024 * ε)) *
        ((∫⁻ a in Icc 0 v, K a * ENNReal.ofReal ((v - a) ^ (p + 1) *
          ∫ s in 0..min u a, (v - s) ^ (-p - 2))) * B) :=
      mul_le_mul' le_rfl (smooth_ordered_reflected_cutoff_aux hp hu huv hvT hK hJ hJB hB)
    _ = _ := by
      have hKi : (∫⁻ a in Icc 0 v, K a * ENNReal.ofReal ((v - a) ^ (p + 1) *
          ∫ s in 0..min u a, (v - s) ^ (-p - 2))) =
          ∫⁻ a in Icc 0 v, inEnv T (kC1 e (triangle 0 T) S) a *
            ENNReal.ofReal ((v - a) ^ (p + 1) *
              ∫ s in 0..min u a, (v - s) ^ (-p - 2)) := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro a ha
        dsimp only [K]
        rw [indicator_of_mem (show a ∈ Icc 0 T from ⟨ha.1, ha.2.trans hvT⟩)]
      rw [hKi, ← ENNReal.ofReal_ofNat 3,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        show (3 : ℝ) * (1024 * ε) = 3072 * ε by ring]
      dsimp only [B]
      ac_rfl

end EmcsfAcExtension.Local
