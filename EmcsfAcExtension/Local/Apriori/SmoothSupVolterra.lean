module

public import EmcsfAcExtension.Local.Apriori.SmoothSupOrdered
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseFields
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseSourcePointwise
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseFinal
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseNorms
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # The outgoing ordered Volterra inequality

The pointwise envelope keeps both ordered inputs. The closed incoming L¹
budget bounds the homogeneous factor before the universal coefficient is
chosen, as in `charged_SF_new_version.tex:L4946–4946`.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem forcing_ordered :
    ∃ C : ℝ, 0 < C ∧ ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      AprioriSetting e T ε M S h → ε ≤ 1 / 8 → ∀ v ∈ Icc 0 T,
      (∫⁻ u in Icc 0 v,
        ‖S.nu u v * S.theta u v / S.r u v ^ 2 *
          (curv S u v + 2 * starRingEnd ℂ (curv S u v)) + emSourceJ e S u v‖ₑ) ≤
        ENNReal.ofReal (C * ε) * orderedKernelDensity (1 / 2) T
          ((Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S)))
          ((Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))) univ v +
        ENNReal.ofReal (C * e ^ 2 * M ^ 2 * T * ε) := by
  obtain ⟨B, hB, hb⟩ := characteristic_forcing_scalar_majorants
  refine ⟨3072 + B, by positivity, ?_⟩
  intro e T ε M S h hset hε v hv
  have hε0 := hset.eps_nonneg
  have hT := hset.pos
  have hp : (1 : ℝ) / 2 ≤ 1 - 16 * ε ^ 2 := by nlinarith only [hε0, hε]
  let K := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S))
  let J := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))
  have hK : Measurable K := measurable_indicator_inEnv
    (continuousOn_kC1_aux hT hset.c1)
  have hJ : Measurable J := measurable_indicator_outEnv
    (continuousOn_jC1_aux hT hset.c1)
  have hpoint (u : ℝ) (hu : u ∈ Icc 0 v) (huv : u < v) :
      ‖S.nu u v * S.theta u v / S.r u v ^ 2 *
        (curv S u v + 2 * starRingEnd ℂ (curv S u v)) + emSourceJ e S u v‖ₑ ≤
        ENNReal.ofReal (3072 * ε) * smoothOrderedKernel (1 / 2) K J u v +
        ENNReal.ofReal (B * e ^ 2 * M ^ 2 * ε) := by
    have hpuv : (u, v) ∈ triangle 0 T := ⟨hu.1, hu.2, hv.2⟩
    have hs := (hb e T ε M S h hset (hε.trans (by norm_num)) u v hpuv).1
    have hbox := hset.box (u, v) hpuv
    have hgeom : (-S.nu u v) * S.lam u v ≤ 1 :=
      (mul_le_mul hbox.2.2.2.1 hbox.2.1
        (hset.c1.lam_pos _ hpuv).le (by norm_num)).trans_eq (one_mul _)
    have he := mul_le_mul_of_nonneg_left hgeom
      (show 0 ≤ B * e ^ 2 * M ^ 2 * ε by positivity)
    have hs' : ‖S.nu u v * S.theta u v / S.r u v ^ 2 *
        (curv S u v + 2 * starRingEnd ℂ (curv S u v)) + emSourceJ e S u v‖ ≤
        3 * ‖S.nu u v * S.theta u v / S.r u v ^ 2 *
          curvScalar (triangle 0 T) S u v‖ + B * e ^ 2 * M ^ 2 * ε := by
      nlinarith only [hs, he]
    have hsE := ENNReal.ofReal_le_ofReal hs'
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)] at hsE
    simp only [ofReal_norm, ENNReal.ofReal_ofNat] at hsE
    apply hsE.trans
    have ho := smooth_ordered_pointwise_aux hset (by norm_num : (0 : ℝ) < 1 / 2)
      hp hu.1 huv hv.2
    apply add_le_add _ le_rfl
    apply (mul_le_mul' (le_refl 3) ho).trans_eq
    rw [← mul_assoc, ← ENNReal.ofReal_ofNat 3,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 2
    ring
  have hint : (∫⁻ u in Icc 0 v,
      ‖S.nu u v * S.theta u v / S.r u v ^ 2 *
        (curv S u v + 2 * starRingEnd ℂ (curv S u v)) + emSourceJ e S u v‖ₑ) ≤
      ∫⁻ u in Icc 0 v,
        ENNReal.ofReal (3072 * ε) * smoothOrderedKernel (1 / 2) K J u v +
          ENNReal.ofReal (B * e ^ 2 * M ^ 2 * ε) := by
    apply lintegral_mono_ae
    have hne : ∀ᵐ u ∂volume.restrict (Icc 0 v), u ≠ v :=
      ae_restrict_of_ae (by simp [ae_iff])
    filter_upwards [ae_restrict_mem measurableSet_Icc, hne] with u hu huv
    exact hpoint u hu (lt_of_le_of_ne hu.2 huv)
  rw [lintegral_add_right _ measurable_const,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    setLIntegral_const, Real.volume_Icc, sub_zero,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ B * e ^ 2 * M ^ 2 * ε)] at hint
  apply hint.trans
  apply add_le_add
  · exact mul_le_mul'
      (ENNReal.ofReal_le_ofReal (by nlinarith only [mul_nonneg hB.le hε0]))
      (smooth_ordered_kernel_slice_aux (by norm_num : (0 : ℝ) ≤ 1 / 2) hK hJ hv.1 hv.2)
  · apply ENNReal.ofReal_le_ofReal
    have hlength := mul_le_mul_of_nonneg_left hv.2
      (show 0 ≤ B * e ^ 2 * M ^ 2 * ε by positivity)
    have hconst := mul_le_mul_of_nonneg_right
      (show B ≤ 3072 + B by linarith) (show 0 ≤ e ^ 2 * M ^ 2 * T * ε by positivity)
    nlinarith only [hlength, hconst]

/-- [node restart-bv-ordered-kernel]
The outgoing ordered Volterra envelope inequality with fixed exponent
`p=1/2`. Universal positive thresholds and the common coefficient precede
all data and higher derivative norms. Both ordered inputs remain inside
the kernel; its sup form follows from `smooth_ordered_kernel_sup_aux`.
The electric term uses `T=2R`, absorbing the fixed factor into the constant. -/
theorem smooth_ordered_volterra : ∃ ε₀ δ₀ C : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
      ∀ v ∈ Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) v ≤
        ENNReal.ofReal C * ‖jC1 (triangle 0 T) S 0 v‖ₑ +
        ENNReal.ofReal (C * e ^ 2 * M ^ 2 * T * ε) +
        ENNReal.ofReal (C * ε) * orderedKernelDensity (1 / 2) T
          ((Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S)))
          ((Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))) univ v := by
  obtain ⟨A, hA, htransport⟩ := j_characteristic_enorm_bound
  obtain ⟨D, hD, hforce⟩ := forcing_ordered
  obtain ⟨εb, δb, hεb, hδb, henvelopes⟩ := closed_envelopes_sharp
  let ε₀ := min εb (min (1 / 8) (1 / (100 * (A + 1))))
  let H := Real.exp 1
  have hH : 0 < H := Real.exp_pos _
  let C := H * (D + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  have hHC : H ≤ C := by dsimp only [C]; nlinarith only [mul_pos hH hD]
  have hHDC : H * D ≤ C := by dsimp only [C]; linarith only [hH]
  refine ⟨ε₀, δb, C, lt_min hεb (lt_min (by norm_num) (by positivity)), hδb, hC, ?_⟩
  intro e T ε M S h hset hε hδ v hv
  have hε0 := hset.eps_nonneg
  have hT := hset.pos
  have hε8 : ε ≤ 1 / 8 := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεA : ε ≤ 1 / (100 * (A + 1)) :=
    hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hAε : A * ε ≤ 1 / 100 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 100 * (A + 1))).mp hεA
    nlinarith only [hh, hε0]
  have hK := (henvelopes e T ε M S h hset (hε.trans (min_le_left _ _)) hδ).2
  have hKr : (∫ u in 0..T, (inEnv T (kC1 e (triangle 0 T) S) u).toReal) ≤ 9 / 8 * ε := by
    rw [← incoming_envelope_integral_toReal hT hset.c1]
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 9 / 8 * ε)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hK
  have hhom : Real.exp (A * ε *
      ∫ u in 0..T, (inEnv T (kC1 e (triangle 0 T) S) u).toReal) ≤ H := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hKr (mul_nonneg hA.le hε0)
    have hs := mul_le_mul_of_nonneg_right hAε hε0
    nlinarith only [hh, hs, hε0, hε8]
  have hf := hforce e T ε M S h hset hε8 v hv
  change (⨆ u ∈ Icc 0 v, ‖jC1 (triangle 0 T) S u v‖ₑ) ≤ _
  apply iSup₂_le
  intro u hu
  have hb := (htransport e T ε M S h hset hε8 u v hu.1 hu.2 hv.2).trans
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hhom) (add_le_add le_rfl hf))
  apply hb.trans
  rw [mul_add, mul_add]
  have hc1 : ENNReal.ofReal H * ‖jC1 (triangle 0 T) S 0 v‖ₑ ≤
      ENNReal.ofReal C * ‖jC1 (triangle 0 T) S 0 v‖ₑ :=
    mul_le_mul' (ENNReal.ofReal_le_ofReal hHC) le_rfl
  have hc2 : ENNReal.ofReal H * ENNReal.ofReal (D * ε) ≤ ENNReal.ofReal (C * ε) := by
    rw [← ENNReal.ofReal_mul hH.le]
    apply ENNReal.ofReal_le_ofReal
    nlinarith only [mul_le_mul_of_nonneg_right hHDC hε0]
  have hc3 : ENNReal.ofReal H * ENNReal.ofReal (D * e ^ 2 * M ^ 2 * T * ε) ≤
      ENNReal.ofReal (C * e ^ 2 * M ^ 2 * T * ε) := by
    rw [← ENNReal.ofReal_mul hH.le]
    apply ENNReal.ofReal_le_ofReal
    have hh := mul_le_mul_of_nonneg_right hHDC
      (show 0 ≤ e ^ 2 * M ^ 2 * T * ε by positivity)
    nlinarith only [hh]
  let Kd := orderedKernelDensity (1 / 2) T
    ((Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S)))
    ((Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))) univ v
  have hc4 : ENNReal.ofReal H * (ENNReal.ofReal (D * ε) * Kd) ≤
      ENNReal.ofReal (C * ε) * Kd := by
    rw [← mul_assoc]
    exact mul_le_mul' hc2 le_rfl
  apply (add_le_add hc1 (add_le_add hc4 hc3)).trans_eq
  dsimp only [Kd]
  ac_rfl

end EmcsfAcExtension.Local
