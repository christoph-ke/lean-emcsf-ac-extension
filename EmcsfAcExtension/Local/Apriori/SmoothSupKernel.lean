module

public import EmcsfAcExtension.Infra.OrderedKernel
import Mathlib.Tactic

/-! # Ordered kernels in the supremum norm

The exact middle-variable mass and the reflected cutoff cancellation used in
`charged_SF_new_version.tex:L5060–5060` and `L6218–6230`. These analytic helpers do not
assert a field transport identity. Constants depend only on the displayed
exponent, uniformly in all endpoints and input functions.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-independent-area#Hardy-exponent-choice]
One exponent is fixed before all solutions or approximation indices.
The numerical margin `ε ≤ 1/8` gives `p = 1/2 < 1 - 16ε²`.
There are no datum-dependent constants (`charged_SF_new_version.tex:L4946`). -/
theorem smooth_hardy_exponent_choice :
    ∃ p : ℝ, 1 / 2 ≤ p ∧ p < 1 ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 8 → p < 1 - 16 * ε ^ 2 := by
  refine ⟨1 / 2, le_rfl, by norm_num, ?_⟩
  intro ε hε0 hε
  have hb := pow_le_pow_left₀ hε0 hε 2
  norm_num at hb
  linarith only [hb]

/-- Comparison of radial and coordinate power weights in the fixed box.
The coefficient `4` is uniform in all radii, separations and `0 < p ≤ 1`. -/
theorem smooth_radial_ratio_rpow_aux {r R x y p : ℝ} (hr : 0 ≤ r) (hR : 0 < R)
    (hx : 0 ≤ x) (hy : 0 < y) (hrx : r ≤ x) (hyR : y / 4 ≤ R)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (r / R) ^ p ≤ 4 * (x / y) ^ p := by
  have ht : 0 ≤ x / y := div_nonneg hx hy.le
  have hratio : r / R ≤ 4 * (x / y) := by
    apply (div_le_iff₀ hR).mpr
    have hi := mul_le_mul_of_nonneg_left hyR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) ht)
    have heq : 4 * (x / y) * (y / 4) = x := by field_simp [hy.ne']
    rw [heq] at hi
    exact hrx.trans hi
  have hi := Real.rpow_le_rpow (div_nonneg hr hR.le) hratio hp
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) ht] at hi
  have hfour : (4 : ℝ) ^ p ≤ 4 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hp1
  exact hi.trans (mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg ht _))

private theorem lintegral_middle_aux {p a v : ℝ} (hp : 0 < p) (hav : a ≤ v) :
    (∫⁻ w in Icc a v, ENNReal.ofReal (orderedPowerKernel p a w v)) ≤
      ENNReal.ofReal (1 / (1 + p)) := by
  rcases hav.eq_or_lt with heq | hlt
  · subst v
    simp
  · have hi : IntegrableOn (orderedPowerKernel p a · v) (Icc a v) := by
      apply ContinuousOn.integrableOn_Icc
      unfold orderedPowerKernel
      exact ((Real.continuous_rpow_const hp.le).comp_continuousOn
        (continuousOn_id.sub continuousOn_const)).div_const _
    have hnonneg : 0 ≤ᵐ[volume.restrict (Icc a v)] (orderedPowerKernel p a · v) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
      exact orderedPowerKernel_nonneg hw.1 hw.2
    rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hav,
      integral_orderedPowerKernel_middle (by linarith only [hp]) hlt]

/-- Supremum form of the ordered operator, with the exact coefficient `1/(1+p)`.
Only the middle input is bounded in supremum norm; the opposite input retains
its full integral. The coefficient depends only on `p`, uniformly in `T,v,K,J`.
This `_aux` helper awaits the field identities before any graph-node assembly. -/
theorem smooth_ordered_kernel_sup_aux {p T v : ℝ} (hp : 0 < p)
    {K J : ℝ → ℝ≥0∞} {B : ℝ≥0∞}
    (hK : AEMeasurable K (volume.restrict (Icc 0 T)))
    (hJ : ∀ w ∈ Icc 0 T, J w ≤ B) :
    orderedKernelDensity p T K J univ v ≤
      ENNReal.ofReal (1 / (1 + p)) * (∫⁻ a in Icc 0 T, K a) * B := by
  classical
  have hinner (a : ℝ) :
      (∫⁻ w in Icc 0 T, (triangle 0 v ∩ univ).indicator
        (fun q => K q.1 * J q.2 * ENNReal.ofReal
          (orderedPowerKernel p q.1 q.2 v)) (a, w)) ≤
      K a * B * ENNReal.ofReal (1 / (1 + p)) := by
    by_cases hav : a ≤ v
    · calc
        _ ≤ ∫⁻ w in Icc a v, K a * B *
            ENNReal.ofReal (orderedPowerKernel p a w v) := by
          calc
            _ ≤ ∫⁻ w in Icc 0 T, (Icc a v).indicator
                (fun w => K a * B * ENNReal.ofReal (orderedPowerKernel p a w v)) w := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
              by_cases ht : (a, w) ∈ triangle 0 v ∩ univ
              · rw [indicator_of_mem ht,
                  indicator_of_mem (show w ∈ Icc a v from ⟨ht.1.2.1, ht.1.2.2⟩)]
                exact mul_le_mul' (mul_le_mul' le_rfl (hJ w hw)) le_rfl
              · rw [indicator_of_notMem ht]
                exact zero_le
            _ ≤ ∫⁻ w, (Icc a v).indicator
                (fun w => K a * B * ENNReal.ofReal (orderedPowerKernel p a w v)) w :=
              lintegral_mono' Measure.restrict_le_self le_rfl
            _ = _ := lintegral_indicator measurableSet_Icc _
        _ = (K a * B) * ∫⁻ w in Icc a v,
            ENNReal.ofReal (orderedPowerKernel p a w v) := by
          rw [lintegral_const_mul _ (by unfold orderedPowerKernel; fun_prop)]
        _ ≤ _ := mul_le_mul' le_rfl (lintegral_middle_aux hp hav)
    · have hz : (fun w => (triangle 0 v ∩ univ).indicator
          (fun q => K q.1 * J q.2 * ENNReal.ofReal
            (orderedPowerKernel p q.1 q.2 v)) (a, w)) = 0 := by
        funext w
        apply indicator_of_notMem
        intro hw
        exact hav (hw.1.2.1.trans hw.1.2.2)
      rw [hz]
      simpa only [Pi.zero_def, lintegral_zero] using
        (show 0 ≤ K a * B * ENNReal.ofReal (1 / (1 + p)) from zero_le)
  unfold orderedKernelDensity
  calc
    _ ≤ ∫⁻ a in Icc 0 T, K a * B * ENNReal.ofReal (1 / (1 + p)) :=
      lintegral_mono hinner
    _ = _ := by
      simp_rw [mul_assoc]
      rw [lintegral_mul_const'' _ hK]
      ring

end EmcsfAcExtension.Local
