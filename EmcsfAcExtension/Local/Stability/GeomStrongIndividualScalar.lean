module

public import EmcsfAcExtension.Local.Stability.GeomStrongScalarPrimitive
public import EmcsfAcExtension.Local.Stability.OrderedKernelArea
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Stability.GeomStrongKernel
import EmcsfAcExtension.Local.Stability.GeomStrongKernelMeas
import EmcsfAcExtension.Local.Stability.AssemblyMoments
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Individual scalar geometric-source area

The geometric primitive has no outer scalar ratio. Its ordered kernel
therefore costs the product of the two label masses, quadratically.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The scalar geometric source has ordered majorant `2048` at exponent
`1/2`. This numerical coefficient is universal before all data and
fields, uniformly in their minimum radius and higher derivatives. -/
theorem stab_geometric_scalar_ordered_pointwise_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) (hε : ε ^ 2 ≤ 1 / 4)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖geometricScalarSource (triangle 0 T) S u v‖ₑ ≤
      ENNReal.ofReal 2048 * stabOrderedKernel (1 / 2)
        ((Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S)))
        ((Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))) u v := by
  have hh := stab_geometric_scalar_ordered_pointwise_of_identity hset
    (fun _ _ hu huv hvT => stab_in_reconstruction_smul hset.c1 hu huv hvT)
    (p := (1 / 2 : ℝ)) (by norm_num) (by linarith only [hε]) hu huv hvT
  convert hh using 1
  congr 1
  simp only [geometricScalarSource, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_pow, div_div]

/-- The scalar geometric-source area is at most `4096 A² ε²`.
The literal coefficient is universal, and dependence on the envelope
constant is displayed before all fields, scales and data. -/
theorem stab_geometric_scalar_area_le_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) (hA : 0 ≤ A) (hε : ε ^ 2 ≤ 1 / 4) :
    (∫⁻ p in triangle 0 T, ‖geometricScalarSource (triangle 0 T) S p.1 p.2‖ₑ) ≤
      ENNReal.ofReal (4096 * A ^ 2 * ε ^ 2) := by
  let K := (Icc 0 T).indicator (inEnv T (kC1 e (triangle 0 T) S))
  let J := (Icc 0 T).indicator (outEnv 0 (jC1 (triangle 0 T) S))
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S.xi 0 0 / (S.nu 0 0 : ℂ)))).trans
      (hset.box.2 (0, 0) ⟨le_rfl, le_rfl, hset.pos.le⟩).2.2.2.2.2.1)
  have mK : Measurable K := by
    dsimp only [K]
    rw [← piecewise_eq_indicator]
    exact (continuousOn_inEnv (continuousOn_kC1_aux hset.pos hset.c1)).measurable_piecewise
      continuousOn_const measurableSet_Icc
  have mJ : Measurable J := by
    dsimp only [J]
    rw [← piecewise_eq_indicator]
    exact (continuousOn_outEnv (continuousOn_jC1_aux hset.pos hset.c1)).measurable_piecewise
      continuousOn_const measurableSet_Icc
  have hb : (∫⁻ p in triangle 0 T,
      ‖geometricScalarSource (triangle 0 T) S p.1 p.2‖ₑ) ≤
      ∫⁻ p in triangle 0 T, ENNReal.ofReal 2048 * stabOrderedKernel (1 / 2) K J p.1 p.2 := by
    apply setLIntegral_mono' (measurableSet_triangle 0 T)
    intro p hp
    rcases hp.2.1.eq_or_lt with heq | hlt
    · have hr : S.r p.1 p.2 = 0 := by
        rw [← heq]
        exact (hset.c1.axis p.1 ⟨hp.1, le_rfl, heq.le.trans hp.2.2⟩).1
      simp only [geometricScalarSource, hr, zero_pow (by decide : 2 ≠ 0),
        mul_zero, div_zero, Complex.ofReal_zero, zero_mul, enorm_zero, zero_le]
    · exact stab_geometric_scalar_ordered_pointwise_c1 hset hε hp.1 hlt hp.2.2
  apply (hb.trans_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)).trans
  have hh := stab_ordered_kernel_triangle_area (T := T) (p := (1 / 2 : ℝ)) (by norm_num) mK mJ
  norm_num only [one_div, inv_div, div_one, ENNReal.ofReal_ofNat] at hh
  have hK : (∫⁻ s in Icc 0 T, K s) ≤ ENNReal.ofReal (A * ε) := by
    dsimp only [K]
    rw [lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      inter_self]
    exact (le_add_of_nonneg_left bot_le).trans hset.env
  have hJ : (∫⁻ s in Icc 0 T, J s) ≤ ENNReal.ofReal (A * ε) := by
    dsimp only [J]
    rw [lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      inter_self]
    exact (le_add_of_nonneg_right bot_le).trans hset.env
  apply (mul_le_mul' le_rfl (hh.trans (mul_le_mul' (mul_le_mul' le_rfl hK) hJ))).trans_eq
  rw [← ENNReal.ofReal_ofNat 2]
  repeat rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end EmcsfAcExtension.Local
