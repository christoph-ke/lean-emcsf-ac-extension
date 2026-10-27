module

public import EmcsfAcExtension.Infra.Triangle
import EmcsfAcExtension.Local.Apriori.AreaJKernel
import EmcsfAcExtension.Local.Apriori.AreaKKernel

/-! # Hardy form of the ordered primitive area bounds

The inverse-cube kernel is integrated before the primitive variable. The
remaining coordinate Hardy weight can be applied to a ratio difference,
so this estimate is multilinear in the two independent nonnegative inputs.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- Outgoing inverse-cube scalar primitive kernel with two independent inputs. -/
@[expose] noncomputable def scalarPrimitiveKernelOut
    (F : ℝ × ℝ → ℝ≥0∞) (J : ℝ → ℝ≥0∞) (u v : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (v - u) ^ 3) *
    ∫⁻ w in Icc u v, ENNReal.ofReal (w - u) * F (u, w) * J w

/-- Incoming inverse-cube scalar primitive kernel with its reflected radial factor. -/
@[expose] noncomputable def scalarPrimitiveKernelIn
    (F : ℝ × ℝ → ℝ≥0∞) (K : ℝ → ℝ≥0∞) (u v : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (v - u) ^ 3) *
    ∫⁻ w in Icc u v, ENNReal.ofReal (v - w) * F (w, v) * K w

/-- Joint measurability of the outgoing primitive kernel. Its variable
endpoints are encoded by a measurable indicator before integrating. -/
theorem measurable_scalarPrimitiveKernelOut {F : ℝ × ℝ → ℝ≥0∞}
    {J : ℝ → ℝ≥0∞} (hF : Measurable F) (hJ : Measurable J) :
    Measurable (Function.uncurry (scalarPrimitiveKernelOut F J)) := by
  have hset : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2 ∧ q.2 ≤ q.1.2} :=
    (measurableSet_le measurable_fst.fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.snd)
  have hbase : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal (q.2 - q.1.1) * F (q.1.1, q.2) * J q.2) := by fun_prop
  have hm := hbase.indicator hset
  have hi : Measurable (fun p : ℝ × ℝ =>
      ∫⁻ w in Icc p.1 p.2, ENNReal.ofReal (w - p.1) * F (p.1, w) * J w) := by
    convert hm.lintegral_prod_right' (ν := (volume : Measure ℝ)) using 1
    funext p
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro w
    rfl
  exact (by fun_prop : Measurable (fun p : ℝ × ℝ =>
    ENNReal.ofReal (1 / (p.2 - p.1) ^ 3))).mul hi

/-- Joint measurability of the incoming primitive kernel, with its original
incoming orientation. No finite-mass assumption is needed. -/
theorem measurable_scalarPrimitiveKernelIn {F : ℝ × ℝ → ℝ≥0∞}
    {K : ℝ → ℝ≥0∞} (hF : Measurable F) (hK : Measurable K) :
    Measurable (Function.uncurry (scalarPrimitiveKernelIn F K)) := by
  have hset : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.1.1 ≤ q.2 ∧ q.2 ≤ q.1.2} :=
    (measurableSet_le measurable_fst.fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.snd)
  have hbase : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal (q.1.2 - q.2) * F (q.2, q.1.2) * K q.2) := by fun_prop
  have hm := hbase.indicator hset
  have hi : Measurable (fun p : ℝ × ℝ =>
      ∫⁻ w in Icc p.1 p.2, ENNReal.ofReal (p.2 - w) * F (w, p.2) * K w) := by
    convert hm.lintegral_prod_right' (ν := (volume : Measure ℝ)) using 1
    funext p
    rw [← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro w
    rfl
  exact (by fun_prop : Measurable (fun p : ℝ × ℝ =>
    ENNReal.ofReal (1 / (p.2 - p.1) ^ 3))).mul hi

private theorem inverse_square_mul_radius {d : ℝ} (hd : 0 ≤ d) :
    ENNReal.ofReal (1 / (2 * d ^ 2)) * ENNReal.ofReal d =
      ENNReal.ofReal (1 / 2) * ENNReal.ofReal (1 / d) := by
  by_cases hd0 : d = 0
  · simp [hd0]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * d ^ 2)),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  field_simp

/-- Outgoing primitive area estimate with an incoming Hardy budget.
The coefficient is exactly `1/2`, uniform in the triangle and in the
measurable nonnegative functions, including functions of infinite mass. -/
theorem outgoing_primitive_hardy_area {T : ℝ} {F : ℝ × ℝ → ℝ≥0∞}
    {J : ℝ → ℝ≥0∞} {B : ℝ≥0∞} (hF : Measurable F) (hJ : Measurable J)
    (hHardy : ∀ w ∈ Icc 0 T,
      (∫⁻ u in Icc 0 w, ENNReal.ofReal (1 / (w - u)) * F (u, w)) ≤ B) :
    (∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T,
      ENNReal.ofReal (1 / (v - u) ^ 3) *
        ∫⁻ w in Icc u v, ENNReal.ofReal (w - u) * F (u, w) * J w) ≤
      ENNReal.ofReal (1 / 2) * B * ∫⁻ w in Icc 0 T, J w := by
  have harea := Area.outgoing_primitive_area_le (a₀ := 0) (T := T)
    (F := fun p : ℝ × ℝ => ENNReal.ofReal (p.2 - p.1) * F p * J p.2) (by fun_prop)
  apply harea.trans
  calc
    _ ≤ ∫⁻ w in Icc 0 T, ENNReal.ofReal (1 / 2) * B * J w := by
      apply setLIntegral_mono' measurableSet_Icc
      intro w hw
      calc
        _ = ∫⁻ u in Icc 0 w, (ENNReal.ofReal (1 / 2) *
            (ENNReal.ofReal (1 / (w - u)) * F (u, w))) * J w := by
          apply setLIntegral_congr_fun measurableSet_Icc
          intro u hu
          dsimp only
          rw [← mul_assoc, ← mul_assoc,
            inverse_square_mul_radius (sub_nonneg.mpr hu.2)]
          ac_rfl
        _ = (ENNReal.ofReal (1 / 2) *
            ∫⁻ u in Icc 0 w, ENNReal.ofReal (1 / (w - u)) * F (u, w)) * J w := by
          rw [lintegral_mul_const'' _ (by fun_prop :
            AEMeasurable (fun u : ℝ => ENNReal.ofReal (1 / 2) *
              (ENNReal.ofReal (1 / (w - u)) * F (u, w))) _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl (hHardy w hw)) le_rfl
    _ = _ := lintegral_const_mul _ hJ

/-- Incoming primitive area estimate with an outgoing Hardy budget.
The coefficient is exactly `1/2`, uniformly in all inputs; the reflected
integration order leaves the outgoing rather than incoming Hardy weight. -/
theorem incoming_primitive_hardy_area {T : ℝ} {F : ℝ × ℝ → ℝ≥0∞}
    {K : ℝ → ℝ≥0∞} {B : ℝ≥0∞} (hF : Measurable F) (hK : Measurable K)
    (hHardy : ∀ w ∈ Icc 0 T,
      (∫⁻ v in Icc w T, ENNReal.ofReal (1 / (v - w)) * F (w, v)) ≤ B) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
      ENNReal.ofReal (1 / (v - u) ^ 3) *
        ∫⁻ w in Icc u v, ENNReal.ofReal (v - w) * F (w, v) * K w) ≤
      ENNReal.ofReal (1 / 2) * B * ∫⁻ w in Icc 0 T, K w := by
  have harea := Area.incoming_primitive_area_le (T := T)
    (F := fun p : ℝ × ℝ => ENNReal.ofReal (p.2 - p.1) * F p * K p.1) (by fun_prop)
  apply harea.trans
  calc
    _ ≤ ∫⁻ w in Icc 0 T, ENNReal.ofReal (1 / 2) * B * K w := by
      apply setLIntegral_mono' measurableSet_Icc
      intro w hw
      calc
        _ = ∫⁻ v in Icc w T, (ENNReal.ofReal (1 / 2) *
            (ENNReal.ofReal (1 / (v - w)) * F (w, v))) * K w := by
          apply setLIntegral_congr_fun measurableSet_Icc
          intro v hv
          dsimp only
          rw [← mul_assoc, ← mul_assoc,
            inverse_square_mul_radius (sub_nonneg.mpr hv.1)]
          ac_rfl
        _ = (ENNReal.ofReal (1 / 2) *
            ∫⁻ v in Icc w T, ENNReal.ofReal (1 / (v - w)) * F (w, v)) * K w := by
          rw [lintegral_mul_const'' _ (by fun_prop :
            AEMeasurable (fun v : ℝ => ENNReal.ofReal (1 / 2) *
              (ENNReal.ofReal (1 / (v - w)) * F (w, v))) _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl (hHardy w hw)) le_rfl
    _ = _ := lintegral_const_mul _ hK

/-- Product-measure outgoing kernel budget. The universal coefficient
`1/2` is uniform in the triangle and all nonnegative inputs. -/
theorem outgoing_primitive_kernel_area_le {T : ℝ} {F : ℝ × ℝ → ℝ≥0∞}
    {J : ℝ → ℝ≥0∞} {B : ℝ≥0∞} (hF : Measurable F) (hJ : Measurable J)
    (hHardy : ∀ w ∈ Icc 0 T,
      (∫⁻ u in Icc 0 w, ENNReal.ofReal (1 / (w - u)) * F (u, w)) ≤ B) :
    (∫⁻ p in triangle 0 T, scalarPrimitiveKernelOut F J p.1 p.2 ∂(volume.prod volume)) ≤
      ENNReal.ofReal (1 / 2) * B * ∫⁻ w in Icc 0 T, J w := by
  have hm : Measurable (fun p : ℝ × ℝ => scalarPrimitiveKernelOut F J p.1 p.2) := by
    simpa only [Function.uncurry_def] using measurable_scalarPrimitiveKernelOut hF hJ
  rw [lintegral_triangle_eq_lintegral_lintegral hm]
  exact outgoing_primitive_hardy_area hF hJ hHardy

/-- Product-measure incoming kernel budget with its outgoing Hardy norm.
The numerical coefficient `1/2` is universal and no finiteness is assumed. -/
theorem incoming_primitive_kernel_area_le {T : ℝ} {F : ℝ × ℝ → ℝ≥0∞}
    {K : ℝ → ℝ≥0∞} {B : ℝ≥0∞} (hF : Measurable F) (hK : Measurable K)
    (hHardy : ∀ w ∈ Icc 0 T,
      (∫⁻ v in Icc w T, ENNReal.ofReal (1 / (v - w)) * F (w, v)) ≤ B) :
    (∫⁻ p in triangle 0 T, scalarPrimitiveKernelIn F K p.1 p.2 ∂(volume.prod volume)) ≤
      ENNReal.ofReal (1 / 2) * B * ∫⁻ w in Icc 0 T, K w := by
  have hm : Measurable (fun p : ℝ × ℝ => scalarPrimitiveKernelIn F K p.1 p.2) := by
    simpa only [Function.uncurry_def] using measurable_scalarPrimitiveKernelIn hF hK
  rw [lintegral_triangle_eq_lintegral_lintegral_symm hm]
  exact incoming_primitive_hardy_area hF hK hHardy

end EmcsfAcExtension.Local.Stab
