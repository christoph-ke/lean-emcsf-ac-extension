module

public import EmcsfAcExtension.Local.Stability.JCloseCoefficient
public import EmcsfAcExtension.Local.Stability.SourceDifferenceEM
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMMeasurable
import EmcsfAcExtension.Local.Stability.SourceDifferenceScalarMeasurable
import EmcsfAcExtension.Local.Stability.JCloseTransport
import EmcsfAcExtension.Local.Stability.KClose
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Literal difference forcings and their Borel representatives

The connection difference remains in the j forcing. Scalar and charged
curvature primitives keep the approved split throughout subtraction.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Stab

/-- The literal scalar-curvature part of the j transport source. -/
@[expose] noncomputable def scalarTransportSourceJ (T : ℝ) (S : Fields) (u v : ℝ) : ℂ :=
  (S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2 *
    (curvScalar (triangle 0 T) S u v + 2 * starRingEnd ℂ (curvScalar (triangle 0 T) S u v))

/-- The literal scalar-curvature part of the k transport source. -/
@[expose] noncomputable def scalarTransportSourceK (e T : ℝ) (S : Fields) (u v : ℝ) : ℂ :=
  (S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
    (curvScalarIn e (triangle 0 T) S u v +
      2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S u v))

/-- The full inhomogeneous difference forcing in the common-gauge j equation. -/
@[expose] noncomputable def jDifferenceForcing (e T : ℝ) (S₁ S₂ : Fields) (u v : ℝ) : ℂ :=
  ((jRealCoefficient S₁ u v - jRealCoefficient S₂ u v : ℝ) : ℂ) * jC1 (triangle 0 T) S₂ u v -
    I * e * (S₁.A u v - S₂.A u v) * jC1 (triangle 0 T) S₂ u v +
    (scalarTransportSourceJ T S₁ u v - scalarTransportSourceJ T S₂ u v) +
    (emTransportSourceJ e S₁ u v - emTransportSourceJ e S₂ u v)

/-- The full inhomogeneous difference forcing in the ordinary outgoing k equation. -/
@[expose] noncomputable def kDifferenceForcing (e T : ℝ) (S₁ S₂ : Fields) (u v : ℝ) : ℂ :=
  ((kRealCoefficient S₁ u v - kRealCoefficient S₂ u v : ℝ) : ℂ) * kC1 e (triangle 0 T) S₂ u v +
    (scalarTransportSourceK e T S₁ u v - scalarTransportSourceK e T S₂ u v) +
    (emTransportSourceK e S₁ u v - emTransportSourceK e S₂ u v)

/-- A continuous complex field on the triangle has a measurable zero
extension. No regularity is required outside that triangle. -/
theorem measurable_triangle_indicator_of_continuousOn {T : ℝ} {f : ℝ × ℝ → ℂ}
    (hf : ContinuousOn f (triangle 0 T)) : Measurable ((triangle 0 T).indicator f) := by
  classical
  exact hf.measurable_piecewise continuousOn_const (measurableSet_triangle 0 T)

/-- Both complete difference forcings have measurable zero extensions.
The result follows from the settings and the literal source identities;
no integrability or difference estimate is assumed. -/
theorem measurable_difference_forcings {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hs₁ : StabSetting e T ε M A S₁ h₁) (hs₂ : StabSetting e T ε M A S₂ h₂) :
    Measurable ((triangle 0 T).indicator (Function.uncurry (jDifferenceForcing e T S₁ S₂))) ∧
    Measurable ((triangle 0 T).indicator (Function.uncurry (kDifferenceForcing e T S₁ S₂))) := by
  have hc₁ := transport_real_coefficients_continuousOn hs₁
  have hc₂ := transport_real_coefficients_continuousOn hs₂
  have hcj₁ := hc₁.1
  have hcj₂ := hc₂.1
  have hck₁ := hc₁.2
  have hck₂ := hc₂.2
  have hj := continuousOn_jC1_aux hs₂.pos hs₂.c1
  have hk := continuousOn_kC1_aux hs₂.pos hs₂.c1
  have hA₁ := hs₁.c1.c1_A.continuousOn
  have hA₂ := hs₂.c1.c1_A.continuousOn
  have hδj : ContinuousOn (fun p => ((jRealCoefficient S₁ p.1 p.2 - jRealCoefficient S₂ p.1 p.2 : ℝ)
      : ℂ) *
      jC1 (triangle 0 T) S₂ p.1 p.2 - I * e * (S₁.A p.1 p.2 - S₂.A p.1 p.2) *
        jC1 (triangle 0 T) S₂ p.1 p.2) (triangle 0 T) := by fun_prop
  have hδk : ContinuousOn (fun p => ((kRealCoefficient S₁ p.1 p.2 - kRealCoefficient S₂ p.1 p.2 : ℝ)
      : ℂ) *
      kC1 e (triangle 0 T) S₂ p.1 p.2) (triangle 0 T) := by fun_prop
  have hsc₁j := measurable_scalar_source_j hs₁
  have hsc₂j := measurable_scalar_source_j hs₂
  have hsc₁k := measurable_scalar_source_k hs₁
  have hsc₂k := measurable_scalar_source_k hs₂
  have he₁ := measurable_emTransportSource_pair hs₁
  have he₂ := measurable_emTransportSource_pair hs₂
  have hmj := ((measurable_triangle_indicator_of_continuousOn hδj).fun_add
    (hsc₁j.fun_sub hsc₂j)).fun_add (he₁.1.fun_sub he₂.1)
  have hmk := ((measurable_triangle_indicator_of_continuousOn hδk).fun_add
    (hsc₁k.fun_sub hsc₂k)).fun_add (he₁.2.fun_sub he₂.2)
  constructor
  · convert hmj using 1
    funext p
    by_cases hp : p ∈ triangle 0 T
    · simp only [indicator_of_mem hp, jDifferenceForcing, scalarTransportSourceJ,
        Function.uncurry_def]
    · simp only [indicator_of_notMem hp, sub_self, add_zero]
  · convert hmk using 1
    funext p
    by_cases hp : p ∈ triangle 0 T
    · simp only [indicator_of_mem hp, kDifferenceForcing, scalarTransportSourceK,
        Function.uncurry_def]
    · simp only [indicator_of_notMem hp, sub_self, add_zero]

/-- The j difference equation in literal linear-transport form.
Its homogeneous complex coefficient retains the first field's connection. -/
theorem j_difference_transport_forcing {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hs₁ : StabSetting e T ε M A S₁ h₁) (hs₂ : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun w => jC1 (triangle 0 T) S₁ w v - jC1 (triangle 0 T) S₂ w v)
      ((((jRealCoefficient S₁ u v : ℝ) : ℂ) - I * e * S₁.A u v) *
          (jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v) +
        jDifferenceForcing e T S₁ S₂ u v) (Icc 0 v) u := by
  have hd := j_difference_transport hs₁ hs₂ hu huv hvT
  dsimp only at hd
  convert hd using 1
  dsimp only [jDifferenceForcing, scalarTransportSourceJ, emTransportSourceJ, jRealCoefficient]
  push_cast
  ring

/-- The k difference equation in literal linear-transport form.
There is no connection forcing in this outgoing equation. -/
theorem k_difference_transport_forcing {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (hs₁ : StabSetting e T ε M A S₁ h₁) (hs₂ : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun w => kC1 e (triangle 0 T) S₁ u w - kC1 e (triangle 0 T) S₂ u w)
      ((kRealCoefficient S₁ u v : ℂ) *
          (kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v) +
        kDifferenceForcing e T S₁ S₂ u v) (Icc u T) v := by
  have hd := k_difference_transport hs₁ hs₂ hu huv hvT
  dsimp only at hd
  convert hd using 1
  dsimp only [kDifferenceForcing, scalarTransportSourceK, emTransportSourceK, kRealCoefficient]
  push_cast
  ring

end EmcsfAcExtension.Local.Stab
