module

public import EmcsfAcExtension.Global.Api.Definitions
import EmcsfAcExtension.Infra.AC.Quotient
import EmcsfAcExtension.Infra.AC.Complex
import EmcsfAcExtension.Local.Calculus.Sections
import EmcsfAcExtension.Global.Observation.Scaling

/-! # A residual gauge parallel to one observation cylinder

The gauge primitive is extended using the endpoint projection only to express
a real function on all of `ℝ`. All cylinder conclusions concern its proper
label interval. No division by the coupling is used.
Source: charged_SF_new_version.tex:L1957–1963; internal project record, boundary-parallel-gauge.
-/

public section

open Set MeasureTheory Complex Filter

namespace EmcsfAcExtension.Global

/-- [internal]
The incoming residual gauge has unit phase, for every real coupling. -/
theorem Observation.norm_gauge_phase (e x : ℝ) :
    ‖Complex.exp (I * e * x)‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- [node prop:charged-observation#boundary-parallel-gauge]
A continuous potential trace on a proper cylinder admits a real C¹ residual
gauge that vanishes at the initial label and kills the potential on that
cylinder. The original axis gauge is not part of the conclusion. -/
theorem Observation.boundary_parallel_gauge (e : ℝ) (S : Fields) (vb : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn (fun u => S.A u (vb u)) (Icc a b)) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ 1 χ ∧ χ a = 0 ∧
      (∀ u ∈ Icc a b, HasDerivAt χ (S.A u (vb u)) u) ∧
      (∀ u ∈ Icc a b, (gaugeFields e S χ).A u (vb u) = 0) ∧
      ∀ u ∈ Icc a b, χ u = ∫ x in a..u, S.A x (vb x) := by
  let w : ℝ → ℝ := fun u => S.A (min (max a u) b) (vb (min (max a u) b))
  have hw : Continuous w := hA.comp_continuous
    ((continuous_const.max continuous_id).min continuous_const)
    (fun u => ⟨le_min (le_max_left _ _) hab, min_le_right _ _⟩)
  let χ : ℝ → ℝ := fun u => ∫ x in a..u, w x
  have hd (u : ℝ) : HasDerivAt χ (w u) u :=
    intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable a u)
      hw.stronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt
  have heq : deriv χ = w := funext fun u => (hd u).deriv
  have hc : ContDiff ℝ 1 χ := contDiff_one_iff_deriv.mpr
    ⟨fun u => (hd u).differentiableAt, by rwa [heq]⟩
  have hfix (u : ℝ) (hu : u ∈ Icc a b) : w u = S.A u (vb u) := by
    dsimp [w]
    rw [max_eq_right hu.1, min_eq_left hu.2]
  refine ⟨χ, hc, by simp [χ], fun u hu => hfix u hu ▸ hd u, ?_, ?_⟩
  · intro u hu
    simp only [gaugeFields, (hd u).deriv, hfix u hu, sub_self]
  · intro u hu
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hu.1] at hx
    exact hfix x ⟨hx.1, hx.2.trans hu.2⟩

/-- [internal]
The geometric fields and scalar moduli are invariant under the residual
gauge. In particular regular-axis zero mass, charge and radius persist. -/
theorem Observation.gauge_invariants (e : ℝ) (S : Fields) (χ : ℝ → ℝ) (u v : ℝ) :
    (gaugeFields e S χ).r u v = S.r u v ∧
    (gaugeFields e S χ).m u v = S.m u v ∧
    (gaugeFields e S χ).Q u v = S.Q u v ∧
    ‖(gaugeFields e S χ).phi u v‖ = ‖S.phi u v‖ ∧
    ‖(gaugeFields e S χ).theta u v‖ = ‖S.theta u v‖ ∧
    ‖(gaugeFields e S χ).xi u v‖ = ‖S.xi u v‖ := by
  simp [gaugeFields, Observation.norm_gauge_phase]

/-- [internal]
The normalized outgoing scalar transforms by the same phase as the scalar.
This identity is valid even if the expansion vanishes away from the domain. -/
theorem Observation.gauge_normalized_out (e : ℝ) (S : Fields) (χ : ℝ → ℝ) (u v : ℝ) :
    (gaugeFields e S χ).a u v = Complex.exp (I * e * χ u) * S.a u v := by
  simp only [Fields.a, gaugeFields]
  ring

/-- [internal]
The actual incoming-coordinate gauge primitive becomes the clock parallel
representative. This proves the clock identity by the chain rule and FTC,
including its endpoints; no change-of-variables premise is assumed. -/
theorem Observation.gauge_clock_representative_of_derivative
    (e : ℝ) (S : Fields) (U V χ : ℝ → ℝ) {a b : ℝ}
    (hU : ContDiff ℝ 1 U)
    (hA : ContinuousOn (fun x => S.A (U x) (V x)) (Icc a b))
    (hχ : ∀ x ∈ Icc a b, HasDerivAt χ (S.A (U x) (V x)) (U x))
    (hχ0 : χ (U a) = 0) :
    EqOn (fun x => (gaugeFields e S χ).a (U x) (V x))
      (curveParallel e S S.a U V a) (Icc a b) := by
  have hUc := contDiff_one_iff_deriv.mp hU
  have hden := hA.mul hUc.2.continuousOn
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun y => χ (U y)) (S.A (U x) (V x) * deriv U x) x :=
    (hχ x hx).comp x (hUc.1 x).hasDerivAt
  intro x hx
  have hsub : uIcc a x ⊆ Icc a b := by
    rw [uIcc_of_le hx.1]
    exact Icc_subset_Icc le_rfl hx.2
  have hi : IntervalIntegrable (fun y => S.A (U y) (V y) * deriv U y) volume a x :=
    (hden.mono (by rw [uIcc_of_le hx.1]; exact Icc_subset_Icc le_rfl hx.2)).intervalIntegrable
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy => hd y (hsub hy)) hi
  rw [hχ0, sub_zero] at he
  change (gaugeFields e S χ).a (U x) (V x) = curveParallel e S S.a U V a x
  rw [Observation.gauge_normalized_out]
  simp only [curveParallel, he]

/-- [internal]
Clock variation in the constructed parallel gauge is exactly the original
covariant variation. No AC or finite-variation premise is needed; internal project record's
covariant variation may therefore be used without a norm loss. -/
theorem Observation.gauge_clock_variation_of_derivative
    (e : ℝ) (S : Fields) (U V χ : ℝ → ℝ) {a b : ℝ}
    (hU : ContDiff ℝ 1 U)
    (hA : ContinuousOn (fun x => S.A (U x) (V x)) (Icc a b))
    (hχ : ∀ x ∈ Icc a b, HasDerivAt χ (S.A (U x) (V x)) (U x))
    (hχ0 : χ (U a) = 0) :
    eVariationOn (fun x => (gaugeFields e S χ).a (U x) (V x)) (Icc a b) =
      curveCovVar e S S.a U V a b :=
  eVariationOn.eq_of_eqOn
    (Observation.gauge_clock_representative_of_derivative e S U V χ hU hA hχ hχ0)

/-- [internal]
The complex FTC turns an actual AC profile and its specified almost
everywhere derivative into integral form. Integrability of that density
is derived from AC, rather than added as a premise. -/
theorem Observation.integralForm_of_ac_ae_complex
    {f g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x ∂volume.restrict (Icc a b), HasDerivAt f (g x) x) :
    IntegralForm f g a b := by
  have hd' : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt f (g x) x := by
    simpa only [uIcc_of_le hab] using (ae_restrict_iff' measurableSet_Icc).mp hd
  have heq : deriv f =ᵐ[volume.restrict (uIoc a b)] g :=
    (ae_restrict_iff' measurableSet_uIoc).mpr
      (hd'.mono fun x hx hmem => (hx (uIoc_subset_uIcc hmem)).deriv)
  have hi := hf.intervalIntegrable_deriv_complex.congr_ae heq
  exact ⟨hi, (hf.integral_eq_sub_of_ae_hasDerivAt_complex hi hd').symm⟩

/-- [internal]
The incoming gauge phase is AC on every compact interval, under exactly
one continuous derivative of the real gauge function. -/
theorem Observation.ac_gauge_phase (e : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => Complex.exp (I * e * χ x)) a b := by
  have hc : AbsolutelyContinuousOnInterval (fun x => e * χ x) a b :=
    (contDiff_const.mul hχ).contDiffOn.absolutelyContinuousOnInterval
  simpa only [Complex.ofReal_mul, mul_assoc] using hc.unit_phase

/-- [internal]
All seven outgoing integral equations survive the residual gauge. The
phase is constant on an outgoing row and the subtracted potential term
is constant there. Only C¹ regularity of the gauge is used. -/
theorem Observation.gauged_out_integral_forms
    {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hseg : outSeg u a b ⊆ D) :
    let P := gaugeFields e S χ
    IntegralForm (P.r u) (P.lam u) a b ∧
      IntegralForm (P.nu u) (P.rUV u) a b ∧
      IntegralForm (P.m u) (P.mV u) a b ∧
      IntegralForm (P.Q u) (P.QV e u) a b ∧
      IntegralForm (P.A u) (P.AV u) a b ∧
      IntegralForm (P.phi u) (P.phiV u) a b ∧
      IntegralForm (P.xi u) (P.xiV e u) a b := by
  have hd := ((contDiff_one_iff_deriv.mp hχ).1 u).hasDerivAt
  have hk (v : ℝ) := gaugeFields_rhs e S χ u v (deriv χ u) hd
  have k₁ := funext (fun v => (hk v).1)
  have k₂ := funext (fun v => (hk v).2.1)
  have k₄ := funext (fun v => (hk v).2.2.2.1)
  have k₆ := funext (fun v => (hk v).2.2.2.2.2.1)
  have k₇ := funext (fun v => (hk v).2.2.2.2.2.2.1)
  have k₉ := funext (fun v => (hk v).2.2.2.2.2.2.2.2.1)
  rcases hS.eq_out u a b hua hab hseg with ⟨hr, hn, hm, hQ, hA, hφ, hξ⟩
  dsimp only
  rw [k₁, k₂, k₄, k₆, k₇, k₉]
  refine ⟨hr, hn, hm, hQ, ?_, ?_, ?_⟩
  · refine ⟨hA.1, ?_⟩
    change (S.A u b - deriv χ u) - (S.A u a - deriv χ u) = ∫ x in a..b, S.AV u x
    rw [← hA.2]
    ring
  · simpa only [gaugeFields, mul_comm] using!
      Observation.integralForm_mul_const hφ (Complex.exp (I * e * χ u))
  · simpa only [gaugeFields, mul_comm] using!
      Observation.integralForm_mul_const hξ (Complex.exp (I * e * χ u))

/-- [internal]
All six incoming integral equations survive the C¹ residual gauge. AC of
the phase times each original scalar profile supplies the product FTC;
no second derivative or BV condition on the gauge derivative is required. -/
theorem Observation.gauged_in_integral_forms
    {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)} (hS : IsSolution e S D)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ) {a b v : ℝ}
    (hab : a ≤ b) (hbv : b < v) (hseg : inSeg a b v ⊆ D) :
    let P := gaugeFields e S χ
    IntegralForm (fun u => P.r u v) (fun u => P.nu u v) a b ∧
      IntegralForm (fun u => P.lam u v) (fun u => P.rUV u v) a b ∧
      IntegralForm (fun u => P.m u v) (fun u => P.mU u v) a b ∧
      IntegralForm (fun u => P.Q u v) (fun u => P.QU e u v) a b ∧
      IntegralForm (fun u => P.phi u v) (fun u => P.phiU e u v) a b ∧
      IntegralForm (fun u => P.theta u v) (fun u => P.thetaU e u v) a b := by
  have hd (u : ℝ) := ((contDiff_one_iff_deriv.mp hχ).1 u).hasDerivAt
  have hk (u : ℝ) := gaugeFields_rhs e S χ u v (deriv χ u) (hd u)
  have k₁ := funext (fun u => (hk u).1)
  have k₃ := funext (fun u => (hk u).2.2.1)
  have k₅ := funext (fun u => (hk u).2.2.2.2.1)
  rcases hS.eq_in a b v hab hbv hseg with ⟨hr, hlam, hm, hQ, _, _⟩
  have hsec := Local.IsSolution.in_section hS hab hbv hseg
  have hphase := Observation.ac_gauge_phase e χ hχ a b
  have hphaseD (u : ℝ) : HasDerivAt (fun x => Complex.exp (I * e * χ x))
      (I * e * deriv χ u * Complex.exp (I * e * χ u)) u := by
    convert ((hd u).ofReal_comp.const_mul (I * e)).cexp using 1
    ring
  dsimp only
  rw [k₁, k₃, k₅]
  refine ⟨hr, hlam, hm, hQ, ?_, ?_⟩
  · apply Observation.integralForm_of_ac_ae_complex hab
      (hphase.mul_normed_ring hsec.2.2.2.2.1.1)
    filter_upwards [hsec.2.2.2.2.1.2] with u hu
    apply ((hphaseD u).mul hu).congr_deriv
    rw [(hk u).2.2.2.2.2.2.2.1]
    ring
  · apply Observation.integralForm_of_ac_ae_complex hab
      (hphase.mul_normed_ring hsec.2.2.2.2.2.1)
    filter_upwards [hsec.2.2.2.2.2.2] with u hu
    apply ((hphaseD u).mul hu).congr_deriv
    rw [(hk u).2.2.2.2.2.2.2.2.2]
    ring

end EmcsfAcExtension.Global
