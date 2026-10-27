module

public import EmcsfAcExtension.Local.Stability.SourceDifferenceEM
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMIntegrable
import EmcsfAcExtension.Local.Stability.SourceDifferenceScalarMeasurable
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Infra.Null.Parametric

/-! # Borel electromagnetic transport sources on the whole triangle

The primitive integrands are continuous through the axis. Explicit Maxwell
terms are total rational expressions in continuous field extensions.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Stab

private theorem measurable_emSource_pair {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) :
    Measurable ((triangle 0 T).indicator (Function.uncurry (emSourceJ e S))) ∧
    Measurable ((triangle 0 T).indicator (Function.uncurry (emSourceK e S))) := by
  let R := fun p => Function.uncurry S.r (triangleProj 0 T p)
  let L := fun p => Function.uncurry S.lam (triangleProj 0 T p)
  let N := fun p => Function.uncurry S.nu (triangleProj 0 T p)
  let Q := fun p => Function.uncurry S.Q (triangleProj 0 T p)
  let X := fun p => Function.uncurry S.theta (triangleProj 0 T p)
  let Y := fun p => Function.uncurry S.xi (triangleProj 0 T p)
  let F := fun p => Function.uncurry S.phi (triangleProj 0 T p)
  have hR : Continuous R := continuous_comp_triangleProj hs.pos.le hs.c1.c1_r.continuousOn
  have hL : Continuous L := continuous_comp_triangleProj hs.pos.le hs.c1.c1_lam.continuousOn
  have hN : Continuous N := continuous_comp_triangleProj hs.pos.le hs.c1.c1_nu.continuousOn
  have hQ : Continuous Q := continuous_comp_triangleProj hs.pos.le hs.c1.c1_Q.continuousOn
  have hX : Continuous X := continuous_comp_triangleProj hs.pos.le hs.c1.c1_theta.continuousOn
  have hY : Continuous Y := continuous_comp_triangleProj hs.pos.le hs.c1.c1_xi.continuousOn
  have hF : Continuous F := continuous_comp_triangleProj hs.pos.le hs.c1.c1_phi.continuousOn
  have hmo : Measurable (fun p =>
      (((-N p) * L p / R p ^ 2 : ℝ) : ℂ) *
        (5 * ((Q p ^ 2 / R p ^ 2 : ℝ) : ℂ) * (X p / (L p : ℂ)) +
          I * e * Q p * (3 * (X p / (L p : ℂ)) + F p)) +
        I * e * (-N p) * (-e * R p * (starRingEnd ℂ (F p) * X p).im) * F p / R p) := by fun_prop
  have hmi : Measurable (fun p =>
      (((-N p) * L p / R p ^ 2 : ℝ) : ℂ) *
        (5 * ((Q p ^ 2 / R p ^ 2 : ℝ) : ℂ) * (Y p / (N p : ℂ)) -
          I * e * Q p * (3 * (Y p / (N p : ℂ)) + F p)) +
        I * e * L p * (e * R p * (starRingEnd ℂ (F p) * Y p).im) * F p / R p) := by fun_prop
  constructor
  · convert hmo.indicator (measurableSet_triangle 0 T) using 1
    funext p
    by_cases hp : p ∈ triangle 0 T
    · simp only [indicator_of_mem hp, R, L, N, Q, X, F, triangleProj_of_mem hp,
        Function.uncurry_def, emSourceJ, Fields.QV]
      push_cast
      ring
    · simp only [indicator_of_notMem hp]
  · convert hmi.indicator (measurableSet_triangle 0 T) using 1
    funext p
    by_cases hp : p ∈ triangle 0 T
    · simp only [indicator_of_mem hp, R, L, N, Q, Y, F, triangleProj_of_mem hp,
        Function.uncurry_def, emSourceK, Fields.QU]
      push_cast
      ring
    · simp only [indicator_of_notMem hp]

/-- Both complete electromagnetic transport sources have measurable zero
extensions. No field regularity is assumed outside the closed triangle. -/
theorem measurable_emTransportSource_pair {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) :
    Measurable ((triangle 0 T).indicator (Function.uncurry (emTransportSourceJ e S))) ∧
    Measurable ((triangle 0 T).indicator (Function.uncurry (emTransportSourceK e S))) := by
  have hraw := emPrimitive_continuousOn hs
  have hZo := continuousOn_integral_outgoing hraw.1
  have hZi := continuousOn_integral_incoming_between hraw.2
  have hco := measurable_inverse_cube_primitive_source hs.pos.le hs.c1.c1_r.continuousOn
    hs.c1.c1_nu.continuousOn hs.c1.c1_theta.continuousOn hZo
  have hci := measurable_inverse_cube_primitive_source hs.pos.le hs.c1.c1_r.continuousOn
    hs.c1.c1_lam.continuousOn.neg hs.c1.c1_xi.continuousOn hZi
  have hcurvo : Measurable ((triangle 0 T).indicator (fun p =>
      (S.nu p.1 p.2 : ℂ) * S.theta p.1 p.2 / (S.r p.1 p.2 : ℂ) ^ 2 *
        (curvEM e S p.1 p.2 + 2 * starRingEnd ℂ (curvEM e S p.1 p.2)))) := by
    convert hco using 1
    funext p
    by_cases hp : p ∈ triangle 0 T
    · simp only [indicator_of_mem hp]
      exact em_curvature_source_j_eq_primitive e S p.1 p.2
    · simp only [indicator_of_notMem hp]
  have hcurvi : Measurable ((triangle 0 T).indicator (fun p =>
      (S.lam p.1 p.2 : ℂ) * S.xi p.1 p.2 / (S.r p.1 p.2 : ℂ) ^ 2 *
        (curvEMIn e S p.1 p.2 + 2 * starRingEnd ℂ (curvEMIn e S p.1 p.2)))) := by
    convert hci using 1
    funext p
    by_cases hp : p ∈ triangle 0 T
    · simp only [indicator_of_mem hp, Pi.neg_apply, Function.uncurry_def, Complex.ofReal_neg]
      exact em_curvature_source_k_eq_primitive e S p.1 p.2
    · simp only [indicator_of_notMem hp]
  have he := measurable_emSource_pair hs
  constructor
  · convert hcurvo.fun_add he.1 using 1
    funext p
    by_cases hp : p ∈ triangle 0 T
    · simp only [indicator_of_mem hp, Function.uncurry_def, emTransportSourceJ]
    · simp only [indicator_of_notMem hp, add_zero]
  · convert hcurvi.fun_add he.2 using 1
    funext p
    by_cases hp : p ∈ triangle 0 T
    · simp only [indicator_of_mem hp, Function.uncurry_def, emTransportSourceK]
    · simp only [indicator_of_notMem hp, add_zero]

end EmcsfAcExtension.Local.Stab
