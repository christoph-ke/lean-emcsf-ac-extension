module

public import EmcsfAcExtension.Infra.AC.Primitive
public import EmcsfAcExtension.Frozen.IntegralForm
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Infra.BV.Basic
import EmcsfAcExtension.Infra.Null.IntegralForm

/-! # Endpoint AC recovery from bounded variation

A continuous finite-variation curve differentiable throughout the open
interval has no remaining singular variation: its derivative is integrable
and FTC on every closed subinterval gives its AC primitive representative.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace EmcsfAcExtension.Local

/-- Recover endpoint AC from continuity, finite variation and interior
differentiability. This finite-dimensional analytic helper introduces no
constant and applies to both real and complex characteristic curves. -/
theorem ac_of_continuous_bv_of_differentiableOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hb : BoundedVariationOn f (Icc a b))
    (hd : DifferentiableOn ℝ f (Ioo a b)) : AbsolutelyContinuousOnInterval f a b := by
  have hi := hb.intervalIntegrable_deriv_finiteDimensional hab
  have hprim : ∀ x ∈ Icc a b, f x = f a + ∫ t in a..x, deriv f t := by
    intro x hx
    have hsub : uIcc a x ⊆ uIcc a b := by
      rw [uIcc_of_le hx.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl hx.2
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
      (hc.mono (Icc_subset_Icc le_rfl hx.2)) (fun y hy =>
        ((hd y ⟨hy.1, hy.2.trans_le hx.2⟩).differentiableAt
          (isOpen_Ioo.mem_nhds ⟨hy.1, hy.2.trans_le hx.2⟩)).hasDerivAt)
      (hi.mono_set hsub)
    rw [hftc]
    abel
  have hp := ((LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval
    (a := a) (b := b)).add
      (hi.absolutelyContinuousOnInterval_intervalIntegral_normed left_mem_uIcc)
  exact hp.congr (fun x hx => (hprim x (by simpa only [uIcc_of_le hab] using hx)).symm)

/-- Continuous densities in interior integral equations recover the full AC
primitive, including both endpoints. No endpoint equation or estimate is an
extra hypothesis, and the primitive coefficient is one. -/
theorem ac_of_continuous_density_of_interior_equations {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f q : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (heq : ∀ c d, a < c → c ≤ d → d < b → IntegralForm f q c d) :
    AbsolutelyContinuousOnInterval f a b := by
  have hd x (hx : x ∈ Ioo a b) : HasDerivAt f (q x) x :=
    hasDerivAt_of_integralForm_interior hx (hq.mono Ioo_subset_Icc_self) heq
  apply absolutelyContinuousOnInterval_of_integralForm_on hab
  · intro x hx
    have hs : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
    have hi := (hq.mono hs).intervalIntegrable_of_Icc (μ := volume) hx.1
    exact ⟨hi, (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 (hf.mono hs)
      (fun y hy => hd y ⟨hy.1, hy.2.trans_le hx.2⟩) hi).symm⟩

/-- Recover AC at a left endpoint from one finite-variation neighborhood and
continuous integral equations everywhere to its right. The coefficient is one
and no derivative bound is required at the endpoint. -/
theorem ac_of_left_bv_of_interior_equations {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f q : ℝ → E} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hq : ContinuousOn q (Ioc a b))
    (heq : ∀ c d, a < c → c ≤ d → d ≤ b → IntegralForm f q c d)
    (hlocal : ∃ c ∈ Ioc a b, BoundedVariationOn f (Icc a c)) :
    AbsolutelyContinuousOnInterval f a b := by
  obtain ⟨c, hc, hcbv⟩ := hlocal
  have hac : AbsolutelyContinuousOnInterval f c b :=
    absolutelyContinuousOnInterval_of_integralForm_on hc.2
      (fun x hx => heq c x hc.1 hx.1 hx.2)
  have hbv := hcbv.trans_Icc (hac.boundedVariationOn_Icc hc.2) hc.1.le hc.2
  apply ac_of_continuous_bv_of_differentiableOn hab.le hf hbv
  intro x hx
  exact (hasDerivAt_of_integralForm_interior hx (hq.mono Ioo_subset_Ioc_self)
    (fun c d hac hcd hdb => heq c d hac hcd hdb.le)).differentiableAt.differentiableWithinAt

/-- Recover AC at a right endpoint from one finite-variation neighborhood and
continuous integral equations to its left. The coefficient is one; all
exceptional endpoint behavior is excluded by continuity and finite variation. -/
theorem ac_of_right_bv_of_interior_equations {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f q : ℝ → E} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hq : ContinuousOn q (Ico a b))
    (heq : ∀ c d, a ≤ c → c ≤ d → d < b → IntegralForm f q c d)
    (hlocal : ∃ c ∈ Ico a b, BoundedVariationOn f (Icc c b)) :
    AbsolutelyContinuousOnInterval f a b := by
  obtain ⟨c, hc, hcbv⟩ := hlocal
  have hac : AbsolutelyContinuousOnInterval f a c :=
    absolutelyContinuousOnInterval_of_integralForm_on hc.1
      (fun x hx => heq a x le_rfl hx.1 (hx.2.trans_lt hc.2))
  have hbv := (hac.boundedVariationOn_Icc hc.1).trans_Icc hcbv hc.1 hc.2.le
  apply ac_of_continuous_bv_of_differentiableOn hab.le hf hbv
  intro x hx
  exact (hasDerivAt_of_integralForm_interior hx (hq.mono Ioo_subset_Ico_self)
    (fun c d hac hcd hdb => heq c d hac.le hcd hdb)).differentiableAt.differentiableWithinAt

end EmcsfAcExtension.Local
