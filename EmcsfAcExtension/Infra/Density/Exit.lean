module

public import Mathlib
public import EmcsfAcExtension.Infra.Density.Representative
import EmcsfAcExtension.Infra.Density.CurveChain

/-!
# Labelwise histories ending at a moving boundary

Tonelli is applied before any finiteness assertion. An exit function is an
ordinary measurable label function; no evaluation of a product-a.e. derivative
is used. The characteristic history includes its exit endpoint, a null edge.
-/

public section

open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal

namespace EmcsfAcExtension.Global.Density

/-- [internal] Substitution for an L¹ label density along a monotone
bi-Lipschitz label. Integrability of the pulled-back derivative follows from AC
and the chain rule; it is not an additional assumption. The constants `K,L`
are exactly the forward and inverse Lipschitz bounds on this interval. -/
theorem integral_substitution_of_monotone_bilipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {q : ℝ → E} {V : ℝ → ℝ} {a b : ℝ} {K L : ℝ≥0}
    (hV : LipschitzOnWith K V (uIcc a b)) (hm : MonotoneOn V (uIcc a b))
    (ha : AntilipschitzWith L ((uIcc a b).domRestrict V))
    (hq : IntervalIntegrable q volume (V a) (V b)) :
    IntervalIntegrable (fun t => deriv V t • q (V t)) volume a b ∧
      (∫ t in a..b, deriv V t • q (V t)) = ∫ v in V a..V b, q v := by
  let Q : ℝ → E := fun v => ∫ s in V a..v, q s
  have hQ := hq.absolutelyContinuousOnInterval_intervalIntegral_normed left_mem_uIcc
  have hcomp : AbsolutelyContinuousOnInterval (Q ∘ V) a b :=
    hQ.comp_monotoneOn hV.absolutelyContinuousOnInterval hm
  have hgood : ∀ᵐ v, v ∈ uIcc (V a) (V b) → HasDerivAt Q (q v) v :=
    hq.ae_hasDerivAt_integral.mono fun v hv hvm => hv hvm (V a) left_mem_uIcc
  have hpull := ae_pullback_of_antilipschitzOn measurableSet_uIcc ha hgood
  have hd : ∀ᵐ t ∂volume.restrict (uIcc a b),
      HasDerivAt (Q ∘ V) (deriv V t • q (V t)) t := by
    filter_upwards [hpull, ae_restrict_mem measurableSet_uIcc,
      ae_restrict_of_ae hV.absolutelyContinuousOnInterval.ae_differentiableAt]
      with t ht htm hdt
    exact (ht (hm.image_uIcc_subset ⟨t, htm, rfl⟩)).scomp t (hdt htm).hasDerivAt
  have hd' := (ae_restrict_iff' measurableSet_uIcc).mp hd
  have hi : IntervalIntegrable (fun t => deriv V t • q (V t)) volume a b := by
    apply hcomp.intervalIntegrable_deriv_finiteDimensional.congr_ae
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    filter_upwards [hd'] with t ht htm
    exact (ht (uIoc_subset_uIcc htm)).deriv
  refine ⟨hi, ?_⟩
  simpa only [Q, Function.comp_apply, intervalIntegral.integral_same, sub_zero] using
    hcomp.integral_eq_sub_of_ae_hasDerivAt_normed hi hd'

/-- [internal] The boundary cost equals the labelwise exit cost. The label
density at exit is assumed L¹, as supplied by the fixed-density majorant; no
integrability of the boundary evaluation is assumed. This applies to real norms
as well as complex transported densities. -/
theorem integral_boundary_eq_exit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {W : ℝ → ℝ → E} {V τ : ℝ → ℝ} {a b : ℝ} {K L : ℝ≥0}
    (hV : LipschitzOnWith K V (uIcc a b)) (hm : MonotoneOn V (uIcc a b))
    (ha : AntilipschitzWith L ((uIcc a b).domRestrict V))
    (hτ : ∀ t ∈ uIcc a b, τ (V t) = t)
    (hW : IntervalIntegrable (fun v => W (τ v) v) volume (V a) (V b)) :
    IntervalIntegrable (fun t => deriv V t • W t (V t)) volume a b ∧
      (∫ t in a..b, deriv V t • W t (V t)) = ∫ v in V a..V b, W (τ v) v := by
  obtain ⟨hi, heq⟩ := integral_substitution_of_monotone_bilipschitz hV hm ha hW
  have hcongr : (fun t => deriv V t • W (τ (V t)) (V t)) =ᵐ[volume.restrict (uIoc a b)]
      (fun t => deriv V t • W t (V t)) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [hτ t (uIoc_subset_uIcc ht)]
  refine ⟨hi.congr_ae hcongr, ?_⟩
  rw [← heq]
  apply intervalIntegral.integral_congr_ae
  exact (ae_restrict_iff' measurableSet_uIoc).mp hcongr.symm

end EmcsfAcExtension.Global.Density
