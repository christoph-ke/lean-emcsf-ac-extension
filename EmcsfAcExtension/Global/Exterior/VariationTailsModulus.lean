module

public import EmcsfAcExtension.Global.Exterior.DerivativeSource
public import EmcsfAcExtension.Infra.LinearTransport
import EmcsfAcExtension.Infra.Density.Exit

/-! # Incoming modulus and stopped-history integration

The imaginary electromagnetic coefficient is removed before taking norms.
The resulting estimate is the integrated M2 of approved internal project record,
`charged_SF_new_version.tex:L1337–L1340`, L1413–L1416. Its numerical coefficient is
one, uniformly in the characteristic, field, and interval.
-/

public section

open Set MeasureTheory Filter Topology Complex

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
The integrated modulus inequality for complex AC transport with a real
coefficient and an imaginary connection. The connection contributes no
norm growth. No differentiability of the norm at its zero set is needed. -/
theorem norm_le_initial_add_integral_of_covariant_transport
    {g q : ℝ → ℂ} {α κ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hg : AbsolutelyContinuousOnInterval g a b)
    (hα : ContinuousOn α (Icc a b)) (hκ : ContinuousOn κ (Icc a b))
    (hq : IntervalIntegrable q volume a b)
    (hd : ∀ᵐ u ∂volume.restrict (Icc a b),
      deriv g u = ((α u : ℂ) - I * κ u) * g u + q u) :
    ‖g b‖ ≤ ‖g a‖ + ∫ u in a..b, (|α u| * ‖g u‖ + ‖q u‖) := by
  let c : ℝ → ℂ := fun u => -I * κ u
  let f : ℝ → ℂ := fun u => (α u : ℂ) * g u + q u
  have hc : IntervalIntegrable c volume a b :=
    ((Complex.continuous_ofReal.comp_continuousOn hκ).const_mul (-I)).intervalIntegrable_of_Icc hab
  have hga : IntervalIntegrable (fun u => (α u : ℂ) * g u) volume a b :=
    ((Complex.continuous_ofReal.comp_continuousOn hα).mul
      (by simpa only [uIcc_of_le hab] using hg.continuousOn)).intervalIntegrable_of_Icc hab
  have hf : IntervalIntegrable f volume a b := hga.add hq
  have hd' : ∀ᵐ u ∂volume.restrict (Icc a b), deriv g u = c u * g u + f u := by
    filter_upwards [hd] with u hu
    rw [hu]
    dsimp [c, f]
    ring
  have heq := eq_integratingFactor_of_ac_deriv_eq_complex hab hg hc hf hd' b ⟨hab, le_rfl⟩
  have hc0 (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ u in a..t, c u).re = 0 := by
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    change RCLike.re (∫ u in a..t, c u) = 0
    rw [← intervalIntegral.intervalIntegral_re (hc.mono_set hsub)]
    simp [c]
  have hp (t : ℝ) (ht : t ∈ Icc a b) :
      ‖Complex.exp (-(∫ u in a..t, c u))‖ = 1 := by
    rw [Complex.norm_exp, Complex.neg_re, hc0 t ht, neg_zero, Real.exp_zero]
  have hfi : IntervalIntegrable
      (fun u => Complex.exp (-(∫ s in a..u, c s)) * f u) volume a b :=
    hf.continuousOn_mul (hc.absolutelyContinuousOnInterval_intervalIntegral_complex
      left_mem_uIcc).neg.cexp.continuousOn
  have hboundi : IntervalIntegrable (fun u => |α u| * ‖g u‖ + ‖q u‖) volume a b :=
    ((hα.abs.mul (by
      simpa only [uIcc_of_le hab] using hg.continuousOn.norm)).intervalIntegrable_of_Icc
      hab).add hq.norm
  rw [heq, norm_mul, Complex.norm_exp, hc0 b ⟨hab, le_rfl⟩, Real.exp_zero, one_mul]
  calc
    ‖g a + ∫ u in a..b, Complex.exp (-(∫ s in a..u, c s)) * f u‖ ≤
        ‖g a‖ + ‖∫ u in a..b, Complex.exp (-(∫ s in a..u, c s)) * f u‖ := norm_add_le _ _
    _ ≤ ‖g a‖ + ∫ u in a..b,
        ‖Complex.exp (-(∫ s in a..u, c s)) * f u‖ :=
      add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hab)
    _ ≤ ‖g a‖ + ∫ u in a..b, (|α u| * ‖g u‖ + ‖q u‖) := by
      apply add_le_add le_rfl
      apply intervalIntegral.integral_mono_on hab hfi.norm hboundi
      intro u hu
      rw [norm_mul, hp u hu, one_mul]
      exact (norm_add_le _ _).trans_eq (by simp [Complex.norm_real, Real.norm_eq_abs])

/-- [internal]
Real Fubini for measurable stopped histories, with the active labels
displayed in the other order. The integrability assumption is on the
actual swept set; no regularity through the axis is requested. -/
theorem integral_integral_swap_stopped_histories
    {H : ℝ × ℝ → ℝ} {τ t : ℝ → ℝ} {a b c d : ℝ}
    (_hτ : Measurable τ)
    (hK : MeasurableSet {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (t p.1) d})
    (hτb : ∀ v ∈ Icc c d, τ v ≤ b)
    (htc : ∀ u ∈ Icc a b, c ≤ t u)
    (hexit : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, u ≤ τ v ↔ t u ≤ v)
    (hH : IntegrableOn H {p | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (t p.1) d}
      (volume.prod volume)) :
    (∫ v in Icc c d, ∫ u in Icc a (τ v), H (u, v)) =
      ∫ u in Icc a b, ∫ v in Icc (t u) d, H (u, v) := by
  classical
  let K : Set (ℝ × ℝ) := {p | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (t p.1) d}
  have hl (u v : ℝ) : K.indicator H (u, v) =
      (Icc c d).indicator (fun v => (Icc a (τ v)).indicator (fun u => H (u, v)) u) v := by
    have he : (u, v) ∈ K ↔ v ∈ Icc c d ∧ u ∈ Icc a (τ v) := by
      constructor
      · rintro ⟨hu, hv⟩
        have hv' : v ∈ Icc c d := ⟨(htc u hu).trans hv.1, hv.2⟩
        exact ⟨hv', hu.1, (hexit u hu v hv').2 hv.1⟩
      · rintro ⟨hv, hu⟩
        have hu' : u ∈ Icc a b := ⟨hu.1, hu.2.trans (hτb v hv)⟩
        exact ⟨hu', (hexit u hu' v hv).1 hu.2, hv.2⟩
    simp only [indicator_apply, he]
    split_ifs <;> first | rfl | tauto
  have hr (u v : ℝ) : K.indicator H (u, v) =
      (Icc a b).indicator (fun u => (Icc (t u) d).indicator (fun v => H (u, v)) v) u := by
    simp only [K, indicator_apply, mem_ofPred_eq]
    split_ifs <;> first | rfl | tauto
  have hf := (integral_prod_symm _ (hH.integrable_indicator hK)).symm.trans
    (integral_prod _ (hH.integrable_indicator hK))
  have hleft : (∫ v, ∫ u, K.indicator H (u, v)) =
      ∫ v in Icc c d, ∫ u in Icc a (τ v), H (u, v) := by
    simp_rw [hl, integral_indicator₂, integral_indicator measurableSet_Icc]
  have hright : (∫ u, ∫ v, K.indicator H (u, v)) =
      ∫ u in Icc a b, ∫ v in Icc (t u) d, H (u, v) := by
    simp_rw [hr, integral_indicator₂, integral_indicator measurableSet_Icc]
  rw [hleft, hright] at hf
  exact hf

/-- [internal] Integrability of the labelwise history integral follows
from L¹ control on the actual swept region. No estimate for the integral
is assumed. The endpoint map may include both exited and surviving labels. -/
theorem integrable_stopped_histories
    {H : ℝ × ℝ → ℝ} {τ t : ℝ → ℝ} {a b c d : ℝ}
    (hK : MeasurableSet {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (t p.1) d})
    (hτb : ∀ v ∈ Icc c d, τ v ≤ b)
    (_htc : ∀ u ∈ Icc a b, c ≤ t u)
    (hexit : ∀ u ∈ Icc a b, ∀ v ∈ Icc c d, u ≤ τ v ↔ t u ≤ v)
    (hH : IntegrableOn H {p | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (t p.1) d}
      (volume.prod volume)) :
    IntegrableOn (fun v => ∫ u in Icc a (τ v), H (u, v)) (Icc c d) := by
  classical
  let K : Set (ℝ × ℝ) := {p | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (t p.1) d}
  apply ((hH.integrable_indicator hK).integral_prod_right.integrableOn).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hsection : {u : ℝ | (u, v) ∈ K} = Icc a (τ v) := by
    ext u
    constructor
    · rintro ⟨hu, hv'⟩
      exact ⟨hu.1, (hexit u hu v hv).2 hv'.1⟩
    · intro hu
      have hu' : u ∈ Icc a b := ⟨hu.1, hu.2.trans (hτb v hv)⟩
      exact ⟨hu', (hexit u hu' v hv).1 hu.2, hv.2⟩
  have hfun : (fun u => K.indicator H (u, v)) =
      (Icc a (τ v)).indicator (fun u => H (u, v)) := by
    funext u
    have hu : (u, v) ∈ K ↔ u ∈ Icc a (τ v) :=
      Set.ext_iff.mp hsection u
    simp only [indicator_apply, hu]
  rw [hfun, integral_indicator measurableSet_Icc]

end EmcsfAcExtension.Global.Exterior
