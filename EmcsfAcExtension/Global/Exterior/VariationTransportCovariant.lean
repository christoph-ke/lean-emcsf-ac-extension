module

public import EmcsfAcExtension.Global.Defs.Curves
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! # Anchor independence and exhaustion of covariant variation

Changing the base point of parallel transport multiplies the field by a
constant unit phase. Uniform bounds on all proper segments therefore pass
to the half-open terminal interval, without assigning a value at its missing
endpoint. Source: `charged_SF_new_version.tex:L1347–L1355`, L1413–L1416.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal] Constant multiplication by a unit complex phase preserves
extended total variation on every ordered set. No constant occurs. -/
theorem eVariationOn_const_mul_unit {f : ℝ → ℂ} {z : ℂ} (hz : ‖z‖ = 1)
    (s : Set ℝ) : eVariationOn (fun x => z * f x) s = eVariationOn f s := by
  unfold eVariationOn
  apply iSup_congr
  rintro ⟨n, u, hu, hus⟩
  apply Finset.sum_congr rfl
  intro i hi
  rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, hz, one_mul]

/-- [internal] Two parallel representatives differ by one constant phase
on each proper later interval. Only integrability of the actual connection
along the containing segment is needed. -/
theorem curveParallel_change_anchor
    {e c a b : ℝ} {S : Fields} {f : ℝ → ℝ → ℂ} {U V : ℝ → ℝ}
    (hca : c ≤ a) (hab : a ≤ b)
    (hA : IntervalIntegrable (fun y => S.A (U y) (V y) * deriv U y) volume c b) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ x ∈ Icc a b,
      curveParallel e S f U V c x = z * curveParallel e S f U V a x := by
  let g : ℝ → ℝ := fun y => S.A (U y) (V y) * deriv U y
  let z : ℂ := Complex.exp (I * e * ∫ y in c..a, g y)
  have hz : ‖z‖ = 1 := by
    simp [z, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  refine ⟨z, hz, ?_⟩
  intro x hx
  have hca' : uIcc c a ⊆ uIcc c b := by
    rw [uIcc_of_le hca, uIcc_of_le (hca.trans hab)]
    exact Icc_subset_Icc le_rfl hab
  have hax' : uIcc a x ⊆ uIcc c b := by
    rw [uIcc_of_le hx.1, uIcc_of_le (hca.trans hab)]
    exact Icc_subset_Icc hca hx.2
  have hi : (∫ y in c..x, g y) = (∫ y in c..a, g y) + ∫ y in a..x, g y :=
    (intervalIntegral.integral_add_adjacent_intervals (hA.mono_set hca')
      (hA.mono_set hax')).symm
  have hp : Complex.exp (I * e * ∫ y in c..x, g y) =
      z * Complex.exp (I * e * ∫ y in a..x, g y) := by
    dsimp only [z]
    rw [← Complex.exp_add, hi, Complex.ofReal_add]
    congr 1
    ring
  change Complex.exp (I * e * ∫ y in c..x, g y) * f (U x) (V x) =
    z * (Complex.exp (I * e * ∫ y in a..x, g y) * f (U x) (V x))
  rw [hp, mul_assoc]

/-- [internal] Covariant variation on a proper segment is independent of
the earlier anchoring row. The local connection integrability premise is
supplied by continuity along a proper boundary in field-level consumers. -/
theorem eVariationOn_curveParallel_eq_curveCovVar
    {e c a b : ℝ} {S : Fields} {f : ℝ → ℝ → ℂ} {U V : ℝ → ℝ}
    (hca : c ≤ a) (hab : a ≤ b)
    (hA : IntervalIntegrable (fun y => S.A (U y) (V y) * deriv U y) volume c b) :
    eVariationOn (curveParallel e S f U V c) (Icc a b) =
      curveCovVar e S f U V a b := by
  obtain ⟨z, hz, heq⟩ := curveParallel_change_anchor
    (e := e) (S := S) (f := f) (U := U) (V := V) hca hab hA
  have he : EqOn (curveParallel e S f U V c)
      (fun x => z * curveParallel e S f U V a x) (Icc a b) := fun x hx => heq x hx
  change _ = eVariationOn (curveParallel e S f U V a) (Icc a b)
  rw [eVariationOn.congr he, eVariationOn_const_mul_unit hz]

/-- [internal] A uniform bound on all closed initial truncations bounds
variation on the full half-open interval. The bound `K` is fixed before the
truncation endpoint is varied, and may be infinite in this order statement. -/
theorem eVariationOn_Ico_le_of_Icc_bound {f : ℝ → ℂ} {a d : ℝ} {K : ℝ≥0∞}
    (hK : ∀ b ∈ Ico a d, eVariationOn f (Icc a b) ≤ K) :
    eVariationOn f (Ico a d) ≤ K := by
  rw [eVariationOn.eq_biSup_inter_Icc]
  apply iSup_le
  intro p
  apply iSup_le
  intro hp
  have hsub : Ico a d ∩ Icc p.1 p.2 ⊆ Icc a p.2 := by
    intro x hx
    exact ⟨hx.1.1, hx.2.2⟩
  exact (eVariationOn.mono f hsub).trans (hK p.2 hp.2.1)

/-- [internal] Uniform proper covariant variation gives finite variation
of the parallel representative on the existing half-open curve. `K` is
fixed independently of every proper terminal truncation. -/
theorem boundedVariationOn_curveParallel_Ico_of_uniform_bound
    {e c d : ℝ} {S : Fields} {f : ℝ → ℝ → ℂ} {U V : ℝ → ℝ} {K : ℝ≥0∞}
    (hK : K ≠ ∞) (hvar : ∀ b ∈ Ico c d, curveCovVar e S f U V c b ≤ K) :
    BoundedVariationOn (curveParallel e S f U V c) (Ico c d) := by
  exact ne_top_of_le_ne_top hK (eVariationOn_Ico_le_of_Icc_bound hvar)

/-- [internal] Finite covariant variation on the half-open curve makes
its intrinsic terminal variation tail vanish. This follows from finite
variation itself and does not require a terminal field value. -/
theorem tendsto_eVariationOn_curveParallel_Ico_zero
    {e c d : ℝ} {S : Fields} {f : ℝ → ℝ → ℂ} {U V : ℝ → ℝ}
    (hbv : BoundedVariationOn (curveParallel e S f U V c) (Ico c d)) :
    Tendsto (fun a => eVariationOn (curveParallel e S f U V c) (Ico a d))
      (𝓝[Ico c d] d) (𝓝 0) := by
  apply (hbv.tendsto_eVariationOn_Ico_zero d).congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  congr 1
  exact inter_eq_right.mpr (Ico_subset_Ico_left ha.1)

/-- [internal] The intrinsic variation tail vanishes along all existing
parameters approaching the missing terminal endpoint from the left. -/
theorem tendsto_eVariationOn_curveParallel_terminal_tail
    {e c d : ℝ} {S : Fields} {f : ℝ → ℝ → ℂ} {U V : ℝ → ℝ}
    (hcd : c < d)
    (hbv : BoundedVariationOn (curveParallel e S f U V c) (Ico c d)) :
    Tendsto (fun a => eVariationOn (curveParallel e S f U V c) (Ico a d))
      (𝓝[<] d) (𝓝 0) := by
  simpa only [nhdsWithin_Ico_eq_nhdsLT hcd] using
    tendsto_eVariationOn_curveParallel_Ico_zero
      (e := e) (S := S) (f := f) (U := U) (V := V) hbv

end EmcsfAcExtension.Global.Exterior
