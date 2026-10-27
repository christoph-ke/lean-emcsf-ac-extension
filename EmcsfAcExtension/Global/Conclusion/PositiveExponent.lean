module

public import EmcsfAcExtension.Global.Conclusion.CompactAxis
public import EmcsfAcExtension.Frozen.Fields.EqOn
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Local.Api.EqOn

/-! # Local, earlier, and uniform incoming positive exponents

internal project record applies the same compact-axis estimate to the restarted triangle and
to the proper earlier trapezoid together with its outgoing hull. Splitting
the late rays and transporting through equality on the original domain
gives exactly the extended-real supremum in `charged_SF_new_version.tex:L4205`–L4215.
Continuation is supplied as its full existential conclusion, so these helpers
do not hide the complete-cone input of the continuation producer. This
two-application variant (internal project record) is the exponent step of the
production assembly; the single application on `triangle ui 0` of the internal project record
blueprint is `uniform_positive_exponents` and proves the same clause.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

/-- Every closed solution triangle has a uniform positive-exponent bound
on complete incoming rays. The constant may depend on `e,S,a,b`, uniformly
in the incoming label `v`. In particular this applies to the `IsSolution`
conclusion of the restarted local theorem, with no additional local export. -/
theorem local_positive_incoming_exponent_of_solution {e a b : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle a b)) :
    ∃ C > 0, ∀ v ∈ Icc a b,
      (∫⁻ u in Ico a v, ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
        ENNReal.ofReal C := by
  obtain ⟨C, hC, hbound⟩ := compact_axis_positive_exponent_bound hS
    (isCompact_triangle a b) Subset.rfl (by
      rintro ⟨u, v⟩ ⟨hu, huv, hv⟩ ⟨x, y⟩ ⟨rfl, hy, hyv⟩
      exact ⟨hu, hy, hyv.trans hv⟩)
  refine ⟨C, hC, fun v hv => hbound a v v hv.1 le_rfl ?_⟩
  exact (inSeg_subset_triangle_iff hv.1).mpr ⟨le_rfl, le_rfl, hv.2⟩

/-- The proper earlier trapezoid `triangle ui 0 ∩ {u ≤ a}` is compact,
lies in the original development, and contains its full outgoing hull.
The bound may depend on `ui,a,e,S`, uniformly over all incoming rays and
their earlier portions. No lower bound on radius at the axis is assumed. -/
theorem earlier_positive_exponent_of_solution {ui a e : ℝ} {S : Fields}
    (hS : IsSolution e S (origDomain ui)) (ha : a ∈ Ioo ui 0) :
    ∃ C > 0, ∀ v ∈ Ioo ui 0,
      (∫⁻ u in Ico ui (min a v), ENNReal.ofReal (positiveExpIntegrand S u v)) ≤
        ENNReal.ofReal C := by
  let K := triangle ui 0 ∩ {p : ℝ × ℝ | p.1 ≤ a}
  have hK : IsCompact K :=
    (isCompact_triangle ui 0).inter_right (isClosed_le continuous_fst continuous_const)
  have hKD : K ⊆ origDomain ui := by
    rintro ⟨u, v⟩ ⟨⟨hu, huv, hv⟩, hua⟩
    exact ⟨hu, hua.trans_lt ha.2, huv, hv⟩
  obtain ⟨C, hC, hbound⟩ := compact_axis_positive_exponent_bound hS hK hKD (by
    rintro ⟨u, v⟩ ⟨⟨hu, huv, hv⟩, hua⟩ ⟨x, y⟩ ⟨rfl, hy, hyv⟩
    exact ⟨⟨hu, hy, hyv.trans hv⟩, hua⟩)
  refine ⟨C, hC, fun v hv => hbound ui (min a v) v
    (le_min ha.1.le hv.1.le) (min_le_right _ _) ?_⟩
  rintro ⟨u, w⟩ ⟨hu, humin, rfl⟩
  exact ⟨⟨hu, humin.trans (min_le_right _ _), hv.2.le⟩,
    humin.trans (min_le_left _ _)⟩

/-- The exact frozen uniform-positive-exponent clause follows from the
existential continuation conclusion. The two compact-axis constants are
chosen before the varying ray: one on the proper earlier trapezoid, one
on the local triangle. This is the exponent step of the production
assembly (`Global/Assembly/Main.lean`). It carries no node tag: the graph
node is carried by the single-triangle export `uniform_positive_exponents`,
which proves the same clause. -/
theorem uniform_positive_exponents_of_continuation (ui e : ℝ) (S : Fields)
    (hcont : ∃ us vp : ℝ, ∃ S' : Fields, ui < us ∧ us < 0 ∧ 0 < vp ∧
      IsSolution e S' (origDomain ui ∪ triangle us vp) ∧
      (∀ t ∈ Icc us vp, S'.A t t = 0) ∧ S'.EqOn S (origDomain ui)) :
    (⨆ v ∈ Ioo ui 0,
      ∫⁻ u in Ico ui v, ENNReal.ofReal (positiveExpIntegrand S u v)) < ⊤ := by
  obtain ⟨us, vp, S', hi, hus, hvp, hS', _, heq⟩ := hcont
  have ho : IsSolution e S' (origDomain ui) := Local.isSolution_mono hS' subset_union_left
  have hl : IsSolution e S' (triangle us 0) := Local.isSolution_mono hS' (by
    rintro ⟨u, v⟩ ⟨hu, huv, hv⟩
    exact Or.inr ⟨hu, huv, hv.trans hvp.le⟩)
  obtain ⟨CE, _hCE, hE⟩ := earlier_positive_exponent_of_solution ho ⟨hi, hus⟩
  obtain ⟨CL, _hCL, hL⟩ := local_positive_incoming_exponent_of_solution hl
  apply lt_of_le_of_lt (b := ENNReal.ofReal CE + ENNReal.ofReal CL)
  · refine iSup_le fun v => iSup_le fun hv => ?_
    have he : (∫⁻ u in Ico ui v, ENNReal.ofReal (positiveExpIntegrand S u v)) =
        ∫⁻ u in Ico ui v, ENNReal.ofReal (positiveExpIntegrand S' u v) := by
      apply setLIntegral_congr_fun measurableSet_Ico
      intro u hu
      have hp : (u, v) ∈ origDomain ui :=
        ⟨hu.1, hu.2.trans hv.2, hu.2.le, hv.2.le⟩
      dsimp [positiveExpIntegrand]
      rw [heq.nu hp, heq.mu hp, heq.r hp]
    rw [he]
    by_cases hvus : v ≤ us
    · have h := hE v hv
      rw [min_eq_right hvus] at h
      exact h.trans (le_add_of_nonneg_right bot_le)
    · have husv : us < v := lt_of_not_ge hvus
      rw [← Ico_union_Ico_eq_Ico hi.le husv.le]
      apply (lintegral_union_le _ _ _).trans
      have h := hE v hv
      rw [min_eq_left husv.le] at h
      exact add_le_add h (hL v ⟨husv.le, hv.2.le⟩)
  · exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

end EmcsfAcExtension.Global.Closure
