module

public import EmcsfAcExtension.Global.Defs.Original
import EmcsfAcExtension.Global.Api.Domains
import EmcsfAcExtension.Global.Calculus.Normalized

/-! # Absolute continuity on the selected closed cone

The approved internal project record route uses the frozen `ac_out`, including the existing
axis endpoint. Variation semicontinuity plays no role in this argument.
Source: charged_SF_new_version.tex:L4132–4133 and approved internal project record.
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Closure

/-- [node sec:charged-closure#ac-route-local-hypothesis]
Every proper closed outgoing cone inherits AC directly from the frozen
solution class (charged_SF_new_version.tex:L4132–4133). No smallness is required. -/
theorem ac_route_local_hypothesis (ui e : ℝ) (S : Fields) (h : OriginalData ui e S)
    {us : ℝ} (hus : us ∈ Ioo ui 0) :
    AbsolutelyContinuousOnInterval (S.a us) us 0 := by
  exact (h.solution.ac_out us us 0 hus.2.le
    ((outSeg_axis_subset_origDomain_iff hus.2.le).2
      ⟨hus.1.le, hus.2, le_rfl⟩)).2.2.2.2

end EmcsfAcExtension.Global.Closure

namespace EmcsfAcExtension.Global.Restart

/-- [internal]
Conditional support for `sec:charged-closure#complete-cone-ac`.
AC on the full selected cone and the vertex modulus bound inherited from
its exterior amplitude. The explicit exterior sequence and amplitude
premises are discharged by the closure construction; no constant is chosen.
Source: charged_SF_new_version.tex:L4132–4133. -/
theorem complete_cone_ac_of_closure (ui e : ℝ) (S : Fields) (h : OriginalData ui e S)
    {us M : ℝ} (hus : us ∈ Ioo ui 0) (U V : ℕ → ℝ)
    (hU : Tendsto U atTop (𝓝 us)) (hV : Tendsto V atTop (𝓝 us))
    (hmem : ∀ n, (U n, V n) ∈ origDomain ui)
    (hamp : ∀ n, ‖S.phi (U n) (V n)‖ ≤ M) :
    AbsolutelyContinuousOnInterval (S.a us) us 0 ∧ ‖S.phi us us‖ ≤ M := by
  refine ⟨Closure.ac_route_local_hypothesis ui e S h hus, ?_⟩
  apply le_of_tendsto
    ((h.solution.cont_phi (us, us) ⟨hus.1.le, hus.2, le_rfl, hus.2.le⟩).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr
        ⟨hU.prodMk_nhds hV, Eventually.of_forall hmem⟩)).norm
    (Eventually.of_forall hamp)

end EmcsfAcExtension.Global.Restart
