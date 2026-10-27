module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.OrigDomain
public import EmcsfAcExtension.Frozen.Fields.EqOn
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Local.Api.EqOn

/-! # Equality at every old point of the last cone

Proper-triangle uniqueness stops before the old last cone. At its old points
`u < 0`, each primary field has a continuous outgoing representative through
`v = 0`. Equality on the half-open section therefore extends to its endpoint.
The absent apex `(0,0)` is never used here.
-/

public section

open Set

namespace EmcsfAcExtension.Global.Restart

private theorem endpoint_eq {E : Type*} [TopologicalSpace E] [T2Space E]
    {f g : ℝ → E} {u : ℝ} (hu : u < 0)
    (hf : ContinuousOn f (Icc u 0)) (hg : ContinuousOn g (Icc u 0))
    (he : Set.EqOn f g (Ico u 0)) : f 0 = g 0 := by
  apply he.of_subset_closure hf hg Ico_subset_Icc_self _ (right_mem_Icc.mpr hu.le)
  rw [closure_Ico hu.ne]

/-- [internal]
Extend proper-overlap equality to the old last cone by continuity of all nine
primary fields. The result includes every old point of the exact overlap;
uniqueness is never applied to the missing point (`charged_SF_new_version.tex:L4186`–L4205). -/
theorem eqOn_last_cone_of_lt {ui e us vp : ℝ} {S N : Fields}
    (hvp : 0 < vp)
    (hold : IsSolution e S (origDomain ui))
    (hnew : IsSolution e N (triangle us vp))
    (he : N.EqOn S ((origDomain ui ∩ triangle us vp) ∩
      {p : ℝ × ℝ | p.2 < 0})) :
    N.EqOn S (origDomain ui ∩ triangle us vp) := by
  rintro ⟨u, v⟩ hp
  by_cases hv : v < 0
  · exact he _ ⟨hp, hv⟩
  have hz : v = 0 := le_antisymm hp.1.2.2.2 (le_of_not_gt hv)
  subst v
  have hu : u < 0 := hp.1.2.1
  have ho : outSeg u u 0 ⊆ origDomain ui := by
    rintro p ⟨rfl, ha, hb⟩
    exact ⟨hp.1.1, hu, ha, hb⟩
  have hn : outSeg u u 0 ⊆ triangle us vp := by
    rintro p ⟨rfl, ha, hb⟩
    exact ⟨hp.2.1, ha, hb.trans hvp.le⟩
  have hs (t : ℝ) (ht : t ∈ Ico u 0) :
      (u, t) ∈ (origDomain ui ∩ triangle us vp) ∩ {p : ℝ × ℝ | p.2 < 0} :=
    ⟨⟨ho ⟨rfl, ht.1, ht.2.le⟩, hn ⟨rfl, ht.1, ht.2.le⟩⟩, ht.2⟩
  exact ⟨endpoint_eq hu (Calculus.continuousOn_out_section hnew.cont_r hn)
      (Calculus.continuousOn_out_section hold.cont_r ho) (fun t ht => he.r (hs t ht)),
    endpoint_eq hu (Calculus.continuousOn_out_section hnew.cont_lam hn)
      (Calculus.continuousOn_out_section hold.cont_lam ho) (fun t ht => he.lam (hs t ht)),
    endpoint_eq hu (Calculus.continuousOn_out_section hnew.cont_nu hn)
      (Calculus.continuousOn_out_section hold.cont_nu ho) (fun t ht => he.nu (hs t ht)),
    endpoint_eq hu (Calculus.continuousOn_out_section hnew.cont_m hn)
      (Calculus.continuousOn_out_section hold.cont_m ho) (fun t ht => he.m (hs t ht)),
    endpoint_eq hu (Calculus.continuousOn_out_section hnew.cont_Q hn)
      (Calculus.continuousOn_out_section hold.cont_Q ho) (fun t ht => he.Q (hs t ht)),
    endpoint_eq hu (Calculus.continuousOn_out_section hnew.cont_phi hn)
      (Calculus.continuousOn_out_section hold.cont_phi ho) (fun t ht => he.phi (hs t ht)),
    endpoint_eq hu (Calculus.continuousOn_out_section hnew.cont_A hn)
      (Calculus.continuousOn_out_section hold.cont_A ho) (fun t ht => he.A (hs t ht)),
    endpoint_eq hu (Calculus.continuousOn_out_section hnew.cont_theta hn)
      (Calculus.continuousOn_out_section hold.cont_theta ho) (fun t ht => he.theta (hs t ht)),
    endpoint_eq hu (Calculus.continuousOn_out_section hnew.cont_xi hn)
      (Calculus.continuousOn_out_section hold.cont_xi ho) (fun t ht => he.xi (hs t ht))⟩

end EmcsfAcExtension.Global.Restart
