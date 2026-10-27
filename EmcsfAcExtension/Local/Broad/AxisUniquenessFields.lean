module

public import EmcsfAcExtension.Local.Broad.GeometryInitial

/-! # Recovery of every field from vanishing broad comparison distances

The distances control the radius, expansions and normalized scalar data.
The common-cone constraints then determine all remaining primary fields.
No construction provenance or derivative envelope enters this argument.
-/

public section

open Set
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- [node restart-stab-broad-uniqueness#remaining-fields-agree]
Vanishing normalized and geometric distances on a complete comparison
triangle force equality of all nine primary fields. There are no estimate
constants and no further smallness hypotheses. Both zero-axis gauges are
explicit, as in the source class used in the local contraction. -/
theorem remaining_fields_agree {s t e : ℝ} {S₁ S₂ : Fields}
    (hS₁ : IsSolution e S₁ (triangle s t)) (hS₂ : IsSolution e S₂ (triangle s t))
    (hA : ∀ u ∈ Icc s t, S₁.A u u = 0 ∧ S₂.A u u = 0)
    (hD : normalized_field_distance s t S₁ S₂ = 0)
    (hG : geometry_distance s t S₁ S₂ = 0) : S₁.EqOn S₂ (triangle s t) := by
  have hfin : geometry_distance s t S₁ S₂ ≠ ⊤ := by rw [hG]; exact ENNReal.zero_ne_top
  have hr u v (hp : (u, v) ∈ triangle s t) : S₁.r u v = S₂.r u v := by
    have h := abs_radius_sub_le_geometry_distance_mul_radius hS₁ hS₂ hfin hp
    rw [hG, ENNReal.toReal_zero, zero_mul] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  have hl u v (hp : (u, v) ∈ triangle s t) : S₁.lam u v = S₂.lam u v := by
    have h := abs_lam_sub_le_geometry_distance hS₁ hfin hp
    rw [hG, ENNReal.toReal_zero] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  have hn u v (hp : (u, v) ∈ triangle s t) : S₁.nu u v = S₂.nu u v := by
    have h := abs_nu_sub_le_geometry_distance hS₁ hfin hp
    rw [hG, ENNReal.toReal_zero] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  have ha u v (hp : (u, v) ∈ triangle s t) : S₁.a u v = S₂.a u v := by
    have h := norm_a_sub_le_distance hS₁ hS₂ hp
    rw [hD, ENNReal.toReal_zero] at h
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  rintro ⟨u, v⟩ hp
  by_cases hut : u < t
  · have hs : outSeg u u t ⊆ triangle s t := by
      rintro p ⟨rfl, hx⟩
      exact ⟨hp.1, hx.1, hx.2⟩
    have hi := common_data_initial_constraint_agreement hS₁ hS₂ hut hs hs
      (fun x hx => ⟨hr u x (hs ⟨rfl, hx⟩), ha u x (hs ⟨rfl, hx⟩)⟩)
      (hA u ⟨hp.1, hut.le⟩).1 (hA u ⟨hp.1, hut.le⟩).2
    exact hi (u, v) ⟨rfl, hp.2.1, hp.2.2⟩
  · have hut' : u = t := le_antisymm (hp.2.1.trans hp.2.2) (le_of_not_gt hut)
    have huv : u = v := le_antisymm hp.2.1 (hp.2.2.trans hut'.symm.le)
    subst v
    have ax₁ := hS₁.axis u hp
    have ax₂ := hS₂.axis u hp
    have hphi : S₁.phi u u = S₂.phi u u :=
      ax₁.2.2.2.2.1.symm.trans ((ha u u hp).trans ax₂.2.2.2.2.1)
    exact ⟨hr u u hp, hl u u hp, hn u u hp,
      ax₁.2.1.trans ax₂.2.1.symm, ax₁.2.2.1.trans ax₂.2.2.1.symm, hphi,
      (hA u ⟨hp.1, hp.2.2⟩).1.trans (hA u ⟨hp.1, hp.2.2⟩).2.symm,
      theta_eq_of_lam_phi_a_eq (hS₁.lam_pos (u, u) hp).ne'
        (hS₂.lam_pos (u, u) hp).ne' (hl u u hp) hphi (ha u u hp),
      (xi_axis_zero hS₁ hp).trans (xi_axis_zero hS₂ hp).symm⟩

end EmcsfAcExtension.Local.Broad
