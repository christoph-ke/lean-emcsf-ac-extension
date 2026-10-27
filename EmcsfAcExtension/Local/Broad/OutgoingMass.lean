module

public import EmcsfAcExtension.Local.Broad.SectionMass

/-! # The outgoing weighted mass comparison in the broad class -/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- [node restart-stab-broad-uniqueness#outgoing-mass-difference]
Outgoing weighted mass comparison, charged_SF_new_version.tex:L5777–5779 and internal project record
(MO). For a fixed geometric box `c,C`, the positive constant is uniform in
`s,t,e,M,ε,L`, both frozen solutions and the outgoing section. No smallness
of `L` or derivative envelope is used. The uniform outgoing comparison is
`Local.stab_broad_mu_sup`, whose proof uses the outgoing constraint. -/
theorem outgoing_mass_difference (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε L : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 → ε ^ 2 ≤ 1 / 2 → 0 ≤ L →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
        ‖S.phi p.1 p.2‖ ≤ M ∧ ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u ∈ Icc s t,
        eVariationOn (S.a u) (Icc u t) ≤ ENNReal.ofReal L) →
      e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1 →
      ∀ u ∈ Icc s t,
      let E := (normalized_field_distance s t S₁ S₂).toReal +
        ε * (geometry_distance s t S₁ S₂).toReal
      IntervalIntegrable (fun v => S₁.lam u v / S₁.r u v * |S₁.mu u v - S₂.mu u v|)
        volume u t ∧
      (∫ v in u..t, S₁.lam u v / S₁.r u v * |S₁.mu u v - S₂.mu u v|) ≤
        K * L * (normalized_field_distance s t S₁ S₂).toReal +
        K * ε * L * (geometry_distance s t S₁ S₂).toReal +
        K * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε * E := by
  obtain ⟨K, hK, hsection⟩ := section_mass_flux_of_bounds c C 1 hc hC zero_le_one
  refine ⟨K, hK, ?_⟩
  intro s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hL hbox hosc hvar hσ u hu E
  have hm₁ : S₁ ∈ ({S₁, S₂} : Set Fields) := by simp
  have hm₂ : S₂ ∈ ({S₁, S₂} : Set Fields) := by simp
  have hs : outSeg u u t ⊆ triangle s t := by
    rintro p ⟨rfl, hx⟩
    exact ⟨hu.1, hx.1, hx.2⟩
  have hsx x (hx : x ∈ Icc u t) : outSeg u u x ⊆ triangle s t := by
    rintro p ⟨rfl, hy⟩
    exact ⟨hu.1, hy.1, hy.2.trans hx.2⟩
  have hfin := geometry_distance_ne_top hS₁ hS₂ hc
    (fun p hp => (hbox S₁ hm₁ p hp).1)
  have hHardy {S : Fields} (hS : IsSolution e S (triangle s t))
      (hm : S ∈ ({S₁, S₂} : Set Fields)) :
      IntervalIntegrable (fun x => S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖) volume u t ∧
      (∫ x in u..t, S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖) ≤ 1 * L := by
    obtain ⟨ii, hi⟩ := outgoing_bv_hardy_solution hS hu.2 hs
    have hv := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvar S hm u hu)
    rw [ENNReal.toReal_ofReal hL] at hv
    exact ⟨ii, hi.trans (by simpa only [one_mul] using hv)⟩
  have hR : S₁.r u t ≤ C * (t - s) :=
    (outgoing_radius_upper hS₁ hu.2 hs
      (fun x hx => (hbox S₁ hm₁ (u, x) (hs ⟨rfl, hx⟩)).2.1)).trans
        (mul_le_mul_of_nonneg_left (show t - u ≤ t - s by linarith [hu.1]) hC)
  apply hsection s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hL hbox hosc hσ
    u t (fun x => (u, x)) (S₁.lam u) (S₂.lam u)
    (fun x => S₁.theta u x / S₁.lam u x) (fun x => S₂.theta u x / S₂.lam u x)
    hu.2 (fun x hx => hs ⟨rfl, hx⟩)
    (continuousOn_out_section hS₁.cont_lam hs) (continuousOn_out_section hS₂.cont_lam hs)
    (continuousOn_out_section (f := fun u v => S₁.theta u v / (S₁.lam u v : ℂ))
      (IsSolution.cont_outgoing_ratio hS₁) hs)
    (continuousOn_out_section (f := fun u v => S₂.theta u v / (S₂.lam u v : ℂ))
      (IsSolution.cont_outgoing_ratio hS₂) hs)
    (fun x hx => ⟨(hbox S₁ hm₁ (u, x) (hs ⟨rfl, hx⟩)).1,
      (hbox S₁ hm₁ (u, x) (hs ⟨rfl, hx⟩)).2.1,
      (hbox S₂ hm₂ (u, x) (hs ⟨rfl, hx⟩)).1,
      (hbox S₂ hm₂ (u, x) (hs ⟨rfl, hx⟩)).2.1⟩)
    (fun x hx => abs_lam_sub_le_geometry_distance hS₁ hfin (hs ⟨rfl, hx⟩))
    (fun x hx => ⟨(hbox S₁ hm₁ (u, x) (hs ⟨rfl, hx⟩)).2.2.2,
      (hbox S₂ hm₂ (u, x) (hs ⟨rfl, hx⟩)).2.2.2,
      (norm_ratio_sub_le_distance_add_scalar hS₁ hS₂ (hs ⟨rfl, hx⟩)).1⟩)
    (fun x hx => (outgoing_radius_reconstruction hS₁ hx.1 (hsx x hx)).symm)
    (fun x hx => (outgoing_radius_reconstruction hS₂ hx.1 (hsx x hx)).symm)
    (fun x hx => ⟨hS₁.r_pos (u, x) (hs ⟨rfl, hx.1.le, hx.2⟩) hx.1,
      hS₂.r_pos (u, x) (hs ⟨rfl, hx.1.le, hx.2⟩) hx.1⟩)
    (outgoing_mass_density_integrable hS₁ hu.2 hs)
    (outgoing_mass_density_integrable hS₂ hu.2 hs)
    (fun x hx => outgoing_mass_ratio_reconstruction hS₁ hx.1 (hsx x hx))
    (fun x hx => outgoing_mass_ratio_reconstruction hS₂ hx.1 (hsx x hx))
    (hHardy hS₁ hm₁).1 (hHardy hS₂ hm₂).1 (hHardy hS₁ hm₁).2 (hHardy hS₂ hm₂).2
    (by simpa only [pow_one, Nat.reduceAdd, Nat.cast_one, one_add_one_eq_two] using
      outgoing_radius_moment hS₁ hu.2 hs 1)
    (fun x hx => by
      have hm := outgoing_radius_moment hS₁ hx.1 (hsx x hx) 2
      norm_num at hm
      exact hm) hR

end EmcsfAcExtension.Local.Broad
