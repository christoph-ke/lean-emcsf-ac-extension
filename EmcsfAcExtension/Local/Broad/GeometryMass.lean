module

public import EmcsfAcExtension.Local.Broad.MassComparison

/-! # The variation-refined mass bound for the geometric comparison

internal project record (internal project record) keeps the factor `L` in the scalar term even when
the
chosen ratio upper bound is larger than the actual variation. Applying
the uniform comparison with `min ε L` proves that refinement directly.
-/

public section

open Set
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- The refined mass-supremum comparison (internal project record (internal project record)). The
constant
depends only on the fixed outgoing geometric box `c,C`, before all other
parameters and both solutions. No relation between `ε` and the finite
variation budget `L` is assumed. -/
theorem mass_sup_le_variation_error (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε L : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 → ε ^ 2 ≤ 1 / 2 → 0 ≤ L →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
        ‖S.phi p.1 p.2‖ ≤ M ∧ ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u v, (u, v) ∈ triangle s t →
        eVariationOn (S.a u) (Icc u v) ≤ ENNReal.ofReal L) →
      let E := (normalized_field_distance s t S₁ S₂).toReal +
        ε * (geometry_distance s t S₁ S₂).toReal
      (mass_ratio_distance s t S₁ S₂).toReal ≤
        K * L * E + K * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε * E := by
  obtain ⟨K, hK, hmass⟩ := Local.stab_broad_mu_sup c C hc hC
  refine ⟨K, hK, ?_⟩
  intro s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hL hbox hosc hvar E
  let α := min ε L
  have hα : 0 ≤ α := le_min hε hL
  have hαε : α ≤ ε := min_le_left _ _
  have hαL : α ≤ L := min_le_right _ _
  have hαsmall : α ^ 2 ≤ 1 / 2 :=
    ((sq_le_sq₀ hα hε).mpr hαε).trans hsmall
  have hαbox : ∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
      ‖S.phi p.1 p.2‖ ≤ M ∧ ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ α := by
    intro S hS p hp
    have hSol : IsSolution e S (triangle s t) := by
      rcases Set.mem_insert_iff.mp hS with rfl | hS
      · exact hS₁
      · have heq : S = S₂ := Set.mem_singleton_iff.mp hS
        simpa only [heq] using hS₂
    have hs : outSeg p.1 p.1 p.2 ⊆ triangle s t := by
      rintro q ⟨hqu, hx⟩
      exact ⟨by simpa only [hqu] using hp.1, by simpa only [hqu] using hx.1, hx.2.trans hp.2.2⟩
    have hz := norm_outgoing_ratio_le_variation hSol hp.2.1 hs
    have hV := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvar S hS p.1 p.2 hp)
    rw [ENNReal.toReal_ofReal hL] at hV
    exact ⟨(hbox S hS p hp).1, (hbox S hS p hp).2.1, (hbox S hS p hp).2.2.1,
      le_min (hbox S hS p hp).2.2.2 (hz.trans hV)⟩
  have hαosc : ∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
      ‖S₂.a u x - S₂.a u y‖ ≤ α := by
    intro u v hp x hx y hy
    refine le_min (hosc u v hp x hx y hy) ?_
    have he := (eVariationOn.edist_le (S₂.a u) hx hy).trans (hvar S₂ (by simp) u v hp)
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
    simp only [edist_dist, dist_eq_norm] at hh
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_ofReal hL] using hh
  have hb := hmass s t e M α S₁ S₂ hS₁ hS₂ hM hα (hαε.trans hε1) hαsmall hαbox hαosc
  let d := (normalized_field_distance s t S₁ S₂).toReal
  let g := (geometry_distance s t S₁ S₂).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hg : 0 ≤ g := ENNReal.toReal_nonneg
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hEα : d + α * g ≤ E := add_le_add le_rfl (mul_le_mul_of_nonneg_right hαε hg)
  calc
    _ ≤ K * α * d + K * α ^ 2 * g +
        K * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * α * (d + α * g) := hb
    _ = K * α * (d + α * g) +
        K * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * α * (d + α * g) := by ring
    _ ≤ K * L * E + K * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε * E := by
      gcongr

end EmcsfAcExtension.Local.Broad
