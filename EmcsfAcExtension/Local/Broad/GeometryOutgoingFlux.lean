module

public import EmcsfAcExtension.Local.Broad.GeometryWeights
public import EmcsfAcExtension.Local.Broad.GeometryFlux
public import EmcsfAcExtension.Local.Broad.BVHardy

/-! # Outgoing quadratic-flux comparison for the optical equations

The scalar average cancellation preserves the small factor on the
geometric distance. The Hardy budgets retain their finite variation size.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- The outgoing quadratic optical flux difference is integrable with
bound `K*L*(D+εG)`. The positive constant depends only on the fixed box
`c,C`, before the triangle, ratio and variation budgets and both solutions.
No initial agreement, axis gauge or envelope hypothesis is needed. -/
theorem outgoing_optical_flux_difference (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e ε L : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) → 0 ≤ ε → 0 ≤ L →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
          ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u v, (u, v) ∈ triangle s t →
        eVariationOn (S.a u) (Icc u v) ≤ ENNReal.ofReal L) →
      ∀ u v, (u, v) ∈ triangle s t →
      let E := (normalized_field_distance s t S₁ S₂).toReal +
        ε * (geometry_distance s t S₁ S₂).toReal
      IntervalIntegrable (fun x => S₁.lam u x / S₁.r u x * ‖S₁.theta u x / S₁.lam u x‖ ^ 2 -
        S₂.lam u x / S₂.r u x * ‖S₂.theta u x / S₂.lam u x‖ ^ 2) volume u v ∧
      |∫ x in u..v, S₁.lam u x / S₁.r u x * ‖S₁.theta u x / S₁.lam u x‖ ^ 2 -
        S₂.lam u x / S₂.r u x * ‖S₂.theta u x / S₂.lam u x‖ ^ 2| ≤ K * L * E := by
  obtain ⟨A, hA, hscalar⟩ := scalar_average_difference_bound c hc
  let W := (C / c) ^ 2
  let KB := (1 + C * (C / c)) / c
  let K := (1 + A) + (1 + A + KB) * W + 1
  have hW : 0 ≤ W := sq_nonneg _
  have hKB : 0 ≤ KB := by dsimp [KB]; positivity
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro s t e ε L S₁ S₂ hS₁ hS₂ hε hL hbox hosc hvar u v hp E
  have hs : outSeg u u v ⊆ triangle s t := by
    rintro p ⟨rfl, hx⟩
    exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
  have hlamBox : ∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C :=
    fun S hS p hp => ⟨(hbox S hS p hp).1, (hbox S hS p hp).2.1⟩
  have hfin := geometry_distance_ne_top hS₁ hS₂ hc (fun p hp => (hbox S₁ (by simp) p hp).1)
  let g := (geometry_distance s t S₁ S₂).toReal
  let H := (1 + A) * E
  have hg : 0 ≤ g := ENNReal.toReal_nonneg
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hεg : ε * g ≤ E := le_add_of_nonneg_left ENNReal.toReal_nonneg
  have hpoint x (hx : x ∈ Icc u v) := radial_weights_of_solution_box hc hC hS₁ hS₂ hlamBox
    (hs ⟨rfl, hx⟩) ⟨(hbox S₁ (by simp) (u, x) (hs ⟨rfl, hx⟩)).1,
      (hbox S₁ (by simp) (u, x) (hs ⟨rfl, hx⟩)).2.1,
      (hbox S₂ (by simp) (u, x) (hs ⟨rfl, hx⟩)).1,
      (hbox S₂ (by simp) (u, x) (hs ⟨rfl, hx⟩)).2.1⟩
    (abs_lam_sub_le_geometry_distance hS₁ hfin (hs ⟨rfl, hx⟩))
  have hr0 {S : Fields} (hS : IsSolution e S (triangle s t)) x (hx : x ∈ Icc u v) :
      0 ≤ S.r u x := by
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst x
      exact le_of_eq (hS.axis u (hs ⟨rfl, le_rfl, hp.2.1⟩)).1.symm
    · exact (hS.r_pos (u, x) (hs ⟨rfl, hx⟩) h).le
  have hHardy {S : Fields} (hS : IsSolution e S (triangle s t))
      (hmem : S ∈ ({S₁, S₂} : Set Fields)) :
      IntervalIntegrable (fun x => S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖) volume u v ∧
        (∫ x in u..v, S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖) ≤ L := by
    obtain ⟨ii, hi⟩ := outgoing_bv_hardy_solution hS hp.2.1 hs
    refine ⟨ii, hi.trans ?_⟩
    have hv := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvar S hmem u v hp)
    simpa only [ENNReal.toReal_ofReal hL] using hv
  have hδf x (hx : x ∈ Icc u v) :
      ‖S₁.theta u x / S₁.lam u x - S₂.theta u x / S₂.lam u x‖ ≤ H := by
    apply (norm_ratio_sub_le_distance_add_scalar hS₁ hS₂ (hs ⟨rfl, hx⟩)).1.trans
    have hφ := hscalar s t e ε S₁ S₂ hS₁ hS₂ hε
      (fun p hp => (hbox S₁ (by simp) p hp).1) hosc u x (hs ⟨rfl, hx⟩)
    have hdE : (normalized_field_distance s t S₁ S₂).toReal ≤ E :=
      le_add_of_nonneg_right (mul_nonneg hε hg)
    dsimp [H]
    nlinarith only [hφ, hdE]
  obtain ⟨ii, hi⟩ := quadratic_flux_difference_of_bounds hp.2.1 hε hH hg hW hKB
    (((continuousOn_out_section hS₁.cont_lam hs).aestronglyMeasurable measurableSet_Icc).div₀
      ((continuousOn_out_section hS₁.cont_r hs).aestronglyMeasurable measurableSet_Icc))
    (((continuousOn_out_section hS₂.cont_lam hs).aestronglyMeasurable measurableSet_Icc).div₀
      ((continuousOn_out_section hS₂.cont_r hs).aestronglyMeasurable measurableSet_Icc))
    (continuousOn_out_section (f := fun u v => S₁.theta u v / S₁.lam u v)
      (IsSolution.cont_outgoing_ratio hS₁) hs)
    (continuousOn_out_section (f := fun u v => S₂.theta u v / S₂.lam u v)
      (IsSolution.cont_outgoing_ratio hS₂) hs)
    (fun x hx => div_nonneg (hS₁.lam_pos (u, x) (hs ⟨rfl, hx⟩)).le (hr0 hS₁ x hx))
    (fun x hx => div_nonneg (hS₂.lam_pos (u, x) (hs ⟨rfl, hx⟩)).le (hr0 hS₂ x hx))
    (fun x hx => (hpoint x hx).1) (fun x hx => (hpoint x hx).2)
    (fun x hx => (hbox S₁ (by simp) (u, x) (hs ⟨rfl, hx⟩)).2.2)
    (fun x hx => (hbox S₂ (by simp) (u, x) (hs ⟨rfl, hx⟩)).2.2) hδf
    (hHardy hS₁ (by simp)).1 (hHardy hS₂ (by simp)).1
    (hHardy hS₁ (by simp)).2 (hHardy hS₂ (by simp)).2
  refine ⟨ii, hi.trans ?_⟩
  have hcoef : H + KB * g * ε ≤ (1 + A + KB) * E := by
    have hm := mul_le_mul_of_nonneg_left hεg hKB
    dsimp [H]
    nlinarith only [hm]
  calc
    H * L + (H + KB * g * ε) * W * L ≤ H * L + ((1 + A + KB) * E) * W * L := by gcongr
    _ = ((1 + A) + (1 + A + KB) * W) * L * E := by dsimp [H]; ring
    _ ≤ K * L * E := by
      gcongr
      dsimp [K]
      linarith

end EmcsfAcExtension.Local.Broad
