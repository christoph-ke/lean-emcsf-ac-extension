module

public import EmcsfAcExtension.Local.Broad.GeometryOutgoingFlux
public import EmcsfAcExtension.Local.Broad.Charge

/-! # Incoming quadratic optical-flux comparison, including truncated sections

Ordinary BV is transferred to the incoming parallel frame by the landed
Maxwell/potential bridge. Prefix budgets follow from the nonnegative
complete-section Hardy integrals.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- Every incoming prefix optical-flux difference has bound `K*L*(D+εG)`.
For fixed `c,C`, the positive constant precedes the triangle, coupling,
scalar and variation sizes and both solutions. The incoming trace is
only ordinary continuous BV; no incoming AC or envelope is assumed. -/
theorem incoming_optical_flux_difference (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε L : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 → 0 ≤ L →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧ c ≤ -S.nu p.1 p.2 ∧
        -S.nu p.1 p.2 ≤ C ∧ c ≤ 1 - S.mu p.1 p.2 ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
        ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ ε) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u v, (u, v) ∈ triangle s t →
        eVariationOn (S.a u) (Icc u v) ≤ ENNReal.ofReal L) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ v ∈ Icc s t,
        eVariationOn (fun x => S.b x v) (Icc s v) ≤ ENNReal.ofReal L) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u ∈ Icc s t, S.A u u = 0) →
      e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1 →
      ∀ v ∈ Icc s t, ∀ u ∈ Icc s v,
      let E := (normalized_field_distance s t S₁ S₂).toReal +
        ε * (geometry_distance s t S₁ S₂).toReal
      IntervalIntegrable (fun x => (-S₁.nu x v) / S₁.r x v * ‖S₁.xi x v / S₁.nu x v‖ ^ 2 -
        (-S₂.nu x v) / S₂.r x v * ‖S₂.xi x v / S₂.nu x v‖ ^ 2) volume s u ∧
      |∫ x in s..u, (-S₁.nu x v) / S₁.r x v * ‖S₁.xi x v / S₁.nu x v‖ ^ 2 -
        (-S₂.nu x v) / S₂.r x v * ‖S₂.xi x v / S₂.nu x v‖ ^ 2| ≤ K * L * E := by
  obtain ⟨A, hA, hscalar⟩ := scalar_average_difference_bound c hc
  obtain ⟨KH, hKH, hHardy⟩ := incoming_bv_hardy_of_ordinary_variation c C hc hC
  let W := (C / c) ^ 2
  let KB := (1 + C * (C / c)) / c
  let K := KH * ((1 + A) + (1 + A + KB) * W) + 1
  have hW : 0 ≤ W := sq_nonneg _
  have hKB : 0 ≤ KB := by dsimp [KB]; positivity
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hL hbox hosc hvo hvi haxis hσ v hv u hu E
  have hs : inSeg s v v ⊆ triangle s t := by
    rintro ⟨a, b⟩ ⟨ha, hb, rfl⟩
    exact ⟨ha, hb, hv.2⟩
  have hsub : Icc s u ⊆ Icc s v := fun x hx => ⟨hx.1, hx.2.trans hu.2⟩
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
  have hr0 {S : Fields} (hS : IsSolution e S (triangle s t)) x (hx : x ∈ Icc s v) :
      0 ≤ S.r x v := by
    rcases eq_or_lt_of_le hx.2 with h | h
    · subst x
      exact le_of_eq (hS.axis v (hs ⟨hv.1, le_rfl, rfl⟩)).1.symm
    · exact (hS.r_pos (x, v) (hs ⟨hx.1, hx.2, rfl⟩) h).le
  have hHardy' {S : Fields} (hS : IsSolution e S (triangle s t))
      (hm : S ∈ ({S₁, S₂} : Set Fields)) := hHardy s t e M L S hS hM hL
    (fun p hp => ⟨(hbox S hm p hp).1, (hbox S hm p hp).2.1,
      (hbox S hm p hp).2.2.2.1, (hbox S hm p hp).2.2.2.2.1,
      (hbox S hm p hp).2.2.2.2.2.1, ((hbox S hm p hp).2.2.2.2.2.2).trans hε1⟩)
    (hvo S hm) (hvi S hm) (haxis S hm) hσ v hv
  have hPrefix {S : Fields} (hS : IsSolution e S (triangle s t))
      (hm : S ∈ ({S₁, S₂} : Set Fields)) :
      IntervalIntegrable (fun x => (-S.nu x v) / S.r x v * ‖S.xi x v / S.nu x v‖) volume s u ∧
        (∫ x in s..u, (-S.nu x v) / S.r x v * ‖S.xi x v / S.nu x v‖) ≤ KH * L := by
    have hh := hHardy' hS hm
    refine ⟨hh.1.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hu)), ?_⟩
    apply (intervalIntegral.integral_mono_interval le_rfl hu.1 hu.2 ?_ hh.1).trans hh.2
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg (div_nonneg (neg_pos.mpr (hS.nu_neg (x, v) (hs ⟨hx.1.le, hx.2, rfl⟩))).le
      (hr0 hS x ⟨hx.1.le, hx.2⟩)) (norm_nonneg _)
  have hpoint x (hx : x ∈ Icc s u) := radial_weights_of_solution_box hc hC hS₁ hS₂ hlamBox
    (hs ⟨(hsub hx).1, (hsub hx).2, rfl⟩)
    ⟨(hbox S₁ (by simp) (x, v) (hs ⟨(hsub hx).1, (hsub hx).2, rfl⟩)).2.2.1,
      (hbox S₁ (by simp) (x, v) (hs ⟨(hsub hx).1, (hsub hx).2, rfl⟩)).2.2.2.1,
      (hbox S₂ (by simp) (x, v) (hs ⟨(hsub hx).1, (hsub hx).2, rfl⟩)).2.2.1,
      (hbox S₂ (by simp) (x, v) (hs ⟨(hsub hx).1, (hsub hx).2, rfl⟩)).2.2.2.1⟩
    (by simpa only [neg_sub_neg, abs_sub_comm] using
      abs_nu_sub_le_geometry_distance hS₁ hfin (hs ⟨(hsub hx).1, (hsub hx).2, rfl⟩))
  have cν₁ := ((continuousOn_in_section hS₁.cont_nu hs).neg).mono hsub
  have cν₂ := ((continuousOn_in_section hS₂.cont_nu hs).neg).mono hsub
  have cr₁ := (continuousOn_in_section hS₁.cont_r hs).mono hsub
  have cr₂ := (continuousOn_in_section hS₂.cont_r hs).mono hsub
  have hδf x (hx : x ∈ Icc s u) :
      ‖S₁.xi x v / S₁.nu x v - S₂.xi x v / S₂.nu x v‖ ≤ H := by
    have hxp : (x, v) ∈ triangle s t := hs ⟨(hsub hx).1, (hsub hx).2, rfl⟩
    apply (norm_ratio_sub_le_distance_add_scalar hS₁ hS₂ hxp).2.trans
    have hφ := hscalar s t e ε S₁ S₂ hS₁ hS₂ hε
      (fun p hp => (hbox S₁ (by simp) p hp).1) hosc x v hxp
    have hdE : (normalized_field_distance s t S₁ S₂).toReal ≤ E :=
      le_add_of_nonneg_right (mul_nonneg hε hg)
    dsimp [H]
    nlinarith only [hφ, hdE]
  obtain ⟨ii, hi⟩ := quadratic_flux_difference_of_bounds hu.1 hε hH hg hW hKB
    ((cν₁.aestronglyMeasurable measurableSet_Icc).div₀ (cr₁.aestronglyMeasurable measurableSet_Icc))
    ((cν₂.aestronglyMeasurable measurableSet_Icc).div₀ (cr₂.aestronglyMeasurable measurableSet_Icc))
    ((continuousOn_in_section (f := fun u v => S₁.xi u v / S₁.nu u v)
      (IsSolution.cont_incoming_ratio hS₁) hs).mono hsub)
    ((continuousOn_in_section (f := fun u v => S₂.xi u v / S₂.nu u v)
      (IsSolution.cont_incoming_ratio hS₂) hs).mono hsub)
    (fun x hx => div_nonneg (neg_pos.mpr (hS₁.nu_neg (x, v)
      (hs ⟨(hsub hx).1, (hsub hx).2, rfl⟩))).le (hr0 hS₁ x (hsub hx)))
    (fun x hx => div_nonneg (neg_pos.mpr (hS₂.nu_neg (x, v)
      (hs ⟨(hsub hx).1, (hsub hx).2, rfl⟩))).le (hr0 hS₂ x (hsub hx)))
    (fun x hx => (hpoint x hx).1) (fun x hx => (hpoint x hx).2)
    (fun x hx => (hbox S₁ (by simp) (x, v) (hs ⟨(hsub hx).1, (hsub hx).2, rfl⟩)).2.2.2.2.2.2)
    (fun x hx => (hbox S₂ (by simp) (x, v) (hs ⟨(hsub hx).1, (hsub hx).2, rfl⟩)).2.2.2.2.2.2) hδf
    (hPrefix hS₁ (by simp)).1 (hPrefix hS₂ (by simp)).1
    (hPrefix hS₁ (by simp)).2 (hPrefix hS₂ (by simp)).2
  refine ⟨ii, hi.trans ?_⟩
  have hcoef : H + KB * g * ε ≤ (1 + A + KB) * E := by
    have hm := mul_le_mul_of_nonneg_left hεg hKB
    dsimp [H]
    nlinarith only [hm]
  calc
    H * (KH * L) + (H + KB * g * ε) * W * (KH * L) ≤
        H * (KH * L) + ((1 + A + KB) * E) * W * (KH * L) := by gcongr
    _ = (KH * ((1 + A) + (1 + A + KB) * W)) * L * E := by dsimp [H]; ring
    _ ≤ K * L * E := by
      gcongr
      dsimp [K]
      linarith

end EmcsfAcExtension.Local.Broad
