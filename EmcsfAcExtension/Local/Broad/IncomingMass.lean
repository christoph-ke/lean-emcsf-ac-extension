module

public import EmcsfAcExtension.Local.Broad.SectionMass

/-! # The incoming weighted mass comparison in the broad class

Incoming ordinary BV is converted to parallel-frame BV using the Maxwell
and zero-axis potential constraints, as required by internal project record internal project record.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

open Broad

/-- [node restart-stab-broad-mu-flux]
Incoming weighted mass comparison, charged_SF_new_version.tex:L5742–5742 and internal project record
(MF). For a fixed geometric box `c,C`, the positive constant is uniform in
`s,t,e,M,ε,L`, both frozen solutions and the incoming section. Ordinary BV
is sufficient under the stated zero-axis gauges; no incoming AC normalized
trace, derivative envelope, or smallness of `L` is assumed. Integrability
of the weighted mass difference is a conclusion. -/
theorem stab_broad_mu_flux (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε L : ℝ) (S₁ S₂ : Fields),
      IsSolution e S₁ (triangle s t) → IsSolution e S₂ (triangle s t) →
      1 ≤ M → 0 ≤ ε → ε ≤ 1 → ε ^ 2 ≤ 1 / 2 → 0 ≤ L →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
        ‖S.phi p.1 p.2‖ ≤ M ∧ ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
        c ≤ -S.nu p.1 p.2 ∧ -S.nu p.1 p.2 ≤ C ∧
        c ≤ 1 - S.mu p.1 p.2 ∧ ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ ε) →
      (∀ u v, (u, v) ∈ triangle s t → ∀ x ∈ Icc u v, ∀ y ∈ Icc u v,
        ‖S₂.a u x - S₂.a u y‖ ≤ ε) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u v, (u, v) ∈ triangle s t →
        eVariationOn (S.a u) (Icc u v) ≤ ENNReal.ofReal L) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ v ∈ Icc s t,
        eVariationOn (fun x => S.b x v) (Icc s v) ≤ ENNReal.ofReal L) →
      (∀ S ∈ ({S₁, S₂} : Set Fields), ∀ u ∈ Icc s t, S.A u u = 0) →
      e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1 →
      ∀ v ∈ Icc s t,
      let E := (normalized_field_distance s t S₁ S₂).toReal +
        ε * (geometry_distance s t S₁ S₂).toReal
      IntervalIntegrable (fun u => (-S₁.nu u v) / S₁.r u v * |S₁.mu u v - S₂.mu u v|)
        volume s v ∧
      (∫ u in s..v, (-S₁.nu u v) / S₁.r u v * |S₁.mu u v - S₂.mu u v|) ≤
        K * L * (normalized_field_distance s t S₁ S₂).toReal +
        K * ε * L * (geometry_distance s t S₁ S₂).toReal +
        K * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε * E := by
  obtain ⟨KH, hKH, hHardy⟩ := incoming_bv_hardy_of_ordinary_variation c C hc hC
  obtain ⟨K, hK, hsection⟩ := section_mass_flux_of_bounds c C KH hc hC hKH.le
  refine ⟨K, hK, ?_⟩
  intro s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hL hbox hng hosc hvo hvi haxis hσ v hv E
  have hm₁ : S₁ ∈ ({S₁, S₂} : Set Fields) := by simp
  have hm₂ : S₂ ∈ ({S₁, S₂} : Set Fields) := by simp
  have hs : inSeg s v v ⊆ triangle s t := by
    rintro p ⟨hx, hy, rfl⟩
    exact ⟨hx, hy, hv.2⟩
  have hneg : MapsTo (fun x : ℝ => -x) (Icc (-v) (-s)) (Icc s v) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hp x (hx : x ∈ Icc (-v) (-s)) : (-x, v) ∈ triangle s t :=
    hs ⟨(hneg hx).1, (hneg hx).2, rfl⟩
  have hsx x (hx : x ∈ Icc (-v) (-s)) : inSeg (-x) v v ⊆ triangle s t := by
    rintro p ⟨hy, hz, rfl⟩
    exact ⟨(hneg hx).1.trans hy, hz, hv.2⟩
  have hfin := geometry_distance_ne_top hS₁ hS₂ hc
    (fun p hp => (hbox S₁ hm₁ p hp).1)
  have hHardy' {S : Fields} (hS : IsSolution e S (triangle s t))
      (hm : S ∈ ({S₁, S₂} : Set Fields)) :=
    hHardy s t e M L S hS hM hL
      (fun p hp => ⟨(hbox S hm p hp).1, (hbox S hm p hp).2.1,
        (hng S hm p hp).2.1, (hng S hm p hp).2.2.1,
        (hbox S hm p hp).2.2.1, ((hng S hm p hp).2.2.2).trans hε1⟩)
      (hvo S hm) (hvi S hm) (haxis S hm) hσ v hv
  have hHardyRef {S : Fields} (hS : IsSolution e S (triangle s t))
      (hm : S ∈ ({S₁, S₂} : Set Fields)) :
      IntervalIntegrable (fun x => (-S.nu (-x) v) / S.r (-x) v *
        ‖S.xi (-x) v / S.nu (-x) v‖) volume (-v) (-s) ∧
      (∫ x in (-v)..(-s), (-S.nu (-x) v) / S.r (-x) v *
        ‖S.xi (-x) v / S.nu (-x) v‖) ≤ KH * L := by
    refine ⟨((IntervalIntegrable.iff_comp_neg).mp (hHardy' hS hm).1).symm, ?_⟩
    rw [intervalIntegral.integral_comp_neg (f := fun x => (-S.nu x v) / S.r x v *
      ‖S.xi x v / S.nu x v‖)]
    simpa only [neg_neg] using (hHardy' hS hm).2
  have hradius {S : Fields} (hS : IsSolution e S (triangle s t)) x
      (hx : x ∈ Icc (-v) (-s)) :
      S.r (-x) v = ∫ y in (-v)..x, -S.nu (-y) v := by
    rw [intervalIntegral.integral_comp_neg (f := fun y => -S.nu y v)]
    simpa only [neg_neg] using
      (incoming_radius_reconstruction hS (hneg hx).2 (hsx x hx)).symm
  have hmassRef {S : Fields} (hS : IsSolution e S (triangle s t)) x
      (hx : x ∈ Icc (-v) (-s)) :
      S.mu (-x) v = (S.r (-x) v)⁻¹ * ∫ y in (-v)..x, (-S.nu (-y) v) *
        ((1 - S.mu (-y) v) * ‖S.xi (-y) v / S.nu (-y) v‖ ^ 2 +
          S.Q (-y) v ^ 2 / S.r (-y) v ^ 2) := by
    rw [intervalIntegral.integral_comp_neg (f := fun y => (-S.nu y v) *
      ((1 - S.mu y v) * ‖S.xi y v / S.nu y v‖ ^ 2 + S.Q y v ^ 2 / S.r y v ^ 2))]
    simpa only [neg_neg] using incoming_mass_ratio_reconstruction hS (hneg hx).2 (hsx x hx)
  have hso : outSeg s s v ⊆ triangle s t := by
    rintro p ⟨rfl, hx⟩
    exact ⟨le_rfl, hx.1, hx.2.trans hv.2⟩
  have hR : S₁.r s v ≤ C * (t - s) :=
    (outgoing_radius_upper hS₁ hv.1 hso
      (fun x hx => (hbox S₁ hm₁ (s, x) (hso ⟨rfl, hx⟩)).2.1)).trans
        (mul_le_mul_of_nonneg_left (show v - s ≤ t - s by linarith [hv.2]) hC)
  have hresult := hsection s t e M ε L S₁ S₂ hS₁ hS₂ hM hε hε1 hsmall hL hbox hosc hσ
    (-v) (-s) (fun x => (-x, v)) (fun x => -S₁.nu (-x) v) (fun x => -S₂.nu (-x) v)
    (fun x => S₁.xi (-x) v / S₁.nu (-x) v) (fun x => S₂.xi (-x) v / S₂.nu (-x) v)
    (neg_le_neg hv.1) hp
    ((continuousOn_in_section hS₁.cont_nu hs).neg.comp continuous_neg.continuousOn hneg)
    ((continuousOn_in_section hS₂.cont_nu hs).neg.comp continuous_neg.continuousOn hneg)
    ((continuousOn_in_section (f := fun u v => S₁.xi u v / (S₁.nu u v : ℂ))
      (IsSolution.cont_incoming_ratio hS₁) hs).comp
      continuous_neg.continuousOn hneg)
    ((continuousOn_in_section (f := fun u v => S₂.xi u v / (S₂.nu u v : ℂ))
      (IsSolution.cont_incoming_ratio hS₂) hs).comp
      continuous_neg.continuousOn hneg)
    (fun x hx => ⟨(hng S₁ hm₁ (-x, v) (hp x hx)).1,
      (hng S₁ hm₁ (-x, v) (hp x hx)).2.1,
      (hng S₂ hm₂ (-x, v) (hp x hx)).1, (hng S₂ hm₂ (-x, v) (hp x hx)).2.1⟩)
    (fun x hx => by simpa only [neg_sub_neg, abs_sub_comm] using
      abs_nu_sub_le_geometry_distance hS₁ hfin (hp x hx))
    (fun x hx => ⟨(hng S₁ hm₁ (-x, v) (hp x hx)).2.2.2,
      (hng S₂ hm₂ (-x, v) (hp x hx)).2.2.2,
      (norm_ratio_sub_le_distance_add_scalar hS₁ hS₂ (hp x hx)).2⟩)
    (hradius hS₁) (hradius hS₂)
    (fun x hx => ⟨hS₁.r_pos (-x, v) (hp x ⟨hx.1.le, hx.2⟩) (by linarith [hx.1]),
      hS₂.r_pos (-x, v) (hp x ⟨hx.1.le, hx.2⟩) (by linarith [hx.1])⟩)
    (((IntervalIntegrable.iff_comp_neg).mp (incoming_mass_density_integrable hS₁ hv.1 hs)).symm)
    (((IntervalIntegrable.iff_comp_neg).mp (incoming_mass_density_integrable hS₂ hv.1 hs)).symm)
    (hmassRef hS₁) (hmassRef hS₂)
    (hHardyRef hS₁ hm₁).1 (hHardyRef hS₂ hm₂).1
    (hHardyRef hS₁ hm₁).2 (hHardyRef hS₂ hm₂).2
    (by
      rw [intervalIntegral.integral_comp_neg (f := fun y => (-S₁.nu y v) * S₁.r y v)]
      simpa only [pow_one, Nat.reduceAdd, Nat.cast_one, one_add_one_eq_two, neg_neg] using
        incoming_radius_moment hS₁ hv.1 hs 1)
    (fun x hx => by
      rw [intervalIntegral.integral_comp_neg (f := fun y => (-S₁.nu y v) * S₁.r y v ^ 2)]
      have hm := incoming_radius_moment hS₁ (hneg hx).2 (hsx x hx) 2
      norm_num at hm
      simpa only [neg_neg, neg_mul, intervalIntegral.integral_neg] using hm)
    (by simpa only [neg_neg] using hR)
  have iresult : IntervalIntegrable (fun x => (-S₁.nu x v) / S₁.r x v *
      |S₁.mu x v - S₂.mu x v|) volume s v :=
    (IntervalIntegrable.iff_comp_neg).mpr hresult.1.symm
  refine ⟨iresult, ?_⟩
  have hi := hresult.2
  rw [intervalIntegral.integral_comp_neg (f := fun x => (-S₁.nu x v) / S₁.r x v *
    |S₁.mu x v - S₂.mu x v|)] at hi
  simpa only [neg_neg] using hi

end EmcsfAcExtension.Local
