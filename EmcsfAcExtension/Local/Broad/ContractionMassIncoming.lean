module

public import EmcsfAcExtension.Local.Broad.ContractionMassOutgoing
import EmcsfAcExtension.Local.Broad.ChargeAlgebra

/-! # Incoming undifferenced mass budget in the ordinary BV gauge

internal project record (BM-) uses the incoming mass reconstruction with the matching
incoming Hardy bound. The parallel-frame bridge is supplied by internal project record;
there is no incoming differentiability assumption on the normalized field.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- [node restart-stab-broad-uniqueness#incoming-undifferenced-mass-budget]
The incoming weighted integral of the undifferenced mass ratio is finite
and bounded by `K * ε * L + K * σ * ε²`. For fixed `c,C`, the positive
constant precedes all triangle, coupling, scalar, variation and solution
parameters. Ordinary characteristic BV and the zero-axis gauge suffice;
the finite budget `L` need not be small. -/
theorem incoming_undifferenced_mass_budget (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε L : ℝ) (S : Fields),
      IsSolution e S (triangle s t) → 1 ≤ M → 0 ≤ ε → ε ≤ 1 → 0 ≤ L →
      (∀ p ∈ triangle s t, c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C ∧
        -S.nu p.1 p.2 ≤ C ∧ c ≤ 1 - S.mu p.1 p.2 ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
        ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε ∧
        ‖S.xi p.1 p.2 / S.nu p.1 p.2‖ ≤ ε) →
      (∀ u v, (u, v) ∈ triangle s t →
        eVariationOn (S.a u) (Icc u v) ≤ ENNReal.ofReal L) →
      (∀ v ∈ Icc s t, eVariationOn (fun u => S.b u v) (Icc s v) ≤ ENNReal.ofReal L) →
      (∀ u ∈ Icc s t, S.A u u = 0) → e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2 ≤ 1 →
      ∀ v ∈ Icc s t,
      IntervalIntegrable (fun u => (-S.nu u v) / S.r u v * S.mu u v) volume s v ∧
      0 ≤ (∫ u in s..v, (-S.nu u v) / S.r u v * S.mu u v) ∧
      (∫ u in s..v, (-S.nu u v) / S.r u v * S.mu u v) ≤
        K * ε * L + K * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε ^ 2 := by
  obtain ⟨KH, hKH, hHardy⟩ := incoming_bv_hardy_of_ordinary_variation c C hc hC
  let K := KH + 2 * C ^ 2 + 1
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro s t e M ε L S hS hM hε hε1 hL hbox hvo hvi haxis hσ v hv
  have hs : inSeg s v v ⊆ triangle s t := by
    rintro p ⟨hx, hy, rfl⟩
    exact ⟨hx, hy, hv.2⟩
  have href : MapsTo (fun x : ℝ => -x) (Icc (-v) (-s)) (Icc s v) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hp x (hx : x ∈ Icc (-v) (-s)) : (-x, v) ∈ triangle s t :=
    hs ⟨(href hx).1, (href hx).2, rfl⟩
  have hsx x (hx : x ∈ Icc (-v) (-s)) : inSeg (-x) v v ⊆ triangle s t := by
    rintro ⟨a, b⟩ ⟨ha, hb, rfl⟩
    exact ⟨(href hx).1.trans ha, hb, hv.2⟩
  have hH := hHardy s t e M L S hS hM hL
    (fun p hp => ⟨(hbox p hp).1, (hbox p hp).2.1, (hbox p hp).2.2.1,
      (hbox p hp).2.2.2.1, (hbox p hp).2.2.2.2.1,
      ((hbox p hp).2.2.2.2.2.2).trans hε1⟩) hvo hvi haxis hσ v hv
  have iH : IntervalIntegrable (fun x => (-S.nu (-x) v) / S.r (-x) v *
      ‖S.xi (-x) v / S.nu (-x) v‖) volume (-v) (-s) :=
    ((IntervalIntegrable.iff_comp_neg).mp hH.1).symm
  have hHr : (∫ x in (-v)..(-s), (-S.nu (-x) v) / S.r (-x) v *
      ‖S.xi (-x) v / S.nu (-x) v‖) ≤ KH * L := by
    rw [intervalIntegral.integral_comp_neg (f := fun x => (-S.nu x v) / S.r x v *
      ‖S.xi x v / S.nu x v‖)]
    simpa only [neg_neg] using hH.2
  have cr : ContinuousOn (fun x => S.r (-x) v) (Icc (-v) (-s)) :=
    (continuousOn_in_section hS.cont_r hs).comp continuous_neg.continuousOn href
  have cm : ContinuousOn (fun x => S.m (-x) v) (Icc (-v) (-s)) :=
    (continuousOn_in_section hS.cont_m hs).comp continuous_neg.continuousOn href
  have cw : ContinuousOn (fun x => -S.nu (-x) v) (Icc (-v) (-s)) :=
    (continuousOn_in_section hS.cont_nu hs).neg.comp continuous_neg.continuousOn href
  have cf : ContinuousOn (fun x => ‖S.xi (-x) v / S.nu (-x) v‖) (Icc (-v) (-s)) :=
    ((continuousOn_in_section (f := fun u v => S.xi u v / S.nu u v)
    (IsSolution.cont_incoming_ratio hS) hs).comp continuous_neg.continuousOn href).norm
  have hμmeas : AEStronglyMeasurable (fun x => S.mu (-x) v)
      (volume.restrict (Icc (-v) (-s))) :=
    ((continuousOn_const.mul cm).aestronglyMeasurable measurableSet_Icc).div₀
      (cr.aestronglyMeasurable measurableSet_Icc)
  let B := e ^ 2 * M ^ 2 * ε ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hq x (hx : x ∈ Icc (-v) (-s)) :
      0 ≤ S.Q (-x) v ^ 2 / S.r (-x) v ^ 2 ∧
      S.Q (-x) v ^ 2 / S.r (-x) v ^ 2 ≤ B * S.r (-x) v ^ 2 := by
    refine ⟨div_nonneg (sq_nonneg _) (sq_nonneg _), ?_⟩
    have hso : outSeg (-x) (-x) v ⊆ triangle s t := by
      rintro ⟨a, b⟩ ⟨rfl, hy⟩
      exact ⟨(href hx).1, hy.1, hy.2.trans hv.2⟩
    have hQ := charge_bound hS (href hx).2 hso
      (fun y hy => (hbox (-x, y) (hso ⟨rfl, hy⟩)).2.2.2.2.1)
      (fun y hy => (hbox (-x, y) (hso ⟨rfl, hy⟩)).2.2.2.2.2.1)
    have hA : 0 ≤ |e| * M * ε := by have := zero_le_one.trans hM; positivity
    have hQ' : |S.Q (-x) v| ≤ (|e| * M * ε) * S.r (-x) v ^ 2 :=
      hQ.trans (by nlinarith only [mul_nonneg hA (sq_nonneg (S.r (-x) v))])
    have hb := electric_square_le_of_charge_bound hA hQ'
    simpa only [B, mul_pow, sq_abs, mul_assoc] using hb
  have hradius x (hx : x ∈ Icc (-v) (-s)) :
      S.r (-x) v = ∫ y in (-v)..x, -S.nu (-y) v := by
    rw [intervalIntegral.integral_comp_neg (f := fun y => -S.nu y v)]
    simpa only [neg_neg] using (incoming_radius_reconstruction hS (href hx).2 (hsx x hx)).symm
  have hrec x (hx : x ∈ Icc (-v) (-s)) : S.mu (-x) v = (S.r (-x) v)⁻¹ *
      ∫ y in (-v)..x, (-S.nu (-y) v) *
        ((1 - S.mu (-y) v) * ‖S.xi (-y) v / S.nu (-y) v‖ ^ 2 +
          S.Q (-y) v ^ 2 / S.r (-y) v ^ 2) := by
    rw [intervalIntegral.integral_comp_neg (f := fun y => (-S.nu y v) *
      ((1 - S.mu y v) * ‖S.xi y v / S.nu y v‖ ^ 2 + S.Q y v ^ 2 / S.r y v ^ 2))]
    simpa only [neg_neg] using incoming_mass_ratio_reconstruction hS (href hx).2 (hsx x hx)
  have hbudget := undifferenced_mass_budget_of_reconstruction (neg_le_neg hv.1) hε hB
    cw cr cf (fun x hx => (neg_pos.mpr (hS.nu_neg (-x, v) (hp x hx))).le)
    hradius (fun x hx => hS.r_pos (-x, v) (hp x ⟨hx.1.le, hx.2⟩) (by linarith [hx.1]))
    (fun x hx => ⟨norm_nonneg _, (hbox (-x, v) (hp x hx)).2.2.2.2.2.2⟩)
    (fun x hx => ⟨(mu_mem_Ico hS (hp x hx)).1, (mu_mem_Ico hS (hp x hx)).2.le⟩)
    hq hμmeas (((IntervalIntegrable.iff_comp_neg).mp
      (incoming_mass_density_integrable hS hv.1 hs)).symm) hrec iH hHr
    (fun x hx => by
      rw [intervalIntegral.integral_comp_neg (f := fun y => (-S.nu y v) * S.r y v ^ 2)]
      have hm := incoming_radius_moment hS (href hx).2 (hsx x hx) 2
      norm_num at hm
      simpa only [neg_neg, neg_mul, intervalIntegral.integral_neg] using hm)
    (by
      rw [intervalIntegral.integral_comp_neg (f := fun y => (-S.nu y v) * S.r y v)]
      simpa only [pow_one, Nat.reduceAdd, Nat.cast_one, one_add_one_eq_two, neg_neg] using
        incoming_radius_moment hS hv.1 hs 1)
  have ii : IntervalIntegrable (fun x => (-S.nu x v) / S.r x v * S.mu x v) volume s v :=
    (IntervalIntegrable.iff_comp_neg).mpr hbudget.1.symm
  have hb := hbudget.2
  rw [intervalIntegral.integral_comp_neg (f := fun x => (-S.nu x v) / S.r x v * S.mu x v)] at hb
  simp only [neg_neg] at hb
  refine ⟨ii, hb.1, hb.2.trans ?_⟩
  have hso : outSeg s s v ⊆ triangle s t := by
    rintro p ⟨rfl, hx⟩
    exact ⟨le_rfl, hx.1, hx.2.trans hv.2⟩
  have hR := (outgoing_radius_upper hS hv.1 hso
    (fun x hx => (hbox (s, x) (hso ⟨rfl, hx⟩)).2.1)).trans
      (mul_le_mul_of_nonneg_left (show v - s ≤ t - s by linarith [hv.2]) hC)
  have hR0 : 0 ≤ S.r s v := by
    rw [← outgoing_radius_reconstruction hS hv.1 hso]
    exact intervalIntegral.integral_nonneg hv.1
      (fun x hx => (hS.lam_pos (s, x) (hso ⟨rfl, hx⟩)).le)
  have hst : 0 ≤ t - s := by linarith [hv.1, hv.2]
  have hRsq : S.r s v ^ 2 ≤ (C * (t - s)) ^ 2 :=
    (sq_le_sq₀ hR0 (mul_nonneg hC hst)).mpr hR
  calc
    ε * (KH * L) + B * S.r s v ^ 2 / 2 ≤ ε * (KH * L) + B * (C * (t - s)) ^ 2 / 2 := by gcongr
    _ = KH * (ε * L) + (2 * C ^ 2) *
        ((e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε ^ 2) := by dsimp [B]; ring
    _ ≤ K * (ε * L) + K * ((e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε ^ 2) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (mul_nonneg hε hL)
        dsimp [K]
        nlinarith only [sq_nonneg C]
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [K]
        linarith [hKH]
    _ = _ := by ring

end EmcsfAcExtension.Local.Broad
