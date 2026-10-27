module

public import EmcsfAcExtension.Local.Broad.ContractionMassCore
public import EmcsfAcExtension.Local.Broad.Charge
import EmcsfAcExtension.Local.Broad.ChargeAlgebra

/-! # Outgoing undifferenced mass budget for broad solutions

This is the outgoing instance of internal project record (W), exposed separately by
internal project record (BM+). The finite variation budget is not assumed small.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local.Broad

/-- [node restart-stab-broad-uniqueness#outgoing-undifferenced-mass-budget]
The outgoing weighted integral of the undifferenced mass ratio is finite
and bounded by `K * ε * L + K * σ * ε²`. The positive constant depends
only on the upper expansion bound `C`, uniformly in the triangle,
coupling, scalar size, small ratio bound, variation budget and solution.
No gauge, incoming Hardy estimate or derivative envelope is required. -/
theorem outgoing_undifferenced_mass_budget (C : ℝ) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (s t e M ε L : ℝ) (S : Fields),
      IsSolution e S (triangle s t) → 0 ≤ M → 0 ≤ ε → 0 ≤ L →
      (∀ p ∈ triangle s t, S.lam p.1 p.2 ≤ C ∧ ‖S.phi p.1 p.2‖ ≤ M ∧
        ‖S.theta p.1 p.2 / S.lam p.1 p.2‖ ≤ ε) →
      (∀ u ∈ Icc s t, eVariationOn (S.a u) (Icc u t) ≤ ENNReal.ofReal L) →
      ∀ u ∈ Icc s t,
      IntervalIntegrable (fun v => S.lam u v / S.r u v * S.mu u v) volume u t ∧
      0 ≤ (∫ v in u..t, S.lam u v / S.r u v * S.mu u v) ∧
      (∫ v in u..t, S.lam u v / S.r u v * S.mu u v) ≤
        K * ε * L + K * (e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε ^ 2 := by
  let K := 1 + 2 * C ^ 2
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro s t e M ε L S hS hM hε hL hbox hvar u hu
  rcases eq_or_lt_of_le hu.2 with hut | hut
  · subst t
    refine ⟨by simp, by simp, ?_⟩
    simp only [intervalIntegral.integral_same]
    positivity
  have hs : outSeg u u t ⊆ triangle s t := by
    rintro p ⟨rfl, hx⟩
    exact ⟨hu.1, hx.1, hx.2⟩
  have hsx x (hx : x ∈ Icc u t) : outSeg u u x ⊆ triangle s t :=
    fun p hp => hs ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩
  let B := e ^ 2 * M ^ 2 * ε ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have cl := continuousOn_out_section hS.cont_lam hs
  have cr := continuousOn_out_section hS.cont_r hs
  have cf := continuousOn_out_section (f := fun u v => ‖S.theta u v / S.lam u v‖)
    (IsSolution.cont_outgoing_ratio hS).norm hs
  have hw x (hx : x ∈ Icc u t) := (hS.lam_pos (u, x) (hs ⟨rfl, hx⟩)).le
  have hq x (hx : x ∈ Icc u t) :
      0 ≤ S.Q u x ^ 2 / S.r u x ^ 2 ∧ S.Q u x ^ 2 / S.r u x ^ 2 ≤ B * S.r u x ^ 2 := by
    refine ⟨div_nonneg (sq_nonneg _) (sq_nonneg _), ?_⟩
    have hQ := charge_bound hS hx.1 (hsx x hx)
      (fun y hy => (hbox (u, y) (hsx x hx ⟨rfl, hy⟩)).2.1)
      (fun y hy => (hbox (u, y) (hsx x hx ⟨rfl, hy⟩)).2.2)
    have hA : 0 ≤ |e| * M * ε := by positivity
    have hQ' : |S.Q u x| ≤ (|e| * M * ε) * S.r u x ^ 2 :=
      hQ.trans (by nlinarith only [mul_nonneg hA (sq_nonneg (S.r u x))])
    have hb := electric_square_le_of_charge_bound hA hQ'
    simpa only [B, mul_pow, sq_abs, mul_assoc] using hb
  obtain ⟨iH, hH⟩ := outgoing_bv_hardy_solution hS hu.2 hs
  have hH' : (∫ x in u..t, S.lam u x / S.r u x * ‖S.theta u x / S.lam u x‖) ≤ L := by
    apply hH.trans
    have hv := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hvar u hu)
    simpa only [ENNReal.toReal_ofReal hL] using hv
  have hbudget := undifferenced_mass_budget_of_reconstruction hu.2 hε hB cl cr cf hw
    (fun x hx => (outgoing_radius_reconstruction hS hx.1 (hsx x hx)).symm)
    (fun x hx => hS.r_pos (u, x) (hs ⟨rfl, hx.1.le, hx.2⟩) hx.1)
    (fun x hx => ⟨norm_nonneg _, (hbox (u, x) (hs ⟨rfl, hx⟩)).2.2⟩)
    (fun x hx => ⟨(mu_mem_Ico hS (hs ⟨rfl, hx⟩)).1,
      (mu_mem_Ico hS (hs ⟨rfl, hx⟩)).2.le⟩) hq
    ((continuousOn_mu_out hS hut hs).aestronglyMeasurable measurableSet_Icc)
    (outgoing_mass_density_integrable hS hu.2 hs)
    (fun x hx => outgoing_mass_ratio_reconstruction hS hx.1 (hsx x hx)) iH hH'
    (fun x hx => by
      have hm := outgoing_radius_moment hS hx.1 (hsx x hx) 2
      norm_num at hm
      exact hm)
    (by simpa only [pow_one, Nat.reduceAdd, Nat.cast_one, one_add_one_eq_two] using
      outgoing_radius_moment hS hu.2 hs 1)
  refine ⟨hbudget.1, hbudget.2.1, hbudget.2.2.trans ?_⟩
  have hst : 0 ≤ t - s := by linarith [hu.1, hu.2]
  have hR : S.r u t ≤ C * (t - s) :=
    (outgoing_radius_upper hS hu.2 hs (fun x hx => (hbox (u, x) (hs ⟨rfl, hx⟩)).1)).trans
      (mul_le_mul_of_nonneg_left (by linarith [hu.1]) hC)
  have hR0 := (hS.r_pos (u, t) (hs ⟨rfl, hu.2, le_rfl⟩) hut).le
  have hRsq : S.r u t ^ 2 ≤ (C * (t - s)) ^ 2 :=
    (sq_le_sq₀ hR0 (mul_nonneg hC hst)).mpr hR
  calc
    ε * L + B * S.r u t ^ 2 / 2 ≤ ε * L + B * (C * (t - s)) ^ 2 / 2 := by gcongr
    _ = 1 * (ε * L) + (2 * C ^ 2) *
        ((e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε ^ 2) := by dsimp [B]; ring
    _ ≤ K * (ε * L) + K * ((e ^ 2 * M ^ 2 * ((t - s) / 2) ^ 2) * ε ^ 2) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (mul_nonneg hε hL)
        dsimp [K]
        nlinarith only [sq_nonneg C]
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [K]
        linarith
    _ = _ := by ring

end EmcsfAcExtension.Local.Broad
