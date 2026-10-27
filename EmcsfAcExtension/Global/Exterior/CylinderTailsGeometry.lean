module

public import EmcsfAcExtension.Global.Exterior.CylinderTails

/-! # Proper cylinder label changes are bi-Lipschitz

The constants are obtained from the original continuous positive optical
coefficients on proper compact rows. No terminal lower expansion bound
and no density or tail estimate is used. Source: `charged_SF_new_version.tex:L1393–L1395`,
L1413–L1413; approved internal project record (I1).
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
A continuous proper radius-cylinder graph is differentiable at every
interior parameter. This pointwise statement supplies the mean-value
argument for its label change, without inferring AC from an a.e. derivative.
No constants occur. -/
theorem cylinder_label_hasDerivAt_of_graph
    {ui e a b ρ u : ℝ} {S : Fields} {V : ℝ → ℝ}
    (h : OriginalData ui e S) (hia : ui ≤ a) (hb : b < 0)
    (hV : ContinuousOn V (Icc a b))
    (hroot : ∀ x ∈ Icc a b, x < V x ∧ V x ≤ 0 ∧ S.r x (V x) = ρ)
    (hu : u ∈ Ioo a b) :
    HasDerivAt V (-S.nu u (V u) / S.lam u (V u)) u := by
  have hm := cylinder_label_strictMono_of_graph h hia hb hroot
  have hum : u ∈ Icc a b := Ioo_subset_Icc_self hu
  have hr := hroot u hum
  have hv0 : V u < 0 := (hm hum ⟨hu.1.le.trans hu.2.le, le_rfl⟩ hu.2).trans_le
    (hroot b ⟨hu.1.le.trans hu.2.le, le_rfl⟩).2.1
  have hp : (u, V u) ∈ origDomain ui :=
    ⟨hia.trans hum.1, hum.2.trans_lt hb, hr.1.le, hr.2.1⟩
  have hd := radius_hasFDerivAt_of_interior h (hia.trans_lt hu.1) hr.1 hv0
  have hl := h.solution.lam_pos (u, V u) hp
  have hdV : HasDerivWithinAt V (-S.nu u (V u) / S.lam u (V u)) (Icc a b) u := by
    apply Level.hasDerivWithinAt_levelGraph_of_fderivWithin
      (D := Set.univ) hum (hV u hum) (fun _ _ => Set.mem_univ _)
      (fun x hx => (hroot x hx).2.2.trans hr.2.2.symm) hd.hasFDerivWithinAt hl.ne'
  exact hdV.hasDerivAt (Icc_mem_nhds hu.1 hu.2)

/-- [internal]
Every proper radius-cylinder segment has positive Lipschitz and inverse
distance constants. They depend on the original solution and fixed proper
interval, and are chosen before both labels are quantified. They are used
only locally; terminal tail cutoffs remain independent of these constants.
-/
theorem cylinder_bilipschitz_of_graph
    {ui e a b ρ : ℝ} {S : Fields} {V : ℝ → ℝ}
    (h : OriginalData ui e S) (hia : ui ≤ a) (hab : a ≤ b) (hb : b < 0)
    (hV : ContinuousOn V (Icc a b))
    (hroot : ∀ u ∈ Icc a b, u < V u ∧ V u ≤ 0 ∧ S.r u (V u) = ρ) :
    ∃ K > 0, ∃ m > 0,
      LipschitzOnWith (Real.toNNReal K) V (Icc a b) ∧
      (∀ u ∈ Icc a b, ∀ w ∈ Icc a b, m * dist u w ≤ dist (V u) (V w)) ∧
      (∀ᵐ u ∂volume.restrict (Icc a b), m ≤ deriv V u) := by
  obtain ⟨c, hc, B, hB, hbounds⟩ := proper_row_optical_bounds h hia hab hb
  have hm := (cylinder_label_strictMono_of_graph h hia hb hroot).monotoneOn
  have hd (u : ℝ) (hu : u ∈ interior (Icc a b)) :
      HasDerivAt V (-S.nu u (V u) / S.lam u (V u)) u := by
    rw [interior_Icc] at hu
    exact cylinder_label_hasDerivAt_of_graph h hia hb hV hroot hu
  have hdiff : DifferentiableOn ℝ V (interior (Icc a b)) :=
    fun u hu => (hd u hu).differentiableAt.differentiableWithinAt
  have hder (u : ℝ) (hu : u ∈ interior (Icc a b)) :
      c / B ≤ deriv V u ∧ deriv V u ≤ B / c := by
    have hu' : u ∈ Icc a b := interior_subset hu
    have hr := hroot u hu'
    have hbd := hbounds u hu' (V u) ⟨hr.1.le, hr.2.1⟩
    have hl : 0 < S.lam u (V u) := hc.trans_le hbd.1
    rw [(hd u hu).deriv]
    constructor
    · apply (div_le_div_iff₀ hB hl).2
      exact (mul_le_mul_of_nonneg_left hbd.2.1 hc.le).trans
        (mul_le_mul_of_nonneg_right hbd.2.2.1 hB.le)
    · apply (div_le_div_iff₀ hl hc).2
      exact (mul_le_mul_of_nonneg_right hbd.2.2.2 hc.le).trans
        (mul_le_mul_of_nonneg_left hbd.1 hB.le)
  have hlo := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hV hdiff
    (fun u hu => (hder u hu).1)
  have hhi := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hV hdiff
    (fun u hu => (hder u hu).2)
  refine ⟨B / c, div_pos hB hc, c / B, div_pos hc hB, ?_, ?_, ?_⟩
  · rw [lipschitzOnWith_iff_dist_le_mul]
    intro u hu w hw
    rw [Real.coe_toNNReal _ (div_pos hB hc).le]
    rcases le_total u w with huw | hwu
    · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hm hu hw huw)),
        Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr huw)]
      simpa only [neg_sub] using hhi u hu w hw huw
    · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hm hw hu hwu)),
        Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hwu)]
      exact hhi w hw u hu hwu
  · intro u hu w hw
    rcases le_total u w with huw | hwu
    · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr huw), Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr (hm hu hw huw))]
      simpa only [neg_sub] using hlo u hu w hw huw
    · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hwu), Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr (hm hw hu hwu))]
      exact hlo w hw u hu hwu
  · rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact (hder u (by rwa [interior_Icc])).1

end EmcsfAcExtension.Global.Exterior
