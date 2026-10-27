module

public import EmcsfAcExtension.Local.Broad.GeometryODE
public import EmcsfAcExtension.Frozen.Fields.EqOn

/-! # Agreement of the common initial constraints

This is the entering-cone statement of internal project record and amendment
internal project record. Its conclusion includes the initial vertex only; the
geometric comparison must still estimate subsequent axis expansions.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Broad

/-- The incoming scalar transport field vanishes at an existing regular
axis point. This is algebraic and does not fix the axis potential gauge. -/
theorem xi_axis_zero {e u : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) (hu : (u, u) ∈ D) : S.xi u u = 0 := by
  have hn : (S.nu u u : ℂ) ≠ 0 := by exact_mod_cast (hS.nu_neg (u, u) hu).ne
  have h := (hS.axis u hu).2.2.2.2.2
  have hz : S.xi u u / (S.nu u u : ℂ) = 0 := by
    simpa only [Fields.b, add_eq_left] using h
  exact (div_eq_zero_iff.mp hz).resolve_right hn

/-- [node restart-stab-broad-uniqueness#common-data-initial-constraint-agreement]
Equal radius and normalized scalar datum on the entering cone, with the
common zero potential at its vertex, determine all nine primary fields
there. This is amendment internal project record: no later axis value is prescribed.
There are no estimate constants, smallness or envelope assumptions, and
the common radius need not be the normalized linear radius. -/
theorem common_data_initial_constraint_agreement {e u v : ℝ} {S₁ S₂ : Fields}
    {D₁ D₂ : Set (ℝ × ℝ)} (hS₁ : IsSolution e S₁ D₁) (hS₂ : IsSolution e S₂ D₂)
    (huv : u < v) (hs₁ : outSeg u u v ⊆ D₁) (hs₂ : outSeg u u v ⊆ D₂)
    (hdata : ∀ x ∈ Icc u v, S₁.r u x = S₂.r u x ∧ S₁.a u x = S₂.a u x)
    (hA₁ : S₁.A u u = 0) (hA₂ : S₂.A u u = 0) :
    S₁.EqOn S₂ (outSeg u u v) := by
  have hr x hx := (hdata x hx).1
  have ha x hx := (hdata x hx).2
  have hl := cone_lam_eq_of_radius_eq hS₁ hS₂ huv hs₁ hs₂ hr
  have hp := cone_phi_eq_of_data_eq hS₁ hS₂ huv hs₁ hs₂ hr ha
  have ht x (hx : x ∈ Icc u v) := theta_eq_of_lam_phi_a_eq
    (hS₁.lam_pos (u, x) (hs₁ ⟨rfl, hx⟩)).ne'
    (hS₂.lam_pos (u, x) (hs₂ ⟨rfl, hx⟩)).ne'
    (hl x hx) (hp x hx) (ha x hx)
  have hq := cone_charge_eq_of_data_eq hS₁ hS₂ huv hs₁ hs₂ hr ha
  have subseg₁ x (hx : x ∈ Icc u v) : outSeg u u x ⊆ D₁ :=
    fun p h => hs₁ ⟨h.1, h.2.1, h.2.2.trans hx.2⟩
  have subseg₂ x (hx : x ∈ Icc u v) : outSeg u u x ⊆ D₂ :=
    fun p h => hs₂ ⟨h.1, h.2.1, h.2.2.trans hx.2⟩
  have hm x (hx : x ∈ Icc u v) : S₁.m u x = S₂.m u x :=
    cone_mass_eq_of_constraint_fields_eq hS₁ hS₂ hx.1 (subseg₁ x hx) (subseg₂ x hx)
      (fun y hy => hr y ⟨hy.1, hy.2.trans hx.2⟩)
      (fun y hy => hl y ⟨hy.1, hy.2.trans hx.2⟩)
      (fun y hy => ht y ⟨hy.1, hy.2.trans hx.2⟩)
      (fun y hy => hq y ⟨hy.1, hy.2.trans hx.2⟩)
  have hn x (hx : x ∈ Icc u v) : S₁.nu u x = S₂.nu u x :=
    cone_nu_eq_of_constraint_fields_eq hS₁ hS₂ hx.1 (subseg₁ x hx) (subseg₂ x hx)
      (fun y hy => hr y ⟨hy.1, hy.2.trans hx.2⟩)
      (fun y hy => hl y ⟨hy.1, hy.2.trans hx.2⟩)
      (fun y hy => hm y ⟨hy.1, hy.2.trans hx.2⟩)
      (fun y hy => hq y ⟨hy.1, hy.2.trans hx.2⟩)
  have hpot x (hx : x ∈ Icc u v) : S₁.A u x = S₂.A u x := by
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst x
      exact hA₁.trans hA₂.symm
    apply eq_endpoint_of_equal_increments h
      (continuousOn_out_section hS₁.cont_A (subseg₁ x hx))
      (continuousOn_out_section hS₂.cont_A (subseg₂ x hx)) (hA₁.trans hA₂.symm)
    intro c d hc hcd hd
    have hseg₁ : outSeg u c d ⊆ D₁ := fun p hp =>
      hs₁ ⟨hp.1, hc.le.trans hp.2.1, hp.2.2.trans (hd.le.trans hx.2)⟩
    have hseg₂ : outSeg u c d ⊆ D₂ := fun p hp =>
      hs₂ ⟨hp.1, hc.le.trans hp.2.1, hp.2.2.trans (hd.le.trans hx.2)⟩
    rw [(hS₁.eq_out u c d hc hcd hseg₁).2.2.2.2.1.2,
      (hS₂.eq_out u c d hc hcd hseg₂).2.2.2.2.1.2]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hcd] at hy
    have hy' : y ∈ Icc u v := ⟨hc.le.trans hy.1, hy.2.trans (hd.le.trans hx.2)⟩
    simp only [Fields.AV, Fields.mu, hr y hy', hl y hy', hn y hy', hm y hy', hq y hy']
  have hxi x (hx : x ∈ Icc u v) : S₁.xi u x = S₂.xi u x := by
    have hzero := (xi_axis_zero hS₁ (hs₁ ⟨rfl, le_rfl, huv.le⟩)).trans
      (xi_axis_zero hS₂ (hs₂ ⟨rfl, le_rfl, huv.le⟩)).symm
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst x
      exact hzero
    apply eq_endpoint_of_equal_increments h
      (continuousOn_out_section hS₁.cont_xi (subseg₁ x hx))
      (continuousOn_out_section hS₂.cont_xi (subseg₂ x hx)) hzero
    intro c d hc hcd hd
    have hseg₁ : outSeg u c d ⊆ D₁ := fun p hp =>
      hs₁ ⟨hp.1, hc.le.trans hp.2.1, hp.2.2.trans (hd.le.trans hx.2)⟩
    have hseg₂ : outSeg u c d ⊆ D₂ := fun p hp =>
      hs₂ ⟨hp.1, hc.le.trans hp.2.1, hp.2.2.trans (hd.le.trans hx.2)⟩
    rw [(hS₁.eq_out u c d hc hcd hseg₁).2.2.2.2.2.2.2,
      (hS₂.eq_out u c d hc hcd hseg₂).2.2.2.2.2.2.2]
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hcd] at hy
    have hy' : y ∈ Icc u v := ⟨hc.le.trans hy.1, hy.2.trans (hd.le.trans hx.2)⟩
    simp only [Fields.xiV, Fields.waveSource, Fields.mu, hr y hy', hl y hy', hn y hy',
      hm y hy', hq y hy', hp y hy', ht y hy']
  rintro p ⟨rfl, hx⟩
  exact ⟨hr _ hx, hl _ hx, hn _ hx, hm _ hx, hq _ hx, hp _ hx, hpot _ hx, ht _ hx, hxi _ hx⟩

end EmcsfAcExtension.Local.Broad
