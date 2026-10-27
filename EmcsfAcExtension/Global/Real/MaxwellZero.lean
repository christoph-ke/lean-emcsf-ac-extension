module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.OrigDomain

/-! # Vanishing charge and potential at zero coupling

internal project record R3 uses only continuity, the outgoing equations, the regular axis and
the axis gauge. The domain hypothesis is stated directly as a segment inclusion.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Real

/-- [internal] A continuous outgoing section that agrees with its right endpoint
off the axis also agrees at its axis endpoint. -/
private theorem eq_axis_of_eq_offAxis {f : ℝ → ℝ → ℝ} {D : Set (ℝ × ℝ)}
    {u v : ℝ} (hc : ContinuousOn (Function.uncurry f) D) (huv : u < v)
    (hs : outSeg u u v ⊆ D)
    (he : ∀ x ∈ Ioo u v, f u x = f u v) : f u v = f u u := by
  have c : ContinuousOn (f u) (Icc u v) :=
    hc.comp (f := fun x => (u, x))
      (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => hs ⟨rfl, hx⟩)
  have h := (show EqOn (f u) (fun _ => f u v) (Ioo u v) from he).of_subset_closure
    c continuousOn_const Ioo_subset_Icc_self
    (show Icc u v ⊆ closure (Ioo u v) by rw [closure_Ioo huv.ne])
  exact (h ⟨le_rfl, huv.le⟩).symm

/-- In the uncharged class, an axis gauge and complete outgoing segments force
both Maxwell fields to vanish throughout any domain (internal project record R3). -/
theorem charge_potential_zero_of_outgoing_segments {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution 0 S D) (hgauge : ∀ t, (t, t) ∈ D → S.A t t = 0)
    (hseg : ∀ p ∈ D, p.1 < p.2 → outSeg p.1 p.1 p.2 ⊆ D) :
    ∀ p ∈ D, S.Q p.1 p.2 = 0 ∧ S.A p.1 p.2 = 0 := by
  have hQ : ∀ p ∈ D, S.Q p.1 p.2 = 0 := by
    rintro ⟨u, v⟩ hp
    rcases (show u ≤ v from hS.subset hp).eq_or_lt with heq | huv
    · change u = v at heq
      subst v
      exact (hS.axis u hp).2.2.1
    · have hs := hseg (u, v) hp huv
      have he : S.Q u v = S.Q u u := by
        apply eq_axis_of_eq_offAxis hS.cont_Q huv hs
        intro x hx
        have hi := (hS.eq_out u x v hx.1 hx.2.le (fun p hp' =>
          hs ⟨hp'.1, hx.1.le.trans hp'.2.1, hp'.2.2⟩)).2.2.2.1.2
        have hz : S.Q u v - S.Q u x = 0 := by simpa [Fields.QV] using hi
        exact (sub_eq_zero.mp hz).symm
      exact he.trans (hS.axis u (hs ⟨rfl, le_rfl, huv.le⟩)).2.2.1
  intro p hp
  refine ⟨hQ p hp, ?_⟩
  rcases p with ⟨u, v⟩
  rcases (show u ≤ v from hS.subset hp).eq_or_lt with heq | huv
  · change u = v at heq
    subst v
    exact hgauge u hp
  · have hs := hseg (u, v) hp huv
    have he : S.A u v = S.A u u := by
      apply eq_axis_of_eq_offAxis hS.cont_A huv hs
      intro x hx
      have hi := (hS.eq_out u x v hx.1 hx.2.le (fun p hp' =>
        hs ⟨hp'.1, hx.1.le.trans hp'.2.1, hp'.2.2⟩)).2.2.2.2.1.2
      have hz : (∫ y in x..v, S.AV u y) = 0 := by
        calc
          (∫ y in x..v, S.AV u y) = ∫ _y in x..v, (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro y hy
            rw [uIcc_of_le hx.2.le] at hy
            simp [Fields.AV, hQ (u, y) (hs ⟨rfl, hx.1.le.trans hy.1, hy.2⟩)]
          _ = 0 := intervalIntegral.integral_zero
      rw [hz] at hi
      exact (sub_eq_zero.mp hi).symm
    exact he.trans (hgauge u (hs ⟨rfl, le_rfl, huv.le⟩))

/-- Charge and potential vanish on the original domain in the uncharged axis gauge. -/
theorem charge_potential_zero_origDomain {ui : ℝ} {S : Fields}
    (hS : IsSolution 0 S (origDomain ui))
    (hgauge : ∀ t, (t, t) ∈ origDomain ui → S.A t t = 0) :
    ∀ p ∈ origDomain ui, S.Q p.1 p.2 = 0 ∧ S.A p.1 p.2 = 0 := by
  apply charge_potential_zero_of_outgoing_segments hS hgauge
  rintro ⟨u, v⟩ hp _ ⟨x, y⟩ ⟨rfl, huy, hyv⟩
  exact ⟨hp.1, hp.2.1, huy, hyv.trans hp.2.2.2⟩

/-- Charge and potential vanish on the union of the original domain and a restart
triangle. The segment property holds for all endpoints, hence in particular when
`ui < us < 0 < vp` as in internal project record R3. -/
theorem charge_potential_zero_origDomain_union_triangle {ui us vp : ℝ} {S : Fields}
    (hS : IsSolution 0 S (origDomain ui ∪ triangle us vp))
    (hgauge : ∀ t, (t, t) ∈ origDomain ui ∪ triangle us vp → S.A t t = 0) :
    ∀ p ∈ origDomain ui ∪ triangle us vp, S.Q p.1 p.2 = 0 ∧ S.A p.1 p.2 = 0 := by
  apply charge_potential_zero_of_outgoing_segments hS hgauge
  rintro ⟨u, v⟩ hp _ ⟨x, y⟩ ⟨rfl, huy, hyv⟩
  rcases hp with hp | hp
  · exact Or.inl ⟨hp.1, hp.2.1, huy, hyv.trans hp.2.2.2⟩
  · exact Or.inr ⟨hp.1, huy, hyv.trans hp.2.2⟩

end EmcsfAcExtension.Global.Real
