module

public import EmcsfAcExtension.Local.Broad.Mass
import EmcsfAcExtension.Local.Calculus.RelativeCharge

/-! # Constraint determination on the common entering cone

The boundary in this file is the entering cone and its vertex, as specified
by amendment internal project record. Later axis values are not boundary data here.
The arguments use the frozen integral class without derivative envelopes.
-/

public section

open Set MeasureTheory Filter Complex
open scoped Topology

namespace EmcsfAcExtension.Local.Broad

/-- Equal radius traces determine the outgoing expansion on a nondegenerate
complete cone. The endpoint values follow from continuity. -/
theorem cone_lam_eq_of_radius_eq {e u v : ℝ} {S₁ S₂ : Fields}
    {D₁ D₂ : Set (ℝ × ℝ)} (hS₁ : IsSolution e S₁ D₁) (hS₂ : IsSolution e S₂ D₂)
    (huv : u < v) (hs₁ : outSeg u u v ⊆ D₁) (hs₂ : outSeg u u v ⊆ D₂)
    (hr : ∀ x ∈ Icc u v, S₁.r u x = S₂.r u x) :
    ∀ x ∈ Icc u v, S₁.lam u x = S₂.lam u x := by
  have heq : EqOn (S₁.lam u) (S₂.lam u) (Ioo u v) := by
    intro x hx
    have h₁ := IsSolution.hasDerivAt_radius_out hS₁ hs₁ hx
    have h₂ := IsSolution.hasDerivAt_radius_out hS₂ hs₂ hx
    have hnear : S₁.r u =ᶠ[𝓝 x] S₂.r u := by
      filter_upwards [Icc_mem_nhds hx.1 hx.2] with y hy
      exact hr y hy
    exact h₁.unique (h₂.congr_of_eventuallyEq hnear)
  exact heq.of_subset_closure (continuousOn_out_section hS₁.cont_lam hs₁)
    (continuousOn_out_section hS₂.cont_lam hs₂) Ioo_subset_Icc_self
    (by rw [closure_Ioo huv.ne])

/-- Equal radius and normalized outgoing data determine the scalar on the
entire entering cone, including its vertex. -/
theorem cone_phi_eq_of_data_eq {e u v : ℝ} {S₁ S₂ : Fields}
    {D₁ D₂ : Set (ℝ × ℝ)} (hS₁ : IsSolution e S₁ D₁) (hS₂ : IsSolution e S₂ D₂)
    (huv : u < v) (hs₁ : outSeg u u v ⊆ D₁) (hs₂ : outSeg u u v ⊆ D₂)
    (hr : ∀ x ∈ Icc u v, S₁.r u x = S₂.r u x)
    (ha : ∀ x ∈ Icc u v, S₁.a u x = S₂.a u x) :
    ∀ x ∈ Icc u v, S₁.phi u x = S₂.phi u x := by
  have hl := cone_lam_eq_of_radius_eq hS₁ hS₂ huv hs₁ hs₂ hr
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst x
    rw [← (hS₁.axis u (hs₁ ⟨rfl, le_rfl, huv.le⟩)).2.2.2.2.1,
      ← (hS₂.axis u (hs₂ ⟨rfl, le_rfl, huv.le⟩)).2.2.2.2.1]
    exact ha u ⟨le_rfl, huv.le⟩
  · have hsub₁ : outSeg u u x ⊆ D₁ :=
      fun p hp => hs₁ ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩
    have hsub₂ : outSeg u u x ⊆ D₂ :=
      fun p hp => hs₂ ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩
    have hprim₁ := outgoing_scalar_reconstruction hS₁ h.le hsub₁
    have hprim₂ := outgoing_scalar_reconstruction hS₂ h.le hsub₂
    have hi : (∫ y in u..x, (S₁.lam u y : ℂ) * S₁.a u y) =
        ∫ y in u..x, (S₂.lam u y : ℂ) * S₂.a u y := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le h.le] at hy
      have hy' : y ∈ Icc u v := ⟨hy.1, hy.2.trans hx.2⟩
      simp only [hl y hy', ha y hy']
    have hz : (S₂.r u x : ℂ) ≠ 0 := by
      exact_mod_cast (hS₂.r_pos (u, x) (hs₂ ⟨rfl, hx⟩) h).ne'
    rw [hr x hx] at hprim₁
    exact mul_left_cancel₀ hz (hprim₁.trans (hi.trans hprim₂.symm))

/-- The normalized-field definition recovers the outgoing transport field
once the expansion, scalar and normalized outgoing traces agree. -/
theorem theta_eq_of_lam_phi_a_eq {S₁ S₂ : Fields} {u v : ℝ}
    (hl₁ : S₁.lam u v ≠ 0) (_hl₂ : S₂.lam u v ≠ 0)
    (hl : S₁.lam u v = S₂.lam u v) (hp : S₁.phi u v = S₂.phi u v)
    (ha : S₁.a u v = S₂.a u v) : S₁.theta u v = S₂.theta u v := by
  have hz : (S₁.lam u v : ℂ) ≠ 0 := by exact_mod_cast hl₁
  have hd : S₁.theta u v / (S₁.lam u v : ℂ) =
      S₂.theta u v / (S₁.lam u v : ℂ) := by
    simpa only [Fields.a, hp, hl, add_right_inj] using ha
  exact (div_left_inj' hz).mp hd

/-- The zero-axis Maxwell primitive determines the charge on a common cone
from its common radius and normalized outgoing datum. -/
theorem cone_charge_eq_of_data_eq {e u v : ℝ} {S₁ S₂ : Fields}
    {D₁ D₂ : Set (ℝ × ℝ)} (hS₁ : IsSolution e S₁ D₁) (hS₂ : IsSolution e S₂ D₂)
    (huv : u < v) (hs₁ : outSeg u u v ⊆ D₁) (hs₂ : outSeg u u v ⊆ D₂)
    (hr : ∀ x ∈ Icc u v, S₁.r u x = S₂.r u x)
    (ha : ∀ x ∈ Icc u v, S₁.a u x = S₂.a u x) :
    ∀ x ∈ Icc u v, S₁.Q u x = S₂.Q u x := by
  have hl := cone_lam_eq_of_radius_eq hS₁ hS₂ huv hs₁ hs₂ hr
  have hp := cone_phi_eq_of_data_eq hS₁ hS₂ huv hs₁ hs₂ hr ha
  intro x hx
  have hsub₁ : outSeg u u x ⊆ D₁ :=
    fun p hp => hs₁ ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩
  have hsub₂ : outSeg u u x ⊆ D₂ :=
    fun p hp => hs₂ ⟨hp.1, hp.2.1, hp.2.2.trans hx.2⟩
  rw [Stab.oscillatory_charge_constraint hS₁ hx.1 hsub₁,
    Stab.oscillatory_charge_constraint hS₂ hx.1 hsub₂]
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le hx.1] at hy
  have hy' : y ∈ Icc u v := ⟨hy.1, hy.2.trans hx.2⟩
  have ht := theta_eq_of_lam_phi_a_eq
    (hS₁.lam_pos (u, y) (hs₁ ⟨rfl, hy'⟩)).ne'
    (hS₂.lam_pos (u, y) (hs₂ ⟨rfl, hy'⟩)).ne'
    (hl y hy') (hp y hy') (ha y hy')
  simp only [hl y hy', hr y hy', hp y hy', ht]

end EmcsfAcExtension.Local.Broad
