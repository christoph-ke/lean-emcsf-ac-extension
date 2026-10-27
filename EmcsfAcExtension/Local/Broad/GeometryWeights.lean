module

public import EmcsfAcExtension.Local.Broad.ScalarAverage
public import EmcsfAcExtension.Local.Broad.GeometryAlgebra

/-! # Both radial weights in a common geometric box

The radius comparison follows from the outgoing radius primitive. The
weight can be either outgoing expansion or negative incoming expansion.
-/

public section

open Set

namespace EmcsfAcExtension.Local.Broad

/-- Comparable positive weights and radii give comparable radial weights.
The coefficient `k²` is explicit and independent of all field values. -/
theorem radial_weight_le_of_comparable_factors {w₁ w₂ r₁ r₂ k : ℝ}
    (hk : 0 ≤ k) (_hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hw : w₁ ≤ k * w₂) (hr : r₂ ≤ k * r₁) : w₁ / r₁ ≤ k ^ 2 * (w₂ / r₂) := by
  calc
    w₁ / r₁ ≤ (k ^ 2 * w₂) / r₂ := by
      apply (div_le_div_iff₀ hr₁ hr₂).mpr
      calc
        w₁ * r₂ ≤ (k * w₂) * (k * r₁) := mul_le_mul hw hr hr₂.le (mul_nonneg hk hw₂)
        _ = _ := by ring
    _ = _ := by ring

/-- A common positive outgoing expansion box gives two-sided radius
comparison with explicit factor `C/c`, uniformly over the complete
triangle and both solutions. -/
theorem radius_comparison_of_solution_box {s t e c C u v : ℝ} {S₁ S₂ : Fields}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hS₁ : IsSolution e S₁ (triangle s t)) (hS₂ : IsSolution e S₂ (triangle s t))
    (hbox : ∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C)
    (hp : (u, v) ∈ triangle s t) :
    S₁.r u v ≤ (C / c) * S₂.r u v ∧ S₂.r u v ≤ (C / c) * S₁.r u v := by
  have hs : outSeg u u v ⊆ triangle s t := by
    rintro p ⟨rfl, hx⟩
    exact ⟨hp.1, hx.1, hx.2.trans hp.2.2⟩
  have hr₁ := outgoing_radius_lower hS₁ hp.2.1 hs
    (fun x hx => (hbox S₁ (by simp) (u, x) (hs ⟨rfl, hx⟩)).1)
  have hr₂ := outgoing_radius_lower hS₂ hp.2.1 hs
    (fun x hx => (hbox S₂ (by simp) (u, x) (hs ⟨rfl, hx⟩)).1)
  have hR₁ := outgoing_radius_upper hS₁ hp.2.1 hs
    (fun x hx => (hbox S₁ (by simp) (u, x) (hs ⟨rfl, hx⟩)).2)
  have hR₂ := outgoing_radius_upper hS₂ hp.2.1 hs
    (fun x hx => (hbox S₂ (by simp) (u, x) (hs ⟨rfl, hx⟩)).2)
  have heq : C * (v - u) = (C / c) * (c * (v - u)) := by field_simp
  constructor
  · exact hR₁.trans (heq.trans_le (mul_le_mul_of_nonneg_left hr₂ (div_nonneg hC hc.le)))
  · exact hR₂.trans (heq.trans_le (mul_le_mul_of_nonneg_left hr₁ (div_nonneg hC hc.le)))

/-- Pointwise comparison of either oriented pair of radial weights in a
fixed box. The explicit coefficients `(C/c)²` and `(1+C*(C/c))/c`
depend only on the box and are uniform in both solutions, labels and
geometric error. The zero-radius convention is included on the axis. -/
theorem radial_weights_of_solution_box {s t e c C u v w₁ w₂ : ℝ} {S₁ S₂ : Fields}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hS₁ : IsSolution e S₁ (triangle s t)) (hS₂ : IsSolution e S₂ (triangle s t))
    (hbox : ∀ S ∈ ({S₁, S₂} : Set Fields), ∀ p ∈ triangle s t,
      c ≤ S.lam p.1 p.2 ∧ S.lam p.1 p.2 ≤ C)
    (hp : (u, v) ∈ triangle s t)
    (hw : c ≤ w₁ ∧ w₁ ≤ C ∧ c ≤ w₂ ∧ w₂ ≤ C)
    (hδw : |w₁ - w₂| ≤ (geometry_distance s t S₁ S₂).toReal) :
    w₁ / S₁.r u v ≤ (C / c) ^ 2 * (w₂ / S₂.r u v) ∧
      |w₁ / S₁.r u v - w₂ / S₂.r u v| ≤
        ((1 + C * (C / c)) / c) * (geometry_distance s t S₁ S₂).toReal * (w₁ / S₁.r u v) := by
  rcases eq_or_lt_of_le (show u ≤ v from hp.2.1) with huv | huv
  · subst v
    simp only [(hS₁.axis u hp).1, (hS₂.axis u hp).1, div_zero, mul_zero, sub_self, abs_zero,
      le_refl, and_self]
  · have hr₁ := hS₁.r_pos (u, v) hp huv
    have hr₂ := hS₂.r_pos (u, v) hp huv
    have hrr := radius_comparison_of_solution_box hc hC hS₁ hS₂ hbox hp
    have hk := div_nonneg hC hc.le
    have hwr : w₁ ≤ (C / c) * w₂ := by
      apply hw.2.1.trans
      have heq : C = (C / c) * c := by field_simp
      exact heq.trans_le (mul_le_mul_of_nonneg_left hw.2.2.1 hk)
    have hfin := geometry_distance_ne_top hS₁ hS₂ hc
      (fun p hp => (hbox S₁ (by simp) p hp).1)
    exact ⟨radial_weight_le_of_comparable_factors hk (hc.le.trans hw.1)
      (hc.le.trans hw.2.2.1) hr₁ hr₂ hwr hrr.2,
      radial_weight_difference_of_bounds hc hC hk ENNReal.toReal_nonneg hw.1
        (hc.le.trans hw.2.2.1) hw.2.2.2 hr₁ hr₂ hrr.1 hδw
        (abs_radius_sub_le_geometry_distance_mul_radius hS₁ hS₂ hfin hp)⟩

end EmcsfAcExtension.Local.Broad
