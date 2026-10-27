module

public import EmcsfAcExtension.Local.Construction.Strip

/-! # Fixed positive tubes around old continuation states

A tube radius chosen from the old geometric lower bounds precedes both
states and the state norm bound. The Hawking-gap numerator is linear;
its change costs at most three times the product-norm state difference.
-/

public section

open Set

namespace EmcsfAcExtension.Local

open Broad

/-- The four real geometric components have difference at most the full
state distance. The linear mass-gap numerator has difference at most three
times that distance. All coefficients are numerical and uniform in both
states, the coupling and every continuation parameter. -/
theorem rectangle_state_geometric_difference_le (x y : RectangleState) :
    |x.2.1 - y.2.1| ≤ ‖x - y‖ ∧ |x.1.1 - y.1.1| ≤ ‖x - y‖ ∧
      |x.2.2.1 - y.2.2.1| ≤ ‖x - y‖ ∧
      |x.2.2.2.1 - y.2.2.2.1| ≤ ‖x - y‖ ∧
      |(x.2.1 - 2 * x.2.2.2.1) - (y.2.1 - 2 * y.2.2.2.1)| ≤ 3 * ‖x - y‖ := by
  have hr (z : RectangleState) : |z.2.1| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le z.2).trans (norm_snd_le z)
  have hl (z : RectangleState) : |z.1.1| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le z.1).trans (norm_fst_le z)
  have hn (z : RectangleState) : |z.2.2.1| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le z.2.2).trans
      ((norm_snd_le z.2).trans (norm_snd_le z))
  have hm (z : RectangleState) : |z.2.2.2.1| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le z.2.2.2).trans
      ((norm_snd_le z.2.2).trans ((norm_snd_le z.2).trans (norm_snd_le z)))
  refine ⟨hr (x - y), hl (x - y), hn (x - y), hm (x - y), ?_⟩
  calc
    |(x.2.1 - 2 * x.2.2.2.1) - (y.2.1 - 2 * y.2.2.2.1)| =
        |(x.2.1 - y.2.1) - 2 * (x.2.2.2.1 - y.2.2.2.1)| := by
      congr 1
      ring
    _ ≤ |x.2.1 - y.2.1| + |2 * (x.2.2.2.1 - y.2.2.2.1)| := by
      simpa only [Real.norm_eq_abs] using
        norm_sub_le (x.2.1 - y.2.1) (2 * (x.2.2.2.1 - y.2.2.2.1))
    _ = |x.2.1 - y.2.1| + 2 * |x.2.2.2.1 - y.2.2.2.1| := by
      rw [abs_mul]
      norm_num
    _ ≤ ‖x - y‖ + 2 * ‖x - y‖ :=
      add_le_add (hr (x - y)) (mul_le_mul_of_nonneg_left (hm (x - y)) (by norm_num))
    _ = 3 * ‖x - y‖ := by ring

/-- A fixed tube around any old lower-side state preserves all geometric
signs and lies in the compact continuation source box. The positive radius
`τ` depends only on `ℓ,r₀`, before the state bound `B` and both states.
The proof uses the explicit witness
`min 1 (min (r₀/4) (min (ℓ/4) (ℓ*r₀/12)))`; the box margin is exactly
the requested half-margin `min (r₀/2) (min (ℓ/2) (ℓ*r₀/2))`.
The individual half-margins are retained for quantitative strip bounds.
No bound on an old derivative, apex location or coupling is required. -/
theorem continuation_state_tube (ℓ r₀ : ℝ) (hℓ : 0 < ℓ) (hr₀ : 0 < r₀) :
    ∃ τ > 0, ∀ (B : ℝ) (old new : RectangleState),
      ‖old‖ ≤ B → r₀ ≤ old.2.1 → ℓ ≤ old.1.1 → ℓ ≤ -old.2.2.1 →
      ℓ ≤ 1 - 2 * old.2.2.2.1 / old.2.1 → ‖new - old‖ ≤ τ →
      new ∈ continuationStateBox (min (r₀ / 2) (min (ℓ / 2) (ℓ * r₀ / 2))) (B + 1) ∧
      new ∈ rectangle_state_region ∧ new.2.2.1 < 0 ∧
      0 < 1 - 2 * new.2.2.2.1 / new.2.1 ∧ r₀ / 2 ≤ new.2.1 ∧
      ℓ / 2 ≤ new.1.1 ∧ ℓ / 2 ≤ -new.2.2.1 ∧
        ℓ * r₀ / 2 ≤ new.2.1 - 2 * new.2.2.2.1 := by
  let τ := min 1 (min (r₀ / 4) (min (ℓ / 4) (ℓ * r₀ / 12)))
  have hτ : 0 < τ := lt_min zero_lt_one
    (lt_min (div_pos hr₀ (by norm_num))
      (lt_min (div_pos hℓ (by norm_num)) (div_pos (mul_pos hℓ hr₀) (by norm_num))))
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτr : τ ≤ r₀ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hτl : τ ≤ ℓ / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτg : τ ≤ ℓ * r₀ / 12 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨τ, hτ, ?_⟩
  intro B old new hB hr hl hn hg hdist
  have hRold : 0 < old.2.1 := hr₀.trans_le hr
  have hNold : ℓ * r₀ ≤ old.2.1 - 2 * old.2.2.2.1 := by
    have he : (1 - 2 * old.2.2.2.1 / old.2.1) * old.2.1 =
        old.2.1 - 2 * old.2.2.2.1 := by field_simp [hRold.ne']
    calc
      ℓ * r₀ ≤ ℓ * old.2.1 := mul_le_mul_of_nonneg_left hr hℓ.le
      _ ≤ (1 - 2 * old.2.2.2.1 / old.2.1) * old.2.1 :=
        mul_le_mul_of_nonneg_right hg hRold.le
      _ = old.2.1 - 2 * old.2.2.2.1 := he
  obtain ⟨hδr, hδl, hδn, _hδm, hδg⟩ := rectangle_state_geometric_difference_le new old
  have hδr' := abs_le.mp (hδr.trans hdist)
  have hδl' := abs_le.mp (hδl.trans hdist)
  have hδn' := abs_le.mp (hδn.trans hdist)
  have hδg' := abs_le.mp (hδg.trans (mul_le_mul_of_nonneg_left hdist (by norm_num)))
  have hrnew : r₀ / 2 ≤ new.2.1 := by linarith only [hr, hτr, hδr'.1, hr₀]
  have hlnew : ℓ / 2 ≤ new.1.1 := by linarith only [hl, hτl, hδl'.1, hℓ]
  have hnnew : new.2.2.1 < 0 := by linarith only [hn, hτl, hδn'.2, hℓ]
  have hnnew_half : ℓ / 2 ≤ -new.2.2.1 := by linarith only [hn, hτl, hδn'.2, hℓ]
  have hgnew : ℓ * r₀ / 2 ≤ new.2.1 - 2 * new.2.2.2.1 := by
    linarith only [hNold, hτg, hδg'.1, hτ]
  have hnorm : ‖new‖ ≤ B + 1 := by
    calc
      ‖new‖ = ‖(new - old) + old‖ := by rw [sub_add_cancel]
      _ ≤ ‖new - old‖ + ‖old‖ := norm_add_le _ _
      _ ≤ τ + B := add_le_add hdist hB
      _ ≤ B + 1 := by linarith only [hτ1]
  have hbox : new ∈ continuationStateBox
      (min (r₀ / 2) (min (ℓ / 2) (ℓ * r₀ / 2))) (B + 1) := by
    refine ⟨?_, (min_le_left _ _).trans hrnew,
      ((min_le_right _ _).trans (min_le_left _ _)).trans hlnew,
      ((min_le_right _ _).trans (min_le_right _ _)).trans hgnew⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hnorm
  have hρ : 0 < min (r₀ / 2) (min (ℓ / 2) (ℓ * r₀ / 2)) :=
    lt_min (div_pos hr₀ (by norm_num))
      (lt_min (div_pos hℓ (by norm_num)) (div_pos (mul_pos hℓ hr₀) (by norm_num)))
  have hregion := continuationStateBox_subset_region hρ hbox
  have hgap : 0 < 1 - 2 * new.2.2.2.1 / new.2.1 := by
    have he : 1 - 2 * new.2.2.2.1 / new.2.1 =
        (new.2.1 - 2 * new.2.2.2.1) / new.2.1 := by field_simp [hregion.1.ne']
    rw [he]
    exact div_pos hregion.2.2 hregion.1
  exact ⟨hbox, hregion, hnnew, hgap, hrnew, hlnew, hnnew_half, hgnew⟩

end EmcsfAcExtension.Local
