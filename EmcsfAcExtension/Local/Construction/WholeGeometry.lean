module

public import Mathlib

/-! # Uniform capped continuation geometry

The corner width is chosen from the candidate apex and the previously
fixed short-cone time. The cap height is then chosen after the strip
height; both choices precede the nearby old apex.
-/

public section

namespace EmcsfAcExtension.Local

/-- Choose a corner width before the strip height and a common capped
extension height afterward. Both are uniform in the old apex `S` and
the terminal endpoint `T`. The cap includes `T` when it is reached.
The constants depend only on `q`, `τ`, then `δstrip`; in particular the
cone length stays below the previously chosen short-cone time. -/
theorem continuation_capped_band_geometry {q τ : ℝ} (hq : 0 < q) (hτ : 0 < τ) :
    ∃ η : ℝ, 0 < η ∧ η < q/8 ∧ η < τ/8 ∧
      ∀ δstrip : ℝ, 0 < δstrip →
        ∃ Δ : ℝ, 0 < Δ ∧ Δ ≤ δstrip ∧ Δ < η ∧ Δ < τ/8 ∧
          ∀ T S : ℝ, q ≤ T → q-Δ < S → S < q →
            q/2 < S ∧ 2*η < S ∧ 0 ≤ S-η ∧
            S-η < S-3*η/4 ∧ S-3*η/4 < S ∧
            S < min T (S+Δ) ∧ min T (S+Δ) ≤ T ∧
            min T (S+Δ)-S ≤ δstrip ∧
            min T (S+Δ)-(S-η) ≤ τ := by
  let η := min q τ / 16
  have hη : 0 < η := div_pos (lt_min hq hτ) (by norm_num)
  have hηq : η < q/8 := by
    have hm := min_le_left q τ
    dsimp only [η]
    linarith only [hm, hq]
  have hητ : η < τ/8 := by
    have hm := min_le_right q τ
    dsimp only [η]
    linarith only [hm, hτ]
  refine ⟨η, hη, hηq, hητ, ?_⟩
  intro δstrip hstrip
  let z := min δstrip (min η (τ/8))
  let Δ := z/2
  have hz : 0 < z := lt_min hstrip (lt_min hη (by positivity))
  have hΔ : 0 < Δ := div_pos hz (by norm_num)
  have hΔz : Δ ≤ z := by dsimp only [Δ]; linarith only [hz]
  have hΔstrip : Δ ≤ δstrip := hΔz.trans (min_le_left _ _)
  have hzη : z ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hzτ : z ≤ τ/8 := (min_le_right _ _).trans (min_le_right _ _)
  have hΔη : Δ < η := by dsimp only [Δ]; linarith only [hzη, hη]
  have hΔτ : Δ < τ/8 := by dsimp only [Δ]; linarith only [hzτ, hτ]
  refine ⟨Δ, hΔ, hΔstrip, hΔη, hΔτ, ?_⟩
  intro T S hqT hclose hSq
  have hhalf : q/2 < S := by linarith only [hclose, hΔη, hηq, hq, hη]
  have hwidth : 2*η < S := by linarith only [hclose, hΔη, hηq, hq, hη]
  have hc : 0 ≤ S-η := by linarith only [hwidth, hη]
  have hcd : S-η < S-3*η/4 := by linarith only [hη]
  have hdS : S-3*η/4 < S := by linarith only [hη]
  have hSb : S < min T (S+Δ) := lt_min (hSq.trans_le hqT) (by linarith only [hΔ])
  have hheight : min T (S+Δ)-S ≤ Δ := by
    have hm := min_le_right T (S+Δ)
    linarith only [hm]
  have hlength : min T (S+Δ)-(S-η) ≤ τ := by
    linarith only [hheight, hΔτ, hητ, hτ]
  exact ⟨hhalf, hwidth, hc, hcd, hdS, hSb, min_le_left _ _,
    hheight.trans hΔstrip, hlength⟩

end EmcsfAcExtension.Local
