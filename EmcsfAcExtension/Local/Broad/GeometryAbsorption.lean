module

public import EmcsfAcExtension.Local.Broad.Setup

/-! # Finite geometric absorption at fixed variation budget

These are algebraic helpers for the solution-level geometric comparison.
They retain the finite real distances and every smallness coefficient.
-/

public section

namespace EmcsfAcExtension.Local.Broad

/-- Absorb the broad geometric feedback with exact coefficient `2*K`.
The coefficient `K` is fixed before all errors and scale parameters.
The variation budget is arbitrary and finite. This helper takes the raw
geometric inequality that the solution-level comparison must prove. -/
theorem geometry_after_absorption_of_bound {K L ε σ d g : ℝ}
    (hK : 0 ≤ K) (_hL : 0 ≤ L) (hε : 0 ≤ ε) (hd : 0 ≤ d) (hg : 0 ≤ g)
    (hσ : σ ≤ 1) (hsmall : K * ε * (L + 1) ≤ 1 / 2)
    (hgeom : g ≤ K * L * d + K * ε * L * g + K * σ * (d + ε * g)) :
    g ≤ 2 * K * (L + 1) * d := by
  have hE : 0 ≤ d + ε * g := by positivity
  have hgeom' : g ≤ K * (L + 1) * d + (K * ε * (L + 1)) * g := by
    apply hgeom.trans
    have hh := mul_le_mul_of_nonneg_right hσ (mul_nonneg hK hE)
    nlinarith only [hh]
  have hfeed := mul_le_mul_of_nonneg_right hsmall hg
  nlinarith only [hgeom', hfeed]

end EmcsfAcExtension.Local.Broad
