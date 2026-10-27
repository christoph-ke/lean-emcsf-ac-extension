module

public import EmcsfAcExtension.Local.Stability.PotentialSourceAlgebra

/-! # The incoming Maxwell-current source over the radius

Both current factors and both coefficient/radius factors are subtracted
before replacing the radial weights by their fixed-box separation
bounds. This preserves the incoming ratio area term explicitly.
-/

public section

namespace EmcsfAcExtension.Local

/-- A current source over the radius retains the local ratio error
`X/L` and undifferenced vanishing ratio `Y/L`. The coefficients `32`
and `224` are universal for the literal coefficient and radius box.
No minimum radius or derivative bound enters. -/
theorem stab_current_over_radius_sub_le
    {a b r s L K G U M Φ X Y J₁ J₂ : ℝ}
    (hL : 0 < L) (hr : 0 < r) (hs : 0 < s)
    (hrL : L / 4 ≤ r) (hsL : L / 4 ≤ s)
    (hK : 0 ≤ K) (hG : 0 ≤ G) (hU : 0 ≤ U) (_hM : 0 ≤ M)
    (_hΦ : 0 ≤ Φ) (_hX : 0 ≤ X) (_hY : 0 ≤ Y)
    (hrel : |r - s| / r ≤ G)
    (ha : |a| ≤ 8 * K) (hab : |a - b| ≤ 48 * K * (G + U))
    (hJ : |J₁ - J₂| ≤ M * X + Φ * Y) (hJ₂ : |J₂| ≤ M * Y) :
    |a / r * J₁ - b / s * J₂| ≤
      32 * K * M * (X / L) + (32 * K * Φ + 224 * K * M * (G + U)) * (Y / L) := by
  have hiR : 1 / r ≤ 4 / L := by
    rw [div_le_div_iff₀ hr hL]
    linarith only [hrL]
  have hiS : 1 / s ≤ 4 / L := by
    rw [div_le_div_iff₀ hs hL]
    linarith only [hsL]
  have hc₁ : |a / r| ≤ 32 * K / L := by
    rw [abs_div, abs_of_pos hr]
    calc
      _ = |a| * (1 / r) := by ring
      _ ≤ (8 * K) * (4 / L) := mul_le_mul ha hiR (one_div_nonneg.mpr hr.le) (by positivity)
      _ = _ := by ring
  have hcD : |a / r - b / s| ≤ 224 * K * (G + U) / L := by
    apply (stab_coefficient_over_radius_sub_le hr hs ha hab hrel).trans
    calc
      _ = (48 * K * (G + U) + (8 * K) * G) * (1 / s) := by ring
      _ ≤ (56 * K * (G + U)) * (4 / L) := by
        apply mul_le_mul _ hiS (one_div_nonneg.mpr hs.le) (by positivity)
        nlinarith only [mul_nonneg hK hU]
      _ = _ := by ring
  apply stab_real_product_sub_le.trans
  apply (add_le_add (mul_le_mul hc₁ hJ (abs_nonneg _) (by positivity))
    (mul_le_mul hcD hJ₂ (abs_nonneg _) (by positivity))).trans_eq
  ring

end EmcsfAcExtension.Local
