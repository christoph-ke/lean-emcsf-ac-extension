module

public import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux

/-! # Comparison of the positive radial measures

The literal fixed box compares the two measures with coefficient `16`.
These preliminary inequalities use no mass or stability conclusion.
-/

public section

open Set

namespace EmcsfAcExtension.Local

private theorem weight_le_aux {a b r s : ℝ} (ha : a ≤ 1) (hb : 1 / 4 ≤ b)
    (hr : 0 < r) (hs : 0 < s) (hcompare : s ≤ 4 * r) : a / r ≤ 16 * (b / s) := by
  rw [← mul_div_assoc, div_le_div_iff₀ hr hs]
  calc
    a * s ≤ s := by simpa only [one_mul] using mul_le_mul_of_nonneg_right ha hs.le
    _ ≤ 4 * r := hcompare
    _ ≤ 16 * b * r := mul_le_mul_of_nonneg_right (by linarith only [hb]) hr.le

/-- The outgoing positive radial measure of the first solution is at
most `16` times that of the second. The coefficient is universal and
independent of all parameters, the pair and minimum radius. -/
theorem stab_out_weight_le_sixteen
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    S₁.lam u v / S₁.r u v ≤ 16 * (S₂.lam u v / S₂.r u v) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  exact weight_le_aux (h₁s.box.2 (u, v) hp).2.1 (h₂s.box.2 (u, v) hp).1
    (h₁s.c1.r_pos (u, v) hp huv) (h₂s.c1.r_pos (u, v) hp huv)
    (stab_radius_compare h₁s h₂s hu huv.le hvT).2

/-- The incoming positive radial measures have the same universal
comparison coefficient `16`, before any difference estimate is used. -/
theorem stab_in_weight_le_sixteen
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    -S₁.nu u v / S₁.r u v ≤ 16 * (-S₂.nu u v / S₂.r u v) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  exact weight_le_aux (h₁s.box.2 (u, v) hp).2.2.2.1 (h₂s.box.2 (u, v) hp).2.2.1
    (h₁s.c1.r_pos (u, v) hp huv) (h₂s.c1.r_pos (u, v) hp huv)
    (stab_radius_compare h₁s h₂s hu huv.le hvT).2

end EmcsfAcExtension.Local
