module

public import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Calculus.Normalized
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Difference of the outgoing scalar derivatives

The exact radial derivative is subtracted at the common null labels.
The coefficient difference retains the second solution's scalar ratio.
-/

public section

open Set

namespace EmcsfAcExtension.Local

private theorem radial_smul_aux {r l : ℝ} (hr : r ≠ 0) (hl : l ≠ 0) (z : ℂ) :
    z / (r : ℂ) = (l / r : ℝ) • (z / (l : ℂ)) := by
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hlC : (l : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
  simp only [Complex.real_smul, Complex.ofReal_div]
  field_simp

/-- The outgoing scalar partial difference is controlled by the
weighted ratio difference plus the geometric error, with universal
coefficients `1` and `20`, before all parameters and the pair. -/
theorem stab_out_scalar_partial_sub_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖pdV (triangle 0 T) S₁.phi u v - pdV (triangle 0 T) S₂.phi u v‖ ≤
      S₁.lam u v / S₁.r u v *
        ‖S₁.theta u v / (S₁.lam u v : ℂ) - S₂.theta u v / (S₂.lam u v : ℂ)‖ +
      20 * (geomDist T S₁ S₂).toReal *
        (S₁.lam u v / S₁.r u v * ‖S₂.theta u v / (S₂.lam u v : ℂ)‖) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  let a := S₁.lam u v / S₁.r u v
  let b := S₂.lam u v / S₂.r u v
  let x := S₁.theta u v / (S₁.lam u v : ℂ)
  let y := S₂.theta u v / (S₂.lam u v : ℂ)
  have h₁ : pdV (triangle 0 T) S₁.phi u v = a • x := by
    rw [(h₁s.c1.eq_v (u, v) hp huv).2.2.2.2.2.1, Fields.phiV]
    exact radial_smul_aux (h₁s.c1.r_pos (u, v) hp huv).ne'
      (h₁s.c1.lam_pos (u, v) hp).ne' _
  have h₂ : pdV (triangle 0 T) S₂.phi u v = b • y := by
    rw [(h₂s.c1.eq_v (u, v) hp huv).2.2.2.2.2.1, Fields.phiV]
    exact radial_smul_aux (h₂s.c1.r_pos (u, v) hp huv).ne'
      (h₂s.c1.lam_pos (u, v) hp).ne' _
  have ha : 0 ≤ a := div_nonneg (h₁s.c1.lam_pos (u, v) hp).le
    (h₁s.c1.r_pos (u, v) hp huv).le
  have heq : a • x - b • y = a • (x - y) + (a - b) • y := by
    simp only [smul_sub, sub_smul]
    abel
  rw [h₁, h₂, heq]
  calc
    _ ≤ ‖a • (x - y)‖ + ‖(a - b) • y‖ := norm_add_le _ _
    _ = a * ‖x - y‖ + |a - b| * ‖y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ _ := by
      apply add_le_add le_rfl
      simpa only [a, b, y, mul_assoc] using mul_le_mul_of_nonneg_right
        (stab_out_weight_sub_le h₁s h₂s hu huv hvT) (norm_nonneg y)

end EmcsfAcExtension.Local
