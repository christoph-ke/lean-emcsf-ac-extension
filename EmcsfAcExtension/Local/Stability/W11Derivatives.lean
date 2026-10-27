module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.W11Algebra
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux

/-! # Pointwise characteristic derivative comparison

Approved internal project record (S3)–(S4). The mass-ratio error and each oriented
radial weight remain explicit before the section integration and
the main Lipschitz estimate are used.
-/

public section

open Set

namespace EmcsfAcExtension.Local

variable {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}

/-- Outgoing characteristic derivative comparison with literal
coefficients `4`, `16`, `3` and `20`. They are universal for the fixed
box, uniformly in every field parameter, background and minimum radius.
No main Lipschitz conclusion is assumed. -/
theorem stab_out_derivative_difference_pointwise
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖pdV (triangle 0 T) S₁.a u v - pdV (triangle 0 T) S₂.a u v‖ ≤
      4 * ‖jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v‖ +
      16 * (supDist T S₁.mu S₂.mu).toReal * ‖jC1 (triangle 0 T) S₂ u v‖ +
      3 * ε ^ 2 * (S₁.lam u v / S₁.r u v *
        ‖S₁.theta u v / (S₁.lam u v : ℂ) - S₂.theta u v / (S₂.lam u v : ℂ)‖) +
      20 * (geomDist T S₁ S₂).toReal * ε ^ 2 *
        (S₁.lam u v / S₁.r u v * ‖S₂.theta u v / (S₂.lam u v : ℂ)‖) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hb₁ := h₁s.box.2 (u, v) hp
  have hb₂ := h₂s.box.2 (u, v) hp
  have hz₁ : ‖S₁.theta u v / (S₁.lam u v : ℂ)‖ ≤ ε :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hb₁.2.2.2.2.2.1
  have hz₂ : ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ≤ ε :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hb₂.2.2.2.2.2.1
  have ha : 0 ≤ S₁.lam u v / S₁.r u v :=
    div_nonneg (h₁s.c1.lam_pos (u, v) hp).le (h₁s.c1.r_pos (u, v) hp huv).le
  have hd₁ := stab_out_derivative_reconstruction (D := triangle 0 T)
    (h₁s.c1.one_sub_mu_pos (u, v) hp).ne'
  have hd₂ := stab_out_derivative_reconstruction (D := triangle 0 T)
    (h₂s.c1.one_sub_mu_pos (u, v) hp).ne'
  have hraw := stab_reconstructed_derivative_sub_le
    hb₁.2.2.2.2.1 hb₂.2.2.2.2.1 ha hz₁ hz₂ hd₁ hd₂
  have hmass := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (stab_mu_sub_le h₁s h₂s hp)
      (by norm_num : (0 : ℝ) ≤ 16)) (norm_nonneg (jC1 (triangle 0 T) S₂ u v))
  have hweight := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (stab_out_weight_sub_le h₁s h₂s hu huv hvT)
      (sq_nonneg ε)) (norm_nonneg (S₂.theta u v / (S₂.lam u v : ℂ)))
  apply hraw.trans
  linarith only [hmass, hweight]

/-- Incoming characteristic derivative comparison in the two own
connections, retaining the positive weight `-ν₁/r₁`. The literal
coefficients are universal and independent of every field parameter,
the scalar background and the minimum radius. -/
theorem stab_in_derivative_difference_pointwise
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖(pdU (triangle 0 T) S₁.b u v + Complex.I * e * S₁.A u v * S₁.b u v) -
      (pdU (triangle 0 T) S₂.b u v + Complex.I * e * S₂.A u v * S₂.b u v)‖ ≤
      4 * ‖kC1 e (triangle 0 T) S₁ u v - kC1 e (triangle 0 T) S₂ u v‖ +
      16 * (supDist T S₁.mu S₂.mu).toReal * ‖kC1 e (triangle 0 T) S₂ u v‖ +
      3 * ε ^ 2 * (-S₁.nu u v / S₁.r u v *
        ‖S₁.xi u v / (S₁.nu u v : ℂ) - S₂.xi u v / (S₂.nu u v : ℂ)‖) +
      20 * (geomDist T S₁ S₂).toReal * ε ^ 2 *
        (-S₁.nu u v / S₁.r u v * ‖S₂.xi u v / (S₂.nu u v : ℂ)‖) := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hb₁ := h₁s.box.2 (u, v) hp
  have hb₂ := h₂s.box.2 (u, v) hp
  have hz₁ : ‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ≤ ε :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans hb₁.2.2.2.2.2.1
  have hz₂ : ‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ≤ ε :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans hb₂.2.2.2.2.2.1
  have ha : 0 ≤ -S₁.nu u v / S₁.r u v :=
    div_nonneg (neg_pos.mpr (h₁s.c1.nu_neg (u, v) hp)).le
      (h₁s.c1.r_pos (u, v) hp huv).le
  have hd₁ : -(pdU (triangle 0 T) S₁.b u v + Complex.I * e * S₁.A u v * S₁.b u v) =
      -kC1 e (triangle 0 T) S₁ u v / ((1 - S₁.mu u v : ℝ) : ℂ) +
      (-S₁.nu u v / S₁.r u v) •
        (‖S₁.xi u v / (S₁.nu u v : ℂ)‖ ^ 2 • (S₁.xi u v / (S₁.nu u v : ℂ))) := by
    rw [stab_in_derivative_reconstruction (h₁s.c1.one_sub_mu_pos (u, v) hp).ne']
    simp only [neg_div, neg_smul, neg_add_rev]
    abel
  have hd₂ : -(pdU (triangle 0 T) S₂.b u v + Complex.I * e * S₂.A u v * S₂.b u v) =
      -kC1 e (triangle 0 T) S₂ u v / ((1 - S₂.mu u v : ℝ) : ℂ) +
      (-S₂.nu u v / S₂.r u v) •
        (‖S₂.xi u v / (S₂.nu u v : ℂ)‖ ^ 2 • (S₂.xi u v / (S₂.nu u v : ℂ))) := by
    rw [stab_in_derivative_reconstruction (h₂s.c1.one_sub_mu_pos (u, v) hp).ne']
    simp only [neg_div, neg_smul, neg_add_rev]
    abel
  have hraw := stab_reconstructed_derivative_sub_le
    hb₁.2.2.2.2.1 hb₂.2.2.2.2.1 ha hz₁ hz₂ hd₁ hd₂
  simp only [neg_sub_neg, norm_sub_rev, norm_neg] at hraw
  have hmass := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (stab_mu_sub_le h₁s h₂s hp)
      (by norm_num : (0 : ℝ) ≤ 16)) (norm_nonneg (kC1 e (triangle 0 T) S₂ u v))
  have hweight := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (stab_in_weight_sub_le h₁s h₂s hu huv hvT)
      (sq_nonneg ε)) (norm_nonneg (S₂.xi u v / (S₂.nu u v : ℂ)))
  apply hraw.trans
  linarith only [hmass, hweight]

end EmcsfAcExtension.Local
