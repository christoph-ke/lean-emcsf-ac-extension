module

public import EmcsfAcExtension.Local.Stability.DifferenceMomentsForcing
public import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
public import EmcsfAcExtension.Local.Defs.Renormalized

/-! # Classical field bounds for the unabsorbed outgoing forcing

The finite comparison distances bound the inverse-gap and radial-weight
differences. The individual ratio in the geometric forcing remains
explicit for the subsequent separated-exponent convolution.
-/

public section

open Set
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The unabsorbed outgoing forcing is bounded with the literal
coefficients `4`, `16`, `20`, independently of all parameters and the
minimum radius. The geometric forcing retains the individual ratio;
this helper is not the final difference-moment node. -/
theorem stab_out_difference_forcing_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ≤ 1)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖jC1 (triangle 0 T) S₁ u v / ((1 - S₁.mu u v : ℝ) : ℂ) -
      jC1 (triangle 0 T) S₂ u v / ((1 - S₂.mu u v : ℝ) : ℂ) -
      (S₁.lam u v / S₁.r u v - S₂.lam u v / S₂.r u v) •
        (S₂.theta u v / (S₂.lam u v : ℂ) -
          ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2 •
            (S₂.theta u v / (S₂.lam u v : ℂ)))‖ ≤
      4 * ‖jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v‖ +
      16 * (supDist T S₁.mu S₂.mu).toReal * ‖jC1 (triangle 0 T) S₂ u v‖ +
      20 * (geomDist T S₁ S₂).toReal * (S₁.lam u v / S₁.r u v) *
        ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hb₁ := h₁s.box.2 (u, v) hp
  have hb₂ := h₂s.box.2 (u, v) hp
  have hx : ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ≤ 1 :=
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi u v / (S₂.nu u v : ℂ)))).trans
      hb₂.2.2.2.2.2.1).trans hε
  have hf := stab_radial_difference_forcing_le hb₁.2.2.2.2.1 hb₂.2.2.2.2.1 hx
    (j₁ := jC1 (triangle 0 T) S₁ u v) (j₂ := jC1 (triangle 0 T) S₂ u v)
    (a₁ := S₁.lam u v / S₁.r u v) (a₂ := S₂.lam u v / S₂.r u v)
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (stab_mu_sub_le h₁s h₂s hp) (by norm_num : (0 : ℝ) ≤ 16))
    (norm_nonneg (jC1 (triangle 0 T) S₂ u v))
  have hg := mul_le_mul_of_nonneg_right (stab_out_weight_sub_le h₁s h₂s hu huv hvT)
    (norm_nonneg (S₂.theta u v / (S₂.lam u v : ℂ)))
  exact hf.trans (add_le_add (add_le_add le_rfl hm) hg)

private theorem ofReal_forcing_aux {F D J B X G U : ℝ}
    (hD : 0 ≤ D) (hJ : 0 ≤ J) (hB : 0 ≤ B) (hX : 0 ≤ X) (hG : 0 ≤ G) (hU : 0 ≤ U)
    (hF : F ≤ 4 * D + 16 * U * J + 20 * G * B * X) :
    ENNReal.ofReal F ≤ 4 * ENNReal.ofReal D +
      16 * ENNReal.ofReal U * ENNReal.ofReal J +
      20 * ENNReal.ofReal G * ENNReal.ofReal B * ENNReal.ofReal X := by
  apply (ENNReal.ofReal_le_ofReal hF).trans_eq
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]
  repeat rw [ENNReal.ofReal_mul (by positivity)]
  norm_num

/-- The same unabsorbed forcing with the two label envelopes in place
of pointwise derivatives. Coefficients `4`, `16`, `20` remain universal.
Only the scalar oscillation in the geometric term remains to be convolved. -/
theorem stab_out_difference_forcing_enorm_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hε : ε ≤ 1)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ENNReal.ofReal
      ‖jC1 (triangle 0 T) S₁ u v / ((1 - S₁.mu u v : ℝ) : ℂ) -
        jC1 (triangle 0 T) S₂ u v / ((1 - S₂.mu u v : ℝ) : ℂ) -
        (S₁.lam u v / S₁.r u v - S₂.lam u v / S₂.r u v) •
          (S₂.theta u v / (S₂.lam u v : ℂ) -
            ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ ^ 2 •
              (S₂.theta u v / (S₂.lam u v : ℂ)))‖ ≤
      4 * outEnv 0 (fun u v => jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v) v +
      16 * ENNReal.ofReal (supDist T S₁.mu S₂.mu).toReal *
        outEnv 0 (jC1 (triangle 0 T) S₂) v +
      20 * ENNReal.ofReal (geomDist T S₁ S₂).toReal *
        ENNReal.ofReal (S₁.lam u v / S₁.r u v) *
          ENNReal.ofReal ‖S₂.theta u v / (S₂.lam u v : ℂ)‖ := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hn := ofReal_forcing_aux
    (norm_nonneg (jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v))
    (norm_nonneg (jC1 (triangle 0 T) S₂ u v))
    (div_nonneg (h₁s.c1.lam_pos (u, v) hp).le (h₁s.c1.r_pos (u, v) hp huv).le)
    (norm_nonneg (S₂.theta u v / (S₂.lam u v : ℂ))) ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg (stab_out_difference_forcing_le h₁s h₂s hε hu huv hvT)
  have hD : ENNReal.ofReal ‖jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v‖ ≤
      outEnv 0 (fun u v => jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v) v := by
    rw [ofReal_norm]
    exact enorm_le_normEnvelope
      (fun u v => jC1 (triangle 0 T) S₁ u v - jC1 (triangle 0 T) S₂ u v) ⟨hu, huv.le⟩
  have hJ : ENNReal.ofReal ‖jC1 (triangle 0 T) S₂ u v‖ ≤
      outEnv 0 (jC1 (triangle 0 T) S₂) v := by
    rw [ofReal_norm]
    exact enorm_le_normEnvelope (jC1 (triangle 0 T) S₂) ⟨hu, huv.le⟩
  exact hn.trans (add_le_add (add_le_add (mul_le_mul' le_rfl hD)
    (mul_le_mul' le_rfl hJ)) le_rfl)

end EmcsfAcExtension.Local
