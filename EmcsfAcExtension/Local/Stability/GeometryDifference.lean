module

public import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Stability.GeometryDifferenceOptical
import EmcsfAcExtension.Local.Stability.GeometryDifferenceOpticalComparison
import EmcsfAcExtension.Local.Stability.FluxDifferenceRegularity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Optical control of the mass-ratio difference

These raw comparisons are the optical step (RO) in approved internal project record.
They precede radial absorption, keeping the flux difference explicit.
They do not close the later geometric-distance graph node.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

private theorem gap_from_optical_aux {n l γ I : ℝ}
    (hl : l ≠ 0) (hγ : γ ≠ 0) (hopt : n / γ = l * Real.exp I) :
    γ = n / l * Real.exp (-I) := by
  have heq := (div_eq_iff hγ).mp hopt
  rw [Real.exp_neg, ← div_eq_mul_inv, div_div]
  apply (eq_div_iff (mul_ne_zero hl (Real.exp_ne_zero I))).mpr
  calc
    γ * (l * Real.exp I) = l * Real.exp I * γ := by ring
    _ = n := heq.symm

/-- The outgoing optical identity controls the mass-ratio difference by
`20G` plus `4` times the outgoing quadratic-flux integral difference.
Both constants are universal, independent of all parameters and minimum
radius. This is a raw comparison before coupled radial absorption. -/
theorem stab_out_mass_gap_sub_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    |S₁.mu u v - S₂.mu u v| ≤ 20 * (geomDist T S₁ S₂).toReal +
      4 * |(∫ s in u..v, S₁.lam u s / S₁.r u s *
          ‖S₁.theta u s / (S₁.lam u s : ℂ)‖ ^ 2) -
        (∫ s in u..v, S₂.lam u s / S₂.r u s *
          ‖S₂.theta u s / (S₂.lam u s : ℂ)‖ ^ 2)| := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have haxis : (u, u) ∈ triangle 0 T := ⟨hu, le_rfl, huv.le.trans hvT⟩
  have hb₁ := h₁s.box.2 (u, u) haxis
  have hb₂ := h₂s.box.2 (u, u) haxis
  have hν₂ : |-S₂.nu u v| ≤ 1 := by
    rw [abs_of_pos (neg_pos.mpr (h₂s.c1.nu_neg (u, v) hp))]
    exact (h₂s.box.2 (u, v) hp).2.2.2.1
  have hI₁ : 0 ≤ ∫ s in u..v, S₁.lam u s / S₁.r u s *
      ‖S₁.theta u s / (S₁.lam u s : ℂ)‖ ^ 2 := by
    apply intervalIntegral.integral_nonneg huv.le
    intro s hs
    have hr := (stab_radius_bounds h₁s hu hs.1 (hs.2.trans hvT)).1
    have hr0 : 0 ≤ S₁.r u s := by linarith only [hr, hs.1]
    exact mul_nonneg (div_nonneg (h₁s.c1.lam_pos (u, s)
      ⟨hu, hs.1, hs.2.trans hvT⟩).le hr0) (sq_nonneg _)
  have hI₂ : 0 ≤ ∫ s in u..v, S₂.lam u s / S₂.r u s *
      ‖S₂.theta u s / (S₂.lam u s : ℂ)‖ ^ 2 := by
    apply intervalIntegral.integral_nonneg huv.le
    intro s hs
    have hr := (stab_radius_bounds h₂s hu hs.1 (hs.2.trans hvT)).1
    have hr0 : 0 ≤ S₂.r u s := by linarith only [hr, hs.1]
    exact mul_nonneg (div_nonneg (h₂s.c1.lam_pos (u, s)
      ⟨hu, hs.1, hs.2.trans hvT⟩).le hr0) (sq_nonneg _)
  have hγ₁ := gap_from_optical_aux (h₁s.c1.lam_pos (u, u) haxis).ne'
    (h₁s.c1.one_sub_mu_pos (u, v) hp).ne' (stab_out_optical_from_axis h₁s hu huv.le hvT)
  have hγ₂ := gap_from_optical_aux (h₂s.c1.lam_pos (u, u) haxis).ne'
    (h₂s.c1.one_sub_mu_pos (u, v) hp).ne' (stab_out_optical_from_axis h₂s hu huv.le hvT)
  have hc := stab_gap_sub_le_of_optical hb₁.1 hb₂.1 hν₂ hI₁ hI₂ hγ₁ hγ₂
  have hpoint := stab_geom_sum_le h₁s h₂s hp
  have hdiag := stab_geom_sum_le h₁s h₂s haxis
  have hrad0 := div_nonneg (abs_nonneg (S₁.r u v - S₂.r u v))
    (h₁s.c1.r_pos (u, v) hp huv).le
  have hν : |(-S₁.nu u v) - (-S₂.nu u v)| ≤ (geomDist T S₁ S₂).toReal := by
    simp only [neg_sub_neg, abs_sub_comm]
    linarith only [hpoint, hrad0, abs_nonneg (S₁.lam u v - S₂.lam u v)]
  have hLam : |S₁.lam u u - S₂.lam u u| ≤ (geomDist T S₁ S₂).toReal := by
    rw [(h₁s.c1.axis u haxis).1, (h₂s.c1.axis u haxis).1] at hdiag
    simp only [sub_self, abs_zero, zero_div, add_zero] at hdiag
    linarith only [hdiag, abs_nonneg (S₁.nu u u - S₂.nu u u)]
  have hleft : |(1 - S₁.mu u v) - (1 - S₂.mu u v)| = |S₁.mu u v - S₂.mu u v| := by
    rw [show (1 - S₁.mu u v) - (1 - S₂.mu u v) =
      -(S₁.mu u v - S₂.mu u v) by ring, abs_neg]
  rw [hleft] at hc
  linarith only [hc, hν, hLam]

end EmcsfAcExtension.Local
