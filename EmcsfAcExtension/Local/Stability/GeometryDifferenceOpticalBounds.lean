module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceOptical
import EmcsfAcExtension.Local.Stability.GeometryDifferenceConeOptical
import EmcsfAcExtension.Local.Stability.GeometryDifferenceOpticalAlgebra
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassSign
import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # Pointwise ordered optical comparisons

The incoming comparison starts on the initial cone. The outgoing
comparison then uses the resulting axis expansion comparison. Only
the literal fixed-box constants occur in these raw estimates.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- The outgoing optical exponential is at most `16` in the literal
fixed box. This numerical bound follows from the exact optical identity
and requires no smallness or derivative supremum. -/
theorem stab_out_optical_exp_le_sixteen
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    Real.exp (∫ s in u..v, S.lam u s / S.r u s *
      ‖S.theta u s / (S.lam u s : ℂ)‖ ^ 2) ≤ 16 := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv, hvT⟩
  have ha : (u, u) ∈ triangle 0 T := ⟨hu, le_rfl, huv.trans hvT⟩
  have hg := hset.c1.one_sub_mu_pos (u, v) hp
  have ho := stab_out_optical_from_axis hset hu huv hvT
  have hb : -S.nu u v / (1 - S.mu u v) ≤ 4 := by
    rw [div_le_iff₀ hg]
    linarith only [(hset.box.2 (u, v) hp).2.2.2.1, (hset.box.2 (u, v) hp).2.2.2.2.1]
  have hm := mul_le_mul_of_nonneg_right (hset.box.2 (u, u) ha).1
    (Real.exp_pos (∫ s in u..v, S.lam u s / S.r u s *
      ‖S.theta u s / (S.lam u s : ℂ)‖ ^ 2)).le
  nlinarith only [ho, hb, hm]

private theorem optical_product_aux {l γ L E : ℝ} (hγ : γ ≠ 0)
    (h : l / γ = L * E) : l = γ * L * E := by
  have hh := (div_eq_iff hγ).mp h
  nlinarith only [hh]

private theorem gap_abs_aux
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) : |1 - S.mu u v| ≤ 1 := by
  rw [abs_of_pos (hset.c1.one_sub_mu_pos (u, v) ⟨hu, huv, hvT⟩)]
  linarith only [stab_mu_nonneg hset hu huv hvT]

private theorem initial_opt_abs_aux
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {v : ℝ} (hv : v ∈ Icc 0 T) :
    |S.lam 0 v / (1 - S.mu 0 v)| ≤ 4 := by
  have hp : (0, v) ∈ triangle (0 : ℝ) T := ⟨le_rfl, hv.1, hv.2⟩
  have hg := hset.c1.one_sub_mu_pos (0, v) hp
  rw [abs_of_pos (div_pos (hset.c1.lam_pos (0, v) hp) hg), div_le_iff₀ hg]
  linarith only [(hset.box.2 (0, v) hp).2.1, (hset.box.2 (0, v) hp).2.2.2.2.1]

private theorem gap_difference_abs_aux {a b : ℝ} : |(1 - a) - (1 - b)| = |a - b| := by
  rw [show (1 - a) - (1 - b) = -(a - b) by ring, abs_neg]

/-- The outgoing expansion comparison obtained by first integrating
the incoming optical equation from the initial cone. The coefficients
`4,1,4` are universal; the unequal initial mass term remains explicit. -/
theorem stab_lam_sub_le_of_optical_integrals
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    |S₁.lam u v - S₂.lam u v| ≤ 4 * |S₁.mu u v - S₂.mu u v| +
      |S₁.lam 0 v / (1 - S₁.mu 0 v) - S₂.lam 0 v / (1 - S₂.mu 0 v)| +
      4 * |(∫ s in 0..u, -S₁.nu s v / S₁.r s v * ‖S₁.xi s v / (S₁.nu s v : ℂ)‖ ^ 2) -
        ∫ s in 0..u, -S₂.nu s v / S₂.r s v * ‖S₂.xi s v / (S₂.nu s v : ℂ)‖ ^ 2| := by
  have hI (S : Fields) (h : ℝ → ℂ) (hset : StabSetting e T ε M A S h) :
      0 ≤ ∫ s in 0..u, -S.nu s v / S.r s v * ‖S.xi s v / (S.nu s v : ℂ)‖ ^ 2 := by
    apply intervalIntegral.integral_nonneg hu
    intro s hs
    have hp : (s, v) ∈ triangle 0 T := ⟨hs.1, hs.2.trans huv, hvT⟩
    have hb := (stab_radius_bounds hset hs.1 (hs.2.trans huv) hvT).1
    have hr : 0 ≤ S.r s v := by linarith only [hb, hs.2.trans huv]
    exact mul_nonneg (div_nonneg (neg_nonneg.mpr (hset.c1.nu_neg (s, v) hp).le) hr)
      (sq_nonneg _)
  have hOpt₁ := optical_product_aux
    (h₁s.c1.one_sub_mu_pos (u, v) ⟨hu, huv, hvT⟩).ne'
    (stab_in_optical_from_initial h₁s hu huv hvT)
  have hOpt₂ := optical_product_aux
    (h₂s.c1.one_sub_mu_pos (u, v) ⟨hu, huv, hvT⟩).ne'
    (stab_in_optical_from_initial h₂s hu huv hvT)
  rw [hOpt₁, hOpt₂]
  have hh := stab_lam_product_sub_le (γ₁ := 1 - S₁.mu u v)
    (gap_abs_aux h₂s hu huv hvT)
    (initial_opt_abs_aux h₁s ⟨hu.trans huv, hvT⟩)
    (initial_opt_abs_aux h₂s ⟨hu.trans huv, hvT⟩) (hI S₁ h₁ h₁s) (hI S₂ h₂ h₂s)
  simpa only [gap_difference_abs_aux] using hh

/-- The incoming expansion comparison after the axis expansion is
known. Each raw term has universal coefficient `16`; the optical
exponential bound comes from the fixed box, without smallness. -/
theorem stab_nu_sub_le_of_optical_integrals
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    |S₁.nu u v - S₂.nu u v| ≤ 16 * |S₁.mu u v - S₂.mu u v| +
      16 * |S₁.lam u u - S₂.lam u u| +
      16 * |(∫ s in u..v, S₁.lam u s / S₁.r u s * ‖S₁.theta u s / (S₁.lam u s : ℂ)‖ ^ 2) -
        ∫ s in u..v, S₂.lam u s / S₂.r u s * ‖S₂.theta u s / (S₂.lam u s : ℂ)‖ ^ 2| := by
  have hp : (u, u) ∈ triangle 0 T := ⟨hu, le_rfl, huv.trans hvT⟩
  have hL₁ : |S₁.lam u u| ≤ 1 := by
    rw [abs_of_pos (h₁s.c1.lam_pos (u, u) hp)]
    exact (h₁s.box.2 (u, u) hp).2.1
  have hL₂ : |S₂.lam u u| ≤ 1 := by
    rw [abs_of_pos (h₂s.c1.lam_pos (u, u) hp)]
    exact (h₂s.box.2 (u, u) hp).2.1
  have hOpt₁ := optical_product_aux
    (h₁s.c1.one_sub_mu_pos (u, v) ⟨hu, huv, hvT⟩).ne'
    (stab_out_optical_from_axis h₁s hu huv hvT)
  have hOpt₂ := optical_product_aux
    (h₂s.c1.one_sub_mu_pos (u, v) ⟨hu, huv, hvT⟩).ne'
    (stab_out_optical_from_axis h₂s hu huv hvT)
  have hh := stab_nu_product_sub_le (γ₁ := 1 - S₁.mu u v)
    (gap_abs_aux h₂s hu huv hvT) hL₁ hL₂
    (stab_out_optical_exp_le_sixteen h₁s hu huv hvT)
    (stab_out_optical_exp_le_sixteen h₂s hu huv hvT)
  rw [← hOpt₁, ← hOpt₂, neg_sub_neg, abs_sub_comm, gap_difference_abs_aux] at hh
  exact hh

end EmcsfAcExtension.Local
