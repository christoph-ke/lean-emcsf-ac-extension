module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceInitialGauge
import EmcsfAcExtension.Local.Stability.FieldDifferenceInitial
import EmcsfAcExtension.Local.Calculus.Reconstruction

/-! # Initial scalar averaging and comparison

The shared radius gauge gives the exact initial average. Its difference
is bounded by the literal datum distance, without a global geometric
distance or an initial derivative supremum.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- The initial scalar obeys the exact radial average, including its
zero-radius integral identity. There is no estimate constant or
smallness premise. -/
theorem stab_initial_scalar_average
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {v : ℝ} (hv : v ∈ Icc 0 T) :
    (v : ℂ) * S.phi 0 v = ∫ s in 0..v, h s := by
  have hr := Area.outgoing_radial_reconstruction hset.c1 le_rfl hv.1 hv.2
  have hi : (∫ s in 0..v, (S.lam 0 s : ℂ) * S.a 0 s) =
      (1 / 2 : ℂ) * ∫ s in 0..v, h s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc 0 T := by
      have hsc : s ∈ Icc 0 v := by simpa only [uIcc_of_le hv.1] using hs
      exact ⟨hsc.1, hsc.2.trans hv.2⟩
    change (S.lam 0 s : ℂ) * S.a 0 s = (1 / 2 : ℂ) * h s
    rw [stab_initial_lam hset hs', (hset.data.1 s hs').2]
    norm_num
  rw [hi, (hset.data.1 v hv).1] at hr
  push_cast at hr
  linear_combination 2 * hr

/-- The scalar difference on the initial cone is bounded by
`dataDist`, with universal coefficient `1`. No global geometric
comparison or scalar difference conclusion is assumed. -/
theorem stab_initial_scalar_difference_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {v : ℝ} (hv : v ∈ Icc 0 T) :
    ‖S₁.phi 0 v - S₂.phi 0 v‖ ≤ dataDist h₁ h₂ T := by
  rcases hv.1.eq_or_lt with rfl | hv0
  · have hp : (0, 0) ∈ triangle (0 : ℝ) T := ⟨le_rfl, le_rfl, h₁s.pos.le⟩
    have hφ₁ : S₁.phi 0 0 = h₁ 0 :=
      ((h₁s.c1.axis 0 hp).2.2.2.2.1).symm.trans (h₁s.data.1 0 hv).2
    have hφ₂ : S₂.phi 0 0 = h₂ 0 :=
      ((h₂s.c1.axis 0 hp).2.2.2.2.1).symm.trans (h₂s.data.1 0 hv).2
    rw [hφ₁, hφ₂]
    exact stab_initial_data_difference_le h₁s h₂s hv
  · have hi₁ : IntervalIntegrable h₁ volume 0 v :=
      (((stab_initial_datum_ac h₁s).mono (by
        rw [uIcc_of_le hv.1, uIcc_of_le h₁s.pos.le]
        exact Icc_subset_Icc_right hv.2)).continuousOn).intervalIntegrable
    have hi₂ : IntervalIntegrable h₂ volume 0 v :=
      (((stab_initial_datum_ac h₂s).mono (by
        rw [uIcc_of_le hv.1, uIcc_of_le h₂s.pos.le]
        exact Icc_subset_Icc_right hv.2)).continuousOn).intervalIntegrable
    have heq : (v : ℂ) * (S₁.phi 0 v - S₂.phi 0 v) =
        ∫ s in 0..v, h₁ s - h₂ s := by
      rw [mul_sub, stab_initial_scalar_average h₁s hv,
        stab_initial_scalar_average h₂s hv, intervalIntegral.integral_sub hi₁ hi₂]
    have hnorm : ‖(v : ℂ) * (S₁.phi 0 v - S₂.phi 0 v)‖ ≤
        dataDist h₁ h₂ T * |v - 0| := by
      rw [heq]
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [uIoc_of_le hv.1] at hs
      exact stab_initial_data_difference_le h₁s h₂s ⟨hs.1.le, hs.2.trans hv.2⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, sub_zero,
      abs_of_pos hv0] at hnorm
    exact (mul_le_mul_iff_right₀ hv0).mp (by simpa only [mul_comm] using hnorm)

end EmcsfAcExtension.Local
