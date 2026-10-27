module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceInitialGauge
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Stability.ChargeDifferenceAlgebra
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.C1ToSolution2

/-! # Charge difference in the shared initial geometry

The two area weights agree on the initial cone. The oscillatory
constraint consequently has no geometric comparison remainder.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- The initial normalized charge difference is at most
`|e|(MX+εΦ)` under initial ratio and scalar difference bounds `X,Φ`.
The numerical coefficient `1` is universal and there is no global
geometric error in this conditional source estimate. -/
theorem stab_initial_charge_le_of_field_bounds
    {e T ε M A X Φ : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hX : 0 ≤ X) (hΦ : 0 ≤ Φ)
    (hx : ∀ v ∈ Icc 0 T,
      ‖S₁.theta 0 v / (S₁.lam 0 v : ℂ) - S₂.theta 0 v / (S₂.lam 0 v : ℂ)‖ ≤ X)
    (hphi : ∀ v ∈ Icc 0 T, ‖S₁.phi 0 v - S₂.phi 0 v‖ ≤ Φ)
    {v : ℝ} (hv : 0 < v) (hvT : v ≤ T) :
    |S₁.Q 0 v - S₂.Q 0 v| / S₁.r 0 v ^ 2 ≤ |e| * (M * X + ε * Φ) := by
  have hu : (0 : ℝ) ≤ 0 := le_rfl
  have huv : (0 : ℝ) < v := hv
  let K := M * X + ε * Φ
  let f₁ := fun s => S₁.lam 0 s * S₁.r 0 s *
    (starRingEnd ℂ (S₁.phi 0 s) * (S₁.theta 0 s / (S₁.lam 0 s : ℂ))).im
  let f₂ := fun s => S₂.lam 0 s * S₂.r 0 s *
    (starRingEnd ℂ (S₂.phi 0 s) * (S₂.theta 0 s / (S₂.lam 0 s : ℂ))).im
  have hM : 0 ≤ M := le_trans (by norm_num) h₁s.box.1
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨hu, le_rfl, huv.le.trans hvT⟩).2.2.2.2.2.1)
  have hmap : MapsTo (fun s : ℝ => (0, s)) (Icc 0 v) (triangle 0 T) :=
    fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩
  have hseg : outSeg 0 0 v ⊆ triangle 0 T := by
    rintro ⟨a, b⟩ ⟨rfl, hs⟩
    exact ⟨hu, hs.1, hs.2.trans hvT⟩
  have hS₁ := h₁s.c1.toIsSolution h₁s.pos
  have hS₂ := h₂s.c1.toIsSolution h₂s.pos
  have cX₁ := (stab_out_ratio_c1 h₁s.c1).continuousOn
  have cX₂ := (stab_out_ratio_c1 h₂s.c1).continuousOn
  have cL₁ := h₁s.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cL₂ := h₂s.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cR₁ := h₁s.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cR₂ := h₂s.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cP₁ := h₁s.c1.c1_phi.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cP₂ := h₂s.c1.c1_phi.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hmap
  have cY₁ := cX₁.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have cY₂ := cX₂.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have cF₁ : ContinuousOn f₁ (Icc 0 v) := (cL₁.mul cR₁).mul
    (Complex.continuous_im.comp_continuousOn (cP₁.star.mul cY₁))
  have cF₂ : ContinuousOn f₂ (Icc 0 v) := (cL₂.mul cR₂).mul
    (Complex.continuous_im.comp_continuousOn (cP₂.star.mul cY₂))
  have iF₁ := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le cF₁
  have iF₂ := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le cF₂
  have hpbound : ∀ s ∈ Icc 0 v, ‖f₁ s - f₂ s‖ ≤ S₁.lam 0 s * S₁.r 0 s * K := by
    intro s hs
    have hp := hmap hs
    rcases eq_or_lt_of_le hs.1 with hus | hus
    · subst s
      simp only [f₁, f₂, (h₁s.c1.axis 0 hp).1, (h₂s.c1.axis 0 hp).1,
        mul_zero, zero_mul, sub_self, norm_zero, le_refl]
    · have hr := h₁s.c1.r_pos (0, s) hp hus
      have harea : |S₁.lam 0 s * S₁.r 0 s - S₂.lam 0 s * S₂.r 0 s| ≤
          8 * (0 : ℝ) * (S₁.lam 0 s * S₁.r 0 s) := by
        rw [stab_initial_lam h₁s ⟨hs.1, hs.2.trans hvT⟩,
          stab_initial_lam h₂s ⟨hs.1, hs.2.trans hvT⟩,
          (h₁s.data.1 s ⟨hs.1, hs.2.trans hvT⟩).1,
          (h₂s.data.1 s ⟨hs.1, hs.2.trans hvT⟩).1]
        simp
      rw [Real.norm_eq_abs]
      have hh := stab_charge_density_sub_le (mul_nonneg (h₁s.c1.lam_pos (0, s) hp).le hr.le)
        (h₁s.box.2 (0, s) hp).2.2.2.2.2.2 (h₂s.box.2 (0, s) hp).2.2.2.2.2.2
        ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 s / (S₂.nu 0 s : ℂ)))).trans
          (h₂s.box.2 (0, s) hp).2.2.2.2.2.1)
        (hx s ⟨hs.1, hs.2.trans hvT⟩) (hphi s ⟨hs.1, hs.2.trans hvT⟩) harea
      simpa only [mul_zero, zero_mul, add_zero, K] using! hh
  have ib : IntervalIntegrable (fun s => S₁.lam 0 s * S₁.r 0 s * K) volume 0 v :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le
      ((cL₁.mul cR₁).mul continuousOn_const)
  have hi := (intervalIntegral.norm_integral_le_integral_norm
    (f := fun s => f₁ s - f₂ s) huv.le).trans
    (intervalIntegral.integral_mono_on huv.le (iF₁.sub iF₂).norm ib hpbound)
  have hm := outgoing_radius_moment hS₁ huv.le hseg 1
  simp only [pow_one, Nat.cast_one, one_add_one_eq_two] at hm
  rw [intervalIntegral.integral_mul_const, hm] at hi
  have hcharge : |S₁.Q 0 v - S₂.Q 0 v| ≤ |e| * (S₁.r 0 v ^ 2 / 2 * K) := by
    rw [Stab.oscillatory_charge_constraint hS₁ huv.le hseg,
      Stab.oscillatory_charge_constraint hS₂ huv.le hseg,
      ← mul_sub, ← intervalIntegral.integral_sub iF₁ iF₂, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using! hi) (abs_nonneg e)
  have hr := h₁s.c1.r_pos (0, v) ⟨hu, huv.le, hvT⟩ huv
  rw [div_le_iff₀ (sq_pos_of_pos hr)]
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hpos : 0 ≤ |e| * (S₁.r 0 v ^ 2 / 2 * K) := by positivity
  dsimp only [K] at hcharge hpos
  nlinarith only [hcharge, hpos]

end EmcsfAcExtension.Local
