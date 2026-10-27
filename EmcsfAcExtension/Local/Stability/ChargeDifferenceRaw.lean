module

public import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Stability.ChargeDifferenceAlgebra
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Calculus.C1ToSolution2

/-! # Difference of the common-label Maxwell primitives

The common first radius weights the entire comparison. The measure
`λ₁r₁ dv` has the exact mass `r₁²/2`; no solution-dependent change of
labels is made between the solutions.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem norm_le_supDist_aux {E : Type*} [NormedAddCommGroup E]
    {T : ℝ} {f g : ℝ → ℝ → E}
    (hf : ContinuousOn (Function.uncurry f) (triangle 0 T))
    (hg : ContinuousOn (Function.uncurry g) (triangle 0 T))
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    ‖f u v - g u v‖ ≤ (supDist T f g).toReal := by
  have hh : ENNReal.ofReal ‖f u v - g u v‖ ≤ supDist T f g := by
    rw [ofReal_norm]
    exact le_iSup₂_of_le (u, v) hp le_rfl
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using
    ENNReal.toReal_mono (supDist_ne_top_of_continuousOn hf hg) hh

/-- The charge difference divided by the first radius squared has the
raw bound with universal coefficient `4`, uniformly in all parameters,
the pair and minimum radius. Only finite classical uniform distances
of the scalar field and outgoing ratio occur on the right. -/
theorem stab_charge_difference_raw
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    |S₁.Q u v - S₂.Q u v| / S₁.r u v ^ 2 ≤ 4 * |e| *
      (M * (supDist T (fun u v => S₁.theta u v / (S₁.lam u v : ℂ))
          (fun u v => S₂.theta u v / (S₂.lam u v : ℂ))).toReal +
        ε * (supDist T S₁.phi S₂.phi).toReal + M * ε * (geomDist T S₁ S₂).toReal) := by
  let X := (supDist T (fun u v => S₁.theta u v / (S₁.lam u v : ℂ))
    (fun u v => S₂.theta u v / (S₂.lam u v : ℂ))).toReal
  let Φ := (supDist T S₁.phi S₂.phi).toReal
  let G := (geomDist T S₁ S₂).toReal
  let K := M * X + ε * Φ + 8 * G * M * ε
  let f₁ := fun s => S₁.lam u s * S₁.r u s *
    (starRingEnd ℂ (S₁.phi u s) * (S₁.theta u s / (S₁.lam u s : ℂ))).im
  let f₂ := fun s => S₂.lam u s * S₂.r u s *
    (starRingEnd ℂ (S₂.phi u s) * (S₂.theta u s / (S₂.lam u s : ℂ))).im
  have hM : 0 ≤ M := le_trans (by norm_num) h₁s.box.1
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi u u / (S₂.nu u u : ℂ)))).trans
      (h₂s.box.2 (u, u) ⟨hu, le_rfl, huv.le.trans hvT⟩).2.2.2.2.2.1)
  have hX : 0 ≤ X := ENNReal.toReal_nonneg
  have hΦ : 0 ≤ Φ := ENNReal.toReal_nonneg
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩
  have hseg : outSeg u u v ⊆ triangle 0 T := by
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
  have cF₁ : ContinuousOn f₁ (Icc u v) := (cL₁.mul cR₁).mul
    (Complex.continuous_im.comp_continuousOn (cP₁.star.mul cY₁))
  have cF₂ : ContinuousOn f₂ (Icc u v) := (cL₂.mul cR₂).mul
    (Complex.continuous_im.comp_continuousOn (cP₂.star.mul cY₂))
  have iF₁ := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le cF₁
  have iF₂ := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le cF₂
  have hpbound : ∀ s ∈ Icc u v, ‖f₁ s - f₂ s‖ ≤ S₁.lam u s * S₁.r u s * K := by
    intro s hs
    have hp := hmap hs
    rcases eq_or_lt_of_le hs.1 with hus | hus
    · subst s
      simp only [f₁, f₂, (h₁s.c1.axis u hp).1, (h₂s.c1.axis u hp).1,
        mul_zero, zero_mul, sub_self, norm_zero, le_refl]
    · have hr := h₁s.c1.r_pos (u, s) hp hus
      have hg := stab_geom_sum_le h₁s h₂s hp
      have hrr0 : 0 ≤ |S₁.r u s - S₂.r u s| / S₁.r u s :=
        div_nonneg (abs_nonneg _) hr.le
      have hLam : |S₁.lam u s - S₂.lam u s| ≤ G := by
        linarith only [hg, hrr0, abs_nonneg (S₁.nu u s - S₂.nu u s)]
      have hRad : |S₁.r u s - S₂.r u s| / S₁.r u s ≤ G := by
        linarith only [hg, abs_nonneg (S₁.lam u s - S₂.lam u s),
          abs_nonneg (S₁.nu u s - S₂.nu u s)]
      have harea := stab_area_weight_sub_le (h₁s.box.2 (u, s) hp).1
        (h₂s.c1.lam_pos (u, s) hp).le (h₂s.box.2 (u, s) hp).2.1 hr hLam hRad
      rw [Real.norm_eq_abs]
      exact stab_charge_density_sub_le (mul_nonneg (h₁s.c1.lam_pos (u, s) hp).le hr.le)
        (h₁s.box.2 (u, s) hp).2.2.2.2.2.2 (h₂s.box.2 (u, s) hp).2.2.2.2.2.2
        ((le_add_of_nonneg_right (norm_nonneg (S₂.xi u s / (S₂.nu u s : ℂ)))).trans
          (h₂s.box.2 (u, s) hp).2.2.2.2.2.1)
        (norm_le_supDist_aux
          (f := fun u v => S₁.theta u v / (S₁.lam u v : ℂ))
          (g := fun u v => S₂.theta u v / (S₂.lam u v : ℂ))
          (by simpa only using! cX₁) (by simpa only using! cX₂) hp)
        (norm_le_supDist_aux h₁s.c1.c1_phi.continuousOn h₂s.c1.c1_phi.continuousOn hp) harea
  have ib : IntervalIntegrable (fun s => S₁.lam u s * S₁.r u s * K) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le
      ((cL₁.mul cR₁).mul continuousOn_const)
  have hi := (intervalIntegral.norm_integral_le_integral_norm
    (f := fun s => f₁ s - f₂ s) huv.le).trans
    (intervalIntegral.integral_mono_on huv.le (iF₁.sub iF₂).norm ib hpbound)
  have hm := outgoing_radius_moment hS₁ huv.le hseg 1
  simp only [pow_one, Nat.cast_one, one_add_one_eq_two] at hm
  rw [intervalIntegral.integral_mul_const, hm] at hi
  have hcharge : |S₁.Q u v - S₂.Q u v| ≤ |e| * (S₁.r u v ^ 2 / 2 * K) := by
    rw [Stab.oscillatory_charge_constraint hS₁ huv.le hseg,
      Stab.oscillatory_charge_constraint hS₂ huv.le hseg,
      ← mul_sub, ← intervalIntegral.integral_sub iF₁ iF₂, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using! hi) (abs_nonneg e)
  have hr := h₁s.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv
  rw [div_le_iff₀ (sq_pos_of_pos hr)]
  have hK : K ≤ 8 * (M * X + ε * Φ + M * ε * G) := by
    dsimp only [K]
    nlinarith only [mul_nonneg hM hX, mul_nonneg hε hΦ]
  have hmult := mul_le_mul_of_nonneg_left hK (show 0 ≤ |e| * S₁.r u v ^ 2 / 2 by positivity)
  nlinarith only [hcharge, hmult]

end EmcsfAcExtension.Local
