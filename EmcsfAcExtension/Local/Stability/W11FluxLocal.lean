module

public import EmcsfAcExtension.Local.Stability.W11LocalOut
public import EmcsfAcExtension.Local.Stability.W11LocalIn
import EmcsfAcExtension.Local.Stability.MomentsQuadratic

/-! # Local quadratic flux budgets

The shortened Hardy estimates retain the actual envelope interval.
Multiplication by the small ratio bounds yields the local estimates at
charged_SF_new_version.tex:L5594–5599, in both characteristic orientations.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem quadratic_local_integral_aux {I : Set ℝ} {W y : ℝ → ℝ} {ε : ℝ}
    (hI : MeasurableSet I) (hε : 0 ≤ ε)
    (hW : ∀ s ∈ I, 0 ≤ W s) (hy : ∀ s ∈ I, 0 ≤ y s ∧ y s ≤ ε) :
    (∫⁻ s in I, ENNReal.ofReal (W s * y s ^ 2)) ≤
      ENNReal.ofReal ε * ∫⁻ s in I, ENNReal.ofReal (W s * y s) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' hI
  intro s hs
  rw [← ENNReal.ofReal_mul hε]
  apply ENNReal.ofReal_le_ofReal
  have hb := mul_le_mul_of_nonneg_right (hy s hs).2 (hy s hs).1
  calc
    _ ≤ W s * (ε * y s) := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left hb (hW s hs)
    _ = _ := by ring


/-- Local quadratic outgoing flux bound from its matching envelope.
The literal coefficient `16/3` is universal; `ε` is displayed, with
no dependence on a minimum radius or initial derivative supremum.
This is the local quantitative part of the quadratic nonconcentration node. -/
theorem Stab.quadratic_flux_out_local_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) (hε : ε ^ 2 ≤ 1 / 4)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (∫⁻ s in Icc u v, ENNReal.ofReal (S.lam u s / S.r u s * ‖S.theta u s / (S.lam u s : ℂ)‖ ^ 2)) ≤
      ENNReal.ofReal ((16 / 3) * ε) * ∫⁻ s in Icc u v, outEnv 0 (jC1 (triangle 0 T) S) s := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S.xi u u / (S.nu u u : ℂ)))).trans
      (hset.box.2 (u, u) ⟨hu, le_rfl, huv.trans hvT⟩).2.2.2.2.2.1)
  have hq := quadratic_local_integral_aux (I := Icc u v)
    (W := fun s => S.lam u s / S.r u s) (y := fun s => ‖S.theta u s / (S.lam u s : ℂ)‖)
    measurableSet_Icc hε0 (by
      intro s hs
      have hp : (u, s) ∈ triangle 0 T := ⟨hu, hs.1, hs.2.trans hvT⟩
      rcases hs.1.eq_or_lt with heq | hus
      · subst s
        rw [(hset.c1.axis _ hp).1, div_zero]
      · exact div_nonneg (hset.c1.lam_pos _ hp).le (hset.c1.r_pos _ hp hus).le)
    (fun s hs => ⟨norm_nonneg _,
      (le_add_of_nonneg_right (norm_nonneg (S.xi u s / (S.nu u s : ℂ)))).trans
        (hset.box.2 (u, s) ⟨hu, hs.1, hs.2.trans hvT⟩).2.2.2.2.2.1⟩)
  apply hq.trans
  apply (mul_le_mul' le_rfl (Stab.hardy_out_local_c1 hset hε hu huv hvT)).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul hε0]
  congr 2
  ring

/-- Local quadratic incoming flux bound from its matching envelope.
The literal coefficient `16/3` is universal; `ε` is displayed, with
no dependence on a minimum radius or initial derivative supremum.
This is the local quantitative part of the quadratic nonconcentration node. -/
theorem Stab.quadratic_flux_in_local_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) (hε : ε ^ 2 ≤ 1 / 4)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (∫⁻ s in Icc u v, ENNReal.ofReal (-S.nu s v / S.r s v * ‖S.xi s v / (S.nu s v : ℂ)‖ ^ 2)) ≤
      ENNReal.ofReal ((16 / 3) * ε) * ∫⁻ s in Icc u v, inEnv T (kC1 e (triangle 0 T) S) s := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S.xi u u / (S.nu u u : ℂ)))).trans
      (hset.box.2 (u, u) ⟨hu, le_rfl, huv.trans hvT⟩).2.2.2.2.2.1)
  have hq := quadratic_local_integral_aux (I := Icc u v)
    (W := fun s => -S.nu s v / S.r s v) (y := fun s => ‖S.xi s v / (S.nu s v : ℂ)‖)
    measurableSet_Icc hε0 (by
      intro s hs
      have hp : (s, v) ∈ triangle 0 T := ⟨hu.trans hs.1, hs.2, hvT⟩
      rcases hs.2.eq_or_lt with heq | hsv
      · subst v
        rw [(hset.c1.axis _ hp).1, div_zero]
      · exact div_nonneg (neg_pos.mpr (hset.c1.nu_neg _ hp)).le (hset.c1.r_pos _ hp hsv).le)
    (fun s hs => ⟨norm_nonneg _,
      (le_add_of_nonneg_left (norm_nonneg (S.theta s v / (S.lam s v : ℂ)))).trans
        (hset.box.2 (s, v) ⟨hu.trans hs.1, hs.2, hvT⟩).2.2.2.2.2.1⟩)
  apply hq.trans
  apply (mul_le_mul' le_rfl (Stab.hardy_in_local_c1 hset hε hu huv hvT)).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul hε0]
  congr 2
  ring

end EmcsfAcExtension.Local
