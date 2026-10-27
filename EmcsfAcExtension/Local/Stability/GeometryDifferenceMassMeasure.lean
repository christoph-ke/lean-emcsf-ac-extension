module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassBudgets
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassAlgebra
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Stability.ChargeDifferenceIndividual

/-! # Electromagnetic radial mass budgets

Normalized charge bounds are multiplied by the exact outgoing area
primitive. No singular integral is inferred from a uniform estimate.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- An individual electromagnetic source in a comparison radial
measure costs at most `8 K² T²`, where `K = |e|Mε`. The coefficient
`8` is universal and the displayed length dependence is retained. -/
theorem stab_out_mixed_em_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    (∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t *
      (S₂.Q u t ^ 2 / S₂.r u t ^ 2))) ≤
        ENNReal.ofReal (8 * (|e| * M * ε) ^ 2 * T ^ 2) := by
  let K := |e| * M * ε
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hi : (∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t *
      (S₂.Q u t ^ 2 / S₂.r u t ^ 2))) ≤
      ENNReal.ofReal (16 * K ^ 2) *
        ∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t * S₁.r u t ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    rcases ht.1.eq_or_lt with rfl | hut
    · simp only [(h₁s.c1.axis u ⟨hu, le_rfl, huT⟩).1, div_zero, zero_mul,
        ENNReal.ofReal_zero, mul_zero]
      exact le_rfl
    · have hp : (u, t) ∈ triangle 0 T := ⟨hu, hut.le, ht.2⟩
      have hr₁ := h₁s.c1.r_pos (u, t) hp hut
      have hr₂ := h₂s.c1.r_pos (u, t) hp hut
      have hq := (div_le_iff₀ (sq_pos_of_pos hr₂)).mp
        (stab_charge_ratio_le h₂s hu hut ht.2)
      have hqr : |S₂.Q u t / S₂.r u t| ≤ K * S₂.r u t := by
        rw [abs_div, abs_of_pos hr₂, div_le_iff₀ hr₂]
        dsimp only [K]
        nlinarith only [hq]
      have hcomp := (stab_radius_compare h₁s h₂s hu hut.le ht.2).2
      have hqsmall : |S₂.Q u t / S₂.r u t| ≤ K * (4 * S₁.r u t) :=
        hqr.trans (mul_le_mul_of_nonneg_left hcomp hK)
      have hsquare := pow_le_pow_left₀ (abs_nonneg _) hqsmall 2
      rw [sq_abs, div_pow] at hsquare
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * K ^ 2)]
      apply ENNReal.ofReal_le_ofReal
      have hb := div_nonneg (h₁s.c1.lam_pos (u, t) hp).le hr₁.le
      have hh := mul_le_mul_of_nonneg_left hsquare hb
      nlinarith only [hh]
  apply hi.trans
  rw [stab_out_weight_radius_sq_lintegral h₁s hu huT le_rfl,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * K ^ 2)]
  apply ENNReal.ofReal_le_ofReal
  have hr := stab_radius_bounds h₁s hu huT le_rfl
  have hr0 : 0 ≤ S₁.r u T := by linarith only [hr.1, huT]
  have hrT : S₁.r u T ≤ T := by linarith only [hr.2, hu]
  have hs := pow_le_pow_left₀ hr0 hrT 2
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg K)
  dsimp only [K] at hh ⊢
  nlinarith only [hh]

/-- The absolute electromagnetic square difference has the universal
area cost `10 K T² (D+KG)`. The normalized charge-difference bound `D`
is a displayed premise of this conditional analytic helper. -/
theorem stab_out_em_difference_le_of_charge_bound
    {e T ε M A D : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hD : 0 ≤ D)
    (hcharge : ∀ u t, 0 ≤ u → u < t → t ≤ T →
      |S₁.Q u t - S₂.Q u t| / S₁.r u t ^ 2 ≤ D)
    {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    (∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t *
      |S₁.Q u t ^ 2 / S₁.r u t ^ 2 - S₂.Q u t ^ 2 / S₂.r u t ^ 2|)) ≤
      ENNReal.ofReal (10 * (|e| * M * ε) * T ^ 2 *
        (D + (|e| * M * ε) * (geomDist T S₁ S₂).toReal)) := by
  let K := |e| * M * ε
  let G := (geomDist T S₁ S₂).toReal
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hG : 0 ≤ G := ENNReal.toReal_nonneg
  have hB : 0 ≤ 20 * K * (D + K * G) := by positivity
  have hi : (∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t *
      |S₁.Q u t ^ 2 / S₁.r u t ^ 2 - S₂.Q u t ^ 2 / S₂.r u t ^ 2|)) ≤
      ENNReal.ofReal (20 * K * (D + K * G)) *
        ∫⁻ t in Icc u T, ENNReal.ofReal (S₁.lam u t / S₁.r u t * S₁.r u t ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    rcases ht.1.eq_or_lt with rfl | hut
    · simp only [(h₁s.c1.axis u ⟨hu, le_rfl, huT⟩).1, div_zero, zero_mul,
        ENNReal.ofReal_zero, mul_zero]
      exact le_rfl
    · have hp : (u, t) ∈ triangle 0 T := ⟨hu, hut.le, ht.2⟩
      have hr₁ := h₁s.c1.r_pos (u, t) hp hut
      have hr₂ := h₂s.c1.r_pos (u, t) hp hut
      have hgeom := stab_geom_sum_le h₁s h₂s hp
      have hrad : |S₁.r u t - S₂.r u t| ≤ G * S₁.r u t := by
        apply (div_le_iff₀ hr₁).mp
        dsimp only [G]
        linarith only [hgeom, abs_nonneg (S₁.lam u t - S₂.lam u t),
          abs_nonneg (S₁.nu u t - S₂.nu u t)]
      have hsquare := stab_charge_square_sub_le hr₁ hr₂ hK hD hG
        (stab_radius_compare h₁s h₂s hu hut.le ht.2).2
        ((div_le_iff₀ (sq_pos_of_pos hr₁)).mp (stab_charge_ratio_le h₁s hu hut ht.2))
        ((div_le_iff₀ (sq_pos_of_pos hr₂)).mp (stab_charge_ratio_le h₂s hu hut ht.2))
        ((div_le_iff₀ (sq_pos_of_pos hr₁)).mp (hcharge u t hu hut ht.2)) hrad
      rw [← ENNReal.ofReal_mul hB]
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left hsquare
        (div_nonneg (h₁s.c1.lam_pos (u, t) hp).le hr₁.le)
      nlinarith only [hh]
  apply hi.trans
  rw [stab_out_weight_radius_sq_lintegral h₁s hu huT le_rfl, ← ENNReal.ofReal_mul hB]
  apply ENNReal.ofReal_le_ofReal
  have hr := stab_radius_bounds h₁s hu huT le_rfl
  have hr0 : 0 ≤ S₁.r u T := by linarith only [hr.1, huT]
  have hrT : S₁.r u T ≤ T := by linarith only [hr.2, hu]
  have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrT 2) hB
  dsimp only [K, G] at hs ⊢
  nlinarith only [hs]

end EmcsfAcExtension.Local
