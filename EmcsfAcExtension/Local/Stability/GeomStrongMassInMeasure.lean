module

public import EmcsfAcExtension.Local.Stability.GeomStrongMassInBudget
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassBudgets
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassAlgebra
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Stability.ChargeDifferenceIndividual

/-! # Incoming electromagnetic radial mass budgets

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
theorem stab_in_mixed_em_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {v : ℝ} (hv : 0 ≤ v) (hvT : v ≤ T) :
    (∫⁻ t in Icc 0 v, ENNReal.ofReal ((-S₁.nu t v) / S₁.r t v *
      (S₂.Q t v ^ 2 / S₂.r t v ^ 2))) ≤
        ENNReal.ofReal (8 * (|e| * M * ε) ^ 2 * T ^ 2) := by
  let K := |e| * M * ε
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hi : (∫⁻ t in Icc 0 v, ENNReal.ofReal ((-S₁.nu t v) / S₁.r t v *
      (S₂.Q t v ^ 2 / S₂.r t v ^ 2))) ≤
      ENNReal.ofReal (16 * K ^ 2) *
        ∫⁻ t in Icc 0 v, ENNReal.ofReal ((-S₁.nu t v) / S₁.r t v * S₁.r t v ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    rcases ht.2.eq_or_lt with rfl | htv
    · simp only [(h₁s.c1.axis t ⟨ht.1, le_rfl, hvT⟩).1, div_zero, zero_mul,
        ENNReal.ofReal_zero, mul_zero]
      exact le_rfl
    · have hp : (t, v) ∈ triangle 0 T := ⟨ht.1, htv.le, hvT⟩
      have hr₁ := h₁s.c1.r_pos (t, v) hp htv
      have hr₂ := h₂s.c1.r_pos (t, v) hp htv
      have hq := (div_le_iff₀ (sq_pos_of_pos hr₂)).mp
        (stab_charge_ratio_le h₂s ht.1 htv hvT)
      have hqr : |S₂.Q t v / S₂.r t v| ≤ K * S₂.r t v := by
        rw [abs_div, abs_of_pos hr₂, div_le_iff₀ hr₂]
        dsimp only [K]
        nlinarith only [hq]
      have hcomp := (stab_radius_compare h₁s h₂s ht.1 htv.le hvT).2
      have hqsmall : |S₂.Q t v / S₂.r t v| ≤ K * (4 * S₁.r t v) :=
        hqr.trans (mul_le_mul_of_nonneg_left hcomp hK)
      have hsquare := pow_le_pow_left₀ (abs_nonneg _) hqsmall 2
      rw [sq_abs, div_pow] at hsquare
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * K ^ 2)]
      apply ENNReal.ofReal_le_ofReal
      have hb := div_nonneg (neg_pos.mpr (h₁s.c1.nu_neg (t, v) hp)).le hr₁.le
      have hh := mul_le_mul_of_nonneg_left hsquare hb
      nlinarith only [hh]
  apply hi.trans
  rw [stab_in_weight_radius_sq_lintegral h₁s le_rfl hv hvT,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * K ^ 2)]
  apply ENNReal.ofReal_le_ofReal
  have hr := stab_radius_bounds h₁s le_rfl hv hvT
  have hr0 : 0 ≤ S₁.r 0 v := by linarith only [hr.1, hv]
  have hrT : S₁.r 0 v ≤ T := by linarith only [hr.2, hvT]
  have hs := pow_le_pow_left₀ hr0 hrT 2
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg K)
  dsimp only [K] at hh ⊢
  nlinarith only [hh]

/-- The absolute electromagnetic square difference has the universal
area cost `10 K T² (D+KG)`. The normalized charge-difference bound `D`
is a displayed premise of this conditional analytic helper. -/
theorem stab_in_em_difference_le_of_charge_bound
    {e T ε M A D : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hD : 0 ≤ D)
    (hcharge : ∀ u t, 0 ≤ u → u < t → t ≤ T →
      |S₁.Q u t - S₂.Q u t| / S₁.r u t ^ 2 ≤ D)
    {v : ℝ} (hv : 0 ≤ v) (hvT : v ≤ T) :
    (∫⁻ t in Icc 0 v, ENNReal.ofReal ((-S₁.nu t v) / S₁.r t v *
      |S₁.Q t v ^ 2 / S₁.r t v ^ 2 - S₂.Q t v ^ 2 / S₂.r t v ^ 2|)) ≤
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
  have hi : (∫⁻ t in Icc 0 v, ENNReal.ofReal ((-S₁.nu t v) / S₁.r t v *
      |S₁.Q t v ^ 2 / S₁.r t v ^ 2 - S₂.Q t v ^ 2 / S₂.r t v ^ 2|)) ≤
      ENNReal.ofReal (20 * K * (D + K * G)) *
        ∫⁻ t in Icc 0 v, ENNReal.ofReal ((-S₁.nu t v) / S₁.r t v * S₁.r t v ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    rcases ht.2.eq_or_lt with rfl | htv
    · simp only [(h₁s.c1.axis t ⟨ht.1, le_rfl, hvT⟩).1, div_zero, zero_mul,
        ENNReal.ofReal_zero, mul_zero]
      exact le_rfl
    · have hp : (t, v) ∈ triangle 0 T := ⟨ht.1, htv.le, hvT⟩
      have hr₁ := h₁s.c1.r_pos (t, v) hp htv
      have hr₂ := h₂s.c1.r_pos (t, v) hp htv
      have hgeom := stab_geom_sum_le h₁s h₂s hp
      have hrad : |S₁.r t v - S₂.r t v| ≤ G * S₁.r t v := by
        apply (div_le_iff₀ hr₁).mp
        dsimp only [G]
        linarith only [hgeom, abs_nonneg (S₁.lam t v - S₂.lam t v),
          abs_nonneg (S₁.nu t v - S₂.nu t v)]
      have hsquare := stab_charge_square_sub_le hr₁ hr₂ hK hD hG
        (stab_radius_compare h₁s h₂s ht.1 htv.le hvT).2
        ((div_le_iff₀ (sq_pos_of_pos hr₁)).mp (stab_charge_ratio_le h₁s ht.1 htv hvT))
        ((div_le_iff₀ (sq_pos_of_pos hr₂)).mp (stab_charge_ratio_le h₂s ht.1 htv hvT))
        ((div_le_iff₀ (sq_pos_of_pos hr₁)).mp (hcharge t v ht.1 htv hvT)) hrad
      rw [← ENNReal.ofReal_mul hB]
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left hsquare
        (div_nonneg (neg_pos.mpr (h₁s.c1.nu_neg (t, v) hp)).le hr₁.le)
      nlinarith only [hh]
  apply hi.trans
  rw [stab_in_weight_radius_sq_lintegral h₁s le_rfl hv hvT, ← ENNReal.ofReal_mul hB]
  apply ENNReal.ofReal_le_ofReal
  have hr := stab_radius_bounds h₁s le_rfl hv hvT
  have hr0 : 0 ≤ S₁.r 0 v := by linarith only [hr.1, hv]
  have hrT : S₁.r 0 v ≤ T := by linarith only [hr.2, hvT]
  have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrT 2) hB
  dsimp only [K, G] at hs ⊢
  nlinarith only [hs]

end EmcsfAcExtension.Local
