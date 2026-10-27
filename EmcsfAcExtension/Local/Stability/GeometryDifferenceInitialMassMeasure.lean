module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassAlgebra
import EmcsfAcExtension.Local.Stability.GeometryDifferenceMassBudgets
import EmcsfAcExtension.Local.Stability.GeometryDifferenceAux
import EmcsfAcExtension.Local.Stability.ChargeDifferenceIndividual

/-! # Electromagnetic initial mass comparison

The common initial radius eliminates the radius-difference term in
subtracting the electromagnetic square. The area primitive retains
the explicit initial length squared.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The initial electromagnetic mass source costs `10 K T² D`, with
`K=|e|Mε` and a displayed initial normalized charge bound `D`.
The numerical coefficient is universal, and the common radius removes
all global geometric errors from this conditional helper. -/
theorem stab_initial_em_le_of_charge_bound
    {e T ε M A D : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂) (hD : 0 ≤ D)
    (hcharge : ∀ t, 0 < t → t ≤ T → |S₁.Q 0 t - S₂.Q 0 t| / S₁.r 0 t ^ 2 ≤ D) :
    (∫⁻ t in Icc 0 T, ENNReal.ofReal (S₁.lam 0 t / S₁.r 0 t *
      |S₁.Q 0 t ^ 2 / S₁.r 0 t ^ 2 - S₂.Q 0 t ^ 2 / S₂.r 0 t ^ 2|)) ≤
        ENNReal.ofReal (10 * (|e| * M * ε) * T ^ 2 * D) := by
  have hu : (0 : ℝ) ≤ 0 := le_rfl
  have huT : (0 : ℝ) ≤ T := h₁s.pos.le
  let K := |e| * M * ε
  let G : ℝ := 0
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans h₁s.box.1
  have hε : 0 ≤ ε := (norm_nonneg _).trans
    ((le_add_of_nonneg_right (norm_nonneg (S₂.xi 0 0 / (S₂.nu 0 0 : ℂ)))).trans
      (h₂s.box.2 (0, 0) ⟨le_rfl, le_rfl, h₂s.pos.le⟩).2.2.2.2.2.1)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hG : 0 ≤ G := le_rfl
  have hB : 0 ≤ 20 * K * (D + K * G) := by positivity
  have hi : (∫⁻ t in Icc 0 T, ENNReal.ofReal (S₁.lam 0 t / S₁.r 0 t *
      |S₁.Q 0 t ^ 2 / S₁.r 0 t ^ 2 - S₂.Q 0 t ^ 2 / S₂.r 0 t ^ 2|)) ≤
      ENNReal.ofReal (20 * K * (D + K * G)) *
        ∫⁻ t in Icc 0 T, ENNReal.ofReal (S₁.lam 0 t / S₁.r 0 t * S₁.r 0 t ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    rcases ht.1.eq_or_lt with rfl | hut
    · simp only [(h₁s.c1.axis 0 ⟨hu, le_rfl, huT⟩).1, div_zero, zero_mul,
        ENNReal.ofReal_zero, mul_zero]
      exact le_rfl
    · have hp : (0, t) ∈ triangle 0 T := ⟨hu, hut.le, ht.2⟩
      have hr₁ := h₁s.c1.r_pos (0, t) hp hut
      have hr₂ := h₂s.c1.r_pos (0, t) hp hut
      have hrad : |S₁.r 0 t - S₂.r 0 t| ≤ G * S₁.r 0 t := by
        rw [(h₁s.data.1 t ⟨ht.1, ht.2⟩).1, (h₂s.data.1 t ⟨ht.1, ht.2⟩).1]
        simp only [sub_self, abs_zero, G, zero_mul, le_refl]
      have hsquare := stab_charge_square_sub_le hr₁ hr₂ hK hD hG
        (stab_radius_compare h₁s h₂s hu hut.le ht.2).2
        ((div_le_iff₀ (sq_pos_of_pos hr₁)).mp (stab_charge_ratio_le h₁s hu hut ht.2))
        ((div_le_iff₀ (sq_pos_of_pos hr₂)).mp (stab_charge_ratio_le h₂s hu hut ht.2))
        ((div_le_iff₀ (sq_pos_of_pos hr₁)).mp (hcharge t hut ht.2)) hrad
      rw [← ENNReal.ofReal_mul hB]
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left hsquare
        (div_nonneg (h₁s.c1.lam_pos (0, t) hp).le hr₁.le)
      nlinarith only [hh]
  apply hi.trans
  rw [stab_out_weight_radius_sq_lintegral h₁s hu huT le_rfl, ← ENNReal.ofReal_mul hB]
  apply ENNReal.ofReal_le_ofReal
  have hr := stab_radius_bounds h₁s hu huT le_rfl
  have hr0 : 0 ≤ S₁.r 0 T := by linarith only [hr.1, huT]
  have hrT : S₁.r 0 T ≤ T := by linarith only [hr.2, hu]
  have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrT 2) hB
  dsimp only [K, G] at hs ⊢
  nlinarith only [hs]

end EmcsfAcExtension.Local
