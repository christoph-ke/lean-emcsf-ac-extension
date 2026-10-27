module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Stability.MainRecords
import EmcsfAcExtension.Local.Stability.AssemblyMoments
import EmcsfAcExtension.Local.Stability.MomentsSections

/-! # Coordinate Hardy weights in the fixed stability box

The inverse-cube area kernel leaves `1/(v-u)`. The lower expansion bounds
and upper radius bound compare that weight with either geometric Hardy
weight, uniformly down to the axis.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

private theorem coordinate_weight_le {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    1 / (v - u) ≤ 4 * S.lam u v / S.r u v ∧
      1 / (v - u) ≤ 4 * (-S.nu u v) / S.r u v := by
  rcases hp.2.1.eq_or_lt with heq | hlt
  · change u = v at heq
    subst v
    have hr := (hset.c1.axis u hp).1
    rw [sub_self, hr]
    norm_num
  · have hd : 0 < v - u := sub_pos.mpr hlt
    have hr := hset.c1.r_pos (u, v) hp hlt
    have hrb := (stab_radius_bounds hset hp.1 hp.2.1 hp.2.2).2
    have hl := mul_le_mul_of_nonneg_right (hset.box.2 (u, v) hp).1 hd.le
    have hn := mul_le_mul_of_nonneg_right (hset.box.2 (u, v) hp).2.2.1 hd.le
    constructor <;> apply (div_le_div_iff₀ hd hr).2 <;> linarith only [hrb, hl, hn]

/-- Coordinate incoming Hardy weight from the geometric incoming weight.
The coefficient is exactly `4`, independent of every setting parameter
and of the nonnegative function, without a measurability hypothesis. -/
theorem coordinate_in_hardy_le {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {v : ℝ} (hv : v ∈ Icc 0 T)
    (F : ℝ → ℝ≥0∞) :
    (∫⁻ u in Icc 0 v, ENNReal.ofReal (1 / (v - u)) * F u) ≤
      ENNReal.ofReal 4 * ∫⁻ u in Icc 0 v,
        ENNReal.ofReal (-S.nu u v / S.r u v) * F u := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro u hu
  have hb := ENNReal.ofReal_le_ofReal (coordinate_weight_le hset ⟨hu.1, hu.2, hv.2⟩).2
  have heq : 4 * (-S.nu u v) / S.r u v = 4 * (-S.nu u v / S.r u v) := by ring
  rw [heq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)] at hb
  exact (mul_le_mul' hb le_rfl).trans_eq (mul_assoc _ _ _)

/-- Coordinate outgoing Hardy weight from the geometric outgoing weight.
The coefficient is exactly `4`, uniformly down to the axis and in all
setting parameters and nonnegative inputs. -/
theorem coordinate_out_hardy_le {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u : ℝ} (hu : u ∈ Icc 0 T)
    (F : ℝ → ℝ≥0∞) :
    (∫⁻ v in Icc u T, ENNReal.ofReal (1 / (v - u)) * F v) ≤
      ENNReal.ofReal 4 * ∫⁻ v in Icc u T,
        ENNReal.ofReal (S.lam u v / S.r u v) * F v := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro v hv
  have hb := ENNReal.ofReal_le_ofReal (coordinate_weight_le hset ⟨hu.1, hv.1, hv.2⟩).1
  have heq : 4 * S.lam u v / S.r u v = 4 * (S.lam u v / S.r u v) := by ring
  rw [heq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)] at hb
  exact (mul_le_mul' hb le_rfl).trans_eq (mul_assoc _ _ _)

/-- Incoming coordinate Hardy norm comparison, with exact universal factor
`4`. The complex function and every setting parameter are arbitrary. -/
theorem coordinate_in_norm_hardy_le {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {v : ℝ} (hv : v ∈ Icc 0 T) (f : ℝ → ℂ) :
    (∫⁻ u in Icc 0 v, ENNReal.ofReal (1 / (v - u)) * ‖f u‖ₑ) ≤
      ENNReal.ofReal 4 * ∫⁻ u in Icc 0 v,
        ENNReal.ofReal (-S.nu u v / S.r u v * ‖f u‖) := by
  apply (coordinate_in_hardy_le hset hv (fun u => ‖f u‖ₑ)).trans_eq
  congr 1
  apply setLIntegral_congr_fun measurableSet_Icc
  intro u hu
  have hr : 0 ≤ S.r u v :=
    (div_nonneg (sub_nonneg.mpr hu.2) (by norm_num : (0 : ℝ) ≤ 4)).trans
      (stab_radius_bounds hset hu.1 hu.2 hv.2).1
  have hw := div_nonneg (neg_pos.mpr (hset.c1.nu_neg (u, v) ⟨hu.1, hu.2, hv.2⟩)).le hr
  dsimp only
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hw]

/-- Outgoing coordinate Hardy norm comparison, with exact universal factor
`4`, independent of the complex function and all setting parameters. -/
theorem coordinate_out_norm_hardy_le {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u : ℝ} (hu : u ∈ Icc 0 T) (f : ℝ → ℂ) :
    (∫⁻ v in Icc u T, ENNReal.ofReal (1 / (v - u)) * ‖f v‖ₑ) ≤
      ENNReal.ofReal 4 * ∫⁻ v in Icc u T,
        ENNReal.ofReal (S.lam u v / S.r u v * ‖f v‖) := by
  apply (coordinate_out_hardy_le hset hu (fun v => ‖f v‖ₑ)).trans_eq
  congr 1
  apply setLIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hr : 0 ≤ S.r u v :=
    (div_nonneg (sub_nonneg.mpr hv.1) (by norm_num : (0 : ℝ) ≤ 4)).trans
      (stab_radius_bounds hset hu.1 hv.1 hv.2).1
  have hw := div_nonneg (hset.c1.lam_pos (u, v) ⟨hu.1, hv.1, hv.2⟩).le hr
  dsimp only
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hw]

private theorem hardy_budget_constant (A ε : ℝ) {N : ℝ≥0∞}
    (hN : N ≤ ENNReal.ofReal (A * ε)) :
    ENNReal.ofReal 4 * (ENNReal.ofReal (16 / 3) * N) ≤ ENNReal.ofReal (32 * A * ε) := by
  calc
    _ ≤ (ENNReal.ofReal 4 * ENNReal.ofReal (16 / 3)) * ENNReal.ofReal (A * ε) := by
      exact (mul_le_mul' le_rfl (mul_le_mul' le_rfl hN)).trans_eq (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal 32 * ENNReal.ofReal (A * ε) := by
      apply mul_le_mul' _ le_rfl
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32)]; congr 1; ring

/-- Individual incoming coordinate Hardy budget from the independent
k envelope. The coefficient `32` is universal and all scales are explicit. -/
theorem coordinate_in_ratio_budget {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) (hε : ε ^ 2 ≤ 1 / 4)
    {v : ℝ} (hv : v ∈ Icc 0 T) :
    (∫⁻ u in Icc 0 v, ENNReal.ofReal (1 / (v - u)) *
      ‖S.xi u v / (S.nu u v : ℂ)‖ₑ) ≤ ENNReal.ofReal (32 * A * ε) := by
  apply (coordinate_in_norm_hardy_le hset hv (fun u => S.xi u v / S.nu u v)).trans
  apply (mul_le_mul' le_rfl (stab_in_hardy hset hε hv.1 hv.2)).trans
  exact hardy_budget_constant A ε ((le_add_left le_rfl).trans hset.env)

/-- Individual outgoing coordinate Hardy budget from the independent
j envelope. The coefficient `32` is universal and independent of all data. -/
theorem coordinate_out_ratio_budget {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) (hε : ε ^ 2 ≤ 1 / 4)
    {u : ℝ} (hu : u ∈ Icc 0 T) :
    (∫⁻ v in Icc u T, ENNReal.ofReal (1 / (v - u)) *
      ‖S.theta u v / (S.lam u v : ℂ)‖ₑ) ≤ ENNReal.ofReal (32 * A * ε) := by
  have hh := stab_out_hardy hset hε hu.1 hu.2
  rw [restrict_Ioc_eq_restrict_Icc] at hh
  apply (coordinate_out_norm_hardy_le hset hu (S.theta u / fun v => (S.lam u v : ℂ))).trans
  apply (mul_le_mul' le_rfl hh).trans
  exact hardy_budget_constant A ε ((le_add_right le_rfl).trans hset.env)

/-- [internal]
 Incoming ratio difference in coordinate Hardy weight, retaining the
phase remainder. The numerical factor `4` is universal; `D` is the fixed
constant of the first-half ratio-difference record. -/
theorem coordinate_in_difference_budget_of_differences {D e T ε M A Δ₀ : ℝ}
    {S₁ S₂ : Fields} {h₁ : ℝ → ℂ} (hset₁ : StabSetting e T ε M A S₁ h₁)
    (hratio : RatioDifferences D e T ε M Δ₀ S₁ S₂) {v : ℝ} (hv : v ∈ Icc 0 T) :
    (∫⁻ u in Icc 0 v, ENNReal.ofReal (1 / (v - u)) *
      ‖S₁.xi u v / (S₁.nu u v : ℂ) - S₂.xi u v / (S₂.nu u v : ℂ)‖ₑ) ≤
      ENNReal.ofReal (4 * D * ((kDist e T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal +
        sigma e M T * ε / M * ((jDist T S₁ S₂).toReal +
          ε * (geomDist T S₁ S₂).toReal + ε * Δ₀ / M))) := by
  apply (coordinate_in_norm_hardy_le hset₁ hv _).trans
  apply (mul_le_mul' le_rfl (hratio.in_hardy v hv)).trans_eq
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  congr 1
  ring

/-- [internal]
 Outgoing ratio difference in coordinate Hardy weight. The numerical
factor `4` is universal and `D` is fixed before the pair. -/
theorem coordinate_out_difference_budget_of_differences {D e T ε M A Δ₀ : ℝ}
    {S₁ S₂ : Fields} {h₁ : ℝ → ℂ} (hset₁ : StabSetting e T ε M A S₁ h₁)
    (hratio : RatioDifferences D e T ε M Δ₀ S₁ S₂) {u : ℝ} (hu : u ∈ Icc 0 T) :
    (∫⁻ v in Icc u T, ENNReal.ofReal (1 / (v - u)) *
      ‖S₁.theta u v / (S₁.lam u v : ℂ) - S₂.theta u v / (S₂.lam u v : ℂ)‖ₑ) ≤
      ENNReal.ofReal (4 * D * ((jDist T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal)) := by
  apply (coordinate_out_norm_hardy_le hset₁ hu _).trans
  apply (mul_le_mul' le_rfl (hratio.out_hardy u hu)).trans_eq
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  congr 1
  ring

end EmcsfAcExtension.Local.Stab
