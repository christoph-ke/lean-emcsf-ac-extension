module

public import EmcsfAcExtension.Local.Stability.GeomStrongElectricSource
import EmcsfAcExtension.Local.Stability.ChargeDifferenceIndividual
import EmcsfAcExtension.Local.Stability.GeomStrongSourceCoefficients

import EmcsfAcExtension.Local.Stability.GeomStrongElectricPrimitive

/-! # An individual electric geometric-source budget

Quadratic radial vanishing removes the cubic coefficient without any
minimum-radius constant, and the explicit charge square is uniformly
bounded at its own normalized scale.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- An individual electric geometric source obeys
`400 (|e|M)² ε²` on the complete triangle. The numerical constant is
universal before all fields, data, scales and derivative suprema. -/
theorem stab_geometric_electric_source_norm_le_c1
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    ‖geometricElectricSource e S u v‖ ≤ 400 * (|e| * M) ^ 2 * ε ^ 2 := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv, hvT⟩
  rcases huv.eq_or_lt with heq | hlt
  · subst v
    simp only [geometricElectricSource, (hset.c1.axis u hp).1,
      zero_pow (by decide : 3 ≠ 0), zero_pow (by decide : 2 ≠ 0), mul_zero,
      div_zero, zero_mul, Complex.ofReal_zero, sub_zero, norm_zero]
    positivity
  · let W : ℂ := (2 * S.nu u v * S.lam u v /
      ((1 - S.mu u v) * S.r u v ^ 3) : ℝ)
    let B := 2 * S.nu u v * S.lam u v / (1 - S.mu u v)
    let q := S.Q u v / S.r u v ^ 2
    have hε : 0 ≤ ε := (norm_nonneg _).trans
      ((le_add_of_nonneg_right (norm_nonneg (S.xi u v / (S.nu u v : ℂ)))).trans
        (hset.box.2 (u, v) hp).2.2.2.2.2.1)
    have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hset.box.1
    have hw : ‖W‖ ≤ 512 / (v - u) ^ 3 := by
      simpa only [W, Complex.norm_real, Real.norm_eq_abs] using
        (stab_geometric_scalar_coefficients_c1 hset hset hu hlt hvT).1
    have hP := stab_electric_primitive_norm_of_quadratic_bound hlt
      (by norm_num : (0 : ℝ) ≤ 512)
      (show 0 ≤ 2 * (|e| * M) ^ 2 * ε ^ 2 by positivity)
      (stab_electric_integrand_aemeasurable_c1 hset hu huv hvT).aestronglyMeasurable
      (fun t ht => stab_electric_curvature_integrand_le_c1 hset hu ht.1 (ht.2.trans hvT)) hw
    have hq : |q| ≤ |e| * M * ε := by
      simpa only [q, abs_div, abs_pow, sq_abs] using stab_charge_ratio_le hset hu hlt hvT
    have hq2 : q ^ 2 ≤ (|e| * M * ε) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg q) hq 2
    have hB := (stab_geometric_electric_coefficients_c1 hset hset hu hlt hvT).1
    have hQ : |2 * B * q ^ 2| ≤ 16 * (|e| * M) ^ 2 * ε ^ 2 := by
      calc
        _ = 2 * |B| * q ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_pow, sq_abs]
        _ ≤ 2 * 8 * (|e| * M * ε) ^ 2 := by gcongr
        _ = _ := by ring
    change ‖W * (∫ t in u..v, electricCurvatureIntegrand e S u t) - ((2 * B * q ^ 2 : ℝ) : ℂ)‖ ≤ _
    apply (norm_sub_le _ _).trans
    rw [Complex.norm_real, Real.norm_eq_abs]
    apply (add_le_add hP hQ).trans
    have hh : 0 ≤ (|e| * M) ^ 2 * ε ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith only [hh]

end EmcsfAcExtension.Local
