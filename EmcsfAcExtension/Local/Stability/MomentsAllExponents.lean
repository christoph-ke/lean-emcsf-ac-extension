module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.Moments
import EmcsfAcExtension.Local.Stability.MomentsIncoming

/-! # All admissible moment exponents in the small-data regime

The positive-exponent ODE core implies the paper's full real exponent
range by monotonicity of powers on `(0,1]`. Negative exponents are used
only off the axis, and their endpoint values do not affect the integrals.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}

/-- Outgoing moment for every real admissible exponent in the small-data
regime. The coefficient is exactly `4`, uniformly in all parameters and
exponents. The sole conditional input is the exact outgoing identity. -/
theorem stab_out_moment_all_exponents_of_identity (hset : StabSetting e T ε M A S h)
    (hidentity : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
      HasDerivWithinAt (fun s => S.theta u s / (S.lam u s : ℂ))
        (jC1 (triangle 0 T) S u v / ((1 - S.mu u v : ℝ) : ℂ) -
          (S.lam u v / S.r u v * (1 - ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2)) •
            (S.theta u v / (S.lam u v : ℂ))) (Icc u T) v)
    (hε : ε ^ 2 ≤ 1 / 4) {p u v : ℝ} (hp : p ≤ 1 - ε ^ 2)
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ENNReal.ofReal ‖S.theta u v / (S.lam u v : ℂ)‖ ≤
      ENNReal.ofReal 4 * ∫⁻ s in Ioc u v,
        ENNReal.ofReal ((S.r u s / S.r u v) ^ p) *
          outEnv 0 (jC1 (triangle 0 T) S) s := by
  have hq0 : 0 < max p (3 / 4 : ℝ) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hq : max p (3 / 4 : ℝ) ≤ 1 - ε ^ 2 := max_le hp (by linarith only [hε])
  apply (stab_out_moment_of_identity hset hidentity hq0 hq hu huv hvT).trans
  apply mul_le_mul' le_rfl
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  have hr := hset.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv
  have hrs := hset.c1.r_pos (u, s) ⟨hu, hs.1.le, hs.2.trans hvT⟩ hs.1
  exact Real.rpow_le_rpow_of_exponent_ge (div_pos hrs hr)
    ((div_le_one hr).2 (stab_radius_section_order hset hu hs.1.le hs.2 hvT).1)
    (le_max_left _ _)

/-- Incoming moment for every real admissible exponent in the small-data
regime. The coefficient is exactly `4`, uniformly in all parameters and
exponents. The only conditional input is the exact incoming identity. -/
theorem stab_in_moment_all_exponents_of_identity (hset : StabSetting e T ε M A S h)
    (hidentity : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ T →
      HasDerivWithinAt (fun s => S.xi s v / (S.nu s v : ℂ))
        (kC1 e (triangle 0 T) S u v / ((1 - S.mu u v : ℝ) : ℂ) -
          (S.nu u v / S.r u v * (1 - ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2)) •
            (S.xi u v / (S.nu u v : ℂ)) -
          (e * S.A u v) • (Complex.I * (S.xi u v / (S.nu u v : ℂ)))) (Icc 0 v) u)
    (hε : ε ^ 2 ≤ 1 / 4) {p u v : ℝ} (hp : p ≤ 1 - ε ^ 2)
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ENNReal.ofReal ‖S.xi u v / (S.nu u v : ℂ)‖ ≤
      ENNReal.ofReal 4 * ∫⁻ s in Icc u v,
        ENNReal.ofReal ((S.r s v / S.r u v) ^ p) *
          inEnv T (kC1 e (triangle 0 T) S) s := by
  have hq0 : 0 < max p (3 / 4 : ℝ) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hq : max p (3 / 4 : ℝ) ≤ 1 - ε ^ 2 := max_le hp (by linarith only [hε])
  have hb := stab_in_moment_of_identity hset hidentity hq0 hq hu huv hvT
  rw [← restrict_Ioo_eq_restrict_Icc] at hb ⊢
  apply hb.trans
  apply mul_le_mul' le_rfl
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  have hr := hset.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv
  have hrs := hset.c1.r_pos (s, v) ⟨hu.trans hs.1.le, hs.2.le, hvT⟩ hs.2
  exact Real.rpow_le_rpow_of_exponent_ge (div_pos hrs hr)
    ((div_le_one hr).2 (stab_radius_section_order hset hu hs.1.le hs.2.le hvT).2)
    (le_max_left _ _)

end EmcsfAcExtension.Local
