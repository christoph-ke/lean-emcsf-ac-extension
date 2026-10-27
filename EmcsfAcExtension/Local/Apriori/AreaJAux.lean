module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Radius and measurability facts for the scalar area estimates

All comparisons use only the fixed bootstrap box. No smallness assumption
or envelope bound is used in this module.
-/

public section

open Set MeasureTheory Filter Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Area

variable {e T ε M : ℝ} {S : Fields} {h : ℝ → ℂ}

/-- The radius is the integral of the outgoing expansion from the regular
axis. This exact identity requires no estimate constant.
-/
theorem radius_out_integral (hset : AprioriSetting e T ε M S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (∫ s in u..v, S.lam u s) = S.r u v := by
  have hm : MapsTo (fun s => (u, s)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩
  have hr : ContinuousOn (S.r u) (Icc u v) := hset.c1.c1_r.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hm
  have hl : ContinuousOn (S.lam u) (Icc u v) := hset.c1.c1_lam.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hm
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hr
    (fun s hs => by
      have hp : (u, s) ∈ triangle 0 T := hm ⟨hs.1.le, hs.2.le⟩
      have hd := hasDerivWithinAt_uncurry_triangle_v hset.c1.c1_r hp
      change HasDerivWithinAt (S.r u) (pdV (triangle 0 T) S.r u s) (Icc u T) s at hd
      rw [(hset.c1.eq_v (u, s) hp hs.1).1] at hd
      exact hd.hasDerivAt (Icc_mem_nhds hs.1 (hs.2.trans_le hvT)))
    (hl.intervalIntegrable_of_Icc (μ := volume) huv)
  rwa [(hset.c1.axis u ⟨hu, le_rfl, huv.trans hvT⟩).1, sub_zero] at hi

/-- Radius and coordinate separation are comparable with the universal
box constants `1/4` and `1`, independently of all solution parameters.
-/
theorem radius_bounds (hset : AprioriSetting e T ε M S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    (v - u) / 4 ≤ S.r u v ∧ S.r u v ≤ v - u := by
  have hl : ContinuousOn (S.lam u) (Icc u v) :=
    hset.c1.c1_lam.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩)
  have hi := hl.intervalIntegrable_of_Icc (μ := volume) huv
  rw [← radius_out_integral hset hu huv hvT]
  constructor
  · have hb := intervalIntegral.integral_mono_on huv intervalIntegrable_const hi
      (fun s hs => (hset.box (u, s) ⟨hu, hs.1, hs.2.trans hvT⟩).1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one_div] using hb
  · have hb := intervalIntegral.integral_mono_on huv hi intervalIntegrable_const
      (fun s hs => (hset.box (u, s) ⟨hu, hs.1, hs.2.trans hvT⟩).2.1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using hb

/-- The scalar outgoing primitive multiplier is bounded by an inverse-cube
coordinate kernel. The numerical coefficient `256` depends only on the
fixed box and is uniform in the solution and its derivative norms.
-/
theorem scalar_out_coefficient_le (hset : AprioriSetting e T ε M S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖((S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2) *
      (S.r u v : ℂ)⁻¹‖ ≤ 256 * ε / (v - u) ^ 3 := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := hset.c1.r_pos (u, v) hp huv
  have hn := hset.c1.nu_neg (u, v) hp
  have hθ := hset.theta_norm_le hp
  have hb := hset.box (u, v) hp
  have hrb := (radius_bounds hset hu huv.le hvT).1
  rw [norm_mul, norm_div, norm_mul, norm_pow, norm_inv,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_neg hn, abs_of_pos hr]
  calc
    (-S.nu u v) * ‖S.theta u v‖ / S.r u v ^ 2 * (S.r u v)⁻¹ ≤
        1 * (4 * ε * 1) / S.r u v ^ 2 * (S.r u v)⁻¹ := by
      gcongr
      · exact hb.2.2.2.1
      · exact hθ.trans (mul_le_mul_of_nonneg_left hb.2.1
          (mul_nonneg (by norm_num) hset.eps_nonneg))
    _ = 4 * ε / S.r u v ^ 3 := by field_simp
    _ ≤ 4 * ε / ((v - u) / 4) ^ 3 := by
      gcongr
      exact mul_nonneg (by norm_num) hset.eps_nonneg
    _ = _ := by field_simp; ring

/-- The scalar incoming primitive multiplier is bounded by an inverse-cube
coordinate kernel. The numerical coefficient `256` depends only on the
fixed box and is uniform in the solution and its derivative norms.
-/
theorem scalar_in_coefficient_le (hset : AprioriSetting e T ε M S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    ‖((S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2) *
      (S.r u v : ℂ)⁻¹‖ ≤ 256 * ε / (v - u) ^ 3 := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := hset.c1.r_pos (u, v) hp huv
  have hl := hset.c1.lam_pos (u, v) hp
  have hξ := hset.xi_norm_le hp
  have hb := hset.box (u, v) hp
  have hrb := (radius_bounds hset hu huv.le hvT).1
  rw [norm_mul, norm_div, norm_mul, norm_pow, norm_inv,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hl, abs_of_pos hr]
  calc
    S.lam u v * ‖S.xi u v‖ / S.r u v ^ 2 * (S.r u v)⁻¹ ≤
        1 * (4 * ε * 1) / S.r u v ^ 2 * (S.r u v)⁻¹ := by
      gcongr
      · exact hb.2.1
      · exact hξ.trans (mul_le_mul_of_nonneg_left hb.2.2.2.1
          (mul_nonneg (by norm_num) hset.eps_nonneg))
    _ = 4 * ε / S.r u v ^ 3 := by field_simp
    _ ≤ 4 * ε / ((v - u) / 4) ^ 3 := by
      gcongr
      exact mul_nonneg (by norm_num) hset.eps_nonneg
    _ = _ := by field_simp; ring

/-- Extending a continuous field on the triangle by zero gives a measurable
field on the ambient plane. This helper introduces no estimate constant.
-/
theorem measurable_triangle_extension {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {f : ℝ × ℝ → E}
    (hf : ContinuousOn f (triangle 0 T)) :
    Measurable ((triangle 0 T).indicator f) := by
  classical
  exact hf.measurable_piecewise continuousOn_const (measurableSet_triangle 0 T)

end EmcsfAcExtension.Local.Area
