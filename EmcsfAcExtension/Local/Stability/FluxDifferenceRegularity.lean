module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Calculus.PartialsC1
import Mathlib.Tactic.FieldSimp

/-! # Quadratic fluxes at the regular axis

The scalar partials remove the apparent division by the radius.
Both optical fluxes are continuous on the whole classical triangle.
-/

public section

open Set

namespace EmcsfAcExtension.Local

private theorem flux_regular_aux {r l : ℝ} (hl : l ≠ 0) (z : ℂ) :
    ‖(r : ℂ) * z‖ ^ 2 / (l * r) = r / l * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  by_cases hr : r = 0
  · simp only [hr, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_div]
  · field_simp

/-- The outgoing quadratic optical flux extends continuously to the
axis in its literal normalized-ratio formula. There is no estimate
constant or additional size hypothesis. -/
theorem stab_out_quadratic_flux_continuous
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    ContinuousOn (fun p : ℝ × ℝ =>
      S.lam p.1 p.2 / S.r p.1 p.2 * ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖ ^ 2)
      (triangle 0 T) := by
  have cP := continuousOn_partial_v hset.c1.c1_phi (uniqueDiffOn_triangle hset.pos)
  have cReg := (hset.c1.c1_r.continuousOn.div hset.c1.c1_lam.continuousOn
    (fun p hp => (hset.c1.lam_pos p hp).ne')).mul (cP.norm.pow 2)
  have cFlux : ContinuousOn (fun p : ℝ × ℝ =>
      ‖S.theta p.1 p.2‖ ^ 2 / (S.lam p.1 p.2 * S.r p.1 p.2)) (triangle 0 T) := by
    apply cReg.congr
    intro p hp
    change ‖S.theta p.1 p.2‖ ^ 2 / (S.lam p.1 p.2 * S.r p.1 p.2) =
      S.r p.1 p.2 / S.lam p.1 p.2 * ‖pdV (triangle 0 T) S.phi p.1 p.2‖ ^ 2
    rw [theta_eq_radius_partial_aux hset.pos hset.c1 hp]
    exact flux_regular_aux (hset.c1.lam_pos p hp).ne' _
  apply cFlux.congr
  intro p hp
  change S.lam p.1 p.2 / S.r p.1 p.2 * ‖S.theta p.1 p.2 / (S.lam p.1 p.2 : ℂ)‖ ^ 2 =
    ‖S.theta p.1 p.2‖ ^ 2 / (S.lam p.1 p.2 * S.r p.1 p.2)
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hl := (hset.c1.lam_pos p hp).ne'
  by_cases hr : S.r p.1 p.2 = 0
  · simp only [hr, mul_zero, div_zero, zero_mul]
  · field_simp

/-- The incoming positive quadratic optical flux is continuous on the
whole classical triangle. Its sign and normalization are literal,
with no estimate constant or size hypothesis. -/
theorem stab_in_quadratic_flux_continuous
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (-S.nu p.1 p.2) / S.r p.1 p.2 * ‖S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ)‖ ^ 2) (triangle 0 T) := by
  have cP := continuousOn_partial_u hset.c1.c1_phi (uniqueDiffOn_triangle hset.pos)
  have cCov := cP.add (((continuousOn_const (c := Complex.I * (e : ℂ))).mul
    (Complex.continuous_ofReal.comp_continuousOn hset.c1.c1_A.continuousOn)).mul
      hset.c1.c1_phi.continuousOn)
  have cReg := (hset.c1.c1_r.continuousOn.div hset.c1.c1_nu.continuousOn
    (fun p hp => (hset.c1.nu_neg p hp).ne)).mul (cCov.norm.pow 2)
  have cFlux : ContinuousOn (fun p : ℝ × ℝ =>
      ‖S.xi p.1 p.2‖ ^ 2 / (S.nu p.1 p.2 * S.r p.1 p.2)) (triangle 0 T) := by
    apply cReg.congr
    intro p hp
    change ‖S.xi p.1 p.2‖ ^ 2 / (S.nu p.1 p.2 * S.r p.1 p.2) =
      S.r p.1 p.2 / S.nu p.1 p.2 *
        ‖pdU (triangle 0 T) S.phi p.1 p.2 +
          Complex.I * e * S.A p.1 p.2 * S.phi p.1 p.2‖ ^ 2
    rw [xi_eq_radius_covariant_partial_aux hset.pos hset.c1 hp]
    exact flux_regular_aux (hset.c1.nu_neg p hp).ne _
  apply cFlux.neg.congr
  intro p hp
  change -S.nu p.1 p.2 / S.r p.1 p.2 * ‖S.xi p.1 p.2 / (S.nu p.1 p.2 : ℂ)‖ ^ 2 =
    -(‖S.xi p.1 p.2‖ ^ 2 / (S.nu p.1 p.2 * S.r p.1 p.2))
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hn := (hset.c1.nu_neg p hp).ne
  by_cases hr : S.r p.1 p.2 = 0
  · simp only [hr, mul_zero, div_zero, zero_mul, neg_zero]
  · field_simp

end EmcsfAcExtension.Local
