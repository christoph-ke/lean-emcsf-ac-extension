module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Calculus.Raychaudhuri
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Infra.Calculus.PartialsC1
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Axis-to-point optical reconstruction

The exact optical identities used by internal project record (RO) extend to the axis
on the classical class. The natural scalar partial removes the apparent
radius denominator in the quadratic flux, so ordinary closed-interval
FTC applies without an extra endpoint regularity assumption.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

private theorem ray_flux_regular_aux {r l : ℝ} (hl : l ≠ 0) (z : ℂ) :
    ‖(r : ℂ) * z‖ ^ 2 / (l * r) = r / l * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  by_cases hr : r = 0
  · simp only [hr, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_div]
  · field_simp

private theorem ray_flux_ratio_aux {r l : ℝ} (hl : l ≠ 0) (z : ℂ) :
    ‖z‖ ^ 2 / (l * r) = l / r * ‖z / (l : ℂ)‖ ^ 2 := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  by_cases hr : r = 0
  · simp only [hr, mul_zero, div_zero, zero_mul]
  · field_simp

/-- The outgoing optical factor reconstructed from its axis value,
as in approved internal project record (RO). This is an exact identity with no estimate
constant and no size or gauge hypothesis beyond the classical setting. -/
theorem stab_out_optical_from_axis
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    -S.nu u v / (1 - S.mu u v) = S.lam u u *
      Real.exp (∫ s in u..v, S.lam u s / S.r u s *
        ‖S.theta u s / (S.lam u s : ℂ)‖ ^ 2) := by
  have hmap : MapsTo (fun s : ℝ => (u, s)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hu, hs.1, hs.2.trans hvT⟩
  have cN := hset.c1.c1_nu.continuousOn.neg
  have cG : ContinuousOn (fun p : ℝ × ℝ => 1 - S.mu p.1 p.2) (triangle 0 T) :=
    continuousOn_const.sub (continuousOn_mu_aux hset.pos hset.c1)
  have cOpt := cN.div cG (fun p hp => (hset.c1.one_sub_mu_pos p hp).ne')
  have hOpt : ∀ p ∈ triangle 0 T, 0 < -S.nu p.1 p.2 / (1 - S.mu p.1 p.2) :=
    fun p hp => div_pos (neg_pos.mpr (hset.c1.nu_neg p hp))
      (hset.c1.one_sub_mu_pos p hp)
  have cLog := cOpt.log (fun p hp => (hOpt p hp).ne')
  have cLogS : ContinuousOn (fun s => Real.log (-S.nu u s / (1 - S.mu u s))) (Icc u v) :=
    cLog.comp (continuous_const.prodMk continuous_id).continuousOn hmap
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
    exact ray_flux_regular_aux (hset.c1.lam_pos p hp).ne' _
  have cFluxS := cFlux.comp (continuous_const.prodMk continuous_id).continuousOn hmap
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv cLogS
    (fun s hs => (eq_ray_out hset.c1 hu hs.1 (hs.2.le.trans hvT)).hasDerivAt
      (Icc_mem_nhds hs.1 (hs.2.trans_le hvT)))
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv cFluxS)
  change (∫ s in u..v, ‖S.theta u s‖ ^ 2 / (S.lam u s * S.r u s)) =
    Real.log (-S.nu u v / (1 - S.mu u v)) -
      Real.log (-S.nu u u / (1 - S.mu u u)) at hi
  have heqFlux : (∫ s in u..v, ‖S.theta u s‖ ^ 2 / (S.lam u s * S.r u s)) =
      ∫ s in u..v, S.lam u s / S.r u s * ‖S.theta u s / (S.lam u s : ℂ)‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc u v := by simpa only [uIcc_of_le huv] using hs
    exact ray_flux_ratio_aux (hset.c1.lam_pos (u, s) (hmap hs')).ne' _
  rw [heqFlux] at hi
  have haxis := hset.c1.axis u ⟨hu, le_rfl, huv.trans hvT⟩
  have hmu : S.mu u u = 0 := by simp only [Fields.mu, haxis.1, div_zero]
  have hnu : -S.nu u u = S.lam u u := by linarith only [haxis.2.2.2.1]
  rw [hmu, sub_zero, hnu, div_one] at hi
  have hlog : Real.log (-S.nu u v / (1 - S.mu u v)) = Real.log (S.lam u u) +
      ∫ s in u..v, S.lam u s / S.r u s * ‖S.theta u s / (S.lam u s : ℂ)‖ ^ 2 := by
    linarith only [hi]
  have hexp := congrArg Real.exp hlog
  rw [Real.exp_log (hOpt (u, v) ⟨hu, huv, hvT⟩), Real.exp_add,
    Real.exp_log (hset.c1.lam_pos (u, u) ⟨hu, le_rfl, huv.trans hvT⟩)] at hexp
  exact hexp

/-- The incoming optical factor reconstructed from the terminal axis
value, as in approved internal project record (RO). The orientation is explicit and the
identity has no estimate constant, size assumption or gauge premise. -/
theorem stab_in_optical_from_axis
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
    S.lam u v / (1 - S.mu u v) = S.lam v v *
      Real.exp (∫ s in u..v, (-S.nu s v) / S.r s v *
        ‖S.xi s v / (S.nu s v : ℂ)‖ ^ 2) := by
  have hmap : MapsTo (fun s : ℝ => (s, v)) (Icc u v) (triangle 0 T) :=
    fun s hs => ⟨hu.trans hs.1, hs.2, hvT⟩
  have cG : ContinuousOn (fun p : ℝ × ℝ => 1 - S.mu p.1 p.2) (triangle 0 T) :=
    continuousOn_const.sub (continuousOn_mu_aux hset.pos hset.c1)
  have cOpt := hset.c1.c1_lam.continuousOn.div cG
    (fun p hp => (hset.c1.one_sub_mu_pos p hp).ne')
  have hOpt : ∀ p ∈ triangle 0 T, 0 < S.lam p.1 p.2 / (1 - S.mu p.1 p.2) :=
    fun p hp => div_pos (hset.c1.lam_pos p hp) (hset.c1.one_sub_mu_pos p hp)
  have cLog := cOpt.log (fun p hp => (hOpt p hp).ne')
  have cLogS : ContinuousOn (fun s => Real.log (S.lam s v / (1 - S.mu s v))) (Icc u v) :=
    cLog.comp (continuous_id.prodMk continuous_const).continuousOn hmap
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
    exact ray_flux_regular_aux (hset.c1.nu_neg p hp).ne _
  have cFluxS := cFlux.comp (continuous_id.prodMk continuous_const).continuousOn hmap
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv cLogS
    (fun s hs => (eq_ray_in hset.c1 (hu.trans hs.1.le) hs.2 hvT).hasDerivAt
      (Icc_mem_nhds (hu.trans_lt hs.1) hs.2))
    (ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv cFluxS)
  change (∫ s in u..v, ‖S.xi s v‖ ^ 2 / (S.nu s v * S.r s v)) =
    Real.log (S.lam v v / (1 - S.mu v v)) -
      Real.log (S.lam u v / (1 - S.mu u v)) at hi
  have heqFlux : (∫ s in u..v, ‖S.xi s v‖ ^ 2 / (S.nu s v * S.r s v)) =
      -(∫ s in u..v, (-S.nu s v) / S.r s v * ‖S.xi s v / (S.nu s v : ℂ)‖ ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc u v := by simpa only [uIcc_of_le huv] using hs
    dsimp only
    rw [ray_flux_ratio_aux (hset.c1.nu_neg (s, v) (hmap hs')).ne _]
    ring
  rw [heqFlux] at hi
  have haxis := hset.c1.axis v ⟨hu.trans huv, le_rfl, hvT⟩
  have hmu : S.mu v v = 0 := by simp only [Fields.mu, haxis.1, div_zero]
  rw [hmu, sub_zero, div_one] at hi
  have hlog : Real.log (S.lam u v / (1 - S.mu u v)) = Real.log (S.lam v v) +
      ∫ s in u..v, (-S.nu s v) / S.r s v * ‖S.xi s v / (S.nu s v : ℂ)‖ ^ 2 := by
    linarith only [hi]
  have hexp := congrArg Real.exp hlog
  rw [Real.exp_log (hOpt (u, v) ⟨hu, huv, hvT⟩), Real.exp_add,
    Real.exp_log (hset.c1.lam_pos (v, v) ⟨hu.trans huv, le_rfl, hvT⟩)] at hexp
  exact hexp

end EmcsfAcExtension.Local
