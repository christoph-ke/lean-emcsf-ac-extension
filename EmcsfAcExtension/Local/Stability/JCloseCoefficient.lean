module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Stability.JClose
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Infra.Calculus.PartialsC1
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Regular real coefficients of the renormalized transports

The apparent inverse radius is removed by the natural scalar constraints.
Both coefficients are continuous on the closed classical triangle.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Stab

/-- The literal real coefficient in the incoming j transport. -/
@[expose] noncomputable def jRealCoefficient (S : Fields) (u v : ℝ) : ℝ :=
  -‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v)

/-- The literal real coefficient in the outgoing k transport. -/
@[expose] noncomputable def kRealCoefficient (S : Fields) (u v : ℝ) : ℝ :=
  -‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)

/-- The outgoing k coefficient is the negative outgoing quadratic flux,
including its totalized value at the axis. -/
theorem k_coefficient_eq_flux {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    kRealCoefficient S u v = -S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2 := by
  have hl := (hs.c1.lam_pos (u, v) hp).ne'
  by_cases hr : S.r u v = 0
  · simp [kRealCoefficient, hr]
  rw [norm_div, div_pow, norm_real, Real.norm_eq_abs, sq_abs]
  dsimp only [kRealCoefficient]
  field_simp

/-- Both transport coefficients have their regular scalar-partial form
on the complete triangle. No smallness, gauge, or size bound is required. -/
theorem transport_real_coefficients_eq_regular {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    jRealCoefficient S u v = -(S.r u v / S.nu u v) *
      ‖pdU (triangle 0 T) S.phi u v + I * e * S.A u v * S.phi u v‖ ^ 2 ∧
    kRealCoefficient S u v = -(S.r u v / S.lam u v) * ‖pdV (triangle 0 T) S.phi u v‖ ^ 2 := by
  have hn := (hs.c1.nu_neg (u, v) hp).ne
  have hl := (hs.c1.lam_pos (u, v) hp).ne'
  have hξ := xi_eq_radius_covariant_partial_aux hs.pos hs.c1 hp
  have hθ := theta_eq_radius_partial_aux hs.pos hs.c1 hp
  constructor
  · dsimp only [jRealCoefficient]
    rw [hξ, norm_mul, norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    by_cases hr : S.r u v = 0
    · simp [hr]
    · field_simp
  · dsimp only [kRealCoefficient]
    rw [hθ, norm_mul, norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    by_cases hr : S.r u v = 0
    · simp [hr]
    · field_simp

/-- Both real transport coefficients are continuous through the axis.
The partial derivatives are only those supplied by the standing classical
class; no higher derivative or bound is introduced. -/
theorem transport_real_coefficients_continuousOn {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) :
    ContinuousOn (Function.uncurry (jRealCoefficient S)) (triangle 0 T) ∧
    ContinuousOn (Function.uncurry (kRealCoefficient S)) (triangle 0 T) := by
  have hpu := continuousOn_partial_u hs.c1.c1_phi (uniqueDiffOn_triangle hs.pos)
  have hpv := continuousOn_partial_v hs.c1.c1_phi (uniqueDiffOn_triangle hs.pos)
  have hA := Complex.continuous_ofReal.comp_continuousOn hs.c1.c1_A.continuousOn
  have hD := hpu.add (((continuousOn_const (c := I * e)).mul hA).mul hs.c1.c1_phi.continuousOn)
  have hcn := (hs.c1.c1_r.continuousOn.div hs.c1.c1_nu.continuousOn
    (fun p hp => (hs.c1.nu_neg p hp).ne)).neg.mul (hD.norm.pow 2)
  have hcl := (hs.c1.c1_r.continuousOn.div hs.c1.c1_lam.continuousOn
    (fun p hp => (hs.c1.lam_pos p hp).ne')).neg.mul (hpv.norm.pow 2)
  constructor
  · apply hcn.congr
    intro p hp
    exact (transport_real_coefficients_eq_regular hs hp).1
  · apply hcl.congr
    intro p hp
    exact (transport_real_coefficients_eq_regular hs hp).2

/-- The j coefficient is nonnegative everywhere in the standing triangle,
including the axis; this fixes the orientation of its amplification budget. -/
theorem jRealCoefficient_nonneg {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    0 ≤ jRealCoefficient S u v := by
  rw [(transport_real_coefficients_eq_regular hs hp).1]
  have hr : 0 ≤ S.r u v :=
    (div_nonneg (sub_nonneg.mpr hp.2.1) (by norm_num : (0 : ℝ) ≤ 4)).trans
      (stab_radius_bounds hs hp.1 hp.2.1 hp.2.2).1
  have hn := hs.c1.nu_neg (u, v) hp
  exact mul_nonneg (neg_nonneg.mpr (div_nonpos_of_nonneg_of_nonpos hr hn.le)) (sq_nonneg _)

/-- The k coefficient is nonpositive everywhere, so its real propagators
have amplification at most one, without a smallness assumption. -/
theorem kRealCoefficient_nonpos {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hs : StabSetting e T ε M A S h) {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    kRealCoefficient S u v ≤ 0 := by
  rw [(transport_real_coefficients_eq_regular hs hp).2]
  have hr : 0 ≤ S.r u v :=
    (div_nonneg (sub_nonneg.mpr hp.2.1) (by norm_num : (0 : ℝ) ≤ 4)).trans
      (stab_radius_bounds hs hp.1 hp.2.1 hp.2.2).1
  have hl := hs.c1.lam_pos (u, v) hp
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg hr hl.le)) (sq_nonneg _)

end EmcsfAcExtension.Local.Stab
