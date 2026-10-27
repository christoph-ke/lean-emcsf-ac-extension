module

public import EmcsfAcExtension.Local.Calculus.Normalized
public import EmcsfAcExtension.Local.Calculus.AxisRatio
public import EmcsfAcExtension.Local.Calculus.AxisScalarFields
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Continuous renormalized derivatives at the classical axis

The natural scalar constraints remove the apparent radius division in each cubic
correction. All continuity statements concern the C¹ class, never an AC trace.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

private theorem cubic_radius_identity_aux (r a : ℝ) (x : ℂ) (ha : a ≠ 0) :
    (a : ℂ) / r * (‖(r : ℂ) * x / a‖ : ℂ) ^ 2 * ((r : ℂ) * x / a) =
      ((r / a : ℝ) : ℂ) ^ 2 * (‖x‖ : ℂ) ^ 2 * x := by
  have hn : ‖(r : ℂ) * x / a‖ ^ 2 = r ^ 2 * ‖x‖ ^ 2 / a ^ 2 := by
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, div_pow, mul_pow, sq_abs, sq_abs]
  have hnC : (‖(r : ℂ) * x / a‖ : ℂ) ^ 2 =
      (r : ℂ) ^ 2 * (‖x‖ : ℂ) ^ 2 / (a : ℂ) ^ 2 := by exact_mod_cast hn
  rw [hnC]
  push_cast
  by_cases hr : r = 0
  · simp only [hr, ofReal_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, div_zero, zero_div]
  · have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    field_simp [haC, hrC]

/-- The outgoing cubic correction has a regular expression in the outgoing scalar
partial. This identity includes the defined axis values and chooses no constants. -/
theorem jC1_eq_regular_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    jC1 (triangle 0 T) S u v = (1 - S.mu u v) *
      (pdV (triangle 0 T) S.a u v - ((S.r u v / S.lam u v : ℝ) : ℂ) ^ 2 *
        (‖pdV (triangle 0 T) S.phi u v‖ : ℂ) ^ 2 * pdV (triangle 0 T) S.phi u v) := by
  rw [jC1, theta_eq_radius_partial_aux hT hS hp]
  rw [cubic_radius_identity_aux _ _ _ (hS.lam_pos _ hp).ne']

/-- The incoming cubic correction has a regular expression in the covariant
incoming scalar partial. It is continuous in every gauge in the classical class. -/
theorem kC1_eq_regular_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) :
    let p := pdU (triangle 0 T) S.phi u v + I * e * S.A u v * S.phi u v
    kC1 e (triangle 0 T) S u v = (1 - S.mu u v) *
      (pdU (triangle 0 T) S.b u v + I * e * S.A u v * S.b u v -
        ((S.r u v / S.nu u v : ℝ) : ℂ) ^ 2 * (‖p‖ : ℂ) ^ 2 * p) := by
  dsimp only
  rw [kC1, xi_eq_radius_covariant_partial_aux hT hS hp]
  rw [cubic_radius_identity_aux _ _ _ (hS.nu_neg _ hp).ne]

/-- The canonical outgoing renormalized derivative is continuous on a positive-time
classical triangle, including the regular axis and its endpoints. -/
theorem continuousOn_jC1_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContinuousOn (Function.uncurry (jC1 (triangle 0 T) S)) (triangle 0 T) := by
  have cH := (continuousOn_const (c := (1 : ℂ))).sub
    (continuous_ofReal.comp_continuousOn (continuousOn_mu_aux hT hS))
  have ca := continuousOn_partial_v (c1_a_aux hS) (uniqueDiffOn_triangle hT)
  have cp := continuousOn_partial_v hS.c1_phi (uniqueDiffOn_triangle hT)
  have cr := continuous_ofReal.comp_continuousOn
    (hS.c1_r.continuousOn.div hS.c1_lam.continuousOn
      (fun p hp => (hS.lam_pos p hp).ne'))
  have cn := continuous_ofReal.comp_continuousOn cp.norm
  have hc : ContinuousOn (fun p : ℝ × ℝ => (1 - S.mu p.1 p.2) *
      (pdV (triangle 0 T) S.a p.1 p.2 - ((S.r p.1 p.2 / S.lam p.1 p.2 : ℝ) : ℂ) ^ 2 *
        (‖pdV (triangle 0 T) S.phi p.1 p.2‖ : ℂ) ^ 2 *
          pdV (triangle 0 T) S.phi p.1 p.2)) (triangle 0 T) :=
    cH.mul (ca.sub (((cr.pow 2).mul (cn.pow 2)).mul cp))
  exact hc.congr (fun p hp => jC1_eq_regular_aux hT hS hp)

/-- The canonical incoming renormalized derivative is continuous on a positive-time
classical triangle. The connection is retained, so no axis gauge is assumed. -/
theorem continuousOn_kC1_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContinuousOn (Function.uncurry (kC1 e (triangle 0 T) S)) (triangle 0 T) := by
  have cH := (continuousOn_const (c := (1 : ℂ))).sub
    (continuous_ofReal.comp_continuousOn (continuousOn_mu_aux hT hS))
  have cb := continuousOn_partial_u (c1_b_aux hS) (uniqueDiffOn_triangle hT)
  have cp := continuousOn_partial_u hS.c1_phi (uniqueDiffOn_triangle hT)
  have cA := (continuousOn_const (c := I * e)).mul
    (continuous_ofReal.comp_continuousOn hS.c1_A.continuousOn)
  have cP := cp.add (cA.mul hS.c1_phi.continuousOn)
  have cr := continuous_ofReal.comp_continuousOn
    (hS.c1_r.continuousOn.div hS.c1_nu.continuousOn
      (fun p hp => (hS.nu_neg p hp).ne))
  have cn := continuous_ofReal.comp_continuousOn cP.norm
  have hc : ContinuousOn (fun p : ℝ × ℝ => (1 - S.mu p.1 p.2) *
      (pdU (triangle 0 T) S.b p.1 p.2 + I * e * S.A p.1 p.2 * S.b p.1 p.2 -
        ((S.r p.1 p.2 / S.nu p.1 p.2 : ℝ) : ℂ) ^ 2 *
          (‖pdU (triangle 0 T) S.phi p.1 p.2 + I * e * S.A p.1 p.2 * S.phi p.1 p.2‖ : ℂ) ^ 2 *
          (pdU (triangle 0 T) S.phi p.1 p.2 + I * e * S.A p.1 p.2 * S.phi p.1 p.2)))
      (triangle 0 T) :=
    cH.mul ((cb.add (cA.mul (c1_b_aux hS).continuousOn)).sub
      (((cr.pow 2).mul (cn.pow 2)).mul cP))
  exact hc.congr (fun p hp => kC1_eq_regular_aux hT hS hp)

/-- The complex curvature is continuous on the classical triangle once the mass
ratio is extended by its literal regular-axis value. -/
theorem continuousOn_curv_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) :
    ContinuousOn (Function.uncurry (curv S)) (triangle 0 T) := by
  have cm := continuous_ofReal.comp_continuousOn (continuousOn_mu_aux hT hS)
  have cl := continuous_ofReal.comp_continuousOn hS.c1_lam.continuousOn
  have cn := continuous_ofReal.comp_continuousOn hS.c1_nu.continuousOn
  exact cm.add ((((((continuousOn_const (c := (1 : ℂ))).sub cm).mul hS.c1_theta.continuousOn).mul
    hS.c1_xi.continuousOn.star).div (cl.mul cn)
      (fun p hp => mul_ne_zero (Complex.ofReal_ne_zero.mpr (hS.lam_pos p hp).ne')
        (Complex.ofReal_ne_zero.mpr (hS.nu_neg p hp).ne))))

end EmcsfAcExtension.Local
