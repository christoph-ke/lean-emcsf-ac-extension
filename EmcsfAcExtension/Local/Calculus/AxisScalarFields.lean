module

public import EmcsfAcExtension.Local.Calculus.AxisContinuity
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Radius times scalar partials on the closed triangle

Multiplying the natural scalar equations by the radius removes their singular
denominator. The resulting identities extend continuously to the regular center.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- The outgoing scalar constraint holds on the axis after multiplication by
`r`. This identifies the continuous quotient supplied by the classical class. -/
theorem theta_eq_radius_partial_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hp : (u, v) ∈ triangle 0 T) :
    S.theta u v = (S.r u v : ℂ) * pdV (triangle 0 T) S.phi u v := by
  apply eqOn_triangle_of_off_axis_aux hT hS.c1_theta.continuousOn
    ((continuous_ofReal.comp_continuousOn hS.c1_r.continuousOn).mul
      (continuousOn_partial_v hS.c1_phi (uniqueDiffOn_triangle hT))) ?_ hp
  intro p hp huv
  change S.theta p.1 p.2 = (S.r p.1 p.2 : ℂ) * pdV (triangle 0 T) S.phi p.1 p.2
  rw [(hS.eq_v p hp huv).2.2.2.2.2.1]
  dsimp only [Fields.phiV]
  have hr : (S.r p.1 p.2 : ℂ) ≠ 0 := by exact_mod_cast (hS.r_pos p hp huv).ne'
  field_simp [hr]

/-- The incoming scalar constraint holds on the axis in covariant form after
multiplication by `r`. It imposes no condition on the axis potential. -/
theorem xi_eq_radius_covariant_partial_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hp : (u, v) ∈ triangle 0 T) :
    S.xi u v = (S.r u v : ℂ) *
      (pdU (triangle 0 T) S.phi u v + I * e * S.A u v * S.phi u v) := by
  apply eqOn_triangle_of_off_axis_aux hT hS.c1_xi.continuousOn
    ((continuous_ofReal.comp_continuousOn hS.c1_r.continuousOn).mul
      ((continuousOn_partial_u hS.c1_phi (uniqueDiffOn_triangle hT)).add
        (((continuousOn_const (c := I * e)).mul
          (continuous_ofReal.comp_continuousOn hS.c1_A.continuousOn)).mul
            hS.c1_phi.continuousOn))) ?_ hp
  intro p hp huv
  change S.xi p.1 p.2 = (S.r p.1 p.2 : ℂ) *
    (pdU (triangle 0 T) S.phi p.1 p.2 + I * e * S.A p.1 p.2 * S.phi p.1 p.2)
  rw [(hS.eq_u p hp huv).2.2.2.2.1]
  dsimp only [Fields.phiU]
  have hr : (S.r p.1 p.2 : ℂ) ≠ 0 := by exact_mod_cast (hS.r_pos p hp huv).ne'
  field_simp [hr]
  ring

end EmcsfAcExtension.Local
