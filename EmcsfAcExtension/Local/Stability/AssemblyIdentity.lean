module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Renormalized
public import EmcsfAcExtension.Local.Stability.OrderedKernelIncoming
import EmcsfAcExtension.Local.Calculus.RadialIdentity
import EmcsfAcExtension.Local.Calculus.CurvatureIntegral
import EmcsfAcExtension.Local.Calculus.Transport

/-! # Field identities in the form used by the stability analytic cores

The reconstruction bridges change only scalar notation and summand order.
The curvature bridges identify the literal primitives with the curvature terms
in the actual renormalized field transports. No additional premise is introduced.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- Outgoing reconstruction in real scalar multiplication notation. -/
theorem stab_out_reconstruction_smul {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun s => S.theta u s / (S.lam u s : ℂ))
      (jC1 (triangle 0 T) S u v / ((1 - S.mu u v : ℝ) : ℂ) -
        (S.lam u v / S.r u v * (1 - ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2)) •
          (S.theta u v / (S.lam u v : ℂ))) (Icc u T) v := by
  simpa only [Complex.real_smul, ofReal_mul, ofReal_sub, ofReal_one, ofReal_pow]
    using stab_out_reconstruction hS hu huv hvT

/-- Incoming reconstruction with damping before the real connection term. -/
theorem stab_in_reconstruction_smul {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun s => S.xi s v / (S.nu s v : ℂ))
      (kC1 e (triangle 0 T) S u v / ((1 - S.mu u v : ℝ) : ℂ) -
        (S.nu u v / S.r u v * (1 - ‖S.xi u v / (S.nu u v : ℂ)‖ ^ 2)) •
          (S.xi u v / (S.nu u v : ℂ)) -
        (e * S.A u v) • (I * (S.xi u v / (S.nu u v : ℂ)))) (Icc 0 v) u := by
  convert stab_in_reconstruction hS hu huv hvT using 1
  simp only [Complex.real_smul, ofReal_mul, ofReal_sub, ofReal_one, ofReal_pow]
  ring

/-- The internal project record incoming primitive is the approved internal project record
definition, literally. -/
theorem stab_curvScalarInConj_eq (e : ℝ) (D : Set (ℝ × ℝ)) (S : Fields) (u v : ℝ) :
    curvScalarInConj e D S u v = curvScalarIn e D S u v := rfl

/-- Incoming curvature decomposition in the named approved primitives. -/
theorem stab_curvature_in {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    starRingEnd ℂ (curv S u v) =
      curvScalarIn e (triangle 0 T) S u v + curvEMIn e S u v :=
  Stab.curvature_radial_representation_in hS hu huv hvT

/-- The actual j transport with its scalar and electromagnetic curvature parts
separated using internal project record. The first curvature summand is the source estimated below.
-/
theorem stab_j_transport_split {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun x => jC1 (triangle 0 T) S x v)
      (-(I * e * S.A u v * jC1 (triangle 0 T) S u v) +
        (-(‖S.xi u v‖ ^ 2 / (S.nu u v * S.r u v)) * jC1 (triangle 0 T) S u v +
          S.nu u v * S.theta u v / S.r u v ^ 2 *
            (curvScalar (triangle 0 T) S u v +
              2 * starRingEnd ℂ (curvScalar (triangle 0 T) S u v)) +
          S.nu u v * S.theta u v / S.r u v ^ 2 *
            (curvEM e S u v + 2 * starRingEnd ℂ (curvEM e S u v)) +
          emSourceJ e S u v)) (Icc 0 v) u := by
  convert bv_j_trans hS hu huv hvT using 1
  rw [Stab.curvature_radial_representation hS hu huv hvT, map_add]
  ring

/-- The actual k transport with the approved incoming scalar primitive separated
from the electromagnetic remainder. Its conjugate orientation agrees with internal project record.
-/
theorem stab_k_transport_split {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (kC1 e (triangle 0 T) S u)
      (-(‖S.theta u v‖ ^ 2 / (S.lam u v * S.r u v)) * kC1 e (triangle 0 T) S u v +
        S.lam u v * S.xi u v / S.r u v ^ 2 *
          (curvScalarIn e (triangle 0 T) S u v +
            2 * starRingEnd ℂ (curvScalarIn e (triangle 0 T) S u v)) +
        S.lam u v * S.xi u v / S.r u v ^ 2 *
          (curvEMIn e S u v + 2 * starRingEnd ℂ (curvEMIn e S u v)) +
        emSourceK e S u v) (Icc u T) v := by
  have hc := stab_curvature_in hS hu huv hvT
  have hcc := congrArg (starRingEnd ℂ) hc
  simp only [map_add, starRingEnd_self_apply] at hcc
  convert bv_k_trans hS hu huv hvT using 1
  rw [hc, hcc]
  ring

end EmcsfAcExtension.Local
