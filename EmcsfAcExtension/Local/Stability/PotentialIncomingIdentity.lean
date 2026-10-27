module

public import EmcsfAcExtension.Local.Defs.Renormalized
public import EmcsfAcExtension.Local.Defs.C1Class
import EmcsfAcExtension.Local.Stability.GeomStrongMassInRaw
import EmcsfAcExtension.Local.Calculus.Normalized

/-! # Cancellation in the incoming potential density

The incoming derivative of the outgoing potential integrand has the
three terms of approved internal project record A11p. The quadratic scalar terms and
the mass/charge correction cancel before any singular integration.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- [internal]
The smooth local incoming differentiation identity for the potential
constraint, internal project record A11p and charged_SF_new_version.tex:L5453–5513. There is no
estimate constant, no second-derivative premise, and no division by
charge or the scalar field. The full general-AC potential strong-limit
record is reserved for internal project record.
-/
theorem Stab.potential_constraint_incoming_derivative_c1
    {e T : ℝ} {S : Fields} (hS : IsC1Solution e S (triangle 0 T))
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    HasDerivWithinAt (fun t => S.AV t v)
      (S.AV u v * geomN (triangle 0 T) S u v -
        2 * S.nu u v / S.r u v * S.AV u v +
        2 * e * S.nu u v ^ 2 * S.lam u v /
          ((1 - S.mu u v) * S.r u v) *
            (starRingEnd ℂ (S.phi u v) * (S.xi u v / (S.nu u v : ℂ))).im)
      (Icc 0 v) u := by
  have hp : (u, v) ∈ triangle 0 T := ⟨hu, huv.le, hvT⟩
  have hr := (hS.r_pos _ hp huv).ne'
  have hn := (hS.nu_neg _ hp).ne
  have hg := (hS.one_sub_mu_pos _ hp).ne'
  have dν := hasDerivWithinAt_u_aux hS.c1_nu hu huv.le hvT
  have dLam := hasDerivWithinAt_u_aux hS.c1_lam hu huv.le hvT
  have dQ := hasDerivWithinAt_u_aux hS.c1_Q hu huv.le hvT
  have dr := hasDerivWithinAt_u_aux hS.c1_r hu huv.le hvT
  have dμ := Stab.incoming_mu_derivative_identity_c1 hS hu huv hvT
  have hd := (((dν.const_mul 2).mul dLam).mul dQ).div
    (((hasDerivWithinAt_const u (Icc 0 v) (1 : ℝ)).sub dμ).mul (dr.pow 2))
    (mul_ne_zero hg (pow_ne_zero 2 hr))
  apply hd.congr_deriv
  rw [(hS.eq_u _ hp huv).1, (hS.eq_u _ hp huv).2.1,
    (hS.eq_u _ hp huv).2.2.2.1]
  dsimp only [Fields.AV, Fields.rUV, Fields.QU, geomN]
  rw [← mul_div_assoc (starRingEnd ℂ (S.phi u v)), Complex.div_ofReal_im]
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Nat.reduceSub, pow_one,
    Nat.cast_ofNat, zero_sub]
  field_simp
  ring

end EmcsfAcExtension.Local
