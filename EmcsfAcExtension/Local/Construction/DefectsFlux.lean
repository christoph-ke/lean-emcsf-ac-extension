module

public import EmcsfAcExtension.Local.Defs.Recon
public import EmcsfAcExtension.Local.Algebra.Defects

/-! # Actual first derivatives of the charge and mass fluxes

These product and quotient rules connect the differentiated primitive
sources to the landed algebraic defect cores. Conjugates are independent
curves in the rules and are specialized to actual conjugates by `star`.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Null

/-- The frozen negative imaginary current equals its complex conjugate
atom form. This identity is used for both Maxwell flux directions. -/
theorem negative_current_eq_complex (e r : ℝ) (phi psi : ℂ) :
    ((-(e * r * (starRingEnd ℂ phi * psi).im) : ℝ) : ℂ) =
      I * e * r / 2 * (starRingEnd ℂ phi * psi - phi * starRingEnd ℂ psi) := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  ring

/-- The real mass flux equals its literal conjugate-atom expression after
inclusion into ℂ. This identity is valid also at totalized zero denominators. -/
theorem mass_flux_eq_complex (d lam q r : ℝ) (psi : ℂ) :
    ((d * ‖psi‖ ^ 2 / (2 * lam) + q ^ 2 * lam / (2 * r ^ 2) : ℝ) : ℂ) =
      (d : ℂ) * starRingEnd ℂ psi * psi / (2 * (lam : ℂ)) +
        (q : ℂ) ^ 2 * lam / (2 * (r : ℂ) ^ 2) := by
  push_cast
  simp only [mul_assoc, Complex.conj_mul']

/-- Differentiate the actual conjugate-atom charge flux. All supplied jets
are first derivatives; no commutation or second derivative is assumed. -/
theorem hasDerivWithinAt_charge_flux {s : Set ℝ} {x : ℝ}
    {R P Pb T Tb : ℝ → ℂ} {r' p' pb' t' tb' : ℂ}
    (g : ℂ) (dR : HasDerivWithinAt R r' s x)
    (dP : HasDerivWithinAt P p' s x) (dPb : HasDerivWithinAt Pb pb' s x)
    (dT : HasDerivWithinAt T t' s x) (dTb : HasDerivWithinAt Tb tb' s x) :
    HasDerivWithinAt (fun y => g / 2 * (R y * (Pb y * T y - P y * Tb y)))
      (g / 2 * (r' * (Pb x * T x - P x * Tb x) +
        R x * (pb' * T x + Pb x * t' - p' * Tb x - P x * tb'))) s x := by
  convert (dR.mul ((dPb.mul dT).sub (dP.mul dTb))).const_mul (g / 2) using 1
  simp only [Pi.mul_apply, Pi.sub_apply]
  ring

/-- Differentiate the actual complex mass flux with arbitrary first jets.
The two nonzero premises are exactly the radius and expansion divisors.
This is the product/quotient expansion substituted in the mass defect core. -/
theorem hasDerivWithinAt_mass_flux {s : Set ℝ} {x : ℝ}
    {R L H Q T Tb : ℝ → ℂ} {r' l' h' q' t' tb' : ℂ}
    (hr : R x ≠ 0) (hl : L x ≠ 0)
    (dR : HasDerivWithinAt R r' s x) (dL : HasDerivWithinAt L l' s x)
    (dH : HasDerivWithinAt H h' s x) (dQ : HasDerivWithinAt Q q' s x)
    (dT : HasDerivWithinAt T t' s x) (dTb : HasDerivWithinAt Tb tb' s x) :
    HasDerivWithinAt
      (fun y => H y * Tb y * T y / (2 * L y) + Q y ^ 2 * L y / (2 * R y ^ 2))
      ((h' * Tb x * T x + H x * (tb' * T x + Tb x * t')) / (2 * L x) -
          H x * Tb x * T x * l' / (2 * L x ^ 2) +
        Q x * q' * L x / R x ^ 2 + Q x ^ 2 * l' / (2 * R x ^ 2) -
          Q x ^ 2 * L x * r' / R x ^ 3) s x := by
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have dkin := ((dH.mul dTb).mul dT).div ((hasDerivWithinAt_const x s (2 : ℂ)).mul dL)
    (mul_ne_zero htwo hl)
  have del := ((dQ.pow 2).mul dL).div
    ((hasDerivWithinAt_const x s (2 : ℂ)).mul (dR.pow 2))
    (mul_ne_zero htwo (pow_ne_zero 2 hr))
  convert dkin.add del using 1
  simp only [Pi.mul_apply, Pi.pow_apply]
  field_simp [hr, hl]
  ring

end EmcsfAcExtension.Local.Null
