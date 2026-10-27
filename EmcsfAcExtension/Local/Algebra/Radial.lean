module

public import Mathlib

/-! # Algebraic cores of the radial reconstruction identities

All derivative symbols are abstract values. The reconstruction identities use only the
definitions of `j`, `k` and the scalar constraint; the cross-direction identities use the
reduced wave, radius and mass equations. See `charged_SF_new_version.tex:L5000`–L5010 and
L5444–L5448,
and the approved internal project record verification in internal project record.
-/

public section

namespace EmcsfAcExtension.Local

open Complex

/-- [node restart-stab-out-reconstruction]
The exact outgoing damped radial equation from the definition of `j`.
`ratioV` denotes `∂ᵥ(θ/λ)`; `r`, `λ` and `1-μ` must be nonzero. -/
theorem stab_out_reconstruction_algebra
    {r lam mu : ℝ} {theta phiV ratioV j : ℂ}
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hmu : 1 - mu ≠ 0)
    (hphiV : phiV = theta / r)
    (hj : j = (1 - (mu : ℂ)) *
      (phiV + ratioV - (lam / r : ℝ) * ‖theta / lam‖ ^ 2 * (theta / lam))) :
    ratioV + (lam / r : ℝ) * (1 - ‖theta / lam‖ ^ 2) * (theta / lam) =
      j / (1 - (mu : ℂ)) := by
  rw [hj, hphiV]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  have hmuC : 1 - (mu : ℂ) ≠ 0 := by exact_mod_cast hmu
  push_cast
  field_simp [hrC, hlamC, hmuC]
  ring

/-- [node restart-stab-in-reconstruction]
The exact incoming covariant damped radial equation from the definition of `k`.
`ratioU` denotes `∂ᵤ(ξ/ν)` (`charged_SF_new_version.tex:L5006`). -/
theorem stab_in_reconstruction_algebra
    {r nu mu e A : ℝ} {phi xi phiU ratioU k : ℂ}
    (hr : r ≠ 0) (hnu : nu ≠ 0) (hmu : 1 - mu ≠ 0)
    (hphiU : phiU = xi / r - I * e * A * phi)
    (hk : k = (1 - (mu : ℂ)) *
      (phiU + ratioU + I * e * A * (phi + xi / nu) -
        (nu / r : ℝ) * ‖xi / nu‖ ^ 2 * (xi / nu))) :
    ratioU + I * e * A * (xi / nu) +
        (nu / r : ℝ) * (1 - ‖xi / nu‖ ^ 2) * (xi / nu) =
      k / (1 - (mu : ℂ)) := by
  rw [hk, hphiU]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hnuC : (nu : ℂ) ≠ 0 := by exact_mod_cast hnu
  have hmuC : 1 - (mu : ℂ) ≠ 0 := by exact_mod_cast hmu
  push_cast
  field_simp [hrC, hnuC, hmuC]
  ring

/-- [node restart-stab-out-reconstruction]
The outgoing reconstruction equation with radius as independent variable.
This is the `radial theta/lambda identity` in the internal project record audit. -/
theorem radial_theta_div_lam_algebra
    {r lam mu : ℝ} {theta phiV ratioV j : ℂ}
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hmu : 1 - mu ≠ 0)
    (hphiV : phiV = theta / r)
    (hj : j = (1 - (mu : ℂ)) *
      (phiV + ratioV - (lam / r : ℝ) * ‖theta / lam‖ ^ 2 * (theta / lam))) :
    ratioV / lam = j / ((1 - (mu : ℂ)) * lam) -
      (1 - ‖theta / lam‖ ^ 2) / r * (theta / lam) := by
  rw [hj, hphiV]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  have hmuC : 1 - (mu : ℂ) ≠ 0 := by exact_mod_cast hmu
  push_cast
  field_simp [hrC, hlamC, hmuC]
  ring

/-- [node restart-stab-in-reconstruction]
The outgoing radial derivative of the incoming ratio, obtained from `ξᵥ` and `νᵥ`.
All four displayed denominators are assumed nonzero. -/
theorem radial_xi_div_nu_algebra
    {r lam nu mu Q e nuV : ℝ} {phi theta xi xiV : ℂ}
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hnu : nu ≠ 0) (hmu : 1 - mu ≠ 0)
    (hnuV : nuV = nu * lam / r * ((mu - Q ^ 2 / r ^ 2) / (1 - mu)))
    (hxiV : xiV = -(nu * theta / r) +
      I * e * Q * phi * nu * lam / ((1 - mu) * r)) :
    ((xiV * nu - xi * nuV) / (nu : ℂ) ^ 2) / lam =
      -(theta / lam) / r -
        ((mu : ℂ) - Q ^ 2 / (r : ℂ) ^ 2) / ((1 - mu) * r) * (xi / nu) +
          I * e * Q * phi / ((1 - mu) * r) := by
  rw [hnuV, hxiV]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  have hnuC : (nu : ℂ) ≠ 0 := by exact_mod_cast hnu
  have hmuC : 1 - (mu : ℂ) ≠ 0 := by exact_mod_cast hmu
  push_cast
  field_simp [hrC, hlamC, hnuC, hmuC]
  ring

/-- [node restart-stab-in-reconstruction]
The radial logarithmic derivative of `-ν` from the radius equation.
No sign assumptions are needed for this algebraic quotient identity. -/
theorem radial_log_neg_nu_algebra {r lam nu mu Q nuV : ℝ}
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hnu : nu ≠ 0) (hmu : 1 - mu ≠ 0)
    (hnuV : nuV = nu * lam / r * ((mu - Q ^ 2 / r ^ 2) / (1 - mu))) :
    nuV / (nu * lam) = (mu - Q ^ 2 / r ^ 2) / ((1 - mu) * r) := by
  rw [hnuV]
  field_simp [hr, hlam, hnu, hmu]

/-- [node restart-sec-bv-stability-independent#outgoing-mu-derivative-identity]
The outgoing derivative of `μ = 2m/r`, after the quotient rule and mass constraint.
Only `r` and `λ` must be nonzero; `1-μ` may vanish in this identity. -/
theorem Stab.outgoing_mu_derivative_identity_algebra {r lam m Q mV : ℝ} {theta : ℂ}
    (hr : r ≠ 0) (hlam : lam ≠ 0)
    (hmV : mV = (1 - 2 * m / r) * ‖theta‖ ^ 2 / (2 * lam) +
      Q ^ 2 * lam / (2 * r ^ 2)) :
    2 * mV / r - 2 * m * lam / r ^ 2 =
      lam / r * ((1 - 2 * m / r) * ‖theta / lam‖ ^ 2 + Q ^ 2 / r ^ 2 - 2 * m / r) := by
  rw [hmV, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  field_simp [hr, hlam]

/-- [node restart-stab-out-reconstruction]
The radial mass-ratio equation, i.e. `λ⁻¹∂ᵥμ`.
Only `r` and `λ` must be nonzero. -/
theorem radial_mu_algebra {r lam m Q mV : ℝ} {theta : ℂ}
    (hr : r ≠ 0) (hlam : lam ≠ 0)
    (hmV : mV = (1 - 2 * m / r) * ‖theta‖ ^ 2 / (2 * lam) +
      Q ^ 2 * lam / (2 * r ^ 2)) :
    (2 * mV / r - 2 * m * lam / r ^ 2) / lam =
      ((1 - 2 * m / r) * ‖theta / lam‖ ^ 2 + Q ^ 2 / r ^ 2 - 2 * m / r) / r := by
  rw [Stab.outgoing_mu_derivative_identity_algebra hr hlam hmV]
  field_simp [hr, hlam]

end EmcsfAcExtension.Local
