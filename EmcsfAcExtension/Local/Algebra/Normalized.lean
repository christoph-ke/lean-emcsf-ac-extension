module

public import Mathlib

/-! # Algebraic cores of the normalized transports

The values with a `U` or `V` suffix stand for partial derivatives. No differentiability or
field configuration is assumed. The equations are those of `charged_SF_new_version.tex:L4328`–L4335;
the substitution proof follows the approved internal project record symbolic audit.
-/

public section

namespace EmcsfAcExtension.Local

open Complex

/-- [node restart-eq-normalized]
Incoming covariant transport of `α/λ = φ + θ/λ`, after the quotient rule.
Only `r`, `λ` and `1-μ` must be nonzero (`charged_SF_new_version.tex:L4328`). -/
theorem eq_normalized_in_algebra
    {r lam nu mu Q e A lamU : ℝ} {phi theta xi phiU thetaU : ℂ}
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hmu : 1 - mu ≠ 0)
    (hlamU : lamU = nu * lam / r * ((mu - Q ^ 2 / r ^ 2) / (1 - mu)))
    (hphiU : phiU = xi / r - I * e * A * phi)
    (hthetaU : thetaU = -(I * e * A * theta) - lam * xi / r -
      I * e * Q * phi * nu * lam / ((1 - mu) * r)) :
    phiU + (thetaU * lam - theta * lamU) / (lam : ℂ) ^ 2 +
        I * e * A * (phi + theta / lam) =
      (-(nu : ℂ) / r) *
        (((mu : ℂ) - Q ^ 2 / (r : ℂ) ^ 2) / (1 - mu) * (theta / lam) +
          I * e * Q * phi / (1 - mu)) := by
  rw [hphiU, hthetaU, hlamU]
  push_cast
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  have hmuC : 1 - (mu : ℂ) ≠ 0 := by exact_mod_cast hmu
  field_simp [hrC, hlamC, hmuC]
  ring

/-- [node restart-eq-normalized]
Outgoing transport of `β/ν = φ + ξ/ν`, after the quotient rule.
Only `r`, `ν` and `1-μ` must be nonzero (`charged_SF_new_version.tex:L4332`). -/
theorem eq_normalized_out_algebra
    {r lam nu mu Q e nuV : ℝ} {phi theta xi phiV xiV : ℂ}
    (hr : r ≠ 0) (hnu : nu ≠ 0) (hmu : 1 - mu ≠ 0)
    (hnuV : nuV = nu * lam / r * ((mu - Q ^ 2 / r ^ 2) / (1 - mu)))
    (hphiV : phiV = theta / r)
    (hxiV : xiV = -(nu * theta / r) +
      I * e * Q * phi * nu * lam / ((1 - mu) * r)) :
    phiV + (xiV * nu - xi * nuV) / (nu : ℂ) ^ 2 =
      (-(lam : ℂ) / r) *
        (((mu : ℂ) - Q ^ 2 / (r : ℂ) ^ 2) / (1 - mu) * (xi / nu) -
          I * e * Q * phi / (1 - mu)) := by
  rw [hphiV, hxiV, hnuV]
  push_cast
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hnuC : (nu : ℂ) ≠ 0 := by exact_mod_cast hnu
  have hmuC : 1 - (mu : ℂ) ≠ 0 := by exact_mod_cast hmu
  field_simp [hrC, hnuC, hmuC]
  ring

end EmcsfAcExtension.Local
