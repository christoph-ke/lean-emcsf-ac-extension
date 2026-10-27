module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Algebraic complex curvature primitives

The rational identities of `charged_SF_new_version.tex:L4533–4538`, using the internal project
record
verification in W4 internal project record. All conjugates are independent atoms:
`thetab`, `xib`, `phib` stand for the conjugates of `theta`, `xi`, `phi`,
and `g = ie`. No differential or regularity claim is made here.

Unlike the normalized transport core, these formulas use the original scalar
jets and therefore explicitly require `r`, `λ`, `ν`, `1-μ` to be nonzero.
-/

public section

namespace EmcsfAcExtension.Local

/-- [node restart-bv-C-v]
Algebraic core of the outgoing curvature primitive (`charged_SF_new_version.tex:L4533–4535`).
`thetaV` and `lamV` are arbitrary outgoing derivative values; the other
derivatives are replaced by the mass, radius and conjugate scalar equations.
`dC` is the quotient rule for `∂_v 𝒞`, and `j` is exactly the outgoing
renormalized derivative after substituting `φ_v = θ/r`. -/
theorem bv_c_v_algebra {K : Type*} [Field K] [CharZero K]
    (r lam nu mu q g theta thetab xib phib thetaV lamV : K)
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hnu : nu ≠ 0) (hmu : 1 - mu ≠ 0) :
    let H := 1 - mu
    let B := mu - q ^ 2 / r ^ 2
    let muV := (H * thetab * theta / lam + q ^ 2 * lam / r ^ 2 - mu * lam) / r
    let nuV := nu * lam * B / (r * H)
    let xibV := -nu * thetab / r - g * q * phib * nu * lam / (H * r)
    let C := mu + H * theta * xib / (lam * nu)
    let dC := muV - muV * theta * xib / (lam * nu) +
      H * thetaV * xib / (lam * nu) + H * theta * xibV / (lam * nu) -
      H * theta * xib * (lamV * nu + lam * nuV) / (lam * nu) ^ 2
    let j := H * (theta / r + thetaV / lam - theta * lamV / lam ^ 2 -
      lam / r * (thetab / lam) * (theta / lam) * (theta / lam))
    lam * C + r * dC = r * xib / nu * j + lam * q ^ 2 / r ^ 2 -
      g * q * theta * phib := by
  dsimp
  field_simp [hr, hlam, hnu, hmu]
  ring

/-- [node restart-bv-C-u]
Algebraic core of the incoming conjugate curvature primitive
(`charged_SF_new_version.tex:L4536–4538`). `xiU` is the covariant derivative `D_u ξ`;
the conjugate curvature product is gauge invariant, so its derivative has
the displayed ordinary product rule. `k` is the exact incoming renormalized
derivative after substituting `D_u φ = ξ/r`. -/
theorem bv_c_u_algebra {K : Type*} [Field K] [CharZero K]
    (r lam nu mu q g thetab xi xib phib xiU nuU : K)
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hnu : nu ≠ 0) (hmu : 1 - mu ≠ 0) :
    let H := 1 - mu
    let B := mu - q ^ 2 / r ^ 2
    let muU := (H * xib * xi / nu + q ^ 2 * nu / r ^ 2 - mu * nu) / r
    let lamU := nu * lam * B / (r * H)
    let thetabU := -lam * xib / r + g * q * phib * nu * lam / (H * r)
    let Cbar := mu + H * xi * thetab / (nu * lam)
    let dCbar := muU - muU * xi * thetab / (nu * lam) +
      H * xiU * thetab / (nu * lam) + H * xi * thetabU / (nu * lam) -
      H * xi * thetab * (nuU * lam + nu * lamU) / (nu * lam) ^ 2
    let k := H * (xi / r + xiU / nu - xi * nuU / nu ^ 2 -
      nu / r * (xib / nu) * (xi / nu) * (xi / nu))
    nu * Cbar + r * dCbar = r * thetab / lam * k + nu * q ^ 2 / r ^ 2 +
      g * q * xi * phib := by
  dsimp
  field_simp [hr, hlam, hnu, hmu]
  ring

end EmcsfAcExtension.Local
