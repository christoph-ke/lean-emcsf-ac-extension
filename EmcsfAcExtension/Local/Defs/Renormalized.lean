module

public import EmcsfAcExtension.Local.Defs.Partial
public import EmcsfAcExtension.Frozen.JOut
public import EmcsfAcExtension.Frozen.KIn
public import EmcsfAcExtension.Frozen.Fields.ChargeU
public import EmcsfAcExtension.Frozen.Fields.ChargeV

/-! # Renormalized derivatives, curvature and sources

Literal internal definitions from internal project record and
`source/charged_SF_new_version.tex`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- [def-node restart-bv-j-def]
`j` of a `C¹` configuration on `D` (restart-bv-j-def, charged_SF_new_version.tex:L4516–4519): the
frozen
  `jOut` with the
within-`D` partial derivative in place of `deriv`. -/
noncomputable def jC1 (D : Set (ℝ × ℝ)) (S : Fields) (u v : ℝ) : ℂ :=
  (1 - S.mu u v) * (pdV D S.a u v -
    S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2 * (S.theta u v / S.lam u v))

/-- [def-node restart-bv-k-def]
[def-node restart-stab-k-definition]
`k` of a `C¹` configuration on `D` (restart-bv-k-def charged_SF_new_version.tex:L4520–4523,
  restart-stab-k-definition
charged_SF_new_version.tex:L4973–4979): the frozen `kIn` with the within-`D` partial derivative. -/
noncomputable def kC1 (e : ℝ) (D : Set (ℝ × ℝ)) (S : Fields) (u v : ℝ) : ℂ :=
  (1 - S.mu u v) * (pdU D S.b u v + I * e * S.A u v * S.b u v -
    S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2 * (S.xi u v / S.nu u v))

/-- [def-node restart-sec-independent-area#complex-curvature]
The complex curvature `𝒞 = μ + (1-μ) θ ξ̄ /(λν)` (charged_SF_new_version.tex:L4501–4502). -/
noncomputable def curv (S : Fields) (u v : ℝ) : ℂ :=
  S.mu u v + (1 - S.mu u v) * S.theta u v * starRingEnd ℂ (S.xi u v) / (S.lam u v * S.nu u v)

/-- [def-node restart-bv-Ej]
The exact outgoing electromagnetic source `𝓔_j` (restart-bv-Ej,
charged_SF_new_version.tex:L4540–4545), with
  `Q_v`
replaced by the right side `QV` of the outgoing Maxwell equation. -/
noncomputable def emSourceJ (e : ℝ) (S : Fields) (u v : ℝ) : ℂ :=
  (-S.nu u v) * S.lam u v / S.r u v ^ 2 *
      (5 * (S.Q u v ^ 2 / S.r u v ^ 2) * (S.theta u v / S.lam u v) +
        I * e * S.Q u v * (3 * (S.theta u v / S.lam u v) + S.phi u v)) +
    I * e * (-S.nu u v) * S.QV e u v * S.phi u v / S.r u v

/-- Unfold `emSourceJ` to its literal internal project record formula. -/
theorem emSourceJ_def (e : ℝ) (S : Fields) (u v : ℝ) :
    emSourceJ e S u v =
  (-S.nu u v) * S.lam u v / S.r u v ^ 2 *
      (5 * (S.Q u v ^ 2 / S.r u v ^ 2) * (S.theta u v / S.lam u v) +
        I * e * S.Q u v * (3 * (S.theta u v / S.lam u v) + S.phi u v)) +
    I * e * (-S.nu u v) * S.QV e u v * S.phi u v / S.r u v := rfl

/-- [def-node restart-bv-Ek]
The exact incoming electromagnetic source `𝓔_k` (restart-bv-Ek,
charged_SF_new_version.tex:L4546–4550), with
  `Q_u`
replaced by `QU`. -/
noncomputable def emSourceK (e : ℝ) (S : Fields) (u v : ℝ) : ℂ :=
  (-S.nu u v) * S.lam u v / S.r u v ^ 2 *
      (5 * (S.Q u v ^ 2 / S.r u v ^ 2) * (S.xi u v / S.nu u v) -
        I * e * S.Q u v * (3 * (S.xi u v / S.nu u v) + S.phi u v)) +
    I * e * S.lam u v * S.QU e u v * S.phi u v / S.r u v

/-- [def-node restart-bv-geom-renorm]
`𝓛 = ∂_v log λ + (λ/r)|θ/λ|²` (restart-bv-geom-renorm, charged_SF_new_version.tex:L4844–4849). -/
noncomputable def geomL (D : Set (ℝ × ℝ)) (S : Fields) (u v : ℝ) : ℝ :=
  pdV D S.lam u v / S.lam u v + S.lam u v / S.r u v * ‖S.theta u v / S.lam u v‖ ^ 2

/-- [def-node restart-bv-geom-renorm]
`𝓝 = ∂_u log(-ν) + (ν/r)|ξ/ν|²` (restart-bv-geom-renorm, charged_SF_new_version.tex:L4844–4849). -/
noncomputable def geomN (D : Set (ℝ × ℝ)) (S : Fields) (u v : ℝ) : ℝ :=
  pdU D S.nu u v / S.nu u v + S.nu u v / S.r u v * ‖S.xi u v / S.nu u v‖ ^ 2

/-- The common source `-2νλ/((1-μ)r²) (Re 𝒞 - 2Q²/r²)` of `∂_u 𝓛 = ∂_v 𝓝`
(restart-bv-geom-trans, charged_SF_new_version.tex:L4850–4855). -/
noncomputable def geomSource (S : Fields) (u v : ℝ) : ℝ :=
  -(2 * S.nu u v * S.lam u v / ((1 - S.mu u v) * S.r u v ^ 2)) *
    ((curv S u v).re - 2 * (S.Q u v ^ 2 / S.r u v ^ 2))

/-- [def-node restart-sec-bv-stability-independent#curvature-radial-representation]
Scalar part of the radial representation `𝒞 = r⁻¹∫_u^v r (ξ̄/ν) j dw + 𝒞_em`
(#curvature-radial-representation, charged_SF_new_version.tex:L5041–5046; integral of restart-bv-C-v
from the
  axis). -/
noncomputable def curvScalar (D : Set (ℝ × ℝ)) (S : Fields) (u v : ℝ) : ℂ :=
  ((S.r u v : ℂ))⁻¹ * ∫ w in u..v,
    (S.r u w : ℂ) * starRingEnd ℂ (S.xi u w / S.nu u w) * jC1 D S u w

/-- [def-node restart-bv-C-charge]
Electromagnetic part `𝒞_em = r⁻¹∫_u^v (λQ²/r² - ieQθφ̄) dw` (restart-bv-C-charge,
  charged_SF_new_version.tex:L4654–4659). -/
noncomputable def curvEM (e : ℝ) (S : Fields) (u v : ℝ) : ℂ :=
  ((S.r u v : ℂ))⁻¹ * ∫ w in u..v,
    (((S.lam u w * S.Q u w ^ 2 / S.r u w ^ 2 : ℝ)) : ℂ) -
      I * e * S.Q u w * S.theta u w * starRingEnd ℂ (S.phi u w)

/-- [def-node restart-bv-C-u]
Incoming scalar curvature primitive, integrated backwards from the axis point `(v,v)`
(charged_SF_new_version.tex:L4536–4538, internal project record). The identity
`conj 𝒞 = curvScalarIn + curvEMIn` off the axis is a separate calculus theorem. -/
noncomputable def curvScalarIn (e : ℝ) (D : Set (ℝ × ℝ)) (S : Fields) (u v : ℝ) : ℂ :=
  -(((S.r u v : ℂ))⁻¹ * ∫ s in u..v,
    (S.r s v : ℂ) * starRingEnd ℂ (S.theta s v / S.lam s v) * kC1 e D S s v)

/-- [def-node restart-sec-independent-area#incoming-curvature-charge]
Incoming electromagnetic curvature primitive, integrated backwards from `(v,v)`
(charged_SF_new_version.tex:L4660, internal project record). -/
noncomputable def curvEMIn (e : ℝ) (S : Fields) (u v : ℝ) : ℂ :=
  -(((S.r u v : ℂ))⁻¹ * ∫ s in u..v,
    ((((S.nu s v * S.Q s v ^ 2 / S.r s v ^ 2 : ℝ)) : ℂ) +
      I * e * S.Q s v * S.xi s v * starRingEnd ℂ (S.phi s v)))

end EmcsfAcExtension.Local
