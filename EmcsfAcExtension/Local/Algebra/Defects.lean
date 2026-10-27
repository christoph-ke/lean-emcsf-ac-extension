module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Algebraic wave recovery and incoming constraint defects

The computations of `charged_SF_new_version.tex:L6148–6198`, following the approved internal project
record
symbolic verification. All values live in an arbitrary field of characteristic
zero, `g = ie`, and suffix `b` denotes an independent conjugate atom.
Covariant scalar derivatives are used inside gauge invariant products; their
connection terms cancel. The calculus layer supplies actual derivatives and
mixed-partial commutation. In particular, this module assumes neither
incoming constraint: the mass and charge errors `E`, `Z` are arbitrary.
-/

public section

namespace EmcsfAcExtension.Local.Null

/-- [node restart-sec-independent-null-construction#rphi-wave-identity]
Algebraic core of the charged wave equation for `rφ`
(`charged_SF_new_version.tex:L6148–6157`). `y = θ/λ`, so `φ+y = α/λ`.
The left side is `D_u(λ(φ+y))`, using the radius mixed derivative and
normalized outgoing transport. No incoming mass or Maxwell constraint is used. -/
theorem rphi_wave_identity_algebra {K : Type*} [Field K] [CharZero K]
    (r lam nu mu q g phi y : K) (hr : r ≠ 0) (hmu : 1 - mu ≠ 0) :
    let H := 1 - mu
    let B := mu - q ^ 2 / r ^ 2
    let lamU := nu * lam * B / (r * H)
    lamU * (phi + y) + lam * (-nu / r * (B / H * y + g * q / H * phi)) =
      nu * lam / (H * r ^ 2) * (B - g * q) * (r * phi) := by
  dsimp
  field_simp [hr, hmu]
  ring

/-- [node restart-sec-independent-null-construction#rphi-wave-identity]
Recovery of the first-order `D_u θ` source from the `rφ` wave identity.
Subtracting `r_uv φ` and `λ D_uφ` from `D_u∂_v(rφ)` leaves the exact
covariant theta transport (`charged_SF_new_version.tex:L6154–6157`). -/
theorem rphi_wave_theta_algebra {K : Type*} [Field K] [CharZero K]
    (r lam nu mu q g phi xi : K) (hr : r ≠ 0) (hmu : 1 - mu ≠ 0) :
    let H := 1 - mu
    let B := mu - q ^ 2 / r ^ 2
    let wave := nu * lam / (H * r ^ 2) * (B - g * q) * (r * phi)
    wave - nu * lam * B / (r * H) * phi - lam * xi / r =
      -lam * xi / r - g * q * phi * nu * lam / (H * r) := by
  dsimp
  field_simp [hr, hmu]
  ring

/-- [node restart-sec-independent-null-construction#rphi-wave-identity]
Recovery of `∂_v ξ`, including the commutator contribution `r ie A_v φ`.
This checks the opposite signs of the charged theta and xi transports
(`charged_SF_new_version.tex:L6154–6157`). -/
theorem rphi_wave_xi_algebra {K : Type*} [Field K] [CharZero K]
    (r lam nu mu q g phi theta xi : K)
    (hr : r ≠ 0) (hmu : 1 - mu ≠ 0) :
    let H := 1 - mu
    let thetaU := -lam * xi / r - g * q * phi * nu * lam / (H * r)
    let potentialV := 2 * nu * lam * q / (H * r ^ 2)
    lam * xi / r + thetaU - nu * theta / r + r * g * potentialV * phi =
      -nu * theta / r + g * q * phi * nu * lam / (H * r) := by
  dsimp
  field_simp [hr, hmu]
  ring

/-- [node restart-sec-independent-null-construction#defect-transport]
Algebraic core of `Z_v = 0` (`charged_SF_new_version.tex:L6183–6196`). `qvU` and
`quV` are the differentiated outgoing and incoming Maxwell sources, with
scalar derivatives replaced by their covariant wave equations. Their
difference vanishes without either incoming constraint or a prescribed
value of `Q_u`; the Maxwell sources themselves do not depend on `Q`. -/
theorem defect_transport_charge_algebra {K : Type*} [Field K] [CharZero K]
    (r lam nu mu q g phi phib theta thetab xi xib : K)
    (hr : r ≠ 0) (hmu : 1 - mu ≠ 0) :
    let H := 1 - mu
    let thetaU := -lam * xi / r - g * q * phi * nu * lam / (H * r)
    let thetabU := -lam * xib / r + g * q * phib * nu * lam / (H * r)
    let xiV := -nu * theta / r + g * q * phi * nu * lam / (H * r)
    let xibV := -nu * thetab / r - g * q * phib * nu * lam / (H * r)
    let qvU := g / 2 * (nu * (phib * theta - phi * thetab) +
      r * (xib / r * theta + phib * thetaU - xi / r * thetab - phi * thetabU))
    let quV := -g / 2 * (lam * (phib * xi - phi * xib) +
      r * (thetab / r * xi + phib * xiV - theta / r * xib - phi * xibV))
    qvU - quV = 0 := by
  dsimp
  field_simp [hr, hmu]
  ring

/-- [node restart-sec-independent-null-construction#defect-transport]
Algebraic core of `E_v = -|θ|² E/(λr) + λQZ/r²`
(`charged_SF_new_version.tex:L6183–6198`). The differentiated outgoing mass equation
uses `m_u = mU + E` and `Q_u = qu + Z`, with arbitrary errors `E`, `Z`.
`mvU - muV` is exactly the mixed mass defect after commuting derivatives.
The coefficient of `E` contains no factor of `1-μ`. -/
theorem defect_transport_mass_algebra {K : Type*} [Field K] [CharZero K]
    (r lam nu mu q g phi phib theta thetab xi xib E Z : K)
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hnu : nu ≠ 0) (hmu : 1 - mu ≠ 0) :
    let H := 1 - mu
    let B := mu - q ^ 2 / r ^ 2
    let mU := H * xib * xi / (2 * nu) + q ^ 2 * nu / (2 * r ^ 2)
    let mV := H * thetab * theta / (2 * lam) + q ^ 2 * lam / (2 * r ^ 2)
    let qu := -g * r / 2 * (phib * xi - phi * xib)
    let qv := g * r / 2 * (phib * theta - phi * thetab)
    let radiusUV := nu * lam * B / (r * H)
    let HU := (mu * nu - 2 * (mU + E)) / r
    let HV := (mu * lam - 2 * mV) / r
    let thetaU := -lam * xi / r - g * q * phi * nu * lam / (H * r)
    let thetabU := -lam * xib / r + g * q * phib * nu * lam / (H * r)
    let xiV := -nu * theta / r + g * q * phi * nu * lam / (H * r)
    let xibV := -nu * thetab / r - g * q * phib * nu * lam / (H * r)
    let mvU := (HU * thetab * theta + H * (thetabU * theta + thetab * thetaU)) /
        (2 * lam) - H * thetab * theta * radiusUV / (2 * lam ^ 2) +
      q * (qu + Z) * lam / r ^ 2 + q ^ 2 * radiusUV / (2 * r ^ 2) -
      q ^ 2 * lam * nu / r ^ 3
    let muV := (HV * xib * xi + H * (xibV * xi + xib * xiV)) /
        (2 * nu) - H * xib * xi * radiusUV / (2 * nu ^ 2) +
      q * qv * nu / r ^ 2 + q ^ 2 * radiusUV / (2 * r ^ 2) -
      q ^ 2 * nu * lam / r ^ 3
    mvU - muV = -(thetab * theta / (lam * r)) * E + lam * q / r ^ 2 * Z := by
  dsimp
  field_simp [hr, hlam, hnu, hmu]
  ring

end EmcsfAcExtension.Local.Null
