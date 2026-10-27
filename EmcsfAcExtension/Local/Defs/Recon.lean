module

public import EmcsfAcExtension.Local.Defs.Partial
public import EmcsfAcExtension.Frozen.Fields.MassU
public import EmcsfAcExtension.Frozen.Fields.ChargeU

/-! # Radial reconstruction and incoming defects

Literal internal definitions from internal project record and
`source/charged_SF_new_version.tex`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

namespace Recon

variable (e : ℝ) (lam : ℝ → ℝ → ℝ) (hh : ℝ → ℝ → ℂ)

/-- [def-node restart-null-reconstruct-rphi]
`r(u,v) = ∫_u^v λ(u,s) ds` (restart-null-reconstruct-rphi, charged_SF_new_version.tex:L5949). -/
noncomputable def r (u v : ℝ) : ℝ := ∫ s in u..v, lam u s

/-- Unfold `r` to its literal internal project record formula. -/
theorem r_def (u v : ℝ) :
    r lam u v =
  ∫ s in u..v, lam u s := rfl

/-- [def-node restart-null-reconstruct-rphi]
[def-node restart-sec-independent-null-construction#scalar-axis-value]
`φ = r⁻¹ ∫_u^v λ (α/λ) ds` off the axis (charged_SF_new_version.tex:L5950–5953); on the axis the
source
  assigns the value
`(α/λ)(u,u)` (restart-sec-independent-null-construction#scalar-axis-value,
charged_SF_new_version.tex:L5958). -/
noncomputable def phi (u v : ℝ) : ℂ :=
  if u < v then ((r lam u v : ℝ) : ℂ)⁻¹ * ∫ s in u..v, (lam u s : ℂ) * hh u s else hh u u

/-- Unfold `phi` to its literal internal project record formula. -/
theorem phi_def (u v : ℝ) :
    phi lam hh u v =
  if u < v then ((r lam u v : ℝ) : ℂ)⁻¹ * ∫ s in u..v, (lam u s : ℂ) * hh u s else hh u u := rfl

/-- `θ/λ = α/λ - φ` for the reconstructed scalar. -/
noncomputable def ratio (u v : ℝ) : ℂ := hh u v - phi lam hh u v

/-- Unfold `ratio` to its literal internal project record formula. -/
theorem ratio_def (u v : ℝ) :
    ratio lam hh u v =
  hh u v - phi lam hh u v := rfl

/-- [def-node restart-null-reconstruct-charge]
`Q(u,v) = -e ∫_u^v r λ Im(φ̄ α/λ) ds` (restart-null-reconstruct-charge,
  charged_SF_new_version.tex:L5954–5957). -/
noncomputable def Q (u v : ℝ) : ℝ :=
  -(e * ∫ s in u..v, r lam u s * lam u s * (starRingEnd ℂ (phi lam hh u s) * hh u s).im)

/-- Unfold `Q` to its literal internal project record formula. -/
theorem q_def (u v : ℝ) :
    Q e lam hh u v =
  -(e * ∫ s in u..v, r lam u s * lam u s * (starRingEnd ℂ (phi lam hh u s) * hh u s).im) := rfl

/-- [def-node restart-null-reconstruct-mass]
The integrating-factor mass (restart-null-reconstruct-mass, charged_SF_new_version.tex:L5959–5965).
-/
noncomputable def m (u v : ℝ) : ℝ :=
  (1 / 2) * ∫ s in u..v, lam u s * (‖ratio lam hh u s‖ ^ 2 + Q e lam hh u s ^ 2 / r lam u s ^ 2) *
    Real.exp (-∫ t in s..v, lam u t * ‖ratio lam hh u t‖ ^ 2 / r lam u t)

/-- Unfold `m` to its literal internal project record formula. -/
theorem m_def (u v : ℝ) :
    m e lam hh u v =
  (1 / 2) * ∫ s in u..v, lam u s * (‖ratio lam hh u s‖ ^ 2 + Q e lam hh u s ^ 2 / r lam u s ^ 2) *
    Real.exp (-∫ t in s..v, lam u t * ‖ratio lam hh u t‖ ^ 2 / r lam u t) := rfl

/-- `μ = 2m/r` for the reconstruction. -/
noncomputable def mu (u v : ℝ) : ℝ := 2 * m e lam hh u v / r lam u v

/-- Unfold `mu` to its literal internal project record formula. -/
theorem mu_def (u v : ℝ) :
    mu e lam hh u v =
  2 * m e lam hh u v / r lam u v := rfl

/-- `z = (μ - Q²/r²)/(1-μ)` (the temporary letter of charged_SF_new_version.tex:L4861, used in the
  transports). -/
noncomputable def z (u v : ℝ) : ℝ :=
  (mu e lam hh u v - Q e lam hh u v ^ 2 / r lam u v ^ 2) / (1 - mu e lam hh u v)

/-- Unfold `z` to its literal internal project record formula. -/
theorem z_def (u v : ℝ) :
    z e lam hh u v =
  (mu e lam hh u v - Q e lam hh u v ^ 2 / r lam u v ^ 2) / (1 - mu e lam hh u v) := rfl

/-- [def-node restart-null-reconstruct-nu]
`ν = -λ(u,u) exp ∫_u^v (λ/r) z ds` (restart-null-reconstruct-nu,
charged_SF_new_version.tex:L5966–5971). -/
noncomputable def nu (u v : ℝ) : ℝ :=
  -lam u u * Real.exp (∫ s in u..v, lam u s / r lam u s * z e lam hh u s)

/-- Unfold `nu` to its literal internal project record formula. -/
theorem nu_def (u v : ℝ) :
    nu e lam hh u v =
  -lam u u * Real.exp (∫ s in u..v, lam u s / r lam u s * z e lam hh u s) := rfl

/-- [def-node restart-null-reconstruct-potential]
`A_u = ∫_u^v 2νλQ/((1-μ)r²) ds` (restart-null-reconstruct-potential,
charged_SF_new_version.tex:L5972–5974). -/
noncomputable def A (u v : ℝ) : ℝ :=
  ∫ s in u..v, 2 * nu e lam hh u s * lam u s * Q e lam hh u s /
    ((1 - mu e lam hh u s) * r lam u s ^ 2)

/-- Unfold `A` to its literal internal project record formula. -/
theorem a_def (u v : ℝ) :
    A e lam hh u v =
  ∫ s in u..v, 2 * nu e lam hh u s * lam u s * Q e lam hh u s /
    ((1 - mu e lam hh u s) * r lam u s ^ 2) := rfl

/-- The configuration reconstructed from a candidate pair `(λ, α/λ)`
(charged_SF_new_version.tex:L5947–5974,
  charged_SF_new_version.tex:L6148):
`θ = λ(α/λ - φ)` (equal to `r∂_vφ` by the radial formula) and `ξ` as the outgoing primitive of its
transport `∂_vξ = -νθ/r + ieQφνλ/((1-μ)r)` from `ξ = 0` on the axis; that this `ξ` equals
`r D_u φ` is the content of #first-order-wave-system. -/
noncomputable def toFields : Fields where
  r := r lam
  lam := lam
  nu := nu e lam hh
  m := m e lam hh
  Q := Q e lam hh
  phi := phi lam hh
  A := A e lam hh
  theta := fun u v => (lam u v : ℂ) * ratio lam hh u v
  xi := fun u v => ∫ s in u..v,
    (-((nu e lam hh u s : ℂ) * ((lam u s : ℂ) * ratio lam hh u s) / (r lam u s : ℂ)) +
      I * e * Q e lam hh u s * phi lam hh u s * nu e lam hh u s * lam u s /
        ((1 - mu e lam hh u s) * r lam u s))

/-- The reconstructed `r` field is its prescribed radial formula. -/
@[simp] theorem toFields_r : (toFields e lam hh).r = r lam := rfl

/-- The reconstructed `lam` field is its prescribed radial formula. -/
@[simp] theorem toFields_lam : (toFields e lam hh).lam = lam := rfl

/-- The reconstructed `nu` field is its prescribed radial formula. -/
@[simp] theorem toFields_nu : (toFields e lam hh).nu = nu e lam hh := rfl

/-- The reconstructed `m` field is its prescribed radial formula. -/
@[simp] theorem toFields_m : (toFields e lam hh).m = m e lam hh := rfl

/-- The reconstructed `Q` field is its prescribed radial formula. -/
@[simp] theorem toFields_Q : (toFields e lam hh).Q = Q e lam hh := rfl

/-- The reconstructed `phi` field is its prescribed radial formula. -/
@[simp] theorem toFields_phi : (toFields e lam hh).phi = phi lam hh := rfl

/-- The reconstructed `A` field is its prescribed radial formula. -/
@[simp] theorem toFields_A : (toFields e lam hh).A = A e lam hh := rfl

end Recon

/-- [def-node restart-sec-independent-null-construction#incoming-defects]
Incoming Maxwell defect `Z = ∂_uQ - er Im(φ̄ξ)` (#incoming-defects,
charged_SF_new_version.tex:L6183–6189). -/
noncomputable def defectQ (e : ℝ) (D : Set (ℝ × ℝ)) (S : Fields) (u v : ℝ) : ℝ :=
  pdU D S.Q u v - S.QU e u v

/-- [def-node restart-sec-independent-null-construction#incoming-defects]
Incoming mass defect `E = ∂_um - (1-μ)|ξ|²/(2ν) - Q²ν/(2r²)` (#incoming-defects). -/
noncomputable def defectM (D : Set (ℝ × ℝ)) (S : Fields) (u v : ℝ) : ℝ :=
  pdU D S.m u v - S.mU u v

end EmcsfAcExtension.Local
