module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The algebraic core of outgoing renormalized transport

This is the rational calculation in `charged_SF_new_version.tex:L4526–4545`, authorized by
internal project record and independently verified in W4 internal project record.
There are no fields or derivative operators in this module. Derivatives enter
through their substituted expressions. The calculus layer must justify those
substitutions and commutation of derivatives.

Use `y = θ/λ`, `z = ξ/ν`, `g = ie`. The independent atoms `yb`, `zb`, `phib`
stand for the complex conjugates of `y`, `z`, `phi`. Working in any field of
characteristic zero isolates the rational calculation from conjugation and
real-to-complex coercions. Only `r` and `1 - mu` occur as denominators; the
nonvanishing of `λ` and `ν` belongs to the substitution of normalized fields.
-/

public section

namespace EmcsfAcExtension.Local

/-- [node restart-bv-j-trans]
Algebraic core of `D_u j`, with the exact source `restart-bv-Ej`
(`charged_SF_new_version.tex:L4526–4545`). Here `aV = ∂_v(φ + θ/λ)` and
`qv = Q_v`; `hqv` is exactly the outgoing Maxwell equation written with
conjugate atoms. `cv` differentiates `-ν/(r(1-μ))`, `bv` differentiates
`μ-Q²/r²`, `dy` and `dyb` are the covariant normalized scalar transports,
and `daV` uses the commutator `-ie A_v(φ+y)`.

The left side is the product rule for `D_u j`, including both conjugate
contributions to the cubic derivative. This proves only the algebraic core;
no differentiability or mixed-partial assertion is assumed or concluded. -/
theorem bv_j_trans_algebra {K : Type*} [Field K] [CharZero K]
    (r lam nu mu q g y yb z zb phi phib aV qv : K)
    (hr : r ≠ 0) (hmu : 1 - mu ≠ 0)
    (hqv : qv = g * r * lam / 2 * (phib * y - phi * yb)) :
    let H := 1 - mu
    let B := mu - q ^ 2 / r ^ 2
    let nuV := nu * lam * B / (r * H)
    let HV := lam / r * (B - H * yb * y)
    let cv := -nuV / (r * H) + nu * (lam * H + r * HV) / (r * H) ^ 2
    let bv := lam / r * (H * yb * y + q ^ 2 / r ^ 2 - mu) -
      2 * q * qv / r ^ 2 + 2 * q ^ 2 * lam / r ^ 3
    let dy := -nu / r * (z + B / H * y + g * q / H * phi)
    let dyb := -nu / r * (zb + B / H * yb - g * q / H * phib)
    let dH := nu / r * (B - H * zb * z)
    let dlr := nu * lam / r ^ 2 * (B / H - 1)
    let daV := cv * (B * y + g * q * phi) -
      nu / (r * H) * (bv * y + B * (aV - lam * y / r) +
        g * qv * phi + g * q * lam * y / r) -
      g * (2 * nu * lam * q / (H * r ^ 2)) * (phi + y)
    let j := H * (aV - lam / r * yb * y * y)
    let C := mu + H * y * zb
    let Cbar := mu + H * yb * z
    let Ej := (-nu) * lam / r ^ 2 *
      (5 * (q ^ 2 / r ^ 2) * y + g * q * (3 * y + phi)) -
      g * nu * qv * phi / r
    dH * (aV - lam / r * yb * y * y) +
        H * (daV - dlr * yb * y * y - lam / r * (dyb * y * y + 2 * yb * y * dy)) =
      -nu * zb * z / r * j + nu * lam * y / r ^ 2 * (C + 2 * Cbar) + Ej := by
  subst qv
  dsimp
  field_simp [hr, hmu]
  ring

/-- [node restart-bv-j-trans]
Complex specialization of `bv_j_trans_algebra`, with real geometric and Maxwell
coefficients, actual complex conjugates and norm squares. The normalized inputs
are `y = θ/λ` and `z = ξ/ν`. `Qv` is the outgoing Maxwell source and `Ej` is
exactly `restart-bv-Ej`. The displayed left side is the substituted product rule
for `D_u j`, with the conjugate covariant transport written as `dyb`. -/
theorem bv_j_trans_complex (r lam nu mu q e : ℝ) (y z phi aV : ℂ)
    (hr : r ≠ 0) (hmu : 1 - mu ≠ 0) :
    let R : ℂ := r
    let L : ℂ := lam
    let N : ℂ := nu
    let M : ℂ := mu
    let Q : ℂ := q
    let g : ℂ := Complex.I * e
    let H := 1 - M
    let B := M - Q ^ 2 / R ^ 2
    let Qv : ℂ := -(e * r * lam * ((starRingEnd ℂ) phi * y).im : ℝ)
    let nuV := N * L * B / (R * H)
    let HV := L / R * (B - H * (‖y‖ : ℂ) ^ 2)
    let cv := -nuV / (R * H) + N * (L * H + R * HV) / (R * H) ^ 2
    let bv := L / R * (H * (‖y‖ : ℂ) ^ 2 + Q ^ 2 / R ^ 2 - M) -
      2 * Q * Qv / R ^ 2 + 2 * Q ^ 2 * L / R ^ 3
    let dy := -N / R * (z + B / H * y + g * Q / H * phi)
    let dyb := -N / R * ((starRingEnd ℂ) z + B / H * (starRingEnd ℂ) y -
      g * Q / H * (starRingEnd ℂ) phi)
    let dH := N / R * (B - H * (‖z‖ : ℂ) ^ 2)
    let dlr := N * L / R ^ 2 * (B / H - 1)
    let daV := cv * (B * y + g * Q * phi) -
      N / (R * H) * (bv * y + B * (aV - L * y / R) +
        g * Qv * phi + g * Q * L * y / R) -
      g * (2 * N * L * Q / (H * R ^ 2)) * (phi + y)
    let j := H * (aV - L / R * (‖y‖ : ℂ) ^ 2 * y)
    let C := M + H * y * (starRingEnd ℂ) z
    let Ej := (-N) * L / R ^ 2 *
      (5 * (Q ^ 2 / R ^ 2) * y + g * Q * (3 * y + phi)) -
      g * N * Qv * phi / R
    dH * (aV - L / R * (‖y‖ : ℂ) ^ 2 * y) +
        H * (daV - dlr * (‖y‖ : ℂ) ^ 2 * y -
          L / R * (dyb * y * y + 2 * (starRingEnd ℂ) y * y * dy)) =
      -N * (‖z‖ : ℂ) ^ 2 / R * j + N * L * y / R ^ 2 *
        (C + 2 * (starRingEnd ℂ) C) + Ej := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hmu' : 1 - (mu : ℂ) ≠ 0 := by exact_mod_cast hmu
  have hqv : (-(e * r * lam * ((starRingEnd ℂ) phi * y).im : ℝ) : ℂ) =
      Complex.I * e * r * lam / 2 *
        ((starRingEnd ℂ) phi * y - phi * (starRingEnd ℂ) y) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    ring
  have h := bv_j_trans_algebra (r : ℂ) (lam : ℂ) (nu : ℂ) (mu : ℂ) (q : ℂ)
    (Complex.I * e) y ((starRingEnd ℂ) y) z ((starRingEnd ℂ) z)
    phi ((starRingEnd ℂ) phi) aV _ hr' hmu' hqv
  dsimp only at h ⊢
  simp only [← Complex.conj_mul', map_add, map_mul, map_sub, map_one,
    Complex.conj_ofReal, starRingEnd_self_apply]
  convert h using 1 <;> ring

end EmcsfAcExtension.Local
