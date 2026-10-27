module

public import EmcsfAcExtension.Local.Algebra.JTransport
import Mathlib.Tactic.Ring

/-! # The algebraic core of incoming renormalized transport

The rational calculation of `charged_SF_new_version.tex:L4530–4532,L4546–4549`.
The variables have the same interpretation as in `JTransport`, with
`z = ξ/ν`, `y = θ/λ`, and `bU = D_u(φ + ξ/ν)`.

The incoming identity follows from the outgoing algebra by interchanging the
null directions and reversing the sign of `g = ie`. This implements the
charge reversal check of `charged_SF_new_version.tex:L4551–4556`, including its effect on
the Maxwell derivative and commutator. No gauge or calculus assertion is used.
-/

public section

namespace EmcsfAcExtension.Local

/-- [node restart-bv-k-trans]
Algebraic core of `∂_v k`, with the exact source `restart-bv-Ek`
(`charged_SF_new_version.tex:L4530–4532,L4546–4549`). `hqu` is the incoming Maxwell
equation in conjugate atoms. `cu`, `bu`, `dz`, `dzb`, `dH`, `dnr`, `dbU`
are the incoming counterparts of the substituted derivatives in
`bv_j_trans_algebra`; in particular, the commutator in `dbU` has positive
sign. All denominator hypotheses are explicit. -/
theorem bv_k_trans_algebra {K : Type*} [Field K] [CharZero K]
    (r lam nu mu q g y yb z zb phi phib bU qu : K)
    (hr : r ≠ 0) (hmu : 1 - mu ≠ 0)
    (hqu : qu = -g * r * nu / 2 * (phib * z - phi * zb)) :
    let H := 1 - mu
    let B := mu - q ^ 2 / r ^ 2
    let lamU := lam * nu * B / (r * H)
    let HU := nu / r * (B - H * zb * z)
    let cu := -lamU / (r * H) + lam * (nu * H + r * HU) / (r * H) ^ 2
    let bu := nu / r * (H * zb * z + q ^ 2 / r ^ 2 - mu) -
      2 * q * qu / r ^ 2 + 2 * q ^ 2 * nu / r ^ 3
    let dz := -lam / r * (y + B / H * z - g * q / H * phi)
    let dzb := -lam / r * (yb + B / H * zb + g * q / H * phib)
    let dH := lam / r * (B - H * yb * y)
    let dnr := lam * nu / r ^ 2 * (B / H - 1)
    let dbU := cu * (B * z - g * q * phi) -
      lam / (r * H) * (bu * z + B * (bU - nu * z / r) -
        g * qu * phi - g * q * nu * z / r) +
      g * (2 * lam * nu * q / (H * r ^ 2)) * (phi + z)
    let k := H * (bU - nu / r * zb * z * z)
    let C := mu + H * y * zb
    let Cbar := mu + H * yb * z
    let Ek := (-nu) * lam / r ^ 2 *
      (5 * (q ^ 2 / r ^ 2) * z - g * q * (3 * z + phi)) +
      g * lam * qu * phi / r
    dH * (bU - nu / r * zb * z * z) +
        H * (dbU - dnr * zb * z * z - nu / r * (dzb * z * z + 2 * zb * z * dz)) =
      -lam * yb * y / r * k + lam * nu * z / r ^ 2 * (Cbar + 2 * C) + Ek := by
  have h := bv_j_trans_algebra r nu lam mu q (-g) z zb y yb phi phib bU qu
    hr hmu hqu
  dsimp only at h ⊢
  simp only [neg_mul, neg_div, sub_neg_eq_add] at h
  convert h using 1 <;> ring

/-- [node restart-bv-k-trans]
Complex specialization of `bv_k_trans_algebra`, with real coefficients,
actual conjugation and norm squares. `Qu` is exactly the incoming Maxwell
source and `Ek` is `restart-bv-Ek`. The left side is the substituted product
rule for `∂_v k`, with both contributions to the conjugate cubic derivative. -/
theorem bv_k_trans_complex (r lam nu mu q e : ℝ) (y z phi bU : ℂ)
    (hr : r ≠ 0) (hmu : 1 - mu ≠ 0) :
    let R : ℂ := r
    let L : ℂ := lam
    let N : ℂ := nu
    let M : ℂ := mu
    let Q : ℂ := q
    let g : ℂ := Complex.I * e
    let H := 1 - M
    let B := M - Q ^ 2 / R ^ 2
    let Qu : ℂ := (e * r * nu * ((starRingEnd ℂ) phi * z).im : ℝ)
    let lamU := L * N * B / (R * H)
    let HU := N / R * (B - H * (‖z‖ : ℂ) ^ 2)
    let cu := -lamU / (R * H) + L * (N * H + R * HU) / (R * H) ^ 2
    let bu := N / R * (H * (‖z‖ : ℂ) ^ 2 + Q ^ 2 / R ^ 2 - M) -
      2 * Q * Qu / R ^ 2 + 2 * Q ^ 2 * N / R ^ 3
    let dz := -L / R * (y + B / H * z - g * Q / H * phi)
    let dzb := -L / R * ((starRingEnd ℂ) y + B / H * (starRingEnd ℂ) z +
      g * Q / H * (starRingEnd ℂ) phi)
    let dH := L / R * (B - H * (‖y‖ : ℂ) ^ 2)
    let dnr := L * N / R ^ 2 * (B / H - 1)
    let dbU := cu * (B * z - g * Q * phi) -
      L / (R * H) * (bu * z + B * (bU - N * z / R) -
        g * Qu * phi - g * Q * N * z / R) +
      g * (2 * L * N * Q / (H * R ^ 2)) * (phi + z)
    let k := H * (bU - N / R * (‖z‖ : ℂ) ^ 2 * z)
    let C := M + H * y * (starRingEnd ℂ) z
    let Ek := (-N) * L / R ^ 2 *
      (5 * (Q ^ 2 / R ^ 2) * z - g * Q * (3 * z + phi)) +
      g * L * Qu * phi / R
    dH * (bU - N / R * (‖z‖ : ℂ) ^ 2 * z) +
        H * (dbU - dnr * (‖z‖ : ℂ) ^ 2 * z -
          N / R * (dzb * z * z + 2 * (starRingEnd ℂ) z * z * dz)) =
      -L * (‖y‖ : ℂ) ^ 2 / R * k + L * N * z / R ^ 2 *
        ((starRingEnd ℂ) C + 2 * C) + Ek := by
  have h := bv_j_trans_complex r nu lam mu q (-e) z y phi bU hr hmu
  dsimp only at h ⊢
  simp only [Complex.ofReal_neg, Complex.ofReal_mul, neg_mul, mul_neg, neg_neg,
    neg_div, sub_neg_eq_add, map_add, map_mul, map_sub, map_one,
    Complex.conj_ofReal, starRingEnd_self_apply] at h ⊢
  convert h using 1
  ring

end EmcsfAcExtension.Local
