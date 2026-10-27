module

public import Mathlib

/-! # Algebraic cancellation in the geometric transports

The proof splits the calculation in `charged_SF_new_version.tex:L4850`–L4876 into the mixed
logarithm,
the quadratic correction and the Maxwell cancellation. All derivatives are scalar variables.
The two orientations are obtained by taking `s = 1` (outgoing ratio) or `s = -1` (incoming
ratio). No calculus or field definitions enter these internal project record algebraic cores.
-/

public section

namespace EmcsfAcExtension.Local

open Complex

/-- [node restart-bv-geom-trans]
Mixed logarithmic derivative, after substituting the radius and mass-ratio equations.
`a` is the radial derivative of `r`, `b` the other null derivative, and `ySq` the squared
normalized scalar ratio. Only `r`, `a` and `1-μ` must be nonzero. -/
theorem geom_log_mixed_algebra
    {r a b mu Q bD muD QD ySq : ℝ}
    (hr : r ≠ 0) (ha : a ≠ 0) (hmu : 1 - mu ≠ 0)
    (hbD : bD = b * a / r * ((mu - Q ^ 2 / r ^ 2) / (1 - mu)))
    (hmuD : muD = a / r * ((1 - mu) * ySq + Q ^ 2 / r ^ 2 - mu)) :
    bD / r * ((mu - Q ^ 2 / r ^ 2) / (1 - mu)) -
        b * a / r ^ 2 * ((mu - Q ^ 2 / r ^ 2) / (1 - mu)) +
        b / r * ((muD - 2 * Q * QD / r ^ 2 + 2 * Q ^ 2 * a / r ^ 3) / (1 - mu) +
          (mu - Q ^ 2 / r ^ 2) * muD / (1 - mu) ^ 2) =
      b * a / r ^ 2 *
        ((1 + (mu - Q ^ 2 / r ^ 2) / (1 - mu)) * ySq -
          2 * ((mu - Q ^ 2 / r ^ 2) / (1 - mu)) +
          2 * Q ^ 2 / ((1 - mu) * r ^ 2) - 2 * Q * QD / ((1 - mu) * a * r)) := by
  rw [hbD, hmuD]
  field_simp [hr, ha, hmu]
  ring

/-- [node restart-bv-geom-trans]
Derivative of the quadratic correction `|t|²/(ar)`, after substituting the radius and
covariant scalar equations. `s = 1` gives `t = θ`, `a = λ`; `s = -1` gives `t = ξ`, `a = ν`.
The `tD` variable denotes a covariant derivative. -/
theorem geom_quadratic_algebra
    {r a b mu Q e s aD : ℝ} {phi t x tD : ℂ}
    (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hmu : 1 - mu ≠ 0)
    (haD : aD = b * a / r * ((mu - Q ^ 2 / r ^ 2) / (1 - mu)))
    (htD : tD = -(a * x / r) -
      s * I * e * Q * phi * b * a / ((1 - mu) * r)) :
    2 * (starRingEnd ℂ t * tD).re / (a * r) -
        ‖t‖ ^ 2 * (aD * r + a * b) / (a * r) ^ 2 =
      b * a / r ^ 2 *
        (-(1 + (mu - Q ^ 2 / r ^ 2) / (1 - mu)) * ‖t / a‖ ^ 2 -
          2 * (starRingEnd ℂ t * x).re / (a * b) -
          2 * s * e * Q * (I * phi * starRingEnd ℂ t).re / ((1 - mu) * a)) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hmuC : 1 - (mu : ℂ) ≠ 0 := by exact_mod_cast hmu
  have htD' : tD = -((a / r : ℝ) : ℂ) * x -
      ((s * e * Q * b * a / ((1 - mu) * r) : ℝ) : ℂ) * I * phi := by
    rw [htD]
    push_cast
    field_simp [hrC, hmuC]
  rw [haD, htD', norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im]
  field_simp [hr, ha, hb, hmu]
  ring

/-- [node restart-bv-geom-trans]
Cancellation of the electromagnetic terms by the oriented Maxwell constraint.
`s = 1` is `Qᵥ = -er Im(φ̄θ)`; `s = -1` is `Qᵤ = er Im(φ̄ξ)`. -/
theorem geom_maxwell_cancellation_algebra
    {r a mu Q e s QD : ℝ} {phi t : ℂ}
    (hr : r ≠ 0) (ha : a ≠ 0) (hmu : 1 - mu ≠ 0)
    (hQD : QD = -s * e * r * (starRingEnd ℂ phi * t).im) :
    s * e * Q * (I * phi * starRingEnd ℂ t).re / ((1 - mu) * a) +
      Q * QD / ((1 - mu) * a * r) = 0 := by
  rw [hQD]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.conj_re, Complex.conj_im]
  field_simp [hr, ha, hmu]
  ring

private theorem geom_curvature_real (a b mu : ℝ) (t x : ℂ) :
    ((mu : ℂ) + (1 - (mu : ℂ)) * t * starRingEnd ℂ x /
      (((a * b : ℝ) : ℂ))).re =
    mu + (1 - mu) * (starRingEnd ℂ t * x).re / (a * b) := by
  simp only [Complex.add_re, Complex.div_ofReal_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem geom_trans_algebra
    {r a b mu Q e s aD bD muD QD : ℝ} {phi t x tD : ℂ}
    (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hmu : 1 - mu ≠ 0)
    (haD : aD = b * a / r * ((mu - Q ^ 2 / r ^ 2) / (1 - mu)))
    (hbD : bD = b * a / r * ((mu - Q ^ 2 / r ^ 2) / (1 - mu)))
    (hmuD : muD = a / r * ((1 - mu) * ‖t / a‖ ^ 2 + Q ^ 2 / r ^ 2 - mu))
    (hQD : QD = -s * e * r * (starRingEnd ℂ phi * t).im)
    (htD : tD = -(a * x / r) -
      s * I * e * Q * phi * b * a / ((1 - mu) * r)) :
    (bD / r * ((mu - Q ^ 2 / r ^ 2) / (1 - mu)) -
        b * a / r ^ 2 * ((mu - Q ^ 2 / r ^ 2) / (1 - mu)) +
        b / r * ((muD - 2 * Q * QD / r ^ 2 + 2 * Q ^ 2 * a / r ^ 3) / (1 - mu) +
          (mu - Q ^ 2 / r ^ 2) * muD / (1 - mu) ^ 2)) +
      (2 * (starRingEnd ℂ t * tD).re / (a * r) -
        ‖t‖ ^ 2 * (aD * r + a * b) / (a * r) ^ 2) =
      -(2 * b * a / ((1 - mu) * r ^ 2)) *
        (((mu : ℂ) + (1 - (mu : ℂ)) * t * starRingEnd ℂ x /
          (((a * b : ℝ) : ℂ))).re - 2 * (Q ^ 2 / r ^ 2)) := by
  rw [geom_log_mixed_algebra hr ha hmu hbD hmuD,
    geom_quadratic_algebra hr ha hb hmu haD htD, geom_curvature_real]
  have hcancel := geom_maxwell_cancellation_algebra (Q := Q) hr ha hmu hQD
  calc
    _ = -(2 * b * a / ((1 - mu) * r ^ 2)) *
          (mu + (1 - mu) * (starRingEnd ℂ t * x).re / (a * b) - 2 * (Q ^ 2 / r ^ 2)) -
        (2 * b * a / r ^ 2) *
          (s * e * Q * (I * phi * starRingEnd ℂ t).re / ((1 - mu) * a) +
            Q * QD / ((1 - mu) * a * r)) := by
      field_simp [hr, ha, hb, hmu]
      ring
    _ = _ := by rw [hcancel]; ring

/-- [node restart-bv-geom-trans]
Algebraic core of `∂ᵤ𝓛 = geomSource` (`charged_SF_new_version.tex:L4850`). The first parenthesis
is the mixed derivative of `log λ`; the second differentiates `|θ|²/(λr)`.
`thetaDu` denotes `Dᵤθ`, and `muV` denotes `∂ᵥ(2m/r)`. All assumptions are reduced
equations or the quotient rule for `μ`; the four geometric denominators are nonzero. -/
theorem bv_geom_trans_out_algebra
    {r lam nu m Q e lamU nuV mV muV QV : ℝ} {phi theta xi thetaDu : ℂ}
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hnu : nu ≠ 0) (hmu : 1 - 2 * m / r ≠ 0)
    (hlamU : lamU = nu * lam / r * ((2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r)))
    (hnuV : nuV = nu * lam / r * ((2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r)))
    (hmV : mV = (1 - 2 * m / r) * ‖theta‖ ^ 2 / (2 * lam) + Q ^ 2 * lam / (2 * r ^ 2))
    (hmuV : muV = 2 * mV / r - 2 * m * lam / r ^ 2)
    (hQV : QV = -(e * r * (starRingEnd ℂ phi * theta).im))
    (hthetaDu : thetaDu = -(lam * xi / r) -
      I * e * Q * phi * nu * lam / ((1 - 2 * m / r) * r)) :
    (nuV / r * ((2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r)) -
        nu * lam / r ^ 2 * ((2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r)) +
        nu / r * ((muV - 2 * Q * QV / r ^ 2 + 2 * Q ^ 2 * lam / r ^ 3) / (1 - 2 * m / r) +
          (2 * m / r - Q ^ 2 / r ^ 2) * muV / (1 - 2 * m / r) ^ 2)) +
      (2 * (starRingEnd ℂ theta * thetaDu).re / (lam * r) -
        ‖theta‖ ^ 2 * (lamU * r + lam * nu) / (lam * r) ^ 2) =
      -(2 * nu * lam / ((1 - 2 * m / r) * r ^ 2)) *
        ((((2 * m / r : ℝ) : ℂ) + (1 - ((2 * m / r : ℝ) : ℂ)) * theta *
          starRingEnd ℂ xi / (((lam * nu : ℝ) : ℂ))).re - 2 * (Q ^ 2 / r ^ 2)) := by
  have hmuV' : muV = lam / r *
      ((1 - 2 * m / r) * ‖theta / lam‖ ^ 2 + Q ^ 2 / r ^ 2 - 2 * m / r) := by
    rw [hmuV, hmV, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
    field_simp [hr, hlam]
  exact geom_trans_algebra (s := 1) hr hlam hnu hmu hlamU hnuV hmuV'
    (by simpa using hQV) (by simpa using hthetaDu)

/-- [node restart-bv-geom-trans]
Algebraic core of `∂ᵥ𝓝 = geomSource` (`charged_SF_new_version.tex:L4850`). The first parenthesis
is the mixed derivative of `log(-ν)`; the second differentiates `|ξ|²/(νr)`.
Both directions have exactly the same real curvature source.
All four geometric denominators must be nonzero. -/
theorem bv_geom_trans_in_algebra
    {r lam nu m Q e lamU nuV mU muU QU : ℝ} {phi theta xi xiV : ℂ}
    (hr : r ≠ 0) (hlam : lam ≠ 0) (hnu : nu ≠ 0) (hmu : 1 - 2 * m / r ≠ 0)
    (hlamU : lamU = lam * nu / r * ((2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r)))
    (hnuV : nuV = lam * nu / r * ((2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r)))
    (hmU : mU = (1 - 2 * m / r) * ‖xi‖ ^ 2 / (2 * nu) + Q ^ 2 * nu / (2 * r ^ 2))
    (hmuU : muU = 2 * mU / r - 2 * m * nu / r ^ 2)
    (hQU : QU = e * r * (starRingEnd ℂ phi * xi).im)
    (hxiV : xiV = -(nu * theta / r) +
      I * e * Q * phi * lam * nu / ((1 - 2 * m / r) * r)) :
    (lamU / r * ((2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r)) -
        lam * nu / r ^ 2 * ((2 * m / r - Q ^ 2 / r ^ 2) / (1 - 2 * m / r)) +
        lam / r * ((muU - 2 * Q * QU / r ^ 2 + 2 * Q ^ 2 * nu / r ^ 3) / (1 - 2 * m / r) +
          (2 * m / r - Q ^ 2 / r ^ 2) * muU / (1 - 2 * m / r) ^ 2)) +
      (2 * (starRingEnd ℂ xi * xiV).re / (nu * r) -
        ‖xi‖ ^ 2 * (nuV * r + nu * lam) / (nu * r) ^ 2) =
      -(2 * nu * lam / ((1 - 2 * m / r) * r ^ 2)) *
        ((((2 * m / r : ℝ) : ℂ) + (1 - ((2 * m / r : ℝ) : ℂ)) * theta *
          starRingEnd ℂ xi / (((lam * nu : ℝ) : ℂ))).re - 2 * (Q ^ 2 / r ^ 2)) := by
  have hmuU' : muU = nu / r *
      ((1 - 2 * m / r) * ‖xi / nu‖ ^ 2 + Q ^ 2 / r ^ 2 - 2 * m / r) := by
    rw [hmuU, hmU, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow, sq_abs]
    field_simp [hr, hnu]
  calc
    _ = -(2 * lam * nu / ((1 - 2 * m / r) * r ^ 2)) *
        ((((2 * m / r : ℝ) : ℂ) + (1 - ((2 * m / r : ℝ) : ℂ)) * xi *
          starRingEnd ℂ theta / (((nu * lam : ℝ) : ℂ))).re - 2 * (Q ^ 2 / r ^ 2)) :=
      geom_trans_algebra (s := -1) hr hnu hlam hmu hnuV hlamU hmuU'
        (by simpa using hQU) (by simpa [neg_div] using hxiV)
    _ = _ := by
      rw [geom_curvature_real, geom_curvature_real]
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring

end EmcsfAcExtension.Local
