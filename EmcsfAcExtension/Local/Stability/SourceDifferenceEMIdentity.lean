module

public import EmcsfAcExtension.Local.Defs.Renormalized

/-! # The complete Maxwell-substituted electromagnetic monomial list

Both explicit derivative sources reduce to three monomial families.
The outgoing and incoming middle terms have opposite signs, and their
Maxwell-current terms have the same negative sign.
-/

public section

open Complex

namespace EmcsfAcExtension.Local.Stab

private theorem im_conj_mul_ratio (p z : ℂ) {l : ℝ} (hl : l ≠ 0) :
    (starRingEnd ℂ p * z).im = l * (starRingEnd ℂ p * (z / (l : ℂ))).im := by
  have hlc := ofReal_ne_zero.mpr hl
  have heq : starRingEnd ℂ p * z = (l : ℂ) * (starRingEnd ℂ p * (z / (l : ℂ))) := by
    field_simp
  rw [heq]
  simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]


/-- The explicit outgoing electromagnetic source after substituting its
Maxwell current. These are all three monomial families of internal project record (EM1). -/
theorem emSourceJ_eq_monomials (e : ℝ) (S : Fields) (u v : ℝ)
    (hr : S.r u v ≠ 0) (hl : S.lam u v ≠ 0) :
    let B := -S.nu u v * S.lam u v
    let q := S.Q u v / S.r u v ^ 2
    let x := S.theta u v / (S.lam u v : ℂ)
    emSourceJ e S u v =
      5 * B * (q : ℂ) ^ 2 * x + I * e * B * q * (3 * x + S.phi u v) -
        I * (e : ℂ) ^ 2 * B * S.phi u v *
          (((starRingEnd ℂ (S.phi u v) * x).im : ℝ) : ℂ) := by
  dsimp only
  have hrc := ofReal_ne_zero.mpr hr
  have hlc := ofReal_ne_zero.mpr hl
  have him := im_conj_mul_ratio (S.phi u v) (S.theta u v) hl
  simp only [emSourceJ, Fields.QV, him]
  push_cast
  field_simp
  ; ring

/-- The explicit incoming electromagnetic source after substituting its
Maxwell current. Its current term has the same negative sign as for j. -/
theorem emSourceK_eq_monomials (e : ℝ) (S : Fields) (u v : ℝ)
    (hr : S.r u v ≠ 0) (hn : S.nu u v ≠ 0) :
    let B := -S.nu u v * S.lam u v
    let q := S.Q u v / S.r u v ^ 2
    let y := S.xi u v / (S.nu u v : ℂ)
    emSourceK e S u v =
      5 * B * (q : ℂ) ^ 2 * y - I * e * B * q * (3 * y + S.phi u v) -
        I * (e : ℂ) ^ 2 * B * S.phi u v *
          (((starRingEnd ℂ (S.phi u v) * y).im : ℝ) : ℂ) := by
  dsimp only
  have hrc := ofReal_ne_zero.mpr hr
  have hnc := ofReal_ne_zero.mpr hn
  have him := im_conj_mul_ratio (S.phi u v) (S.xi u v) hn
  simp only [emSourceK, Fields.QU, him]
  push_cast
  field_simp
  ; ring

end EmcsfAcExtension.Local.Stab
