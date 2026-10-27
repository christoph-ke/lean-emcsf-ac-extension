module

public import EmcsfAcExtension.Local.Construction.FullSystemDivision
public import EmcsfAcExtension.Local.Construction.FullSystemRadial

import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # First regularity of the exact mass damping

The apparently singular coefficient `λ |h-φ|² / r` is the divided product
of two zero-axis C¹ fields, divided only by a positive radial average.
This is the use of internal project record (5) in its mass formula (6).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Null

/-- A zero-axis complex C¹ field has a C¹ squared norm divided by radial
width, with the raw totalized value zero on the diagonal. -/
theorem contDiffOn_norm_sq_div_width {a b c : ℝ} (hac : a < c) (hcb : c ≤ b)
    {f : ℝ → ℝ → ℂ}
    (cf : ContDiffOn ℝ 1 (Function.uncurry f)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hf0 : ∀ t ∈ Icc a c, f t t = 0) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => ‖f p.1 p.2‖ ^ 2 / (p.2 - p.1))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  have cc : ContDiffOn ℝ 1 (Function.uncurry (fun u v => starRingEnd ℂ (f u v)))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
    simpa only [Function.uncurry, Function.comp_apply] using!
      Complex.conjCLE.contDiff.comp_contDiffOn cf
  have hc := contDiffOn_divided_product (f := fun u v => starRingEnd ℂ (f u v))
    (g := f) hac hcb cc cf (fun t ht => by simp [hf0 t ht]) hf0
  have he (z : ℂ) (x : ℝ) : ((starRingEnd ℂ z * z) / (x : ℂ)).re = ‖z‖ ^ 2 / x := by
    rw [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
  apply (Complex.reCLM.contDiff.comp_contDiffOn hc).congr
  intro p _
  simpa only [Function.comp_apply, Complex.reCLM_apply] using!
    (he (f p.1 p.2) (p.2 - p.1)).symm

/-- The literal integrating-factor mass damping is jointly C¹. This
removes the singular radius by a positive radial average and the divided
product lemma; no second derivative is used. The lower bound `l` is fixed
before the candidate and there are no new estimate constants. -/
theorem contDiffOn_mass_damping {a b c l : ℝ} (hac : a < c) (hcb : c ≤ b)
    {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ} (hl : 0 < l)
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContDiffOn ℝ 1 (Function.uncurry hh)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ =>
      lam p.1 p.2 * ‖Recon.ratio lam hh p.1 p.2‖ ^ 2 / Recon.r lam p.1 p.2)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  obtain ⟨_, _, cf, _⟩ := contDiffOn_radial_scalar_fields hac hcb hl cl ch hlo
  have cT := contDiffOn_norm_sq_div_width hac hcb cf (fun t _ => Recon.ratio_axis)
  have cL := contDiffOn_radial_average hac hcb cl
  apply ((cl.mul cT).div cL (fun p hp =>
    (hl.trans_le (radial_average_lam_lower cl.continuousOn hlo hp)).ne')).congr
  intro p _
  dsimp only [Function.uncurry, Pi.mul_apply, Pi.div_apply, Pi.inv_apply]
  rw [Recon.r, integral_eq_width_smul_radial_average lam p.1 p.2]
  simp only [smul_eq_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end EmcsfAcExtension.Local.Null
