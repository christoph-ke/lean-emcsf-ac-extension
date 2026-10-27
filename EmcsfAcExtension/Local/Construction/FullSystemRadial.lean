module

public import EmcsfAcExtension.Local.Construction.FullSystemIntegral
public import EmcsfAcExtension.Local.Defs.Recon
import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # Joint first regularity of the nonsingular radial averages

internal project record (1), (6), and the C¹ part of `#smooth-regularity`.
The quotient for the scalar average is taken only after cancelling the
radial width, so the proof includes the axis and all wedge corners.
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Null

/-- A radial average preserves a positive lower bound on the entire wedge.
The lower bound `l` is fixed before the candidate and is unchanged. -/
theorem radial_average_lam_lower {a b c l : ℝ} {lam : ℝ → ℝ → ℝ}
    (cl : ContinuousOn (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2)
    {p : ℝ × ℝ} (hp : p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :
    l ≤ ∫ t in (0 : ℝ)..1, lam p.1 (p.1 + (p.2 - p.1) * t) := by
  have ci : ContinuousOn (fun t => lam p.1 (p.1 + (p.2 - p.1) * t)) (Icc 0 1) :=
    cl.comp (by fun_prop) (fun _ ht => radialPoint_mem_wedge hp ht)
  simpa using intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    intervalIntegrable_const (ci.intervalIntegrable_of_Icc (by norm_num))
    (fun t ht => hlo _ (radialPoint_mem_wedge hp ht))

/-- The scalar reconstruction equals the quotient of two nonsingular
radial averages at every wedge point, including the diagonal. -/
theorem phi_eq_radial_averages {a b c l : ℝ} {lam : ℝ → ℝ → ℝ}
    {hh : ℝ → ℝ → ℂ} (hl : 0 < l)
    (cl : ContinuousOn (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2)
    {p : ℝ × ℝ} (hp : p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :
    Recon.phi lam hh p.1 p.2 =
      (∫ t in (0 : ℝ)..1, (lam p.1 (p.1 + (p.2 - p.1) * t) : ℂ) *
        hh p.1 (p.1 + (p.2 - p.1) * t)) /
      ((∫ t in (0 : ℝ)..1, lam p.1 (p.1 + (p.2 - p.1) * t) : ℝ) : ℂ) := by
  have hL := hl.trans_le (radial_average_lam_lower cl hlo hp)
  have hL0 : ((∫ t in (0 : ℝ)..1,
      lam p.1 (p.1 + (p.2 - p.1) * t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  rcases hp.1.2.1.eq_or_lt with he | he
  · simp only [he, sub_self, zero_mul, add_zero, intervalIntegral.integral_const,
      sub_zero, one_smul, Recon.phi_axis]
    have hlp : 0 < lam p.2 p.2 := by simpa only [he] using hl.trans_le (hlo p hp)
    exact (mul_div_cancel_left₀ (hh p.2 p.2) (Complex.ofReal_ne_zero.mpr hlp.ne')).symm
  · simp only [Recon.phi, he, ite_true]
    rw [Recon.r,
      integral_eq_width_smul_radial_average lam p.1 p.2,
      integral_eq_width_smul_radial_average (fun u v => (lam u v : ℂ) * hh u v) p.1 p.2]
    simp only [smul_eq_mul, Complex.ofReal_mul, Complex.real_smul]
    have hx : ((p.2 - p.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr he).ne'
    field_simp

/-- Joint C¹ regularity of the radius, scalar average, scalar oscillation,
and outgoing scalar field on the original closed construction wedge.
Only joint C¹ of the fixed-point pair and a positive radius-density lower
bound are used. No higher derivative or incoming field equation is assumed. -/
theorem contDiffOn_radial_scalar_fields {a b c l : ℝ} (hac : a < c) (hcb : c ≤ b)
    {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ} (hl : 0 < l)
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContDiffOn ℝ 1 (Function.uncurry hh)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2) :
    ContDiffOn ℝ 1 (Function.uncurry (Recon.r lam))
        (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      ContDiffOn ℝ 1 (Function.uncurry (Recon.phi lam hh))
        (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      ContDiffOn ℝ 1 (Function.uncurry (Recon.ratio lam hh))
        (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      ContDiffOn ℝ 1 (fun p => (lam p.1 p.2 : ℂ) * Recon.ratio lam hh p.1 p.2)
        (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  have cL := contDiffOn_radial_average hac hcb cl
  have clC := Complex.ofRealCLM.contDiff.comp_contDiffOn cl
  have cN := contDiffOn_radial_average hac hcb (clC.mul ch)
  have cp : ContDiffOn ℝ 1 (Function.uncurry (Recon.phi lam hh))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
    have hd : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
        ((∫ t in (0 : ℝ)..1, lam p.1 (p.1 + (p.2 - p.1) * t) : ℝ) : ℂ) ≠ 0 := by
      intro p hp
      exact Complex.ofReal_ne_zero.mpr
        (hl.trans_le (radial_average_lam_lower cl.continuousOn hlo hp)).ne'
    apply (cN.mul ((Complex.ofRealCLM.contDiff.comp_contDiffOn cL).inv hd)).congr
    intro p hp
    simpa [Function.uncurry, Function.comp_def, div_eq_mul_inv] using!
      phi_eq_radial_averages hl cl.continuousOn hlo hp
  have cf := ch.sub cp
  exact ⟨contDiffOn_radial_primitive hac hcb cl, cp, cf, clC.mul cf⟩

end EmcsfAcExtension.Local.Null
