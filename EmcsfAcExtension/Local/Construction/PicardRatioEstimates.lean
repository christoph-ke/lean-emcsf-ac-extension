module

public import EmcsfAcExtension.Local.Construction.PicardMassLipschitz
public import EmcsfAcExtension.Local.Construction.PicardRatios
public import EmcsfAcExtension.Local.Construction.PicardFiniteProfile

/-! # Uniform estimates for normalized mass and charge ratios

The normalized ratio formulas are polynomial in seven bounded inputs,
including the reciprocal radial average. Their finite dimensional bounds
are uniform in cone position and incoming width.
-/

public section

open Set

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- The seven polynomial ratio outputs, in order: normalized mass aspect,
mass aspect, normalized mass-aspect jet, normalized charge-square quotient,
charge-square quotient, its normalized jet, and the Hawking gap. The inputs
are width, expansion, reciprocal radial average, squared scalar remainder,
normalized charge, charge kernel, and normalized mass. -/
@[expose] noncomputable def picardRatioPolynomial (v : Fin 7 → ℝ) : Fin 7 → ℝ :=
  let mu0 := 2 * v 6 * v 2
  let mu := v 0 ^ 2 * mu0
  let q0 := v 4 ^ 2 * v 2 ^ 2
  ![mu0, mu, v 1 * v 2 * ((1 - mu) * v 3 + v 0 ^ 2 * q0 - mu0),
    q0, v 0 ^ 4 * q0, 2 * v 4 * v 5 * v 2 ^ 2 - 2 * v 1 * v 4 ^ 2 * v 2 ^ 3,
    1 - mu]

/-- The normalized ratio polynomial is smooth on its whole finite
dimensional input space; positivity is needed only to bound the inputs. -/
theorem contDiff_picardRatioPolynomial : ContDiff ℝ 1 picardRatioPolynomial := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp only [picardRatioPolynomial, Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero,
    Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;> fun_prop

/-- Continuous input profiles for the normalized mass and charge ratios. -/
@[expose] noncomputable def picardRatioInput (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) :
    C(PicardDomain c a L, Fin 7 → ℝ) where
  toFun p := ![p.1.2 - p.1.1, (z.1.1 p).1,
    (picardRadialAverage (picardLamValues z) p)⁻¹,
    ‖picardScalarRemainder ell he z hl p‖ ^ 2,
    picardChargeRemainder e ell he z hl p,
    picardChargeKernel e ell he z hl p,
    picardMassRemainder e ell he z hl p]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
    · exact (continuous_snd.comp continuous_subtype_val).sub
        (continuous_fst.comp continuous_subtype_val)
    · exact z.1.1.continuous.fst
    · exact (picardRadialAverage (picardLamValues z)).continuous.inv₀
        (fun p => (he.trans_le (picardRadialAverage_lower _ hl p)).ne')
    · exact (picardScalarRemainder ell he z hl).continuous.norm.pow 2
    · exact (picardChargeRemainder e ell he z hl).continuous
    · exact (picardChargeKernel e ell he z hl).continuous
    · exact (picardMassRemainder e ell he z hl).continuous

/-- The seven normalized ratio profiles as one continuous vector. -/
@[expose] noncomputable def picardRatioProfiles (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) :
    C(PicardDomain c a L, Fin 7 → ℝ) :=
  ContinuousMap.comp ⟨picardRatioPolynomial, contDiff_picardRatioPolynomial.continuous⟩
    (picardRatioInput e ell he z hl)

/-- The profile vector is exactly the existing normalized reconstruction
formulas, with no change to any radial definition. -/
theorem picardRatioProfiles_apply (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) :
    picardRatioProfiles e ell he z hl p =
      ![picardMuRemainder e ell he z hl p, picardMuValues e ell he z hl p,
        picardMuJetRemainder e ell he z hl p, picardQSquareRemainder e ell he z hl p,
        picardQSquareValues e ell he z hl p, picardQSquareJetRemainder e ell he z hl p,
        1 - picardMuValues e ell he z hl p] := by
  ext i
  fin_cases i <;> simp [picardRatioProfiles, picardRatioInput, picardRatioPolynomial,
    picardMuRemainder, picardMuValues, picardMuJetRemainder, picardQSquareRemainder,
    picardQSquareValues, picardQSquareJetRemainder, div_eq_mul_inv]

end EmcsfAcExtension.Local
