module

public import EmcsfAcExtension.Local.Construction.PicardRatioEstimates
public import EmcsfAcExtension.Local.Construction.PicardRealSources

/-! # Uniform estimates on the positive-gap coefficient domain

The normalized z and B formulas are smooth finite dimensional formulas on
the half-space where the gap has its fixed positive lower bound. The
resulting constants precede cone position, incoming width, and candidates.
-/

public section

open Set

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- The finite rational formulas for z, B and inverse-gap values and jets.
The last input is the gap; its positive lower bound is explicit below. -/
@[expose] noncomputable def picardGapPolynomial (v : Fin 11 → ℝ) : Fin 9 → ℝ :=
  let z0 := (v 4 - v 0 ^ 2 * v 7) / v 10
  let zj := ((1 - v 8) * v 6 - v 10 * v 0 ^ 2 * v 9) / v 10 ^ 2
  ![z0, zj, v 0 * v 1 * z0 * v 3,
    (v 0 * v 2 * z0 + v 1 * zj) * v 3 - v 1 ^ 2 * z0 * v 3 ^ 2,
    (v 10)⁻¹, v 6 * (v 10)⁻¹ ^ 2, v 0 ^ 2 * z0, v 0 * zj,
    v 0 * (v 6 * (v 10)⁻¹ ^ 2)]

/-- The rational coefficient formulas are smooth on the positive-gap
half-space. No derivative of a normalized input profile is taken. -/
theorem contDiffOn_picardGapPolynomial (κ : ℝ) (hκ : 0 < κ) :
    ContDiffOn ℝ 1 picardGapPolynomial {v | κ ≤ v 10} := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i <;> simp only [picardGapPolynomial, Fin.isValue, inv_pow, Fin.zero_eta,
      Matrix.cons_val_zero,
    Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val]
  all_goals fun_prop (disch :=
    intro v hv
    have hp : 0 < v 10 := hκ.trans_le hv
    positivity)

/-- Continuous inputs for the z, B and inverse-gap coefficient formulas. -/
@[expose] noncomputable def picardGapInput (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) :
    C(PicardDomain c a L, Fin 11 → ℝ) :=
  let R := picardRatioProfiles e ell he z hl
  ContinuousMap.pi ![picardWidth, picardLamValues z,
    ⟨fun p => (z.1.2 p).1, z.1.2.continuous.fst⟩,
    picardProfileCoordinate (picardRatioInput e ell he z hl) 2,
    picardProfileCoordinate R 0, picardProfileCoordinate R 1,
    picardProfileCoordinate R 2, picardProfileCoordinate R 3,
    picardProfileCoordinate R 4, picardProfileCoordinate R 5,
    picardProfileCoordinate R 6]

/-- The exact normalized z and B profiles, inverse gap and its normalized
jet, and the complete z and inverse-gap value/jet formulas, in that order. -/
@[expose] noncomputable def picardGapProfiles (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell κ : ℝ) (he : 0 < ell) (hκ : 0 < κ)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q) :
    C(PicardDomain c a L, Fin 9 → ℝ) :=
  ContinuousMap.pi ![picardZRemainder e ell κ he hκ z hl hg,
    picardZJetRemainder e ell κ he hκ z hl hg,
    picardBValues e ell κ he hκ z hl hg, picardBJets e ell κ he hκ z hl hg,
    (picardGapInv ha haL e ell κ he hκ z hl hg).1.1,
    picardGapInvJetRemainder ha haL e ell κ he hκ z hl hg,
    picardZValues e ell κ he hκ z hl hg, picardZJets e ell κ he hκ z hl hg,
    (picardGapInv ha haL e ell κ he hκ z hl hg).1.2]

/-- The finite rational formula is exactly the existing reconstruction
profiles, including the continuous axis values. -/
theorem picardGapProfiles_apply (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell κ : ℝ) (he : 0 < ell) (hκ : 0 < κ)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q) (p : PicardDomain c a L) :
    picardGapProfiles ha haL e ell κ he hκ z hl hg p =
      picardGapPolynomial (picardGapInput e ell he z hl p) := by
  ext i
  fin_cases i <;> simp [picardGapProfiles, picardGapInput, picardGapPolynomial,
    picardProfileCoordinate, picardRatioProfiles_apply, picardRatioInput,
    picardZRemainder, picardZJetRemainder, picardBValues, picardBJets,
    picardGapInv_value, picardGapInv_jet, picardGapInvJetRemainder,
    picardZValues, picardZJets, picardWidth, picardLamValues,
    div_eq_mul_inv, inv_pow]

end EmcsfAcExtension.Local
