module

public import EmcsfAcExtension.Local.Construction.PicardGapEstimates
public import EmcsfAcExtension.Local.Construction.PicardSources

/-! # Finite dimensional formulas for the incoming sources

After the weighted cancellations, G, C_A, W and P and their outgoing jets
are polynomial functions of the normalized profiles and the reconstructed
null expansion. This module records those exact formulas.
-/

public section

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- The finite polynomial formulas for the values and outgoing jets of
`G,C_A,W,P`. The real inputs are width, expansion, expansion jet, reciprocal
radial average, inverse gap, normalized inverse-gap jet, normalized z and its
jet, normalized charge, charge kernel, and the values and jet of nu. The
complex inputs are the scalar remainder, candidate scalar jet, phi and phi jet. -/
@[expose] noncomputable def picardSourcePolynomial (e : ℝ)
    (v : (Fin 12 → ℝ) × (Fin 4 → ℂ)) : (Fin 4 → ℝ) × (Fin 4 → ℂ) :=
  let r := v.1
  let f := v.2
  let g0 := r 10 * r 6
  let gj := r 0 * r 11 * r 6 + r 10 * r 7
  let ca0 := 2 * r 10 * r 1 * r 8 * r 4
  let caj := 2 * (((r 0 * (r 11 * r 1 + r 10 * r 2) * r 8 + r 10 * r 1 * r 9) * r 4) +
    r 0 ^ 2 * (r 10 * r 1 * r 8) * r 5)
  let w0 := (r 6 : ℂ) * f 0 + Complex.I * e * (r 8 : ℂ) * f 2 * (r 4 : ℂ)
  let wj := (r 7 : ℂ) * f 0 + (r 6 : ℂ) * (f 1 - f 3) + Complex.I * e *
    (((r 9 : ℂ) * f 2 + (r 0 : ℂ) * (r 8 : ℂ) * f 3) * (r 4 : ℂ) +
      (r 0 : ℂ) ^ 2 * (r 8 : ℂ) * f 2 * (r 5 : ℂ))
  let p0 := -(r 10 : ℂ) * w0
  let pj := -(r 0 : ℂ) * (r 11 : ℂ) * w0 - (r 10 : ℂ) * wj
  (![r 0 * r 3 * g0, r 3 * gj - r 1 * r 3 ^ 2 * g0,
      r 0 * r 3 ^ 2 * ca0, r 3 ^ 2 * caj - 2 * r 1 * r 3 ^ 3 * ca0],
    ![(r 0 : ℂ) ^ 3 * w0, (r 0 : ℂ) ^ 2 * wj,
      (r 0 : ℂ) ^ 2 * (r 3 : ℂ) * p0,
      (r 0 : ℂ) * ((r 3 : ℂ) * pj - (r 1 : ℂ) * (r 3 : ℂ) ^ 2 * p0)])

@[fun_prop] private theorem picard_contDiff_ofReal_aux :
    ContDiff ℝ 1 (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff

/-- The same polynomial with the coupling included as an input coordinate.
This fixed formula makes its uniform bound depend only on the coupling norm. -/
@[expose] noncomputable def picardUniversalSourcePolynomial
    (v : ℝ × ((Fin 12 → ℝ) × (Fin 4 → ℂ))) : (Fin 4 → ℝ) × (Fin 4 → ℂ) :=
  picardSourcePolynomial v.1 v.2

/-- The source polynomial is jointly smooth in the coupling and all profiles. -/
theorem contDiff_picardUniversalSourcePolynomial :
    ContDiff ℝ 1 picardUniversalSourcePolynomial := by
  change ContDiff ℝ 1 (fun v : ℝ × ((Fin 12 → ℝ) × (Fin 4 → ℂ)) =>
    ((picardSourcePolynomial v.1 v.2).1, (picardSourcePolynomial v.1 v.2).2))
  apply ContDiff.prodMk
  all_goals
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp only [picardSourcePolynomial, Fin.isValue, neg_mul, mul_neg,
        sub_neg_eq_add,
      Fin.zero_eta, Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk,
          Matrix.cons_val] <;> fun_prop

/-- The continuous real and complex input vectors for the incoming-source
polynomial, built from the exact outgoing reconstruction profiles. -/
@[expose] noncomputable def picardSourceInput (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell κ : ℝ) (he : 0 < ell) (hκ : 0 < κ)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q) :
    C(PicardDomain c a L, (Fin 12 → ℝ) × (Fin 4 → ℂ)) :=
  let R := picardGapProfiles ha haL e ell κ he hκ z hl hg
  let N := picardNuRecon ha haL e ell κ he hκ z hl hg
  ContinuousMap.prodMk
    (ContinuousMap.pi ![picardWidth, picardLamValues z,
      ⟨fun p => (z.1.2 p).1, z.1.2.continuous.fst⟩,
      picardProfileCoordinate (picardRatioInput e ell he z hl) 2,
      picardProfileCoordinate R 4, picardProfileCoordinate R 5,
      picardProfileCoordinate R 0, picardProfileCoordinate R 1,
      picardChargeRemainder e ell he z hl, picardChargeKernel e ell he z hl,
      N.1.1, N.1.2])
    (ContinuousMap.pi ![picardScalarRemainder ell he z hl, picardHJets z,
      picardPhiValues ell he z hl, picardPhiJets ell he z hl])

/-- The exact incoming-source values and outgoing jets as continuous finite
vectors: the real vector is `G,G_v,C_A,(C_A)_v`, and the complex vector is
`W,W_v,P,P_v`. -/
@[expose] noncomputable def picardSourceProfiles (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell κ : ℝ) (he : 0 < ell) (hκ : 0 < κ)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q) :
    C(PicardDomain c a L, (Fin 4 → ℝ) × (Fin 4 → ℂ)) :=
  let G := picardGRecon ha haL e ell κ he hκ z hl hg
  let A := picardCARecon ha haL e ell κ he hκ z hl hg
  let W := picardWRecon ha haL e ell κ he hκ z hl hg
  let P := picardPRecon ha haL e ell κ he hκ z hl hg
  ContinuousMap.prodMk (ContinuousMap.pi ![G.1.1, G.1.2, A.1.1, A.1.2])
    (ContinuousMap.pi ![W.1.1, W.1.2, P.1.1, P.1.2])

/-- The finite polynomial is exactly the reconstructed incoming sources,
including their axis jets. This identity uses no candidate second derivative. -/
theorem picardSourceProfiles_apply (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell κ : ℝ) (he : 0 < ell) (hκ : 0 < κ)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q) (p : PicardDomain c a L) :
    picardSourceProfiles ha haL e ell κ he hκ z hl hg p =
      picardSourcePolynomial e (picardSourceInput ha haL e ell κ he hκ z hl hg p) := by
  apply Prod.ext
  all_goals
    ext i
    fin_cases i
    all_goals
      simp only [picardSourceProfiles, picardGRecon, picardDivideRadius, picardCarrierOfRawDeriv,
        picardDivisionValues, picardGNumeratorRemainder, ContinuousMap.mul_apply, smul_eq_mul,
        picardDivisionJets, picardGNumeratorJetRemainder, picardWidth, ContinuousMap.add_apply,
        ContinuousMap.coe_mk, div_eq_mul_inv, picardCARecon, picardDivideRadiusSq,
            picardAverageInvSmul,
        picardCANumeratorRemainder, picardCarrierLinear, ContinuousLinearMap.coe_fst',
        ContinuousMap.coe_smul, ContinuousMap.coe_mul, Pi.smul_apply, Pi.mul_apply,
        picardCANumeratorJetRemainder, smul_add, ContinuousMap.coe_add, Pi.add_apply,
        ContinuousMap.coe_pow, Pi.pow_apply, picardPRecon, picardWidthSmul,
            picardPNumeratorRemainder,
        picardComplexProfile, picardWRemainder, picardScalarRecon, neg_mul, ContinuousMap.neg_apply,
        smul_neg, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_inv,
        picardPNumeratorJetRemainder, picardWJetRemainder, picardScalarDifferenceRecon,
        picardCarrierAdd, ContinuousLinearMap.coe_snd', picardCarrierNeg, ContinuousMap.sub_apply,
        Complex.ofReal_mul, Complex.ofReal_pow, sub_neg_eq_add, ContinuousMap.prod_eval,
        ContinuousMap.pi_eval, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
            picardSourcePolynomial,
        picardSourceInput, picardLamValues, picardProfileCoordinate, picardRatioInput,
            Matrix.cons_val,
        picardGapProfiles, Matrix.cons_val_one, picardHJets, inv_pow, mul_neg, neg_sub, Fin.mk_one,
        Fin.reduceFinMk, picardWRecon_value_profile, picardWRecon_jet_profile, neg_inj] <;> ring

end EmcsfAcExtension.Local
