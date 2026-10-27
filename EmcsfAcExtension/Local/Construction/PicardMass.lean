module

public import EmcsfAcExtension.Local.Construction.PicardCharge
public import EmcsfAcExtension.Local.Construction.PicardAlgebra

/-! # Mass reconstruction in the outgoing Picard carrier

The integrating factor constructs continuous values and outgoing first jets.
Rescaling the formula factors the cubic axis order without differentiating a
normalized scalar remainder. This is part of the radial C1 construction.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- Solve the real outgoing equation `m_v=b-a*m` with zero axis value by
a product of outgoing carriers and integrating factors. -/
@[expose] noncomputable def picardMassLinear (ha : 0 ≤ a) (haL : a ≤ L)
    (am bm : C(PicardDomain c a L, ℝ)) : PicardCarrier c a L ℝ :=
  let S := picardOutgoing ha haL am
  picardCarrierMul ha haL (picardCarrierExp ha haL (picardCarrierNeg ha haL S))
    (picardOutgoing ha haL (bm * (picardCarrierExp ha haL S).1.1))

/-- The carrier solution has the exact outgoing integrating-factor formula. -/
theorem picardMassLinear_value (ha : 0 ≤ a) (haL : a ≤ L)
    (am bm : C(PicardDomain c a L, ℝ)) (p : PicardDomain c a L) :
    (picardMassLinear ha haL am bm).1.1 p =
      ∫ s in p.1.1..p.1.2, bm (picardClamp ha haL (p.1.1, s)) *
        Real.exp (-∫ t in s..p.1.2, am (picardClamp ha haL (p.1.1, t))) := by
  let S := picardOutgoing ha haL am
  change Real.exp (-S.1.1 p) * (∫ s in p.1.1..p.1.2,
    bm (picardClamp ha haL (p.1.1, s)) * Real.exp (S.1.1 (picardClamp ha haL (p.1.1, s)))) = _
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le p.2.1.2.1] at hs
  have hi := picardCarrier_integral_between S p ⟨p.2.1.2.1, p.2.1.2.2⟩
    ⟨hs.1, hs.2.trans p.2.1.2.2⟩
  change (∫ t in s..p.1.2, am (picardSectionPoint p t)) =
    S.1.1 (picardSectionPoint p p.1.2) - S.1.1 (picardSectionPoint p s) at hi
  have hi' : (∫ t in s..p.1.2, am (picardClamp ha haL (p.1.1, t))) =
      S.1.1 p - S.1.1 (picardClamp ha haL (p.1.1, s)) := by
    simpa only [picardClamp_sectionPoint, picardSectionPoint_self] using hi
  dsimp only
  rw [hi']
  have he : Real.exp (-S.1.1 p) * Real.exp (S.1.1 (picardClamp ha haL (p.1.1, s))) =
      Real.exp (-(S.1.1 p - S.1.1 (picardClamp ha haL (p.1.1, s)))) := by
    rw [←Real.exp_add]
    congr 1
    ring
  calc
    _ = bm (picardClamp ha haL (p.1.1, s)) *
        (Real.exp (-S.1.1 p) * Real.exp (S.1.1 (picardClamp ha haL (p.1.1, s)))) := by ring
    _ = _ := by rw [he]

/-- The continuous outgoing jet satisfies the linear equation on the closed wedge. -/
theorem picardMassLinear_jet (ha : 0 ≤ a) (haL : a ≤ L)
    (am bm : C(PicardDomain c a L, ℝ)) (p : PicardDomain c a L) :
    (picardMassLinear ha haL am bm).1.2 p = bm p - am p * (picardMassLinear ha haL am bm).1.1 p :=
        by
  let S := picardOutgoing ha haL am
  let V := picardOutgoing ha haL (bm * (picardCarrierExp ha haL S).1.1)
  change Real.exp (-S.1.1 p) * (-am p) * V.1.1 p +
    Real.exp (-S.1.1 p) * (bm p * Real.exp (S.1.1 p)) =
    bm p - am p * (Real.exp (-S.1.1 p) * V.1.1 p)
  have he : Real.exp (-S.1.1 p) * Real.exp (S.1.1 p) = 1 := by
    rw [←Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ = -(am p * (Real.exp (-S.1.1 p) * V.1.1 p)) +
        bm p * (Real.exp (-S.1.1 p) * Real.exp (S.1.1 p)) := by ring
    _ = _ := by rw [he]; ring




/-- The continuous mass integrating-factor source, factored by one axis width. -/
@[expose] noncomputable def picardMassAm (ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) :
    C(PicardDomain c a L, ℝ) where
  toFun p := (p.1.2 - p.1.1) * (z.1.1 p).1 * ‖picardScalarRemainder ell he z hl p‖ ^ 2 /
    picardRadialAverage (picardLamValues z) p
  continuous_toFun := by
    have hpos (p : PicardDomain c a L) : 0 < picardRadialAverage (picardLamValues z) p :=
      he.trans_le (picardRadialAverage_lower _ hl p)
    exact ((((continuous_snd.comp continuous_subtype_val).sub
      (continuous_fst.comp continuous_subtype_val)).mul z.1.1.continuous.fst).mul
      ((picardScalarRemainder ell he z hl).continuous.norm.pow 2)).div
      (picardRadialAverage (picardLamValues z)).continuous (fun p => (hpos p).ne')
/-- The continuous quadratic mass-source coefficient after removing the width squared. -/
@[expose] noncomputable def picardMassKernel (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) :
    C(PicardDomain c a L, ℝ) where
  toFun p := ((z.1.1 p).1 / 2) *
    (‖picardScalarRemainder ell he z hl p‖ ^ 2 + (p.1.2 - p.1.1) ^ 2 *
      picardChargeRemainder e ell he z hl p ^ 2 / picardRadialAverage (picardLamValues z) p ^ 2)
  continuous_toFun := by
    have hpos (p : PicardDomain c a L) : 0 < picardRadialAverage (picardLamValues z) p :=
      he.trans_le (picardRadialAverage_lower _ hl p)
    have hx : Continuous (fun p : PicardDomain c a L => p.1.2 - p.1.1) :=
      (continuous_snd.comp continuous_subtype_val).sub (continuous_fst.comp continuous_subtype_val)
    exact (z.1.1.continuous.fst.div_const 2).mul
      (((picardScalarRemainder ell he z hl).continuous.norm.pow 2).add
        (((hx.pow 2).mul ((picardChargeRemainder e ell he z hl).continuous.pow 2)).div
          ((picardRadialAverage (picardLamValues z)).continuous.pow 2)
          (fun p => pow_ne_zero 2 (hpos p).ne')))
/-- The continuous quadratic outgoing mass source, including its factor `1/2`. -/
@[expose] noncomputable def picardMassBm (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) :
    C(PicardDomain c a L, ℝ) where
  toFun p := (p.1.2 - p.1.1) ^ 2 * picardMassKernel e ell he z hl p
  continuous_toFun := (((continuous_snd.comp continuous_subtype_val).sub
    (continuous_fst.comp continuous_subtype_val)).pow 2).mul
      (picardMassKernel e ell he z hl).continuous

/-- The continuous integrating-factor source equals the literal raw source,
including the axis. Only candidate lambda positivity is required. -/
theorem picardMassAm_eq_recon (ha : 0 ≤ a) (haL : a ≤ L) (ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) :
    picardMassAm ell he z hl p = picardCandidateLam ha haL z p.1.1 p.1.2 *
      ‖Recon.ratio (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2‖ ^ 2 /
      Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 := by
  rcases lt_or_eq_of_le p.2.1.2.1 with hp|hp
  · have hx : 0 < p.1.2 - p.1.1 := sub_pos.mpr hp
    have hR : 0 < picardRadialAverage (picardLamValues z) p :=
      he.trans_le (picardRadialAverage_lower _ hl p)
    rw [picardCandidateLam_coe ha haL z p, picard_recon_r_eq_radialAverage ha haL z p,
      picard_ratio_eq_normalized ha haL ell he z hl p, norm_smul, Real.norm_eq_abs, abs_of_pos hx]
    change (p.1.2 - p.1.1) * (z.1.1 p).1 * ‖picardScalarRemainder ell he z hl p‖ ^ 2 /
      picardRadialAverage (picardLamValues z) p = (z.1.1 p).1 *
      ((p.1.2 - p.1.1) * ‖picardScalarRemainder ell he z hl p‖) ^ 2 /
        ((p.1.2 - p.1.1) * picardRadialAverage (picardLamValues z) p)
    field_simp [hx.ne', hR.ne']
  · simp [picardMassAm, hp, Recon.ratio_def, Recon.phi_def, Recon.r_def]

/-- The continuous mass source equals the literal raw mass source, including
the axis and the exact factor `1/2`. No Hawking gap is assumed. -/
theorem picardMassBm_eq_recon (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) :
    picardMassBm e ell he z hl p = (1 / 2 : ℝ) * picardCandidateLam ha haL z p.1.1 p.1.2 *
      (‖Recon.ratio (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2‖ ^ 2 +
        Recon.Q e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 ^ 2 /
          Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 ^ 2) := by
  rcases lt_or_eq_of_le p.2.1.2.1 with hp|hp
  · have hx : 0 < p.1.2 - p.1.1 := sub_pos.mpr hp
    have hR : 0 < picardRadialAverage (picardLamValues z) p :=
      he.trans_le (picardRadialAverage_lower _ hl p)
    have hQ := (picardChargeRecon_value ha haL e ell he z hl p).symm.trans
      (picardChargeRecon_normalized ha haL e ell he z hl p)
    rw [picardCandidateLam_coe ha haL z p, picard_recon_r_eq_radialAverage ha haL z p,
      picard_ratio_eq_normalized ha haL ell he z hl p, hQ, norm_smul, Real.norm_eq_abs, abs_of_pos
          hx]
    change (p.1.2 - p.1.1) ^ 2 * (((z.1.1 p).1 / 2) *
      (‖picardScalarRemainder ell he z hl p‖ ^ 2 + (p.1.2 - p.1.1) ^ 2 *
        picardChargeRemainder e ell he z hl p ^ 2 / picardRadialAverage (picardLamValues z) p ^ 2))
            =
      (1 / 2 : ℝ) * (z.1.1 p).1 * (((p.1.2 - p.1.1) * ‖picardScalarRemainder ell he z hl p‖) ^ 2 +
        ((p.1.2 - p.1.1) ^ 3 * picardChargeRemainder e ell he z hl p) ^ 2 /
          ((p.1.2 - p.1.1) * picardRadialAverage (picardLamValues z) p) ^ 2)
    field_simp [hx.ne', hR.ne']
  · simp [picardMassBm, hp, Recon.ratio_def, Recon.phi_def, Recon.r_def, Recon.q_def]




/-- The mass reconstruction as a compatible continuous value and first-jet carrier. -/
@[expose] noncomputable def picardMassRecon (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) :
    PicardCarrier c a L ℝ :=
  picardMassLinear ha haL (picardMassAm ell he z hl) (picardMassBm e ell he z hl)

/-- The mass carrier has exactly the existing `Recon.m` values. -/
theorem picardMassRecon_value (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) :
    (picardMassRecon ha haL e ell he z hl).1.1 p =
      Recon.m e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 := by
  change (picardMassLinear ha haL (picardMassAm ell he z hl) (picardMassBm e ell he z hl)).1.1 p = _
  rw [picardMassLinear_value, Recon.m_def, ←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le p.2.1.2.1] at hs
  have hInner : (∫ t in s..p.1.2, picardMassAm ell he z hl (picardClamp ha haL (p.1.1, t))) =
      ∫ t in s..p.1.2, picardCandidateLam ha haL z p.1.1 t *
        ‖Recon.ratio (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 t‖ ^ 2 /
          Recon.r (picardCandidateLam ha haL z) p.1.1 t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hs.2] at ht
    let q := picardSectionPoint p t
    have hq : q.1 = (p.1.1, t) := picardSectionPoint_of_mem p
      ⟨hs.1.trans ht.1, ht.2.trans p.2.1.2.2⟩
    have hClamp : picardClamp ha haL (p.1.1, t) = q := by
      simpa only [hq] using picardClamp_coe ha haL q
    dsimp only
    rw [hClamp, picardMassAm_eq_recon ha haL ell he z hl q, hq]
  let q := picardSectionPoint p s
  have hq : q.1 = (p.1.1, s) := picardSectionPoint_of_mem p ⟨hs.1, hs.2.trans p.2.1.2.2⟩
  have hClamp : picardClamp ha haL (p.1.1, s) = q := by
    simpa only [hq] using picardClamp_coe ha haL q
  dsimp only
  rw [hClamp, picardMassBm_eq_recon ha haL e ell he z hl q, hq, hInner]
  ring




/-- The continuous normalized mass `m/(v-u)^3`, defined without dividing
by the axis width. Its rescaled exponential uses the normalized outgoing tail. -/
@[expose] noncomputable def picardMassRemainder (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) :
    C(PicardDomain c a L, ℝ) where
  toFun p := ∫ t in (0 : ℝ)..1, t ^ 2 * picardMassKernel e ell he z hl (picardRadialPoint p t) *
    Real.exp (-(p.1.2 - p.1.1) * picardRadialTail (picardMassAm ell he z hl) (p, t))
  continuous_toFun := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact ((continuous_snd.pow 2).mul
      ((picardMassKernel e ell he z hl).continuous.comp continuous_picardRadialPoint)).mul
        (Real.continuous_exp.comp ((((continuous_snd.comp continuous_subtype_val).sub
          (continuous_fst.comp continuous_subtype_val)).comp continuous_fst).neg.mul
          (picardRadialTail (picardMassAm ell he z hl)).continuous))

/-- Exact cubic vanishing of the mass carrier on the full closed wedge. -/
theorem picardMassRecon_normalized (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) :
    (picardMassRecon ha haL e ell he z hl).1.1 p =
      (p.1.2 - p.1.1) ^ 3 * picardMassRemainder e ell he z hl p := by
  let x := p.1.2 - p.1.1
  let am := picardMassAm ell he z hl
  let bm := picardMassBm e ell he z hl
  let K := picardMassKernel e ell he z hl
  let F : ℝ → ℝ := fun s => bm (picardClamp ha haL (p.1.1, s)) *
    Real.exp (-∫ t in s..p.1.2, am (picardClamp ha haL (p.1.1, t)))
  have hv : x * 1 + p.1.1 = p.1.2 := by dsimp [x]; ring
  have hScaled := intervalIntegral.smul_integral_comp_mul_add (f := F) (a := 0) (b := 1) x p.1.1
  simp only [smul_eq_mul, mul_zero, zero_add] at hScaled
  rw [hv] at hScaled
  change (picardMassLinear ha haL am bm).1.1 p = _
  rw [picardMassLinear_value]
  change (∫ s in p.1.1..p.1.2, F s) = _
  rw [←hScaled]
  change x * (∫ t in (0 : ℝ)..1, F (x * t + p.1.1)) =
    x ^ 3 * (∫ t in (0 : ℝ)..1, t ^ 2 * K (picardRadialPoint p t) *
      Real.exp (-x * picardRadialTail am (p, t)))
  rw [←intervalIntegral.integral_const_mul, ←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  have hClamp (r : ℝ) (hr : r ∈ Icc 0 1) :
      picardClamp ha haL (p.1.1, x * r + p.1.1) = picardRadialPoint p r := by
    simpa only [picardRadialPoint_of_mem p hr, x, add_comm, mul_comm] using
      picardClamp_coe ha haL (picardRadialPoint p r)
  have hTail : (∫ r in (x * t + p.1.1)..p.1.2, am (picardClamp ha haL (p.1.1, r))) =
      x * picardRadialTail am (p, t) := by
    have hs := intervalIntegral.smul_integral_comp_mul_add
      (f := fun r => am (picardClamp ha haL (p.1.1, r))) (a := t) (b := 1) x p.1.1
    rw [hv] at hs
    have hI : (∫ r in t..1, am (picardClamp ha haL (p.1.1, x * r + p.1.1))) =
        ∫ r in t..1, am (picardRadialPoint p r) := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le ht.2] at hr
      dsimp only
      rw [hClamp r ⟨ht.1.trans hr.1, hr.2⟩]
    rw [hI] at hs
    exact hs.symm
  dsimp only
  change x * (bm (picardClamp ha haL (p.1.1, x * t + p.1.1)) * Real.exp
    (-∫ r in (x * t + p.1.1)..p.1.2, am (picardClamp ha haL (p.1.1, r)))) = _
  rw [hTail, hClamp t ht]
  simp only [neg_mul]
  change x * ((((picardRadialPoint p t).1.2 - (picardRadialPoint p t).1.1) ^ 2 *
    K (picardRadialPoint p t)) * Real.exp (-(x * picardRadialTail am (p, t)))) = _
  rw [picardRadialPoint_of_mem p ht]
  dsimp only
  dsimp only [x]
  ring


/-- The mass carrier's continuous jet satisfies the outgoing mass ODE everywhere. -/
theorem picardMassRecon_jet (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) :
    (picardMassRecon ha haL e ell he z hl).1.2 p = picardMassBm e ell he z hl p -
      picardMassAm ell he z hl p * (picardMassRecon ha haL e ell he z hl).1.1 p :=
  picardMassLinear_jet ha haL _ _ p

end EmcsfAcExtension.Local
