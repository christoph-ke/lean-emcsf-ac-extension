module

public import EmcsfAcExtension.Local.Construction.PicardRatios

/-! # The radial B coefficient and null expansion

Normalized values and the D1 outgoing derivative formula construct `B` on the
explicit S1 domain. The axis trace and an outgoing exponential then reconstruct
`nu` without an incoming candidate derivative. The full radial node remains open.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- An outgoing carrier primitive equals the raw oriented integral when
the continuous source has the prescribed raw values on the closed wedge. -/
theorem picardOutgoing_value_eq_of_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (ha : 0 ≤ a) (haL : a ≤ L) (f : C(PicardDomain c a L, E)) (raw : ℝ → ℝ → E)
    (hf : ∀ q : PicardDomain c a L, f q = raw q.1.1 q.1.2) (p : PicardDomain c a L) :
    (picardOutgoing ha haL f).1.1 p = ∫ s in p.1.1..p.1.2, raw p.1.1 s := by
  change (∫ s in p.1.1..p.1.2, f (picardClamp ha haL (p.1.1, s))) = _
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le p.2.1.2.1] at hs
  dsimp only
  rw [picardClamp_sectionPoint, hf (picardSectionPoint p s),
    picardSectionPoint_of_mem p ⟨hs.1, hs.2.trans p.2.1.2.2⟩]

/-- The candidate expansion has its stored outgoing derivative in section interiors. -/
theorem picardCandidateLam_hasDerivAt_aux (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) (p : PicardDomain c a L)
    (hp : p.1.1 < p.1.2) (ht : p.1.2 < c + L) :
    HasDerivAt (picardCandidateLam ha haL z p.1.1) (z.1.2 p).1 p.1.2 := by
  let F := picardCarrierLinear ha haL (ContinuousLinearMap.fst ℝ ℝ ℂ) z
  have hF (q : PicardDomain c a L) : F.1.1 q = picardCandidateLam ha haL z q.1.1 q.1.2 := by
    exact (picardCandidateLam_coe ha haL z q).symm
  exact picardCarrier_hasDerivAt_of_eq ha haL F _ hF p hp ht
/-- The candidate axis expansion, constant along every outgoing section.
This construction takes no incoming derivative of the axis trace. -/
@[expose] noncomputable def picardAxisLam (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) : PicardCarrier c a L ℝ :=
  picardCarrierOfRawDeriv (fun u _ => picardCandidateLam ha haL z u u)
    ⟨fun p => (z.1.1 (picardRadialPoint p 0)).1, z.1.1.continuous.fst.comp
      (continuous_picardRadialPoint.comp (continuous_id.prodMk continuous_const))⟩
    (ContinuousMap.const _ 0)
    (by
      intro p
      have hc := picardCandidateLam_coe ha haL z (picardRadialPoint p 0)
      have hm : (0 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
      simpa only [ContinuousMap.coe_mk, picardRadialPoint_of_mem p hm, zero_mul, add_zero] using
          hc.symm)
    (by intro p _ _; exact hasDerivAt_const p.1.2 (picardCandidateLam ha haL z p.1.1 p.1.1))

/-- The axis carrier has exactly the candidate values `lambda(u,u)`. -/
theorem picardAxisLam_value (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) (p : PicardDomain c a L) :
    (picardAxisLam ha haL z).1.1 p = picardCandidateLam ha haL z p.1.1 p.1.1 := by
  change (z.1.1 (picardRadialPoint p 0)).1 = picardCandidateLam ha haL z p.1.1 p.1.1
  have hc := picardCandidateLam_coe ha haL z (picardRadialPoint p 0)
  have hm : (0 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  simpa only [picardRadialPoint_of_mem p hm, zero_mul, add_zero] using hc.symm
/-- The continuous `B=(lambda/r)z` values after cancelling the axis width,
on the explicit positive-gap domain S1. -/
@[expose] noncomputable def picardBValues (e ell kappa : ℝ) (he : 0 < ell) (hk : 0 < kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) : C(PicardDomain c a L, ℝ) where
  toFun p := (p.1.2 - p.1.1) * (z.1.1 p).1 * picardZRemainder e ell kappa he hk z hl hgap p /
    picardRadialAverage (picardLamValues z) p
  continuous_toFun := by
    exact ((((continuous_snd.comp continuous_subtype_val).sub
      (continuous_fst.comp continuous_subtype_val)).mul z.1.1.continuous.fst).mul
      (picardZRemainder e ell kappa he hk z hl hgap).continuous).div
      (picardRadialAverage (picardLamValues z)).continuous
      (fun p => (he.trans_le (picardRadialAverage_lower _ hl p)).ne')
/-- The continuous outgoing `B` jet from internal project record D1, with no second derivative. -/
@[expose] noncomputable def picardBJets (e ell kappa : ℝ) (he : 0 < ell) (hk : 0 < kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) : C(PicardDomain c a L, ℝ) where
  toFun p := ((p.1.2 - p.1.1) * (z.1.2 p).1 * picardZRemainder e ell kappa he hk z hl hgap p +
    (z.1.1 p).1 * picardZJetRemainder e ell kappa he hk z hl hgap p) /
      picardRadialAverage (picardLamValues z) p -
      (z.1.1 p).1 ^ 2 * picardZRemainder e ell kappa he hk z hl hgap p /
        picardRadialAverage (picardLamValues z) p ^ 2
  continuous_toFun := by
    have hpos (p : PicardDomain c a L) : 0 < picardRadialAverage (picardLamValues z) p :=
      he.trans_le (picardRadialAverage_lower _ hl p)
    exact ((((((continuous_snd.comp continuous_subtype_val).sub
      (continuous_fst.comp continuous_subtype_val)).mul z.1.2.continuous.fst).mul
      (picardZRemainder e ell kappa he hk z hl hgap).continuous).add
      (z.1.1.continuous.fst.mul (picardZJetRemainder e ell kappa he hk z hl hgap).continuous)).div
      (picardRadialAverage (picardLamValues z)).continuous (fun p => (hpos p).ne')).sub
      (((z.1.1.continuous.fst.pow 2).mul (picardZRemainder e ell kappa he hk z hl
          hgap).continuous).div
        ((picardRadialAverage (picardLamValues z)).continuous.pow 2)
        (fun p => pow_ne_zero 2 (hpos p).ne'))

/-- The normalized `B` values equal its literal reconstruction formula, including the axis. -/
theorem picardBValues_eq_recon (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ) (he : 0 < ell) (hk : 0 <
    kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p : PicardDomain c a L) :
    picardBValues e ell kappa he hk z hl hgap p = picardCandidateLam ha haL z p.1.1 p.1.2 /
      Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 *
      Recon.z e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 := by
  rcases lt_or_eq_of_le p.2.1.2.1 with hp|hp
  · have hx : 0 < p.1.2 - p.1.1 := sub_pos.mpr hp
    have hR : 0 < picardRadialAverage (picardLamValues z) p :=
      he.trans_le (picardRadialAverage_lower _ hl p)
    rw [picardCandidateLam_coe ha haL z p, picard_recon_r_eq_radialAverage ha haL z p,
      ←picardZValues_eq_recon ha haL e ell kappa he hk z hl hgap p]
    change (p.1.2 - p.1.1) * (z.1.1 p).1 * picardZRemainder e ell kappa he hk z hl hgap p /
      picardRadialAverage (picardLamValues z) p = (z.1.1 p).1 /
      ((p.1.2 - p.1.1) * picardRadialAverage (picardLamValues z) p) *
      ((p.1.2 - p.1.1) ^ 2 * picardZRemainder e ell kappa he hk z hl hgap p)
    field_simp [hx.ne', hR.ne']
  · simp [picardBValues, hp, Recon.r_def]

/-- The normalized `B` jet equals the interior product and quotient-rule expression. -/
theorem picardBJets_eq_quotient_aux (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ) (he : 0 < ell) (hk
    : 0 < kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p : PicardDomain c a L)
    (hp : p.1.1 < p.1.2) : picardBJets e ell kappa he hk z hl hgap p =
      (((z.1.2 p).1 * Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 -
        picardCandidateLam ha haL z p.1.1 p.1.2 * picardCandidateLam ha haL z p.1.1 p.1.2) /
        Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 ^ 2) *
        Recon.z e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 +
        (picardCandidateLam ha haL z p.1.1 p.1.2 / Recon.r (picardCandidateLam ha haL z) p.1.1
            p.1.2) *
          picardZJets e ell kappa he hk z hl hgap p := by
  have hx : 0 < p.1.2 - p.1.1 := sub_pos.mpr hp
  have hR : 0 < picardRadialAverage (picardLamValues z) p :=
    he.trans_le (picardRadialAverage_lower _ hl p)
  have hZ : Recon.z e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 =
      (p.1.2 - p.1.1) ^ 2 * picardZRemainder e ell kappa he hk z hl hgap p :=
    (picardZValues_eq_recon ha haL e ell kappa he hk z hl hgap p).symm
  simp only [picard_recon_r_eq_radialAverage, picardCandidateLam_coe, hZ]
  change ((p.1.2 - p.1.1) * (z.1.2 p).1 * picardZRemainder e ell kappa he hk z hl hgap p +
    (z.1.1 p).1 * picardZJetRemainder e ell kappa he hk z hl hgap p) /
      picardRadialAverage (picardLamValues z) p -
      (z.1.1 p).1 ^ 2 * picardZRemainder e ell kappa he hk z hl hgap p /
        picardRadialAverage (picardLamValues z) p ^ 2 =
    (((z.1.2 p).1 * ((p.1.2 - p.1.1) * picardRadialAverage (picardLamValues z) p) -
      (z.1.1 p).1 * (z.1.1 p).1) / ((p.1.2 - p.1.1) * picardRadialAverage (picardLamValues z) p) ^
          2) *
      ((p.1.2 - p.1.1) ^ 2 * picardZRemainder e ell kappa he hk z hl hgap p) +
      ((z.1.1 p).1 / ((p.1.2 - p.1.1) * picardRadialAverage (picardLamValues z) p)) *
        ((p.1.2 - p.1.1) * picardZJetRemainder e ell kappa he hk z hl hgap p)
  field_simp [hx.ne', hR.ne']
  ring

/-- The literal `B` formula has the normalized outgoing derivative in section interiors. -/
theorem picardB_hasDerivAt_aux (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ) (he : 0 < ell) (hk : 0 <
    kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p : PicardDomain c a L)
    (hp : p.1.1 < p.1.2) (ht : p.1.2 < c + L) :
    HasDerivAt (fun v => picardCandidateLam ha haL z p.1.1 v /
      Recon.r (picardCandidateLam ha haL z) p.1.1 v *
      Recon.z e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 v)
      (picardBJets e ell kappa he hk z hl hgap p) p.1.2 := by
  have hL := picardCandidateLam_hasDerivAt_aux ha haL z p hp ht
  have hc : Continuous (picardCandidateLam ha haL z p.1.1) :=
    (continuous_picardCandidateLam ha haL z).comp (continuous_const.prodMk continuous_id)
  have hr : HasDerivAt (Recon.r (picardCandidateLam ha haL z) p.1.1)
      (picardCandidateLam ha haL z p.1.1 p.1.2) p.1.2 :=
    (hc.integral_hasStrictDerivAt p.1.1 p.1.2).hasDerivAt
  have hrp : 0 < Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 := by
    rw [picard_recon_r_eq_radialAverage ha haL z p]
    exact mul_pos (sub_pos.mpr hp) (he.trans_le (picardRadialAverage_lower _ hl p))
  have hd := (hL.fun_div hr hrp.ne').fun_mul (picardZ_hasDerivAt_aux ha haL e ell kappa he hk z hl
      hgap p hp ht)
  rw [picardBJets_eq_quotient_aux ha haL e ell kappa he hk z hl hgap p hp]
  exact hd
/-- The `B` coefficient as a compatible value and outgoing first-jet carrier on S1. -/
@[expose] noncomputable def picardBRecon (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ) (he : 0 < ell)
    (hk : 0 < kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) : PicardCarrier c a L ℝ :=
  picardCarrierOfRawDeriv
    (fun u v => picardCandidateLam ha haL z u v / Recon.r (picardCandidateLam ha haL z) u v *
      Recon.z e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) u v)
    (picardBValues e ell kappa he hk z hl hgap) (picardBJets e ell kappa he hk z hl hgap)
    (picardBValues_eq_recon ha haL e ell kappa he hk z hl hgap)
    (fun p hp ht => picardB_hasDerivAt_aux ha haL e ell kappa he hk z hl hgap p hp ht)
/-- The null expansion reconstructed from the axis value and the outgoing exponential. -/
@[expose] noncomputable def picardNuRecon (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ) (he : 0 <
    ell) (hk : 0 < kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) : PicardCarrier c a L ℝ :=
  picardCarrierMul ha haL (picardCarrierNeg ha haL (picardAxisLam ha haL z))
    (picardCarrierExp ha haL (picardOutgoing ha haL (picardBValues e ell kappa he hk z hl hgap)))

/-- The null-expansion carrier has exactly the literal `Recon.nu` values. -/
theorem picardNuRecon_value (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ) (he : 0 < ell) (hk : 0 <
    kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p : PicardDomain c a L) :
    (picardNuRecon ha haL e ell kappa he hk z hl hgap).1.1 p =
      Recon.nu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 := by
  change -(picardAxisLam ha haL z).1.1 p * Real.exp
    ((picardOutgoing ha haL (picardBValues e ell kappa he hk z hl hgap)).1.1 p) = _
  rw [picardAxisLam_value, picardOutgoing_value_eq_of_eq ha haL _
    (fun u v => picardCandidateLam ha haL z u v / Recon.r (picardCandidateLam ha haL z) u v *
      Recon.z e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) u v)
          (picardBValues_eq_recon ha haL e ell kappa he hk z hl hgap) p,
    Recon.nu_def]


end EmcsfAcExtension.Local
