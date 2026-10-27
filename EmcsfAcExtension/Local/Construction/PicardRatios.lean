module

public import EmcsfAcExtension.Local.Construction.PicardMass

/-! # Normalized radial quotients and the positive-gap domain

Continuous values and outgoing first jets are constructed for the mass aspect,
charge-square quotient, and `z`. The S1 gap is explicit in every `z` construction.
This module supplies part of radial C1 regularity and closes no graph node.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- Transfer an interior outgoing derivative to a raw function whose
values agree with a carrier on the closed wedge. -/
theorem picardCarrier_hasDerivAt_of_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (ha : 0 ≤ a) (haL : a ≤ L) (F : PicardCarrier c a L E) (raw : ℝ → ℝ → E)
    (hF : ∀ p : PicardDomain c a L, F.1.1 p = raw p.1.1 p.1.2)
    (p : PicardDomain c a L) (hp : p.1.1 < p.1.2) (ht : p.1.2 < c + L) :
    HasDerivAt (raw p.1.1) (F.1.2 p) p.1.2 := by
  have hd := picardCarrierValue_hasDerivAt ha haL F p hp ht
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hp ht] with v hv
  let q : PicardDomain c a L := ⟨(p.1.1, v), ⟨⟨p.2.1.1, hv.1.le, hv.2.le⟩, p.2.2⟩⟩
  exact ((picardCarrierValue_coe ha haL F q).trans (hF q)).symm
/-- The continuous quadratic mass-aspect coefficient `2 m_0 / R`. -/
@[expose] noncomputable def picardMuRemainder (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) : C(PicardDomain c a L, ℝ) where
  toFun p := 2 * picardMassRemainder e ell he z hl p / picardRadialAverage (picardLamValues z) p
  continuous_toFun := by
    exact (continuous_const.mul (picardMassRemainder e ell he z hl).continuous).div
      (picardRadialAverage (picardLamValues z)).continuous
      (fun p => (he.trans_le (picardRadialAverage_lower _ hl p)).ne')
/-- Continuous quadratic mass-aspect values on the whole closed wedge. -/
@[expose] noncomputable def picardMuValues (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) : C(PicardDomain c a L, ℝ) where
  toFun p := (p.1.2 - p.1.1) ^ 2 * picardMuRemainder e ell he z hl p
  continuous_toFun := (((continuous_snd.comp continuous_subtype_val).sub
    (continuous_fst.comp continuous_subtype_val)).pow 2).mul (picardMuRemainder e ell he z
        hl).continuous
/-- The continuous quartic coefficient of `Q^2/r^2`. -/
@[expose] noncomputable def picardQSquareRemainder (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) : C(PicardDomain c a L, ℝ) where
  toFun p := picardChargeRemainder e ell he z hl p ^ 2 /
    picardRadialAverage (picardLamValues z) p ^ 2
  continuous_toFun := ((picardChargeRemainder e ell he z hl).continuous.pow 2).div
    ((picardRadialAverage (picardLamValues z)).continuous.pow 2)
    (fun p => pow_ne_zero 2 (he.trans_le (picardRadialAverage_lower _ hl p)).ne')
/-- The continuous linear coefficient of the outgoing mass-aspect jet,
from the normalized mass ODE. No second candidate derivative is used. -/
@[expose] noncomputable def picardMuJetRemainder (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) : C(PicardDomain c a L, ℝ) where
  toFun p := (z.1.1 p).1 / picardRadialAverage (picardLamValues z) p *
    ((1 - picardMuValues e ell he z hl p) * ‖picardScalarRemainder ell he z hl p‖ ^ 2 +
      (p.1.2 - p.1.1) ^ 2 * picardQSquareRemainder e ell he z hl p - picardMuRemainder e ell he z hl
          p)
  continuous_toFun := by
    have hx : Continuous (fun p : PicardDomain c a L => p.1.2 - p.1.1) :=
      (continuous_snd.comp continuous_subtype_val).sub (continuous_fst.comp continuous_subtype_val)
    exact (z.1.1.continuous.fst.div (picardRadialAverage (picardLamValues z)).continuous
      (fun p => (he.trans_le (picardRadialAverage_lower _ hl p)).ne')).mul
      ((((continuous_const.sub (picardMuValues e ell he z hl).continuous).mul
        ((picardScalarRemainder ell he z hl).continuous.norm.pow 2)).add
        ((hx.pow 2).mul (picardQSquareRemainder e ell he z hl).continuous)).sub
        (picardMuRemainder e ell he z hl).continuous)
/-- The outgoing mass-aspect jet with its linear axis factor. -/
@[expose] noncomputable def picardMuJets (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) : C(PicardDomain c a L, ℝ) where
  toFun p := (p.1.2 - p.1.1) * picardMuJetRemainder e ell he z hl p
  continuous_toFun := ((continuous_snd.comp continuous_subtype_val).sub
    (continuous_fst.comp continuous_subtype_val)).mul (picardMuJetRemainder e ell he z
        hl).continuous

/-- The normalized mass-aspect values equal the literal `Recon.mu`. -/
theorem picardMuValues_eq_recon (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) : picardMuValues e ell he z hl p =
    Recon.mu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 := by
  rcases lt_or_eq_of_le p.2.1.2.1 with hp|hp
  · have hx : 0 < p.1.2 - p.1.1 := sub_pos.mpr hp
    have hR : 0 < picardRadialAverage (picardLamValues z) p :=
      he.trans_le (picardRadialAverage_lower _ hl p)
    rw [Recon.mu_def, ←picardMassRecon_value ha haL e ell he z hl p,
      picardMassRecon_normalized ha haL e ell he z hl p, picard_recon_r_eq_radialAverage ha haL z p]
    change (p.1.2 - p.1.1) ^ 2 * (2 * picardMassRemainder e ell he z hl p /
      picardRadialAverage (picardLamValues z) p) =
      2 * ((p.1.2 - p.1.1) ^ 3 * picardMassRemainder e ell he z hl p) /
        ((p.1.2 - p.1.1) * picardRadialAverage (picardLamValues z) p)
    field_simp [hx.ne', hR.ne']
  · simp [picardMuValues, hp, Recon.mu_def, Recon.r_def]

/-- The normalized mass-aspect jet equals the off-axis quotient-rule expression. -/
theorem picardMuJets_eq_quotient_aux (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) (hp : p.1.1 < p.1.2) :
    picardMuJets e ell he z hl p =
      (2 * (picardMassRecon ha haL e ell he z hl).1.2 p *
          Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 -
        2 * (picardMassRecon ha haL e ell he z hl).1.1 p * picardCandidateLam ha haL z p.1.1 p.1.2)
            /
        Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 ^ 2 := by
  have hx : 0 < p.1.2 - p.1.1 := sub_pos.mpr hp
  have hR : 0 < picardRadialAverage (picardLamValues z) p :=
    he.trans_le (picardRadialAverage_lower _ hl p)
  rw [picardMassRecon_jet]
  simp only [picardMassRecon_normalized, picard_recon_r_eq_radialAverage, picardCandidateLam_coe]
  change (p.1.2 - p.1.1) * ((z.1.1 p).1 / picardRadialAverage (picardLamValues z) p *
    ((1 - (p.1.2 - p.1.1) ^ 2 * (2 * picardMassRemainder e ell he z hl p /
      picardRadialAverage (picardLamValues z) p)) * ‖picardScalarRemainder ell he z hl p‖ ^ 2 +
      (p.1.2 - p.1.1) ^ 2 * (picardChargeRemainder e ell he z hl p ^ 2 /
        picardRadialAverage (picardLamValues z) p ^ 2) -
        2 * picardMassRemainder e ell he z hl p / picardRadialAverage (picardLamValues z) p)) =
      (2 * ((p.1.2 - p.1.1) ^ 2 * (((z.1.1 p).1 / 2) *
          (‖picardScalarRemainder ell he z hl p‖ ^ 2 + (p.1.2 - p.1.1) ^ 2 *
            picardChargeRemainder e ell he z hl p ^ 2 / picardRadialAverage (picardLamValues z) p ^
                2)) -
          ((p.1.2 - p.1.1) * (z.1.1 p).1 * ‖picardScalarRemainder ell he z hl p‖ ^ 2 /
            picardRadialAverage (picardLamValues z) p) *
            ((p.1.2 - p.1.1) ^ 3 * picardMassRemainder e ell he z hl p)) *
            ((p.1.2 - p.1.1) * picardRadialAverage (picardLamValues z) p) -
        2 * ((p.1.2 - p.1.1) ^ 3 * picardMassRemainder e ell he z hl p) * (z.1.1 p).1) /
        ((p.1.2 - p.1.1) * picardRadialAverage (picardLamValues z) p) ^ 2
  field_simp [hx.ne', hR.ne']; ring

/-- The literal mass aspect has the normalized outgoing derivative in section interiors. -/
theorem picardMu_hasDerivAt_aux (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) (hp : p.1.1 < p.1.2) (ht : p.1.2 < c + L) :
    HasDerivAt (Recon.mu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1)
      (picardMuJets e ell he z hl p) p.1.2 := by
  have hm := picardCarrier_hasDerivAt_of_eq ha haL (picardMassRecon ha haL e ell he z hl) _
    (picardMassRecon_value ha haL e ell he z hl) p hp ht
  have hc : Continuous (picardCandidateLam ha haL z p.1.1) :=
    (continuous_picardCandidateLam ha haL z).comp (continuous_const.prodMk continuous_id)
  have hr : HasDerivAt (Recon.r (picardCandidateLam ha haL z) p.1.1)
      (picardCandidateLam ha haL z p.1.1 p.1.2) p.1.2 :=
    (hc.integral_hasStrictDerivAt p.1.1 p.1.2).hasDerivAt
  have hrp : 0 < Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 := by
    rw [picard_recon_r_eq_radialAverage ha haL z p]
    exact mul_pos (sub_pos.mpr hp) (he.trans_le (picardRadialAverage_lower _ hl p))
  have hd := (hm.const_mul 2).fun_div hr hrp.ne'
  change HasDerivAt (fun v => 2 * Recon.m e (picardCandidateLam ha haL z)
    (picardCandidateH ha haL z) p.1.1 v / Recon.r (picardCandidateLam ha haL z) p.1.1 v)
    (picardMuJets e ell he z hl p) p.1.2
  rw [picardMuJets_eq_quotient_aux ha haL e ell he z hl p hp, picardMassRecon_value]
  exact hd
/-- The literal mass aspect as a continuous value and outgoing first-jet carrier. -/
@[expose] noncomputable def picardMuRecon (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) : PicardCarrier c a L ℝ :=
  picardCarrierOfRawDeriv
    (Recon.mu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z))
    (picardMuValues e ell he z hl) (picardMuJets e ell he z hl)
    (picardMuValues_eq_recon ha haL e ell he z hl)
    (fun p hp ht => picardMu_hasDerivAt_aux ha haL e ell he z hl p hp ht)

/-- Continuous quartic charge-square/radius-square values. -/
@[expose] noncomputable def picardQSquareValues (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) : C(PicardDomain c a L, ℝ) where
  toFun p := (p.1.2 - p.1.1) ^ 4 * picardQSquareRemainder e ell he z hl p
  continuous_toFun := (((continuous_snd.comp continuous_subtype_val).sub
    (continuous_fst.comp continuous_subtype_val)).pow 4).mul (picardQSquareRemainder e ell he z
        hl).continuous
/-- The continuous cubic coefficient of the outgoing `Q^2/r^2` jet. -/
@[expose] noncomputable def picardQSquareJetRemainder (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) : C(PicardDomain c a L, ℝ) where
  toFun p := 2 * picardChargeRemainder e ell he z hl p * picardChargeKernel e ell he z hl p /
    picardRadialAverage (picardLamValues z) p ^ 2 -
      2 * (z.1.1 p).1 * picardChargeRemainder e ell he z hl p ^ 2 /
        picardRadialAverage (picardLamValues z) p ^ 3
  continuous_toFun := by
    have hpos (p : PicardDomain c a L) : 0 < picardRadialAverage (picardLamValues z) p :=
      he.trans_le (picardRadialAverage_lower _ hl p)
    exact (((continuous_const.mul (picardChargeRemainder e ell he z hl).continuous).mul
      (picardChargeKernel e ell he z hl).continuous).div
      ((picardRadialAverage (picardLamValues z)).continuous.pow 2)
      (fun p => pow_ne_zero 2 (hpos p).ne')).sub
      (((continuous_const.mul z.1.1.continuous.fst).mul
        ((picardChargeRemainder e ell he z hl).continuous.pow 2)).div
        ((picardRadialAverage (picardLamValues z)).continuous.pow 3)
        (fun p => pow_ne_zero 3 (hpos p).ne'))
/-- The outgoing charge-square quotient jet with its cubic axis factor. -/
@[expose] noncomputable def picardQSquareJets (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) : C(PicardDomain c a L, ℝ) where
  toFun p := (p.1.2 - p.1.1) ^ 3 * picardQSquareJetRemainder e ell he z hl p
  continuous_toFun := (((continuous_snd.comp continuous_subtype_val).sub
    (continuous_fst.comp continuous_subtype_val)).pow 3).mul (picardQSquareJetRemainder e ell he z
        hl).continuous

/-- The continuous quartic formula equals the literal `Q^2/r^2` quotient. -/
theorem picardQSquareValues_eq_recon (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) : picardQSquareValues e ell he z hl p =
    Recon.Q e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 ^ 2 /
      Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 ^ 2 := by
  rcases lt_or_eq_of_le p.2.1.2.1 with hp|hp
  · have hx : 0 < p.1.2 - p.1.1 := sub_pos.mpr hp
    have hR : 0 < picardRadialAverage (picardLamValues z) p :=
      he.trans_le (picardRadialAverage_lower _ hl p)
    rw [←picardChargeRecon_value ha haL e ell he z hl p,
      picardChargeRecon_normalized ha haL e ell he z hl p, picard_recon_r_eq_radialAverage ha haL z
          p]
    change (p.1.2 - p.1.1) ^ 4 * (picardChargeRemainder e ell he z hl p ^ 2 /
      picardRadialAverage (picardLamValues z) p ^ 2) =
      ((p.1.2 - p.1.1) ^ 3 * picardChargeRemainder e ell he z hl p) ^ 2 /
        ((p.1.2 - p.1.1) * picardRadialAverage (picardLamValues z) p) ^ 2
    field_simp [hx.ne', hR.ne']
  · simp [picardQSquareValues, hp, Recon.r_def]

/-- The normalized charge-square jet equals its off-axis quotient-rule expression. -/
theorem picardQSquareJets_eq_quotient_aux (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) (hp : p.1.1 < p.1.2) :
    picardQSquareJets e ell he z hl p =
      (2 * Recon.Q e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 *
          (picardChargeRecon ha haL e ell he z hl).1.2 p *
          Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 ^ 2 -
        Recon.Q e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 ^ 2 *
          (2 * Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 *
            picardCandidateLam ha haL z p.1.1 p.1.2)) /
        (Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 ^ 2) ^ 2 := by
  have hx : 0 < p.1.2 - p.1.1 := sub_pos.mpr hp
  have hR : 0 < picardRadialAverage (picardLamValues z) p :=
    he.trans_le (picardRadialAverage_lower _ hl p)
  have hQ := (picardChargeRecon_value ha haL e ell he z hl p).symm.trans
    (picardChargeRecon_normalized ha haL e ell he z hl p)
  simp only [picardChargeRecon_jet, hQ, picard_recon_r_eq_radialAverage, picardCandidateLam_coe]
  change (p.1.2 - p.1.1) ^ 3 * (2 * picardChargeRemainder e ell he z hl p *
      picardChargeKernel e ell he z hl p / picardRadialAverage (picardLamValues z) p ^ 2 -
      2 * (z.1.1 p).1 * picardChargeRemainder e ell he z hl p ^ 2 /
        picardRadialAverage (picardLamValues z) p ^ 3) = _
  dsimp only [picardLamValues]
  field_simp [hx.ne', hR.ne']

/-- The literal charge-square quotient has the normalized outgoing derivative. -/
theorem picardQSquare_hasDerivAt_aux (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) (hp : p.1.1 < p.1.2) (ht : p.1.2 < c + L) :
    HasDerivAt (fun v => Recon.Q e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 v
        ^ 2 /
      Recon.r (picardCandidateLam ha haL z) p.1.1 v ^ 2) (picardQSquareJets e ell he z hl p) p.1.2
          := by
  have hQ := picardCarrier_hasDerivAt_of_eq ha haL (picardChargeRecon ha haL e ell he z hl) _
    (picardChargeRecon_value ha haL e ell he z hl) p hp ht
  have hc : Continuous (picardCandidateLam ha haL z p.1.1) :=
    (continuous_picardCandidateLam ha haL z).comp (continuous_const.prodMk continuous_id)
  have hr : HasDerivAt (Recon.r (picardCandidateLam ha haL z) p.1.1)
      (picardCandidateLam ha haL z p.1.1 p.1.2) p.1.2 :=
    (hc.integral_hasStrictDerivAt p.1.1 p.1.2).hasDerivAt
  have hrp : 0 < Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 := by
    rw [picard_recon_r_eq_radialAverage ha haL z p]
    exact mul_pos (sub_pos.mpr hp) (he.trans_le (picardRadialAverage_lower _ hl p))
  have hd := (hQ.fun_pow 2).fun_div (hr.fun_pow 2) (pow_ne_zero 2 hrp.ne')
  rw [picardQSquareJets_eq_quotient_aux ha haL e ell he z hl p hp]
  simpa only [Nat.reduceSub, pow_one, Nat.cast_ofNat] using hd
/-- The charge-square quotient as a continuous value and outgoing first-jet carrier. -/
@[expose] noncomputable def picardQSquareRecon (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) : PicardCarrier c a L ℝ :=
  picardCarrierOfRawDeriv
    (fun u v => Recon.Q e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) u v ^ 2 /
      Recon.r (picardCandidateLam ha haL z) u v ^ 2)
    (picardQSquareValues e ell he z hl) (picardQSquareJets e ell he z hl)
    (picardQSquareValues_eq_recon ha haL e ell he z hl)
    (fun p hp ht => picardQSquare_hasDerivAt_aux ha haL e ell he z hl p hp ht)

/-- The continuous quadratic coefficient of `z` on the explicit positive-gap domain. -/
@[expose] noncomputable def picardZRemainder (e ell kappa : ℝ) (he : 0 < ell) (hk : 0 < kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) : C(PicardDomain c a L, ℝ) where
  toFun p := (picardMuRemainder e ell he z hl p - (p.1.2 - p.1.1) ^ 2 * picardQSquareRemainder e ell
      he z hl p) /
    (1 - picardMuValues e ell he z hl p)
  continuous_toFun := by
    exact ((picardMuRemainder e ell he z hl).continuous.sub
      ((((continuous_snd.comp continuous_subtype_val).sub
        (continuous_fst.comp continuous_subtype_val)).pow 2).mul
        (picardQSquareRemainder e ell he z hl).continuous)).div
      (continuous_const.sub (picardMuValues e ell he z hl).continuous)
      (fun p => (hk.trans_le (hgap p)).ne')
/-- Continuous quadratic `z` values on the S1 domain `1-mu >= kappa > 0`. -/
@[expose] noncomputable def picardZValues (e ell kappa : ℝ) (he : 0 < ell) (hk : 0 < kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) : C(PicardDomain c a L, ℝ) where
  toFun p := (p.1.2 - p.1.1) ^ 2 * picardZRemainder e ell kappa he hk z hl hgap p
  continuous_toFun := (((continuous_snd.comp continuous_subtype_val).sub
    (continuous_fst.comp continuous_subtype_val)).pow 2).mul
    (picardZRemainder e ell kappa he hk z hl hgap).continuous
/-- The continuous linear coefficient of the outgoing `z` jet on the S1 domain. -/
@[expose] noncomputable def picardZJetRemainder (e ell kappa : ℝ) (he : 0 < ell) (hk : 0 < kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) : C(PicardDomain c a L, ℝ) where
  toFun p := ((1 - picardQSquareValues e ell he z hl p) * picardMuJetRemainder e ell he z hl p -
    (1 - picardMuValues e ell he z hl p) * (p.1.2 - p.1.1) ^ 2 * picardQSquareJetRemainder e ell he
        z hl p) /
      (1 - picardMuValues e ell he z hl p) ^ 2
  continuous_toFun := by
    exact (((continuous_const.sub (picardQSquareValues e ell he z hl).continuous).mul
      (picardMuJetRemainder e ell he z hl).continuous).sub
      (((continuous_const.sub (picardMuValues e ell he z hl).continuous).mul
        (((continuous_snd.comp continuous_subtype_val).sub
          (continuous_fst.comp continuous_subtype_val)).pow 2)).mul
          (picardQSquareJetRemainder e ell he z hl).continuous)).div
      ((continuous_const.sub (picardMuValues e ell he z hl).continuous).pow 2)
      (fun p => pow_ne_zero 2 (hk.trans_le (hgap p)).ne')
/-- The outgoing `z` jet with its linear axis factor and the explicit S1 gap. -/
@[expose] noncomputable def picardZJets (e ell kappa : ℝ) (he : 0 < ell) (hk : 0 < kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) : C(PicardDomain c a L, ℝ) where
  toFun p := (p.1.2 - p.1.1) * picardZJetRemainder e ell kappa he hk z hl hgap p
  continuous_toFun := ((continuous_snd.comp continuous_subtype_val).sub
    (continuous_fst.comp continuous_subtype_val)).mul
    (picardZJetRemainder e ell kappa he hk z hl hgap).continuous

/-- The continuous quadratic formula equals the literal `Recon.z`, including the axis. -/
theorem picardZValues_eq_recon (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ) (he : 0 < ell) (hk : 0 <
    kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p : PicardDomain c a L) :
    picardZValues e ell kappa he hk z hl hgap p =
      Recon.z e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 := by
  rw [Recon.z_def, ←picardMuValues_eq_recon ha haL e ell he z hl p,
    ←picardQSquareValues_eq_recon ha haL e ell he z hl p]
  change (p.1.2 - p.1.1) ^ 2 * ((picardMuRemainder e ell he z hl p -
    (p.1.2 - p.1.1) ^ 2 * picardQSquareRemainder e ell he z hl p) /
    (1 - (p.1.2 - p.1.1) ^ 2 * picardMuRemainder e ell he z hl p)) =
    ((p.1.2 - p.1.1) ^ 2 * picardMuRemainder e ell he z hl p -
      (p.1.2 - p.1.1) ^ 4 * picardQSquareRemainder e ell he z hl p) /
      (1 - (p.1.2 - p.1.1) ^ 2 * picardMuRemainder e ell he z hl p)
  ring

/-- The normalized `z` jet equals its off-axis quotient-rule expression. -/
theorem picardZJets_eq_quotient_aux (e ell kappa : ℝ) (he : 0 < ell) (hk : 0 < kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p : PicardDomain c a L) :
    picardZJets e ell kappa he hk z hl hgap p =
      ((picardMuJets e ell he z hl p - picardQSquareJets e ell he z hl p) *
          (1 - picardMuValues e ell he z hl p) -
        (picardMuValues e ell he z hl p - picardQSquareValues e ell he z hl p) *
          (-picardMuJets e ell he z hl p)) / (1 - picardMuValues e ell he z hl p) ^ 2 := by
  change (p.1.2 - p.1.1) * (((1 - picardQSquareValues e ell he z hl p) * picardMuJetRemainder e ell
      he z hl p -
    (1 - picardMuValues e ell he z hl p) * (p.1.2 - p.1.1) ^ 2 * picardQSquareJetRemainder e ell he
        z hl p) /
      (1 - picardMuValues e ell he z hl p) ^ 2) =
    (((p.1.2 - p.1.1) * picardMuJetRemainder e ell he z hl p -
        (p.1.2 - p.1.1) ^ 3 * picardQSquareJetRemainder e ell he z hl p) * (1 - picardMuValues e ell
            he z hl p) -
      (picardMuValues e ell he z hl p - picardQSquareValues e ell he z hl p) *
        (-((p.1.2 - p.1.1) * picardMuJetRemainder e ell he z hl p))) / (1 - picardMuValues e ell he
            z hl p) ^ 2
  ring

/-- The literal `z` coefficient has the normalized outgoing derivative on the S1 domain. -/
theorem picardZ_hasDerivAt_aux (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ) (he : 0 < ell) (hk : 0 <
    kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p : PicardDomain c a L)
    (hp : p.1.1 < p.1.2) (ht : p.1.2 < c + L) :
    HasDerivAt (Recon.z e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1)
      (picardZJets e ell kappa he hk z hl hgap p) p.1.2 := by
  have hm := picardMu_hasDerivAt_aux ha haL e ell he z hl p hp ht
  have hq := picardQSquare_hasDerivAt_aux ha haL e ell he z hl p hp ht
  have hden : 1 - Recon.mu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 ≠
      0 := by
    rw [←picardMuValues_eq_recon ha haL e ell he z hl p]
    exact (hk.trans_le (hgap p)).ne'
  have hd := (hm.fun_sub hq).fun_div ((hasDerivAt_const p.1.2 (1 : ℝ)).fun_sub hm) hden
  change HasDerivAt (fun v =>
    (Recon.mu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 v -
      Recon.Q e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 v ^ 2 /
        Recon.r (picardCandidateLam ha haL z) p.1.1 v ^ 2) /
      (1 - Recon.mu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 v))
    (picardZJets e ell kappa he hk z hl hgap p) p.1.2
  rw [picardZJets_eq_quotient_aux, picardMuValues_eq_recon ha haL e ell he z hl p,
    picardQSquareValues_eq_recon ha haL e ell he z hl p]
  simpa only [zero_sub] using hd
/-- The literal `z` coefficient as a compatible carrier on the explicit S1 domain. -/
@[expose] noncomputable def picardZRecon (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ) (he : 0 < ell)
    (hk : 0 < kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) : PicardCarrier c a L ℝ :=
  picardCarrierOfRawDeriv
    (Recon.z e (picardCandidateLam ha haL z) (picardCandidateH ha haL z))
    (picardZValues e ell kappa he hk z hl hgap) (picardZJets e ell kappa he hk z hl hgap)
    (picardZValues_eq_recon ha haL e ell kappa he hk z hl hgap)
    (fun p hp ht => picardZ_hasDerivAt_aux ha haL e ell kappa he hk z hl hgap p hp ht)

end EmcsfAcExtension.Local
