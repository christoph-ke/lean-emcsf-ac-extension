module

public import EmcsfAcExtension.Local.Construction.PicardRadial
public import EmcsfAcExtension.Local.Construction.PicardIntegral

/-! # Charge reconstruction in the outgoing Picard carrier

The normalized scalar formula removes the apparent axis singularity before
integration. Charge values vanish cubically and their outgoing jets quadratically.
This module supplies part of the radial C1 construction; it closes no graph node.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- The continuous quadratic charge-source coefficient after removing `(v-u)^2`. -/
@[expose] noncomputable def picardChargeKernel (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) :
    C(PicardDomain c a L, ℝ) where
  toFun p := -e * picardRadialAverage (picardLamValues z) p * (z.1.1 p).1 *
    (starRingEnd ℂ (picardPhiValues ell he z hl p) * picardScalarRemainder ell he z hl p).im
  continuous_toFun := by
    exact ((continuous_const.mul (picardRadialAverage (picardLamValues z)).continuous).mul
      z.1.1.continuous.fst).mul (Complex.continuous_im.comp
        (((picardPhiValues ell he z hl).continuous.star).mul
          (picardScalarRemainder ell he z hl).continuous))
/-- The continuous outgoing charge source on the full closed wedge. -/
@[expose] noncomputable def picardChargeSource (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) :
    C(PicardDomain c a L, ℝ) where
  toFun p := (p.1.2 - p.1.1) ^ 2 * picardChargeKernel e ell he z hl p
  continuous_toFun := (((continuous_snd.comp continuous_subtype_val).sub
    (continuous_fst.comp continuous_subtype_val)).pow 2).mul
      (picardChargeKernel e ell he z hl).continuous

/-- The factored continuous charge source equals the literal raw source,
including the axis. No Hawking-gap assumption is needed. -/
theorem picardChargeSource_eq_recon (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) :
    picardChargeSource e ell he z hl p = -e *
      Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 * (z.1.1 p).1 *
      (starRingEnd ℂ (Recon.phi (picardCandidateLam ha haL z)
        (picardCandidateH ha haL z) p.1.1 p.1.2) *
        (z.1.1 p).2).im := by
  have hf := picard_ratio_eq_normalized ha haL ell he z hl p
  rw [Recon.ratio_def, picardCandidateH_coe ha haL z p,
    ← picardPhiValues_eq_recon ha haL ell he z hl p] at hf
  have hh : (z.1.1 p).2 = picardPhiValues ell he z hl p +
      (p.1.2 - p.1.1) • picardScalarRemainder ell he z hl p := by rw [←hf]; abel
  have him : (starRingEnd ℂ (picardPhiValues ell he z hl p) * (z.1.1 p).2).im =
      (p.1.2 - p.1.1) * (starRingEnd ℂ (picardPhiValues ell he z hl p) *
        picardScalarRemainder ell he z hl p).im := by
    rw [hh, mul_add, Complex.add_im, Complex.conj_mul']
    simp only [←Complex.ofReal_pow, Complex.ofReal_im, zero_add, Complex.real_smul, Complex.mul_im,
      Complex.mul_re, Complex.ofReal_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [picard_recon_r_eq_radialAverage ha haL z p,
    ←picardPhiValues_eq_recon ha haL ell he z hl p, him]
  change (p.1.2 - p.1.1) ^ 2 * (-e * _ * _ * _) = _
  dsimp only [picardLamValues]
  ring

/-- The charge reconstruction and its continuous outgoing jet as a carrier. -/
@[expose] noncomputable def picardChargeRecon (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) :
    PicardCarrier c a L ℝ := picardOutgoing ha haL (picardChargeSource e ell he z hl)

/-- The charge carrier has exactly the values of the existing `Recon.Q`. -/
theorem picardChargeRecon_value (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) :
    ((picardChargeRecon ha haL e ell he z hl).1.1 p) =
      Recon.Q e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 := by
  change (∫ s in p.1.1..p.1.2, picardChargeSource e ell he z hl (picardClamp ha haL (p.1.1, s))) = _
  rw [Recon.q_def, ←intervalIntegral.integral_const_mul, ←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le p.2.1.2.1] at hs
  let q := picardSectionPoint p s
  have hq : q.1 = (p.1.1, s) := picardSectionPoint_of_mem p ⟨hs.1, hs.2.trans p.2.1.2.2⟩
  have hClamp : picardClamp ha haL (p.1.1, s) = q := by
    simpa only [hq] using picardClamp_coe ha haL q
  dsimp only
  rw [hClamp, picardChargeSource_eq_recon ha haL e ell he z hl q]
  rw [←picardCandidateLam_coe ha haL z q, ←picardCandidateH_coe ha haL z q, hq]
  ring

/-- The continuous normalized charge `Q / (v-u)^3`, defined by a moment
without division by the distance to the axis. -/
@[expose] noncomputable def picardChargeRemainder (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) :
    C(PicardDomain c a L, ℝ) := picardRadialMoment 2 (picardChargeKernel e ell he z hl)

/-- Exact cubic vanishing of the charge carrier, including zero width. -/
theorem picardChargeRecon_normalized (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) :
    (picardChargeRecon ha haL e ell he z hl).1.1 p =
      (p.1.2 - p.1.1) ^ 3 * picardChargeRemainder e ell he z hl p := by
  change (∫ s in p.1.1..p.1.2, picardChargeSource e ell he z hl (picardClamp ha haL (p.1.1, s))) = _
  have hm := picardOutgoing_moment ha haL 2 (picardChargeKernel e ell he z hl) p
  rw [show (2 + 1 : ℕ) = 3 from rfl] at hm
  change _ = (p.1.2 - p.1.1) ^ 3 • picardRadialMoment 2 (picardChargeKernel e ell he z hl) p
  rw [←hm]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le p.2.1.2.1] at hs
  let q := picardSectionPoint p s
  have hq : q.1 = (p.1.1, s) := picardSectionPoint_of_mem p ⟨hs.1, hs.2.trans p.2.1.2.2⟩
  have hClamp : picardClamp ha haL (p.1.1, s) = q := by
    simpa only [hq] using picardClamp_coe ha haL q
  dsimp only
  rw [hClamp]
  change (q.1.2 - q.1.1) ^ 2 * picardChargeKernel e ell he z hl q = _
  rw [hq]
  rfl

/-- The charge carrier's continuous outgoing jet is the quadratic source. -/
@[simp] theorem picardChargeRecon_jet (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (p : PicardDomain c a L) :
    (picardChargeRecon ha haL e ell he z hl).1.2 p =
      (p.1.2 - p.1.1) ^ 2 * picardChargeKernel e ell he z hl p := rfl

end EmcsfAcExtension.Local
