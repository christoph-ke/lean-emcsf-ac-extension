module

public import EmcsfAcExtension.Local.Construction.PicardDivision
public import EmcsfAcExtension.Local.Construction.PicardCoefficients

/-! # Real incoming transport sources with continuous outgoing jets

The positive-gap reconstruction supplies `G,C_A,A` as compatible carriers.
Vanishing profiles and radius division prove axis regularity without second
candidate derivatives. Uniform radial Lipschitz bounds remain to be assembled.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- The continuous distance `v-u` to the axis. -/
@[expose] noncomputable def picardWidth : C(PicardDomain c a L, ℝ) :=
  ⟨fun p => p.1.2 - p.1.1, (continuous_snd.comp continuous_subtype_val).sub
    (continuous_fst.comp continuous_subtype_val)⟩
/-- The continuous gap carrier `1-mu`, formed from the mass-aspect carrier. -/
@[expose] noncomputable def picardGapCarrier (ha : 0 ≤ a) (haL : a ≤ L) (e ell : ℝ) (he : 0 < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) : PicardCarrier c a L ℝ :=
  let M := picardMuRecon ha haL e ell he z hl
  picardCarrierOfRawDeriv (fun u v => 1 - picardCarrierValue ha haL M u v)
    ⟨fun p => 1 - picardMuValues e ell he z hl p,
      continuous_const.sub (picardMuValues e ell he z hl).continuous⟩ (-M.1.2)
    (by intro p; rw [picardCarrierValue_coe]; rfl)
    (by
      intro p hp ht
      simpa only [ContinuousMap.neg_apply, zero_sub] using
        (hasDerivAt_const p.1.2 (1 : ℝ)).fun_sub (picardCarrierValue_hasDerivAt ha haL M p hp ht))
/-- The inverse-gap carrier on the explicit S1 domain `1-mu >= kappa > 0`. -/
@[expose] noncomputable def picardGapInv (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
    PicardCarrier c a L ℝ :=
  picardCarrierInv ha haL kappa hk (picardGapCarrier ha haL e ell he z hl) hgap

/-- The inverse-gap values are exactly `(1-mu)^(-1)`. -/
theorem picardGapInv_value (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q)
    (p : PicardDomain c a L) : (picardGapInv ha haL e ell kappa he hk z hl hgap).1.1 p =
      (1 - picardMuValues e ell he z hl p)⁻¹ := rfl
/-- The continuous linear coefficient of the inverse-gap outgoing jet. -/
@[expose] noncomputable def picardGapInvJetRemainder (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
    C(PicardDomain c a L, ℝ) :=
  picardMuJetRemainder e ell he z hl * (picardGapInv ha haL e ell kappa he hk z hl hgap).1.1 ^ 2

/-- The inverse-gap jet has its exact linear axis factor. -/
theorem picardGapInv_jet (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q)
    (p : PicardDomain c a L) : (picardGapInv ha haL e ell kappa he hk z hl hgap).1.2 p =
      (p.1.2 - p.1.1) * picardGapInvJetRemainder ha haL e ell kappa he hk z hl hgap p := by
  change -(-picardMuJets e ell he z hl p) / (1 - picardMuValues e ell he z hl p) ^ 2 =
    (p.1.2 - p.1.1) * (picardMuJetRemainder e ell he z hl p *
      ((1 - picardMuValues e ell he z hl p)⁻¹) ^ 2)
  change -(-((p.1.2 - p.1.1) * picardMuJetRemainder e ell he z hl p)) /
    (1 - picardMuValues e ell he z hl p) ^ 2 = _
  rw [neg_neg, div_eq_mul_inv, inv_pow]
  ring
/-- The quadratic numerator profile of `nu*z` for the incoming expansion coefficient. -/
@[expose] noncomputable def picardGNumeratorRemainder (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
    C(PicardDomain c a L, ℝ) :=
  (picardNuRecon ha haL e ell kappa he hk z hl hgap).1.1 * picardZRemainder e ell kappa he hk z hl
      hgap
/-- The linear first-jet profile of the numerator `nu*z`. -/
@[expose] noncomputable def picardGNumeratorJetRemainder (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa :
    ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
    C(PicardDomain c a L, ℝ) :=
  picardWidth * (picardNuRecon ha haL e ell kappa he hk z hl hgap).1.2 *
    picardZRemainder e ell kappa he hk z hl hgap +
    (picardNuRecon ha haL e ell kappa he hk z hl hgap).1.1 * picardZJetRemainder e ell kappa he hk z
        hl hgap
/-- The incoming expansion coefficient `G=(nu/r)z` as a compatible carrier on S1. -/
@[expose] noncomputable def picardGRecon (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
    PicardCarrier c a L ℝ := by
  let N := picardNuRecon ha haL e ell kappa he hk z hl hgap
  let Z := picardZRecon ha haL e ell kappa he hk z hl hgap
  refine picardDivideRadius ha haL ell he z hl (picardCarrierMul ha haL N Z)
    (picardGNumeratorRemainder ha haL e ell kappa he hk z hl hgap)
    (picardGNumeratorJetRemainder ha haL e ell kappa he hk z hl hgap) ?_ ?_
  · intro p
    change N.1.1 p * ((p.1.2 - p.1.1) ^ 2 * picardZRemainder e ell kappa he hk z hl hgap p) =
      (p.1.2 - p.1.1) ^ 2 * (N.1.1 p * picardZRemainder e ell kappa he hk z hl hgap p)
    ring
  · intro p
    change N.1.2 p * ((p.1.2 - p.1.1) ^ 2 * picardZRemainder e ell kappa he hk z hl hgap p) +
      N.1.1 p * ((p.1.2 - p.1.1) * picardZJetRemainder e ell kappa he hk z hl hgap p) =
      (p.1.2 - p.1.1) * ((p.1.2 - p.1.1) * N.1.2 p * picardZRemainder e ell kappa he hk z hl hgap p
          +
        N.1.1 p * picardZJetRemainder e ell kappa he hk z hl hgap p)
    ring

/-- The incoming expansion carrier equals the literal reconstruction expression. -/
theorem picardGRecon_value (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q)
    (p : PicardDomain c a L) : (picardGRecon ha haL e ell kappa he hk z hl hgap).1.1 p =
      Recon.nu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 /
        Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 *
        Recon.z e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 := by
  simp only [picardGRecon, picardDivideRadius_value, picardCarrierMul_value]
  rw [picardNuRecon_value]
  change _ * (_ * picardZValues e ell kappa he hk z hl hgap p) = _
  rw [picardZValues_eq_recon ha haL e ell kappa he hk z hl hgap p]
  simp only [div_eq_mul_inv]
  ring

/-- The cubic connection numerator `2*nu*lambda*Q/(1-mu)` as a carrier. -/
@[expose] noncomputable def picardCANumerator (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
        PicardCarrier c a L ℝ :=
  let N := picardNuRecon ha haL e ell kappa he hk z hl hgap
  let L := picardCarrierLinear ha haL (ContinuousLinearMap.fst ℝ ℝ ℂ) z
  let Q := picardChargeRecon ha haL e ell he z hl
  let U := picardGapInv ha haL e ell kappa he hk z hl hgap
  picardCarrierLinear ha haL ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
    (picardCarrierMul ha haL (picardCarrierMul ha haL (picardCarrierMul ha haL N L) Q) U)

/-- The continuous cubic profile of the connection numerator. -/
@[expose] noncomputable def picardCANumeratorRemainder (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
        C(PicardDomain c a L, ℝ) :=
  let N := picardNuRecon ha haL e ell kappa he hk z hl hgap
  let L := picardCarrierLinear ha haL (ContinuousLinearMap.fst ℝ ℝ ℂ) z
  let U := picardGapInv ha haL e ell kappa he hk z hl hgap
  (2 : ℝ) • (N.1.1 * L.1.1 * picardChargeRemainder e ell he z hl * U.1.1)

/-- The continuous quadratic first-jet profile of the connection numerator. -/
@[expose] noncomputable def picardCANumeratorJetRemainder (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa :
    ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
        C(PicardDomain c a L, ℝ) :=
  let N := picardNuRecon ha haL e ell kappa he hk z hl hgap
  let L := picardCarrierLinear ha haL (ContinuousLinearMap.fst ℝ ℝ ℂ) z
  let U := picardGapInv ha haL e ell kappa he hk z hl hgap
  (2 : ℝ) • ((picardWidth * (N.1.2 * L.1.1 + N.1.1 * L.1.2) * picardChargeRemainder e ell he z hl +
    N.1.1 * L.1.1 * picardChargeKernel e ell he z hl) * U.1.1 +
    picardWidth ^ 2 * (N.1.1 * L.1.1 * picardChargeRemainder e ell he z hl) *
        picardGapInvJetRemainder ha haL e ell kappa he hk z hl hgap)

/-- The connection numerator has exactly its cubic value profile. -/
theorem picardCANumerator_value_profile (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p :
        PicardDomain c a L) :
    (picardCANumerator ha haL e ell kappa he hk z hl hgap).1.1 p = (p.1.2 - p.1.1) ^ 3 *
        picardCANumeratorRemainder ha haL e ell kappa he hk z hl hgap p := by
  simp only [picardCANumerator, picardCarrierLinear_value, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, picardCarrierMul_value, picardChargeRecon_normalized]
  change 2 * ((((picardNuRecon ha haL e ell kappa he hk z hl hgap).1.1 p *
    (picardCarrierLinear ha haL (ContinuousLinearMap.fst ℝ ℝ ℂ) z).1.1 p) *
    ((p.1.2 - p.1.1) ^ 3 * picardChargeRemainder e ell he z hl p)) *
    (picardGapInv ha haL e ell kappa he hk z hl hgap).1.1 p) =
    (p.1.2 - p.1.1) ^ 3 * (2 * ((picardNuRecon ha haL e ell kappa he hk z hl hgap).1.1 p *
    (picardCarrierLinear ha haL (ContinuousLinearMap.fst ℝ ℝ ℂ) z).1.1 p *
    picardChargeRemainder e ell he z hl p * (picardGapInv ha haL e ell kappa he hk z hl hgap).1.1
        p))
  ring

/-- The connection numerator has exactly its quadratic first-jet profile. -/
theorem picardCANumerator_jet_profile (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p :
        PicardDomain c a L) :
    (picardCANumerator ha haL e ell kappa he hk z hl hgap).1.2 p = (p.1.2 - p.1.1) ^ 2 *
        picardCANumeratorJetRemainder ha haL e ell kappa he hk z hl hgap p := by
  simp only [picardCANumerator, picardCarrierLinear_value, picardCarrierLinear_jet,
    smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    picardCarrierMul_value, picardCarrierMul_jet, picardChargeRecon_normalized,
    picardChargeRecon_jet, picardGapInv_jet]
  let N := picardNuRecon ha haL e ell kappa he hk z hl hgap
  let U := picardGapInv ha haL e ell kappa he hk z hl hgap
  change 2 * ((((N.1.2 p * (z.1.1 p).1 + N.1.1 p * (z.1.2 p).1) *
    ((p.1.2 - p.1.1) ^ 3 * picardChargeRemainder e ell he z hl p) +
      (N.1.1 p * (z.1.1 p).1) * ((p.1.2 - p.1.1) ^ 2 * picardChargeKernel e ell he z hl p)) * U.1.1
          p +
      ((N.1.1 p * (z.1.1 p).1) * ((p.1.2 - p.1.1) ^ 3 * picardChargeRemainder e ell he z hl p)) *
        ((p.1.2 - p.1.1) * picardGapInvJetRemainder ha haL e ell kappa he hk z hl hgap p))) =
      (p.1.2 - p.1.1) ^ 2 * (2 * ((((p.1.2 - p.1.1) * (N.1.2 p * (z.1.1 p).1 + N.1.1 p * (z.1.2
          p).1) *
        picardChargeRemainder e ell he z hl p + N.1.1 p * (z.1.1 p).1 * picardChargeKernel e ell he
            z hl p) *
        U.1.1 p) + (p.1.2 - p.1.1) ^ 2 * (N.1.1 p * (z.1.1 p).1 * picardChargeRemainder e ell he z
            hl p) *
          picardGapInvJetRemainder ha haL e ell kappa he hk z hl hgap p))
  ring

/-- The connection source `C_A` as a compatible carrier, using regularized radius-square division.
-/
@[expose] noncomputable def picardCARecon (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
        PicardCarrier c a L ℝ :=
  picardDivideRadiusSq ha haL ell he z hl (picardCANumerator ha haL e ell kappa he hk z hl hgap)
    (picardCANumeratorRemainder ha haL e ell kappa he hk z hl hgap) (picardCANumeratorJetRemainder
        ha haL e ell kappa he hk z hl hgap)
    (picardCANumerator_value_profile ha haL e ell kappa he hk z hl hgap)
        (picardCANumerator_jet_profile ha haL e ell kappa he hk z hl hgap)

/-- The connection-source carrier equals its exact raw formula, including the axis. -/
theorem picardCARecon_value (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p :
        PicardDomain c a L) :
    (picardCARecon ha haL e ell kappa he hk z hl hgap).1.1 p =
      2 * Recon.nu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 *
        picardCandidateLam ha haL z p.1.1 p.1.2 *
        Recon.Q e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 /
        ((1 - Recon.mu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2) *
          Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 ^ 2) := by
  simp only [picardCARecon, picardDivideRadiusSq_value, picardCANumerator,
      picardCarrierLinear_value,
    smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, picardCarrierMul_value,
    picardNuRecon_value, picardChargeRecon_value, picardGapInv_value]
  change _ * (2 * ((_ * ((z.1.1 p).1)) * _ * (1 - picardMuValues e ell he z hl p)⁻¹)) = _
  rw [←picardCandidateLam_coe ha haL z p, picardMuValues_eq_recon ha haL e ell he z hl p]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- The reconstructed connection as the outgoing primitive of `C_A`. -/
@[expose] noncomputable def picardARecon (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
        PicardCarrier c a L ℝ :=
  picardOutgoing ha haL (picardCARecon ha haL e ell kappa he hk z hl hgap).1.1

/-- The connection carrier has exactly the existing `Recon.A` values. -/
theorem picardARecon_value (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p :
        PicardDomain c a L) :
    (picardARecon ha haL e ell kappa he hk z hl hgap).1.1 p =
      Recon.A e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 := by
  change (picardOutgoing ha haL (picardCARecon ha haL e ell kappa he hk z hl hgap).1.1).1.1 p = _
  rw [picardOutgoing_value_eq_of_eq ha haL _
    (fun u v => 2 * Recon.nu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) u v *
      picardCandidateLam ha haL z u v * Recon.Q e (picardCandidateLam ha haL z) (picardCandidateH ha
          haL z) u v /
      ((1 - Recon.mu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) u v) *
        Recon.r (picardCandidateLam ha haL z) u v ^ 2)) (picardCARecon_value ha haL e ell kappa he
            hk z hl hgap) p, Recon.a_def]



/-- The reconstructed radius as an outgoing primitive carrier. -/
@[expose] noncomputable def picardRadiusRecon (ha : 0 ≤ a) (haL : a ≤ L)
    (z : PicardCarrier c a L (ℝ × ℂ)) : PicardCarrier c a L ℝ :=
  picardOutgoing ha haL (picardLamValues z)

end EmcsfAcExtension.Local
