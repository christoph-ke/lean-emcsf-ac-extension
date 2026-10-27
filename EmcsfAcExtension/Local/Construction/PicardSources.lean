module

public import EmcsfAcExtension.Local.Construction.PicardRealSources

/-! # Complex incoming transport sources with continuous outgoing jets

The charged source `P` is built from cubic numerator profiles. Radius division
proves axis regularity without a second candidate derivative. Uniform radial
bounds and Lipschitz constants beyond the scalar and charge parts remain open.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- View a continuous real profile as a continuous complex profile. -/
@[expose] noncomputable def picardComplexProfile (f : C(PicardDomain c a L, ℝ)) : C(PicardDomain c a
    L, ℂ) :=
  ⟨fun p => (f p : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

/-- The candidate scalar minus its radial scalar reconstruction, as an outgoing carrier. -/
@[expose] noncomputable def picardScalarDifferenceRecon (ha : 0 ≤ a) (haL : a ≤ L) (ell : ℝ) (he : 0
    < ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) : PicardCarrier c a L ℂ :=
  picardCarrierAdd ha haL (picardCarrierLinear ha haL (ContinuousLinearMap.snd ℝ ℝ ℂ) z)
    (picardCarrierNeg ha haL (picardScalarRecon ha haL ell he z hl))

/-- The scalar difference has exactly the normalized linear value profile. -/
theorem picardScalarDifferenceRecon_value_profile (ha : 0 ≤ a) (haL : a ≤ L) (ell : ℝ) (he : 0 <
    ell)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1) (p : PicardDomain c a L) :
    (picardScalarDifferenceRecon ha haL ell he z hl).1.1 p = (p.1.2 - p.1.1) • picardScalarRemainder
        ell he z hl p := by
  change (z.1.1 p).2 - ((z.1.1 p).2 - (p.1.2 - p.1.1) • picardScalarRemainder ell he z hl p) = _
  abel

/-- The cubic charged numerator `W=z*f+ie*Q*phi/(1-mu)` as an outgoing carrier. -/
@[expose] noncomputable def picardWRecon (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
        PicardCarrier c a L ℂ :=
  let Z := picardCarrierLinear ha haL Complex.ofRealCLM (picardZRecon ha haL e ell kappa he hk z hl
      hgap)
  let Q := picardCarrierLinear ha haL Complex.ofRealCLM (picardChargeRecon ha haL e ell he z hl)
  let U := picardCarrierLinear ha haL Complex.ofRealCLM (picardGapInv ha haL e ell kappa he hk z hl
      hgap)
  let Phi := picardScalarRecon ha haL ell he z hl
  picardCarrierAdd ha haL (picardCarrierCMul ha haL Z (picardScalarDifferenceRecon ha haL ell he z
      hl))
    (picardCarrierLinear ha haL ((Complex.I * (e : ℂ)) • ContinuousLinearMap.id ℝ ℂ)
      (picardCarrierCMul ha haL (picardCarrierCMul ha haL Q Phi) U))

/-- The continuous cubic value profile of the charged numerator `W`. -/
@[expose] noncomputable def picardWRemainder (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
        C(PicardDomain c a L, ℂ) :=
  let Phi := (picardScalarRecon ha haL ell he z hl).1.1
  let U := (picardGapInv ha haL e ell kappa he hk z hl hgap).1.1
  picardComplexProfile (picardZRemainder e ell kappa he hk z hl hgap) * picardScalarRemainder ell he
      z hl +
    (Complex.I * (e : ℂ)) • (picardComplexProfile (picardChargeRemainder e ell he z hl) * Phi *
        picardComplexProfile U)

/-- The continuous quadratic outgoing-jet profile of the charged numerator `W`. -/
@[expose] noncomputable def picardWJetRemainder (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
        C(PicardDomain c a L, ℂ) :=
  let Phi := picardScalarRecon ha haL ell he z hl
  let U := (picardGapInv ha haL e ell kappa he hk z hl hgap).1.1
  picardComplexProfile (picardZJetRemainder e ell kappa he hk z hl hgap) * picardScalarRemainder ell
      he z hl +
    picardComplexProfile (picardZRemainder e ell kappa he hk z hl hgap) *
        (picardScalarDifferenceRecon ha haL ell he z hl).1.2 +
    (Complex.I * (e : ℂ)) • ((picardComplexProfile (picardChargeKernel e ell he z hl) * Phi.1.1 +
      picardComplexProfile picardWidth * picardComplexProfile (picardChargeRemainder e ell he z hl)
          * Phi.1.2) *
      picardComplexProfile U + (picardComplexProfile picardWidth) ^ 2 *
        picardComplexProfile (picardChargeRemainder e ell he z hl) * Phi.1.1 *
        picardComplexProfile (picardGapInvJetRemainder ha haL e ell kappa he hk z hl hgap))

/-- The charged numerator has exactly its cubic value profile. -/
theorem picardWRecon_value_profile (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p :
        PicardDomain c a L) :
    (picardWRecon ha haL e ell kappa he hk z hl hgap).1.1 p = (p.1.2 - p.1.1) ^ 3 • picardWRemainder
        ha haL e ell kappa he hk z hl hgap p := by
  simp only [picardWRecon, picardCarrierAdd_value, picardCarrierCMul_value,
      picardCarrierLinear_value,
    smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  rw [picardScalarDifferenceRecon_value_profile]
  change (((p.1.2 - p.1.1) ^ 2 * picardZRemainder e ell kappa he hk z hl hgap p : ℝ) : ℂ) *
    ((p.1.2 - p.1.1) • picardScalarRemainder ell he z hl p) +
    (Complex.I * (e : ℂ)) * (((picardChargeRecon ha haL e ell he z hl).1.1 p : ℂ) *
      (picardScalarRecon ha haL ell he z hl).1.1 p * ((picardGapInv ha haL e ell kappa he hk z hl
          hgap).1.1 p : ℂ)) = _
  rw [picardChargeRecon_normalized]
  change _ = (p.1.2 - p.1.1) ^ 3 • ((picardZRemainder e ell kappa he hk z hl hgap p : ℂ) *
    picardScalarRemainder ell he z hl p + (Complex.I * (e : ℂ)) *
      ((picardChargeRemainder e ell he z hl p : ℂ) * (picardScalarRecon ha haL ell he z hl).1.1 p *
        ((picardGapInv ha haL e ell kappa he hk z hl hgap).1.1 p : ℂ)))
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The charged numerator has exactly its quadratic first-jet profile, without a second derivative.
-/
theorem picardWRecon_jet_profile (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p :
        PicardDomain c a L) :
    (picardWRecon ha haL e ell kappa he hk z hl hgap).1.2 p = (p.1.2 - p.1.1) ^ 2 •
        picardWJetRemainder ha haL e ell kappa he hk z hl hgap p := by
  simp only [picardWRecon, picardCarrierAdd_jet, picardCarrierCMul_value, picardCarrierCMul_jet,
    picardCarrierLinear_value, picardCarrierLinear_jet, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  simp only [picardScalarDifferenceRecon_value_profile, picardChargeRecon_normalized,
      picardChargeRecon_jet, picardGapInv_jet]
  let Phi := picardScalarRecon ha haL ell he z hl
  let F := picardScalarDifferenceRecon ha haL ell he z hl
  let U := picardGapInv ha haL e ell kappa he hk z hl hgap
  change (((p.1.2 - p.1.1) * picardZJetRemainder e ell kappa he hk z hl hgap p : ℝ) : ℂ) *
      ((p.1.2 - p.1.1) • picardScalarRemainder ell he z hl p) +
    (((p.1.2 - p.1.1) ^ 2 * picardZRemainder e ell kappa he hk z hl hgap p : ℝ) : ℂ) * F.1.2 p +
    (Complex.I * (e : ℂ)) *
      (((((p.1.2 - p.1.1) ^ 2 * picardChargeKernel e ell he z hl p : ℝ) : ℂ) * Phi.1.1 p +
        (((p.1.2 - p.1.1) ^ 3 * picardChargeRemainder e ell he z hl p : ℝ) : ℂ) * Phi.1.2 p) *
            (U.1.1 p : ℂ) +
        ((((p.1.2 - p.1.1) ^ 3 * picardChargeRemainder e ell he z hl p : ℝ) : ℂ) * Phi.1.1 p) *
          (((p.1.2 - p.1.1) * picardGapInvJetRemainder ha haL e ell kappa he hk z hl hgap p : ℝ) :
              ℂ)) =
    (p.1.2 - p.1.1) ^ 2 • ((picardZJetRemainder e ell kappa he hk z hl hgap p : ℂ) *
      picardScalarRemainder ell he z hl p + (picardZRemainder e ell kappa he hk z hl hgap p : ℂ) *
          F.1.2 p +
      (Complex.I * (e : ℂ)) * (((picardChargeKernel e ell he z hl p : ℂ) * Phi.1.1 p +
        ((p.1.2 - p.1.1 : ℝ) : ℂ) * (picardChargeRemainder e ell he z hl p : ℂ) * Phi.1.2 p) *
            (U.1.1 p : ℂ) +
        ((p.1.2 - p.1.1 : ℝ) : ℂ) ^ 2 * (picardChargeRemainder e ell he z hl p : ℂ) * Phi.1.1 p *
          (picardGapInvJetRemainder ha haL e ell kappa he hk z hl hgap p : ℂ)))
  simp only [Complex.real_smul]
  push_cast
  ring


/-- The charged numerator carrier has the exact raw reconstruction values. -/
theorem picardWRecon_value (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p :
        PicardDomain c a L) :
    (picardWRecon ha haL e ell kappa he hk z hl hgap).1.1 p =
      (Recon.z e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 : ℂ) *
        Recon.ratio (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 +
        Complex.I * e * Recon.Q e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1
            p.1.2 *
          Recon.phi (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 /
          (1 - (Recon.mu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 :
              ℂ)) := by
  have hf : (picardScalarDifferenceRecon ha haL ell he z hl).1.1 p =
      Recon.ratio (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 := by
    change (z.1.1 p).2 - picardPhiValues ell he z hl p = _
    rw [Recon.ratio_def, picardCandidateH_coe ha haL z p, ←picardPhiValues_eq_recon ha haL ell he z
        hl p]
  have hphi : (picardScalarRecon ha haL ell he z hl).1.1 p =
      Recon.phi (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 := by
    change picardPhiValues ell he z hl p = _
    exact picardPhiValues_eq_recon ha haL ell he z hl p
  simp only [picardWRecon, picardCarrierAdd_value, picardCarrierCMul_value,
      picardCarrierLinear_value,
    smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  change (picardZValues e ell kappa he hk z hl hgap p : ℂ) * (picardScalarDifferenceRecon ha haL ell
      he z hl).1.1 p +
    (Complex.I * (e : ℂ)) * (((picardChargeRecon ha haL e ell he z hl).1.1 p : ℂ) *
      (picardScalarRecon ha haL ell he z hl).1.1 p * ((picardGapInv ha haL e ell kappa he hk z hl
          hgap).1.1 p : ℂ)) = _
  rw [hf, hphi, picardChargeRecon_value, picardGapInv_value, picardMuValues_eq_recon ha haL e ell he
      z hl p,
    picardZValues_eq_recon ha haL e ell kappa he hk z hl hgap p]
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- The numerator `-nu*W` of the incoming scalar source as an outgoing carrier. -/
@[expose] noncomputable def picardPNumerator (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
        PicardCarrier c a L ℂ :=
  picardCarrierNeg ha haL (picardCarrierCMul ha haL
    (picardCarrierLinear ha haL Complex.ofRealCLM (picardNuRecon ha haL e ell kappa he hk z hl
        hgap)) (picardWRecon ha haL e ell kappa he hk z hl hgap))

/-- The continuous cubic value profile of `-nu*W`. -/
@[expose] noncomputable def picardPNumeratorRemainder (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
        C(PicardDomain c a L, ℂ) :=
  -(picardComplexProfile ((picardNuRecon ha haL e ell kappa he hk z hl hgap).1.1)) *
      picardWRemainder ha haL e ell kappa he hk z hl hgap

/-- The continuous quadratic outgoing-jet profile of `-nu*W`. -/
@[expose] noncomputable def picardPNumeratorJetRemainder (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa :
    ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
        C(PicardDomain c a L, ℂ) :=
  -picardComplexProfile picardWidth * picardComplexProfile ((picardNuRecon ha haL e ell kappa he hk
      z hl hgap).1.2) * picardWRemainder ha haL e ell kappa he hk z hl hgap -
    picardComplexProfile ((picardNuRecon ha haL e ell kappa he hk z hl hgap).1.1) *
        picardWJetRemainder ha haL e ell kappa he hk z hl hgap

/-- The scalar-source numerator has exactly its cubic value profile. -/
theorem picardPNumerator_value_profile (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p :
        PicardDomain c a L) :
    (picardPNumerator ha haL e ell kappa he hk z hl hgap).1.1 p = (p.1.2 - p.1.1) ^ 3 •
        picardPNumeratorRemainder ha haL e ell kappa he hk z hl hgap p := by
  simp only [picardPNumerator, picardCarrierNeg_value, picardCarrierCMul_value,
      picardCarrierLinear_value,
    picardWRecon_value_profile]
  change -(((picardNuRecon ha haL e ell kappa he hk z hl hgap).1.1 p : ℂ) *
    ((p.1.2 - p.1.1) ^ 3 • picardWRemainder ha haL e ell kappa he hk z hl hgap p)) =
    (p.1.2 - p.1.1) ^ 3 • (-((picardNuRecon ha haL e ell kappa he hk z hl hgap).1.1 p : ℂ) *
        picardWRemainder ha haL e ell kappa he hk z hl hgap p)
  simp only [Complex.real_smul]
  ring

/-- The scalar-source numerator has exactly its quadratic outgoing-jet profile. -/
theorem picardPNumerator_jet_profile (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p :
        PicardDomain c a L) :
    (picardPNumerator ha haL e ell kappa he hk z hl hgap).1.2 p = (p.1.2 - p.1.1) ^ 2 •
        picardPNumeratorJetRemainder ha haL e ell kappa he hk z hl hgap p := by
  simp only [picardPNumerator, picardCarrierNeg_jet, picardCarrierCMul_jet,
    picardCarrierLinear_value, picardCarrierLinear_jet, picardWRecon_value_profile,
        picardWRecon_jet_profile]
  change -(((picardNuRecon ha haL e ell kappa he hk z hl hgap).1.2 p : ℂ) * ((p.1.2 - p.1.1) ^ 3 •
      picardWRemainder ha haL e ell kappa he hk z hl hgap p) +
    ((picardNuRecon ha haL e ell kappa he hk z hl hgap).1.1 p : ℂ) * ((p.1.2 - p.1.1) ^ 2 •
        picardWJetRemainder ha haL e ell kappa he hk z hl hgap p)) =
    (p.1.2 - p.1.1) ^ 2 • (-((p.1.2 - p.1.1 : ℝ) : ℂ) * ((picardNuRecon ha haL e ell kappa he hk z
        hl hgap).1.2 p : ℂ) *
      picardWRemainder ha haL e ell kappa he hk z hl hgap p - ((picardNuRecon ha haL e ell kappa he
          hk z hl hgap).1.1 p : ℂ) * picardWJetRemainder ha haL e ell kappa he hk z hl hgap p)
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The exact incoming scalar source `P` as an outgoing first-jet carrier on S1. -/
@[expose] noncomputable def picardPRecon (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
        PicardCarrier c a L ℂ := by
  refine picardDivideRadius ha haL ell he z hl (picardPNumerator ha haL e ell kappa he hk z hl hgap)
    (picardWidthSmul (picardPNumeratorRemainder ha haL e ell kappa he hk z hl hgap))
        (picardWidthSmul (picardPNumeratorJetRemainder ha haL e ell kappa he hk z hl hgap)) ?_ ?_
  · intro p
    rw [picardPNumerator_value_profile]
    change (p.1.2 - p.1.1) ^ 3 • picardPNumeratorRemainder ha haL e ell kappa he hk z hl hgap p =
      (p.1.2 - p.1.1) ^ 2 • ((p.1.2 - p.1.1) • picardPNumeratorRemainder ha haL e ell kappa he hk z
          hl hgap p)
    simp only [smul_smul]
    congr 1
  · intro p
    rw [picardPNumerator_jet_profile]
    change (p.1.2 - p.1.1) ^ 2 • picardPNumeratorJetRemainder ha haL e ell kappa he hk z hl hgap p =
      (p.1.2 - p.1.1) • ((p.1.2 - p.1.1) • picardPNumeratorJetRemainder ha haL e ell kappa he hk z
          hl hgap p)
    simp only [smul_smul, pow_two]

/-- The scalar-source carrier equals the literal source in `Recon.picardH`, including the axis. -/
theorem picardPRecon_value (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) (p :
        PicardDomain c a L) :
    (picardPRecon ha haL e ell kappa he hk z hl hgap).1.1 p =
      ((-Recon.nu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 /
        Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2 : ℝ) : ℂ) *
        ((Recon.z e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 : ℂ) *
          Recon.ratio (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 +
          Complex.I * e * Recon.Q e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1
              p.1.2 *
            Recon.phi (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 /
            (1 - (Recon.mu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 :
                ℂ))) := by
  simp only [picardPRecon, picardDivideRadius_value, picardPNumerator, picardCarrierNeg_value,
    picardCarrierCMul_value, picardCarrierLinear_value, picardNuRecon_value, picardWRecon_value]
  change (Recon.r (picardCandidateLam ha haL z) p.1.1 p.1.2)⁻¹ •
    (-((Recon.nu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) p.1.1 p.1.2 : ℂ) * _))
        = _
  simp only [Complex.real_smul]
  push_cast
  simp only [div_eq_mul_inv]
  ring



/-- The ordinary incoming scalar source at a fixed point, `-ie*A*h + P`,
as a compatible outgoing first-jet carrier. -/
@[expose] noncomputable def picardOrdinarySourceRecon (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell kappa : ℝ) (he : 0 < ell) (hk : 0 < kappa)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) : PicardCarrier c a L ℂ :=
  let A := picardCarrierLinear ha haL Complex.ofRealCLM (picardARecon ha haL e ell kappa he hk z hl
      hgap)
  let H := picardCarrierLinear ha haL (ContinuousLinearMap.snd ℝ ℝ ℂ) z
  picardCarrierAdd ha haL
    (picardCarrierLinear ha haL ((-(Complex.I * (e : ℂ))) • ContinuousLinearMap.id ℝ ℂ)
      (picardCarrierCMul ha haL A H)) (picardPRecon ha haL e ell kappa he hk z hl hgap)

end EmcsfAcExtension.Local
