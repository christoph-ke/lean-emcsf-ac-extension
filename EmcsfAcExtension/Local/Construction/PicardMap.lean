module

public import EmcsfAcExtension.Local.Construction.PicardIncoming
public import EmcsfAcExtension.Local.Construction.PicardSources

/-! # The exact Picard map in the complete carrier

The reconstructed coefficients act in the outgoing value/jet carrier and give
exactly the audited incoming Picard formulas. Quantitative E3 estimates are
proved in `PicardUpdateBounds`; the original and short-cone constructions
restrict this exact map to their complete invariant balls.
-/

public section

open Set MeasureTheory Filter Topology
open scoped Topology

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

/-- Incoming integration reads exactly a raw source agreeing with the
continuous source on the wedge, for every incoming subsegment. -/
theorem picardIncoming_integral_eq_of_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ha : 0 ≤ a) (haL : a ≤ L) (f : C(PicardDomain c a L, E)) (raw : ℝ → ℝ → E)
    (hf : ∀ q : PicardDomain c a L, f q = raw q.1.1 q.1.2) (p : PicardDomain c a L)
    {b : ℝ} (hb : b ∈ Icc c p.1.1) :
    (∫ s in b..p.1.1, f (picardClamp ha haL (s, p.1.2))) = ∫ s in b..p.1.1, raw s p.1.2 := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hb.2] at hs
  let q : PicardDomain c a L := ⟨(s, p.1.2),
    ⟨⟨hb.1.trans hs.1, hs.2.trans p.2.1.2.1, p.2.1.2.2⟩, hs.2.trans p.2.2⟩⟩
  have hq : picardClamp ha haL (s, p.1.2) = q := picardClamp_coe ha haL q
  dsimp only
  rw [hq, hf q]
/-- The exact incoming Picard map as a compatible value and first-jet carrier
on the explicit positive-lambda and S1 gap domain. -/
@[expose] noncomputable def picardCarrierUpdate (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (center z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
    PicardCarrier c a L (ℝ × ℂ) :=
  picardIncomingCarrierUpdate ha haL e center
    (picardGRecon ha haL e ell kappa he hk z hl hgap)
    (picardARecon ha haL e ell kappa he hk z hl hgap)
    (picardPRecon ha haL e ell kappa he hk z hl hgap)

/-- The carrier map agrees exactly with `Recon.picardLam` and `Recon.picardH`
for a center carrying the prescribed cone data. Ball preservation and
contraction remain separate quantitative obligations. -/
theorem picardCarrierUpdate_value_of_center_values (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) (center z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1) (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q)
    (lam0 : ℝ → ℝ) (h0 : ℝ → ℂ)
    (hc : ∀ p : PicardDomain c a L, center.1.1 p = (lam0 p.1.2, h0 p.1.2)) (p : PicardDomain c a L)
        :
    (picardCarrierUpdate ha haL e ell kappa he hk center z hl hgap).1.1 p =
      (Recon.picardLam e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) c lam0 p.1.1
          p.1.2,
        Recon.picardH e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) c h0 p.1.1 p.1.2)
            := by
  let G := picardGRecon ha haL e ell kappa he hk z hl hgap
  let A := picardARecon ha haL e ell kappa he hk z hl hgap
  let P := picardPRecon ha haL e ell kappa he hk z hl hgap
  have hA {b : ℝ} (hb : b ∈ Icc c p.1.1) :
      (∫ s in b..p.1.1, A.1.1 (picardClamp ha haL (s, p.1.2))) =
        ∫ s in b..p.1.1, Recon.A e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) s p.1.2
            :=
    picardIncoming_integral_eq_of_eq ha haL _
      (Recon.A e (picardCandidateLam ha haL z) (picardCandidateH ha haL z))
      (picardARecon_value ha haL e ell kappa he hk z hl hgap) p hb
  apply Prod.ext
  · change ((picardIncomingCarrierUpdate ha haL e center G A P).1.1 p).1 = _
    rw [picardIncomingCarrierUpdate_value, Recon.picardLam_def, hc p]
    dsimp only
    congr 1
    congr 1
    exact picardIncoming_integral_eq_of_eq ha haL _
      (fun u v => Recon.nu e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) u v /
        Recon.r (picardCandidateLam ha haL z) u v *
        Recon.z e (picardCandidateLam ha haL z) (picardCandidateH ha haL z) u v)
      (picardGRecon_value ha haL e ell kappa he hk z hl hgap) p ⟨le_rfl, p.2.1.1⟩
  · change ((picardIncomingCarrierUpdate ha haL e center G A P).1.1 p).2 = _
    rw [picardIncomingCarrierUpdate_h_value, picardIncomingPhase_value, Recon.picardH_def, hc p,
      hA ⟨le_rfl, p.2.1.1⟩]
    dsimp only
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le p.2.1.1] at hs
    dsimp only
    rw [hA hs]
    let q : PicardDomain c a L := ⟨(s, p.1.2),
      ⟨⟨hs.1, hs.2.trans p.2.1.2.1, p.2.1.2.2⟩, hs.2.trans p.2.2⟩⟩
    have hq : picardClamp ha haL (s, p.1.2) = q := picardClamp_coe ha haL q
    rw [hq]
    rw [show P.1.1 q = _ from picardPRecon_value ha haL e ell kappa he hk z hl hgap q]

/-- The exact carrier Picard map preserves the prescribed initial cone values. -/
theorem picardCarrierUpdate_mem_initialSet (ha : 0 ≤ a) (haL : a ≤ L) (e ell kappa : ℝ)
    (he : 0 < ell) (hk : 0 < kappa) {datum : ℝ → ℝ × ℂ}
    {center : PicardCarrier c a L (ℝ × ℂ)} (hc : center ∈ picardInitialSet datum)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hgap : ∀ q, kappa ≤ 1 - picardMuValues e ell he z hl q) :
    picardCarrierUpdate ha haL e ell kappa he hk center z hl hgap ∈ picardInitialSet datum :=
  picardIncomingCarrierUpdate_mem_initialSet ha haL e hc _ _ _

end EmcsfAcExtension.Local
