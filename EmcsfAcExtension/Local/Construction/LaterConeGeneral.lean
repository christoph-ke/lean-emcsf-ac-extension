module

public import EmcsfAcExtension.Local.Construction.LaterCone

/-! # The exact later-cone map on a general S1 wedge

This companion to `later_cone_map` exposes the general-domain conclusion of
`charged_SF_new_version.tex:L5975–L5992`, using internal project record §later-cone-map and
internal project record §later-cone-map. The C¹ datum supplies the actual cone center;
the candidate has the positive expansion and gap required by internal project record.
-/

public section

open Set
open scoped ContDiff

namespace EmcsfAcExtension.Local.Null

/-- [node restart-sec-independent-null-construction#later-cone-map]
On every S1 wedge with `0 ≤ a ≤ L` and `0 < L`, the later-cone update is
the exact reconstruction map based at `c`, with both prescribed C¹ datum
factors. It takes the prescribed starting values, has regular vertex
reconstruction, and every actual fixed point has zero incoming within
derivatives on the axis. The outgoing datum derivatives are unrestricted.
There is no upper cap on `a` or `L` and there are no estimate constants.
The expansion and gap margins `ell,κ` specify the candidate's S1 domain;
the companion `later_cone_map` supplies uniform short-cone existence. -/
theorem later_cone_map_general {c a L : ℝ} (ha : 0 ≤ a) (haL : a ≤ L)
    (hL : 0 < L) (e ell κ : ℝ) (he : 0 < ell) (hκ : 0 < κ)
    (datum : ℝ → ℝ × ℂ) (hc : ContDiffOn ℝ 1 datum (Icc c (c + L)))
    (z : PicardCarrier c a L (ℝ × ℂ))
    (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q) :
    let center := picardConeCenterOfContDiff (a := a) datum hL hc
    let lam := picardCandidateLam ha haL z
    let hh := picardCandidateH ha haL z
    (∀ p : PicardDomain c a L,
      (picardCarrierUpdate ha haL e ell κ he hκ center z hl hg).1.1 p =
        (Recon.picardLam e lam hh c (fun v => (datum v).1) p.1.1 p.1.2,
         Recon.picardH e lam hh c (fun v => (datum v).2) p.1.1 p.1.2)) ∧
    (∀ v, Recon.picardLam e lam hh c (fun v => (datum v).1) c v = (datum v).1 ∧
      Recon.picardH e lam hh c (fun v => (datum v).2) c v = (datum v).2) ∧
    (Recon.r lam c c = 0 ∧ Recon.phi lam hh c c = hh c c ∧
      Recon.Q e lam hh c c = 0 ∧ Recon.m e lam hh c c = 0 ∧
      Recon.mu e lam hh c c = 0 ∧ Recon.nu e lam hh c c = -lam c c ∧
      Recon.A e lam hh c c = 0) ∧
    ((∀ p : PicardDomain c a L, z.1.1 p =
        picardUpdate ha haL e (fun v => (datum v).1) (fun v => (datum v).2) z p.1.1 p.1.2) →
      ∀ (p : PicardDomain c a L), p.1.2 = p.1.1 →
        HasDerivWithinAt (fun u => lam u p.1.2) 0 (Icc c p.1.1) p.1.1 ∧
        HasDerivWithinAt (fun u => hh u p.1.2) 0 (Icc c p.1.1) p.1.1) := by
  let center := picardConeCenterOfContDiff (a := a) datum hL hc
  have ids := laterCone_map_identities_of_center_values ha haL e ell κ he hκ center z hl hg
    (fun v => (datum v).1) (fun v => (datum v).2) (fun _ => rfl)
  refine ⟨ids.1, ?_, ids.2.1, ids.2.2.2.2.2⟩
  intro v
  exact ⟨Recon.picardLam_initial e _ _ c _ v, Recon.picardH_initial e _ _ c _ v⟩

end EmcsfAcExtension.Local.Null
