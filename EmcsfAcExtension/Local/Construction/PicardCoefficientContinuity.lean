module

public import EmcsfAcExtension.Local.Construction.PicardMap

/-! # Joint continuity of the literal incoming coefficients

The exact carrier identifications transfer joint continuity to the raw
reconstruction formulas used by the incoming Picard equations. No incoming
derivative of an old candidate is assumed.
-/

public section

open Set

namespace EmcsfAcExtension.Local

variable {c a L : ℝ}

private theorem picard_continuousOn_of_carrier_aux {E : Type*} [TopologicalSpace E]
    (f : ℝ × ℝ → E) (F : C(PicardDomain c a L, E))
    (hF : ∀ p, F p = f p.1) :
    ContinuousOn f (triangle c (c + L) ∩ {p : ℝ × ℝ | p.1 ≤ c + a}) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun p : PicardDomain c a L => f p.1)
  have heq : (fun p : PicardDomain c a L => f p.1) = (F : PicardDomain c a L → E) :=
    funext (fun p => (hF p).symm)
  rw [heq]
  exact F.continuous

/-- The literal incoming coefficients G, A and P are jointly continuous on
the closed wedge, including the axis, for every outgoing carrier on S1's
positive-lambda and positive-gap domain. These are the coefficient continuity
inputs to the fixed-point regularity interface of internal project record. -/
theorem picard_coefficients_continuousOn (ha : 0 ≤ a) (haL : a ≤ L)
    (e ell κ : ℝ) (he : 0 < ell) (hκ : 0 < κ)
    (z : PicardCarrier c a L (ℝ × ℂ)) (hl : ∀ q, ell ≤ (z.1.1 q).1)
    (hg : ∀ q, κ ≤ 1 - picardMuValues e ell he z hl q) :
    let lam := picardCandidateLam ha haL z
    let hh := picardCandidateH ha haL z
    let D := triangle c (c + L) ∩ {p : ℝ × ℝ | p.1 ≤ c + a}
    ContinuousOn (fun p : ℝ × ℝ => Recon.nu e lam hh p.1 p.2 / Recon.r lam p.1 p.2 *
      Recon.z e lam hh p.1 p.2) D ∧
    ContinuousOn (Function.uncurry (Recon.A e lam hh)) D ∧
    ContinuousOn (fun p : ℝ × ℝ =>
      ((-Recon.nu e lam hh p.1 p.2 / Recon.r lam p.1 p.2 : ℝ) : ℂ) *
        ((Recon.z e lam hh p.1 p.2 : ℂ) * Recon.ratio lam hh p.1 p.2 +
          Complex.I * e * Recon.Q e lam hh p.1 p.2 * Recon.phi lam hh p.1 p.2 /
            (1 - (Recon.mu e lam hh p.1 p.2 : ℂ)))) D := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact picard_continuousOn_of_carrier_aux _
      (picardGRecon ha haL e ell κ he hκ z hl hg).1.1
      (picardGRecon_value ha haL e ell κ he hκ z hl hg)
  · exact picard_continuousOn_of_carrier_aux _
      (picardARecon ha haL e ell κ he hκ z hl hg).1.1
      (picardARecon_value ha haL e ell κ he hκ z hl hg)
  · exact picard_continuousOn_of_carrier_aux _
      (picardPRecon ha haL e ell κ he hκ z hl hg).1.1
      (picardPRecon_value ha haL e ell κ he hκ z hl hg)

end EmcsfAcExtension.Local
