module

public import EmcsfAcExtension.Local.Construction.FullSystemCoefficients
public import EmcsfAcExtension.Local.Construction.FullSystemRegularity
public import EmcsfAcExtension.Local.Construction.WaveSystemMixed

import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # Recovery of both radius derivatives at a C¹ Picard fixed point

The literal radius primitive and the reconstructed exponential have equal
cross transports. internal project record (21)–(22) then supplies the incoming radius
identity on the original closed construction wedge, without a C² premise.
-/

public section

open Set

namespace EmcsfAcExtension.Local.Null

/-- [node restart-sec-independent-null-construction#radius-null-identity]
The actual reconstructed radius satisfies both null derivative identities
on the entire closed fixed-point wedge. Joint C¹ of the pair is the output
of the carrier regularity step. The only fixed-point equation needed for
this geometric identity is the literal `picardLam` equation. Bounds `l`
and `κ` are explicit; no estimate constant or incoming radius equation is
assumed. -/
theorem radius_null_identity {a b c l κ e : ℝ}
    (hac : a < c) (hcb : c ≤ b) {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ}
    {lam₀ : ℝ → ℝ} (hl : 0 < l) (hκ : 0 < κ)
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContDiffOn ℝ 1 (Function.uncurry hh)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2)
    (hgap : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      κ ≤ 1 - Recon.mu e lam hh p.1 p.2)
    (hfix : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardLam e lam hh a lam₀ p.1 p.2 = lam p.1 p.2) :
    ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) (Recon.r lam) p.1 p.2 = lam p.1 p.2 ∧
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) (Recon.r lam) p.1 p.2 =
        Recon.nu e lam hh p.1 p.2 := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  obtain ⟨cr, _, _, _⟩ := contDiffOn_radial_scalar_fields hac hcb hl cl ch hlo
  obtain ⟨_, _, _, cC, cn, _, cG, _⟩ :=
    contDiffOn_reconstruction_coefficients hac hcb hl hκ cl ch hlo hgap
  have crv : ∀ p ∈ D, pdV D (Recon.r lam) p.1 p.2 = lam p.1 p.2 := by
    apply pdV_on_wedge_eq_of_sectional hac hcb cr cl.continuousOn
    intro p hp
    exact Recon.hasDerivWithinAt_r
      (cl.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
        (fun v hv => ⟨⟨hp.1.1, hv.1, hv.2⟩, hp.2⟩)) ⟨hp.1.2.1, hp.1.2.2⟩
  have cB : ContinuousOn (fun p : ℝ × ℝ => lam p.1 p.2 / Recon.r lam p.1 p.2 *
      Recon.z e lam hh p.1 p.2) D := by
    apply (cl.continuousOn.mul cC.continuousOn).congr
    intro p _
    dsimp only [Function.uncurry_def, Pi.mul_apply]
    ring
  have cnv : ∀ p ∈ D, pdV D (Recon.nu e lam hh) p.1 p.2 =
      Recon.nu e lam hh p.1 p.2 * lam p.1 p.2 /
        Recon.r lam p.1 p.2 * Recon.z e lam hh p.1 p.2 := by
    have cNV : ContinuousOn (fun p : ℝ × ℝ =>
        Recon.nu e lam hh p.1 p.2 * lam p.1 p.2 /
          Recon.r lam p.1 p.2 * Recon.z e lam hh p.1 p.2) D := by
      apply ((cn.continuousOn.mul cl.continuousOn).mul cC.continuousOn).congr
      intro p _
      dsimp only [Function.uncurry_def, Pi.mul_apply]
      ring
    apply pdV_on_wedge_eq_of_sectional hac hcb cn cNV
    intro p hp
    exact Recon.hasDerivWithinAt_nu_of_continuous
      (cB.comp (continuousOn_const.prodMk continuousOn_id)
        (fun v hv => ⟨⟨hp.1.1, hv.1, hv.2⟩, hp.2⟩)) ⟨hp.1.2.1, hp.1.2.2⟩
  have clu := pdU_lam_on_wedge_of_picard hac hcb cl cG.continuousOn hfix
  have cru := radius_null_identity_on_wedge_of_outgoing_and_transport hac hcb cr cl cn crv
    (fun p hp => by rw [clu p hp, cnv p hp]; ring)
    (fun _ _ => Recon.r_axis) (fun _ _ => Recon.nu_axis)
  exact fun p hp => ⟨crv p hp, cru p hp⟩

end EmcsfAcExtension.Local.Null
