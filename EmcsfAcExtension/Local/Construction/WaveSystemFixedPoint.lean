module

public import EmcsfAcExtension.Local.Defs.Picard
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Local.Construction.FullSystemCoefficients
import EmcsfAcExtension.Local.Construction.FullSystemRegularity
import EmcsfAcExtension.Local.Construction.WaveSystem
import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # The actual C¹ rφ primitive at a Picard fixed point

internal project record (23): the outgoing primitive has source λh, and that C¹
source has the covariant incoming wave derivative. Both Picard equations
remain explicit and every derivative is taken within the original wedge.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Null

/-- [node restart-sec-independent-null-construction#rphi-wave-identity]
The actual primitive's outgoing derivative is λh, whose incoming partial
satisfies the covariant rφ wave equation off axis. Joint C¹ of the pair
is the previously proved carrier upgrade. The selected mixed derivative
is obtained from the primitive, without any C² hypothesis. Bounds `l,κ`
are fixed before the candidate and there are no estimate constants. -/
theorem rphi_wave_identity {a b c l κ e : ℝ}
    (hac : a < c) (hcb : c ≤ b) {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ}
    {lam₀ : ℝ → ℝ} {h₀ : ℝ → ℂ} (hl : 0 < l) (hκ : 0 < κ)
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContDiffOn ℝ 1 (Function.uncurry hh)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2)
    (hgap : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      κ ≤ 1 - Recon.mu e lam hh p.1 p.2)
    (hL : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardLam e lam hh a lam₀ p.1 p.2 = lam p.1 p.2)
    (hH : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardH e lam hh a h₀ p.1 p.2 = hh p.1 p.2) :
    (∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c})
        (fun u v => (Recon.r lam u v : ℂ) * Recon.phi lam hh u v) p.1 p.2 =
        (lam p.1 p.2 : ℂ) * hh p.1 p.2) ∧
    (∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, p.1 < p.2 →
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c})
        (fun u v => (lam u v : ℂ) * hh u v) p.1 p.2 =
      (Recon.nu e lam hh p.1 p.2 : ℂ) * lam p.1 p.2 /
          ((1 - (Recon.mu e lam hh p.1 p.2 : ℂ)) * (Recon.r lam p.1 p.2 : ℂ) ^ 2) *
        ((Recon.mu e lam hh p.1 p.2 : ℂ) -
          (Recon.Q e lam hh p.1 p.2 : ℂ) ^ 2 / (Recon.r lam p.1 p.2 : ℂ) ^ 2 -
          I * e * Recon.Q e lam hh p.1 p.2) *
        ((Recon.r lam p.1 p.2 : ℂ) * Recon.phi lam hh p.1 p.2) -
        I * e * Recon.A e lam hh p.1 p.2 * ((lam p.1 p.2 : ℂ) * hh p.1 p.2)) := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  obtain ⟨cr, cp, _, _⟩ := contDiffOn_radial_scalar_fields hac hcb hl cl ch hlo
  obtain ⟨_, _, _, _, _, cA, cG, cP⟩ :=
    contDiffOn_reconstruction_coefficients hac hcb hl hκ cl ch hlo hgap
  have cN : ContDiffOn ℝ 1
      (Function.uncurry (fun u v => (Recon.r lam u v : ℂ) * Recon.phi lam hh u v)) D := by
    simpa only [Function.uncurry, Function.comp_apply] using!
      (Complex.ofRealCLM.contDiff.comp_contDiffOn cr).mul cp
  have cJ : ContDiffOn ℝ 1 (Function.uncurry (fun u v => (lam u v : ℂ) * hh u v)) D := by
    simpa only [Function.uncurry, Function.comp_apply] using!
      (Complex.ofRealCLM.contDiff.comp_contDiffOn cl).mul ch
  have hsV (u : ℝ) (hu : u ∈ Icc a c) : MapsTo (fun v => (u, v)) (Icc u b) D :=
    fun v hv => ⟨⟨hu.1, hv.1, hv.2⟩, hu.2⟩
  have cl' (u : ℝ) (hu : u ∈ Icc a c) : ContinuousOn (lam u) (Icc u b) :=
    cl.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) (hsV u hu)
  have ch' (u : ℝ) (hu : u ∈ Icc a c) : ContinuousOn (hh u) (Icc u b) :=
    ch.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) (hsV u hu)
  constructor
  · apply pdV_on_wedge_eq_of_sectional hac hcb cN cJ.continuousOn
    intro p hp
    exact Recon.hasDerivWithinAt_r_mul_phi hl (cl' p.1 ⟨hp.1.1, hp.2⟩)
      (ch' p.1 ⟨hp.1.1, hp.2⟩) (fun v hv => hlo (p.1, v) (hsV p.1 ⟨hp.1.1, hp.2⟩ hv))
      ⟨hp.1.2.1, hp.1.2.2⟩
  · intro p hp huv
    let U := min c ((p.1 + p.2) / 2)
    have huU : p.1 ≤ U := le_min hp.2 (by linarith only [huv])
    have hUc : U ≤ c := min_le_left _ _
    have hUv : U < p.2 := (min_le_right _ _).trans_lt (by linarith only [huv])
    have haU : a < U := lt_min hac (by linarith only [hp.1.1, huv])
    have hu : p.1 ∈ Icc a U := ⟨hp.1.1, huU⟩
    have hsU : MapsTo (fun u => (u, p.2)) (Icc a U) D :=
      fun u hu => ⟨⟨hu.1, hu.2.trans hUv.le, hp.1.2.2⟩, hu.2.trans hUc⟩
    have dw := rphi_wave_identity_of_picard (e := e) (c := a) (U := U) (b := b)
      (u := p.1) (v := p.2) hl hκ hu hUv hp.1.2.2
      (fun u hu => cl' u ⟨hu.1, hu.2.trans hUc⟩)
      (fun u hu => ch' u ⟨hu.1, hu.2.trans hUc⟩)
      (fun u hu s hs => hlo (u, s) ⟨⟨hu.1, hs.1, hs.2⟩, hu.2.trans hUc⟩)
      (fun u hu s hs => hgap (u, s) ⟨⟨hu.1, hs.1, hs.2⟩, hu.2.trans hUc⟩)
      (cG.continuousOn.comp (f := fun u : ℝ => (u, p.2))
        (continuousOn_id.prodMk continuousOn_const) hsU)
      (cA.continuousOn.comp (f := fun u : ℝ => (u, p.2))
        (continuousOn_id.prodMk continuousOn_const) hsU)
      (cP.continuousOn.comp (f := fun u : ℝ => (u, p.2))
        (continuousOn_id.prodMk continuousOn_const) hsU)
      (fun u hu => hL (u, p.2) (hsU hu)) (fun u hu => hH (u, p.2) (hsU hu))
    have heq (u : ℝ) (hu : u ∈ Icc a U) :
        derivWithin (fun s => (Recon.r lam u s : ℂ) * Recon.phi lam hh u s)
          (Icc u b) p.2 = (lam u p.2 : ℂ) * hh u p.2 :=
      (Recon.hasDerivWithinAt_r_mul_phi hl (cl' u ⟨hu.1, hu.2.trans hUc⟩)
        (ch' u ⟨hu.1, hu.2.trans hUc⟩)
        (fun s hs => hlo (u, s) ⟨⟨hu.1, hs.1, hs.2⟩, hu.2.trans hUc⟩)
        ⟨(hu.2.trans_lt hUv).le, hp.1.2.2⟩).derivWithin
        (uniqueDiffOn_Icc ((hu.2.trans_lt hUv).trans_le hp.1.2.2) p.2
          ⟨(hu.2.trans_lt hUv).le, hp.1.2.2⟩)
    have dj : HasDerivWithinAt (fun u => (lam u p.2 : ℂ) * hh u p.2) _ (Icc a U) p.1 :=
      dw.congr (fun u hu => (heq u hu).symm) (heq p.1 hu).symm
    exact ((hasDerivWithinAt_pdU cJ hp hsU).derivWithin
      (uniqueDiffOn_Icc haU p.1 hu)).symm.trans (dj.derivWithin (uniqueDiffOn_Icc haU p.1 hu))

end EmcsfAcExtension.Local.Null
