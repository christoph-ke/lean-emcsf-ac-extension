module

public import EmcsfAcExtension.Local.Defs.C1Class
public import EmcsfAcExtension.Local.Defs.Picard
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Local.Construction.FullSystem
import EmcsfAcExtension.Local.Construction.FullSystemRegularity
import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # internal project record carrier interface for C¹ system recovery

The raw inputs are exactly continuous values/outgoing jets on the closed
wedge and their sectional FTC compatibility, as in internal project record.
All incoming derivatives and all primary-field C¹ regularity are proved.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Null

/-- Sectional FTC compatibility in the actual internal project record carrier supplies
both outgoing derivatives, including within derivatives on collapsed
sections. The two literal fixed-point equations then give joint C¹ of the
pair on the full wedge. No ambient derivative of a clamped representative
or higher jet is assumed, and there are no estimate constants. -/
theorem contDiffOn_pair_of_picard_carrier
    {a b c e : ℝ} {lam lamV : ℝ → ℝ → ℝ} {hh hhV : ℝ → ℝ → ℂ}
    {lam₀ : ℝ → ℝ} {h₀ : ℝ → ℂ} (hac : a < c) (hcb : c ≤ b)
    (cl : ContinuousOn (Function.uncurry lam) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContinuousOn (Function.uncurry hh) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (clV : ContinuousOn (Function.uncurry lamV) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (chV : ContinuousOn (Function.uncurry hhV) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (fl : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      lam p.1 p.2 = lam p.1 p.1 + ∫ s in p.1..p.2, lamV p.1 s)
    (fh : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      hh p.1 p.2 = hh p.1 p.1 + ∫ s in p.1..p.2, hhV p.1 s)
    (cG : ContinuousOn (fun p : ℝ × ℝ => Recon.nu e lam hh p.1 p.2 /
      Recon.r lam p.1 p.2 * Recon.z e lam hh p.1 p.2)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cA : ContinuousOn (Function.uncurry (Recon.A e lam hh))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cP : ContinuousOn (fun p : ℝ × ℝ =>
      (((-Recon.nu e lam hh p.1 p.2 / Recon.r lam p.1 p.2 : ℝ) : ℂ) *
        ((Recon.z e lam hh p.1 p.2 : ℂ) * Recon.ratio lam hh p.1 p.2 +
          I * e * Recon.Q e lam hh p.1 p.2 * Recon.phi lam hh p.1 p.2 /
            (1 - (Recon.mu e lam hh p.1 p.2 : ℂ)))))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hL : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardLam e lam hh a lam₀ p.1 p.2 = lam p.1 p.2)
    (hH : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardH e lam hh a h₀ p.1 p.2 = hh p.1 p.2) :
    ContDiffOn ℝ 1 (Function.uncurry lam) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      ContDiffOn ℝ 1 (Function.uncurry hh) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  have hs (p : ℝ × ℝ) (hp : p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :
      MapsTo (fun v => (p.1, v)) (Icc p.1 b) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :=
    fun v hv => ⟨⟨hp.1.1, hv.1, hv.2⟩, hp.2⟩
  apply contDiffOn_one_on_wedge_of_picard_of_continuous_coefficients hac hcb cl ch clV chV
  · intro p hp
    have hd := (hasDerivWithinAt_const p.2 (Icc p.1 b) (lam p.1 p.1)).add
      (Recon.hasDerivWithinAt_primitive
        (clV.comp (continuousOn_const.prodMk continuousOn_id) (hs p hp))
        ⟨hp.1.2.1, hp.1.2.2⟩)
    simp only [zero_add] at hd
    exact hd.congr (fun v hv => fl (p.1, v) (hs p hp hv)) (fl p hp)
  · intro p hp
    have hd := (hasDerivWithinAt_const p.2 (Icc p.1 b) (hh p.1 p.1)).add
      (Recon.hasDerivWithinAt_primitive
        (chV.comp (continuousOn_const.prodMk continuousOn_id) (hs p hp))
        ⟨hp.1.2.1, hp.1.2.2⟩)
    simp only [zero_add] at hd
    exact hd.congr (fun v hv => fh (p.1, v) (hs p hp hv)) (fh p hp)
  · exact cG
  · exact cA
  · exact cP
  · exact hL
  · exact hH

/--
The complete internal project record internal project record assembly from C¹ cone data and the
exact raw
internal project record carrier interface. All nine actual reconstructions form an
`IsC1Solution` on the original closed wedge and retain the zero axis gauge.
Neither incoming constraint nor any higher regularity is a premise. Bounds
`l,κ` are fixed before the candidate and no estimate constant is introduced. -/
theorem smooth_full_system
    {a b c l κ e : ℝ} {lam lamV : ℝ → ℝ → ℝ} {hh hhV : ℝ → ℝ → ℂ}
    {lam₀ : ℝ → ℝ} {h₀ : ℝ → ℂ} (hac : a < c) (hcb : c ≤ b)
    (hl : 0 < l) (hκ : 0 < κ)
    (_cLam₀ : ContDiffOn ℝ 1 lam₀ (Icc a b))
    (_cH₀ : ContDiffOn ℝ 1 h₀ (Icc a b))
    (cl : ContinuousOn (Function.uncurry lam) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContinuousOn (Function.uncurry hh) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (clV : ContinuousOn (Function.uncurry lamV) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (chV : ContinuousOn (Function.uncurry hhV) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (fl : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      lam p.1 p.2 = lam p.1 p.1 + ∫ s in p.1..p.2, lamV p.1 s)
    (fh : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      hh p.1 p.2 = hh p.1 p.1 + ∫ s in p.1..p.2, hhV p.1 s)
    (cG : ContinuousOn (fun p : ℝ × ℝ => Recon.nu e lam hh p.1 p.2 /
      Recon.r lam p.1 p.2 * Recon.z e lam hh p.1 p.2)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cA : ContinuousOn (Function.uncurry (Recon.A e lam hh))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cP : ContinuousOn (fun p : ℝ × ℝ =>
      (((-Recon.nu e lam hh p.1 p.2 / Recon.r lam p.1 p.2 : ℝ) : ℂ) *
        ((Recon.z e lam hh p.1 p.2 : ℂ) * Recon.ratio lam hh p.1 p.2 +
          I * e * Recon.Q e lam hh p.1 p.2 * Recon.phi lam hh p.1 p.2 /
            (1 - (Recon.mu e lam hh p.1 p.2 : ℂ)))))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hL : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardLam e lam hh a lam₀ p.1 p.2 = lam p.1 p.2)
    (hH : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardH e lam hh a h₀ p.1 p.2 = hh p.1 p.2)
    (hlo : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, l ≤ lam p.1 p.2)
    (hgap : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      κ ≤ 1 - Recon.mu e lam hh p.1 p.2) :
    IsC1Solution e (Recon.toFields e lam hh) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      ∀ t ∈ Icc a c, (Recon.toFields e lam hh).A t t = 0 := by
  obtain ⟨cl1, ch1⟩ := contDiffOn_pair_of_picard_carrier hac hcb cl ch clV chV fl fh cG cA cP hL hH
  exact smooth_full_system_of_picard hac hcb hl hκ cl1 ch1 hlo hgap hL hH

end EmcsfAcExtension.Local.Null
