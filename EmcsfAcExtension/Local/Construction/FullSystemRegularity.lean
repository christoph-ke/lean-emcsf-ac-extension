module

public import EmcsfAcExtension.Local.Construction.WaveSystemPicard
public import EmcsfAcExtension.Frozen.Triangle
public import EmcsfAcExtension.Local.Construction.FullSystemDomain
import EmcsfAcExtension.Infra.Calculus.SectionalC1
import EmcsfAcExtension.Local.Calculus.Partials

/-! # First joint regularity of a Picard fixed point

The C¹ part of internal project record `#smooth-regularity`, equation H3. Both fixed-point
equations remain explicit. Coefficient continuity and outgoing jets are
separate carrier inputs; this file does not assume a solution class.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Null


/-- The two literal Picard equations upgrade a continuous pair with
continuous outgoing first derivatives to joint C¹ regularity on a
nondegenerate closed construction wedge. The three coefficient continuity premises
are the outputs required from joint radial reconstruction. No incoming
derivative, higher regularity, or conclusion bundle is an input.
There are no estimate constants. -/
theorem contDiffOn_one_on_wedge_of_picard_of_continuous_coefficients
    {a b c e : ℝ} {lam lamV : ℝ → ℝ → ℝ} {hh hhV : ℝ → ℝ → ℂ}
    {lam₀ : ℝ → ℝ} {h₀ : ℝ → ℂ} (hac : a < c) (hcb : c ≤ b)
    (cl : ContinuousOn (Function.uncurry lam) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ch : ContinuousOn (Function.uncurry hh) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (clV : ContinuousOn (Function.uncurry lamV) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (chV : ContinuousOn (Function.uncurry hhV) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (dlV : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      HasDerivWithinAt (lam p.1) (lamV p.1 p.2) (Icc p.1 b) p.2)
    (dhV : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      HasDerivWithinAt (hh p.1) (hhV p.1 p.2) (Icc p.1 b) p.2)
    (cG : ContinuousOn (fun p : ℝ × ℝ =>
      Recon.nu e lam hh p.1 p.2 / Recon.r lam p.1 p.2 * Recon.z e lam hh p.1 p.2)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cA : ContinuousOn (Function.uncurry (Recon.A e lam hh)) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cP : ContinuousOn (fun p : ℝ × ℝ =>
      (((-Recon.nu e lam hh p.1 p.2 / Recon.r lam p.1 p.2 : ℝ) : ℂ) *
        ((Recon.z e lam hh p.1 p.2 : ℂ) * Recon.ratio lam hh p.1 p.2 +
          I * e * Recon.Q e lam hh p.1 p.2 * Recon.phi lam hh p.1 p.2 /
            (1 - (Recon.mu e lam hh p.1 p.2 : ℂ))))) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hL : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardLam e lam hh a lam₀ p.1 p.2 = lam p.1 p.2)
    (hH : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardH e lam hh a h₀ p.1 p.2 = hh p.1 p.2) :
    ContDiffOn ℝ 1 (Function.uncurry lam) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) ∧
      ContDiffOn ℝ 1 (Function.uncurry hh) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  have hs (p : ℝ × ℝ) (hp : p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :
      MapsTo (fun x => (x, p.2)) (Icc a (min c p.2)) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :=
    fun x hx => ⟨⟨hx.1, (le_min_iff.mp hx.2).2, hp.1.2.2⟩, (le_min_iff.mp hx.2).1⟩
  have cs : ∀ {E : Type} [TopologicalSpace E] {f : ℝ × ℝ → E},
      ContinuousOn f (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) →
      ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
        ContinuousOn (fun x => f (x, p.2)) (Icc a (min c p.2)) := by
    intro E _ f cf p hp
    exact cf.comp (continuousOn_id.prodMk continuousOn_const) (hs p hp)
  constructor
  · apply contDiffOn_wedge_of_sectional_derivatives hac hcb
      (gU := fun p => lam p.1 p.2 *
        (Recon.nu e lam hh p.1 p.2 / Recon.r lam p.1 p.2 * Recon.z e lam hh p.1 p.2))
      (gV := Function.uncurry lamV)
    · intro p hp
      exact Recon.hasDerivWithinAt_lam_of_picardLam (cs cG p hp) ⟨hp.1.1, le_min hp.2 hp.1.2.1⟩
        (fun x hx => hL (x, p.2) (hs p hp hx))
    · exact dlV
    · exact cl.mul cG
    · exact clV
  · apply contDiffOn_wedge_of_sectional_derivatives hac hcb
      (gU := fun p =>
        -(I * e * Recon.A e lam hh p.1 p.2) * hh p.1 p.2 +
          (((-Recon.nu e lam hh p.1 p.2 / Recon.r lam p.1 p.2 : ℝ) : ℂ) *
            ((Recon.z e lam hh p.1 p.2 : ℂ) * Recon.ratio lam hh p.1 p.2 +
              I * e * Recon.Q e lam hh p.1 p.2 * Recon.phi lam hh p.1 p.2 /
                (1 - (Recon.mu e lam hh p.1 p.2 : ℂ)))))
      (gV := Function.uncurry hhV)
    · intro p hp
      exact Recon.hasDerivWithinAt_h_of_picardH (cs cA p hp) (cs cP p hp)
        ⟨hp.1.1, le_min hp.2 hp.1.2.1⟩ (fun x hx => hH (x, p.2) (hs p hp hx))
    · exact dhV
    · exact ((continuousOn_const.mul
        (Complex.continuous_ofReal.comp_continuousOn cA)).neg.mul ch).add cP
    · exact chV

/-- A supplied continuous incoming sectional jet is the actual domain
partial everywhere on the closed wedge. Interior uniqueness and continuity
handle collapsed corner sections without asserting their uniqueness. -/
theorem pdU_on_wedge_eq_of_sectional {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b c : ℝ} {f : ℝ → ℝ → E} {U : ℝ × ℝ → E}
    (hac : a < c) (hcb : c ≤ b)
    (cf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cU : ContinuousOn U (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hU : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      HasDerivWithinAt (fun x => f x p.2) (U p) (Icc a (min c p.2)) p.1) :
    ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) f p.1 p.2 = U p := by
  apply eqOn_wedge_of_interior hac hcb
    (continuousOn_pdU cf (uniqueDiffOn_triangle_inter_fst_le hac hcb)) cU
  intro p hp
  have hs : MapsTo (fun x => (x, p.2)) (Icc a (min c p.2))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :=
    fun x hx => ⟨⟨hx.1, (le_min_iff.mp hx.2).2, (interior_subset hp).1.2.2⟩,
      (le_min_iff.mp hx.2).1⟩
  have hn : Icc a (min c p.2) ∈ nhds p.1 := by
    have ht := (show Continuous (fun x : ℝ => (x, p.2)) from
      continuous_id.prodMk continuous_const).continuousAt (x := p.1)
    exact Filter.mem_of_superset (ht.preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hp)) (fun _ hx => ⟨hx.1.1, le_min hx.2 hx.1.2.1⟩)
  exact ((hasDerivWithinAt_pdU cf (interior_subset hp) hs).hasDerivAt hn).deriv.symm.trans
    ((hU p (interior_subset hp)).hasDerivAt hn).deriv

/-- A continuous outgoing sectional jet is the actual domain partial
on the whole closed wedge, including a collapsed top radial section. -/
theorem pdV_on_wedge_eq_of_sectional {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b c : ℝ} {f : ℝ → ℝ → E} {V : ℝ × ℝ → E}
    (hac : a < c) (hcb : c ≤ b)
    (cf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cV : ContinuousOn V (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hV : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      HasDerivWithinAt (f p.1) (V p) (Icc p.1 b) p.2) :
    ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) f p.1 p.2 = V p := by
  apply eqOn_wedge_of_interior hac hcb
    (continuousOn_pdV cf (uniqueDiffOn_triangle_inter_fst_le hac hcb)) cV
  intro p hp
  have hs : MapsTo (fun x => (p.1, x)) (Icc p.1 b)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :=
    fun x hx => ⟨⟨(interior_subset hp).1.1, hx.1, hx.2⟩, (interior_subset hp).2⟩
  have hn : Icc p.1 b ∈ nhds p.2 := by
    have ht := (show Continuous (fun x : ℝ => (p.1, x)) from
      continuous_const.prodMk continuous_id).continuousAt (x := p.2)
    exact Filter.mem_of_superset (ht.preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hp)) (fun _ hx => ⟨hx.1.2.1, hx.1.2.2⟩)
  exact ((hasDerivWithinAt_pdV cf (interior_subset hp) hs).hasDerivAt hn).deriv.symm.trans
    ((hV p (interior_subset hp)).hasDerivAt hn).deriv

/-- The incoming expansion transport is an actual domain partial at every
fixed-point wedge point, including its axis corners. The input is the
literal fixed-point equation and the C¹ pair already recovered from the
carrier. There are no estimate constants. -/
theorem pdU_lam_on_wedge_of_picard {a b c e : ℝ} (hac : a < c) (hcb : c ≤ b)
    {lam : ℝ → ℝ → ℝ} {hh : ℝ → ℝ → ℂ} {lam₀ : ℝ → ℝ}
    (cl : ContDiffOn ℝ 1 (Function.uncurry lam) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cG : ContinuousOn (fun p : ℝ × ℝ => Recon.nu e lam hh p.1 p.2 /
      Recon.r lam p.1 p.2 * Recon.z e lam hh p.1 p.2)
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (hfix : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      Recon.picardLam e lam hh a lam₀ p.1 p.2 = lam p.1 p.2) :
    ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c},
      pdU (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) lam p.1 p.2 =
        lam p.1 p.2 * (Recon.nu e lam hh p.1 p.2 /
          Recon.r lam p.1 p.2 * Recon.z e lam hh p.1 p.2) := by
  apply pdU_on_wedge_eq_of_sectional hac hcb cl (cl.continuousOn.mul cG)
  intro p hp
  have hs : MapsTo (fun x => (x, p.2)) (Icc a (min c p.2))
      (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) :=
    fun x hx => ⟨⟨hx.1, (le_min_iff.mp hx.2).2, hp.1.2.2⟩, (le_min_iff.mp hx.2).1⟩
  exact Recon.hasDerivWithinAt_lam_of_picardLam
    (cG.comp (continuousOn_id.prodMk continuousOn_const) hs)
    ⟨hp.1.1, le_min hp.2 hp.1.2.1⟩ (fun x hx => hfix (x, p.2) (hs hx))

end EmcsfAcExtension.Local.Null
