module

public import EmcsfAcExtension.Local.Construction.FullSystemLinear
public import EmcsfAcExtension.Local.Calculus.Partials

/-! # Incoming first regularity of the scalar jet from b's primitive

internal project record (26)–(28). Dividing the already continuous incoming jet by
its nonvanishing expansion yields a linear outgoing ODE whose coefficients
are C¹. Its primitive supplies the missing incoming first derivative.
-/

public section

open Set Complex
open scoped Topology

namespace EmcsfAcExtension.Local.Null

/-- A continuous wave jet becomes jointly C¹ through the normalized
incoming scalar's linear primitive. The displayed derivative of `X` uses
only the first outgoing partial of φ. No incoming derivative of `X` or
second derivative of φ is a premise. The coefficients `B,J` are literal
regularized radial intermediates, with no estimate constants. -/
theorem contDiffOn_incoming_wave_jet_of_linear_primitive {a b c : ℝ}
    (hac : a < c) (hcb : c ≤ b)
    {phi X J : ℝ → ℝ → ℂ} {nu B : ℝ → ℝ → ℝ} {g : ℝ → ℂ}
    (cp : ContDiffOn ℝ 1 (Function.uncurry phi) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cn : ContDiffOn ℝ 1 (Function.uncurry nu) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cB : ContDiffOn ℝ 1 (Function.uncurry B) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cJ : ContDiffOn ℝ 1 (Function.uncurry J) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cX : ContinuousOn (Function.uncurry X) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cg : ContDiffOn ℝ 1 g (Icc a c))
    (hn : ∀ p ∈ triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}, nu p.1 p.2 ≠ 0)
    (hg : ∀ t ∈ Icc a c, phi t t = g t)
    (hX0 : ∀ t ∈ Icc a c, X t t = 0)
    (dnu : ∀ u ∈ Icc a c, ∀ v ∈ Ioo u b,
      HasDerivAt (nu u) (nu u v * B u v) v)
    (dX : ∀ u ∈ Icc a c, ∀ v ∈ Ioo u b,
      HasDerivAt (X u)
        (-((nu u v : ℂ) * pdV (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) phi u v) +
          (nu u v : ℂ) * J u v) v) :
    ContDiffOn ℝ 1 (Function.uncurry X) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let bb (u v : ℝ) := phi u v + X u v / (nu u v : ℂ)
  let F (u v : ℝ) := (B u v : ℂ) * phi u v + J u v
  have cnC := Complex.ofRealCLM.contDiff.comp_contDiffOn cn
  have cBC := Complex.ofRealCLM.contDiff.comp_contDiffOn cB
  have cbb : ContinuousOn (Function.uncurry bb) D := cp.continuousOn.add
    (cX.div cnC.continuousOn (fun p hp => Complex.ofReal_ne_zero.mpr (hn p hp)))
  have cF : ContDiffOn ℝ 1 (Function.uncurry F) D := (cBC.mul cp).add cJ
  have dbb (u : ℝ) (hu : u ∈ Icc a c) (v : ℝ) (hv : v ∈ Ioo u b) :
      HasDerivAt (bb u) ((-B u v) • bb u v + F u v) v := by
    have hp : (u, v) ∈ D := ⟨⟨hu.1, hv.1.le, hv.2.le⟩, hu.2⟩
    have dp := (hasDerivWithinAt_pdV cp hp (s := Icc u b)
      (fun x hx => ⟨⟨hu.1, hx.1, hx.2⟩, hu.2⟩)).hasDerivAt (Icc_mem_nhds hv.1 hv.2)
    have hnC : (nu u v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hn (u, v) hp)
    have hq := (dX u hu v hv).div (dnu u hu v hv).ofReal_comp hnC
    convert dp.add hq using 1
    dsimp only [bb, F]
    rw [Complex.real_smul]
    push_cast
    field_simp [hnC]
    ring
  have cnegB : ContDiffOn ℝ 1 (Function.uncurry (fun u v => -B u v)) D := by
    simpa only [Function.uncurry, Pi.neg_apply] using! cB.neg
  have cbb' : ContDiffOn ℝ 1 (Function.uncurry bb) D :=
    contDiffOn_wedge_of_outgoing_linear_transport (f := bb) (F := F) (k := fun u v => -B u v)
      hac hcb cbb cF cnegB cg
      (fun t ht => by simp [bb, hX0 t ht, hg t ht]) dbb
  apply (cnC.mul (cbb'.sub cp)).congr
  intro p hp
  change X p.1 p.2 = (nu p.1 p.2 : ℂ) * (bb p.1 p.2 - phi p.1 p.2)
  dsimp only [bb]
  field_simp [Complex.ofReal_ne_zero.mpr (hn p hp)]
  ring

end EmcsfAcExtension.Local.Null
