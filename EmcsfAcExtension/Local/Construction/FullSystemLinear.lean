module

public import EmcsfAcExtension.Local.Construction.FullSystemIntegral
public import EmcsfAcExtension.Local.Construction.Defects
import EmcsfAcExtension.Local.Construction.ReconBasic

/-! # First regularity recovered from the outgoing linear primitive

The variation-of-constants step of internal project record (26)–(28). This supplies
incoming first regularity without differentiating a pre-existing incoming
partial a second time.
-/

public section

open Set MeasureTheory
open scoped Topology

namespace EmcsfAcExtension.Local.Null

/-- A continuous field solving an outgoing linear ODE with C¹ coefficient,
C¹ forcing, and C¹ axis trace is jointly C¹ on the original closed wedge.
The proof identifies the actual field with its C¹ variation-of-constants
primitive. No incoming derivative of that field is assumed. -/
theorem contDiffOn_wedge_of_outgoing_linear_transport {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b c : ℝ} (hac : a < c) (hcb : c ≤ b)
    {f F : ℝ → ℝ → E} {k : ℝ → ℝ → ℝ} {g : ℝ → E}
    (cf : ContinuousOn (Function.uncurry f) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cF : ContDiffOn ℝ 1 (Function.uncurry F) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (ck : ContDiffOn ℝ 1 (Function.uncurry k) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}))
    (cg : ContDiffOn ℝ 1 g (Icc a c))
    (hg : ∀ t ∈ Icc a c, f t t = g t)
    (hd : ∀ u ∈ Icc a c, ∀ v ∈ Ioo u b, HasDerivAt (f u) (k u v • f u v + F u v) v) :
    ContDiffOn ℝ 1 (Function.uncurry f) (triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}) := by
  let D := triangle a b ∩ {p : ℝ × ℝ | p.1 ≤ c}
  let J (u v : ℝ) := ∫ s in u..v, k u s
  let H (u v : ℝ) := Real.exp (-J u v) • F u v
  let z (u v : ℝ) := Real.exp (J u v) • (g u + ∫ s in u..v, H u s)
  have cJ : ContDiffOn ℝ 1 (Function.uncurry J) D := contDiffOn_radial_primitive hac hcb ck
  have cH : ContDiffOn ℝ 1 (Function.uncurry H) D :=
    (Real.contDiff_exp.comp_contDiffOn cJ.neg).smul cF
  have cz : ContDiffOn ℝ 1 (Function.uncurry z) D :=
    (Real.contDiff_exp.comp_contDiffOn cJ).smul
      ((cg.comp contDiffOn_fst (fun p hp => ⟨hp.1.1, hp.2⟩)).add
        (contDiffOn_radial_primitive hac hcb cH))
  have heq : EqOn (Function.uncurry f) (Function.uncurry z) D := by
    intro p hp
    have hu : p.1 ∈ Icc a c := ⟨hp.1.1, hp.2⟩
    have hs : MapsTo (fun v => (p.1, v)) (Icc p.1 b) D :=
      fun v hv => ⟨⟨hp.1.1, hv.1, hv.2⟩, hp.2⟩
    have ck' := ck.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) hs
    have cH' := cH.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) hs
    have hz (v : ℝ) (hv : v ∈ Ioo p.1 b) :
        HasDerivAt (z p.1) (k p.1 v • z p.1 v + F p.1 v) v := by
      have hJ := (Recon.hasDerivWithinAt_primitive ck' ⟨hv.1.le, hv.2.le⟩).hasDerivAt
        (Icc_mem_nhds hv.1 hv.2)
      have hH := (Recon.hasDerivWithinAt_primitive cH' ⟨hv.1.le, hv.2.le⟩).hasDerivAt
        (Icc_mem_nhds hv.1 hv.2)
      have hz' := hJ.exp.smul ((hasDerivAt_const v (g p.1)).add hH)
      convert hz' using 1
      · funext x; rfl
      · dsimp only [J, H, z, Function.comp_apply, Function.uncurry, Pi.smul_apply,
          Pi.add_apply, id_eq]
        simp only [zero_add, smul_smul]
        rw [show Real.exp (∫ s in p.1..v, k p.1 s) *
          Real.exp (-(∫ s in p.1..v, k p.1 s)) = 1 by
            rw [← Real.exp_add, add_neg_cancel, Real.exp_zero], one_smul]
        rw [mul_comm (k p.1 v) (Real.exp (∫ s in p.1..v, k p.1 s))]
        abel
    have hz0 : f p.1 p.1 - z p.1 p.1 = 0 := by simp [z, J, hg p.1 hu]
    have hzero := eq_zero_of_homogeneous_transport_smul (hu.2.trans hcb)
      ((cf.sub cz.continuousOn).comp (continuousOn_const.prodMk continuousOn_id) hs) ck' hz0
      (fun v hv => by
        convert (hd p.1 hu v hv).sub (hz v hv) using 1
        · funext s; rfl
        · dsimp only [Function.comp_apply, Function.uncurry, Pi.sub_apply, id_eq]
          rw [smul_sub]
          abel) p.2 ⟨hp.1.2.1, hp.1.2.2⟩
    exact sub_eq_zero.mp hzero
  exact cz.congr heq

end EmcsfAcExtension.Local.Null
