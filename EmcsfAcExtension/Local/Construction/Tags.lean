module

public import EmcsfAcExtension.Local.Construction.ContinuationInputs
import EmcsfAcExtension.Local.Construction.Corner
import EmcsfAcExtension.Local.Construction.WireOriginal

/-! # Unconditional canonical-ball local fixed point

The landed original-cone Picard producer supplies the invariant complete
ball and its contractive literal update. The fixed point wrapper retains
exactly the source datum and quantitative smallness assumptions.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- [node restart-sec-independent-null-construction#smooth-local-solution]
The canonical-ball Banach fixed point, charged_SF_new_version.tex:L6064–L6086, with the
original Picard input discharged. The positive width depends on the fixed
`T,e,h` and its C¹ size; the smallness thresholds and background are literal
universal constants. No derivative supremum bound is added to the datum. -/
theorem Null.smooth_local_fixed_point
    {T e : ℝ} {h : ℝ → ℂ} (hT : 0 < T)
    (hh : ContDiffOn ℝ 1 h (Icc 0 T))
    (hε : datumVar h T ≤ 1 / 64) (hδ : |e| * datumM h T * T ≤ 1 / 16) :
    ∃ a : ℝ, 0 < a ∧ a ≤ T ∧
      ∃ _ball : ContinuationPicardBall e 0 a T (fun _ => 1/2) h
          (1/128) (1/2-1/128) (3/4),
      ∃ Z : ContinuationPair 0 a T,
        Z.IsFixedPoint e (fun _ => 1/2) h ∧ Z.InConeBall (fun _ => 1/2) h (1/128) ∧
        ∀ p ∈ continuationWedge 0 a T,
          1/2-1/128 ≤ Z.lam p.1 p.2 ∧ 3/4 ≤ 1-Recon.mu e Z.lam Z.hh p.1 p.2 :=
  smooth_local_fixedPoint_of_inputs continuation_original_picard_input hT hh hε hδ

end EmcsfAcExtension.Local
