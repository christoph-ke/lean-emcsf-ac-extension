module

public import EmcsfAcExtension.Local.Defs.Recon
public import EmcsfAcExtension.Local.Calculus.Partials

/-! # Continuity of the incoming defects from primary C¹ fields

The regular charge quotient and the nonzero incoming expansion give a C¹
incoming mass source. Keeping this calculation on abstract fields avoids
unfolding reconstruction integrals in the algebraic source identity.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Null

/-- Both incoming defects are continuous once the primary fields and the
regularized mass sources have the indicated C¹ regularity. The only
division hypothesis is the displayed nonzero incoming expansion. This is
an analytic helper: it assumes neither incoming constraint nor transport
of a defect, and it introduces no estimate constant. -/
theorem continuousOn_defects_of_c1_fields {D : Set (ℝ × ℝ)} {e : ℝ} {S : Fields}
    (hD : UniqueDiffOn ℝ D)
    (cr : ContDiffOn ℝ 1 (Function.uncurry S.r) D)
    (cp : ContDiffOn ℝ 1 (Function.uncurry S.phi) D)
    (cx : ContDiffOn ℝ 1 (Function.uncurry S.xi) D)
    (cQ : ContDiffOn ℝ 1 (Function.uncurry S.Q) D)
    (cm : ContDiffOn ℝ 1 (Function.uncurry S.m) D)
    (cμ : ContDiffOn ℝ 1 (Function.uncurry S.mu) D)
    (cn : ContDiffOn ℝ 1 (Function.uncurry S.nu) D)
    (cqR : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => S.Q p.1 p.2 ^ 2 / S.r p.1 p.2 ^ 2) D)
    (hn : ∀ p ∈ D, S.nu p.1 p.2 ≠ 0) :
    ContinuousOn (Function.uncurry (defectQ e D S)) D ∧
      ContinuousOn (Function.uncurry (defectM D S)) D := by
  have cQU : ContinuousOn (Function.uncurry (S.QU e)) D := by
    simpa only [Fields.QU, Function.uncurry_def, Function.comp_apply] using!
      ((continuousOn_const (c := e)).mul cr.continuousOn).mul
        (Complex.continuous_im.comp_continuousOn
          ((Complex.continuous_conj.comp_continuousOn cp.continuousOn).mul cx.continuousOn))
  have cMU : ContDiffOn ℝ 1 (Function.uncurry S.mU) D := by
    have cF := ((((contDiffOn_const (c := (1 : ℝ))).sub cμ).mul
      ((contDiff_norm_sq ℝ).comp_contDiffOn cx)).div
        ((contDiffOn_const (c := (2 : ℝ))).mul cn)
        (fun p hp => mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (hn p hp))).add
          ((cqR.mul cn).div_const 2)
    apply cF.congr
    intro p _
    dsimp only [Fields.mU, Function.uncurry_def, Function.comp_apply,
      Pi.mul_apply, Pi.div_apply, Pi.add_apply, Pi.sub_apply]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  exact ⟨(continuousOn_pdU cQ hD).sub cQU,
    (continuousOn_pdU cm hD).sub cMU.continuousOn⟩

end EmcsfAcExtension.Local.Null
