module

public import EmcsfAcExtension.Local.Defs.Partial

/-! # First partial product rules used in C¹ system recovery

All derivatives are within the actual construction domain. Uniqueness of
the domain differential is stated explicitly and no exterior extension
of a field is involved.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local.Null

/-- A real field's incoming partial commutes with the inclusion into ℂ. -/
theorem pdU_ofReal {D : Set (ℝ × ℝ)} {f : ℝ → ℝ → ℝ}
    (hD : UniqueDiffOn ℝ D) (cf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    {u v : ℝ} (hp : (u, v) ∈ D) :
    pdU D (fun u v => (f u v : ℂ)) u v = (pdU (E := ℝ) D f u v : ℂ) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp_hasFDerivWithinAt (u, v)
    ((cf.differentiableOn (by norm_num) (u, v) hp).hasFDerivWithinAt)
  change fderivWithin ℝ (Complex.ofRealCLM ∘ Function.uncurry f) D (u, v) (1, 0) = _
  rw [hd.fderivWithin (hD (u, v) hp)]
  rfl

/-- The incoming partial of a product of two complex C¹ fields. -/
theorem pdU_mul {D : Set (ℝ × ℝ)} {f g : ℝ → ℝ → ℂ}
    (hD : UniqueDiffOn ℝ D) (cf : ContDiffOn ℝ 1 (Function.uncurry f) D)
    (cg : ContDiffOn ℝ 1 (Function.uncurry g) D)
    {u v : ℝ} (hp : (u, v) ∈ D) :
    pdU D (fun u v => f u v * g u v) u v =
      pdU D f u v * g u v + f u v * pdU D g u v := by
  change fderivWithin ℝ (fun p => Function.uncurry f p * Function.uncurry g p) D (u, v) (1, 0) = _
  rw [fderivWithin_fun_mul (hD (u, v) hp)
    (cf.differentiableOn (by norm_num) (u, v) hp)
    (cg.differentiableOn (by norm_num) (u, v) hp)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  dsimp only [pdU, Function.uncurry]
  ring

end EmcsfAcExtension.Local.Null
