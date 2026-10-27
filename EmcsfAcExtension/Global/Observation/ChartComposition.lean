module

public import EmcsfAcExtension.Global.Api.Definitions
import Mathlib

/-! # Composition of the two observation null charts

The inner label change acts on the already gauged outer fields. The
composition identity keeps the potential as the same pulled-back
covector, with no additional gauge transformation.
Source: charged_SF_new_version.tex:L2587–2608; approved internal project record (N0).
-/

public section

namespace EmcsfAcExtension.Global.Observation

/-- [internal]
Two C¹ null pullbacks compose as the literal composed null maps. The
identity includes the retained potential and both scalar densities.
No field regularity, equations, positivity or constants are required. -/
theorem nullPullback_comp_of_c1_maps (S : Fields) (F G U V : ℝ → ℝ)
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V) :
    nullPullback (nullPullback S F G) U V = nullPullback S (F ∘ U) (G ∘ V) := by
  have dFU (u : ℝ) : deriv (F ∘ U) u = deriv F (U u) * deriv U u :=
    (((hF.differentiable (by norm_num) (U u)).hasDerivAt).comp u
      (hU.differentiable (by norm_num) u).hasDerivAt).deriv
  have dGV (v : ℝ) : deriv (G ∘ V) v = deriv G (V v) * deriv V v :=
    (((hG.differentiable (by norm_num) (V v)).hasDerivAt).comp v
      (hV.differentiable (by norm_num) v).hasDerivAt).deriv
  simp only [nullPullback]
  congr 1 <;> funext u v <;> simp only [Function.comp_apply, dFU, dGV]
  all_goals (push_cast; ring)

end EmcsfAcExtension.Global.Observation
