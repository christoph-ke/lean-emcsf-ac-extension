module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Parameters for uniform first-jet comparison

The tolerance and entering datum are fixed before the old apex and both
states. Only the first derivative of the fixed datum enters its modulus.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- Choose the value tolerance and strip height before all old apexes
and states. `r` is the desired bound for each directional jet difference.
The three numeric inequalities control the characteristic components,
the incoming Volterra comparison, and the outgoing comparison. -/
theorem exists_uniform_jet_parameters {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T B C H J r : ℝ}
    (hT : 0 < T) (hB : 0 < B) (hC : 0 < C) (hH : 0 < H)
    (hJ : 0 < J) (hr : 0 < r) {yi : ℝ → E}
    (hyi : ContDiffOn ℝ 1 yi (Icc 0 T)) :
    ∃ ζ > 0, ∃ δ₀ > 0, ∃ ω > 0,
      J*ζ ≤ r ∧
      2*(ω+C*ζ*(B+H+C)*T)*Real.exp (2*(C+1)*T) ≤ r ∧
      2*C*(B+H)*δ₀*Real.exp (2*(C+1)*T) ≤ r ∧
      (∀ x ∈ Icc 0 T, ∀ y ∈ Icc 0 T, |x-y| ≤ δ₀ →
        ‖derivWithin yi (Icc 0 T) x-derivWithin yi (Icc 0 T) y‖ ≤ ω) := by
  let A := Real.exp (2*(C+1)*T)
  have hA : 0 < A := Real.exp_pos _
  have hA1 : 1 ≤ A := Real.one_le_exp (by positivity)
  let Q := C*(B+H+C)*T
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let R := C*(B+H)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let ω := r/(8*A)
  have hω : 0 < ω := by dsimp [ω]; positivity
  have hD : ContinuousOn (derivWithin yi (Icc 0 T)) (Icc 0 T) :=
    ((contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hT)).mp hyi).2
  obtain ⟨μ,hμ,hmod⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hD) ω hω
  let ζ := r/(8*A*(Q+J+1))
  let δ₀ := min μ (r/(4*A*(R+1)))
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hδ₀ : 0 < δ₀ := lt_min hμ (by positivity)
  have hζeq : 8*A*(Q+J+1)*ζ = r := by
    dsimp [ζ]
    exact mul_div_cancel₀ _ (by positivity)
  have hωeq : 8*A*ω = r := by
    dsimp [ω]
    exact mul_div_cancel₀ _ (by positivity)
  have hδle : 4*A*(R+1)*δ₀ ≤ r := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*A*(R+1))).mp
      (show δ₀ ≤ r/(4*A*(R+1)) from min_le_right _ _)
    simpa only [mul_comm] using hh
  have hJQ : J ≤ 8*A*(Q+J+1) := by nlinarith
  have hQle : 8*A*Q*ζ ≤ r := by
    have hh : Q ≤ Q+J+1 := by linarith
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 8*A)) hζ.le).trans_eq hζeq
  refine ⟨ζ,hζ,δ₀,hδ₀,ω,hω,?_,?_,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right hJQ hζ.le).trans_eq hζeq
  · change 2*(ω+C*ζ*(B+H+C)*T)*A ≤ r
    have heq : C*ζ*(B+H+C)*T = Q*ζ := by dsimp [Q]; ring
    rw [heq]
    nlinarith
  · change 2*C*(B+H)*δ₀*A ≤ r
    have heq : 2*C*(B+H)*δ₀*A = 2*R*δ₀*A := by dsimp [R]; ring
    rw [heq]
    nlinarith [mul_nonneg hδ₀.le hA.le]
  · intro x hx y hy hxy
    have := hmod x hx y hy (by simpa only [Real.dist_eq] using hxy.trans (min_le_left _ _))
    simpa only [dist_eq_norm] using this

end EmcsfAcExtension.Local
