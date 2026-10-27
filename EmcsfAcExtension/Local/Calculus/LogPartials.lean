module

public import EmcsfAcExtension.Local.Defs.Partial
public import EmcsfAcExtension.Frozen.Triangle
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Canonical logarithmic partials and complex norm squares

The logarithmic chain rule uses uniqueness of the full triangle differential,
so it remains valid at the terminal vertex where an individual section degenerates.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- Incoming logarithmic chain rule for the canonical domain partial, including
all three edges and all vertices of a positive-time triangle. -/
theorem pdU_log_aux {T : ℝ} {f : ℝ → ℝ → ℝ} (hT : 0 < T)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) (hne : f u v ≠ 0) :
    pdU (triangle 0 T) (fun x y => Real.log (f x y)) u v =
      pdU (triangle 0 T) f u v / f u v := by
  have hd := ((hf.differentiableOn (by norm_num) _ hp).hasFDerivWithinAt.log hne).fderivWithin
    (uniqueDiffOn_triangle hT _ hp)
  change (fderivWithin ℝ (fun p : ℝ × ℝ => Real.log (f p.1 p.2))
    (triangle 0 T) (u, v)) (1, 0) = _
  simp only [Function.uncurry_def] at hd
  rw [hd]
  simp only [smul_apply, smul_eq_mul, pdU, Function.uncurry_def, div_eq_mul_inv]
  ring

/-- Outgoing logarithmic chain rule for the canonical domain partial, including
the terminal vertex where its outgoing section is a singleton. -/
theorem pdV_log_aux {T : ℝ} {f : ℝ → ℝ → ℝ} (hT : 0 < T)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (triangle 0 T))
    {u v : ℝ} (hp : (u, v) ∈ triangle 0 T) (hne : f u v ≠ 0) :
    pdV (triangle 0 T) (fun x y => Real.log (f x y)) u v =
      pdV (triangle 0 T) f u v / f u v := by
  have hd := ((hf.differentiableOn (by norm_num) _ hp).hasFDerivWithinAt.log hne).fderivWithin
    (uniqueDiffOn_triangle hT _ hp)
  change (fderivWithin ℝ (fun p : ℝ × ℝ => Real.log (f p.1 p.2))
    (triangle 0 T) (u, v)) (0, 1) = _
  simp only [Function.uncurry_def] at hd
  rw [hd]
  simp only [smul_apply, smul_eq_mul, pdV, Function.uncurry_def, div_eq_mul_inv]
  ring

/-- A complex field's norm square has derivative `2 Re(conj f · f')` along a
real section. This supplies the real quadratic corrections without differentiating
an absolute value at zero. -/
theorem hasDerivWithinAt_norm_sq_complex_aux {f : ℝ → ℂ} {f' : ℂ}
    {s : Set ℝ} {x : ℝ} (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (fun t => ‖f t‖ ^ 2)
      (2 * (starRingEnd ℂ (f x) * f').re) s x := by
  apply hf.norm_sq.congr_deriv
  rw [Complex.inner, mul_comm f' (starRingEnd ℂ (f x))]

end EmcsfAcExtension.Local
