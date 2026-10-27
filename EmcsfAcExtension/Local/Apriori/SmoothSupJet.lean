module

public import EmcsfAcExtension.Local.Defs.C1Class
import EmcsfAcExtension.Local.Calculus.AxisContinuity

/-! # A uniform bound for the regular algebraic first-jet formulas

The inputs are numerical bounds for regularized center ratios, expansion
partials, and the potential partial. All radius divisions have already
been removed. Compactness here is on one fixed finite-dimensional ball
of numerical inputs, chosen before any solution or constructed apex.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- The eleven fields and their two partials as continuous formulas in
regular inputs. Real coordinates are `r,λ,ν,d,Q/r³,μ/r²,A,λu,λv,νu,νv,Au,
1/λ,1/ν,1/d`; complex coordinates are `φ,f/r,g/r,av,Du b`.
Outputs occur in triples `(value, incoming partial, outgoing partial)`
for `r,λ,ν,m,Q,A,φ,θ,ξ,a,b`, in that order. -/
@[expose] noncomputable def smoothJetFormula (e : ℝ)
    (x : (Fin 15 → ℝ) × (Fin 5 → ℂ)) : Fin 33 → ℂ :=
  let r := x.1 0
  let l := x.1 1
  let n := x.1 2
  let d := x.1 3
  let q := x.1 4
  let m := x.1 5
  let A := x.1 6
  let lu := x.1 7
  let lv := x.1 8
  let nu := x.1 9
  let nv := x.1 10
  let Au := x.1 11
  let li := x.1 12
  let ni := x.1 13
  let di := x.1 14
  let φ := x.2 0
  let f := x.2 1
  let g := x.2 2
  let av := x.2 3
  let Dub := x.2 4
  let a := φ + r * f
  let b := φ + r * g
  let θ := l * r * f
  let ξ := n * r * g
  let φu := n * g - I * e * A * φ
  let φv := l * f
  let bu := Dub - I * e * A * b
  ![(r : ℂ), n, l,
    l, lu, lv,
    n, nu, nv,
    m * r ^ 3 / 2, n / 2 * (d * r ^ 2 * ‖g‖ ^ 2 + q ^ 2 * r ^ 4),
      l / 2 * (d * r ^ 2 * ‖f‖ ^ 2 + q ^ 2 * r ^ 4),
    q * r ^ 3, e * n * r ^ 2 * (starRingEnd ℂ φ * g).im,
      -(e * l * r ^ 2 * (starRingEnd ℂ φ * f).im),
    A, Au, 2 * n * l * q * r * di,
    φ, φu, φv,
    θ, -(I * e * A * θ) - l * n * g - I * e * q * r ^ 2 * φ * n * l * di,
      lv * r * f + l * (av - φv),
    ξ, nu * r * g + n * (bu - φu),
      -(n * l * f) + I * e * q * r ^ 2 * φ * n * l * di,
    a, -(I * e * A * a) - lu * li * r * f - I * e * n * q * r ^ 2 * φ * di, av,
    b, bu, -(nv * ni * r * g) + I * e * l * q * r ^ 2 * φ * di]

/-- The regular jet formulas are continuous on their entire numerical
input space. Inverses of the three nondegenerate geometric quantities
are bounded inputs, so this assertion makes no nonvanishing assumption. -/
theorem continuous_smoothJetFormula (e : ℝ) : Continuous (smoothJetFormula e) := by
  apply continuous_pi
  intro i
  fin_cases i <;>
    dsimp only [smoothJetFormula, Matrix.cons_val_zero, Matrix.cons_val_succ] <;> fun_prop

/-- A single finite bound for every numerical first-jet formula is
chosen after `e,L` and before the inputs. This compactness argument is
on a fixed ball in the numerical input space, uniformly over all fields
and all constructed apices; it is not compactness of one solution. -/
theorem smooth_jet_formula_bound_aux (e L : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : (Fin 15 → ℝ) × (Fin 5 → ℂ), ‖x‖ ≤ L →
      ∀ i, ‖smoothJetFormula e x i‖ ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : (Fin 15 → ℝ) × (Fin 5 → ℂ)) L).bddAbove_image
     (continuous_smoothJetFormula e).norm.continuousOn
  refine ⟨1 + |C|, by positivity, ?_⟩
  intro x hx i
  have hx' : x ∈ Metric.closedBall (0 : (Fin 15 → ℝ) × (Fin 5 → ℂ)) L := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  exact (norm_le_pi_norm (smoothJetFormula e x) i).trans
    ((hC (mem_image_of_mem _ hx')).trans (by linarith only [le_abs_self C]))

/-- A norm bound proved off the axis extends to the closed triangle for
every continuous field. The constant is unchanged. Nondegeneracy `0<T`
is needed for density of the off-axis part. -/
theorem smooth_norm_bound_of_off_axis_aux {E : Type*} [NormedAddCommGroup E]
    {T B : ℝ} {f : ℝ × ℝ → E} (hT : 0 < T)
    (cf : ContinuousOn f (triangle 0 T))
    (hf : ∀ p ∈ triangle 0 T, p.1 < p.2 → ‖f p‖ ≤ B) :
    ∀ p ∈ triangle 0 T, ‖f p‖ ≤ B := by
  have he := eqOn_triangle_of_off_axis_aux hT (cf.norm.inf continuousOn_const) cf.norm
    (fun p hp huv => min_eq_left (hf p hp huv))
  intro p hp
  have hh := min_le_right ‖f p‖ B
  have he' : min ‖f p‖ B = ‖f p‖ := he hp
  rwa [he'] at hh

end EmcsfAcExtension.Local
