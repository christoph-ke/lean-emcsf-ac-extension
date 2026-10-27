module

public import EmcsfAcExtension.Local.Apriori.SmoothSupC1Regular
public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.SmoothSupJetBound
import EmcsfAcExtension.Local.Apriori.SmoothSupJet
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.Normalized
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Uniform bounds for both derivatives of the geometric coefficient

The compact set is a numerical input ball fixed before any solution or apex.
The actual coefficient is C¹ at the axis, so the off-axis estimates pass to
its actual first derivatives on the entire closed triangle.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

/-- The three geometric formulas have a finite common bound on a fixed
numerical ball. Its constant depends only on `e,L`, uniformly in all
inputs, solutions and apices. -/
theorem smooth_geom_jet_formula_bound_aux (e L : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : (Fin 15 → ℝ) × (Fin 5 → ℂ), ‖x‖ ≤ L →
      ∀ i, |smoothGeomJetFormula e x i| ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : (Fin 15 → ℝ) × (Fin 5 → ℂ)) L).bddAbove_image
    (continuous_smoothGeomJetFormula e).norm.continuousOn
  refine ⟨1 + |C|, by positivity, ?_⟩
  intro x hx i
  have hx' : x ∈ Metric.closedBall (0 : (Fin 15 → ℝ) × (Fin 5 → ℂ)) L := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  simpa only [Real.norm_eq_abs] using
    (norm_le_pi_norm (smoothGeomJetFormula e x) i).trans
      ((hC (mem_image_of_mem _ hx')).trans (by linarith only [le_abs_self C]))

/-- Uniform bounds for `G` and both of its actual closed-triangle partials.
The positive bound depends only on the displayed numerical budgets, before
`S,h,s,ε`. Both partials are continuous, by `smooth_geom_coeff_c1_aux`.
This is a conditional recovery helper, with the same budgets as the full
field-jet recovery; no second derivative is supplied as an input. -/
theorem smooth_geom_coeff_bound_of_bounds (e R M D G H P Q U : ℝ)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hD : 0 ≤ D) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hU : 0 ≤ U) :
    ∃ B : ℝ, 0 < B ∧ ∀ (s ε : ℝ) (S : Fields) (h : ℝ → ℂ), s ≤ R →
      AprioriSetting e s ε M S h →
      (∀ q ∈ triangle 0 s,
        ‖pdV (triangle 0 s) S.a q.1 q.2‖ ≤ D ∧
        ‖pdU (triangle 0 s) S.b q.1 q.2 + I * e * S.A q.1 q.2 * S.b q.1 q.2‖ ≤ D ∧
        ‖S.theta q.1 q.2 / S.lam q.1 q.2‖ ≤ D * S.r q.1 q.2 ∧
        ‖S.xi q.1 q.2 / S.nu q.1 q.2‖ ≤ D * S.r q.1 q.2) →
      (∀ q ∈ triangle 0 s,
        |pdU (triangle 0 s) S.lam q.1 q.2| ≤ G ∧
        |pdV (triangle 0 s) S.lam q.1 q.2| ≤ G ∧
        |pdU (triangle 0 s) S.nu q.1 q.2| ≤ G ∧
        |pdV (triangle 0 s) S.nu q.1 q.2| ≤ G) →
      (∀ q ∈ triangle 0 s, |S.A q.1 q.2| ≤ P ∧
        |pdU (triangle 0 s) S.A q.1 q.2| ≤ H) →
      (∀ q ∈ triangle 0 s, |S.Q q.1 q.2| ≤ Q * S.r q.1 q.2 ^ 3 ∧
        S.mu q.1 q.2 ≤ U * S.r q.1 q.2 ^ 2) →
      ∀ q ∈ triangle 0 s,
        |smoothGeomCoeff S q.1 q.2| ≤ B ∧
        |pdU (triangle 0 s) (smoothGeomCoeff S) q.1 q.2| ≤ B ∧
        |pdV (triangle 0 s) (smoothGeomCoeff S) q.1 q.2| ≤ B := by
  let L := 1 + R + M + D + G + H + P + Q + U + 4
  obtain ⟨B, hB, hb⟩ := smooth_geom_jet_formula_bound_aux e L
  refine ⟨B, hB, ?_⟩
  intro s ε S h hsR hset hscalar hexp hpot hcenter
  have hc := smooth_geom_coeff_c1_aux hset.pos hset.c1
  have hcoord (i : Fin 3) (q : ℝ × ℝ) (hq : q ∈ triangle 0 s) (huv : q.1 < q.2) :
      |smoothGeomJetFormula e (smoothJetInput e s S q.1 q.2) i| ≤ B :=
    hb _ (smooth_jet_input_bound_of_bounds hset hsR hR hM hD hG hH hP hQ hU
      rfl hq huv (hscalar q hq) (hexp q hq) (hpot q hq) (hcenter q hq)) i
  have hu (q : ℝ × ℝ) (hq : q ∈ triangle 0 s) (huv : q.1 < q.2) :
      pdU (triangle 0 s) (smoothGeomCoeff S) q.1 q.2 =
        smoothGeomJetFormula e (smoothJetInput e s S q.1 q.2) 1 :=
    (uniqueDiffOn_Icc (hq.1.trans_lt huv) q.1 ⟨hq.1, huv.le⟩).eq_deriv _
      (hasDerivWithinAt_u_aux hc hq.1 huv.le hq.2.2)
      (smooth_geom_coeff_deriv_u_aux hset.c1 hq.1 huv hq.2.2)
  have hv (q : ℝ × ℝ) (hq : q ∈ triangle 0 s) (huv : q.1 < q.2) :
      pdV (triangle 0 s) (smoothGeomCoeff S) q.1 q.2 =
        smoothGeomJetFormula e (smoothJetInput e s S q.1 q.2) 2 :=
    (uniqueDiffOn_Icc (huv.trans_le hq.2.2) q.2 ⟨huv.le, hq.2.2⟩).eq_deriv _
      (hasDerivWithinAt_v_aux hc hq.1 huv.le hq.2.2)
      (smooth_geom_coeff_deriv_v_aux hset.c1 hq.1 huv hq.2.2)
  have hwhole {f : ℝ → ℝ → ℝ} (cf : ContinuousOn (Function.uncurry f) (triangle 0 s))
      (hf : ∀ q ∈ triangle 0 s, q.1 < q.2 → |f q.1 q.2| ≤ B) :
      ∀ q ∈ triangle 0 s, |f q.1 q.2| ≤ B := by
    simpa only [Real.norm_eq_abs, Function.uncurry_def] using
      smooth_norm_bound_of_off_axis_aux hset.pos cf
        (fun q hq huv => by
          simpa only [Real.norm_eq_abs, Function.uncurry_def] using hf q hq huv)
  have hb0 := hwhole hc.continuousOn (fun q hq huv => by
    rw [← smooth_geom_jet_value_aux hset.c1 hq huv]
    exact hcoord 0 q hq huv)
  have hbu := hwhole (continuousOn_pdU hc (uniqueDiffOn_triangle hset.pos))
    (fun q hq huv => by rw [hu q hq huv]; exact hcoord 1 q hq huv)
  have hbv := hwhole (continuousOn_pdV hc (uniqueDiffOn_triangle hset.pos))
    (fun q hq huv => by rw [hv q hq huv]; exact hcoord 2 q hq huv)
  exact fun q hq => ⟨hb0 q hq, hbu q hq, hbv q hq⟩

end EmcsfAcExtension.Local
