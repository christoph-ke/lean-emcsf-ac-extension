module

public import EmcsfAcExtension.Local.Defs.C1Class
import EmcsfAcExtension.Infra.Calculus.PartialsC1

/-! # Continuous extension of nonsingular equations to the regular axis

Only equations whose right sides are continuous on the full closed triangle
are extended here. Singular source terms are treated separately by axis factors.
-/

public section

open Set Complex

namespace EmcsfAcExtension.Local

private theorem off_axis_of_mem_interior_aux {T : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ interior (triangle 0 T)) : p.1 < p.2 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  have hdist : dist (p.1, p.2 - ε / 2) p < ε := by
    simp only [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero, sub_sub_cancel_left,
      abs_neg]
    rw [abs_of_pos (half_pos hε), max_eq_right (half_pos hε).le]
    exact half_lt_self hε
  have h := hball hdist
  change 0 ≤ p.1 ∧ p.1 ≤ p.2 - ε / 2 ∧ p.2 - ε / 2 ≤ T at h
  exact lt_of_le_of_lt h.2.1 (sub_lt_self _ (half_pos hε))

/-- Two continuous fields agreeing off the axis agree on the full nondegenerate
triangle. This helper supplies the closed-domain extension of regular equations. -/
theorem eqOn_triangle_of_off_axis_aux {E : Type*} [TopologicalSpace E] [T2Space E]
    {T : ℝ} {f g : (ℝ × ℝ) → E} (hT : 0 < T)
    (hf : ContinuousOn f (triangle 0 T)) (hg : ContinuousOn g (triangle 0 T))
    (heq : ∀ p ∈ triangle 0 T, p.1 < p.2 → f p = g p) :
    EqOn f g (triangle 0 T) := by
  apply Set.EqOn.of_subset_closure (s := interior (triangle 0 T))
    (fun p hp => heq p (interior_subset hp) (off_axis_of_mem_interior_aux hp)) hf hg
    interior_subset
  rw [closure_interior_triangle hT]

/-- The radius equations extend to the axis because both expansions and the
canonical radius partials are continuous. No axis gauge is used. -/
theorem radius_axis_partials_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    pdU (triangle 0 T) S.r t t = S.nu t t ∧
      pdV (triangle 0 T) S.r t t = S.lam t t := by
  have hp : (t, t) ∈ triangle 0 T := ⟨ht.1, le_rfl, ht.2⟩
  exact ⟨eqOn_triangle_of_off_axis_aux hT
      (continuousOn_partial_u hS.c1_r (uniqueDiffOn_triangle hT)) hS.c1_nu.continuousOn
      (fun p hp huv => (hS.eq_u p hp huv).1) hp,
    eqOn_triangle_of_off_axis_aux hT
      (continuousOn_partial_v hS.c1_r (uniqueDiffOn_triangle hT)) hS.c1_lam.continuousOn
      (fun p hp huv => (hS.eq_v p hp huv).1) hp⟩

/-- Both Maxwell partials vanish on the regular axis. Their polynomial right
sides extend continuously, and the radius itself vanishes there. -/
theorem charge_axis_partials_aux {e T : ℝ} {S : Fields} (hT : 0 < T)
    (hS : IsC1Solution e S (triangle 0 T)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    pdU (triangle 0 T) S.Q t t = 0 ∧ pdV (triangle 0 T) S.Q t t = 0 := by
  have hp : (t, t) ∈ triangle 0 T := ⟨ht.1, le_rfl, ht.2⟩
  have hc := (Complex.continuous_im.comp_continuousOn
    (hS.c1_phi.continuousOn.star.mul hS.c1_xi.continuousOn))
  have hc' := (Complex.continuous_im.comp_continuousOn
    (hS.c1_phi.continuousOn.star.mul hS.c1_theta.continuousOn))
  have hu := eqOn_triangle_of_off_axis_aux hT
    (continuousOn_partial_u hS.c1_Q (uniqueDiffOn_triangle hT))
    ((continuousOn_const.mul hS.c1_r.continuousOn).mul hc)
    (fun p hp huv => (hS.eq_u p hp huv).2.2.2.1) hp
  have hv := eqOn_triangle_of_off_axis_aux hT
    (continuousOn_partial_v hS.c1_Q (uniqueDiffOn_triangle hT))
    (((continuousOn_const.mul hS.c1_r.continuousOn).mul hc').neg)
    (fun p hp huv => (hS.eq_v p hp huv).2.2.2.1) hp
  exact ⟨by simpa [pdU, (hS.axis t hp).1] using hu,
    by simpa [pdV, (hS.axis t hp).1] using hv⟩

end EmcsfAcExtension.Local
