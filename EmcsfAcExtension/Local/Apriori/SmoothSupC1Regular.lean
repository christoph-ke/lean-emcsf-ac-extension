module

public import EmcsfAcExtension.Local.Apriori.SmoothSupC1Coefficient
import EmcsfAcExtension.Local.Calculus.AxisRates
import EmcsfAcExtension.Local.Calculus.AxisScalarFields
import EmcsfAcExtension.Local.Calculus.AxisRatio
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Local.Calculus.OffAxisMixed
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # Continuous geometric jets at a C¹ center

Cubic mass and charge factors and the natural scalar constraints supply
continuous regular inputs. The formulas therefore extend both derivatives
of the logarithmic expansion coefficient to the entire closed triangle.
-/

public section

open Set Complex Filter
open scoped Topology

namespace EmcsfAcExtension.Local

/-- The value component of the regular formula is the literal coefficient
at positive radius. This algebraic identity has no estimate constants. -/
theorem smooth_geom_jet_value_aux {e T : ℝ} {S : Fields}
    (hS : IsC1Solution e S (triangle 0 T)) {u v : ℝ}
    (hp : (u, v) ∈ triangle 0 T) (huv : u < v) :
    smoothGeomJetFormula e (smoothJetInput e T S u v) 0 = smoothGeomCoeff S u v := by
  change S.nu u v * S.r u v *
    (S.mu u v / S.r u v ^ 2 - (S.Q u v / S.r u v ^ 3) ^ 2 * S.r u v ^ 2) *
      (1 - S.mu u v)⁻¹ = _
  dsimp only [smoothGeomCoeff]
  field_simp [(hS.r_pos _ hp huv).ne', (hS.one_sub_mu_pos _ hp).ne']

/-- The three geometric jet formulas have a continuous extension to the
closed triangle for every C¹ solution. The value extension is exactly `G`,
including its totalized axis value. No per-solution bound is selected. -/
theorem exists_continuous_smooth_geom_jet_aux {e T : ℝ} {S : Fields}
    (hT : 0 < T) (hS : IsC1Solution e S (triangle 0 T)) :
    ∃ F : (ℝ × ℝ) → Fin 3 → ℝ, ContinuousOn F (triangle 0 T) ∧
      (∀ p ∈ triangle 0 T, p.1 < p.2 →
        F p = smoothGeomJetFormula e (smoothJetInput e T S p.1 p.2)) ∧
      (∀ p ∈ triangle 0 T, F p 0 = smoothGeomCoeff S p.1 p.2) := by
  obtain ⟨R, cR, hRp, hR, _⟩ := exists_positive_radius_factor_aux hT hS
  obtain ⟨q, cq, hq⟩ := exists_continuous_charge_cubic_factor_aux hT hS
  obtain ⟨m, cm, hm⟩ := exists_continuous_mass_cubic_factor_aux hT hS
  let qr (p : ℝ × ℝ) := q p / R p ^ 3
  let mr (p : ℝ × ℝ) := 2 * m p / R p ^ 3
  have cqr : ContinuousOn qr (triangle 0 T) :=
    cq.div (cR.pow 3) (fun p hp => pow_ne_zero 3 (hRp p hp).ne')
  have cmr : ContinuousOn mr (triangle 0 T) :=
    (continuousOn_const.mul cm).div (cR.pow 3) (fun p hp => pow_ne_zero 3 (hRp p hp).ne')
  have hqr (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) (huv : p.1 < p.2) :
      qr p = S.Q p.1 p.2 / S.r p.1 p.2 ^ 3 := by
    rw [hq p.1 p.2 hp, hR p.1 p.2 hp]
    dsimp only [qr]
    field_simp [(sub_pos.mpr huv).ne', (hRp p hp).ne']
  have hmr (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) (huv : p.1 < p.2) :
      mr p = S.mu p.1 p.2 / S.r p.1 p.2 ^ 2 := by
    dsimp only [Fields.mu]
    rw [hm p.1 p.2 hp, hR p.1 p.2 hp]
    dsimp only [mr]
    field_simp [(sub_pos.mpr huv).ne', (hRp p hp).ne']
  let f (p : ℝ × ℝ) := pdV (triangle 0 T) S.phi p.1 p.2 / S.lam p.1 p.2
  let g (p : ℝ × ℝ) := (pdU (triangle 0 T) S.phi p.1 p.2 +
    I * e * S.A p.1 p.2 * S.phi p.1 p.2) / S.nu p.1 p.2
  have cf : ContinuousOn f (triangle 0 T) :=
    (continuousOn_pdV hS.c1_phi (uniqueDiffOn_triangle hT)).div
      (continuous_ofReal.comp_continuousOn hS.c1_lam.continuousOn)
      (fun p hp => ofReal_ne_zero.mpr (hS.lam_pos p hp).ne')
  have cg : ContinuousOn g (triangle 0 T) :=
    ((continuousOn_pdU hS.c1_phi (uniqueDiffOn_triangle hT)).add
      ((continuousOn_const.mul
        (continuous_ofReal.comp_continuousOn hS.c1_A.continuousOn)).mul
        hS.c1_phi.continuousOn)).div
      (continuous_ofReal.comp_continuousOn hS.c1_nu.continuousOn)
      (fun p hp => ofReal_ne_zero.mpr (hS.nu_neg p hp).ne)
  have hf (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) (huv : p.1 < p.2) :
      f p = S.theta p.1 p.2 / S.lam p.1 p.2 / S.r p.1 p.2 := by
    rw [theta_eq_radius_partial_aux hT hS hp]
    dsimp only [f]
    field_simp [ofReal_ne_zero.mpr (hS.r_pos p hp huv).ne',
      ofReal_ne_zero.mpr (hS.lam_pos p hp).ne']
  have hg (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) (huv : p.1 < p.2) :
      g p = S.xi p.1 p.2 / S.nu p.1 p.2 / S.r p.1 p.2 := by
    rw [xi_eq_radius_covariant_partial_aux hT hS hp]
    dsimp only [g]
    field_simp [ofReal_ne_zero.mpr (hS.r_pos p hp huv).ne',
      ofReal_ne_zero.mpr (hS.nu_neg p hp).ne]
  let X (p : ℝ × ℝ) : (Fin 15 → ℝ) × (Fin 5 → ℂ) :=
    (![S.r p.1 p.2, S.lam p.1 p.2, S.nu p.1 p.2, 1 - S.mu p.1 p.2,
        qr p, mr p, 0, 0, 0, pdU (triangle 0 T) S.nu p.1 p.2,
        pdV (triangle 0 T) S.nu p.1 p.2, 0, 0, 0, (1 - S.mu p.1 p.2)⁻¹],
      ![S.phi p.1 p.2, f p, g p, 0, 0])
  have cr := hS.c1_r.continuousOn
  have cl := hS.c1_lam.continuousOn
  have cn := hS.c1_nu.continuousOn
  have cμ := continuousOn_mu_aux hT hS
  have cnu := continuousOn_pdU hS.c1_nu (uniqueDiffOn_triangle hT)
  have cnv := continuousOn_pdV hS.c1_nu (uniqueDiffOn_triangle hT)
  have cdi := (continuousOn_const.sub cμ).inv₀ (fun p hp => (hS.one_sub_mu_pos p hp).ne')
  have cp := hS.c1_phi.continuousOn
  have cX : ContinuousOn X (triangle 0 T) := by
    apply ContinuousOn.prodMk
    · apply continuousOn_pi.mpr
      intro i
      fin_cases i <;> dsimp [X]
      all_goals first | exact cdi | fun_prop
    · apply continuousOn_pi.mpr
      intro i
      fin_cases i <;> dsimp [X] <;> fun_prop
  let F (p : ℝ × ℝ) := smoothGeomJetFormula e (X p)
  have cF : ContinuousOn F (triangle 0 T) :=
    (continuous_smoothGeomJetFormula e).comp_continuousOn cX
  have hF (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) (huv : p.1 < p.2) :
      F p = smoothGeomJetFormula e (smoothJetInput e T S p.1 p.2) := by
    funext i
    fin_cases i <;>
      simp [F, smoothGeomJetFormula, X, smoothJetInput,
        Matrix.cons_val_zero, hqr p hp huv, hmr p hp huv,
        hf p hp huv, hg p hp huv]
  refine ⟨F, cF, hF, ?_⟩
  intro p hp
  rcases hp.2.1.eq_or_lt with heq | huv
  · rcases p with ⟨u, v⟩
    dsimp only at heq
    subst v
    have hr := (hS.axis u hp).1
    simp only [F, smoothGeomJetFormula, X, smoothGeomCoeff,
      Matrix.cons_val_zero, hr, mul_zero, zero_mul, div_zero]
  · rw [hF p hp huv]
    exact smooth_geom_jet_value_aux hS hp huv

private theorem interior_triangle_off {T : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ interior (triangle 0 T)) : p.1 < p.2 := by
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hp)
  have hd : dist (p.1, p.2 - ε / 2) p < ε := by
    simp only [Prod.dist_eq, Real.dist_eq, sub_self, abs_zero, sub_sub_cancel_left, abs_neg]
    rw [abs_of_pos (half_pos hε), max_eq_right (half_pos hε).le]
    exact half_lt_self hε
  have hh := (hb hd).2.1
  exact lt_of_le_of_lt hh (sub_lt_self _ (half_pos hε))

/-- The literal geometric coefficient is C¹ on the entire closed triangle
for a C¹ solution. The continuous cubic factors remove its axis singularity;
continuous limits of both derivatives give the actual within derivatives.
No size bound, higher regularity, or extra equation is assumed. -/
theorem smooth_geom_coeff_c1_aux {e T : ℝ} {S : Fields}
    (hT : 0 < T) (hS : IsC1Solution e S (triangle 0 T)) :
    ContDiffOn ℝ 1 (Function.uncurry (smoothGeomCoeff S)) (triangle 0 T) := by
  obtain ⟨F, cF, hF, hval⟩ := exists_continuous_smooth_geom_jet_aux hT hS
  let O := {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T}
  let L (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
    F p 1 • ContinuousLinearMap.fst ℝ ℝ ℝ + F p 2 • ContinuousLinearMap.snd ℝ ℝ ℝ
  have cL : ContinuousOn L (triangle 0 T) :=
    ((continuousOn_pi.mp cF 1).smul continuousOn_const).add
      ((continuousOn_pi.mp cF 2).smul continuousOn_const)
  have cg : ContinuousOn (Function.uncurry (smoothGeomCoeff S)) (triangle 0 T) :=
    (continuousOn_pi.mp cF 0).congr (fun p hp => (hval p hp).symm)
  have hdiff := smooth_geom_coeff_c1_off_aux hS
  have heq (p : ℝ × ℝ) (hp : p ∈ O) :
      fderivWithin ℝ (Function.uncurry (smoothGeomCoeff S)) O p = L p := by
    have hdu := (uniqueDiffOn_Icc (hp.1.trans_lt hp.2.1) p.1 ⟨hp.1, hp.2.1.le⟩).eq_deriv _
      (hasDerivWithinAt_off_triangle_u_aux hdiff hp.1 hp.2.1 hp.2.2)
      (smooth_geom_coeff_deriv_u_aux hS hp.1 hp.2.1 hp.2.2)
    have hdv := (uniqueDiffOn_Icc (hp.2.1.trans_le hp.2.2) p.2 ⟨hp.2.1.le, hp.2.2⟩).eq_deriv _
      (hasDerivWithinAt_off_triangle_v_aux hdiff hp.1 hp.2.1 hp.2.2)
      (smooth_geom_coeff_deriv_v_aux hS hp.1 hp.2.1 hp.2.2)
    rw [← hF p ⟨hp.1, hp.2.1.le, hp.2.2⟩ hp.2.1] at hdu hdv
    apply ContinuousLinearMap.ext
    intro x
    have hx : x = x.1 • ((1, 0) : ℝ × ℝ) + x.2 • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    conv_lhs => rw [hx, map_add, map_smul, map_smul]
    change x.1 * pdU O (smoothGeomCoeff S) p.1 p.2 +
      x.2 * pdV O (smoothGeomCoeff S) p.1 p.2 = _
    rw [hdu, hdv]
    change x.1 * F p 1 + x.2 * F p 2 = F p 1 * x.1 + F p 2 * x.2
    ring
  have hi : interior (triangle 0 T) ⊆ O := fun p hp =>
    ⟨(interior_subset hp).1, interior_triangle_off hp, (interior_subset hp).2.2⟩
  have heqi (p : ℝ × ℝ) (hp : p ∈ interior (triangle 0 T)) :
      fderiv ℝ (Function.uncurry (smoothGeomCoeff S)) p = L p := by
    rw [← fderivWithin_of_mem_nhds (s := O)
      (mem_of_superset (isOpen_interior.mem_nhds hp) hi)]
    exact heq p (hi hp)
  have hder (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) :
      HasFDerivWithinAt (Function.uncurry (smoothGeomCoeff S)) (L p) (triangle 0 T) p := by
    rw [← closure_interior_triangle hT]
    apply hasFDerivWithinAt_closure_of_tendsto_fderiv
      (hdiff.differentiableOn (by norm_num) |>.mono hi)
      (convex_triangle 0 T).interior isOpen_interior
    · intro y hy
      rw [closure_interior_triangle hT] at hy
      exact (cg y hy).mono interior_subset
    · apply ((cL p hp).mono interior_subset).congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (heqi y hy).symm
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (uniqueDiffOn_triangle hT)]
  exact ⟨by simp, L, contDiffOn_zero.mpr cL, hder⟩

end EmcsfAcExtension.Local
