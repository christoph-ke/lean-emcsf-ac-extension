module

public import EmcsfAcExtension.Global.Defs.Observation
import EmcsfAcExtension.Infra.ODE.Continuation

/-!
# Static reference ODE

The literal inverse-radius vector field of `charged_SF_new_version.tex:L2199–L2225`.
The independent variable is adjoined to the state to express the nondegenerate
domain as an open state set. Existence is proved before any trajectory is used.
These radial references carry no regular-center `IsSolution` assertion.
-/

public section

open Set Metric Filter Topology
open scoped NNReal

namespace EmcsfAcExtension.Global

local notation "State" => (ℝ × ℝ × ℝ × ℂ)

/-- [internal]
The augmented static field is smooth wherever expansion and gap are nonzero.
The scalar parameters are fixed; this assertion has no quantitative constants. -/
theorem static_inv_radius_contDiffAt (P : ℂ) (q : ℝ) (w : State)
    (hlam : w.2.2.1 ≠ 0) (hg : 1 - 2 * w.1 * w.2.1 ≠ 0) :
    ContDiffAt ℝ 1
      (fun v : State => ((1 : ℝ), staticInvRadiusRHS P q v.1 v.2)) w := by
  unfold staticInvRadiusRHS
  have hc : ((2 * w.2.2.1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hlam)
  have hd : 8 * w.2.2.1 ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hlam)
  have hl : ContDiffAt ℝ 1 (fun v : State => v.2.2.1) w := by fun_prop
  have hgap : ContDiffAt ℝ 1 (fun v : State => 1 - 2 * v.1 * v.2.1) w := by
    fun_prop
  have hreal : ContDiffAt ℝ 1 (fun v : State => (2 : ℝ) * v.2.2.1) w :=
    contDiffAt_const.mul hl
  have hcast : ContDiffAt ℝ 1 (fun v : State => ((2 * v.2.2.1 : ℝ) : ℂ)) w := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using!
      Complex.ofRealCLM.contDiff.contDiffAt.comp w hreal
  have hphi : ContDiffAt ℝ 1 (fun v : State => P / ((2 * v.2.2.1 : ℝ) : ℂ)) w := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using!
      (contDiffAt_const (c := P) (𝕜 := ℝ)).mul (hcast.inv hc)
  exact contDiffAt_const.prodMk
    ((((hgap.neg.mul contDiffAt_const).div (contDiffAt_const.mul (hl.pow 2)) hd).sub
      contDiffAt_const).prodMk
        (((hl.neg.mul (by fun_prop)).div hgap hg).prodMk
          hphi))

/-- [internal]
Joint smoothness in the scalar amplitude, electric charge, and augmented state.
In particular, dependence on the complex phase is included at amplitude zero. -/
theorem static_inv_radius_joint_contDiffAt (p : ℂ × ℝ) (w : State)
    (hlam : w.2.2.1 ≠ 0) (hg : 1 - 2 * w.1 * w.2.1 ≠ 0) :
    ContDiffAt ℝ 1
      (fun v : (ℂ × ℝ) × State =>
        ((1 : ℝ), staticInvRadiusRHS v.1.1 v.1.2 v.2.1 v.2.2)) (p, w) := by
  unfold staticInvRadiusRHS
  have hc : ((2 * w.2.2.1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hlam)
  have hd : 8 * w.2.2.1 ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hlam)
  have hl : ContDiffAt ℝ 1 (fun v : (ℂ × ℝ) × State => v.2.2.2.1) (p, w) := by
    fun_prop
  have hgap : ContDiffAt ℝ 1
      (fun v : (ℂ × ℝ) × State => 1 - 2 * v.2.1 * v.2.2.1) (p, w) := by
    fun_prop
  have hn : ContDiffAt ℝ 1 (fun v : (ℂ × ℝ) × State => ‖v.1.1‖ ^ 2) (p, w) :=
    (contDiff_norm_sq ℂ).contDiffAt.comp (p, w) contDiffAt_fst.fst
  have hreal : ContDiffAt ℝ 1
      (fun v : (ℂ × ℝ) × State => (2 : ℝ) * v.2.2.2.1) (p, w) :=
    contDiffAt_const.mul hl
  have hcast : ContDiffAt ℝ 1
      (fun v : (ℂ × ℝ) × State => ((2 * v.2.2.2.1 : ℝ) : ℂ)) (p, w) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using!
      Complex.ofRealCLM.contDiff.contDiffAt.comp (p, w) hreal
  have hphi : ContDiffAt ℝ 1
      (fun v : (ℂ × ℝ) × State => v.1.1 / ((2 * v.2.2.2.1 : ℝ) : ℂ)) (p, w) := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using!
      ((contDiffAt_fst (𝕜 := ℝ) (p := (p, w))).fst).mul (hcast.inv hc)
  exact contDiffAt_const.prodMk
    ((((hgap.neg.mul hn).div (contDiffAt_const.mul (hl.pow 2)) hd).sub
      (by fun_prop)).prodMk
        (((hl.neg.mul (by fun_prop)).div hgap hg).prodMk
          hphi))

/-- [internal]
State Lipschitz bounds locally uniform in both reference parameters. The radius
and Lipschitz bound may depend on the displayed parameter and state centers.
They are uniform over the returned parameter neighborhood. -/
theorem static_inv_radius_local_lipschitz (p : ℂ × ℝ) (w : State)
    (hlam : 0 < w.2.2.1) (hg : 0 < 1 - 2 * w.1 * w.2.1) :
    ∃ (V : Set (ℂ × ℝ)) (r : ℝ) (K : ℝ≥0),
      IsOpen V ∧ p ∈ V ∧ 0 < r ∧ ∀ q ∈ V,
        LipschitzOnWith K
          (fun v : State => ((1 : ℝ), staticInvRadiusRHS q.1 q.2 v.1 v.2))
          (closedBall w r) := by
  obtain ⟨K, O, hO, hK⟩ := (static_inv_radius_joint_contDiffAt p w
    (ne_of_gt hlam) (ne_of_gt hg)).exists_lipschitzOnWith
  obtain ⟨d, hd, hdO⟩ := Metric.mem_nhds_iff.mp hO
  have hmem {q : ℂ × ℝ} (hq : q ∈ ball p (d / 2)) {v : State}
      (hv : v ∈ closedBall w (d / 2)) : (q, v) ∈ O := by
    apply hdO
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨(mem_ball.mp hq).trans (half_lt_self hd),
      (mem_closedBall.mp hv).trans_lt (half_lt_self hd)⟩
  refine ⟨ball p (d / 2), d / 2, K, isOpen_ball,
    mem_ball_self (half_pos hd), half_pos hd, fun q hq => ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv z hz
  have hdist : dist (q, v) (q, z) = dist v z := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
  simpa only [hdist] using
    hK.dist_le_mul (q, v) (hmem hq hv) (q, z) (hmem hq hz)

private theorem state_domain_open :
    IsOpen {w : State | 0 < w.2.2.1 ∧ 0 < 1 - 2 * w.1 * w.2.1} := by
  exact (isOpen_lt continuous_const continuous_snd.snd.fst).inter
    (isOpen_lt continuous_const
      (show Continuous (fun w : State => 1 - 2 * w.1 * w.2.1) by fun_prop))

private theorem field_continuous (P : ℂ) (q : ℝ) :
    ContinuousOn
      (fun w : ℝ × State => ((1 : ℝ), staticInvRadiusRHS P q w.2.1 w.2.2))
      (univ ×ˢ {w : State | 0 < w.2.2.1 ∧ 0 < 1 - 2 * w.1 * w.2.1}) := by
  intro w hw
  exact ((static_inv_radius_contDiffAt P q w.2
    (ne_of_gt hw.2.1) (ne_of_gt hw.2.2)).continuousAt.comp
      continuous_snd.continuousAt).continuousWithinAt

private theorem field_local_lipschitz (P : ℂ) (q : ℝ) (t : ℝ)
    (w : State) (hw : 0 < w.2.2.1 ∧ 0 < 1 - 2 * w.1 * w.2.1) :
    ∃ (r δ : ℝ) (K : ℝ≥0), 0 < r ∧ 0 < δ ∧
      ∀ s ∈ Icc (t - δ) (t + δ),
        LipschitzOnWith K
          (fun v : State => ((1 : ℝ), staticInvRadiusRHS P q v.1 v.2))
          (closedBall w r) := by
  obtain ⟨K, V, hV, hK⟩ := (static_inv_radius_contDiffAt P q w
    (ne_of_gt hw.1) (ne_of_gt hw.2)).exists_lipschitzOnWith
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r / 2, 1, K, half_pos hr, zero_lt_one, fun _ _ => hK.mono ?_⟩
  exact (closedBall_subset_ball (half_lt_self hr)).trans hrV

/-- [internal]
Existence and uniqueness of a maximal nondegenerate inverse-radius reference,
including initial inverse radius zero. The parameters and initial data are
arbitrary except for positive initial expansion and gap. No solution is selected
in this statement, and no constant depends on actual spacetime solution data. -/
theorem static_inv_radius_exists_maximal (P : ℂ) (q x₀ m₀ lam₀ : ℝ) (φ₀ : ℂ)
    (hlam : 0 < lam₀) (hg : 0 < 1 - 2 * x₀ * m₀) :
    ∃ (D : Set ℝ) (w : ℝ → State),
      IsOpen D ∧ OrdConnected D ∧ x₀ ∈ D ∧ w x₀ = (x₀, m₀, lam₀, φ₀) ∧
      (∀ x ∈ D, HasDerivAt w ((1 : ℝ), staticInvRadiusRHS P q (w x).1 (w x).2) x) ∧
      (∀ x ∈ D, 0 < (w x).2.2.1 ∧ 0 < 1 - 2 * (w x).1 * (w x).2.1) ∧
      ∀ (D' : Set ℝ) (v : ℝ → State), IsOpen D' → OrdConnected D' → x₀ ∈ D' →
        v x₀ = (x₀, m₀, lam₀, φ₀) →
        (∀ x ∈ D', HasDerivAt v ((1 : ℝ), staticInvRadiusRHS P q (v x).1 (v x).2) x) →
        (∀ x ∈ D', 0 < (v x).2.2.1 ∧ 0 < 1 - 2 * (v x).1 * (v x).2.1) →
        D' ⊆ D ∧ EqOn v w D' := by
  exact ODE.exists_maximal_solution
    (f := fun _ v => ((1 : ℝ), staticInvRadiusRHS P q v.1 v.2))
    state_domain_open (field_continuous P q)
    (field_local_lipschitz P q) x₀ (x₀, m₀, lam₀, φ₀) ⟨hlam, hg⟩

/-- [internal]
Project the augmented existence theorem to the literal inverse-radius ODE.
The starting inverse radius may be zero. The maximality and uniqueness clauses
retain both positive expansion and positive gap. -/
theorem static_inv_radius_exists (P : ℂ) (q x₀ m₀ lam₀ : ℝ) (φ₀ : ℂ)
    (hlam : 0 < lam₀) (hg : 0 < 1 - 2 * x₀ * m₀) :
    ∃ (D : Set ℝ) (z : ℝ → ℝ × ℝ × ℂ),
      IsOpen D ∧ OrdConnected D ∧ x₀ ∈ D ∧ z x₀ = (m₀, lam₀, φ₀) ∧
      (∀ x ∈ D, HasDerivAt z (staticInvRadiusRHS P q x (z x)) x) ∧
      (∀ x ∈ D, 0 < (z x).2.1 ∧ 0 < 1 - 2 * x * (z x).1) ∧
      ∀ (D' : Set ℝ) (v : ℝ → ℝ × ℝ × ℂ),
        IsOpen D' → OrdConnected D' → x₀ ∈ D' → v x₀ = (m₀, lam₀, φ₀) →
        (∀ x ∈ D', HasDerivAt v (staticInvRadiusRHS P q x (v x)) x) →
        (∀ x ∈ D', 0 < (v x).2.1 ∧ 0 < 1 - 2 * x * (v x).1) →
        D' ⊆ D ∧ EqOn v z D' := by
  obtain ⟨D, w, hD, hcD, hx₀, hw₀, hw, hwU, hmax⟩ :=
    static_inv_radius_exists_maximal P q x₀ m₀ lam₀ φ₀ hlam hg
  have hfst (x : ℝ) (hx : x ∈ D) : HasDerivAt (fun t => (w t).1) 1 x :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := w x)).comp_hasDerivAt x (hw x hx)
  have hcoord : EqOn (fun x => (w x).1) id D := by
    apply hD.eqOn_of_deriv_eq hcD.isPreconnected
      (fun x hx => (hfst x hx).differentiableAt.differentiableWithinAt)
      differentiableOn_id (fun x hx => ?_) hx₀ (by simp [hw₀])
    exact (hfst x hx).deriv.trans (hasDerivAt_id x).deriv.symm
  refine ⟨D, fun x => (w x).2, hD, hcD, hx₀, by simp [hw₀], ?_, ?_, ?_⟩
  · intro x hx
    have hd := (hasFDerivAt_snd (𝕜 := ℝ) (p := w x)).comp_hasDerivAt x (hw x hx)
    simpa only [hcoord hx, id_eq, Function.comp_def, ContinuousLinearMap.coe_snd'] using hd
  · intro x hx
    simpa only [hcoord hx, id_eq] using hwU x hx
  · intro D' v hD' hcD' hx₀' hv₀ hv hvU
    obtain ⟨hsub, heq⟩ := hmax D' (fun x => (x, v x)) hD' hcD' hx₀'
      (by simp [hv₀]) (fun x hx => (hasDerivAt_id x).prodMk (hv x hx)) hvU
    exact ⟨hsub, fun x hx => congrArg Prod.snd (heq hx)⟩

/-- [internal]
The adjoined inverse-radius coordinate equals the independent variable on any
closed solution interval initialized with that equality. No nondegeneracy of
the time interval is required. -/
theorem static_inv_radius_coordinate_of_solution {P : ℂ} {q a b x₀ : ℝ}
    {w : ℝ → State} (hx₀ : x₀ ∈ Icc a b)
    (hw : IsIntegralCurveOn w
      (fun _ v => ((1 : ℝ), staticInvRadiusRHS P q v.1 v.2)) (Icc a b))
    (hw₀ : (w x₀).1 = x₀) :
    ∀ x ∈ Icc a b, (w x).1 = x := by
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivWithinAt (fun t => (w t).1 - t) 0 (Icc a b) x := by
    have hfst : HasDerivWithinAt (fun t => (w t).1) 1 (Icc a b) x :=
      (hasFDerivAt_fst (𝕜 := ℝ) (p := w x)).comp_hasDerivWithinAt x (hw x hx)
    simpa only [Pi.sub_def, id_eq, sub_self] using!
      hfst.sub (hasDerivWithinAt_id x (Icc a b))
  intro x hx
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hd (fun _ _ => by simp : ∀ t ∈ Icc a b, ‖(0 : ℝ)‖ ≤ 0) (convex_Icc a b) hx₀ hx
  have heq : ((w x).1 - x) - ((w x₀).1 - x₀) = 0 :=
    norm_le_zero_iff.mp (by simpa only [zero_mul] using he)
  linarith only [heq, hw₀]

/-- [internal]
The three component derivatives of a literal static inverse-radius solution.
Every consumer obtains the derivative premise from ODE existence. -/
theorem static_inv_radius_components_of_solution {P : ℂ} {q x : ℝ}
    {z : ℝ → ℝ × ℝ × ℂ}
    (hz : HasDerivAt z (staticInvRadiusRHS P q x (z x)) x) :
    HasDerivAt (fun t => (z t).1)
      (-(1 - 2 * x * (z x).1) * ‖P‖ ^ 2 / (8 * (z x).2.1 ^ 2) - q ^ 2 / 2) x ∧
    HasDerivAt (fun t => (z t).2.1)
      (-(z x).2.1 * (2 * (z x).1 - q ^ 2 * x) / (1 - 2 * x * (z x).1)) x ∧
    HasDerivAt (fun t => (z t).2.2) (P / ((2 * (z x).2.1 : ℝ) : ℂ)) x := by
  have hm := (hasFDerivAt_fst (𝕜 := ℝ) (p := z x)).comp_hasDerivAt x hz
  have ht := (hasFDerivAt_snd (𝕜 := ℝ) (p := z x)).comp_hasDerivAt x hz
  have hl := (hasFDerivAt_fst (𝕜 := ℝ) (p := (z x).2)).comp_hasDerivAt x ht
  have hp := (hasFDerivAt_snd (𝕜 := ℝ) (p := (z x).2)).comp_hasDerivAt x ht
  exact ⟨by simpa only [Function.comp_def, ContinuousLinearMap.coe_fst',
      staticInvRadiusRHS] using! hm,
    by simpa only [Function.comp_def, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', staticInvRadiusRHS] using! hl,
    by simpa only [Function.comp_def, ContinuousLinearMap.coe_snd',
      staticInvRadiusRHS] using! hp⟩

/-- [internal]
The radial derivative of `r * φ` equals `φ + y`, with the conserved scalar ratio
`y = -(P / (2 * λ)) * x`. This is the derivative used in the outer estimate;
the identity is valid for every positive inverse radius. -/
theorem static_radial_weighted_scalar_deriv_of_solution {P : ℂ} {q x : ℝ}
    {z : ℝ → ℝ × ℝ × ℂ} (hx : 0 < x)
    (hz : HasDerivAt z (staticInvRadiusRHS P q x (z x)) x) :
    HasDerivAt (fun r : ℝ => (r : ℂ) * (z r⁻¹).2.2)
      ((z x).2.2 - (P / ((2 * (z x).2.1 : ℝ) : ℂ)) * x) x⁻¹ := by
  have hp := (static_inv_radius_components_of_solution hz).2.2
  have hp' : HasDerivAt (fun t => (z t).2.2)
      (P / ((2 * (z x).2.1 : ℝ) : ℂ)) ((x⁻¹)⁻¹) := by
    simpa only [inv_inv] using hp
  have hd := (hasDerivAt_id x⁻¹).ofReal_comp.mul
    (hp'.scomp x⁻¹ (hasDerivAt_inv (inv_ne_zero hx.ne')))
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have halg (A B : ℂ) : B - A * (x : ℂ) =
      B + (x : ℂ)⁻¹ * (-(x : ℂ) ^ 2 * A) := by
    field_simp
    ring
  convert hd using 1
  · simp only [Function.comp_def, Pi.mul_def, id_eq]
  · simpa only [Complex.ofReal_one, one_mul, inv_inv, Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_neg, Complex.ofReal_pow,
      Function.comp_def, id_eq, ← inv_pow] using!
        halg (P / ((2 * (z x).2.1 : ℝ) : ℂ)) (z x).2.2

/-- [internal]
The static scalar remains in the fixed complex direction of its amplitude on
every inward interval. Its real coefficient is at least its initial inverse
radius. This uses only the literal ODE and the positive expansion. -/
theorem static_scalar_phase_of_solution {P : ℂ} {q x₀ : ℝ} {D : Set ℝ}
    {z : ℝ → ℝ × ℝ × ℂ} (hD : IsOpen D) (hcD : OrdConnected D) (hx₀ : x₀ ∈ D)
    (hz : ∀ x ∈ D, HasDerivAt z (staticInvRadiusRHS P q x (z x)) x)
    (hlam : ∀ x ∈ D, 0 < (z x).2.1) (hinit : (z x₀).2.2 = P * x₀) :
    ∀ x ∈ D, x₀ ≤ x → ∃ c : ℝ, x₀ ≤ c ∧ (z x).2.2 = P * c := by
  have hp := fun x hx => (static_inv_radius_components_of_solution (hz x hx)).2.2
  by_cases hP : P = 0
  · have hd (x : ℝ) (hx : x ∈ D) : HasDerivAt (fun t => (z t).2.2) 0 x := by
      simpa only [hP, zero_div] using hp x hx
    intro x hx _
    refine ⟨x₀, le_rfl, ?_⟩
    exact (hD.is_const_of_deriv_eq_zero hcD.isPreconnected
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hd t ht).deriv) hx hx₀).trans hinit
  · have hquot (x : ℝ) (hx : x ∈ D) :
        HasDerivAt (fun t => (z t).2.2 / P)
          (((1 / (2 * (z x).2.1) : ℝ) : ℂ)) x := by
      have hlamx : ((2 * (z x).2.1 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt (hlam x hx)))
      have heq : (P / ((2 * (z x).2.1 : ℝ) : ℂ)) / P =
          (((1 / (2 * (z x).2.1) : ℝ) : ℂ)) := by
        push_cast
        field_simp
      simpa only [heq] using (hp x hx).div_const P
    have hreal (x : ℝ) (hx : x ∈ D) :
        HasDerivAt (fun t => ((z t).2.2 / P).re) (1 / (2 * (z x).2.1)) x := by
      simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using!
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hquot x hx)
    have himag (x : ℝ) (hx : x ∈ D) :
        HasDerivAt (fun t => ((z t).2.2 / P).im) 0 x := by
      simpa only [Function.comp_def, Complex.imCLM_apply, Complex.ofReal_im] using!
        Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hquot x hx)
    have hinitquot : (z x₀).2.2 / P = (x₀ : ℂ) := by
      rw [hinit]
      exact mul_div_cancel_left₀ _ hP
    have himag_zero (x : ℝ) (hx : x ∈ D) : ((z x).2.2 / P).im = 0 := by
      have he := hD.is_const_of_deriv_eq_zero hcD.isPreconnected
        (fun t ht => (himag t ht).differentiableAt.differentiableWithinAt)
        (fun t ht => (himag t ht).deriv) hx hx₀
      simpa only [hinitquot, Complex.ofReal_im] using he
    intro x hx hxx₀
    have hseg : Icc x₀ x ⊆ D := hcD.out hx₀ hx
    have hmono : MonotoneOn (fun t => ((z t).2.2 / P).re) (Icc x₀ x) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc x₀ x)
        (HasDerivAt.continuousOn (fun t ht => hreal t (hseg ht)))
        (fun t ht => (hreal t (hseg (interior_subset ht))).differentiableAt.differentiableWithinAt)
      intro t ht
      rw [(hreal t (hseg (interior_subset ht))).deriv]
      have hlt := hlam t (hseg (interior_subset ht))
      positivity
    refine ⟨((z x).2.2 / P).re, ?_, ?_⟩
    · simpa only [hinitquot, Complex.ofReal_re] using
        hmono (left_mem_Icc.mpr hxx₀) (right_mem_Icc.mpr hxx₀) hxx₀
    · have heq : (z x).2.2 / P = (((z x).2.2 / P).re : ℂ) := by
        apply Complex.ext <;> simp only [Complex.ofReal_re, Complex.ofReal_im, himag_zero x hx]
      calc
        (z x).2.2 = ((z x).2.2 / P) * P := (div_mul_cancel₀ _ hP).symm
        _ = P * (((z x).2.2 / P).re : ℂ) :=
          (congrArg (fun v : ℂ => v * P) heq).trans (mul_comm _ _)

/-- [internal]
The literal inverse-radius ODE implies all four radial static equations and
the conserved scalar flux. The gap and expansion are positive at the displayed
positive radius; this makes no assertion about a regular center. -/
theorem static_radial_equations_of_solution {P : ℂ} {q r : ℝ}
    {z : ℝ → ℝ × ℝ × ℂ} (hr : 0 < r)
    (hz : HasDerivAt z (staticInvRadiusRHS P q r⁻¹ (z r⁻¹)) r⁻¹)
    (hlam : 0 < (z r⁻¹).2.1) (hgap : 0 < 1 - 2 * r⁻¹ * (z r⁻¹).1) :
    let m : ℝ → ℝ := fun s => (z s⁻¹).1
    let lam : ℝ → ℝ := fun s => (z s⁻¹).2.1
    let phi : ℝ → ℂ := fun s => (z s⁻¹).2.2
    let y : ℝ → ℂ := fun s => -P / ((2 * s * lam s : ℝ) : ℂ)
    let g := 1 - 2 * m r / r
    let k := (2 * m r / r - q ^ 2 / r ^ 2) / g
    HasDerivAt (fun s => Real.log (lam s)) (k / r) r ∧
    HasDerivAt m (g * ‖y r‖ ^ 2 / 2 + q ^ 2 / (2 * r ^ 2)) r ∧
    HasDerivAt y (((-(1 + k) / r : ℝ) : ℂ) * y r) r ∧
    HasDerivAt phi (y r / (r : ℂ)) r ∧
    1 + k = (1 - q ^ 2 / r ^ 2) / g ∧
    ((2 * r * lam r : ℝ) : ℂ) * y r = -P := by
  let m : ℝ → ℝ := fun s => (z s⁻¹).1
  let lam : ℝ → ℝ := fun s => (z s⁻¹).2.1
  let phi : ℝ → ℂ := fun s => (z s⁻¹).2.2
  let y : ℝ → ℂ := fun s => -P / ((2 * s * lam s : ℝ) : ℂ)
  let g := 1 - 2 * m r / r
  let k := (2 * m r / r - q ^ 2 / r ^ 2) / g
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hlc : (lam r : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hg : g ≠ 0 := by
    have heq : g = 1 - 2 * r⁻¹ * (z r⁻¹).1 := by dsimp only [g, m]; ring
    rw [heq]
    exact hgap.ne'
  obtain ⟨hm, hl, hp⟩ := static_inv_radius_components_of_solution hz
  have hmP : HasDerivAt m
      (g * ‖P‖ ^ 2 / (8 * r ^ 2 * (lam r) ^ 2) + q ^ 2 / (2 * r ^ 2)) r := by
    convert hm.scomp r (hasDerivAt_inv hr.ne') using 1
    · simp only [m, Function.comp_def]
    · dsimp only [g, m, lam]
      simp only [smul_eq_mul]
      field_simp
      ring
  have hlr : HasDerivAt lam (lam r * k / r) r := by
    convert hl.scomp r (hasDerivAt_inv hr.ne') using 1
    · simp only [lam, Function.comp_def]
    · dsimp only [k, g, m, lam]
      simp only [smul_eq_mul]
      field_simp
  have hlog : HasDerivAt (fun s => Real.log (lam s)) (k / r) r := by
    have heq : (lam r * k / r) / lam r = k / r := by
      field_simp [show lam r ≠ 0 from hlam.ne']
    simpa only [heq] using hlr.log hlam.ne'
  have hden : 0 < 2 * r * lam r := by positivity
  have hdenC : ((2 * r * lam r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hden.ne'
  have hnorm : ‖y r‖ ^ 2 = ‖P‖ ^ 2 / (4 * r ^ 2 * (lam r) ^ 2) := by
    dsimp only [y]
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
    field_simp
    ring
  have hmass : HasDerivAt m (g * ‖y r‖ ^ 2 / 2 + q ^ 2 / (2 * r ^ 2)) r := by
    rw [hnorm]
    convert hmP using 1
    field_simp
    ring
  have hphi : HasDerivAt phi (y r / (r : ℂ)) r := by
    convert hp.scomp r (hasDerivAt_inv hr.ne') using 1
    · simp only [phi, Function.comp_def]
    · dsimp only [y, lam]
      simp only [Complex.real_smul]
      push_cast
      field_simp
  have hy : HasDerivAt y (((-(1 + k) / r : ℝ) : ℂ) * y r) r := by
    have hd := (hasDerivAt_const r (-P)).div
      ((((hasDerivAt_id r).const_mul 2).mul hlr).ofReal_comp) hdenC
    convert hd using 1
    · simp only [y, Pi.div_def, Pi.mul_def, id_eq]
    · dsimp only [y]
      simp only [Pi.mul_def, id_eq]
      push_cast
      field_simp
      ring
  refine ⟨hlog, hmass, hy, hphi, ?_, ?_⟩
  · dsimp only [k]
    apply (eq_div_iff hg).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hg]
    dsimp only [g]
    ring
  · dsimp only [y]
    exact mul_div_cancel₀ _ hdenC

/-- [internal]
Static geometry depends only on the amplitude norm and the squared electric
charge: references with equal initial geometry have equal mass and expansion
wherever both exist. Scalar values impose no additional geometric premise. -/
theorem static_geometry_eq_of_solutions
    {P P' : ℂ} {q q' x₀ : ℝ} {D D' : Set ℝ} {z z' : ℝ → ℝ × ℝ × ℂ}
    (hP : ‖P‖ = ‖P'‖) (hq : q ^ 2 = q' ^ 2)
    (hD : IsOpen D) (hcD : OrdConnected D) (hD' : IsOpen D') (hcD' : OrdConnected D')
    (hx₀ : x₀ ∈ D) (hx₀' : x₀ ∈ D')
    (hz : ∀ x ∈ D, HasDerivAt z (staticInvRadiusRHS P q x (z x)) x)
    (hz' : ∀ x ∈ D', HasDerivAt z' (staticInvRadiusRHS P' q' x (z' x)) x)
    (hpos : ∀ x ∈ D, 0 < (z x).2.1 ∧ 0 < 1 - 2 * x * (z x).1)
    (hpos' : ∀ x ∈ D', 0 < (z' x).2.1 ∧ 0 < 1 - 2 * x * (z' x).1)
    (hm₀ : (z x₀).1 = (z' x₀).1) (hlam₀ : (z x₀).2.1 = (z' x₀).2.1) :
    ∀ x ∈ D ∩ D', (z x).1 = (z' x).1 ∧ (z x).2.1 = (z' x).2.1 := by
  let U : Set (ℝ × ℝ × ℝ) := {v | 0 < v.2.2 ∧ 0 < 1 - 2 * v.1 * v.2.1}
  let G : (ℝ × ℝ × ℝ) → ℝ × ℝ × ℝ := fun v =>
    (1, -(1 - 2 * v.1 * v.2.1) * ‖P‖ ^ 2 / (8 * v.2.2 ^ 2) - q ^ 2 / 2,
      -v.2.2 * (2 * v.2.1 - q ^ 2 * v.1) / (1 - 2 * v.1 * v.2.1))
  let y := fun x => (x, (z x).1, (z x).2.1)
  let y' := fun x => (x, (z' x).1, (z' x).2.1)
  have hlocal : ∀ t ∈ D ∩ D', ∀ v ∈ U, ∃ (r d : ℝ) (K : ℝ≥0),
      0 < r ∧ 0 < d ∧ ∀ s ∈ Ioo (t - d) (t + d),
        LipschitzOnWith K G (closedBall v r) := by
    intro t _ v hv
    have hl : v.2.2 ≠ 0 := ne_of_gt hv.1
    have hg : 1 - 2 * v.1 * v.2.1 ≠ 0 := ne_of_gt hv.2
    have hd : 8 * v.2.2 ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hl)
    have hG : ContDiffAt ℝ 1 G v := by
      dsimp only [G]
      fun_prop (disch := first | assumption | norm_num)
    obtain ⟨K, O, hO, hK⟩ := hG.exists_lipschitzOnWith
    obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.mp hO
    exact ⟨r / 2, 1, K, half_pos hr, zero_lt_one, fun _ _ =>
      hK.mono ((closedBall_subset_ball (half_lt_self hr)).trans hrO)⟩
  have hy (x : ℝ) (hx : x ∈ D) : HasDerivAt y (G (y x)) x := by
    obtain ⟨hm, hl, _⟩ := static_inv_radius_components_of_solution (hz x hx)
    exact (hasDerivAt_id x).prodMk (hm.prodMk hl)
  have hy' (x : ℝ) (hx : x ∈ D') : HasDerivAt y' (G (y' x)) x := by
    obtain ⟨hm, hl, _⟩ := static_inv_radius_components_of_solution (hz' x hx)
    simpa only [G, y', hP.symm, hq.symm] using! (hasDerivAt_id x).prodMk (hm.prodMk hl)
  have heq := ODE.solution_eqOn_of_locally_lipschitz (f := fun _ => G) (U := U) (hD.inter hD')
    (hcD.inter hcD').isPreconnected ⟨hx₀, hx₀'⟩ hlocal
    (fun x hx => hy x hx.1) (fun x hx => hy' x hx.2)
    (fun x hx => hpos x hx.1) (fun x hx => hpos' x hx.2)
    (by dsimp only [y, y']; rw [hm₀, hlam₀])
  intro x hx
  exact ⟨congrArg (fun v => v.2.1) (heq hx), congrArg (fun v => v.2.2) (heq hx)⟩


/-- [node eq:co-static]
Construct the unique maximal positive-gap static reference from normalized
data at `L ≥ 64` (`charged_SF_new_version.tex:L2168–L2189`, L2199–L2225).
Its inverse-radius system is the literal source field; the four radial equations,
fixed scalar phase, geometry dependence only on `‖P‖`
and `q²`, and conserved flux are included.
No static trajectory is selected before existence, and no regular-center
solution is asserted. There are no unspecified constants in this theorem. -/
theorem co_static (P : ℂ) (q M L : ℝ) (_hM : 0 ≤ M)
    (hnorm : M + ‖P‖ + |q| = 1) (hL : 64 ≤ L) :
    ∃ (D : Set ℝ) (z : ℝ → ℝ × ℝ × ℂ),
      IsOpen D ∧ OrdConnected D ∧ L⁻¹ ∈ D ∧
      z L⁻¹ = (M, 1 / 2, P / (L : ℂ)) ∧
      (∀ x ∈ D, HasDerivAt z (staticInvRadiusRHS P q x (z x)) x) ∧
      (∀ x ∈ D, 0 < (z x).2.1 ∧ 0 < 1 - 2 * x * (z x).1) ∧
      (∀ (D' : Set ℝ) (v : ℝ → ℝ × ℝ × ℂ),
        IsOpen D' → OrdConnected D' → L⁻¹ ∈ D' →
        v L⁻¹ = (M, 1 / 2, P / (L : ℂ)) →
        (∀ x ∈ D', HasDerivAt v (staticInvRadiusRHS P q x (v x)) x) →
        (∀ x ∈ D', 0 < (v x).2.1 ∧ 0 < 1 - 2 * x * (v x).1) →
        D' ⊆ D ∧ EqOn v z D') ∧
      (-P / ((2 * L * (z L⁻¹).2.1 : ℝ) : ℂ) = -P / (L : ℂ)) ∧
      (∀ x ∈ D, L⁻¹ ≤ x → ∃ c : ℝ, L⁻¹ ≤ c ∧ (z x).2.2 = P * c) ∧
      (∀ (P' : ℂ) (q' : ℝ) (D' : Set ℝ) (v : ℝ → ℝ × ℝ × ℂ),
        ‖P‖ = ‖P'‖ → q ^ 2 = q' ^ 2 → IsOpen D' → OrdConnected D' → L⁻¹ ∈ D' →
        (v L⁻¹).1 = M → (v L⁻¹).2.1 = 1 / 2 →
        (∀ x ∈ D', HasDerivAt v (staticInvRadiusRHS P' q' x (v x)) x) →
        (∀ x ∈ D', 0 < (v x).2.1 ∧ 0 < 1 - 2 * x * (v x).1) →
        ∀ x ∈ D ∩ D', (z x).1 = (v x).1 ∧ (z x).2.1 = (v x).2.1) ∧
      ∀ r > 0, r⁻¹ ∈ D →
        let m : ℝ → ℝ := fun s => (z s⁻¹).1
        let lam : ℝ → ℝ := fun s => (z s⁻¹).2.1
        let phi : ℝ → ℂ := fun s => (z s⁻¹).2.2
        let y : ℝ → ℂ := fun s => -P / ((2 * s * lam s : ℝ) : ℂ)
        let g := 1 - 2 * m r / r
        let k := (2 * m r / r - q ^ 2 / r ^ 2) / g
        HasDerivAt (fun s => Real.log (lam s)) (k / r) r ∧
        HasDerivAt m (g * ‖y r‖ ^ 2 / 2 + q ^ 2 / (2 * r ^ 2)) r ∧
        HasDerivAt y (((-(1 + k) / r : ℝ) : ℂ) * y r) r ∧
        HasDerivAt phi (y r / (r : ℂ)) r ∧
        1 + k = (1 - q ^ 2 / r ^ 2) / g ∧
        ((2 * r * lam r : ℝ) : ℂ) * y r = -P := by
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hM1 : M ≤ 1 := by linarith only [hnorm, norm_nonneg P, abs_nonneg q]
  have hgap : 0 < 1 - 2 * L⁻¹ * M := by
    have hratio : 2 * M / L < 1 := (div_lt_one hLpos).mpr
      (by linarith only [hM1, hL])
    have heq : 2 * L⁻¹ * M = 2 * M / L := by ring
    rw [heq]
    linarith only [hratio]
  have hphi : P * ((L⁻¹ : ℝ) : ℂ) = P / (L : ℂ) := by
    rw [Complex.ofReal_inv, div_eq_mul_inv]
  obtain ⟨D, z, hD, hcD, hLD, hz₀, hz, hpos, hmax⟩ :=
    static_inv_radius_exists P q L⁻¹ M (1 / 2) (P * ((L⁻¹ : ℝ) : ℂ))
      (by norm_num) hgap
  have hboundary : z L⁻¹ = (M, 1 / 2, P / (L : ℂ)) := by
    simpa only [hphi] using hz₀
  refine ⟨D, z, hD, hcD, hLD, hboundary, hz, hpos, ?_, ?_, ?_, ?_, ?_⟩
  · intro D' v hD' hcD' hLD' hv₀ hv hvU
    apply hmax D' v hD' hcD' hLD' _ hv hvU
    simpa only [hphi] using hv₀
  · have heq : 2 * L * (z L⁻¹).2.1 = L := by rw [hz₀]; ring
    rw [heq]
  · exact static_scalar_phase_of_solution hD hcD hLD hz
      (fun x hx => (hpos x hx).1) (by rw [hz₀])
  · intro P' q' D' v hP hq hD' hcD' hLD' hvm hvl hv hvpos
    apply static_geometry_eq_of_solutions hP hq hD hcD hD' hcD' hLD hLD' hz hv hpos hvpos
    · simpa only [hz₀] using hvm.symm
    · simpa only [hz₀] using hvl.symm
  · intro r hr hrD
    exact static_radial_equations_of_solution hr (hz r⁻¹ hrD)
      (hpos r⁻¹ hrD).1 (hpos r⁻¹ hrD).2

end EmcsfAcExtension.Global
