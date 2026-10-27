/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Calculus.Endpoint
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.Reconstruction
import EmcsfAcExtension.Local.Calculus.Sections

/-! # Characteristic equations and relative charge for the conditional gap

The equations are the frozen AC equations, including their closed characteristic
endpoint versions. Radial integrals are written in null labels with `dr = λ dv`.
The numerical constants below are independent of the solution, coupling, and
triangle. Source: charged_SF_new_version.tex:L1483–1551.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Global.Gap

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [def-node cg:radius]
The mixed-radius equations on closed characteristic sections, including existing
axis endpoints. The prescribed densities are the literal frozen expressions. -/
theorem radius (hS : IsSolution e S D) :
    (∀ u a b, u ≤ a → a ≤ b → outSeg u a b ⊆ D →
      IntegralForm (S.nu u) (S.rUV u) a b) ∧
    (∀ a b v, a ≤ b → b ≤ v → inSeg a b v ⊆ D →
      IntegralForm (fun u => S.lam u v) (fun u => S.rUV u v) a b) := by
  exact ⟨fun _ _ _ hua hab hs => (Calculus.out_integralForm hS hua hab hs).2.1,
    fun _ _ _ hab hbv hs => (Calculus.in_integralForm hS hab hbv hs).2.1⟩

/-- [def-node cg:mass]
Both ordinary Hawking-mass equations on closed characteristic sections. No
renormalized mass or additional regularity assumption is used. -/
theorem mass (hS : IsSolution e S D) :
    (∀ u a b, u ≤ a → a ≤ b → outSeg u a b ⊆ D →
      IntegralForm (S.m u) (S.mV u) a b) ∧
    (∀ a b v, a ≤ b → b ≤ v → inSeg a b v ⊆ D →
      IntegralForm (fun u => S.m u v) (fun u => S.mU u v) a b) := by
  exact ⟨fun _ _ _ hua hab hs => (Calculus.out_integralForm hS hua hab hs).2.2.1,
    fun _ _ _ hab hbv hs => (Calculus.in_integralForm hS hab hbv hs).2.2.1⟩

/-- [def-node cg:scalar]
The outgoing Maxwell and scalar-transport equations in the frozen class, on
closed characteristic sections with their actual endpoint traces. -/
theorem scalar (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u ≤ a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    IntegralForm (S.Q u) (S.QV e u) a b ∧
      IntegralForm (S.xi u) (S.xiV e u) a b := by
  have h := Calculus.out_integralForm hS hua hab hs
  exact ⟨h.2.2.2.1, h.2.2.2.2.2.2⟩

/-- [node sec:charged-gap#mass-monotonicity]
The incoming ordinary mass density is nonpositive and the outgoing one is
nonnegative, with no size assumption on the coupling or scalar field. -/
theorem mass_monotonicity (hS : IsSolution e S D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.mU u v ≤ 0 ∧ 0 ≤ S.mV u v := by
  have hg := (hS.one_sub_mu_pos (u, v) hp).le
  have hn := (hS.nu_neg (u, v) hp).le
  have hl := (hS.lam_pos (u, v) hp).le
  constructor
  · exact add_nonpos
      (div_nonpos_of_nonneg_of_nonpos (mul_nonneg hg (sq_nonneg _))
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hn))
      (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hn)
        (mul_nonneg (by norm_num) (sq_nonneg _)))
  · exact add_nonneg
      (div_nonneg (mul_nonneg hg (sq_nonneg _)) (mul_nonneg (by norm_num) hl))
      (div_nonneg (mul_nonneg (sq_nonneg _) hl) (mul_nonneg (by norm_num) (sq_nonneg _)))

/-- [internal]
Outgoing mass is nondecreasing on any closed characteristic section. This
includes its existing regular-axis endpoint. -/
theorem mass_out_le (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u ≤ a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    S.m u a ≤ S.m u b := by
  have h := (mass hS).1 u a b hua hab hs
  have hi := intervalIntegral.integral_nonneg (μ := volume) hab
    (fun v hv => (mass_monotonicity hS (hs ⟨rfl, hv⟩)).2)
  rw [← h.2] at hi
  exact sub_nonneg.mp hi

/-- [internal]
The area radius is nondecreasing on a closed outgoing section. -/
theorem radius_out_le (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u ≤ a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    S.r u a ≤ S.r u b := by
  have h := (Calculus.out_integralForm hS hua hab hs).1
  have hi := intervalIntegral.integral_nonneg (μ := volume) hab
    (fun v hv => (hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)).le)
  rw [← h.2] at hi
  exact sub_nonneg.mp hi

/-- [internal]
The frozen mass ratio is jointly continuous on the solution domain. At an
existing axis point this uses its two-dimensional frozen limit and its actual
totalized value zero. No continuity at a missing endpoint is inferred. -/
theorem continuousOn_mu (hS : IsSolution e S D) :
    ContinuousOn (Function.uncurry S.mu) D := by
  intro p hp
  by_cases huv : p.1 < p.2
  · exact (continuousWithinAt_const.mul (hS.cont_m p hp)).div (hS.cont_r p hp)
      (hS.r_pos p hp huv).ne'
  · have heq : p.1 = p.2 := le_antisymm (hS.subset hp) (le_of_not_gt huv)
    rcases p with ⟨u, v⟩
    dsimp only at heq
    subst v
    have hzero : S.mu u u = 0 := by simp [Fields.mu, (hS.axis u hp).1]
    apply Metric.continuousWithinAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hlim⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hS.axis_mu u hp) ε hε
    refine ⟨δ, hδ, ?_⟩
    intro q hq hdist
    by_cases hquv : q.1 < q.2
    · simpa only [Function.uncurry_apply_pair, hzero] using hlim ⟨hq, hquv⟩ hdist
    · have hqe : q.1 = q.2 := le_antisymm (hS.subset hq) (le_of_not_gt hquv)
      have hqp : (q.1, q.1) = q := Prod.ext rfl hqe
      have hqzero : S.mu q.1 q.2 = 0 := by
        have haxis := (hS.axis q.1 (by rw [hqp]; exact hq)).1
        rw [← hqe]
        simp [Fields.mu, haxis]
      change dist (S.mu q.1 q.2) (S.mu u u) < ε
      rw [hzero, hqzero, dist_self]
      exact hε

/-- [internal]
The mixed-radius source is continuous on every closed positive-radius outgoing
annulus. No derivative of `ν` in the incoming direction is asserted. -/
theorem continuousOn_rUV_out (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hs : outSeg u a b ⊆ D) :
    ContinuousOn (S.rUV u) (Icc a b) := by
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cq := Calculus.continuousOn_out_section hS.cont_Q hs
  have cmu := Calculus.continuousOn_out_section (continuousOn_mu hS) hs
  have nr (v : ℝ) (hv : v ∈ Icc a b) : S.r u v ≠ 0 :=
    (hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
  exact ((cn.mul cl).div cr nr).mul
    ((cmu.sub ((cq.pow 2).div (cr.pow 2) (fun v hv => pow_ne_zero _ (nr v hv)))).div
      (continuousOn_const.sub cmu) (fun v hv =>
        (hS.one_sub_mu_pos (u, v) (hs ⟨rfl, hv⟩)).ne'))

/-- [internal]
The supported outgoing derivative of `ν` is pointwise in the interior of a
positive-radius characteristic segment, by FTC for its continuous source. -/
theorem nu_out_hasDerivAt (hS : IsSolution e S D) {u a b v : ℝ}
    (hua : u < a) (hs : outSeg u a b ⊆ D) (hv : v ∈ Ioo a b) :
    HasDerivAt (S.nu u) (S.rUV u v) v := by
  apply Local.hasDerivAt_of_integralForm_interior hv
    ((continuousOn_rUV_out hS hua hs).mono Ioo_subset_Icc_self)
  intro c d hc hcd hd
  exact (hS.eq_out u c d (hua.trans hc) hcd (by
    rintro ⟨x, y⟩ ⟨rfl, hcy, hyd⟩
    exact hs ⟨rfl, hc.le.trans hcy, hyd.trans hd.le⟩)).2.1

/-- [internal]
Outgoing `ν` is nonincreasing when the charged geometric numerator is
nonnegative. The conditional-gap consumer derives this bound by Gauss' law. -/
theorem nu_out_antitone_of_charge_bound (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D)
    (hcharge : ∀ v ∈ Icc a b, S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v) :
    S.nu u b ≤ S.nu u a := by
  have hf := (radius hS).1 u a b hua.le hab hs
  have hi := intervalIntegral.integral_nonneg (μ := volume) hab
    (f := fun v => -S.rUV u v) (fun v hv => by
      have hn := hS.nu_neg (u, v) (hs ⟨rfl, hv⟩)
      have hl := hS.lam_pos (u, v) (hs ⟨rfl, hv⟩)
      have hr := hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)
      have hg := hS.one_sub_mu_pos (u, v) (hs ⟨rfl, hv⟩)
      exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn.le hl.le) hr.le)
        (div_nonneg (sub_nonneg.mpr (hcharge v hv)) hg.le)))
  rw [intervalIntegral.integral_neg, ← hf.2] at hi
  linarith only [hi]

/-- [node cg:radial-mass]
The exact radial mass density with the null Jacobian divided out. Its
coefficient is `1/2`, uniformly over all solutions and couplings. -/
theorem radial_mass (hS : IsSolution e S D) {u v : ℝ} (hp : (u, v) ∈ D) :
    S.mV u v / S.lam u v =
      (1 - S.mu u v) / 2 * ‖S.theta u v / S.lam u v‖ ^ 2 +
        S.Q u v ^ 2 / (2 * S.r u v ^ 2) := by
  have h := Local.RelCharge.radial_mass_equation hS hp
  linear_combination h / 2

/-- [node cg:radial-mass]
The outgoing ordinary derivative divided by the radial Jacobian is the
paper's radial mass derivative a.e. on each positive-radius annulus. The
identity is uniform in all data and requires no bootstrap estimate. -/
theorem radial_mass_ae (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    ∀ᵐ v ∂volume.restrict (Icc a b), deriv (S.m u) v / S.lam u v =
      (1 - S.mu u v) / 2 * ‖S.theta u v / S.lam u v‖ ^ 2 +
        S.Q u v ^ 2 / (2 * S.r u v ^ 2) := by
  filter_upwards [(Calculus.out_section hS hua.le hab hs).2.2.1.2,
    ae_restrict_mem measurableSet_Icc] with v hd hv
  rw [hd.deriv]
  exact radial_mass hS (hs ⟨rfl, hv⟩)

end EmcsfAcExtension.Global.Gap


namespace EmcsfAcExtension.Global.Gap

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [internal]
Both ordinary mass sources are jointly continuous off the axis. Their
restriction to a moving positive-radius collar therefore uses actual continuous
functions, rather than representatives of two-dimensional a.e. classes. -/
theorem continuousOn_mass_sources (hS : IsSolution e S D) :
    ContinuousOn (Function.uncurry S.mU) (D ∩ {p | p.1 < p.2}) ∧
      ContinuousOn (Function.uncurry S.mV) (D ∩ {p | p.1 < p.2}) := by
  let K := D ∩ {p : ℝ × ℝ | p.1 < p.2}
  have cr := hS.cont_r.mono (show K ⊆ D from inter_subset_left)
  have cl := hS.cont_lam.mono (show K ⊆ D from inter_subset_left)
  have cn := hS.cont_nu.mono (show K ⊆ D from inter_subset_left)
  have cq := hS.cont_Q.mono (show K ⊆ D from inter_subset_left)
  have cmu := (continuousOn_mu hS).mono (show K ⊆ D from inter_subset_left)
  have cx := hS.cont_xi.mono (show K ⊆ D from inter_subset_left)
  have ct := hS.cont_theta.mono (show K ⊆ D from inter_subset_left)
  have nr (p : ℝ × ℝ) (hp : p ∈ K) : S.r p.1 p.2 ≠ 0 :=
    (hS.r_pos p hp.1 hp.2).ne'
  constructor
  · exact (((continuousOn_const.sub cmu).mul (cx.norm.pow 2)).div
      (continuousOn_const.mul cn) (fun p hp =>
        mul_ne_zero (by norm_num) (hS.nu_neg p hp.1).ne)).add
      (((cq.pow 2).mul cn).div (continuousOn_const.mul (cr.pow 2)) (fun p hp =>
        mul_ne_zero (by norm_num) (pow_ne_zero _ (nr p hp))))
  · exact (((continuousOn_const.sub cmu).mul (ct.norm.pow 2)).div
      (continuousOn_const.mul cl) (fun p hp =>
        mul_ne_zero (by norm_num) (hS.lam_pos p hp.1).ne')).add
      (((cq.pow 2).mul cl).div (continuousOn_const.mul (cr.pow 2)) (fun p hp =>
        mul_ne_zero (by norm_num) (pow_ne_zero _ (nr p hp))))

/-- [internal]
The ordinary mass has its prescribed joint differential at every ambient
interior point of a complete triangle. This is derived from the frozen
characteristic equations and continuous mass sources. -/
private theorem mass_partial_in {e u₀ b u v : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) (hu : u₀ < u) (huv : u < v) (hv : v ≤ b) :
    HasFDerivAt (fun x => S.m x v) (ContinuousLinearMap.toSpanSingleton ℝ (S.mU u v)) u := by
  have hs : inSeg u₀ v v ⊆ triangle u₀ b := by
    rintro ⟨x, y⟩ ⟨hx, hxy, rfl⟩
    exact ⟨hx, hxy, hv⟩
  exact (Local.IsSolution.hasDerivAt_mass_in hS hs ⟨hu, huv⟩).hasFDerivAt

private theorem mass_partial_out {e u₀ b u v : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) (hu : u₀ ≤ u) (huv : u < v) (hv : v < b) :
    HasFDerivAt (S.m u) (ContinuousLinearMap.toSpanSingleton ℝ (S.mV u v)) v := by
  have hs : outSeg u u b ⊆ triangle u₀ b := by
    rintro ⟨x, y⟩ ⟨rfl, hxy, hy⟩
    exact ⟨hu, hxy, hy⟩
  exact (Local.IsSolution.hasDerivAt_mass_out hS hs ⟨huv, hv⟩).hasFDerivAt

/-- [internal]
The ordinary mass has its prescribed joint differential at every ambient
interior point of a complete triangle, derived from its continuous sources. -/
theorem mass_hasFDerivAt {e u₀ b u v : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) (hu : u₀ < u) (huv : u < v) (hv : v < b) :
    HasFDerivAt (Function.uncurry S.m)
      ((ContinuousLinearMap.toSpanSingleton ℝ (S.mU u v)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (S.mV u v))) (u, v) := by
  let U := {p : ℝ × ℝ | u₀ < p.1 ∧ p.1 < p.2 ∧ p.2 < b}
  have ho : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_snd).inter (isOpen_lt continuous_snd continuous_const))
  have hp : (u, v) ∈ U := ⟨hu, huv, hv⟩
  have hsub : U ⊆ triangle u₀ b ∩ {p | p.1 < p.2} :=
    fun p hp => ⟨⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩, hp.2.1⟩
  have cU := (continuousOn_mass_sources hS).1.mono hsub
  have cV := (continuousOn_mass_sources hS).2.mono hsub
  let L : ℝ → (ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toSpanSingleton ℝ
  have cL : Continuous L := ContinuousLinearMap.toSpanSingletonCLE.continuous
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (u, v)) (f := S.m)
    (f₁ := fun x y => L (S.mU x y)) (f₂ := fun x y => L (S.mV x y))
  · filter_upwards [ho.eventually_mem hp] with q hq
    exact mass_partial_in hS hq.1 hq.2.1 hq.2.2.le
  · filter_upwards [ho.eventually_mem hp] with q hq
    exact mass_partial_out hS hq.1.le hq.2.1 hq.2.2
  · exact (cL.comp_continuousOn cU).continuousAt (ho.mem_nhds hp)
  · exact (cL.comp_continuousOn cV).continuousAt (ho.mem_nhds hp)

/-- [internal]
The actual mass chain rule along a differentiable positive-radius graph in the
interior of a complete triangle. The partial incoming density is distinguished
from the total derivative of mass along the moving graph. -/
theorem mass_curve_hasDerivAt {e u₀ b u V' : ℝ} {S : Fields} {V : ℝ → ℝ}
    (hS : IsSolution e S (triangle u₀ b))
    (hu : u₀ < u) (huv : u < V u) (hv : V u < b) (hV : HasDerivAt V V' u) :
    HasDerivAt (fun t => S.m t (V t)) (S.mU u (V u) + S.mV u (V u) * V') u := by
  have h := (mass_hasFDerivAt hS hu huv hv).comp_hasDerivAt u
    ((hasDerivAt_id u).prodMk hV)
  simpa only [Function.comp_def, Function.uncurry_def, id_eq,
    ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, one_mul, mul_one, mul_comm] using h

private theorem radius_partial_in {e u₀ b u v : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) (hu : u₀ < u) (huv : u < v) (hv : v ≤ b) :
    HasFDerivAt (fun x => S.r x v) (ContinuousLinearMap.toSpanSingleton ℝ (S.nu u v)) u := by
  have hs : inSeg u₀ v v ⊆ triangle u₀ b := by
    rintro ⟨x, y⟩ ⟨hx, hxy, rfl⟩
    exact ⟨hx, hxy, hv⟩
  apply HasDerivAt.hasFDerivAt
  apply Local.hasDerivAt_of_integralForm_interior ⟨hu, huv⟩
    ((Calculus.continuousOn_in_section hS.cont_nu hs).mono Ioo_subset_Icc_self)
  intro c d hc hcd hd
  exact (hS.eq_in c d v hcd hd (by
    rintro ⟨x, y⟩ ⟨hx, hxy, rfl⟩
    exact ⟨hc.le.trans hx, hxy.trans hd.le, hv⟩)).1

private theorem radius_partial_out {e u₀ b u v : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) (hu : u₀ ≤ u) (huv : u < v) (hv : v < b) :
    HasFDerivAt (S.r u) (ContinuousLinearMap.toSpanSingleton ℝ (S.lam u v)) v := by
  have hs : outSeg u u b ⊆ triangle u₀ b := by
    rintro ⟨x, y⟩ ⟨rfl, hxy, hy⟩
    exact ⟨hu, hxy, hy⟩
  exact (Local.IsSolution.hasDerivAt_radius_out hS hs ⟨huv, hv⟩).hasFDerivAt

/-- [internal]
The area radius is strictly differentiable at each off-axis ambient interior
point, with the actual prescribed partials `ν, λ`. This supplies the local
implicit-function theorem for a fractional-radius collar. -/
theorem radius_hasStrictFDerivAt {e u₀ b u v : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle u₀ b)) (hu : u₀ < u) (huv : u < v) (hv : v < b) :
    HasStrictFDerivAt (Function.uncurry S.r)
      ((ContinuousLinearMap.toSpanSingleton ℝ (S.nu u v)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (S.lam u v))) (u, v) := by
  let U := {p : ℝ × ℝ | u₀ < p.1 ∧ p.1 < p.2 ∧ p.2 < b}
  have ho : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_snd).inter (isOpen_lt continuous_snd continuous_const))
  have hp : (u, v) ∈ U := ⟨hu, huv, hv⟩
  have hsub : U ⊆ triangle u₀ b := fun _ hp => ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
  let L : ℝ → (ℝ →L[ℝ] ℝ) := ContinuousLinearMap.toSpanSingleton ℝ
  have cL : Continuous L := ContinuousLinearMap.toSpanSingletonCLE.continuous
  apply hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (u, v)) (f := S.r)
    (f₁ := fun x y => L (S.nu x y)) (f₂ := fun x y => L (S.lam x y))
  · filter_upwards [ho.eventually_mem hp] with q hq
    exact radius_partial_in hS hq.1 hq.2.1 hq.2.2.le
  · filter_upwards [ho.eventually_mem hp] with q hq
    exact radius_partial_out hS hq.1.le hq.2.1 hq.2.2
  · exact (cL.comp_continuousOn (hS.cont_nu.mono hsub)).continuousAt (ho.mem_nhds hp)
  · exact (cL.comp_continuousOn (hS.cont_lam.mono hsub)).continuousAt (ho.mem_nhds hp)

end EmcsfAcExtension.Global.Gap

namespace EmcsfAcExtension.Global.Annulus

/-- [node lem:charged-conditional-gap#weighted-charge-estimate]
Gauss' law with the bootstrap scalar size on a complete outgoing cone. Both
integrals include the radial Jacobian `λ`. The exact coefficient `1/4096` is
uniform in the solution, coupling, cone, and positive bootstrap gap. -/
theorem weighted_charge_estimate {e δ : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u < v)
    (hseg : outSeg u u v ⊆ D) (hδ : 0 < δ)
    (hgap : ∀ s ∈ Icc u v, δ ≤ 1 - S.mu u s)
    (hsmall : ∀ s ∈ Icc u v, |e| * S.r u s * ‖S.phi u s‖ ≤ δ / 64) :
    S.Q u v ^ 2 ≤
      (∫ s in u..v, S.lam u s * (1 - S.mu u s) *
        ‖S.theta u s / S.lam u s‖ ^ 2) *
      (∫ s in u..v, S.lam u s * (e ^ 2 * S.r u s ^ 2 *
        ‖S.phi u s‖ ^ 2 / (1 - S.mu u s))) ∧
    (∫ s in u..v, S.lam u s * (1 - S.mu u s) *
        ‖S.theta u s / S.lam u s‖ ^ 2) *
      (∫ s in u..v, S.lam u s * (e ^ 2 * S.r u s ^ 2 *
        ‖S.phi u s‖ ^ 2 / (1 - S.mu u s))) ≤
      2 * S.m u v * δ * S.r u v / 4096 := by
  have hp (s : ℝ) (hs : s ∈ Icc u v) : (u, s) ∈ D := hseg ⟨rfl, hs⟩
  have hr (s : ℝ) (hs : s ∈ Icc u v) : 0 ≤ S.r u s := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · subst s
      rw [(hS.axis u (hp u ⟨le_rfl, huv.le⟩)).1]
    · exact (hS.r_pos (u, s) (hp s hs) h).le
  have cr := Calculus.continuousOn_out_section hS.cont_r hseg
  have cl := Calculus.continuousOn_out_section hS.cont_lam hseg
  have cp := Calculus.continuousOn_out_section hS.cont_phi hseg
  have cg : ContinuousOn (fun s => 1 - S.mu u s) (Icc u v) :=
    continuousOn_const.sub (Local.continuousOn_mu_out hS huv hseg)
  have hi : IntervalIntegrable (fun s => S.lam u s *
      (e ^ 2 * S.r u s ^ 2 * ‖S.phi u s‖ ^ 2 / (1 - S.mu u s))) volume u v :=
    ContinuousOn.intervalIntegrable_of_Icc huv.le
      (cl.mul (((continuousOn_const.mul (cr.pow 2)).mul (cp.norm.pow 2)).div cg
        (fun s hs => (hS.one_sub_mu_pos (u, s) (hp s hs)).ne')))
  have hpoint (s : ℝ) (hs : s ∈ Icc u v) :
      S.lam u s * (e ^ 2 * S.r u s ^ 2 *
        ‖S.phi u s‖ ^ 2 / (1 - S.mu u s)) ≤ S.lam u s * (δ / 4096) := by
    apply mul_le_mul_of_nonneg_left _ (hS.lam_pos (u, s) (hp s hs)).le
    apply (div_le_iff₀ (hS.one_sub_mu_pos (u, s) (hp s hs))).mpr
    have hsq := (sq_le_sq₀
      (mul_nonneg (mul_nonneg (abs_nonneg e) (hr s hs)) (norm_nonneg _))
      (div_nonneg hδ.le (by norm_num))).mpr (hsmall s hs)
    simp only [mul_pow, sq_abs] at hsq
    have hg := mul_le_mul_of_nonneg_left (hgap s hs) (div_nonneg hδ.le
      (show (0 : ℝ) ≤ 4096 by norm_num))
    nlinarith only [hsq, hg]
  have hib := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) huv.le
    (cl.mul continuousOn_const : ContinuousOn (fun s => S.lam u s * (δ / 4096)) _)
  have hB := intervalIntegral.integral_mono_on huv.le hi hib hpoint
  simp only [Pi.mul_apply] at hB
  have hrform := (Calculus.out_integralForm hS le_rfl huv.le hseg).1
  have haxis := hS.axis u (hp u ⟨le_rfl, huv.le⟩)
  rw [intervalIntegral.integral_mul_const, ← hrform.2, haxis.1, sub_zero] at hB
  have hA : 0 ≤ ∫ s in u..v, S.lam u s * (1 - S.mu u s) *
      ‖S.theta u s / S.lam u s‖ ^ 2 :=
    intervalIntegral.integral_nonneg huv.le (fun s hs =>
      mul_nonneg (mul_nonneg (hS.lam_pos (u, s) (hp s hs)).le
        (hS.one_sub_mu_pos (u, s) (hp s hs)).le) (sq_nonneg _))
  have heq : (∫ s in u..v, S.lam u s * (e ^ 2 * S.r u s ^ 2 *
      ‖S.phi u s‖ ^ 2 / (1 - S.mu u s))) =
      e ^ 2 * (∫ s in u..v, S.lam u s * S.r u s ^ 2 *
        ‖S.phi u s‖ ^ 2 / (1 - S.mu u s)) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun s _ => by ring)
  constructor
  · rw [heq]
    convert Local.RelCharge.maxwell_cauchy_schwarz hS huv hseg using 1
    ring
  · calc
      _ ≤ (∫ s in u..v, S.lam u s * (1 - S.mu u s) *
          ‖S.theta u s / S.lam u s‖ ^ 2) * (S.r u v * (δ / 4096)) :=
        mul_le_mul_of_nonneg_left hB hA
      _ ≤ 2 * S.m u v * (S.r u v * (δ / 4096)) :=
        mul_le_mul_of_nonneg_right (Local.RelCharge.mass_controls_radial_flux hS huv hseg)
          (mul_nonneg (hr v ⟨huv.le, le_rfl⟩) (div_nonneg hδ.le (by norm_num)))
      _ = _ := by ring

end EmcsfAcExtension.Global.Annulus

namespace EmcsfAcExtension.Global.Gap

variable {e : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}

/-- [node cg:relative-charge]
The conditional relative-charge estimate, with the fixed perturbation size
`1/1024`. Both coefficients are uniform in all solution and triangle data. -/
theorem relative_charge {e δ : ℝ} {S : Fields} {D : Set (ℝ × ℝ)}
    (hS : IsSolution e S D) {u v : ℝ} (huv : u < v)
    (hseg : outSeg u u v ⊆ D) (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : 0 ≤ S.mu u v)
    (hgap : ∀ s ∈ Icc u v, δ ≤ 1 - S.mu u s)
    (hsmall : ∀ s ∈ Icc u v, |e| * S.r u s * ‖S.phi u s‖ ≤ δ / 64) :
    S.Q u v ^ 2 / S.r u v ^ 2 ≤ (δ / 4096) * S.mu u v ∧
      (δ / 4096) * S.mu u v ≤ (1 / 1024 : ℝ) * S.mu u v := by
  have h := Annulus.weighted_charge_estimate hS huv hseg hδ.1 hgap hsmall
  have hr := hS.r_pos (u, v) (hseg ⟨rfl, huv.le, le_rfl⟩) huv
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    calc
      _ ≤ _ := h.1.trans h.2
      _ = (δ / 4096) * S.mu u v * S.r u v ^ 2 := by
        dsimp [Fields.mu]
        field_simp [hr.ne']
  · exact mul_le_mul_of_nonneg_right (by linarith only [hδ.2]) hmu

/-- [internal]
Outgoing `ν` is nonincreasing under the actual conditional-gap bootstrap on
the complete outgoing cone. Gauss' law discharges the charged numerator bound. -/
theorem nu_out_antitone {δ u a b : ℝ} (hS : IsSolution e S D)
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u u b ⊆ D)
    (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ v ∈ Icc u b, 0 ≤ S.mu u v)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v)
    (hsmall : ∀ v ∈ Icc u b, |e| * S.r u v * ‖S.phi u v‖ ≤ δ / 64) :
    S.nu u b ≤ S.nu u a := by
  apply nu_out_antitone_of_charge_bound hS hua hab
    (fun p hp => hs (outSeg_subset_outSeg hua.le le_rfl hp))
  intro v hv
  have huv := hua.trans_le hv.1
  have hvb : v ∈ Icc u b := ⟨huv.le, hv.2⟩
  have hrel := relative_charge hS huv
    (fun p hp => hs (outSeg_subset_outSeg le_rfl hv.2 hp)) hδ (hmu v hvb)
    (fun x hx => hgap x ⟨hx.1, hx.2.trans hv.2⟩)
    (fun x hx => hsmall x ⟨hx.1, hx.2.trans hv.2⟩)
  exact (hrel.1.trans hrel.2).trans (by nlinarith only [hmu v hvb])

/-- [internal]
Characteristic FTC for the logarithm of the negative incoming expansion on a
positive-radius annulus. The radial derivative has its exact null Jacobian. -/
theorem log_neg_nu_integralForm (hS : IsSolution e S D) {u a b : ℝ}
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u a b ⊆ D) :
    IntegralForm (fun v => Real.log (-S.nu u v))
      (fun v => S.lam u v * (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
        ((1 - S.mu u v) * S.r u v)) a b := by
  have cn := Calculus.continuousOn_out_section hS.cont_nu hs
  have cl := Calculus.continuousOn_out_section hS.cont_lam hs
  have cr := Calculus.continuousOn_out_section hS.cont_r hs
  have cq := Calculus.continuousOn_out_section hS.cont_Q hs
  have cmu := Calculus.continuousOn_out_section (continuousOn_mu hS) hs
  have nr (v : ℝ) (hv : v ∈ Icc a b) : S.r u v ≠ 0 :=
    (hS.r_pos (u, v) (hs ⟨rfl, hv⟩) (hua.trans_le hv.1)).ne'
  have nn (v : ℝ) (hv : v ∈ Icc a b) : S.nu u v ≠ 0 :=
    (hS.nu_neg (u, v) (hs ⟨rfl, hv⟩)).ne
  have ng (v : ℝ) (hv : v ∈ Icc a b) : 1 - S.mu u v ≠ 0 :=
    (hS.one_sub_mu_pos (u, v) (hs ⟨rfl, hv⟩)).ne'
  have cf : ContinuousOn (fun v => Real.log (-S.nu u v)) (Icc a b) :=
    cn.neg.log (fun v hv => neg_ne_zero.mpr (nn v hv))
  have csrc : ContinuousOn (fun v => S.lam u v *
      (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
      ((1 - S.mu u v) * S.r u v)) (Icc a b) :=
    (cl.mul (cmu.sub ((cq.pow 2).div (cr.pow 2) (fun v hv => pow_ne_zero _ (nr v hv))))).div
      ((continuousOn_const.sub cmu).mul cr) (fun v hv => mul_ne_zero (ng v hv) (nr v hv))
  refine ⟨csrc.intervalIntegrable_of_Icc hab,
    (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab cf ?_
      (csrc.intervalIntegrable_of_Icc hab)).symm⟩
  intro v hv
  have hd := ((nu_out_hasDerivAt hS hua hs hv).neg).log
    (neg_ne_zero.mpr (nn v ⟨hv.1.le, hv.2.le⟩))
  apply hd.congr_deriv
  dsimp [Fields.rUV]
  field_simp [nn v ⟨hv.1.le, hv.2.le⟩, nr v ⟨hv.1.le, hv.2.le⟩,
    ng v ⟨hv.1.le, hv.2.le⟩]

/-- [node cg:radial-nu]
The radial logarithmic expansion identity and its sign under the complete-cone
bootstrap. The integral density includes `λ`; after division by the strictly
positive Jacobian it is exactly the radial derivative in charged_SF_new_version.tex:L1539.
The monotonicity has no data-dependent constant. -/
theorem radial_nu {δ u a b : ℝ} (hS : IsSolution e S D)
    (hua : u < a) (hab : a ≤ b) (hs : outSeg u u b ⊆ D)
    (hδ : 0 < δ ∧ δ ≤ 1)
    (hmu : ∀ v ∈ Icc u b, 0 ≤ S.mu u v)
    (hgap : ∀ v ∈ Icc u b, δ ≤ 1 - S.mu u v)
    (hsmall : ∀ v ∈ Icc u b, |e| * S.r u v * ‖S.phi u v‖ ≤ δ / 64) :
    IntegralForm (fun v => Real.log (-S.nu u v))
      (fun v => S.lam u v * (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
        ((1 - S.mu u v) * S.r u v)) a b ∧
    (∀ v ∈ Icc a b, 0 ≤ (S.mu u v - S.Q u v ^ 2 / S.r u v ^ 2) /
        ((1 - S.mu u v) * S.r u v)) ∧
    S.nu u b ≤ S.nu u a := by
  refine ⟨log_neg_nu_integralForm hS hua hab
    (fun p hp => hs (outSeg_subset_outSeg hua.le le_rfl hp)), ?_,
    nu_out_antitone hS hua hab hs hδ hmu hgap hsmall⟩
  intro v hv
  have huv := hua.trans_le hv.1
  have hvb : v ∈ Icc u b := ⟨huv.le, hv.2⟩
  have hp : (u, v) ∈ D := hs ⟨rfl, hvb⟩
  have hrel := relative_charge hS huv
    (fun p hp => hs (outSeg_subset_outSeg le_rfl hv.2 hp)) hδ (hmu v hvb)
    (fun x hx => hgap x ⟨hx.1, hx.2.trans hv.2⟩)
    (fun x hx => hsmall x ⟨hx.1, hx.2.trans hv.2⟩)
  have hcharge : S.Q u v ^ 2 / S.r u v ^ 2 ≤ S.mu u v :=
    (hrel.1.trans hrel.2).trans (by nlinarith only [hmu v hvb])
  exact div_nonneg (sub_nonneg.mpr hcharge)
    (mul_nonneg (hS.one_sub_mu_pos (u, v) hp).le (hS.r_pos (u, v) hp huv).le)

end EmcsfAcExtension.Global.Gap

namespace EmcsfAcExtension.Global.Gap

/-- [node sec:charged-gap#characteristic-calculus]
Joint radius and mass calculus off the axis, continuity of the axis gap, and
every frozen characteristic FTC on closed sections. Every endpoint density is
integrable in its literal frozen form. Radial and collar identities below use
these facts with their exact null Jacobians; no smooth approximation is assumed. -/
theorem characteristic_calculus {e a b : ℝ} {S : Fields}
    (hS : IsSolution e S (triangle a b)) (hab : a < b) :
    ContinuousOn (Function.uncurry S.mu) (triangle a b) ∧
    ContDiffOn ℝ 1 (Function.uncurry S.r) (triangle a b) ∧
    (∀ u v, a < u → u < v → v < b →
      HasStrictFDerivAt (Function.uncurry S.r)
        ((ContinuousLinearMap.toSpanSingleton ℝ (S.nu u v)).coprod
          (ContinuousLinearMap.toSpanSingleton ℝ (S.lam u v))) (u, v) ∧
      HasFDerivAt (Function.uncurry S.m)
        ((ContinuousLinearMap.toSpanSingleton ℝ (S.mU u v)).coprod
          (ContinuousLinearMap.toSpanSingleton ℝ (S.mV u v))) (u, v)) ∧
    (∀ u c d, u ≤ c → c ≤ d → outSeg u c d ⊆ triangle a b →
      IntegralForm (S.r u) (S.lam u) c d ∧ IntegralForm (S.nu u) (S.rUV u) c d ∧
      IntegralForm (S.m u) (S.mV u) c d ∧ IntegralForm (S.Q u) (S.QV e u) c d ∧
      IntegralForm (S.A u) (S.AV u) c d ∧ IntegralForm (S.phi u) (S.phiV u) c d ∧
      IntegralForm (S.xi u) (S.xiV e u) c d) ∧
    (∀ c d v, c ≤ d → d ≤ v → inSeg c d v ⊆ triangle a b →
      IntegralForm (fun u => S.r u v) (fun u => S.nu u v) c d ∧
      IntegralForm (fun u => S.lam u v) (fun u => S.rUV u v) c d ∧
      IntegralForm (fun u => S.m u v) (fun u => S.mU u v) c d ∧
      IntegralForm (fun u => S.Q u v) (fun u => S.QU e u v) c d ∧
      IntegralForm (fun u => S.phi u v) (fun u => S.phiU e u v) c d ∧
      IntegralForm (fun u => S.theta u v) (fun u => S.thetaU e u v) c d) :=
  ⟨continuousOn_mu hS, Local.IsSolution.contDiffOn_r hS hab,
    fun _ _ hu huv hv => ⟨radius_hasStrictFDerivAt hS hu huv hv, mass_hasFDerivAt hS hu huv hv⟩,
    fun _ _ _ huc hcd hs => Calculus.out_integralForm hS huc hcd hs,
    fun _ _ _ hcd hdv hs => Calculus.in_integralForm hS hcd hdv hs⟩

end EmcsfAcExtension.Global.Gap
