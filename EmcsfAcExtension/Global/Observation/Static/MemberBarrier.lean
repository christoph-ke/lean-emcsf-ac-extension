module

public import EmcsfAcExtension.Global.Observation.Static.ODE
import EmcsfAcExtension.Infra.ODE.Continuation
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Strict barriers for individual static references

The inverse-radius mass equation has a nonpositive derivative. Its electric
term, or the conserved scalar mode when charge vanishes, precludes persistence
of nonnegative mass and a positive fixed gap down to radius zero.
Source: `charged_SF_new_version.tex:L2230–L2273` and internal project record's member barrier
argument.
-/

public section

open Set Metric Filter Topology
open scoped NNReal

namespace EmcsfAcExtension.Global.Observation

local notation "State" => (ℝ × ℝ × ℝ × ℂ)

/-- [internal]
Project the literal inverse-radius equation to its mass equation. This helper
is used only with the trajectories supplied by static ODE existence. -/
theorem static_mass_deriv_of_solution {P : ℂ} {q x : ℝ}
    {z : ℝ → ℝ × ℝ × ℂ}
    (hz : HasDerivAt z (staticInvRadiusRHS P q x (z x)) x) :
    HasDerivAt (fun t => (z t).1)
      (-(1 - 2 * x * (z x).1) * ‖P‖ ^ 2 / (8 * (z x).2.1 ^ 2) - q ^ 2 / 2) x := by
  simpa only [Function.comp_def, ContinuousLinearMap.coe_fst', staticInvRadiusRHS] using!
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z x)).comp_hasDerivAt x hz

/-- [internal]
The electric term bounds the inverse-radius mass slope independently of the
scalar amplitude. There is no estimate constant to choose. -/
theorem static_mass_slope_le (P : ℂ) (q x : ℝ) (z : ℝ × ℝ × ℂ)
    (hg : 0 ≤ 1 - 2 * x * z.1) :
    (staticInvRadiusRHS P q x z).1 ≤ -(q ^ 2 / 2) := by
  have hs : 0 ≤ (1 - 2 * x * z.1) * ‖P‖ ^ 2 / (8 * z.2.1 ^ 2) :=
    div_nonneg (mul_nonneg hg (sq_nonneg _)) (by positivity)
  change -(1 - 2 * x * z.1) * ‖P‖ ^ 2 / (8 * z.2.1 ^ 2) - q ^ 2 / 2 ≤ _
  rw [neg_mul, neg_div]
  linarith only [hs]

/-- [internal]
Mass is nonincreasing as inverse radius increases on a convex positive-gap
solution interval. The positive gap is the reference gap, with no regular-axis
hypothesis. -/
theorem static_mass_antitone_of_solution {P : ℂ} {q : ℝ} {D : Set ℝ}
    {z : ℝ → ℝ × ℝ × ℂ} (hD : Convex ℝ D)
    (hz : ∀ x ∈ D, HasDerivAt z (staticInvRadiusRHS P q x (z x)) x)
    (hg : ∀ x ∈ D, 0 ≤ 1 - 2 * x * (z x).1) :
    AntitoneOn (fun x => (z x).1) D := by
  have hm := fun x hx => static_mass_deriv_of_solution (hz x hx)
  apply antitoneOn_of_deriv_nonpos hD
    (HasDerivAt.continuousOn hm)
    (fun x hx => (hm x (interior_subset hx)).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [(hm x (interior_subset hx)).deriv]
  exact (static_mass_slope_le P q x (z x) (hg x (interior_subset hx))).trans
    (by nlinarith only [sq_nonneg q])

/-- [internal]
Safe static references continue through any prescribed finite inverse radius.
All compact bounds are derived from nonnegative mass and the fixed positive
gap on the displayed interval. The maximality premise is discharged by static
ODE existence; the safe bounds arise in the contradiction argument for a strict
barrier. No continuation hypothesis enters a source node's conclusion. -/
theorem static_Icc_subset_domain_of_safe_maximal_solution
    {P : ℂ} {q a B δ : ℝ} {D : Set ℝ} {w : ℝ → State}
    (ha : 0 < a) (haB : a ≤ B) (hδ : 0 < δ)
    (hD : IsOpen D) (hcD : OrdConnected D) (haD : a ∈ D)
    (hw : ∀ t ∈ D,
      HasDerivAt w ((1 : ℝ), staticInvRadiusRHS P q (w t).1 (w t).2) t)
    (hwU : ∀ t ∈ D, 0 < (w t).2.2.1 ∧ 0 < 1 - 2 * (w t).1 * (w t).2.1)
    (hcoord : ∀ t ∈ D, (w t).1 = t)
    (hmax : ∀ (D' : Set ℝ) (v : ℝ → State), IsOpen D' → OrdConnected D' → a ∈ D' →
      v a = w a →
      (∀ t ∈ D', HasDerivAt v ((1 : ℝ), staticInvRadiusRHS P q (v t).1 (v t).2) t) →
      (∀ t ∈ D', 0 < (v t).2.2.1 ∧ 0 < 1 - 2 * (v t).1 * (v t).2.1) → D' ⊆ D)
    (hsafe : ∀ t ∈ D ∩ Icc a B, 0 ≤ (w t).2.1 ∧ δ ≤ 1 - 2 * t * (w t).2.1) :
    Icc a B ⊆ D := by
  let z : ℝ → ℝ × ℝ × ℂ := fun t => (w t).2
  let m₀ := (z a).1
  let lam₀ := (z a).2.1
  have hlam₀ : 0 < lam₀ := (hwU a haD).1
  have hm₀ : 0 ≤ m₀ := (hsafe a ⟨haD, le_rfl, haB⟩).1
  have hz (t : ℝ) (ht : t ∈ D) :
      HasDerivAt z (staticInvRadiusRHS P q t (z t)) t := by
    simpa only [z, hcoord t ht, Function.comp_def, ContinuousLinearMap.coe_snd'] using!
      (hasFDerivAt_snd (𝕜 := ℝ) (p := w t)).comp_hasDerivAt t (hw t ht)
  have hmass (t : ℝ) (ht : t ∈ D ∩ Icc a B) : (z t).1 ∈ Icc 0 m₀ := by
    have hseg : Icc a t ⊆ D := hcD.out haD ht.1
    have hanti := static_mass_antitone_of_solution (convex_Icc a t)
      (fun s hs => hz s (hseg hs)) (fun s hs => by
        simpa only [z, hcoord s (hseg hs)] using (hwU s (hseg hs)).2.le)
    exact ⟨(hsafe t ht).1,
      hanti (left_mem_Icc.mpr ht.2.1) (right_mem_Icc.mpr ht.2.1) ht.2.1⟩
  let K : ℝ := (2 * m₀ + q ^ 2 * B) / δ
  have hB : 0 ≤ B := ha.le.trans haB
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hlog (t : ℝ) (ht : t ∈ D ∩ Icc a B) :
      HasDerivAt (fun s => Real.log ((z s).2.1))
        (-(2 * (z t).1 - q ^ 2 * t) / (1 - 2 * t * (z t).1)) t := by
    have hl := (static_inv_radius_components_of_solution (hz t ht.1)).2.1
    have hlam : (z t).2.1 ≠ 0 := ne_of_gt (hwU t ht.1).1
    have hg : 1 - 2 * t * (z t).1 ≠ 0 := by
      simpa only [z, hcoord t ht.1] using ne_of_gt (hwU t ht.1).2
    have heq : (-(z t).2.1 * (2 * (z t).1 - q ^ 2 * t) /
        (1 - 2 * t * (z t).1)) / (z t).2.1 =
        -(2 * (z t).1 - q ^ 2 * t) / (1 - 2 * t * (z t).1) := by
      field_simp
    simpa only [heq] using hl.log hlam
  have hlog_bound (t : ℝ) (ht : t ∈ D ∩ Icc a B) :
      |-(2 * (z t).1 - q ^ 2 * t) / (1 - 2 * t * (z t).1)| ≤ K := by
    have hm := hmass t ht
    have hmnonneg : 0 ≤ (z t).1 := hm.1
    have ht₀ : 0 ≤ t := ha.le.trans ht.2.1
    have hg := (hsafe t ht).2
    have hnum : |2 * (z t).1 - q ^ 2 * t| ≤ 2 * m₀ + q ^ 2 * B := by
      calc
        |2 * (z t).1 - q ^ 2 * t| ≤ |2 * (z t).1| + |q ^ 2 * t| := abs_sub _ _
        _ = 2 * (z t).1 + q ^ 2 * t := by
          rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        _ ≤ 2 * m₀ + q ^ 2 * B := add_le_add
          (mul_le_mul_of_nonneg_left hm.2 (by norm_num))
          (mul_le_mul_of_nonneg_left ht.2.2 (sq_nonneg q))
    rw [abs_div, abs_neg, abs_of_pos (show 0 < 1 - 2 * t * (z t).1 from hδ.trans_le hg)]
    apply (div_le_iff₀ (hδ.trans_le hg)).mpr
    calc
      |2 * (z t).1 - q ^ 2 * t| ≤ 2 * m₀ + q ^ 2 * B := hnum
      _ = K * δ := by dsimp only [K]; rw [div_mul_cancel₀ _ hδ.ne']
      _ ≤ K * (1 - 2 * t * (z t).1) := mul_le_mul_of_nonneg_left hg hK
  let ell := Real.exp (Real.log lam₀ - K * (B - a))
  let upper := Real.exp (Real.log lam₀ + K * (B - a))
  have hell : 0 < ell := Real.exp_pos _
  have hlam (t : ℝ) (ht : t ∈ D ∩ Icc a B) : (z t).2.1 ∈ Icc ell upper := by
    have hseg : Icc a t ⊆ D := hcD.out haD ht.1
    have hsub : Icc a t ⊆ Icc a B := Icc_subset_Icc le_rfl ht.2.2
    have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hlog s ⟨hseg hs, hsub hs⟩).hasDerivWithinAt)
      (fun s hs => by simpa only [Real.norm_eq_abs] using hlog_bound s ⟨hseg hs, hsub hs⟩)
      (convex_Icc a t) (left_mem_Icc.mpr ht.2.1) (right_mem_Icc.mpr ht.2.1)
    have he' : |Real.log ((z t).2.1) - Real.log lam₀| ≤ K * (B - a) := by
      have hd : K * (t - a) ≤ K * (B - a) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2 a) hK
      have he'' : |Real.log ((z t).2.1) - Real.log lam₀| ≤ K * (t - a) := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2.1)] using he
      exact he''.trans hd
    have hpos : 0 < (z t).2.1 := (hwU t ht.1).1
    constructor
    · calc
        ell ≤ Real.exp (Real.log ((z t).2.1)) := Real.exp_le_exp.mpr
          (by linarith only [(abs_le.mp he').1])
        _ = (z t).2.1 := Real.exp_log hpos
    · calc
        (z t).2.1 = Real.exp (Real.log ((z t).2.1)) := (Real.exp_log hpos).symm
        _ ≤ upper := Real.exp_le_exp.mpr (by linarith only [(abs_le.mp he').2])
  let N := ‖P‖ / (2 * ell)
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hphi_bound (t : ℝ) (ht : t ∈ D ∩ Icc a B) :
      ‖P / ((2 * (z t).2.1 : ℝ) : ℂ)‖ ≤ N := by
    have hl := hlam t ht
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < 2 * (z t).2.1 by linarith only [hell, hl.1])]
    exact div_le_div_of_nonneg_left (norm_nonneg P) (by positivity)
      (mul_le_mul_of_nonneg_left hl.1 (by norm_num))
  let phiBound := ‖(z a).2.2‖ + N * (B - a)
  have hphi (t : ℝ) (ht : t ∈ D ∩ Icc a B) : ‖(z t).2.2‖ ≤ phiBound := by
    have hseg : Icc a t ⊆ D := hcD.out haD ht.1
    have hsub : Icc a t ⊆ Icc a B := Icc_subset_Icc le_rfl ht.2.2
    have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (static_inv_radius_components_of_solution (hz s (hseg hs))).2.2.hasDerivWithinAt)
      (fun s hs => hphi_bound s ⟨hseg hs, hsub hs⟩)
      (convex_Icc a t) (left_mem_Icc.mpr ht.2.1) (right_mem_Icc.mpr ht.2.1)
    have he' : ‖(z t).2.2 - (z a).2.2‖ ≤ N * (t - a) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2.1)] using he
    have hn := norm_le_norm_sub_add (z t).2.2 (z a).2.2
    have hd := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.2 a) hN
    dsimp only [phiBound]
    linarith only [hn, he', hd]
  let U : Set State := {v | 0 < v.2.2.1 ∧ 0 < 1 - 2 * v.1 * v.2.1}
  let C : Set State := (Icc a B ×ˢ Icc 0 m₀ ×ˢ Icc ell upper ×ˢ
    closedBall 0 phiBound) ∩ {v | δ ≤ 1 - 2 * v.1 * v.2.1}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_snd.snd.fst).inter
      (isOpen_lt continuous_const
        (show Continuous (fun v : State => 1 - 2 * v.1 * v.2.1) by fun_prop))
  have hC : IsCompact C :=
    (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod
      (isCompact_closedBall _ _)))).inter_right
        (isClosed_le continuous_const (by fun_prop))
  have hCU : C ⊆ U := fun v hv =>
    ⟨hell.trans_le hv.1.2.2.1.1, hδ.trans_le hv.2⟩
  have hcont : ContinuousOn
      (fun p : ℝ × State => ((1 : ℝ), staticInvRadiusRHS P q p.2.1 p.2.2))
      (univ ×ˢ U) := by
    intro p hp
    exact ((static_inv_radius_contDiffAt P q p.2 (ne_of_gt hp.2.1)
      (ne_of_gt hp.2.2)).continuousAt.comp
        (f := fun p : ℝ × State => p.2) continuous_snd.continuousAt).continuousWithinAt
  have hlocal : ∀ t : ℝ, ∀ v ∈ U, ∃ (r d : ℝ) (K : ℝ≥0),
      0 < r ∧ 0 < d ∧ ∀ s ∈ Icc (t - d) (t + d),
        LipschitzOnWith K
          (fun v : State => ((1 : ℝ), staticInvRadiusRHS P q v.1 v.2))
          (closedBall v r) := by
    intro t v hv
    obtain ⟨V, r, K, _, hpV, hr, hK⟩ :=
      static_inv_radius_local_lipschitz (P, q) v hv.1 hv.2
    exact ⟨r, 1, K, hr, zero_lt_one, fun _ _ => hK (P, q) hpV⟩
  apply ODE.Icc_subset_domain_of_maximal_of_mem_isCompact
    (f := fun _ v => ((1 : ℝ), staticInvRadiusRHS P q v.1 v.2))
    haB hU hC hCU hcont hlocal hD hcD haD hw hwU hmax
  intro t ht
  refine ⟨⟨?_, hmass t ht, hlam t ht, ?_⟩, ?_⟩
  · simpa only [hcoord t ht.1] using ht.2
  · simpa only [mem_closedBall, dist_zero_right] using hphi t ht
  · simpa only [mem_ofPred_eq, hcoord t ht.1] using! (hsafe t ht).2

/-- [internal]
Each nontrivial positive-gap static datum reaches a strict mass or gap barrier
at a finite inverse radius. The interval and margin may depend on this datum;
there is no constant asserted uniformly here. All ODE witnesses are obtained
from maximal existence before the contradiction argument. -/
theorem static_member_barrier_of_nontrivial_data
    (P : ℂ) (q a m₀ lam₀ δ : ℝ) (phi₀ : ℂ)
    (ha : 0 < a) (hlam₀ : 0 < lam₀) (hg₀ : 0 < 1 - 2 * a * m₀)
    (hδ : 0 < δ) (hactive : P ≠ 0 ∨ q ≠ 0 ∨ m₀ ≠ 0) :
    ∃ b ≥ a, ∃ z : ℝ → ℝ × ℝ × ℂ,
      z a = (m₀, lam₀, phi₀) ∧
      (∀ x ∈ Icc a b, HasDerivAt z (staticInvRadiusRHS P q x (z x)) x) ∧
      (∀ x ∈ Icc a b, 0 < (z x).2.1 ∧ 0 < 1 - 2 * x * (z x).1) ∧
      ((z b).1 < 0 ∨ 1 - 2 * b * (z b).1 < δ) := by
  obtain ⟨D, w, hD, hcD, haD, hw₀, hw, hwU, hmax⟩ :=
    static_inv_radius_exists_maximal P q a m₀ lam₀ phi₀ hlam₀ hg₀
  have hfst (x : ℝ) (hx : x ∈ D) : HasDerivAt (fun t => (w t).1) 1 x :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := w x)).comp_hasDerivAt x (hw x hx)
  have hcoord' : EqOn (fun x => (w x).1) id D := by
    apply hD.eqOn_of_deriv_eq hcD.isPreconnected
      (fun x hx => (hfst x hx).differentiableAt.differentiableWithinAt)
      differentiableOn_id (fun x hx => ?_) haD (by simp only [hw₀, id_eq])
    exact (hfst x hx).deriv.trans (hasDerivAt_id x).deriv.symm
  have hcoord : ∀ x ∈ D, (w x).1 = x := fun _ hx => hcoord' hx
  let z : ℝ → ℝ × ℝ × ℂ := fun x => (w x).2
  have hza : z a = (m₀, lam₀, phi₀) := by simp only [z, hw₀]
  have hz (x : ℝ) (hx : x ∈ D) :
      HasDerivAt z (staticInvRadiusRHS P q x (z x)) x := by
    simpa only [z, hcoord x hx, Function.comp_def, ContinuousLinearMap.coe_snd'] using!
      (hasFDerivAt_snd (𝕜 := ℝ) (p := w x)).comp_hasDerivAt x (hw x hx)
  have hpos (x : ℝ) (hx : x ∈ D) :
      0 < (z x).2.1 ∧ 0 < 1 - 2 * x * (z x).1 := by
    simpa only [z, hcoord x hx] using! hwU x hx
  have hpoint : ∃ b ∈ D, a ≤ b ∧ ((z b).1 < 0 ∨ 1 - 2 * b * (z b).1 < δ) := by
    by_contra hn
    have hsafe (t : ℝ) (ht : t ∈ D) (hat : a ≤ t) :
        0 ≤ (z t).1 ∧ δ ≤ 1 - 2 * t * (z t).1 := by
      constructor
      · by_contra hm
        exact hn ⟨t, ht, hat, Or.inl (lt_of_not_ge hm)⟩
      · by_contra hg
        exact hn ⟨t, ht, hat, Or.inr (lt_of_not_ge hg)⟩
    have hm₀ : 0 ≤ m₀ := by simpa only [hza] using (hsafe a haD le_rfl).1
    have hfull (B : ℝ) (hBa : a ≤ B) : Icc a B ⊆ D := by
      apply static_Icc_subset_domain_of_safe_maximal_solution ha hBa hδ
        hD hcD haD hw hwU hcoord
      · intro D' v hD' hcD' haD' hv₀ hv hvU
        exact (hmax D' v hD' hcD' haD' (hv₀.trans hw₀) hv hvU).1
      · exact fun t ht => hsafe t ht.1 ht.2.1
    have hmass_le (B : ℝ) (hBa : a ≤ B) (c : ℝ)
        (hc : ∀ t ∈ Icc a B, (staticInvRadiusRHS P q t (z t)).1 ≤ -c) :
        (z B).1 - m₀ ≤ -c * (B - a) := by
      have hm := fun t ht => static_mass_deriv_of_solution (hz t (hfull B hBa ht))
      have he := (convex_Icc a B).image_sub_le_mul_sub_of_deriv_le
        (HasDerivAt.continuousOn hm)
        (fun t ht => (hm t (interior_subset ht)).differentiableAt.differentiableWithinAt)
        (fun t ht => by rw [(hm t (interior_subset ht)).deriv]; exact hc t (interior_subset ht))
        a (left_mem_Icc.mpr hBa) B (right_mem_Icc.mpr hBa) hBa
      simpa only [hza] using he
    by_cases hq : q = 0
    · by_cases hP : P = 0
      · have hmne : m₀ ≠ 0 := by simpa only [hP, hq, ne_self_iff_false, false_or] using hactive
        have hmpos : 0 < m₀ := lt_of_le_of_ne hm₀ (Ne.symm hmne)
        let B := a + 1 / (2 * m₀)
        have hBa : a ≤ B := le_add_of_nonneg_right (by positivity)
        have hBD : B ∈ D := hfull B hBa (right_mem_Icc.mpr hBa)
        have hzero (t : ℝ) (ht : t ∈ D) : HasDerivAt (fun s => (z s).1) 0 t := by
          simpa only [hP, hq, norm_zero, pow_two, mul_zero, zero_div, sub_zero, neg_zero] using!
            static_mass_deriv_of_solution (hz t ht)
        have hmB : (z B).1 = m₀ := by
          have he := hD.is_const_of_deriv_eq_zero hcD.isPreconnected
            (fun t ht => (hzero t ht).differentiableAt.differentiableWithinAt)
            (fun t ht => (hzero t ht).deriv) hBD haD
          simpa only [hza] using he
        have hg := (hsafe B hBD hBa).2
        rw [hmB] at hg
        have heq : 2 * B * m₀ = 2 * a * m₀ + 1 := by
          dsimp only [B]; field_simp
        have hprod : 0 < 2 * a * m₀ := by positivity
        linarith only [hδ, hg, heq, hprod]
      · let c := δ * ‖P‖ ^ 2 / (8 * lam₀ ^ 2)
        have hcpos : 0 < c := by
          have := norm_pos_iff.mpr hP
          dsimp only [c]; positivity
        let B := a + (m₀ + 1) / c
        have hBa : a ≤ B := le_add_of_nonneg_right (div_nonneg (by linarith only [hm₀]) hcpos.le)
        have hl (t : ℝ) (ht : t ∈ Icc a B) :=
          (static_inv_radius_components_of_solution (hz t (hfull B hBa ht))).2.1
        have hanti : AntitoneOn (fun t => (z t).2.1) (Icc a B) := by
          apply antitoneOn_of_deriv_nonpos (convex_Icc a B) (HasDerivAt.continuousOn hl)
            (fun t ht => (hl t (interior_subset ht)).differentiableAt.differentiableWithinAt)
          intro t ht
          have htd := hfull B hBa (interior_subset ht)
          have hm := (hsafe t htd (interior_subset ht).1).1
          have hp := hpos t htd
          rw [(hl t (interior_subset ht)).deriv]
          simp only [hq, pow_two, zero_mul, sub_zero]
          exact div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp.1.le) (by positivity)) hp.2.le
        have hc : ∀ t ∈ Icc a B, (staticInvRadiusRHS P q t (z t)).1 ≤ -c := by
          intro t ht
          have htd := hfull B hBa ht
          have hp := hpos t htd
          have hgap := (hsafe t htd ht.1).2
          have hlam : (z t).2.1 ≤ lam₀ := by
            simpa only [hza] using hanti (left_mem_Icc.mpr hBa) ht ht.1
          have hlam2 := (sq_le_sq₀ hp.1.le hlam₀.le).mpr hlam
          have hr : c ≤ (1 - 2 * t * (z t).1) * ‖P‖ ^ 2 / (8 * (z t).2.1 ^ 2) := by
            calc
              c ≤ (1 - 2 * t * (z t).1) * ‖P‖ ^ 2 / (8 * lam₀ ^ 2) :=
                div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hgap (sq_nonneg _)) (by positivity)
              _ ≤ _ := div_le_div_of_nonneg_left
                (mul_nonneg hp.2.le (sq_nonneg _))
                (mul_pos (by norm_num) (sq_pos_of_pos hp.1))
                (mul_le_mul_of_nonneg_left hlam2 (by norm_num))
          simpa only [staticInvRadiusRHS, hq, pow_two, mul_zero, zero_div,
            sub_zero, neg_mul, neg_div] using
            neg_le_neg hr
        have he := hmass_le B hBa c hc
        have hid : c * (B - a) = m₀ + 1 := by dsimp only [B]; field_simp; ring
        rw [neg_mul, hid] at he
        have hmB := (hsafe B (hfull B hBa (right_mem_Icc.mpr hBa)) hBa).1
        linarith only [he, hmB]
    · let c := q ^ 2 / 2
      have hcpos : 0 < c := by dsimp only [c]; exact half_pos (sq_pos_of_ne_zero hq)
      let B := a + (m₀ + 1) / c
      have hBa : a ≤ B := le_add_of_nonneg_right (div_nonneg (by linarith only [hm₀]) hcpos.le)
      have he := hmass_le B hBa c (fun t ht =>
        static_mass_slope_le P q t (z t) (hpos t (hfull B hBa ht)).2.le)
      have hid : c * (B - a) = m₀ + 1 := by dsimp only [B]; field_simp; ring
      rw [neg_mul, hid] at he
      have hmB := (hsafe B (hfull B hBa (right_mem_Icc.mpr hBa)) hBa).1
      linarith only [he, hmB]
  obtain ⟨b, hbD, hab, hstrict⟩ := hpoint
  have hseg : Icc a b ⊆ D := hcD.out haD hbD
  exact ⟨b, hab, z, hza, fun x hx => hz x (hseg hx),
    fun x hx => hpos x (hseg hx), hstrict⟩

/-- [node prop:charged-observation#member-strict-static-barrier]
Every member of the normalized static family reaches a strict violation at a
positive physical radius `ρ ≤ L₀ = b⁻¹`. Expansion and gap remain positive on
its entire stopped interval. Initial inverse radius zero is allowed. The radius
and violation may depend on the member and `δgap`; no uniform constant is chosen
here. The hypotheses are precisely the outer reference's literal ODE and data. -/
theorem member_strict_static_barrier
    (δgap b x₀ M q : ℝ) (P : ℂ) (outer : ℝ → ℝ × ℝ × ℂ)
    (hδgap : δgap ∈ Ioo 0 1) (hb : 0 < b) (hx₀ : x₀ ∈ Icc 0 b)
    (_hM : 0 ≤ M) (hnorm : M + ‖P‖ + |q| = 1)
    (hinit : outer x₀ = (M, 1 / 2, P * x₀))
    (hsol : IsIntegralCurveOn outer (staticInvRadiusRHS P q) (Icc x₀ b))
    (hlam : 0 < (outer b).2.1) (hg : 0 < 1 - 2 * b * (outer b).1) :
    ∃ ρ ∈ Ioc 0 b⁻¹, ∃ z : ℝ → ℝ × ℝ × ℂ,
      z b = outer b ∧
      (∀ x ∈ Icc b ρ⁻¹,
        HasDerivAt z (staticInvRadiusRHS P q x (z x)) x ∧
        0 < (z x).2.1 ∧ 0 < 1 - 2 * x * (z x).1) ∧
      ((z ρ⁻¹).1 < 0 ∨ 1 - 2 * ρ⁻¹ * (z ρ⁻¹).1 < δgap) := by
  have hactive : P ≠ 0 ∨ q ≠ 0 ∨ (outer b).1 ≠ 0 := by
    by_cases hP : P = 0
    · by_cases hq : q = 0
      · right; right
        have hM1 : M = 1 := by
          simpa only [hP, hq, norm_zero, abs_zero, add_zero] using hnorm
        have hd (x : ℝ) (hx : x ∈ Icc x₀ b) :
            HasDerivWithinAt (fun t => (outer t).1) 0 (Icc x₀ b) x := by
          simpa only [Function.comp_def, ContinuousLinearMap.coe_fst', staticInvRadiusRHS,
            hP, hq, norm_zero, pow_two, mul_zero, zero_div, sub_zero, neg_zero] using!
              (hasFDerivAt_fst (𝕜 := ℝ) (p := outer x)).comp_hasDerivWithinAt x (hsol x hx)
        have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
          (fun _ _ => by simp : ∀ t ∈ Icc x₀ b, ‖(0 : ℝ)‖ ≤ 0)
          (convex_Icc x₀ b) (left_mem_Icc.mpr hx₀.2) (right_mem_Icc.mpr hx₀.2)
        have heq : (outer b).1 - (outer x₀).1 = 0 :=
          norm_le_zero_iff.mp (by simpa only [zero_mul] using he)
        rw [hinit, hM1] at heq
        linarith only [heq]
      · exact Or.inr (Or.inl hq)
    · exact Or.inl hP
  obtain ⟨B, hbB, z, hz₀, hz, hpos, hstrict⟩ :=
    static_member_barrier_of_nontrivial_data P q b (outer b).1 (outer b).2.1 δgap
      (outer b).2.2 hb hlam hg hδgap.1 hactive
  have hB : 0 < B := hb.trans_le hbB
  refine ⟨B⁻¹, ⟨inv_pos.mpr hB, (inv_le_inv₀ hB hb).mpr hbB⟩, z,
    by simpa using hz₀, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ Icc b B := by simpa only [inv_inv] using hx
    exact ⟨hz x hx', hpos x hx'⟩
  · simpa only [inv_inv] using hstrict

end EmcsfAcExtension.Global.Observation
