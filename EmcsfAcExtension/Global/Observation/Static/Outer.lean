module

public import EmcsfAcExtension.Global.Observation.Static.ODE
import EmcsfAcExtension.Infra.ODE.ParamDependence

/-!
# A uniform outer interval for static references

Compact uniform local existence is applied to the literal inverse-radius field.
All existence times precede the normalized reference data, including the initial
inverse radius zero. Source: `charged_SF_new_version.tex:L2196–L2227`.
-/

public section

open Set Metric Filter Topology
open scoped NNReal

namespace EmcsfAcExtension.Global

local notation "State" => (ℝ × ℝ × ℝ × ℂ)

private def outerBox : Set State :=
  {w | |w.1| < 1 / 32 ∧ |w.2.1| < 2 ∧
    w.2.2.1 ∈ Ioo (1 / 4) 1 ∧ ‖w.2.2.2‖ < 1}

private theorem outerBox_open : IsOpen outerBox := by
  have hx : Continuous (fun w : State => |w.1|) := by fun_prop
  have hm : Continuous (fun w : State => |w.2.1|) := by fun_prop
  have hl : Continuous (fun w : State => w.2.2.1) := by fun_prop
  have hphi : Continuous (fun w : State => ‖w.2.2.2‖) := by fun_prop
  exact (isOpen_lt hx continuous_const).inter
    ((isOpen_lt hm continuous_const).inter
      ((isOpen_Ioo.preimage hl).inter (isOpen_lt hphi continuous_const)))

private theorem outerBox_gap {w : State} (hw : w ∈ outerBox) :
    0 < w.2.2.1 ∧ 0 < 1 - 2 * w.1 * w.2.1 := by
  have hprod : |2 * w.1 * w.2.1| ≤ 1 / 8 := by
    calc
      |2 * w.1 * w.2.1| = 2 * |w.1| * |w.2.1| := by
        rw [abs_mul, abs_mul]; norm_num
      _ ≤ 2 * (1 / 32) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hw.1.le (by norm_num)) hw.2.1.le
          (abs_nonneg _) (by norm_num)
      _ = 1 / 8 := by norm_num
  exact ⟨lt_trans (by norm_num) hw.2.2.1.1,
    by linarith only [(le_abs_self (2 * w.1 * w.2.1)).trans hprod]⟩

/-- [internal]
A universal outer existence time, uniform over all bounded normalized data and
over the variable initial inverse radius, including zero. The bounds describe
one fixed nondegenerate box, independent of scalar phase and charge. This is an
existence statement; trajectories are not defined before it. -/
theorem static_outer_exists :
    ∃ a > 0, a ≤ (1 / 128 : ℝ) ∧
      ∀ (P : ℂ) (q M x₀ : ℝ), ‖P‖ ≤ 1 → |q| ≤ 1 →
        M ∈ Icc 0 1 → x₀ ∈ Icc 0 a →
        ∃ z : ℝ → ℝ × ℝ × ℂ,
          z x₀ = (M, 1 / 2, P * x₀) ∧
          IsIntegralCurveOn z (staticInvRadiusRHS P q) (Icc (x₀ - 2 * a) (x₀ + 2 * a)) ∧
          ∀ x ∈ Icc (x₀ - 2 * a) (x₀ + 2 * a),
            |x| < 1 / 32 ∧ |(z x).1| < 2 ∧
            (z x).2.1 ∈ Ioo (1 / 4) 1 ∧
            0 < 1 - 2 * x * (z x).1 ∧ ‖(z x).2.2‖ < 1 := by
  let S : Set (ℂ × ℝ) := closedBall 0 1 ×ˢ Icc (-1) 1
  let C : Set State := Icc 0 (1 / 128) ×ˢ Icc 0 1 ×ˢ
    ({1 / 2} : Set ℝ) ×ˢ closedBall 0 (1 / 128)
  have hS : IsCompact S := (isCompact_closedBall _ _).prod isCompact_Icc
  have hC : IsCompact C := isCompact_Icc.prod
    (isCompact_Icc.prod (isCompact_singleton.prod (isCompact_closedBall _ _)))
  have hCU : C ⊆ outerBox := by
    intro w hw
    have hx : |w.1| ≤ 1 / 128 := abs_le.mpr ⟨by linarith only [hw.1.1], hw.1.2⟩
    have hm : |w.2.1| ≤ 1 := abs_le.mpr ⟨by linarith only [hw.2.1.1], hw.2.1.2⟩
    have hlam : w.2.2.1 = 1 / 2 := hw.2.2.1
    have hphi : ‖w.2.2.2‖ ≤ 1 / 128 := by simpa using hw.2.2.2
    exact ⟨by linarith only [hx], by linarith only [hm], by rw [hlam]; norm_num,
      by linarith only [hphi]⟩
  have hc : ContinuousOn
      (fun w : ℝ × (ℂ × ℝ) × State =>
        ((1 : ℝ), staticInvRadiusRHS w.2.1.1 w.2.1.2 w.2.2.1 w.2.2.2))
      (univ ×ˢ S ×ˢ outerBox) := by
    intro w hw
    obtain ⟨hlam, hg⟩ := outerBox_gap hw.2.2
    have hmap : ContinuousAt (fun v : ℝ × (ℂ × ℝ) × State => v.2) w :=
      continuous_snd.continuousAt
    exact ((static_inv_radius_joint_contDiffAt w.2.1 w.2.2
      (ne_of_gt hlam) (ne_of_gt hg)).continuousAt.comp (f := fun v : ℝ × (ℂ × ℝ) × State => v.2)
        hmap).continuousWithinAt
  have hl : ∀ w ∈ outerBox, ∀ p ∈ S,
      ∃ (V : Set (ℂ × ℝ)) (r d : ℝ) (K : ℝ≥0),
        IsOpen V ∧ p ∈ V ∧ 0 < r ∧ 0 < d ∧
        ∀ q ∈ S ∩ V, ∀ t ∈ Icc (-d) d,
          LipschitzOnWith K
            (fun v : State => ((1 : ℝ), staticInvRadiusRHS q.1 q.2 v.1 v.2))
            (closedBall w r) := by
    intro w hw p _
    obtain ⟨hlam, hg⟩ := outerBox_gap hw
    obtain ⟨V, r, K, hV, hpV, hr, hK⟩ :=
      static_inv_radius_local_lipschitz p w hlam hg
    exact ⟨V, r, 1, K, hV, hpV, hr, zero_lt_one, fun q hq _ _ => hK q hq.2⟩
  obtain ⟨ε, hε, hsol⟩ := ODE.exists_uniform_local_solution_of_continuousOn
    hS outerBox_open hC hCU hc 0 (by simpa only [zero_sub, zero_add] using hl)
  let a : ℝ := min (ε / 2) (1 / 128)
  have ha : 0 < a := lt_min (half_pos hε) (by norm_num)
  have ha2ε : 2 * a ≤ ε := by
    have h := min_le_left (ε / 2) (1 / 128 : ℝ)
    linarith only [h]
  have haε : a ≤ ε := by linarith only [ha.le, ha2ε]
  have ha128 : a ≤ 1 / 128 := min_le_right _ _
  refine ⟨a, ha, ha128, fun P q M x₀ hP hq hM hx₀ => ?_⟩
  have hp : (P, q) ∈ S := ⟨by simpa using hP, abs_le.mp hq⟩
  have hinit : (x₀, M, 1 / 2, P * x₀) ∈ C := by
    refine ⟨⟨hx₀.1, hx₀.2.trans ha128⟩, hM, rfl, ?_⟩
    rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hx₀.1]
    exact (mul_le_of_le_one_left hx₀.1 hP).trans (hx₀.2.trans ha128)
  obtain ⟨w, hw₀, hw, hwU⟩ := hsol x₀
    (by constructor <;> simp only [zero_sub, zero_add] <;>
      linarith only [hx₀.1, hx₀.2, hε, haε]) (P, q) hp
      (x₀, M, 1 / 2, P * x₀) hinit
  have hsub : Icc (x₀ - 2 * a) (x₀ + 2 * a) ⊆ Icc (x₀ - ε) (x₀ + ε) :=
    Icc_subset_Icc (by linarith only [ha2ε]) (by linarith only [ha2ε])
  have hcoord : ∀ x ∈ Icc (x₀ - ε) (x₀ + ε), (w x).1 = x :=
    static_inv_radius_coordinate_of_solution ⟨by linarith only [hε],
      by linarith only [hε]⟩ hw (by rw [hw₀])
  refine ⟨fun x => (w x).2, by simp only [hw₀], ?_, ?_⟩
  · intro x hx
    have hd := (hasFDerivAt_snd (𝕜 := ℝ) (p := w x)).comp_hasDerivWithinAt x
      (hw x (hsub hx))
    have hd' := hd.mono hsub
    simpa only [hcoord x (hsub hx), Function.comp_def, ContinuousLinearMap.coe_snd']
      using hd'
  · intro x hx
    have hbox := hwU (hsub hx)
    obtain ⟨_, hg⟩ := outerBox_gap hbox
    simpa only [hcoord x (hsub hx)] using
      (show |(w x).1| < 1 / 32 ∧ |(w x).2.1| < 2 ∧
        (w x).2.2.1 ∈ Ioo (1 / 4) 1 ∧
        0 < 1 - 2 * (w x).1 * (w x).2.1 ∧ ‖(w x).2.2.2‖ < 1 from
          ⟨hbox.1, hbox.2.1, hbox.2.2.1, hg, hbox.2.2.2⟩)

/-- [internal]
The universal outer bound `5` for the expansion component of the literal ODE.
It is independent of the normalized scalar amplitude, charge, and starting point. -/
theorem static_inv_radius_outer_lam_bound (q x m lam : ℝ) (hq : |q| ≤ 1) (hx : |x| ≤ 1 / 32)
    (hm : |m| ≤ 2) (hlam : lam ∈ Icc (1 / 4) 1) :
    |-lam * (2 * m - q ^ 2 * x) / (1 - 2 * x * m)| ≤ 5 := by
  have hq2 : q ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg q) zero_le_one).mpr hq
  have hprod : |2 * x * m| ≤ 1 / 8 := by
    calc
      |2 * x * m| = 2 * |x| * |m| := by rw [abs_mul, abs_mul]; norm_num
      _ ≤ 2 * (1 / 32) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hx (by norm_num)) hm
          (abs_nonneg _) (by norm_num)
      _ = 1 / 8 := by norm_num
  have hgap : 7 / 8 ≤ 1 - 2 * x * m := by linarith only [le_abs_self (2*x*m), hprod]
  have hnum : |2 * m - q ^ 2 * x| ≤ 4 + 1 / 32 := by
    calc
      |2 * m - q ^ 2 * x| ≤ |2 * m| + |q ^ 2 * x| := abs_sub _ _
      _ = 2 * |m| + q ^ 2 * |x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg q)]; norm_num
      _ ≤ 2 * 2 + 1 * (1 / 32) :=
        add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num))
          (mul_le_mul hq2 hx (abs_nonneg _) zero_le_one)
      _ = 4 + 1 / 32 := by ring
  rw [abs_div, abs_mul, abs_neg, abs_of_pos (show 0 < lam by linarith only [hlam.1]),
    abs_of_pos (show 0 < 1 - 2 * x * m by linarith only [hgap])]
  apply (div_le_iff₀ (by linarith only [hgap] : 0 < 1 - 2 * x * m)).mpr
  have hmul : lam * |2 * m - q ^ 2 * x| ≤ 1 * (4 + 1 / 32) :=
    mul_le_mul hlam.2 hnum (abs_nonneg _) zero_le_one
  linarith only [hmul, hgap]

/-- [internal]
The scalar component of the literal ODE has norm at most twice the amplitude
on the universal outer expansion box. The factor `2` is universal. -/
theorem static_inv_radius_outer_phi_bound (P : ℂ) (lam : ℝ)
    (hlam : (1 / 4 : ℝ) ≤ lam) :
    ‖P / ((2 * lam : ℝ) : ℂ)‖ ≤ 2 * ‖P‖ := by
  have hden : 0 < 2 * lam := by linarith only [hlam]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  have hp := mul_nonneg (norm_nonneg P)
    (show 0 ≤ 4 * lam - 1 by linarith only [hlam])
  nlinarith only [hp]

/-- [internal]
Uniform scalar estimates on an outer static interval. The constants `4` and
`40` are universal, independent of the normalized data and initial inverse
radius. The second expression is the radial derivative of `r * φ`. -/
theorem static_outer_scalar_bounds_of_solution (P : ℂ) (q M x₀ b : ℝ)
    (z : ℝ → ℝ × ℝ × ℂ) (hP : ‖P‖ ≤ 1) (hq : |q| ≤ 1)
    (hx₀ : 0 ≤ x₀) (_hxb : x₀ ≤ b)
    (hz₀ : z x₀ = (M, 1 / 2, P * x₀))
    (hz : ∀ x ∈ Icc x₀ b, HasDerivAt z (staticInvRadiusRHS P q x (z x)) x)
    (hbox : ∀ x ∈ Icc x₀ b, |x| ≤ 1 / 32 ∧ |(z x).1| ≤ 2 ∧
      (z x).2.1 ∈ Icc (1 / 4) 1) :
    ∀ x ∈ Icc x₀ b,
      ‖(z x).2.2‖ + ‖(P / ((2 * (z x).2.1 : ℝ) : ℂ)) * x‖ ≤ 4 * x ∧
      ‖(z x).2.2 - (P / ((2 * (z x).2.1 : ℝ) : ℂ)) * x‖ ≤ 40 * x ^ 2 := by
  let A : ℝ → ℂ := fun x => P / ((2 * (z x).2.1 : ℝ) : ℂ)
  let dl : ℝ → ℝ := fun x =>
    -(z x).2.1 * (2 * (z x).1 - q ^ 2 * x) / (1 - 2 * x * (z x).1)
  let dA : ℝ → ℂ := fun x =>
    (-P * ((2 * dl x : ℝ) : ℂ)) / ((2 * (z x).2.1 : ℝ) : ℂ) ^ 2
  have hcomp := fun x hx => static_inv_radius_components_of_solution (hz x hx)
  have hA (x : ℝ) (hx : x ∈ Icc x₀ b) : HasDerivAt A (dA x) x := by
    have hden : ((2 * (z x).2.1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show 2 * (z x).2.1 ≠ 0 by
        have := (hbox x hx).2.2.1
        positivity)
    simpa only [A, dA, dl, Pi.div_def, zero_mul, zero_sub, neg_mul] using!
      (hasDerivAt_const x P).div
        (((hcomp x hx).2.1.const_mul 2).ofReal_comp) hden
  have hAnorm (x : ℝ) (hx : x ∈ Icc x₀ b) : ‖dA x‖ ≤ 40 := by
    have hlam := (hbox x hx).2.2
    have hdl : |dl x| ≤ 5 :=
      static_inv_radius_outer_lam_bound q x (z x).1 (z x).2.1 hq
        (hbox x hx).1 (hbox x hx).2.1 hlam
    have hnum : ‖P‖ * |2 * dl x| ≤ 10 := by
      have hd2 : |2 * dl x| ≤ 10 := by
        rw [abs_mul]
        norm_num
        linarith only [hdl]
      exact (mul_le_mul hP hd2 (abs_nonneg _) zero_le_one).trans_eq (by norm_num)
    have hden : (1 / 4 : ℝ) ≤ |2 * (z x).2.1| ^ 2 := by
      rw [sq_abs]
      nlinarith only [hlam.1, sq_nonneg (2 * (z x).2.1 - 1 / 2)]
    simp only [dA, norm_div, norm_mul, norm_neg, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, ← abs_mul]
    apply (div_le_iff₀ (by linarith only [hden] : 0 < |2 * (z x).2.1| ^ 2)).mpr
    linarith only [hnum, hden]
  have hφnorm (x : ℝ) (hx : x ∈ Icc x₀ b) : ‖(z x).2.2‖ ≤ 2 * ‖P‖ * x := by
    have hsub : Icc x₀ x ⊆ Icc x₀ b := Icc_subset_Icc le_rfl hx.2
    have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hcomp t (hsub ht)).2.2.hasDerivWithinAt)
      (fun t ht => static_inv_radius_outer_phi_bound P (z t).2.1 (hbox t (hsub ht)).2.2.1)
      (convex_Icc x₀ x) (left_mem_Icc.mpr hx.1) (right_mem_Icc.mpr hx.1)
    have hinitnorm : ‖(z x₀).2.2‖ = ‖P‖ * x₀ := by
      simp only [hz₀, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx₀]
    have hdiff : ‖(z x).2.2 - (z x₀).2.2‖ ≤ 2 * ‖P‖ * (x - x₀) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx.1)] using he
    have ht := (norm_le_norm_sub_add (z x).2.2 (z x₀).2.2).trans
      (add_le_add hdiff hinitnorm.le)
    nlinarith only [ht, mul_nonneg (norm_nonneg P) hx₀]
  intro x hx
  have hxpos : 0 ≤ x := hx₀.trans hx.1
  have hAx : ‖A x * (x : ℂ)‖ ≤ 2 * ‖P‖ * x := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxpos]
    exact mul_le_mul_of_nonneg_right
      (static_inv_radius_outer_phi_bound P (z x).2.1 (hbox x hx).2.2.1) hxpos
  refine ⟨?_, ?_⟩
  · have hsum := add_le_add (hφnorm x hx) hAx
    have hmult : ‖P‖ * x ≤ x := mul_le_of_le_one_left hxpos hP
    dsimp only [A] at hAx
    nlinarith only [hsum, hmult]
  · let f : ℝ → ℂ := fun t => (z t).2.2 - A t * t
    have hsub : Icc x₀ x ⊆ Icc x₀ b := Icc_subset_Icc le_rfl hx.2
    have hf (t : ℝ) (ht : t ∈ Icc x₀ x) :
        HasDerivWithinAt f (-dA t * (t : ℂ)) (Icc x₀ x) t := by
      have hd := (hcomp t (hsub ht)).2.2.sub
        ((hA t (hsub ht)).mul (hasDerivAt_id t).ofReal_comp)
      convert hd.hasDerivWithinAt using 1
      · simp only [f, Pi.sub_def, Pi.mul_apply, id_eq]
      · change -dA t * (t : ℂ) = A t - (dA t * (t : ℂ) + A t * (1 : ℂ))
        ring
    have hfbound (t : ℝ) (ht : t ∈ Icc x₀ x) : ‖-dA t * (t : ℂ)‖ ≤ 40 * x := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hx₀.trans ht.1)]
      exact mul_le_mul (hAnorm t (hsub ht)) ht.2 (hx₀.trans ht.1) (by norm_num)
    have hf₀ : f x₀ = 0 := by
      simp [f, A, hz₀]
    have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hfbound
      (convex_Icc x₀ x) (left_mem_Icc.mpr hx.1) (right_mem_Icc.mpr hx.1)
    have he' : ‖f x‖ ≤ 40 * x * (x - x₀) := by
      simpa only [hf₀, sub_zero, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hx.1)] using he
    change ‖f x‖ ≤ 40 * x ^ 2
    nlinarith only [he', mul_nonneg hxpos hx₀]

/-- [node eq:co-static-outer]
Universal outer estimates, in the regular inverse-radius coordinate `x = 1/r`.
The outer cutoff is `b = L₀⁻¹` and the initial point is `x₀ = L⁻¹`; zero is
included. Thus `a⁻¹` is a universal `L_out ≥ 128`. The constant `C` and cutoff
`a` precede all normalized parameters, and no actual solution data occur.
The radial scalar ratio is `y = -(P / (2 * λ)) * x`.
-/
theorem co_static_outer :
    ∃ a > 0, ∃ C > 0, a ≤ (1 / 128 : ℝ) ∧ ∀ b ∈ Ioc 0 a,
      ∀ (P : ℂ) (q M x₀ : ℝ), 0 ≤ M → M + ‖P‖ + |q| = 1 → x₀ ∈ Icc 0 b →
      ∃ z : ℝ → ℝ × ℝ × ℂ, z x₀ = (M, 1 / 2, P * x₀) ∧
        ∀ x ∈ Icc x₀ b,
          HasDerivAt z (staticInvRadiusRHS P q x (z x)) x ∧
          (z x).2.1 ∈ Icc (1 / 4) 1 ∧ |(z x).1| ≤ 2 ∧
          1 / 2 ≤ 1 - 2 * x * (z x).1 ∧
          ‖(z x).2.2‖ + ‖(P / ((2 * (z x).2.1 : ℝ) : ℂ)) * x‖ ≤ C * x ∧
          ‖(z x).2.2 - (P / ((2 * (z x).2.1 : ℝ) : ℂ)) * x‖ ≤ C * x ^ 2 ∧
          (0 < x →
            HasDerivAt (fun r : ℝ => (r : ℂ) * (z r⁻¹).2.2)
              ((z x).2.2 - (P / ((2 * (z x).2.1 : ℝ) : ℂ)) * x) x⁻¹ ∧
            ‖deriv (fun r : ℝ => (r : ℂ) * (z r⁻¹).2.2) x⁻¹‖ ≤ C * x ^ 2) := by
  obtain ⟨a, ha, ha128, hsol⟩ := static_outer_exists
  refine ⟨a, ha, 40, by norm_num, ha128, fun b hb P q M x₀ hM hnorm hx₀ => ?_⟩
  have hP : ‖P‖ ≤ 1 := by linarith only [hM, hnorm, abs_nonneg q]
  have hq : |q| ≤ 1 := by linarith only [hM, hnorm, norm_nonneg P]
  have hM1 : M ≤ 1 := by linarith only [hnorm, norm_nonneg P, abs_nonneg q]
  obtain ⟨z, hz₀, hz, hbox⟩ := hsol P q M x₀ hP hq ⟨hM, hM1⟩
    ⟨hx₀.1, hx₀.2.trans hb.2⟩
  have hsub : Icc x₀ b ⊆ Icc (x₀ - 2 * a) (x₀ + 2 * a) := by
    apply Icc_subset_Icc <;> linarith only [ha.le, hb.2, hx₀.1]
  have hzAt (x : ℝ) (hx : x ∈ Icc x₀ b) :
      HasDerivAt z (staticInvRadiusRHS P q x (z x)) x := by
    apply (hz x (hsub hx)).hasDerivAt
    exact Icc_mem_nhds (by linarith only [hx.1, ha])
      (by linarith only [hx.2, hb.2, hx₀.1, ha])
  have hbounds (x : ℝ) (hx : x ∈ Icc x₀ b) :
      |x| ≤ 1 / 32 ∧ |(z x).1| ≤ 2 ∧ (z x).2.1 ∈ Icc (1 / 4) 1 := by
    have h := hbox x (hsub hx)
    exact ⟨h.1.le, h.2.1.le, ⟨h.2.2.1.1.le, h.2.2.1.2.le⟩⟩
  have hscalar := static_outer_scalar_bounds_of_solution P q M x₀ b z hP hq
    hx₀.1 hx₀.2 hz₀ hzAt hbounds
  refine ⟨z, hz₀, fun x hx => ?_⟩
  have hprod : |2 * x * (z x).1| ≤ 1 / 8 := by
    calc
      |2 * x * (z x).1| = 2 * |x| * |(z x).1| := by
        rw [abs_mul, abs_mul]; norm_num
      _ ≤ 2 * (1 / 32) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hbounds x hx).1 (by norm_num))
          (hbounds x hx).2.1 (abs_nonneg _) (by norm_num)
      _ = 1 / 8 := by norm_num
  refine ⟨hzAt x hx, (hbounds x hx).2.2, (hbounds x hx).2.1,
    by linarith only [le_abs_self (2 * x * (z x).1), hprod],
    (hscalar x hx).1.trans ?_, (hscalar x hx).2, fun hxp => ?_⟩
  · nlinarith only [hx₀.1.trans hx.1]
  · have hd := static_radial_weighted_scalar_deriv_of_solution hxp (hzAt x hx)
    exact ⟨hd, by rw [hd.deriv]; exact (hscalar x hx).2⟩

end EmcsfAcExtension.Global
