module

public import EmcsfAcExtension.Global.Observation.Static.CompactFamily
public import EmcsfAcExtension.Global.Observation.Static.MemberBarrier
import EmcsfAcExtension.Infra.ODE.ParamDependence

/-!
# Uniform strict static barriers

Finite-time ODE stability preserves each strict member-dependent barrier.
The infrastructure's finite-subcover theorem selects common positive radius
and violation bounds, with coefficient bounds only on each selected stopped
interval. No reference is followed down to another member's smaller radius.
Source: `charged_SF_new_version.tex:L2263–L2263` and internal project record's uniform-family
paragraph.
-/

public section

open Set Metric Filter Topology
open scoped NNReal

namespace EmcsfAcExtension.Global.Observation

local notation "Param" => (ℝ × ℂ × ℝ × ℝ)
local notation "State" => (ℝ × ℝ × ℝ × ℂ)

private noncomputable def stateDomain : Set State :=
  {w | 0 < w.2.2.1 ∧ 0 < 1 - 2 * w.1 * w.2.1}

private noncomputable def staticField (_ : ℝ) (p : Param) (w : State) : State :=
  (1, staticInvRadiusRHS p.2.1 p.2.2.1 w.1 w.2)

private noncomputable def coefficients (p : Param) (w : State) : ℝ :=
  ‖w‖ + |w.2.2.1⁻¹| + |(1 - 2 * w.1 * w.2.1)⁻¹| +
    ‖(p.2.1 / ((2 * w.2.2.1 : ℝ) : ℂ)) * w.1‖ +
    |(2 * w.1 * w.2.1 - p.2.2.1 ^ 2 * w.1 ^ 2) / (1 - 2 * w.1 * w.2.1)|

private noncomputable def violation (δ : ℝ) (w : State) : ℝ :=
  max (-w.2.1) (δ - (1 - 2 * w.1 * w.2.1))

private theorem stateDomain_open : IsOpen stateDomain :=
  (isOpen_lt continuous_const continuous_snd.snd.fst).inter
    (isOpen_lt continuous_const
      (show Continuous (fun w : State => 1 - 2 * w.1 * w.2.1) by fun_prop))

private theorem staticField_continuous (S : Set Param) :
    ContinuousOn (fun w : ℝ × Param × State => staticField w.1 w.2.1 w.2.2)
      (univ ×ˢ S ×ˢ stateDomain) := by
  intro w hw
  have hmap : ContinuousAt
      (fun w : ℝ × Param × State => ((w.2.1.2.1, w.2.1.2.2.1), w.2.2)) w := by
    fun_prop
  exact ((static_inv_radius_joint_contDiffAt (w.2.1.2.1, w.2.1.2.2.1) w.2.2
    (ne_of_gt hw.2.2.1) (ne_of_gt hw.2.2.2)).continuousAt.comp
      (f := fun w : ℝ × Param × State => ((w.2.1.2.1, w.2.1.2.2.1), w.2.2))
      hmap).continuousWithinAt

private theorem staticField_local_lipschitz (S : Set Param) :
    ∀ t : ℝ, ∀ p ∈ S, ∀ w ∈ stateDomain,
      ∃ (V : Set Param) (R d : ℝ) (K : ℝ≥0),
        IsOpen V ∧ p ∈ V ∧ 0 < R ∧ 0 < d ∧
        ∀ q ∈ S ∩ V, ∀ s ∈ Icc (t - d) (t + d),
          LipschitzOnWith K (staticField s q) (closedBall w R) := by
  intro t p _ w hw
  obtain ⟨V, R, K, hV, hpV, hR, hK⟩ :=
    static_inv_radius_local_lipschitz (p.2.1, p.2.2.1) w hw.1 hw.2
  exact ⟨(fun p : Param => (p.2.1, p.2.2.1)) ⁻¹' V, R, 1, K,
    hV.preimage (by fun_prop), hpV, hR, zero_lt_one, fun q hq _ _ =>
      hK (q.2.1, q.2.2.1) hq.2⟩

private theorem coefficients_continuous (S : Set Param) :
    ContinuousOn (fun w : Param × State => coefficients w.1 w.2)
      (S ×ˢ stateDomain) := by
  intro w hw
  have hlam : w.2.2.2.1 ≠ 0 := ne_of_gt hw.2.1
  have hg : 1 - 2 * w.2.1 * w.2.2.1 ≠ 0 := ne_of_gt hw.2.2
  have hcast : ((2 * w.2.2.2.1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hlam)
  unfold coefficients
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := first | assumption | norm_num)

private theorem violation_continuous (δ : ℝ) : Continuous (violation δ) := by
  unfold violation
  fun_prop

private theorem barrier_patch_of_reference
    {S : Set Param} {a B δ : ℝ} {p : Param} {z : ℝ → State} {f : Param → State}
    (hS : IsCompact S) (hp : p ∈ S) (haB : a ≤ B) (hf : ContinuousOn f S)
    (hz : IsIntegralCurveOn z (fun t => staticField t p) (Icc a B))
    (hzU : MapsTo z (Icc a B) stateDomain) (hz₀ : z a = f p)
    (hstrict : 0 < violation δ (z B)) :
    ∃ (V : Set Param) (γ C : ℝ), IsOpen V ∧ p ∈ V ∧ 0 < γ ∧ 0 < C ∧
      ∀ q ∈ S ∩ V, ∃ y : ℝ → State,
        y a = f q ∧ IsIntegralCurveOn y (fun t => staticField t q) (Icc a B) ∧
        MapsTo y (Icc a B) stateDomain ∧
        (∀ t ∈ Icc a B, coefficients q (y t) ≤ C) ∧ γ ≤ violation δ (y B) := by
  let A := z '' Icc a B
  have hA : IsCompact A := isCompact_Icc.image_of_continuousOn hz.continuousOn
  obtain ⟨R, hR, hRU⟩ := hA.exists_cthickening_subset_open stateDomain_open
    (image_subset_iff.mpr hzU)
  let T := cthickening (R / 2) A
  have hT : IsCompact T := hA.cthickening
  have hTU : T ⊆ stateDomain :=
    (cthickening_mono (by linarith only [hR.le] : R / 2 ≤ R) A).trans hRU
  let γ := violation δ (z B) / 2
  have hγ : 0 < γ := half_pos hstrict
  have hnb : {w | γ < violation δ w} ∈ 𝓝 (z B) :=
    (violation_continuous δ).continuousAt.preimage_mem_nhds
      (Ioi_mem_nhds (half_lt_self hstrict))
  obtain ⟨r, hr, hrv⟩ := Metric.mem_nhds_iff.mp hnb
  let ε := min (R / 2) r
  have hε : 0 < ε := lt_min (half_pos hR) hr
  have he := ODE.eventually_exists_solution_of_locally_lipschitz haB hp hS
    stateDomain_open (staticField_continuous S) (staticField_local_lipschitz S)
    hz hzU (hf p hp) hz₀.symm ε hε
  obtain ⟨V, hV, hpV, hVe⟩ := mem_nhdsWithin.mp he
  have hc : ContinuousOn (fun w : Param × State => coefficients w.1 w.2) (S ×ˢ T) :=
    (coefficients_continuous S).mono (prod_mono Subset.rfl hTU)
  obtain ⟨C₀, hC₀⟩ := (hS.prod hT).exists_bound_of_continuousOn hc
  let C := max C₀ 1
  have hC : 0 < C := zero_lt_one.trans_le (le_max_right _ _)
  refine ⟨V, γ, C, hV, hpV, hγ, hC, fun q hq => ?_⟩
  obtain ⟨y, hy₀, hy, hyU, hyd⟩ := hVe ⟨hq.2, hq.1⟩
  have hyT (t : ℝ) (ht : t ∈ Icc a B) : y t ∈ T := by
    apply closedBall_subset_cthickening (mem_image_of_mem z ht) (R / 2)
    exact mem_closedBall.mpr ((hyd t ht).le.trans (min_le_left _ _))
  refine ⟨y, hy₀, hy, hyU, fun t ht => ?_, ?_⟩
  · exact ((le_abs_self (coefficients q (y t))).trans
      (hC₀ (q, y t) ⟨hq.1, hyT t ht⟩)).trans (le_max_left _ _)
  · apply le_of_lt
    apply hrv
    exact mem_ball.mpr ((hyd B (right_mem_Icc.mpr haB)).trans_le (min_le_right _ _))

/-- [internal]
Uniform stopped barriers for a fixed outer cutoff and continuous reference-data
family. The constants may depend on `δgap`, `b`, and this fixed family; they are
chosen before its member. This lets callers enlarge `L₀ = b⁻¹` for the outer
absorptions before selecting barriers. The canonical theorem below discharges
all family hypotheses from compact static existence. -/
theorem uniform_static_barriers_of_outer_family (δgap b : ℝ)
    (hδgap : δgap ∈ Ioo 0 1) (hb : 0 < b) (outer : Param → ℝ → ℝ × ℝ × ℂ)
    (hout : ∀ p ∈ {p : Param | 0 ≤ p.1 ∧
      p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 b},
      outer p p.2.2.2 = (p.1, 1 / 2, p.2.1 * p.2.2.2) ∧
      IsIntegralCurveOn (outer p) (staticInvRadiusRHS p.2.1 p.2.2.1) (Icc p.2.2.2 b))
    (hcontinuous : ContinuousOn (fun p => outer p b)
      {p : Param | 0 ≤ p.1 ∧ p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 b})
    (hpositive : ∀ p ∈ {p : Param | 0 ≤ p.1 ∧
      p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 b},
      0 < (outer p b).2.1 ∧ 0 < 1 - 2 * b * (outer p b).1) :
    ∃ r > 0, ∃ γ > 0, ∃ C > 0,
      ∀ p ∈ {p : Param | 0 ≤ p.1 ∧
        p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 b},
      ∃ ρ ∈ Icc r b⁻¹, ∃ z : ℝ → ℝ × ℝ × ℂ,
        z b = outer p b ∧
        IsIntegralCurveOn z (staticInvRadiusRHS p.2.1 p.2.2.1) (Icc b ρ⁻¹) ∧
        (∀ x ∈ Icc b ρ⁻¹, 0 < (z x).2.1 ∧ 0 < 1 - 2 * x * (z x).1 ∧
          ‖(x, z x)‖ + |(z x).2.1⁻¹| + |(1 - 2 * x * (z x).1)⁻¹| +
            ‖(p.2.1 / ((2 * (z x).2.1 : ℝ) : ℂ)) * x‖ +
            |(2 * x * (z x).1 - p.2.2.1 ^ 2 * x ^ 2) / (1 - 2 * x * (z x).1)| ≤ C) ∧
        ((z ρ⁻¹).1 ≤ -γ ∨ 1 - 2 * ρ⁻¹ * (z ρ⁻¹).1 ≤ δgap - γ) := by
  classical
  let S : Set Param := {p | 0 ≤ p.1 ∧
    p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 b}
  let f : Param → State := fun p => (b, outer p b)
  have hS : IsCompact S := static_parameters_isCompact b
  have hf : ContinuousOn f S := continuousOn_const.prodMk hcontinuous
  have houter (p : Param) (hp : p ∈ S) := (hout p hp).2
  have hpatch (p : S) : ∃ (ρ : ℝ) (V : Set Param) (γ C : ℝ),
      ρ ∈ Ioc 0 b⁻¹ ∧ IsOpen V ∧ (p : Param) ∈ V ∧ 0 < γ ∧ 0 < C ∧
      ∀ q ∈ S ∩ V, ∃ y : ℝ → State, y b = f q ∧
        IsIntegralCurveOn y (fun t => staticField t q) (Icc b ρ⁻¹) ∧
        MapsTo y (Icc b ρ⁻¹) stateDomain ∧
        (∀ t ∈ Icc b ρ⁻¹, coefficients q (y t) ≤ C) ∧ γ ≤ violation δgap (y ρ⁻¹) := by
    obtain ⟨ρ, hρ, z, hz₀, hz, hstrict⟩ := member_strict_static_barrier δgap b p.1.2.2.2
      p.1.1 p.1.2.2.1 p.1.2.1 (outer p) hδgap hb p.2.2.2 p.2.1 p.2.2.1
      (hout p p.2).1 (houter p p.2) (hpositive p p.2).1 (hpositive p p.2).2
    have haρ : b ≤ ρ⁻¹ := by
      simpa only [inv_inv] using (inv_le_inv₀ (inv_pos.mpr hb) hρ.1).mpr hρ.2
    let w : ℝ → State := fun t => (t, z t)
    have hw : IsIntegralCurveOn w (fun t => staticField t p) (Icc b ρ⁻¹) :=
      fun t ht => (hasDerivWithinAt_id t _).prodMk (hz t ht).1.hasDerivWithinAt
    have hwU : MapsTo w (Icc b ρ⁻¹) stateDomain := fun t ht => (hz t ht).2
    have hw₀ : w b = f p := by dsimp only [w, f]; rw [hz₀]
    have hv : 0 < violation δgap (w ρ⁻¹) := by
      rcases hstrict with hm | hg
      · exact lt_max_of_lt_left (neg_pos.mpr hm)
      · exact lt_max_of_lt_right (sub_pos.mpr hg)
    obtain ⟨V, γ, C, hV, hpV, hγ, hC, hnear⟩ :=
      barrier_patch_of_reference hS p.2 haρ hf hw hwU hw₀ hv
    exact ⟨ρ, V, γ, C, hρ, hV, hpV, hγ, hC, hnear⟩
  choose ρ V margin bound hρ hV hpV hmargin hbound hnear using hpatch
  obtain ⟨s, r, γ, C, hr, hγ, hC, hbounds, hcover⟩ :=
    ODE.exists_uniform_strict_margins_of_open_cover hS V ρ bound
      (fun i _ => margin i) hV (fun _ => continuousOn_const) (by
        intro p hp
        exact ⟨⟨p, hp⟩, hpV ⟨p, hp⟩, (hρ ⟨p, hp⟩).1, hmargin ⟨p, hp⟩⟩)
  refine ⟨r, hr, γ, hγ, C, hC, fun p hp => ?_⟩
  obtain ⟨i, his, hpVi, hγi⟩ := hcover p hp
  obtain ⟨y, hy₀, hy, hyU, hybound, hystrict⟩ := hnear i p ⟨hp, hpVi⟩
  have haρ : b ≤ (ρ i)⁻¹ := by
    simpa only [inv_inv] using (inv_le_inv₀ (inv_pos.mpr hb) (hρ i).1).mpr (hρ i).2
  have hcoord := static_inv_radius_coordinate_of_solution (left_mem_Icc.mpr haρ) hy
    (by rw [hy₀])
  let z : ℝ → ℝ × ℝ × ℂ := fun x => (y x).2
  have hz : IsIntegralCurveOn z (staticInvRadiusRHS p.2.1 p.2.2.1) (Icc b (ρ i)⁻¹) := by
    intro x hx
    simpa only [z, staticField, hcoord x hx, Function.comp_def, ContinuousLinearMap.coe_snd'] using!
      (hasFDerivAt_snd (𝕜 := ℝ) (p := y x)).comp_hasDerivWithinAt x (hy x hx)
  refine ⟨ρ i, ⟨(hbounds i his).1, (hρ i).2⟩, z,
    by simp only [z, hy₀, f], hz, fun x hx => ?_, ?_⟩
  · have hpos := hyU hx
    have hcoef : coefficients p (y x) ≤ C :=
      (hybound x hx).trans ((le_abs_self (bound i)).trans (hbounds i his).2)
    have heta : y x = (x, z x) := by
      apply Prod.ext
      · exact hcoord x hx
      · rfl
    rw [heta] at hpos hcoef
    exact ⟨hpos.1, hpos.2, hcoef⟩
  · have hv := hγi.trans hystrict
    have hBmem : (ρ i)⁻¹ ∈ Icc b (ρ i)⁻¹ := right_mem_Icc.mpr haρ
    change γ ≤ max (-(z (ρ i)⁻¹).1)
      (δgap - (1 - 2 * (y (ρ i)⁻¹).1 * (z (ρ i)⁻¹).1)) at hv
    rw [hcoord _ hBmem] at hv
    rcases le_max_iff.mp hv with hm | hg
    · exact Or.inl (by linarith only [hm])
    · exact Or.inr (by linarith only [hg])


/-- [node prop:charged-observation#uniform-static-barriers]
Uniform strict barriers for the compact static family. The inverse outer radius
`a`, positive lower stopping radius `r`, positive violation `γ`, and coefficient
bound `C` are chosen after `δgap` alone, before every normalized member. References
are stopped separately at their selected `ρ`; the theorem never asserts a
common existence interval down to the smallest radius of another member. -/
theorem uniform_static_barriers (δgap : ℝ) (hδgap : δgap ∈ Ioo 0 1) :
    ∃ a > 0, a ≤ (1 / 128 : ℝ) ∧ ∃ r > 0, ∃ γ > 0, ∃ C > 0,
      let S : Set Param := {p | 0 ≤ p.1 ∧
        p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 a}
      ∃ outer : Param → ℝ → ℝ × ℝ × ℂ,
        (∀ p ∈ S, outer p p.2.2.2 = (p.1, 1 / 2, p.2.1 * p.2.2.2) ∧
          IsIntegralCurveOn (outer p) (staticInvRadiusRHS p.2.1 p.2.2.1)
            (Icc (p.2.2.2 - 2 * a) (p.2.2.2 + 2 * a)) ∧
          ∀ x ∈ Icc (p.2.2.2 - 2 * a) (p.2.2.2 + 2 * a),
            |x| ≤ 1 / 32 ∧ |(outer p x).1| ≤ 2 ∧
            (outer p x).2.1 ∈ Icc (1 / 4) 1 ∧ ‖(outer p x).2.2‖ ≤ 1) ∧
        ∀ p ∈ S, ∃ ρ ∈ Icc r a⁻¹, ∃ z : ℝ → ℝ × ℝ × ℂ,
          z a = outer p a ∧
          IsIntegralCurveOn z (staticInvRadiusRHS p.2.1 p.2.2.1) (Icc a ρ⁻¹) ∧
          (∀ x ∈ Icc a ρ⁻¹, 0 < (z x).2.1 ∧ 0 < 1 - 2 * x * (z x).1 ∧
            ‖(x, z x)‖ + |(z x).2.1⁻¹| + |(1 - 2 * x * (z x).1)⁻¹| +
              ‖(p.2.1 / ((2 * (z x).2.1 : ℝ) : ℂ)) * x‖ +
              |(2 * x * (z x).1 - p.2.2.1 ^ 2 * x ^ 2) / (1 - 2 * x * (z x).1)| ≤ C) ∧
          ((z ρ⁻¹).1 ≤ -γ ∨ 1 - 2 * ρ⁻¹ * (z ρ⁻¹).1 ≤ δgap - γ) := by
  classical
  obtain ⟨a, ha, ha128, hfamily⟩ := compact_static_family
  obtain ⟨outer, hout, hcontinuous, _⟩ := hfamily a ⟨ha, le_rfl⟩
  let S : Set Param := {p | 0 ≤ p.1 ∧
    p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 a}
  let f : Param → State := fun p => (a, outer p a)
  have hsub (p : Param) (hp : p ∈ S) : Icc p.2.2.2 a ⊆
      Icc (p.2.2.2 - 2 * a) (p.2.2.2 + 2 * a) :=
    Icc_subset_Icc (by linarith only [ha.le])
      (by linarith only [ha.le, hp.2.2.1])
  have houter (p : Param) (hp : p ∈ S) :
      IsIntegralCurveOn (outer p) (staticInvRadiusRHS p.2.1 p.2.2.1) (Icc p.2.2.2 a) :=
    (hout p hp).2.1.mono (hsub p hp)
  have hpositive (p : Param) (hp : p ∈ S) : f p ∈ stateDomain := by
    have h := (hout p hp).2.2 a (hsub p hp (right_mem_Icc.mpr hp.2.2.2))
    have hlam : 0 < (outer p a).2.1 := lt_of_lt_of_le (by norm_num) h.2.2.1.1
    have hprod : |2 * a * (outer p a).1| ≤ 1 / 8 := by
      calc
        |2 * a * (outer p a).1| = 2 * |a| * |(outer p a).1| := by
          rw [abs_mul, abs_mul]; norm_num
        _ ≤ 2 * (1 / 32) * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h.1 (by norm_num)) h.2.1
            (abs_nonneg _) (by norm_num)
        _ = 1 / 8 := by norm_num
    exact ⟨hlam, by linarith only [le_abs_self (2 * a * (outer p a).1), hprod]⟩
  obtain ⟨r, hr, γ, hγ, C, hC, hbar⟩ :=
    uniform_static_barriers_of_outer_family δgap a hδgap ha outer
      (fun p hp => ⟨(hout p hp).1, houter p hp⟩) hcontinuous hpositive
  exact ⟨a, ha, ha128, r, hr, γ, hγ, C, hC, outer, hout, hbar⟩

end EmcsfAcExtension.Global.Observation
