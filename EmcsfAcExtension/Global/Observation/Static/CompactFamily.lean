module

public import EmcsfAcExtension.Global.Observation.Static.Outer
import EmcsfAcExtension.Infra.ODE.ParamDependence

/-!
# Compact parameters for the static references

The parameter is `(M, P, q, x₀)`, with complex scalar amplitude `P` and real
charge `q`. The compactified inverse outer radius `x₀` includes zero.
Source: `charged_SF_new_version.tex:L2199–L2227`.
-/

public section

open Set Metric Filter Topology
open scoped NNReal

namespace EmcsfAcExtension.Global.Observation

local notation "Param" => (ℝ × ℂ × ℝ × ℝ)
local notation "State" => (ℝ × ℝ × ℝ × ℂ)

/-- [internal]
The normalized static parameter set is compact, including complex phase and
initial inverse radius zero. The upper inverse radius `a` is fixed before the
member; this assertion introduces no estimate constant. -/
theorem static_parameters_isCompact (a : ℝ) :
    IsCompact {p : ℝ × ℂ × ℝ × ℝ |
      0 ≤ p.1 ∧ p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 a} := by
  apply (show IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : ℂ) 1 ×ˢ
      Icc (-1 : ℝ) 1 ×ˢ Icc 0 a) from
    isCompact_Icc.prod ((isCompact_closedBall (0 : ℂ) 1).prod
      (isCompact_Icc.prod isCompact_Icc))).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter
        (isClosed_Icc.preimage (by fun_prop)))
  · intro p hp
    have hP : ‖p.2.1‖ ≤ 1 := by
      linarith only [hp.1, hp.2.1, abs_nonneg p.2.2.1]
    have hq : |p.2.2.1| ≤ 1 := by
      linarith only [hp.1, hp.2.1, norm_nonneg p.2.1]
    have hM : p.1 ≤ 1 := by
      linarith only [hp.2.1, norm_nonneg p.2.1, abs_nonneg p.2.2.1]
    exact ⟨⟨hp.1, hM⟩, by simpa using hP, abs_le.mp hq, hp.2.2⟩

/-- [internal]
Continuous endpoint data for a static family already supplied by uniform outer
existence. The initial inverse radius varies down to zero; the fixed endpoint
is `b`. The box is universal and the existence half-width `a` precedes the data. -/
theorem static_endpoint_continuous_of_solutions (a b : ℝ) (ha : 0 < a)
    (_hb : 0 ≤ b) (hba : b ≤ a) (z : Param → ℝ → ℝ × ℝ × ℂ)
    (hinit : ∀ p ∈ {p : Param | 0 ≤ p.1 ∧
      p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 b},
      z p p.2.2.2 = (p.1, 1 / 2, p.2.1 * p.2.2.2))
    (hsol : ∀ p ∈ {p : Param | 0 ≤ p.1 ∧
      p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 b},
      IsIntegralCurveOn (z p) (staticInvRadiusRHS p.2.1 p.2.2.1)
        (Icc p.2.2.2 (p.2.2.2 + 2 * a)))
    (hbox : ∀ p ∈ {p : Param | 0 ≤ p.1 ∧
      p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 b},
      ∀ x ∈ Icc p.2.2.2 (p.2.2.2 + 2 * a),
        |x| ≤ 1 / 32 ∧ |(z p x).1| ≤ 2 ∧
        (z p x).2.1 ∈ Icc (1 / 4) 1 ∧ ‖(z p x).2.2‖ ≤ 1) :
    ContinuousOn (fun p => z p b)
      {p : Param | 0 ≤ p.1 ∧
        p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 b} := by
  let S : Set Param := {p | 0 ≤ p.1 ∧
    p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 b}
  let U : Set State := {w | 0 < w.2.2.1 ∧ 0 < 1 - 2 * w.1 * w.2.1}
  let C : Set State := Icc (-(1 / 32)) (1 / 32) ×ˢ Icc (-2) 2 ×ˢ
    Icc (1 / 4) 1 ×ˢ closedBall 0 1
  let F := fun (_ : ℝ) (p : Param) (w : State) =>
    ((1 : ℝ), staticInvRadiusRHS p.2.1 p.2.2.1 w.1 w.2)
  let v := fun (p : Param) (x : ℝ) => (x, z p x)
  have hC : IsCompact C := isCompact_Icc.prod
    (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_closedBall _ _)))
  have hCU : C ⊆ U := by
    intro w hw
    have hx : |w.1| ≤ 1 / 32 := abs_le.mpr hw.1
    have hm : |w.2.1| ≤ 2 := abs_le.mpr hw.2.1
    have hprod : |2 * w.1 * w.2.1| ≤ 1 / 8 := by
      calc
        |2 * w.1 * w.2.1| = 2 * |w.1| * |w.2.1| := by
          rw [abs_mul, abs_mul]; norm_num
        _ ≤ 2 * (1 / 32) * 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hx (by norm_num)) hm
            (abs_nonneg _) (by norm_num)
        _ = 1 / 8 := by norm_num
    exact ⟨by linarith only [hw.2.2.1.1],
      by linarith only [le_abs_self (2 * w.1 * w.2.1), hprod]⟩
  have hF : ContinuousOn (fun w : ℝ × Param × State => F w.1 w.2.1 w.2.2)
      (univ ×ˢ S ×ˢ U) := by
    intro w hw
    have hmap : Continuous (fun w : ℝ × Param × State =>
        ((w.2.1.2.1, w.2.1.2.2.1), w.2.2)) := by fun_prop
    exact ((static_inv_radius_joint_contDiffAt (w.2.1.2.1, w.2.1.2.2.1) w.2.2
      (ne_of_gt hw.2.2.1) (ne_of_gt hw.2.2.2)).continuousAt.comp
        (f := fun w : ℝ × Param × State => ((w.2.1.2.1, w.2.1.2.2.1), w.2.2))
        hmap.continuousAt).continuousWithinAt
  have hlocal : ∀ t : ℝ, ∀ p ∈ S, ∀ w ∈ U,
      ∃ (V : Set Param) (R d : ℝ) (K : ℝ≥0),
        IsOpen V ∧ p ∈ V ∧ 0 < R ∧ 0 < d ∧
        ∀ q ∈ S ∩ V, ∀ s ∈ Icc (t - d) (t + d),
          LipschitzOnWith K (F s q) (closedBall w R) := by
    intro t p _ w hw
    obtain ⟨V, R, K, hV, hpV, hR, hK⟩ :=
      static_inv_radius_local_lipschitz (p.2.1, p.2.2.1) w hw.1 hw.2
    refine ⟨(fun p : Param => (p.2.1, p.2.2.1)) ⁻¹' V,
      R, 1, K, hV.preimage (by fun_prop), hpV, hR, zero_lt_one, ?_⟩
    exact fun q hq _ _ => hK (q.2.1, q.2.2.1) hq.2
  have hv : ∀ p ∈ S, IsIntegralCurveOn (v p) (fun t => F t p)
      (Icc (p.2.2.2 + 0) (p.2.2.2 + 2 * a)) := by
    intro p hp x hx
    simp only [add_zero] at hx ⊢
    exact (hasDerivWithinAt_id x _).prodMk
      (hsol p hp x hx)
  have hvC : ∀ p ∈ S, MapsTo (v p)
      (Icc (p.2.2.2 + 0) (p.2.2.2 + 2 * a)) C := by
    intro p hp x hx
    obtain ⟨hx', hm, hlam, hphi⟩ := hbox p hp x (by simpa only [add_zero] using hx)
    exact ⟨abs_le.mp hx', abs_le.mp hm, hlam, by simpa using hphi⟩
  have hv₀ : ContinuousOn (fun p => v p (p.2.2.2 + 0)) S := by
    have heq : EqOn (fun p => v p (p.2.2.2 + 0))
        (fun p : Param => (p.2.2.2, p.1, (1 / 2 : ℝ), p.2.1 * p.2.2.2)) S := by
      intro p hp
      simp only [v, add_zero, hinit p hp]
    exact (show ContinuousOn
      (fun p : Param => (p.2.2.2, p.1, (1 / 2 : ℝ), p.2.1 * p.2.2.2)) S by
        fun_prop).congr heq
  have hσ : MapsTo (fun p : Param => b - p.2.2.2) S (Icc 0 (2 * a)) := by
    intro p hp
    exact ⟨sub_nonneg.mpr hp.2.2.2,
      by linarith only [hp.2.2.1, hba, ha.le]⟩
  have he := ODE.continuousOn_endpoint_of_locally_lipschitz
    (by linarith only [ha.le] : 0 ≤ 2 * a) (static_parameters_isCompact b) hC hCU
    (by fun_prop : ContinuousOn (fun p : Param => p.2.2.2) S)
    (by fun_prop : ContinuousOn (fun p : Param => b - p.2.2.2) S) hσ
    hF hlocal hv hvC hv₀
  have he' : ContinuousOn (fun p => v p b) S := by
    simpa only [add_sub_cancel] using he
  exact he'.snd

/-- [node prop:charged-observation#compact-static-family]
The data at inverse radius `b = L₀⁻¹` form a compact continuous family, including
initial inverse radius zero and all complex phases. The universal outer width
`a` is chosen before `b` and every normalized parameter tuple. Trajectories are
witnesses obtained after uniform ODE existence, with their positive-gap box. -/
theorem compact_static_family :
    ∃ a > 0, a ≤ (1 / 128 : ℝ) ∧ ∀ b ∈ Ioc 0 a,
      let S : Set Param := {p | 0 ≤ p.1 ∧
        p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 b}
      ∃ z : Param → ℝ → ℝ × ℝ × ℂ,
        (∀ p ∈ S, z p p.2.2.2 = (p.1, 1 / 2, p.2.1 * p.2.2.2) ∧
          IsIntegralCurveOn (z p) (staticInvRadiusRHS p.2.1 p.2.2.1)
            (Icc (p.2.2.2 - 2 * a) (p.2.2.2 + 2 * a)) ∧
          ∀ x ∈ Icc (p.2.2.2 - 2 * a) (p.2.2.2 + 2 * a),
            |x| ≤ 1 / 32 ∧ |(z p x).1| ≤ 2 ∧
            (z p x).2.1 ∈ Icc (1 / 4) 1 ∧ ‖(z p x).2.2‖ ≤ 1) ∧
        ContinuousOn (fun p => z p b) S ∧
        IsCompact ((fun p => ((p.2.1, p.2.2.1), z p b)) '' S) := by
  classical
  obtain ⟨a, ha, ha128, hsol⟩ := static_outer_exists
  refine ⟨a, ha, ha128, fun b hb => ?_⟩
  let S : Set Param := {p | 0 ≤ p.1 ∧
    p.1 + ‖p.2.1‖ + |p.2.2.1| = 1 ∧ p.2.2.2 ∈ Icc 0 b}
  have hex (p : Param) : ∃ z : ℝ → ℝ × ℝ × ℂ, p ∈ S →
      z p.2.2.2 = (p.1, 1 / 2, p.2.1 * p.2.2.2) ∧
      IsIntegralCurveOn z (staticInvRadiusRHS p.2.1 p.2.2.1)
        (Icc (p.2.2.2 - 2 * a) (p.2.2.2 + 2 * a)) ∧
      ∀ x ∈ Icc (p.2.2.2 - 2 * a) (p.2.2.2 + 2 * a),
        |x| ≤ 1 / 32 ∧ |(z x).1| ≤ 2 ∧
        (z x).2.1 ∈ Icc (1 / 4) 1 ∧ ‖(z x).2.2‖ ≤ 1 := by
    by_cases hp : p ∈ S
    · have hP : ‖p.2.1‖ ≤ 1 := by
        linarith only [hp.1, hp.2.1, abs_nonneg p.2.2.1]
      have hq : |p.2.2.1| ≤ 1 := by
        linarith only [hp.1, hp.2.1, norm_nonneg p.2.1]
      have hM : p.1 ∈ Icc 0 1 := ⟨hp.1, by
        linarith only [hp.2.1, norm_nonneg p.2.1, abs_nonneg p.2.2.1]⟩
      obtain ⟨z, hz₀, hz, hbox⟩ := hsol p.2.1 p.2.2.1 p.1 p.2.2.2 hP hq hM
        ⟨hp.2.2.1, hp.2.2.2.trans hb.2⟩
      refine ⟨z, fun _ => ⟨hz₀, hz, fun x hx => ?_⟩⟩
      have h := hbox x hx
      exact ⟨h.1.le, h.2.1.le, ⟨h.2.2.1.1.le, h.2.2.1.2.le⟩, h.2.2.2.2.le⟩
    · exact ⟨0, fun h => False.elim (hp h)⟩
  choose z hz using hex
  have hsub (p : Param) : Icc p.2.2.2 (p.2.2.2 + 2 * a) ⊆
      Icc (p.2.2.2 - 2 * a) (p.2.2.2 + 2 * a) :=
    Icc_subset_Icc (by linarith only [ha.le]) le_rfl
  have hc := static_endpoint_continuous_of_solutions a b ha hb.1.le hb.2 z
    (fun p hp => (hz p hp).1) (fun p hp => (hz p hp).2.1.mono (hsub p))
    (fun p hp x hx => (hz p hp).2.2 x (hsub p hx))
  refine ⟨z, hz, hc, ?_⟩
  exact (static_parameters_isCompact b).image_of_continuousOn
    ((show ContinuousOn (fun p : Param => (p.2.1, p.2.2.1)) S by fun_prop).prodMk hc)

end EmcsfAcExtension.Global.Observation
