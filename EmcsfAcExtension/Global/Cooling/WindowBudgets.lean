/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Cooling.EnergyExports
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Global.Calculus.Gauge
import EmcsfAcExtension.Infra.Measure.WindowSquare

/-! # Actual-field window budgets

Local observation inequalities are integrated against the actual two
clock measures. The cylinder identity is discharged unconditionally.
Source: `charged_SF_new_version.tex:L2923`–L2965.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Cooling

/-- [internal] Actual-field center and outgoing budgets from local window
observation. The only result premise is the window inequality, discharged
by observation in the consumer. The constant depends only on `Tstar,Cstar`
and is chosen before all physical data. -/
theorem charged_cool_window_budgets_of_window_observation
    (Tstar Cstar : ℝ)
    (hTs : 0 < Tstar) (hCs : 0 < Cstar) :
    ∃ Cbudget > 0, ∀ (ui e b δ s t : ℝ) (S : Fields) (_h : OriginalData ui e S),
      0 < b → s < t → δ ≤ 1 / 2 →
      ∀ γ : ClockCylinder S (origDomain ui) b s t,
      AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t →
      (∀ x ∈ Icc s t, S.mu (γ.U x) (γ.V x) +
        ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ≤ δ) →
      (∀ x ∈ Icc (s + Tstar * b) (t - Tstar * b),
        ENNReal.ofReal (b * (‖S.theta (γ.U x) (γ.V x) /
          (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 + S.mu (γ.U x) (γ.V x) ^ 2)) ≤
          ENNReal.ofReal Cstar *
            (ENNReal.ofReal (cylinderDissipation S γ.U γ.V (x - Tstar * b) (x + Tstar * b)) +
              ENNReal.ofReal b * (curveCovVar e S S.a γ.U γ.V
                (x - Tstar * b) (x + Tstar * b)) ^ 2)) →
      let σ := (curveCovVar e S S.a γ.U γ.V s t).toReal
      (∫ x in Icc (s + Tstar * b) (t - Tstar * b),
        (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
          S.mu (γ.U x) (γ.V x) ^ 2) / b) ≤
        2 * Cstar * Tstar * (cylinderDissipation S γ.U γ.V s t / b + σ ^ 2) ∧
      (∫ x in s..t,
        (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
          S.mu (γ.U x) (γ.V x) ^ 2) / b) ≤
        Cbudget * (cylinderEnergy S b (γ.U s) (γ.V s) / b + σ ^ 2) := by
  obtain ⟨Cout, hCout, hout⟩ := charged_cool_outgoing_budget_of_observation Tstar Cstar hTs hCs
  refine ⟨Cout, hCout, ?_⟩
  intro ui e b δ s t S h hb hst hδ γ hac hweak hobs
  have hcylinder := charged_cool_identity ui e b s t S h hb hst γ hac
  let q := fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b
  let y := fun x => S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)
  let z := fun x => S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)
  let μ := fun x => S.mu (γ.U x) (γ.V x)
  let D := fun x => ‖y x - z x‖ ^ 2
  let f := fun x => ‖y x‖ ^ 2 + μ x ^ 2
  let g := fun x => ‖deriv (curveParallel e S S.a γ.U γ.V s) x‖
  let σ := ∫ x in s..t, g x
  have hσ : 0 ≤ σ := intervalIntegral.integral_nonneg hst.le (fun _ _ => norm_nonneg _)
  have hσeq : (curveCovVar e S S.a γ.U γ.V s t).toReal = σ :=
    hac.toReal_eVariationOn_eq_integral_norm_deriv hst.le
  have hn (x : ℝ) (hx : x ∈ Icc s t) :=
    normalized_energy_lower hb (h.mu _ (γ.mem x hx))
  have hqn : ∀ x ∈ Icc s t, 0 ≤ q x := fun x hx => (hn x hx).1
  have hp (x : ℝ) (hx : x ∈ Icc s t) := weak_regime_energy_comparison S b
    (γ.U x) (γ.V x) δ hb (γ.radius x hx) (h.mu _ (γ.mem x hx)).1 hδ (hweak x hx)
  have cγ := γ.c1_U.continuousOn.prodMk γ.c1_V.continuousOn
  have cy : ContinuousOn y (Icc s t) :=
    (h.solution.cont_theta.comp cγ γ.mem).div
      (Complex.continuous_ofReal.comp_continuousOn (h.solution.cont_lam.comp cγ γ.mem))
      (fun x hx => Complex.ofReal_ne_zero.mpr (h.solution.lam_pos _ (γ.mem x hx)).ne')
  have cz : ContinuousOn z (Icc s t) :=
    (h.solution.cont_xi.comp cγ γ.mem).div
      (Complex.continuous_ofReal.comp_continuousOn (h.solution.cont_nu.comp cγ γ.mem))
      (fun x hx => Complex.ofReal_ne_zero.mpr (h.solution.nu_neg _ (γ.mem x hx)).ne)
  have cμ : ContinuousOn μ (Icc s t) :=
    (continuousOn_const.mul (h.solution.cont_m.comp cγ γ.mem)).div
      (h.solution.cont_r.comp cγ γ.mem) (fun x hx => by rw [γ.radius x hx]; exact hb.ne')
  have cD : ContinuousOn D (Icc s t) := (cy.sub cz).norm.pow 2
  have cf : ContinuousOn f (Icc s t) := (cy.norm.pow 2).add (cμ.pow 2)
  have hD : IntervalIntegrable D volume s t := cD.intervalIntegrable_of_Icc hst.le
  have henergy := charged_cool_energy_of_cylinder ui e b s t S h hb hst γ hac hcylinder
  rw [hσeq] at henergy
  obtain ⟨hsup, hdiss₀, _⟩ := henergy
  have hdiss : (∫ x in s..t, D x / b) ≤ 4 * q s + 3 * σ ^ 2 := by
    simpa only [cylinderDissipation, intervalIntegral.integral_div] using hdiss₀
  let dissMu := clockDensityMeasure D s t
  let ω := covariantVariationMeasure e S S.a γ.U γ.V s t
  have : IsFiniteMeasure dissMu := clock_density_measure_finite hst.le hD (fun _ _ => sq_nonneg _)
  have : IsFiniteMeasure ω := covariant_variation_measure_finite hst.le hac
  have hA := connection_intervalIntegrable h hst.le γ
  have hdissMu : (dissMu univ).toReal / b ≤ 4 * q s + 3 * σ ^ 2 := by
    rw [clock_density_measure_univ hst.le hD (fun _ _ => sq_nonneg _),
      ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hst.le (fun _ _ => sq_nonneg _))]
    simpa only [intervalIntegral.integral_div] using hdiss
  have hω : (ω univ).toReal = σ := by
    rw [covariant_variation_measure_univ hst.le hac, hσeq]
  have hfpoint (x : ℝ) (hx : x ∈ Icc s t) : f x ≤ 3 * q x := by
    have hμn := (h.mu _ (γ.mem x hx)).1
    have hμup : μ x ≤ 1 / 2 := by
      have hw := hweak x hx
      dsimp only [μ]
      linarith [norm_nonneg (y x)]
    have hlo := (hp x hx).1
    change (‖y x‖ ^ 2 + μ x) / 2 ≤ q x at hlo
    have hyl := (hn x hx).2
    change ‖y x‖ ^ 2 ≤ 2 * q x at hyl
    dsimp only [f]
    nlinarith only [hlo, hyl, hμup, hμn, sq_nonneg ‖y x‖]
  have hobs' : ∀ x ∈ Icc (s + Tstar * b) (t - Tstar * b),
      f x ≤ Cstar * ((dissMu (Icc (x - Tstar * b) (x + Tstar * b))).toReal / b +
        (ω (Icc (x - Tstar * b) (x + Tstar * b))).toReal ^ 2) := by
    intro x hx
    have hsub : Icc (x - Tstar * b) (x + Tstar * b) ⊆ Icc s t := by
      intro a ha
      constructor <;> linarith only [hx.1, hx.2, ha.1, ha.2]
    have hab : x - Tstar * b ≤ x + Tstar * b := by linarith [mul_pos hTs hb]
    have he : ENNReal.ofReal (b * f x) ≤ ENNReal.ofReal Cstar *
        (dissMu (Icc (x - Tstar * b) (x + Tstar * b)) + ENNReal.ofReal b *
          (ω (Icc (x - Tstar * b) (x + Tstar * b))) ^ 2) := by
      rw [clock_density_measure_apply hst.le hD (fun _ _ => sq_nonneg _) hab hsub,
        covariant_variation_measure_apply hst.le hA hac hab hsub]
      exact hobs x hx
    have hr := ENNReal.toReal_mono (by finiteness) he
    rw [ENNReal.toReal_ofReal (by dsimp only [f]; positivity : 0 ≤ b * f x),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hCs.le,
      ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hb.le, ENNReal.toReal_pow] at hr
    calc
      f x = (b * f x) / b := by field_simp [hb.ne']
      _ ≤ _ := div_le_div_of_nonneg_right hr hb.le
      _ = _ := by field_simp [hb.ne']
  have houtf := hout dissMu ω f b s t (q s) σ hb (hqn s (left_mem_Icc.mpr hst.le)) hσ
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hst.le).1
      (cf.intervalIntegrable_of_Icc hst.le)) (fun x hx => (hfpoint x hx).trans
      (mul_le_mul_of_nonneg_left (hsup x hx) (by norm_num))) hdissMu hω hobs'
  have houti : (∫ x in s..t, f x / b) ≤ Cout * (q s + σ ^ 2) := by
    simpa only [intervalIntegral.integral_of_le hst.le, restrict_Ioc_eq_restrict_Icc] using houtf
  have hsub : Icc (s + Tstar * b) (t - Tstar * b) ⊆ Icc s t := by
    intro x hx
    have hp : 0 ≤ Tstar * b := by positivity
    constructor <;> linarith only [hx.1, hx.2, hp]
  have hc := charged_cool_centers_of_observation Tstar Cstar hTs.le hCs.le
    dissMu ω hb (((intervalIntegrable_iff_integrableOn_Icc_of_le hst.le).mp
      (cf.intervalIntegrable_of_Icc hst.le)).mono_set hsub) hobs'
  rw [hω, clock_density_measure_univ hst.le hD (fun _ _ => sq_nonneg _),
    ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hst.le (fun _ _ => sq_nonneg _))] at hc
  rw [hσeq]
  exact ⟨hc, houti⟩

end EmcsfAcExtension.Global.Cooling
