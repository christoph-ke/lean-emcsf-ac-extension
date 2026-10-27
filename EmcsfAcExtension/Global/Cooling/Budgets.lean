/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Cooling.Endpoint
public import EmcsfAcExtension.Global.Cooling.Windows
import EmcsfAcExtension.Infra.AC.Variation
import EmcsfAcExtension.Global.Calculus.Gauge
import EmcsfAcExtension.Infra.Measure.WindowSquare

/-! # Duration-independent cooling budgets

The identity-only bound is valid on every ordered clock interval before
observation is used. Full-window counting and the two endpoint strips
then supply the outgoing and full integrated budgets
(`charged_SF_new_version.tex:L2898–L2988`).
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Cooling

/-- [internal] The identity-only supremum and dissipation bounds, on an
arbitrary proper interval. The displayed numerical constants are universal;
no observation window, duration bound, or variation smallness is assumed. -/
theorem energy_budget_of_balance {q D g : ℝ → ℝ} {b s t : ℝ}
    (hb : 0 < b) (hst : s ≤ t)
    (hq : AbsolutelyContinuousOnInterval q s t)
    (hD : IntervalIntegrable D volume s t) (hg : IntervalIntegrable g volume s t)
    (hqn : ∀ x ∈ Icc s t, 0 ≤ q x)
    (hDn : ∀ x ∈ Icc s t, 0 ≤ D x) (hgn : ∀ x ∈ Icc s t, 0 ≤ g x)
    (hbal : ∀ᵐ x ∂volume.restrict (Icc s t),
      deriv q x + D x / (2 * b) ≤ Real.sqrt (2 * q x) * g x) :
    let σ := ∫ x in s..t, g x
    (∀ x ∈ Icc s t, q x ≤ 2 * q s + σ ^ 2) ∧
      (∫ x in s..t, D x / b) ≤ 4 * q s + 3 * σ ^ 2 := by
  let σ := ∫ x in s..t, g x
  have hσ : 0 ≤ σ := intervalIntegral.integral_nonneg hst hgn
  have hroot (x : ℝ) (hx : x ∈ Icc s t) :
      Real.sqrt (q x) ≤ Real.sqrt (q s) + σ / Real.sqrt 2 := by
    have hsub : Icc s x ⊆ Icc s t := Icc_subset_Icc le_rfl hx.2
    have hsub' : uIcc s x ⊆ uIcc s t := by
      simpa only [uIcc_of_le hx.1, uIcc_of_le hst] using hsub
    have hd : ∀ᵐ y ∂volume.restrict (Icc s x), deriv q y ≤ Real.sqrt (2 * q y) * g y := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hbal,
        ae_restrict_mem measurableSet_Icc] with y hy hym
      have hpos := div_nonneg (hDn y (hsub hym)) (by positivity : 0 ≤ 2 * b)
      linarith
    have hsqrt := sqrt_growth_of_ae_deriv_le hx.1 (hq.mono hsub') (hg.mono_set hsub')
      (fun y hy => hqn y (hsub hy)) (fun y hy => hgn y (hsub hy)) hd
    have hint : (∫ y in s..x, g y) ≤ σ :=
      intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
        ((ae_restrict_mem measurableSet_Ioc).mono
          (fun y hy => hgn y (Ioc_subset_Icc_self hy))) hg
    exact hsqrt.trans (add_le_add le_rfl (div_le_div_of_nonneg_right hint (Real.sqrt_nonneg 2)))
  have hsup := supremum_energy_bound_of_square_root hqn hst hσ hroot
  refine ⟨hsup, ?_⟩
  let B := Real.sqrt 2 * Real.sqrt (q s) + σ
  have hB (x : ℝ) (hx : x ∈ Icc s t) : Real.sqrt (2 * q x) ≤ B := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hm := mul_le_mul_of_nonneg_left (hroot x hx) (Real.sqrt_nonneg 2)
    have he : Real.sqrt 2 * (Real.sqrt (q s) + σ / Real.sqrt 2) = B := by
      dsimp only [B]
      field_simp
    exact hm.trans_eq he
  have hbound : ∀ᵐ x ∂volume.restrict (Icc s t),
      deriv q x + D x / (2 * b) ≤ B * g x := by
    filter_upwards [hbal, ae_restrict_mem measurableSet_Icc] with x hx hxm
    exact hx.trans (mul_le_mul_of_nonneg_right (hB x hxm) (hgn x hxm))
  have hi := intervalIntegral.integral_mono_ae_restrict hst
    (hq.intervalIntegrable_deriv.add (hD.div_const _)) (hg.const_mul B) hbound
  rw [intervalIntegral.integral_add hq.intervalIntegrable_deriv (hD.div_const _),
    hq.integral_deriv_eq_sub, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul] at hi
  rw [intervalIntegral.integral_div]
  have ht := hqn t (right_mem_Icc.mpr hst)
  have hs := hqn s (left_mem_Icc.mpr hst)
  have hA2 : (Real.sqrt 2 * Real.sqrt (q s)) ^ 2 = 2 * q s := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hs]
  have hsplit : (∫ x in s..t, D x) / (2 * b) = ((∫ x in s..t, D x) / b) / 2 := by ring
  rw [hsplit] at hi
  dsimp only [B] at hi
  change q t - q s + ((∫ x in s..t, D x) / b) / 2 ≤
    (Real.sqrt 2 * Real.sqrt (q s) + σ) * σ at hi
  nlinarith only [hi, ht, hA2, sq_nonneg (Real.sqrt 2 * Real.sqrt (q s) - σ)]

/-- [internal] Identity-only charged cylinder energy and dissipation budgets,
with universal coefficients, on every proper interval. This helper is
available before any completed observation window and is consumed below.
No duration, coupling, scalar-background, or radius bound enters its constants. -/
theorem _root_.EmcsfAcExtension.Global.charged_cool_energy_of_cylinder
    (ui e b s t : ℝ) (S : Fields) (h : OriginalData ui e S)
    (hb : 0 < b) (hst : s < t) (γ : ClockCylinder S (origDomain ui) b s t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t)
    (hcylinder : AbsolutelyContinuousOnInterval
        (fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b) s t ∧
      ∀ᵐ x ∂volume.restrict (Icc s t),
        deriv (fun y => cylinderEnergy S b (γ.U y) (γ.V y) / b) x +
          ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ) -
            S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 / (2 * b) =
          (starRingEnd ℂ (curveParallel e S
            (fun u v => S.theta u v / (S.lam u v : ℂ)) γ.U γ.V s x) *
              deriv (curveParallel e S S.a γ.U γ.V s) x).re) :
    let σ := (curveCovVar e S S.a γ.U γ.V s t).toReal
    (∀ x ∈ Icc s t, cylinderEnergy S b (γ.U x) (γ.V x) / b ≤
      2 * (cylinderEnergy S b (γ.U s) (γ.V s) / b) + σ ^ 2) ∧
    cylinderDissipation S γ.U γ.V s t / b ≤
      4 * (cylinderEnergy S b (γ.U s) (γ.V s) / b) + 3 * σ ^ 2 ∧
    (∀ x ∈ Icc s t, cylinderEnergy S b (γ.U x) (γ.V x) / b +
      cylinderDissipation S γ.U γ.V s t / b ≤
        6 * (cylinderEnergy S b (γ.U s) (γ.V s) / b + σ ^ 2)) := by
  let q := fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b
  let y := fun x => S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)
  let z := fun x => S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)
  let D := fun x => ‖y x - z x‖ ^ 2
  let g := fun x => ‖deriv (curveParallel e S S.a γ.U γ.V s) x‖
  let σ := ∫ x in s..t, g x
  have hσeq : (curveCovVar e S S.a γ.U γ.V s t).toReal = σ :=
    hac.toReal_eVariationOn_eq_integral_norm_deriv hst.le
  have hn (x : ℝ) (hx : x ∈ Icc s t) :=
    normalized_energy_lower hb (h.mu _ (γ.mem x hx))
  have hqn : ∀ x ∈ Icc s t, 0 ≤ q x := fun x hx => (hn x hx).1
  have cγ := γ.c1_U.continuousOn.prodMk γ.c1_V.continuousOn
  have cy : ContinuousOn y (Icc s t) :=
    (h.solution.cont_theta.comp cγ γ.mem).div
      (Complex.continuous_ofReal.comp_continuousOn (h.solution.cont_lam.comp cγ γ.mem))
      (fun x hx => Complex.ofReal_ne_zero.mpr (h.solution.lam_pos _ (γ.mem x hx)).ne')
  have cz : ContinuousOn z (Icc s t) :=
    (h.solution.cont_xi.comp cγ γ.mem).div
      (Complex.continuous_ofReal.comp_continuousOn (h.solution.cont_nu.comp cγ γ.mem))
      (fun x hx => Complex.ofReal_ne_zero.mpr (h.solution.nu_neg _ (γ.mem x hx)).ne)
  have hD : IntervalIntegrable D volume s t :=
    ((cy.sub cz).norm.pow 2).intervalIntegrable_of_Icc hst.le
  have hbal : ∀ᵐ x ∂volume.restrict (Icc s t),
      deriv q x + D x / (2 * b) ≤ Real.sqrt (2 * q x) * g x := by
    filter_upwards [hcylinder.2, ae_restrict_mem measurableSet_Icc] with x hx hxm
    have hy : ‖y x‖ ≤ Real.sqrt (2 * q x) := Real.le_sqrt_of_sq_le (hn x hxm).2
    have hpair := Complex.re_le_norm (starRingEnd ℂ (curveParallel e S
      (fun u v => S.theta u v / (S.lam u v : ℂ)) γ.U γ.V s x) *
        deriv (curveParallel e S S.a γ.U γ.V s) x)
    rw [norm_mul, Complex.norm_conj, Calculus.norm_curveParallel] at hpair
    exact hx.le.trans (hpair.trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _)))
  obtain ⟨hsup, hdiss⟩ := energy_budget_of_balance hb hst.le hcylinder.1 hD
    hac.intervalIntegrable_deriv_finiteDimensional.norm hqn
    (fun _ _ => sq_nonneg _) (fun _ _ => norm_nonneg _) hbal
  rw [hσeq]
  refine ⟨hsup, ?_, ?_⟩
  · simpa only [cylinderDissipation, intervalIntegral.integral_div] using hdiss
  · intro x hx
    change q x + (∫ y in s..t, D y) / b ≤ 6 * (q s + σ ^ 2)
    rw [← intervalIntegral.integral_div]
    nlinarith only [hsup x hx, hdiss, hqn s (left_mem_Icc.mpr hst.le), sq_nonneg σ]

/-- [internal] Integrate an observation inequality over the full-window
centers. The exact coefficient is `2*Cstar*Tstar`, fixed before duration,
radius, the observed density, and the two finite clock measures. -/
theorem _root_.EmcsfAcExtension.Global.charged_cool_centers_of_observation
    (Tstar Cstar : ℝ) (hTs : 0 ≤ Tstar) (hCs : 0 ≤ Cstar)
    (dissMu ω : Measure ℝ) [IsFiniteMeasure dissMu] [IsFiniteMeasure ω]
    {f : ℝ → ℝ} {b s t : ℝ} (hb : 0 < b)
    (hf : IntegrableOn f (Icc (s + Tstar * b) (t - Tstar * b)))
    (hobs : ∀ x ∈ Icc (s + Tstar * b) (t - Tstar * b),
      f x ≤ Cstar * ((dissMu (Icc (x - Tstar * b) (x + Tstar * b))).toReal / b +
        (ω (Icc (x - Tstar * b) (x + Tstar * b))).toReal ^ 2)) :
    (∫ x in Icc (s + Tstar * b) (t - Tstar * b), f x / b) ≤
      2 * Cstar * Tstar * ((dissMu univ).toReal / b + (ω univ).toReal ^ 2) := by
  let centers := Icc (s + Tstar * b) (t - Tstar * b)
  let wdissMu := fun x => (dissMu (Icc (x - Tstar * b) (x + Tstar * b))).toReal
  let wω := fun x => (ω (Icc (x - Tstar * b) (x + Tstar * b))).toReal ^ 2
  have hdissMu := integrableOn_window_measure dissMu (Tstar * b) centers
  have hω := integrableOn_window_sq ω (Tstar * b) centers
  have hi : (∫ x in centers, f x / b) ≤
      ∫ x in centers, (Cstar / b ^ 2) * wdissMu x + (Cstar / b) * wω x := by
    apply integral_mono_ae (hf.div_const _) ((hdissMu.const_mul _).add (hω.const_mul _))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    calc
      f x / b ≤ (Cstar * (wdissMu x / b + wω x)) / b :=
        div_le_div_of_nonneg_right (hobs x hx) hb.le
      _ = _ := by dsimp only [wdissMu, wω, Pi.add_apply]; field_simp [hb.ne']
  rw [integral_add (hdissMu.const_mul _) (hω.const_mul _), integral_const_mul,
    integral_const_mul] at hi
  have hdissMub := integral_window_measure_le dissMu (mul_nonneg hTs hb.le) centers
  have hωb := integral_window_sq_le ω (mul_nonneg hTs hb.le) centers
  have hmdissMu := mul_le_mul_of_nonneg_left hdissMub (by positivity : 0 ≤ Cstar / b ^ 2)
  have hmω := mul_le_mul_of_nonneg_left hωb (by positivity : 0 ≤ Cstar / b)
  have he : Cstar / b ^ 2 * (2 * (Tstar * b) * (dissMu univ).toReal) +
      Cstar / b * (2 * (Tstar * b) * (ω univ).toReal ^ 2) =
      2 * Cstar * Tstar * ((dissMu univ).toReal / b + (ω univ).toReal ^ 2) := by
    field_simp [hb.ne']
  exact hi.trans ((add_le_add hmdissMu hmω).trans_eq he)

/-- [internal] Full and arbitrarily short outgoing budgets from observation
and the already proved identity-only bounds. The common constant depends
only on `Tstar,Cstar`, before all physical and clock data. -/
theorem _root_.EmcsfAcExtension.Global.charged_cool_outgoing_budget_of_observation
    (Tstar Cstar : ℝ) (hTs : 0 < Tstar) (hCs : 0 < Cstar) :
    ∃ C > 0, ∀ (dissMu ω : Measure ℝ) [IsFiniteMeasure dissMu] [IsFiniteMeasure ω]
      (f : ℝ → ℝ) (b s t q₀ σ : ℝ), 0 < b → 0 ≤ q₀ → 0 ≤ σ →
      IntegrableOn f (Icc s t) →
      (∀ x ∈ Icc s t, f x ≤ 3 * (2 * q₀ + σ ^ 2)) →
      (dissMu univ).toReal / b ≤ 4 * q₀ + 3 * σ ^ 2 → (ω univ).toReal = σ →
      (∀ x ∈ Icc (s + Tstar * b) (t - Tstar * b),
        f x ≤ Cstar * ((dissMu (Icc (x - Tstar * b) (x + Tstar * b))).toReal / b +
          (ω (Icc (x - Tstar * b) (x + Tstar * b))).toReal ^ 2)) →
      (∫ x in Icc s t, f x / b) ≤ C * (q₀ + σ ^ 2) := by
  refine ⟨12 * Tstar + 8 * Cstar * Tstar, by positivity, ?_⟩
  intro dissMu ω _ _ f b s t q₀ σ hb hq hσ hf hbound hdissMu hω hobs
  have hsub : Icc (s + Tstar * b) (t - Tstar * b) ⊆ Icc s t := by
    intro x hx
    have hp : 0 ≤ Tstar * b := by positivity
    constructor <;> linarith only [hx.1, hx.2, hp]
  have hc := charged_cool_centers_of_observation Tstar Cstar hTs.le hCs.le
    dissMu ω hb (hf.mono_set hsub) hobs
  rw [hω] at hc
  have hc' := hc.trans (mul_le_mul_of_nonneg_left
    (add_le_add hdissMu le_rfl) (by positivity))
  have he := endpoint_interval_budget_of_bound (mul_nonneg hTs.le hb.le)
    (by positivity : 0 ≤ 3 * (2 * q₀ + σ ^ 2) / b) (hf.div_const b)
    (fun x hx => div_le_div_of_nonneg_right (hbound x hx) hb.le)
  have heq : 2 * (Tstar * b) * (3 * (2 * q₀ + σ ^ 2) / b) =
      6 * Tstar * (2 * q₀ + σ ^ 2) := by field_simp; ring
  rw [heq] at he
  have hsplit := setIntegral_sdiff measurableSet_Icc (hf.div_const b) hsub
  nlinarith only [hc', he, hsplit, mul_nonneg hTs.le (sq_nonneg σ)]

/-- [internal] Field-level budgets on an arbitrary proper cylinder interval,
conditional on the cylinder identity and the observation inequalities for
its full windows. The one positive constant depends only on `Tstar,Cstar`,
before all radius, duration, energy, coupling, and scalar-background data.
The pointwise-plus-integral formulation also controls the compact suprema
in `charged_SF_new_version.tex:L2833–L2852`. -/
theorem _root_.EmcsfAcExtension.Global.charged_cool_integrated_of_observation_of_cylinder
    (Tstar Cstar : ℝ)
    (hTs : 0 < Tstar) (hCs : 0 < Cstar) :
    ∃ Cbudget > 0, ∀ (ui e b δ s t : ℝ) (S : Fields) (_h : OriginalData ui e S),
      0 < b → s < t → δ ≤ 1 / 2 →
      ∀ γ : ClockCylinder S (origDomain ui) b s t,
      AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t →
      (∀ x ∈ Icc s t, S.mu (γ.U x) (γ.V x) +
        ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ≤ δ) →
      (AbsolutelyContinuousOnInterval
          (fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b) s t ∧
        ∀ᵐ x ∂volume.restrict (Icc s t),
          deriv (fun y => cylinderEnergy S b (γ.U y) (γ.V y) / b) x +
            ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ) -
              S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 / (2 * b) =
            (starRingEnd ℂ (curveParallel e S
              (fun u v => S.theta u v / (S.lam u v : ℂ)) γ.U γ.V s x) *
                deriv (curveParallel e S S.a γ.U γ.V s) x).re) →
      (∀ x ∈ Icc (s + Tstar * b) (t - Tstar * b),
        ENNReal.ofReal (b * (‖S.theta (γ.U x) (γ.V x) /
          (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 + S.mu (γ.U x) (γ.V x) ^ 2)) ≤
          ENNReal.ofReal Cstar *
            (ENNReal.ofReal (cylinderDissipation S γ.U γ.V (x - Tstar * b) (x + Tstar * b)) +
              ENNReal.ofReal b * (curveCovVar e S S.a γ.U γ.V
                (x - Tstar * b) (x + Tstar * b)) ^ 2)) →
      let σ := (curveCovVar e S S.a γ.U γ.V s t).toReal
      (∀ x ∈ Icc s t, cylinderEnergy S b (γ.U x) (γ.V x) / b +
        cylinderDissipation S γ.U γ.V s t / b ≤
          Cbudget * (cylinderEnergy S b (γ.U s) (γ.V s) / b + σ ^ 2)) ∧
      (∀ x ∈ Icc s t, S.m (γ.U x) (γ.V x) / b +
        ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
        (∫ y in s..t,
          (‖S.theta (γ.U y) (γ.V y) / (S.lam (γ.U y) (γ.V y) : ℂ)‖ ^ 2 +
            ‖S.xi (γ.U y) (γ.V y) / (S.nu (γ.U y) (γ.V y) : ℂ)‖ ^ 2 +
            S.mu (γ.U y) (γ.V y) ^ 2 +
            (cylinderEnergy S b (γ.U y) (γ.V y) / b) ^ 2) / b) ≤
          Cbudget * (cylinderEnergy S b (γ.U s) (γ.V s) / b + σ ^ 2)) ∧
      (∫ x in s..t, (cylinderEnergy S b (γ.U x) (γ.V x) / b) ^ 2 / b) ≤
        Cbudget * (cylinderEnergy S b (γ.U s) (γ.V s) / b + σ ^ 2) := by
  obtain ⟨Cout, hCout, hout⟩ := charged_cool_outgoing_budget_of_observation Tstar Cstar hTs hCs
  refine ⟨14 + 5 * Cout, by positivity, ?_⟩
  intro ui e b δ s t S h hb hst hδ γ hac hweak hcylinder hobs
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
  let B := fun x => ‖y x‖ ^ 2 + ‖z x‖ ^ 2 + μ x ^ 2 + q x ^ 2
  have cq : ContinuousOn q (Icc s t) := by
    simpa only [uIcc_of_le hst.le] using hcylinder.1.continuousOn
  have cB : ContinuousOn B (Icc s t) :=
    (((cy.norm.pow 2).add (cz.norm.pow 2)).add (cμ.pow 2)).add (cq.pow 2)
  have hfull : (∫ x in s..t, B x / b) ≤
      5 * (∫ x in s..t, f x / b) + 2 * (∫ x in s..t, D x / b) := by
    have hi := intervalIntegral.integral_mono_on (μ := volume) hst.le
      ((cB.div_const b).intervalIntegrable_of_Icc hst.le)
      ((((cf.div_const b).const_mul 5).add
        ((cD.div_const b).const_mul 2)).intervalIntegrable_of_Icc hst.le) (by
        intro x hx
        have hz : ‖z x‖ ≤ ‖y x‖ + ‖y x - z x‖ := by
          calc
            _ = ‖y x - (y x - z x)‖ := by congr 1; abel
            _ ≤ _ := norm_sub_le _ _
        have hzsq := (sq_le_sq₀ (norm_nonneg (z x)) (by positivity)).2 hz
        have hq2 := (hp x hx).2.2.1
        change q x ^ 2 ≤ 2 * f x at hq2
        have hpoint : B x ≤ 5 * f x + 2 * D x := by
          dsimp only [B, f, D] at ⊢ hq2
          nlinarith only [hzsq, hq2, sq_nonneg (‖y x‖ - ‖y x - z x‖), sq_nonneg (μ x)]
        calc
          B x / b ≤ (5 * f x + 2 * D x) / b := div_le_div_of_nonneg_right hpoint hb.le
          _ = _ := by dsimp only [Pi.add_apply]; ring)
    simp only [Pi.add_apply] at hi
    rw [intervalIntegral.integral_add
      (((cf.div_const b).intervalIntegrable_of_Icc hst.le).const_mul 5)
      (((cD.div_const b).intervalIntegrable_of_Icc hst.le).const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
    exact hi
  rw [hσeq]
  constructor
  · intro x hx
    have hs := hqn s (left_mem_Icc.mpr hst.le)
    have hCq := mul_nonneg hCout.le hs
    have hCσ := mul_nonneg hCout.le (sq_nonneg σ)
    change q x + (∫ y in s..t, D y) / b ≤ (14 + 5 * Cout) * (q s + σ ^ 2)
    rw [← intervalIntegral.integral_div]
    nlinarith only [hsup x hx, hdiss, hs, sq_nonneg σ, hCq, hCσ]
  · constructor
    · intro x hx
      have hm := (hp x hx).2.2.2.2
      have hy := (hn x hx).2
      have hs := hqn s (left_mem_Icc.mpr hst.le)
      have hCq := mul_nonneg hCout.le hs
      have hCσ := mul_nonneg hCout.le (sq_nonneg σ)
      change S.m (γ.U x) (γ.V x) / b + ‖y x‖ ^ 2 + (∫ y in s..t, B y / b) ≤
        (14 + 5 * Cout) * (q s + σ ^ 2)
      nlinarith only [hm, hy, hsup x hx, hdiss, hfull, houti, hs, sq_nonneg σ, hCq, hCσ]
    · have hqi : (∫ x in s..t, q x ^ 2 / b) ≤ ∫ x in s..t, B x / b := by
        apply intervalIntegral.integral_mono_on hst.le
          (((cq.pow 2).div_const b).intervalIntegrable_of_Icc hst.le)
          ((cB.div_const b).intervalIntegrable_of_Icc hst.le)
        intro x hx
        apply div_le_div_of_nonneg_right _ hb.le
        dsimp only [B, Pi.pow_apply]
        nlinarith only [sq_nonneg ‖y x‖, sq_nonneg ‖z x‖, sq_nonneg (μ x)]
      have hs := hqn s (left_mem_Icc.mpr hst.le)
      have hCq := mul_nonneg hCout.le hs
      have hCσ := mul_nonneg hCout.le (sq_nonneg σ)
      change (∫ x in s..t, q x ^ 2 / b) ≤ (14 + 5 * Cout) * (q s + σ ^ 2)
      nlinarith only [hqi, hfull, houti, hdiss, hs, sq_nonneg σ, hCq, hCσ]

end EmcsfAcExtension.Global.Cooling
