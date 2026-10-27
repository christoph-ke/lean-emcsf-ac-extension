/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Cooling.IdentityBudgets
import EmcsfAcExtension.Global.Observation.Energy
import EmcsfAcExtension.Infra.AC.Variation

/-! # Cooling nodes that precede observation

These exports retain the proposition hypotheses for its energy and
endpoint nodes. Their constants are chosen before the physical data.
Source: `charged_SF_new_version.tex:L2833`–L2840, L2898–L2915, L2948–L2960,
and L3002–L3006. The observation proposition is never assumed.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global

/-- [node eq:charged-cool-energy]
The literal supremum-plus-dissipation budget, retaining the proposition
hypotheses (L2535–L2542). The witness `C = 6` is universal, hence depends
only on the fixed observation constants; it precedes all physical data. -/
theorem charged_cool_energy (δ Tstar Cstar δstar ηstar : ℝ)
    (_hδ : 0 < δ ∧ δ < 1) (_hTs : 0 < Tstar) (_hCs : 0 < Cstar)
    (_hδs : 0 < δstar ∧ δstar ≤ 1 / 2) (_hηs : 0 < ηstar) :
    ∃ C > 0, ∀ (ui e b T : ℝ) (S : Fields), 0 < b → 0 < T → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b 0 T,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V 0) 0 T →
    (∀ τ ∈ Icc 0 T, S.mu (γ.U τ) (γ.V τ) +
      ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    (∀ τ ∈ Icc (Tstar * b) (T - Tstar * b),
      triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
    sSup ((fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b) '' Icc 0 T) +
        cylinderDissipation S γ.U γ.V 0 T / b ≤
      C * (cylinderEnergy S b (γ.U 0) (γ.V 0) / b +
        (curveCovVar e S S.a γ.U γ.V 0 T).toReal ^ 2) := by
  refine ⟨6, by norm_num, ?_⟩
  intro ui e b T S hb hT h γ hac _ _
  exact charged_cool_energy_sup ui e b 0 T S h hb hT γ hac

/-- [node prop:charged-cool#endpoint-interval-budget]
The missed endpoint strips have total length at most `2*Tstar*b`, and
their density budget is controlled by the actual energy supremum and by
initial energy plus squared variation. This includes the empty center set
(L2653–L2665). The witness `C = 12*Tstar` precedes all physical data. -/
theorem charged_cool_endpoint_interval_budget (δ Tstar Cstar δstar ηstar : ℝ)
    (_hδ : 0 < δ ∧ δ < 1) (hTs : 0 < Tstar) (_hCs : 0 < Cstar)
    (hδs : 0 < δstar ∧ δstar ≤ 1 / 2) (_hηs : 0 < ηstar) :
    ∃ C > 0, ∀ (ui e b T : ℝ) (S : Fields), 0 < b → 0 < T → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b 0 T,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V 0) 0 T →
    (∀ τ ∈ Icc 0 T, S.mu (γ.U τ) (γ.V τ) +
      ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    (∀ τ ∈ Icc (Tstar * b) (T - Tstar * b),
      triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
    volume (Icc 0 T \ Icc (Tstar * b) (T - Tstar * b)) ≤ ENNReal.ofReal (2 * Tstar * b) ∧
    (∫ x in Icc 0 T \ Icc (Tstar * b) (T - Tstar * b),
      (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
        S.mu (γ.U x) (γ.V x) ^ 2) / b) ≤
      C * sSup ((fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b) '' Icc 0 T) ∧
    (∫ x in Icc 0 T \ Icc (Tstar * b) (T - Tstar * b),
      (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
        S.mu (γ.U x) (γ.V x) ^ 2) / b) ≤
      C * (cylinderEnergy S b (γ.U 0) (γ.V 0) / b +
        (curveCovVar e S S.a γ.U γ.V 0 T).toReal ^ 2) := by
  refine ⟨12 * Tstar, by positivity, ?_⟩
  intro ui e b T S hb hT h γ hac hweak _
  let q := fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b
  let M := sSup (q '' Icc 0 T)
  let σ := (curveCovVar e S S.a γ.U γ.V 0 T).toReal
  let f := fun x => (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
    S.mu (γ.U x) (γ.V x) ^ 2) / b
  have hq := (charged_cool_identity ui e b 0 T S h hb hT γ hac).1
  have cq : ContinuousOn q (Icc 0 T) := by
    simpa only [uIcc_of_le hT.le] using hq.continuousOn
  have hle (x : ℝ) (hx : x ∈ Icc 0 T) : q x ≤ M :=
    le_csSup (isCompact_Icc.bddAbove_image cq) (mem_image_of_mem _ hx)
  have hqn := (Cooling.normalized_energy_lower hb (h.mu _ (γ.mem 0 (left_mem_Icc.mpr hT.le)))).1
  have hMn : 0 ≤ M := hqn.trans (hle 0 (left_mem_Icc.mpr hT.le))
  obtain ⟨cy, _, cμ⟩ := Cylinder.continuousOn_normalized_traces h.solution γ
  have hf : IntegrableOn f (Icc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mp
      ((((cy.norm.pow 2).add (cμ.pow 2)).div_const b).intervalIntegrable_of_Icc hT.le)
  have hfq (x : ℝ) (hx : x ∈ Icc 0 T) : f x ≤ 3 * q x / b := by
    have hp := Cooling.weak_regime_energy_comparison S b (γ.U x) (γ.V x) δstar hb
      (γ.radius x hx) (h.mu _ (γ.mem x hx)).1 hδs.2 (hweak x hx)
    have hμ := (h.mu _ (γ.mem x hx)).1
    have hμup : S.mu (γ.U x) (γ.V x) ≤ 1 / 2 := by
      linarith [hweak x hx, hδs.2, norm_nonneg (S.theta (γ.U x) (γ.V x) /
        (S.lam (γ.U x) (γ.V x) : ℂ))]
    apply div_le_div_of_nonneg_right _ hb.le
    have hy := (Cooling.normalized_energy_lower hb (h.mu _ (γ.mem x hx))).2
    change ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
      S.mu (γ.U x) (γ.V x) ^ 2 ≤ 3 * q x
    nlinarith only [hp.1, hy, hμ, hμup]
  have hi := Cooling.endpoint_interval_budget_of_bound (mul_nonneg hTs.le hb.le)
    (by positivity : 0 ≤ 3 * M / b) hf (fun x hx =>
      (hfq x hx).trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hle x hx) (by norm_num)) hb.le))
  have he : 2 * (Tstar * b) * (3 * M / b) = 6 * Tstar * M := by field_simp; ring
  rw [he, zero_add] at hi
  have hs := charged_cool_supremum_energy_bound ui e b 0 T S h hb hT γ hac
  change M ≤ 2 * q 0 + σ ^ 2 at hs
  refine ⟨?_, ?_, ?_⟩
  · simpa only [zero_add, mul_assoc] using
      Cooling.volume_endpoint_strips_le 0 T (Tstar * b) (mul_nonneg hTs.le hb.le)
  · change (∫ x in Icc 0 T \ Icc (Tstar * b) (T - Tstar * b), f x) ≤ 12 * Tstar * M
    nlinarith only [hi, mul_nonneg hTs.le hMn]
  · change (∫ x in Icc 0 T \ Icc (Tstar * b) (T - Tstar * b), f x) ≤
      12 * Tstar * (q 0 + σ ^ 2)
    have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 6 * Tstar)
    nlinarith only [hi, hm, mul_nonneg hTs.le (sq_nonneg σ)]

/-- [node prop:charged-cool#cooling-time-propagation]
Every chosen time in the latter half propagates to the endpoint, using
only that subinterval's energy estimate and variation monotonicity
(L2709–L2713). The coefficients are universal; observation is not used. -/
theorem charged_cool_cooling_time_propagation (ui e b T : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hb : 0 < b) (hT : 0 < T)
    (γ : ClockCylinder S (origDomain ui) b 0 T)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V 0) 0 T) :
    ∀ s ∈ Icc (T / 2) T,
      cylinderEnergy S b (γ.U T) (γ.V T) / b ≤
        2 * (cylinderEnergy S b (γ.U s) (γ.V s) / b) +
          (curveCovVar e S S.a γ.U γ.V 0 T).toReal ^ 2 := by
  intro s hs
  have hs0 : 0 ≤ s := by linarith only [hs.1, hT]
  rcases lt_or_eq_of_le hs.2 with hst | heq
  · have hsub : Icc s T ⊆ Icc 0 T := Icc_subset_Icc hs0 le_rfl
    have hA := Cooling.connection_intervalIntegrable h hT.le γ
    have hacsub := Cooling.curveParallel_ac_subinterval hT.le hA hac hst.le hsub
    have hv : curveCovVar e S S.a γ.U γ.V s T ≤ curveCovVar e S S.a γ.U γ.V 0 T := by
      rw [Cooling.curveCovVar_eq_restricted_variation hT.le hA hsub hst.le]
      exact eVariationOn.mono _ hsub
    have hvr := ENNReal.toReal_mono (hac.boundedVariationOn_Icc hT.le) hv
    have he := (charged_cool_energy_bounds ui e b s T S h hb hst
      (Cooling.restrictCylinder γ hsub) hacsub).1 T (right_mem_Icc.mpr hst.le)
    dsimp only [Cooling.restrictCylinder] at he
    exact he.trans (add_le_add le_rfl
      ((sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).2 hvr))
  · rw [heq]
    have hn := (Cooling.normalized_energy_lower hb
      (h.mu _ (γ.mem T (right_mem_Icc.mpr hT.le)))).1
    nlinarith only [hn, sq_nonneg (curveCovVar e S S.a γ.U γ.V 0 T).toReal]

end EmcsfAcExtension.Global
