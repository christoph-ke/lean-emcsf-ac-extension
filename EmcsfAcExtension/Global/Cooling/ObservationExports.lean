/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Cooling.ObservationInput
public import EmcsfAcExtension.Global.Cooling.WindowBudgets
import EmcsfAcExtension.Infra.AC.Variation

/-! # Cooling budgets with observation as the only upstream premise

The cylinder balance and all local window inequalities are discharged.
The helpers deliberately carry no node tags until observation lands.
Source: `charged_SF_new_version.tex:L2923`–L2988.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Cooling

/-- [internal] Simultaneous actual-field center, outgoing, energy,
full integrated and squared-energy budgets. Observation is the only
remaining upstream result. All constants precede physical data and depend
only on the gap through the observation constants. -/
theorem budgets_of_observation (δ : ℝ) (_hδ : 0 < δ ∧ δ < 1)
    (hobs : observationInput δ) :
    ∃ Tstar Cstar δstar ηstar C : ℝ,
    0 < Tstar ∧ 0 < Cstar ∧ 0 < δstar ∧ δstar ≤ 1 / 2 ∧ 0 < ηstar ∧ 0 < C ∧
    ∀ (ui e b s t : ℝ) (S : Fields), 0 < b → s < t → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b s t,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t →
    (∀ τ ∈ Icc s t, S.mu (γ.U τ) (γ.V τ) +
      ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    (∀ τ ∈ Icc (s + Tstar * b) (t - Tstar * b),
      triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
    let σ := (curveCovVar e S S.a γ.U γ.V s t).toReal
    ((∫ x in Icc (s + Tstar * b) (t - Tstar * b),
      (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
        S.mu (γ.U x) (γ.V x) ^ 2) / b) ≤
      2 * Cstar * Tstar * (cylinderDissipation S γ.U γ.V s t / b + σ ^ 2)) ∧
    ((∫ x in s..t,
      (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
        S.mu (γ.U x) (γ.V x) ^ 2) / b) ≤
      C * (cylinderEnergy S b (γ.U s) (γ.V s) / b + σ ^ 2)) ∧
    (sSup ((fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b) '' Icc s t) +
        cylinderDissipation S γ.U γ.V s t / b ≤
      C * (cylinderEnergy S b (γ.U s) (γ.V s) / b + σ ^ 2)) ∧
    (sSup ((fun x => S.m (γ.U x) (γ.V x) / b +
      ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2) '' Icc s t) +
        (∫ x in s..t,
          (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           ‖S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           S.mu (γ.U x) (γ.V x) ^ 2 +
           (cylinderEnergy S b (γ.U x) (γ.V x) / b) ^ 2) / b) ≤
      C * (cylinderEnergy S b (γ.U s) (γ.V s) / b + σ ^ 2)) ∧
    ((∫ x in s..t, (cylinderEnergy S b (γ.U x) (γ.V x) / b) ^ 2 / b) ≤
      C * (cylinderEnergy S b (γ.U s) (γ.V s) / b + σ ^ 2)) := by
  obtain ⟨Ts, Cs, δs, ηs, hTs, hCs, hδs, hηs, hobs⟩ := hobs
  obtain ⟨Cb, hCb, hfield⟩ := charged_cool_integrated_of_observation_of_cylinder Ts Cs hTs hCs
  obtain ⟨Co, hCo, hwindow⟩ := charged_cool_window_budgets_of_window_observation Ts Cs hTs hCs
  let δw := min δs (1 / 2)
  refine ⟨Ts, Cs, δw, ηs, Cb + Co + 6, hTs, hCs, lt_min hδs (by norm_num),
    min_le_right _ _, hηs, by positivity, ?_⟩
  intro ui e b s t S hb hst h γ hac hweak hwindows
  have hA := connection_intervalIntegrable h hst.le γ
  have hlocalobs (x : ℝ) (hx : x ∈ Icc (s + Ts * b) (t - Ts * b)) :
      ENNReal.ofReal (b * (‖S.theta (γ.U x) (γ.V x) /
        (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 + S.mu (γ.U x) (γ.V x) ^ 2)) ≤
        ENNReal.ofReal Cs *
          (ENNReal.ofReal (cylinderDissipation S γ.U γ.V (x - Ts * b) (x + Ts * b)) +
            ENNReal.ofReal b * (curveCovVar e S S.a γ.U γ.V (x - Ts * b) (x + Ts * b)) ^ 2) := by
    have hsub : Icc (x - Ts * b) (x + Ts * b) ⊆ Icc s t := by
      intro y hy
      constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2]
    have hwin : x - Ts * b ≤ x + Ts * b := by linarith [mul_pos hTs hb]
    simpa only [restrictCylinder] using
      hobs ui e b x S hb h (restrictCylinder γ hsub)
        (hwindows x hx).1 (hwindows x hx).2.1
        (curveParallel_ac_subinterval hst.le hA hac hwin hsub)
        (fun y hy => (hweak y (hsub hy)).trans (min_le_left _ _)) (hwindows x hx).2.2
  have hi := charged_cool_identity ui e b s t S h hb hst γ hac
  have hf := hfield ui e b δw s t S h hb hst (min_le_right _ _) γ hac hweak hi hlocalobs
  have hw := hwindow ui e b δw s t S h hb hst (min_le_right _ _) γ hac hweak hlocalobs
  let B := cylinderEnergy S b (γ.U s) (γ.V s) / b +
    (curveCovVar e S S.a γ.U γ.V s t).toReal ^ 2
  have hBn : 0 ≤ B := add_nonneg
    (normalized_energy_lower hb (h.mu _ (γ.mem s (left_mem_Icc.mpr hst.le)))).1 (sq_nonneg _)
  have hCbmono : Cb * B ≤ (Cb + Co + 6) * B := mul_le_mul_of_nonneg_right (by linarith) hBn
  have hComono : Co * B ≤ (Cb + Co + 6) * B := mul_le_mul_of_nonneg_right (by linarith) hBn
  have h6 : 6 * B ≤ (Cb + Co + 6) * B := mul_le_mul_of_nonneg_right (by linarith) hBn
  refine ⟨hw.1, hw.2.trans hComono, ?_, ?_, hf.2.2.trans hCbmono⟩
  · exact (charged_cool_energy_sup ui e b s t S h hb hst γ hac).trans h6
  · have hs : sSup ((fun x => S.m (γ.U x) (γ.V x) / b +
          ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2) '' Icc s t) ≤
        Cb * B - (∫ x in s..t,
          (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           ‖S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           S.mu (γ.U x) (γ.V x) ^ 2 +
           (cylinderEnergy S b (γ.U x) (γ.V x) / b) ^ 2) / b) := by
      apply csSup_le ((nonempty_Icc.mpr hst.le).image _)
      rintro _ ⟨x, hx, rfl⟩
      exact (le_sub_iff_add_le).mpr (hf.2.1 x hx)
    exact ((le_sub_iff_add_le).mp hs).trans hCbmono

/-- [internal] Full-window center estimate with exact coefficient `2*Cstar*Tstar`.
Observation is the only upstream premise. Constants depend only on the
fixed gap through the observation constants, before all physical data. -/
theorem centers_of_observation (δ : ℝ) (_hδ : 0 < δ ∧ δ < 1)
    (hobs : observationInput δ) :
    ∃ Tstar Cstar δstar ηstar C : ℝ,
    0 < Tstar ∧ 0 < Cstar ∧ 0 < δstar ∧ δstar ≤ 1 / 2 ∧ 0 < ηstar ∧ 0 < C ∧
    ∀ (ui e b s t : ℝ) (S : Fields), 0 < b → s < t → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b s t,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t →
    (∀ τ ∈ Icc s t, S.mu (γ.U τ) (γ.V τ) +
      ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    (∀ τ ∈ Icc (s + Tstar * b) (t - Tstar * b),
      triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
    let σ := (curveCovVar e S S.a γ.U γ.V s t).toReal
    (∫ x in Icc (s + Tstar * b) (t - Tstar * b),
      (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
        S.mu (γ.U x) (γ.V x) ^ 2) / b) ≤
      2 * Cstar * Tstar * (cylinderDissipation S γ.U γ.V s t / b + σ ^ 2) := by
  obtain ⟨Ts, Cs, δs, ηs, C, hTs, hCs, hδs, hδhalf, hηs, hC, hbudget⟩ :=
    budgets_of_observation δ _hδ hobs
  refine ⟨Ts, Cs, δs, ηs, C, hTs, hCs, hδs, hδhalf, hηs, hC, ?_⟩
  intro ui e b s t S hb hst h γ hac hweak hwindows
  have hbudget := hbudget ui e b s t S hb hst h γ hac hweak hwindows
  exact hbudget.1

/-- [internal] Full outgoing-ratio and mass-square budget, including short intervals.
Observation is the only upstream premise. Constants depend only on the
fixed gap through the observation constants, before all physical data. -/
theorem outgoing_budget_of_observation (δ : ℝ) (_hδ : 0 < δ ∧ δ < 1)
    (hobs : observationInput δ) :
    ∃ Tstar Cstar δstar ηstar C : ℝ,
    0 < Tstar ∧ 0 < Cstar ∧ 0 < δstar ∧ δstar ≤ 1 / 2 ∧ 0 < ηstar ∧ 0 < C ∧
    ∀ (ui e b s t : ℝ) (S : Fields), 0 < b → s < t → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b s t,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t →
    (∀ τ ∈ Icc s t, S.mu (γ.U τ) (γ.V τ) +
      ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    (∀ τ ∈ Icc (s + Tstar * b) (t - Tstar * b),
      triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
    let σ := (curveCovVar e S S.a γ.U γ.V s t).toReal
    (∫ x in s..t,
      (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
        S.mu (γ.U x) (γ.V x) ^ 2) / b) ≤
      C * (cylinderEnergy S b (γ.U s) (γ.V s) / b + σ ^ 2) := by
  obtain ⟨Ts, Cs, δs, ηs, C, hTs, hCs, hδs, hδhalf, hηs, hC, hbudget⟩ :=
    budgets_of_observation δ _hδ hobs
  refine ⟨Ts, Cs, δs, ηs, C, hTs, hCs, hδs, hδhalf, hηs, hC, ?_⟩
  intro ui e b s t S hb hst h γ hac hweak hwindows
  have hbudget := hbudget ui e b s t S hb hst h γ hac hweak hwindows
  exact hbudget.2.1

/-- [internal] Literal supremum-plus-integral budget on any proper interval.
Observation is the only upstream premise. Constants depend only on the
fixed gap through the observation constants, before all physical data. -/
theorem integrated_of_observation (δ : ℝ) (_hδ : 0 < δ ∧ δ < 1)
    (hobs : observationInput δ) :
    ∃ Tstar Cstar δstar ηstar C : ℝ,
    0 < Tstar ∧ 0 < Cstar ∧ 0 < δstar ∧ δstar ≤ 1 / 2 ∧ 0 < ηstar ∧ 0 < C ∧
    ∀ (ui e b s t : ℝ) (S : Fields), 0 < b → s < t → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b s t,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t →
    (∀ τ ∈ Icc s t, S.mu (γ.U τ) (γ.V τ) +
      ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    (∀ τ ∈ Icc (s + Tstar * b) (t - Tstar * b),
      triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
    let σ := (curveCovVar e S S.a γ.U γ.V s t).toReal
    sSup ((fun x => S.m (γ.U x) (γ.V x) / b +
      ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2) '' Icc s t) +
        (∫ x in s..t,
          (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           ‖S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           S.mu (γ.U x) (γ.V x) ^ 2 +
           (cylinderEnergy S b (γ.U x) (γ.V x) / b) ^ 2) / b) ≤
      C * (cylinderEnergy S b (γ.U s) (γ.V s) / b + σ ^ 2) := by
  obtain ⟨Ts, Cs, δs, ηs, C, hTs, hCs, hδs, hδhalf, hηs, hC, hbudget⟩ :=
    budgets_of_observation δ _hδ hobs
  refine ⟨Ts, Cs, δs, ηs, C, hTs, hCs, hδs, hδhalf, hηs, hC, ?_⟩
  intro ui e b s t S hb hst h γ hac hweak hwindows
  have hbudget := hbudget ui e b s t S hb hst h γ hac hweak hwindows
  exact hbudget.2.2.2.1

/-- [internal] Squared normalized energy budget on any proper interval.
Observation is the only upstream premise. Constants depend only on the
fixed gap through the observation constants, before all physical data. -/
theorem squared_energy_of_observation (δ : ℝ) (_hδ : 0 < δ ∧ δ < 1)
    (hobs : observationInput δ) :
    ∃ Tstar Cstar δstar ηstar C : ℝ,
    0 < Tstar ∧ 0 < Cstar ∧ 0 < δstar ∧ δstar ≤ 1 / 2 ∧ 0 < ηstar ∧ 0 < C ∧
    ∀ (ui e b s t : ℝ) (S : Fields), 0 < b → s < t → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b s t,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t →
    (∀ τ ∈ Icc s t, S.mu (γ.U τ) (γ.V τ) +
      ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    (∀ τ ∈ Icc (s + Tstar * b) (t - Tstar * b),
      triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
    let σ := (curveCovVar e S S.a γ.U γ.V s t).toReal
    (∫ x in s..t, (cylinderEnergy S b (γ.U x) (γ.V x) / b) ^ 2 / b) ≤
      C * (cylinderEnergy S b (γ.U s) (γ.V s) / b + σ ^ 2) := by
  obtain ⟨Ts, Cs, δs, ηs, C, hTs, hCs, hδs, hδhalf, hηs, hC, hbudget⟩ :=
    budgets_of_observation δ _hδ hobs
  refine ⟨Ts, Cs, δs, ηs, C, hTs, hCs, hδs, hδhalf, hηs, hC, ?_⟩
  intro ui e b s t S hb hst h γ hac hweak hwindows
  have hbudget := hbudget ui e b s t S hb hst h γ hac hweak hwindows
  exact hbudget.2.2.2.2

end EmcsfAcExtension.Global.Cooling
