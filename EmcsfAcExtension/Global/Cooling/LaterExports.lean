/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Cooling.ObservationExports
import EmcsfAcExtension.Global.Cooling.Decrease
import EmcsfAcExtension.Infra.AC.Variation

/-! # Averaging, subintervals and decrease after observation

The only upstream premise in these untagged helpers is the observation
proposition. Every energy and clock estimate is proved from original data.
Source: `charged_SF_new_version.tex:L2986`–L3021.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global.Cooling

/-- [internal] The literal latter-half averaged small-energy time
(L2697–L2708), with observation as the only upstream result. `C` depends
only on the fixed gap through observation and precedes `H` and all data. -/
theorem averaged_small_energy_time_of_observation (δ : ℝ) (_hδ : 0 < δ ∧ δ < 1)
    (hobs : observationInput δ) :
    ∃ Tstar Cstar δstar ηstar C : ℝ,
    0 < Tstar ∧ 0 < Cstar ∧ 0 < δstar ∧ δstar ≤ 1 / 2 ∧ 0 < ηstar ∧ 0 < C ∧
    ∀ H : ℝ, 0 < H →
    ∀ (ui e b ε T : ℝ) (S : Fields), 0 < b → 0 < ε → 0 < T → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b 0 T,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V 0) 0 T →
    (∀ τ ∈ Icc 0 T, S.mu (γ.U τ) (γ.V τ) +
      ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    (∀ τ ∈ Icc (0 + Tstar * b) (T - Tstar * b),
      triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
    cylinderEnergy S b (γ.U 0) (γ.V 0) / b ≤ ε → T = H * b / ε →
    let σ := (curveCovVar e S S.a γ.U γ.V 0 T).toReal
    ∃ x ∈ Icc (T / 2) T,
      cylinderEnergy S b (γ.U x) (γ.V x) / b ≤
        Real.sqrt ((2 * C * ε / H) * (ε + σ ^ 2)) ∧
      Real.sqrt ((2 * C * ε / H) * (ε + σ ^ 2)) ≤
        Real.sqrt (2 * C / H) * (ε + Real.sqrt ε * σ) := by
  obtain ⟨Ts, Cs, δs, ηs, C, hTs, hCs, hδs, hδhalf, hηs, hC, hbudget⟩ :=
    squared_energy_of_observation δ _hδ hobs
  refine ⟨Ts, Cs, δs, ηs, C, hTs, hCs, hδs, hδhalf, hηs, hC, ?_⟩
  intro H hH ui e b ε T S hb hε hT h γ hac hweak hwindows hq₀ hclock
  let q := fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b
  have hi := hbudget ui e b 0 T S hb hT h γ hac hweak hwindows
  have hbound : (∫ x in 0..T, q x ^ 2 / b) ≤
      C * (ε + (curveCovVar e S S.a γ.U γ.V 0 T).toReal ^ 2) :=
    hi.trans (mul_le_mul_of_nonneg_left (add_le_add hq₀ le_rfl) hC.le)
  have cq : ContinuousOn q (Icc 0 T) := by
    simpa only [uIcc_of_le hT.le] using
      (charged_cool_identity ui e b 0 T S h hb hT γ hac).1.continuousOn
  exact averaged_energy_envelope_of_budget C H hC hH q b ε T _ hb hε
    ENNReal.toReal_nonneg hclock cq
    (fun x hx => (normalized_energy_lower hb (h.mu _ (γ.mem x hx))).1) hbound

/-- [internal] Both literal supremum budgets on every ordered
subinterval, including a singleton and arbitrarily short unfinished stages
(L2691–L2695). Each interval uses its own initial energy, parallel anchor,
variation, and endpoint strips. Observation is the sole upstream premise;
the constant depends only on the fixed gap, before all physical data. -/
theorem subinterval_budgets_of_observation (δ : ℝ) (_hδ : 0 < δ ∧ δ < 1)
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
    ∀ a ∈ Icc s t, ∀ c ∈ Icc a t,
    let σ := (curveCovVar e S S.a γ.U γ.V a c).toReal
    (sSup ((fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b) '' Icc a c) +
        cylinderDissipation S γ.U γ.V a c / b ≤
      C * (cylinderEnergy S b (γ.U a) (γ.V a) / b + σ ^ 2)) ∧
    (sSup ((fun x => S.m (γ.U x) (γ.V x) / b +
      ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2) '' Icc a c) +
        (∫ x in a..c,
          (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           ‖S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           S.mu (γ.U x) (γ.V x) ^ 2 +
           (cylinderEnergy S b (γ.U x) (γ.V x) / b) ^ 2) / b) ≤
      C * (cylinderEnergy S b (γ.U a) (γ.V a) / b + σ ^ 2)) := by
  obtain ⟨Ts, Cs, δs, ηs, C, hTs, hCs, hδs, hδhalf, hηs, hC, hbudget⟩ :=
    budgets_of_observation δ _hδ hobs
  refine ⟨Ts, Cs, δs, ηs, C + 6, hTs, hCs, hδs, hδhalf, hηs, by positivity, ?_⟩
  intro ui e b s t S hb hst h γ hac hweak hwindows a ha c hc
  have hsub : Icc a c ⊆ Icc s t := Icc_subset_Icc ha.1 hc.2
  have hBn : 0 ≤ cylinderEnergy S b (γ.U a) (γ.V a) / b +
      (curveCovVar e S S.a γ.U γ.V a c).toReal ^ 2 :=
    add_nonneg (normalized_energy_lower hb (h.mu _ (γ.mem a ha))).1 (sq_nonneg _)
  have hscale : C * (cylinderEnergy S b (γ.U a) (γ.V a) / b +
      (curveCovVar e S S.a γ.U γ.V a c).toReal ^ 2) ≤
      (C + 6) * (cylinderEnergy S b (γ.U a) (γ.V a) / b +
      (curveCovVar e S S.a γ.U γ.V a c).toReal ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) hBn
  rcases lt_or_eq_of_le hc.1 with hlt | rfl
  · have hacsub := curveParallel_ac_subinterval hst.le
      (connection_intervalIntegrable h hst.le γ) hac hlt.le hsub
    have hweaksub : ∀ x ∈ Icc a c, S.mu (γ.U x) (γ.V x) +
        ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ≤ δs :=
      fun x hx => hweak x (hsub hx)
    have hwindowsub : ∀ x ∈ Icc (a + Ts * b) (c - Ts * b),
        triangle (γ.U (x - Ts * b)) (γ.V (x + Ts * b)) ⊆ origDomain ui ∧
        (∀ p ∈ triangle (γ.U (x - Ts * b)) (γ.V (x + Ts * b)),
          0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
        |e| * b * (1 + ‖S.a (γ.U x) (γ.V x)‖) ≤ ηs := by
      intro x hx
      apply hwindows x
      constructor <;> linarith only [hx.1, hx.2, ha.1, hc.2]
    have hi := hbudget ui e b a c S hb hlt h (restrictCylinder γ hsub)
      hacsub hweaksub hwindowsub
    dsimp only [restrictCylinder] at hi
    exact ⟨hi.2.2.1.trans hscale, hi.2.2.2.1.trans hscale⟩
  · have hp := weak_regime_energy_comparison S b (γ.U a) (γ.V a) δs hb
      (γ.radius a ha) (h.mu _ (γ.mem a ha)).1 hδhalf (hweak a ha)
    have hy := (normalized_energy_lower hb (h.mu _ (γ.mem a ha))).2
    have hn := (normalized_energy_lower hb (h.mu _ (γ.mem a ha))).1
    have hvar : curveCovVar e S S.a γ.U γ.V a a = 0 := by
      simp [curveCovVar_def]
    simp only [Icc_self, image_singleton, csSup_singleton,
      cylinderDissipation, intervalIntegral.integral_same, zero_div,
      hvar, ENNReal.toReal_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
    constructor
    · nlinarith only [hn, mul_nonneg hC.le hn]
    · nlinarith only [hp.2.2.2.2, hy, hn, mul_nonneg hC.le hn]

end EmcsfAcExtension.Global.Cooling
