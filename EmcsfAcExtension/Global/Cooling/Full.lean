/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Cooling.LaterExports
import EmcsfAcExtension.Global.Cooling.Decrease
import EmcsfAcExtension.Infra.AC.Variation

/-! # The full cooling proposition awaiting observation

Both literal supremum budgets on every ordered subinterval and the
endpoint decrease share constants fixed before all physical data.
Source: `charged_SF_new_version.tex:L2798`–L2871, L2986–L3021.
-/

public section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace EmcsfAcExtension.Global

open Cooling

/-- [internal] The entire source cooling proposition, with literal real
suprema and both budgets on all ordered subintervals, including singletons.
Observation is the only remaining upstream result. `Cbudget` depends only
on the observation constants; `Hd,Cd` only on those constants and `d`,
before all physical data. This helper is ready for a node-tagged wrapper
when observation lands. -/
theorem charged_cool_full_of_observation (δ : ℝ) (_hδ : 0 < δ ∧ δ < 1)
    (hobs : Cooling.observationInput δ) :
    ∃ Tstar δstar ηstar Cbudget : ℝ,
    0 < Tstar ∧ 0 < δstar ∧ 0 < ηstar ∧ 0 < Cbudget ∧
    ∀ d : ℝ, 0 < d → ∃ Hd Cd : ℝ, 0 < Hd ∧ 0 < Cd ∧
    ∀ (ui e b ε T : ℝ) (S : Fields), 0 < b → 0 < ε → 0 < T → OriginalData ui e S →
    ∀ γ : ClockCylinder S (origDomain ui) b 0 T,
    AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V 0) 0 T →
    (∀ τ ∈ Icc 0 T, S.mu (γ.U τ) (γ.V τ) +
      ‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ≤ δstar) →
    (∀ τ ∈ Icc (Tstar * b) (T - Tstar * b),
      triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)) ⊆ origDomain ui ∧
      (∀ p ∈ triangle (γ.U (τ - Tstar * b)) (γ.V (τ + Tstar * b)),
        0 ≤ S.mu p.1 p.2 ∧ δ ≤ 1 - S.mu p.1 p.2) ∧
      |e| * b * (1 + ‖S.a (γ.U τ) (γ.V τ)‖) ≤ ηstar) →
    (∀ a ∈ Icc 0 T, ∀ c ∈ Icc a T,
      let σ := (curveCovVar e S S.a γ.U γ.V a c).toReal
      (sSup ((fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b) '' Icc a c) +
        cylinderDissipation S γ.U γ.V a c / b ≤
      Cbudget * (cylinderEnergy S b (γ.U a) (γ.V a) / b + σ ^ 2)) ∧
      (sSup ((fun x => S.m (γ.U x) (γ.V x) / b +
      ‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2) '' Icc a c) +
        (∫ x in a..c,
          (‖S.theta (γ.U x) (γ.V x) / (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           ‖S.xi (γ.U x) (γ.V x) / (S.nu (γ.U x) (γ.V x) : ℂ)‖ ^ 2 +
           S.mu (γ.U x) (γ.V x) ^ 2 +
           (cylinderEnergy S b (γ.U x) (γ.V x) / b) ^ 2) / b) ≤
      Cbudget * (cylinderEnergy S b (γ.U a) (γ.V a) / b + σ ^ 2))) ∧
    (cylinderEnergy S b (γ.U 0) (γ.V 0) / b ≤ ε → T = Hd * b / ε →
      cylinderEnergy S b (γ.U T) (γ.V T) / b ≤ d * ε + Cd *
        (curveCovVar e S S.a γ.U γ.V 0 T).toReal ^ 2) := by
  obtain ⟨Ts, Cs, δs, ηs, C, hTs, hCs, hδs, hδhalf, hηs, hC, hbudget⟩ :=
    Cooling.budgets_of_observation δ _hδ hobs
  refine ⟨Ts, δs, ηs, C + 6, hTs, hδs, hηs, by positivity, ?_⟩
  intro d hd
  obtain ⟨hHd, hCd, _⟩ := charged_cool_constants (C + 6) d (by positivity) hd
  refine ⟨18 * (C + 6) / d ^ 2, 1 + d / 3, hHd, hCd, ?_⟩
  intro ui e b ε T S hb hε hT h γ hac hweak hwindows
  have hwhole := hbudget ui e b 0 T S hb hT h γ hac hweak (by
    simpa only [zero_add] using hwindows)
  constructor
  · intro a ha c hc
    have hsub : Icc a c ⊆ Icc 0 T := Icc_subset_Icc ha.1 hc.2
    have hBn : 0 ≤ cylinderEnergy S b (γ.U a) (γ.V a) / b +
        (curveCovVar e S S.a γ.U γ.V a c).toReal ^ 2 :=
      add_nonneg (normalized_energy_lower hb (h.mu _ (γ.mem a ha))).1 (sq_nonneg _)
    have hscale : C * (cylinderEnergy S b (γ.U a) (γ.V a) / b +
        (curveCovVar e S S.a γ.U γ.V a c).toReal ^ 2) ≤
        (C + 6) * (cylinderEnergy S b (γ.U a) (γ.V a) / b +
        (curveCovVar e S S.a γ.U γ.V a c).toReal ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) hBn
    rcases lt_or_eq_of_le hc.1 with hlt | rfl
    · have hacsub := curveParallel_ac_subinterval hT.le
        (connection_intervalIntegrable h hT.le γ) hac hlt.le hsub
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
  · intro hq₀ hclock
    let q := fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b
    let σ := (curveCovVar e S S.a γ.U γ.V 0 T).toReal
    have hb₁ : (∫ x in 0..T, q x ^ 2 / b) ≤ C * (ε + σ ^ 2) :=
      hwhole.2.2.2.2.trans (mul_le_mul_of_nonneg_left (add_le_add hq₀ le_rfl) hC.le)
    have hb₂ : (∫ x in 0..T, q x ^ 2 / b) ≤ (C + 6) * (ε + σ ^ 2) :=
      hb₁.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    have cq : ContinuousOn q (Icc 0 T) := by
      simpa only [uIcc_of_le hT.le] using
        (charged_cool_identity ui e b 0 T S h hb hT γ hac).1.continuousOn
    exact charged_cool_decrease_of_budgets (C + 6) d (by positivity) hd q b ε T σ
      hb hε ENNReal.toReal_nonneg hclock cq
      (fun x hx => (Cooling.normalized_energy_lower hb (h.mu _ (γ.mem x hx))).1) hb₂
      (charged_cool_cooling_time_propagation ui e b T S h hb hT γ hac)

end EmcsfAcExtension.Global
