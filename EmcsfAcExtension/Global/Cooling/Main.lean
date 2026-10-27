/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Cooling.Decrease
public import EmcsfAcExtension.Global.Cooling.Full
import EmcsfAcExtension.Infra.AC.Variation

/-! # Conditional charged cooling

The observation statement of internal project record is the only pending upstream
result. The cylinder identity is discharged by `Cooling.cylinder_input`.
The original two-input helper is retained with its public signature.
No frozen theorem anchor or provider is imported.
-/

public section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Global.Cooling

private theorem ofReal_budget {C q : ℝ} {σ : ℝ≥0∞}
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hσ : σ ≠ ∞) :
    ENNReal.ofReal (C * (q + σ.toReal ^ 2)) =
      ENNReal.ofReal (C * q) + ENNReal.ofReal C * σ ^ 2 := by
  rw [mul_add, ENNReal.ofReal_add (mul_nonneg hC hq) (by positivity),
    ENNReal.ofReal_mul hC, ENNReal.ofReal_mul hC,
    ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hσ]

end EmcsfAcExtension.Global.Cooling

namespace EmcsfAcExtension.Global

/-- [internal] Compatibility helper in the exact internal project record template,
with explicit observation and cylinder inputs. The observation-only wrapper
below discharges the cylinder premise using the landed energy calculus.
`Cbudget` depends only on the observation constants. `Hd,Cd` depend only
on those constants and `d`, before all duration, energy, scalar-background,
coupling, and physical-radius data. The integral estimate is quantified
over all subintervals before the endpoint cooling conclusion. -/
theorem charged_cool_of_observation_of_cylinder (δ : ℝ) (_hδ : 0 < δ ∧ δ < 1)
    (hobs : Cooling.observationInput δ) (hcylinder : Cooling.cylinderInput) :
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
    (∀ s ∈ Icc 0 T, ∀ t ∈ Icc s T,
      ENNReal.ofReal (∫ τ in s..t,
        (‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2 +
         ‖S.xi (γ.U τ) (γ.V τ) / (S.nu (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2 +
         S.mu (γ.U τ) (γ.V τ) ^ 2 +
         (cylinderEnergy S b (γ.U τ) (γ.V τ) / b) ^ 2) / b) ≤
        ENNReal.ofReal (Cbudget * cylinderEnergy S b (γ.U s) (γ.V s) / b) +
        ENNReal.ofReal Cbudget * (curveCovVar e S S.a γ.U γ.V s t) ^ 2) ∧
    (cylinderEnergy S b (γ.U 0) (γ.V 0) / b ≤ ε → T = Hd * b / ε →
      ENNReal.ofReal (cylinderEnergy S b (γ.U T) (γ.V T) / b) ≤
        ENNReal.ofReal (d * ε) + ENNReal.ofReal Cd *
          (curveCovVar e S S.a γ.U γ.V 0 T) ^ 2) := by
  obtain ⟨Ts, Cs, δs, ηs, hTs, hCs, hδs, hηs, hobs⟩ := hobs
  obtain ⟨Cb, hCb, hfield⟩ := charged_cool_integrated_of_observation_of_cylinder Ts Cs hTs hCs
  let δw := min δs (1 / 2)
  have hδw : 0 < δw := lt_min hδs (by norm_num)
  have hδhalf : δw ≤ 1 / 2 := min_le_right _ _
  refine ⟨Ts, δw, ηs, Cb, hTs, hδw, hηs, hCb, ?_⟩
  intro d hd
  obtain ⟨hHd, hCd, _⟩ := charged_cool_constants Cb d hCb hd
  refine ⟨18 * Cb / d ^ 2, 1 + d / 3, hHd, hCd, ?_⟩
  intro ui e b ε T S hb hε hT h γ hac hweak hwindows
  have hA := Cooling.connection_intervalIntegrable h hT.le γ
  let q := fun x => cylinderEnergy S b (γ.U x) (γ.V x) / b
  have hqn (x : ℝ) (hx : x ∈ Icc 0 T) : 0 ≤ q x :=
    (Cooling.normalized_energy_lower hb (h.mu _ (γ.mem x hx))).1
  have hacsub (a c : ℝ) (hac' : a ≤ c) (hsub : Icc a c ⊆ Icc 0 T) :=
    Cooling.curveParallel_ac_subinterval hT.le hA hac hac' hsub
  have hnorm (a c : ℝ) (hac' : a < c) (hsub : Icc a c ⊆ Icc 0 T) := by
    have hi := hcylinder ui e b a c S h hb hac'
      (Cooling.restrictCylinder γ hsub) (hacsub a c hac'.le hsub)
    simpa only [Cooling.restrictCylinder] using
      charged_cool_identity_of_cylinder hb hac'.le hi.1 hi.2
  have hlocalobs (a c : ℝ) (ha : 0 ≤ a) (hc : c ≤ T)
      (x : ℝ) (hx : x ∈ Icc (a + Ts * b) (c - Ts * b)) :
      ENNReal.ofReal (b * (‖S.theta (γ.U x) (γ.V x) /
        (S.lam (γ.U x) (γ.V x) : ℂ)‖ ^ 2 + S.mu (γ.U x) (γ.V x) ^ 2)) ≤
        ENNReal.ofReal Cs *
          (ENNReal.ofReal (cylinderDissipation S γ.U γ.V (x - Ts * b) (x + Ts * b)) +
            ENNReal.ofReal b * (curveCovVar e S S.a γ.U γ.V (x - Ts * b) (x + Ts * b)) ^ 2) := by
    have hxfull : x ∈ Icc (Ts * b) (T - Ts * b) := by
      constructor <;> linarith only [hx.1, hx.2, ha, hc]
    have hsub : Icc (x - Ts * b) (x + Ts * b) ⊆ Icc 0 T := by
      intro y hy
      constructor <;> linarith only [hxfull.1, hxfull.2, hy.1, hy.2]
    have hwin : x - Ts * b < x + Ts * b := by nlinarith [mul_pos hTs hb]
    simpa only [Cooling.restrictCylinder] using
      hobs ui e b x S hb h (Cooling.restrictCylinder γ hsub)
        (hwindows x hxfull).1 (hwindows x hxfull).2.1
        (hacsub _ _ hwin.le hsub)
        (fun y hy => (hweak y (hsub hy)).trans (min_le_left _ _))
        (hwindows x hxfull).2.2
  have hbudgets (a c : ℝ) (ha : a ∈ Icc 0 T) (hc : c ∈ Icc a T) (hlt : a < c) := by
    have hsub : Icc a c ⊆ Icc 0 T := Icc_subset_Icc ha.1 hc.2
    simpa only [Cooling.restrictCylinder] using
      hfield ui e b δw a c S h hb hlt hδhalf (Cooling.restrictCylinder γ hsub)
        (hacsub a c hlt.le hsub) (fun x hx => hweak x (hsub hx))
        (hnorm a c hlt hsub) (hlocalobs a c ha.1 hc.2)
  have hvarfin : curveCovVar e S S.a γ.U γ.V 0 T ≠ ∞ := hac.boundedVariationOn_Icc hT.le
  constructor
  · intro a ha c hc
    rcases lt_or_eq_of_le hc.1 with hlt | rfl
    · have hsub : Icc a c ⊆ Icc 0 T := Icc_subset_Icc ha.1 hc.2
      have hvarfin' : curveCovVar e S S.a γ.U γ.V a c ≠ ∞ :=
        (hacsub a c hlt.le hsub).boundedVariationOn_Icc hlt.le
      have hi := (hbudgets a c ha hc hlt).2.1 a (left_mem_Icc.mpr hlt.le)
      have hm : S.m (γ.U a) (γ.V a) / b = S.mu (γ.U a) (γ.V a) / 2 := by
        rw [Fields.mu, γ.radius a ha]
        ring
      have hn : 0 ≤ S.m (γ.U a) (γ.V a) / b +
          ‖S.theta (γ.U a) (γ.V a) / (S.lam (γ.U a) (γ.V a) : ℂ)‖ ^ 2 := by
        rw [hm]
        have hμ := (h.mu _ (γ.mem a ha)).1
        positivity
      have hI := le_trans (le_add_of_nonneg_left hn) hi
      calc
        _ ≤ ENNReal.ofReal (Cb * (q a + (curveCovVar e S S.a γ.U γ.V a c).toReal ^ 2)) :=
          ENNReal.ofReal_le_ofReal hI
        _ = _ := by
          rw [Cooling.ofReal_budget hCb.le (hqn a ha) hvarfin']
          congr 2
          dsimp only [q]
          ring
    · simp only [intervalIntegral.integral_same, ENNReal.ofReal_zero]
      positivity
  · intro hq₀ hclock
    have hnwhole := hnorm 0 T hT Subset.rfl
    have hwhole := hbudgets 0 T (left_mem_Icc.mpr hT.le) (right_mem_Icc.mpr hT.le) hT
    let σ := (curveCovVar e S S.a γ.U γ.V 0 T).toReal
    have hbudget : (∫ x in 0..T, q x ^ 2 / b) ≤ Cb * (ε + σ ^ 2) :=
      hwhole.2.2.trans (mul_le_mul_of_nonneg_left (add_le_add hq₀ le_rfl) hCb.le)
    have hprop (x : ℝ) (hx : x ∈ Icc (T / 2) T) : q T ≤ 2 * q x + σ ^ 2 := by
      have hxm : x ∈ Icc 0 T := ⟨by linarith only [hx.1, hT], hx.2⟩
      rcases lt_or_eq_of_le hx.2 with hlt | heq
      · have hsub : Icc x T ⊆ Icc 0 T := Icc_subset_Icc hxm.1 le_rfl
        have hvarfin' : curveCovVar e S S.a γ.U γ.V x T ≠ ∞ :=
          (hacsub x T hlt.le hsub).boundedVariationOn_Icc hlt.le
        have hvarle : curveCovVar e S S.a γ.U γ.V x T ≤ curveCovVar e S S.a γ.U γ.V 0 T := by
          rw [Cooling.curveCovVar_eq_restricted_variation hT.le hA hsub hlt.le]
          exact eVariationOn.mono _ hsub
        have hr := Observation.square_root_energy_of_cylinder ui e b x T S h hb hlt
          (Cooling.restrictCylinder γ hsub) (hacsub x T hlt.le hsub) (hnorm x T hlt hsub)
        dsimp only [Cooling.restrictCylinder] at hr
        rw [← ENNReal.ofReal_toReal hvarfin',
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / Real.sqrt 2),
          ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (by positivity)] at hr
        have hr' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hr
        have hσle := ENNReal.toReal_mono hvarfin hvarle
        have hroot : Real.sqrt (q T) ≤ Real.sqrt (q x) + σ / Real.sqrt 2 := by
          have hm := mul_le_mul_of_nonneg_left hσle (by positivity : 0 ≤ 1 / Real.sqrt 2)
          simpa only [q, σ, div_eq_mul_inv, one_mul, mul_comm] using
            hr'.trans (add_le_add le_rfl hm)
        exact Cooling.cooling_time_propagation_of_square_root (hqn x hxm)
          (hqn T (right_mem_Icc.mpr hT.le))
          ENNReal.toReal_nonneg hroot
      · rw [heq]
        nlinarith only [hqn T (right_mem_Icc.mpr hT.le), sq_nonneg σ]
    have cq : ContinuousOn q (Icc 0 T) := by
      simpa only [uIcc_of_le hT.le] using hnwhole.1.continuousOn
    have hcool := charged_cool_decrease_of_budgets Cb d hCb hd q b ε T σ hb hε
      ENNReal.toReal_nonneg hclock cq hqn hbudget hprop
    calc
      _ ≤ ENNReal.ofReal (d * ε + (1 + d / 3) * σ ^ 2) := ENNReal.ofReal_le_ofReal hcool
      _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity : 0 ≤ 1 + d / 3),
          ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hvarfin]

/-- [internal] Charged cooling in internal project record, with the observation
proposition as its only remaining upstream premise. All cylinder identities
are proved from the frozen original data. Constants have the same scope
as the source: `Cbudget` depends only on observation constants, and `Hd,Cd`
only on these constants and `d`, before every physical datum. -/
theorem charged_cool_of_observation (δ : ℝ) (_hδ : 0 < δ ∧ δ < 1)
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
    (∀ s ∈ Icc 0 T, ∀ t ∈ Icc s T,
      ENNReal.ofReal (∫ τ in s..t,
        (‖S.theta (γ.U τ) (γ.V τ) / (S.lam (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2 +
         ‖S.xi (γ.U τ) (γ.V τ) / (S.nu (γ.U τ) (γ.V τ) : ℂ)‖ ^ 2 +
         S.mu (γ.U τ) (γ.V τ) ^ 2 +
         (cylinderEnergy S b (γ.U τ) (γ.V τ) / b) ^ 2) / b) ≤
        ENNReal.ofReal (Cbudget * cylinderEnergy S b (γ.U s) (γ.V s) / b) +
        ENNReal.ofReal Cbudget * (curveCovVar e S S.a γ.U γ.V s t) ^ 2) ∧
    (cylinderEnergy S b (γ.U 0) (γ.V 0) / b ≤ ε → T = Hd * b / ε →
      ENNReal.ofReal (cylinderEnergy S b (γ.U T) (γ.V T) / b) ≤
        ENNReal.ofReal (d * ε) + ENNReal.ofReal Cd *
          (curveCovVar e S S.a γ.U γ.V 0 T) ^ 2) :=
  charged_cool_of_observation_of_cylinder δ _hδ hobs Cooling.cylinder_input

/-- [internal] The cooling decrease with observation as the sole
upstream premise (L2559–L2572). The duration and variation constants are
chosen before every physical datum, with exactly the source dependence
on `d` and observation constants. No comparison of variation and energy
and no additive electric error is assumed. -/
theorem charged_cool_decrease_of_observation (δ : ℝ) (_hδ : 0 < δ ∧ δ < 1)
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
    (cylinderEnergy S b (γ.U 0) (γ.V 0) / b ≤ ε → T = Hd * b / ε →
      ENNReal.ofReal (cylinderEnergy S b (γ.U T) (γ.V T) / b) ≤
        ENNReal.ofReal (d * ε) + ENNReal.ofReal Cd *
          (curveCovVar e S S.a γ.U γ.V 0 T) ^ 2) := by
  obtain ⟨Ts, δs, ηs, Cb, hTs, hδs, hηs, hCb, hcool⟩ :=
    charged_cool_of_observation δ _hδ hobs
  refine ⟨Ts, δs, ηs, Cb, hTs, hδs, hηs, hCb, ?_⟩
  intro d hd
  obtain ⟨Hd, Cd, hHd, hCd, hcool⟩ := hcool d hd
  refine ⟨Hd, Cd, hHd, hCd, ?_⟩
  intro ui e b ε T S hb hε hT h γ hac hweak hwindows
  exact (hcool ui e b ε T S hb hε hT h γ hac hweak hwindows).2

end EmcsfAcExtension.Global
