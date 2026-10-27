module

public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Curves
public import EmcsfAcExtension.Global.Defs.Observation
import EmcsfAcExtension.Global.Closure.Profiles
import EmcsfAcExtension.Global.Closure.StageSums
import EmcsfAcExtension.Global.Cooling.Cylinder
import EmcsfAcExtension.Infra.AC.Variation

/-! # Small numerical envelopes and the energy-only unfinished cylinder

These estimates precede interaction closure and the observation-dependent
integrated budgets. Source: `charged_SF_new_version.tex:L4016–L4026`.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
The actual energy on an unfinished cylinder is bounded by its initial
energy and actual covariant variation, including a singleton cylinder.
The coefficients `2,1` are universal, independent of observation, coupling,
data, radius and duration. Source: charged_SF_new_version.tex:L3120–L3120, L4016–L4026. -/
theorem current_cylinder_energy (ui e b s t : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hb : 0 < b) (hst : s ≤ t)
    (γ : ClockCylinder S (origDomain ui) b s t)
    (hac : AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t) :
    cylinderEnergy S b (γ.U t) (γ.V t) / b ≤
      2 * (cylinderEnergy S b (γ.U s) (γ.V s) / b) +
        (curveCovVar e S S.a γ.U γ.V s t).toReal ^ 2 := by
  have hvar : curveCovVar e S S.a γ.U γ.V s t ≠ ⊤ :=
    hac.boundedVariationOn_Icc hst
  have hroot := Observation.square_root_energy_le ui e b s t S h hb hst γ hac
  have hr := ENNReal.toReal_mono (by finiteness) hroot
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_add ENNReal.ofReal_ne_top (by finiteness),
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt 2)] at hr
  exact current_energy_of_square_root
    (Cooling.normalized_energy_lower hb (h.mu _ (γ.mem t (right_mem_Icc.mpr hst)))).1
    (Cooling.normalized_energy_lower hb (h.mu _ (γ.mem s (left_mem_Icc.mpr hst)))).1
    ENNReal.toReal_nonneg hr

/-- [node sec:charged-closure#stopped-budget-smallness]
The recurrence envelopes are uniformly small under the variation stop.
`Csum` depends only on `χ,C₁,Cbudget`, before both tolerances, all data,
variations and cutoffs. The unfinished-cylinder conclusion is energy-only:
it needs no interaction or observation inequality. The stage initial
energy is the already propagated envelope. Source: charged_SF_new_version.tex:L4016–L4026. -/
theorem stopped_budget_smallness (χ C₁ Cbudget F : ℝ)
    (hχ : 0 ≤ χ ∧ χ < 1) (hC₁ : 0 ≤ C₁) (hCb : 0 ≤ Cbudget) (hF : 0 < F) :
    ∃ Csum > 0, ∃ εstop > 0, ∃ εentry > 0,
      (∀ (ε₀ J : ℝ) (σ : ℕ → ℝ) (N : ℕ),
        0 ≤ ε₀ → ε₀ ≤ εentry → 0 ≤ J → (∀ n, 0 ≤ σ n) →
        J + ∑ n ∈ Finset.range N, σ n ≤ εstop →
        ∀ n ∈ Finset.range N,
          Real.sqrt (stageBudget Cbudget χ C₁ ε₀ σ n) ≤
            Csum * (Real.sqrt ε₀ + εstop) ∧
          Csum * (Real.sqrt ε₀ + εstop) < F) ∧
      (∀ (ui e b s t ε₀ : ℝ) (S : Fields) (σ : ℕ → ℝ) (n : ℕ),
        OriginalData ui e S → 0 < b → s ≤ t →
        ∀ γ : ClockCylinder S (origDomain ui) b s t,
        AbsolutelyContinuousOnInterval (curveParallel e S S.a γ.U γ.V s) s t →
        cylinderEnergy S b (γ.U s) (γ.V s) / b ≤ energyEnvelope χ C₁ ε₀ σ n →
        cylinderEnergy S b (γ.U t) (γ.V t) / b ≤
          2 * energyEnvelope χ C₁ ε₀ σ n +
            (curveCovVar e S S.a γ.U γ.V s t).toReal ^ 2) := by
  obtain ⟨Csum, hCs, hsums⟩ := finite_stage_sums χ C₁ Cbudget hχ hC₁ hCb
  let a := F / (4 * Csum)
  have ha : 0 < a := div_pos hF (by positivity)
  refine ⟨Csum, hCs, a, ha, a ^ 2, sq_pos_of_pos ha, ?_, ?_⟩
  · intro ε₀ J σ N he heA hJ hσ hstop n hn
    have hroot : Real.sqrt ε₀ ≤ a := Real.sqrt_le_iff.mpr ⟨ha.le, heA⟩
    have hsum : ∑ i ∈ Finset.range N, σ i ≤ a := by linarith only [hstop, hJ]
    refine ⟨?_, ?_⟩
    · exact (Finset.single_le_sum (fun i _ => Real.sqrt_nonneg _) hn).trans
        ((hsums ε₀ σ N he hσ).2.trans
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) hCs.le))
    · calc
        Csum * (Real.sqrt ε₀ + a) ≤ Csum * (a + a) := by gcongr
        _ = F / 2 := by dsimp only [a]; field_simp; ring
        _ < F := by linarith only [hF]
  · intro ui e b s t ε₀ S σ n h hb hst γ hac hinit
    exact (current_cylinder_energy ui e b s t S h hb hst γ hac).trans
      (add_le_add (mul_le_mul_of_nonneg_left hinit (by norm_num)) le_rfl)

end EmcsfAcExtension.Global.Closure
