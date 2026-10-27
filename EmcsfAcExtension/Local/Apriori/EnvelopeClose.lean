module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseIntegral
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseInitial
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseSource
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseNorms
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseAxis
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # The two coupled real envelope inequalities

The constants are chosen before the data and retain all charged-scale
factors. These are `charged_SF_new_version.tex:L4734–L4743`, with the fixed numerical
smallness margin used by the landed characteristic variation absorption.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

private theorem toReal_le_amplified_sum {J x y z : ℝ≥0∞} {H : ℝ}
    (hH : 0 ≤ H) (hx : x ≠ ⊤) (hy : y ≠ ⊤) (hz : z ≠ ⊤)
    (h : J ≤ ENNReal.ofReal H * (x + y + z)) :
    J.toReal ≤ H * (x.toReal + y.toReal + z.toReal) := by
  have hfin : ENNReal.ofReal H * (x + y + z) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hx, hy⟩, hz⟩)
  have hi := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hH] at hi
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ hH
  exact ENNReal.toReal_add_le.trans (add_le_add ENNReal.toReal_add_le le_rfl)

/-- [node restart-bv-J-close]
The outgoing coupled envelope inequality (`charged_SF_new_version.tex:L4734–L4739`).
`C` is universal within the fixed box, independent of all data and higher
derivatives. The fixed margin `ε ≤ 1/8` is sufficient; no charged-scale
smallness is needed for this conditional transport inequality. -/
theorem bv_J_close : ∃ C : ℝ, 0 < C ∧
    ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h → ε ≤ 1 / 8 →
    let J := (∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 s) S) v).toReal
    let K := (∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 s) S) u).toReal
    J ≤ Real.exp (C * ε * K) *
      (ε + C * ε ^ 3 + C * ε * K * J + C * (|e| * (s / 2) * M) ^ 2 * ε) := by
  obtain ⟨A, hA, ha⟩ := outgoing_envelope_bound_with_forcing
  obtain ⟨B, hB, hb⟩ := initial_j_budget
  obtain ⟨D, hD, hd⟩ := characteristic_forcing_area_budgets
  let C := A + B + D
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro e s ε M S h hset hε
  let J := ∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 s) S) v
  let K := ∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 s) S) u
  let δ := |e| * (s / 2) * M
  have hJ : J ≠ ⊤ := outEnv_lintegral_ne_top_of_continuousOn
    (continuousOn_jC1_aux hset.pos hset.c1)
  have hK : K ≠ ⊤ := inEnv_lintegral_ne_top_of_continuousOn
    (continuousOn_kC1_aux hset.pos hset.c1)
  have hε0 := hset.eps_nonneg
  have hbase : 0 ≤ ε + B * ε ^ 3 := by positivity
  have hDε : 0 ≤ D * ε := mul_nonneg hD.le hε0
  have helec : 0 ≤ D * δ ^ 2 * ε := by positivity
  dsimp only [δ] at helec
  have hi := (ha e s ε M S h hset hε).trans
    (mul_le_mul' le_rfl (add_le_add (hb e s ε M S h hset)
      (hd e s ε M S h hset hε).1))
  rw [← incoming_envelope_integral_toReal hset.pos hset.c1] at hi
  rw [← add_assoc] at hi
  have hr := toReal_le_amplified_sum (Real.exp_pos _).le ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK) hJ)
    ENNReal.ofReal_ne_top hi
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hbase,
    ENNReal.toReal_ofReal hDε, ENNReal.toReal_ofReal helec] at hr
  have hAC : A ≤ C := by dsimp only [C]; linarith only [hB, hD]
  have hBC : B ≤ C := by dsimp only [C]; linarith only [hA, hD]
  have hDC : D ≤ C := by dsimp only [C]; linarith only [hA, hB]
  apply hr.trans
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hε0)
      ENNReal.toReal_nonneg
  · gcongr
  · positivity
  · exact (Real.exp_pos _).le

/-- [node restart-bv-K-close]
The incoming coupled envelope inequality with exactly the axis scalar
variation as boundary datum (`charged_SF_new_version.tex:L4740–L4743`). `C` is universal
within the fixed box, independent of all data and higher derivatives.
The margin `ε ≤ 1/8` is sufficient for the variation absorption. -/
theorem bv_K_close : ∃ C : ℝ, 0 < C ∧
    ∀ (e s ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e s ε M S h → ε ≤ 1 / 8 →
    let J := (∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 s) S) v).toReal
    let K := (∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 s) S) u).toReal
    K ≤ (eVariationOn (fun t => S.phi t t) (Icc 0 s)).toReal +
      C * ε * J * K + C * (|e| * (s / 2) * M) ^ 2 * ε := by
  obtain ⟨C, hC, hc⟩ := characteristic_forcing_area_budgets
  refine ⟨C, hC, ?_⟩
  intro e s ε M S h hset hε
  let J := ∫⁻ v in Icc 0 s, outEnv 0 (jC1 (triangle 0 s) S) v
  let K := ∫⁻ u in Icc 0 s, inEnv s (kC1 e (triangle 0 s) S) u
  let δ := |e| * (s / 2) * M
  have hJ : J ≠ ⊤ := outEnv_lintegral_ne_top_of_continuousOn
    (continuousOn_jC1_aux hset.pos hset.c1)
  have hK : K ≠ ⊤ := inEnv_lintegral_ne_top_of_continuousOn
    (continuousOn_kC1_aux hset.pos hset.c1)
  have haxis : eVariationOn (fun t => S.phi t t) (Icc 0 s) ≠ ⊤ :=
    ne_top_of_le_ne_top hJ (smooth_axis_variation_budget hset.pos hset.c1 hset.data.2)
  have hε0 := hset.eps_nonneg
  have hCε : 0 ≤ C * ε := mul_nonneg hC.le hε0
  have he : 0 ≤ C * δ ^ 2 * ε := by positivity
  have hi := (incoming_envelope_bound_with_forcing hset).trans
    (add_le_add le_rfl (hc e s ε M S h hset hε).2)
  rw [← add_assoc] at hi
  have hi' : K ≤ ENNReal.ofReal 1 *
      (eVariationOn (fun t => S.phi t t) (Icc 0 s) +
        ENNReal.ofReal (C * ε) * J * K + ENNReal.ofReal (C * δ ^ 2 * ε)) := by
    simpa only [ENNReal.ofReal_one, one_mul] using hi
  have hr := toReal_le_amplified_sum (by norm_num : (0 : ℝ) ≤ 1) haxis
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ) hK)
    ENNReal.ofReal_ne_top hi'
  simpa only [one_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hCε,
    ENNReal.toReal_ofReal he] using hr

end EmcsfAcExtension.Local
