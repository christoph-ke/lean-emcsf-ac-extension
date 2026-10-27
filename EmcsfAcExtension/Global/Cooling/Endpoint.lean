/- Copyright (c) 2026. All rights reserved. -/
module

public import EmcsfAcExtension.Global.Cooling.SquareRoot

/-! # Weak-regime comparisons and the uncaptured endpoint strips

These estimates are pointwise or depend only on the length of the two
endpoint strips (`charged_SF_new_version.tex:L2948–L2983`). They do not assume the
existence of a completed observation window.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Cooling

/-- [internal]
On the fixed weak regime, normalized energy is comparable to outgoing
scalar energy plus mass ratio. The displayed constants are universal for
all weak thresholds at most `1/2`, independently of radius and background. -/
theorem weak_regime_energy_comparison (S : Fields) (b u v δ : ℝ)
    (hb : 0 < b) (hr : S.r u v = b) (hmu : 0 ≤ S.mu u v)
    (hδ : δ ≤ 1 / 2) (hweak : S.mu u v + ‖S.theta u v / (S.lam u v : ℂ)‖ ≤ δ) :
    (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 + S.mu u v) / 2 ≤
        cylinderEnergy S b u v / b ∧
      cylinderEnergy S b u v / b ≤
        ‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 + S.mu u v ∧
      (cylinderEnergy S b u v / b) ^ 2 ≤
        2 * (‖S.theta u v / (S.lam u v : ℂ)‖ ^ 2 + S.mu u v ^ 2) ∧
      S.m u v / b = S.mu u v / 2 ∧
      S.m u v / b ≤ cylinderEnergy S b u v / b := by
  let y := ‖S.theta u v / (S.lam u v : ℂ)‖
  let μ := S.mu u v
  let q := cylinderEnergy S b u v / b
  have hyn : 0 ≤ y := norm_nonneg _
  have hy : y ≤ 1 / 2 := by dsimp only [y]; linarith
  have hμ : μ ≤ 1 / 2 := by dsimp only [μ]; linarith [norm_nonneg (S.theta u v / (S.lam u v : ℂ))]
  have hg : 0 < 1 - μ := by linarith
  have hlogup := Real.log_le_sub_one_of_pos hg
  have hloglo := Real.one_sub_inv_le_log_of_pos hg
  have hinv : (1 - μ)⁻¹ ≤ 1 + 2 * μ := by
    rw [← one_div]
    apply (div_le_iff₀ hg).2
    dsimp only [μ] at *
    nlinarith only [hmu, hμ]
  have heq : q = (y ^ 2 - Real.log (1 - μ)) / 2 := by
    dsimp only [q, y, μ]
    rw [cylinderEnergy_def]
    field_simp
  have hlo : (y ^ 2 + μ) / 2 ≤ q := by linarith
  have hqn : 0 ≤ q := by dsimp only [μ] at *; nlinarith only [hlo, hmu, sq_nonneg y]
  have hup : q ≤ y ^ 2 + μ := by nlinarith only [heq, hloglo, hinv, sq_nonneg y]
  have hysq : y ^ 2 ≤ 1 := by nlinarith only [hyn, hy]
  have hq2 : q ^ 2 ≤ 2 * (y ^ 2 + μ ^ 2) := by
    have hp := sq_le_sq₀ hqn (by dsimp only [μ]; positivity : 0 ≤ y ^ 2 + μ) |>.2 hup
    nlinarith only [hp, sq_nonneg (y ^ 2 - μ), mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hysq)]
  have hm : S.m u v / b = μ / 2 := by
    dsimp only [μ]
    rw [Fields.mu, hr]
    ring
  exact ⟨hlo, hup, hq2, hm, by rw [hm]; nlinarith only [hlo, sq_nonneg y]⟩

/-- [internal] The part of a clock interval missed by full-window centers
has length at most `2*h`, even if the full-window center set is empty. -/
theorem volume_endpoint_strips_le (s t h : ℝ) (hh : 0 ≤ h) :
    volume (Icc s t \ Icc (s + h) (t - h)) ≤ ENNReal.ofReal (2 * h) := by
  have hsub : Icc s t \ Icc (s + h) (t - h) ⊆
      Icc s (s + h) ∪ Icc (t - h) t := by
    intro x hx
    by_cases hleft : x ≤ s + h
    · exact Or.inl ⟨hx.1.1, hleft⟩
    · exact Or.inr ⟨by
        by_contra hright
        exact hx.2 ⟨(lt_of_not_ge hleft).le, (lt_of_not_ge hright).le⟩, hx.1.2⟩
  calc
    _ ≤ volume (Icc s (s + h) ∪ Icc (t - h) t) := measure_mono hsub
    _ ≤ volume (Icc s (s + h)) + volume (Icc (t - h) t) := measure_union_le _ _
    _ = ENNReal.ofReal (2 * h) := by
      rw [Real.volume_Icc, Real.volume_Icc]
      have h₁ : s + h - s = h := by ring
      have h₂ : t - (t - h) = h := by ring
      rw [h₁, h₂, ← ENNReal.ofReal_add hh hh]
      congr 1
      ring

/-- [internal] Endpoint-strip integration with its explicit length factor.
The bound is uniform in the containing interval, including short intervals. -/
theorem endpoint_interval_budget_of_bound {f : ℝ → ℝ} {s t h M : ℝ} (hh : 0 ≤ h) (hM : 0 ≤ M)
    (hf : IntegrableOn f (Icc s t))
    (hbound : ∀ x ∈ Icc s t, f x ≤ M) :
    (∫ x in Icc s t \ Icc (s + h) (t - h), f x) ≤ 2 * h * M := by
  let E := Icc s t \ Icc (s + h) (t - h)
  have hsub : E ⊆ Icc s t := sdiff_subset
  have hfin : volume E ≠ ∞ := ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono hsub)
  have : IsFiniteMeasure (volume.restrict E) := ⟨by simpa using hfin.lt_top⟩
  have hi : (∫ x in E, f x) ≤ ∫ _x in E, M :=
    integral_mono_ae (hf.mono_set hsub) (integrable_const M)
      ((ae_restrict_mem (measurableSet_Icc.diff measurableSet_Icc)).mono
        (fun x hx => hbound x (hsub hx)))
  rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ] at hi
  have hvol := ENNReal.toReal_mono ENNReal.ofReal_ne_top (volume_endpoint_strips_le s t h hh)
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * h)] at hvol
  exact hi.trans (mul_le_mul_of_nonneg_right hvol hM)

end EmcsfAcExtension.Global.Cooling
