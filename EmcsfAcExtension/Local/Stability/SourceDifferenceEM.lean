module

public import EmcsfAcExtension.Local.Stability.MainRecords
public import EmcsfAcExtension.Local.Stability.SourceDifferenceCharge
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMFactors
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMSourceJ
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMSourceK

/-! # Complete electromagnetic transport source difference

Both literal charged curvature primitives and all explicit electromagnetic
monomials enter the estimate. The area contributes the full length square.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- The complete literal electromagnetic part of the outgoing j transport. -/
@[expose] noncomputable def emTransportSourceJ (e : ℝ) (S : Fields) (u v : ℝ) : ℂ :=
  (S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2 *
    (curvEM e S u v + 2 * starRingEnd ℂ (curvEM e S u v)) + emSourceJ e S u v

/-- The complete literal electromagnetic part of the incoming k transport. -/
@[expose] noncomputable def emTransportSourceK (e : ℝ) (S : Fields) (u v : ℝ) : ℂ :=
  (S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
    (curvEMIn e S u v + 2 * starRingEnd ℂ (curvEMIn e S u v)) + emSourceK e S u v

/-- A uniform nonnegative bound gives an incoming area bound `T² E`.
The coefficient one is universal; no measurability of the bounded integrand
is needed for this upper estimate of the lower Lebesgue integral. -/
theorem incoming_area_le_of_uniform_bound {T E : ℝ} {F : ℝ × ℝ → ℝ≥0∞}
    (hT : 0 ≤ T) (_hE : 0 ≤ E) (hF : ∀ p ∈ triangle 0 T, F p ≤ ENNReal.ofReal E) :
    (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, F (u, v)) ≤ ENNReal.ofReal (T ^ 2 * E) := by
  calc
    _ ≤ ∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 T, ENNReal.ofReal E := by
      apply setLIntegral_mono' measurableSet_Icc
      intro v hv
      apply (setLIntegral_mono' measurableSet_Icc (fun u hu => hF (u, v) ⟨hu.1, hu.2, hv.2⟩)).trans
      exact lintegral_mono_set (Icc_subset_Icc le_rfl hv.2)
    _ = _ := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
      rw [ENNReal.ofReal_mul (sq_nonneg T), ENNReal.ofReal_pow hT]
      ring

/-- [internal]
 The complete electromagnetic source difference with its sharper data
remainder. `C` depends only on the fixed first-half constant `D`, uniformly
in all solutions, physical scales, data and derivative suprema. -/
theorem electromagnetic_source_difference_sharp_of_differences (D : ℝ) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (T e ε M A : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ≤ 1 → sigma e M T ≤ 1 →
      RatioDifferences D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      FieldDifference D T ε (dataDist h₁ h₂ T) S₁ S₂ →
      ChargeDifference D e T ε M (dataDist h₁ h₂ T) S₁ S₂ →
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖emTransportSourceJ e S₁ u v - emTransportSourceJ e S₂ u v‖ₑ +
          ‖emTransportSourceK e S₁ u v - emTransportSourceK e S₂ u v‖ₑ) ≤
        ENNReal.ofReal (C * sigma e M T * ((jDist T S₁ S₂).toReal +
          (kDist e T S₁ S₂).toReal + ε * (geomDist T S₁ S₂).toReal +
          ε * dataDist h₁ h₂ T / M)) := by
  obtain ⟨Cj, hCj, hj⟩ := em_curvature_source_j_difference_of_differences D hD
  obtain ⟨Ck, hCk, hk⟩ := em_curvature_source_k_difference_of_differences D hD
  obtain ⟨Ce, hCe, he⟩ := explicit_em_source_difference_of_differences D hD
  refine ⟨4 * (Cj + Ck + Ce), by positivity, ?_⟩
  intro T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁ hratio hfield hcharge
  let X := (jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal +
    ε * (geomDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T / M
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.2.1
  have hM : 0 ≤ M := zero_le_one.trans hs₂.box.1
  have hδ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hpoint (u v : ℝ) (hp : (u, v) ∈ triangle 0 T) :
      ‖emTransportSourceJ e S₁ u v - emTransportSourceJ e S₂ u v‖ +
        ‖emTransportSourceK e S₁ u v - emTransportSourceK e S₂ u v‖ ≤
          (Cj + Ck + Ce) * e ^ 2 * M ^ 2 * X := by
    rcases hp.2.1.eq_or_lt with heq | hlt
    · change u = v at heq
      subst v
      have hr₁ := (hs₁.c1.axis u hp).1
      have hr₂ := (hs₂.c1.axis u hp).1
      simp only [emTransportSourceJ, emTransportSourceK, emSourceJ, emSourceK, hr₁, hr₂]
      norm_num
      positivity
    have hJbound := hj T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁ hratio hfield hcharge u v hp.1 hlt
        hp.2.2
    have hKbound := hk T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁ hratio hfield hcharge u v hp.1 hlt
        hp.2.2
    have hEbound := he T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁ hratio hfield hcharge (u, v) hp hlt
    have htriangle (a b c d : ℂ) : ‖(a + b) - (c + d)‖ ≤ ‖a - c‖ + ‖b - d‖ := by
      rw [show (a + b) - (c + d) = (a - c) + (b - d) by ring]
      exact norm_add_le _ _
    dsimp only [emTransportSourceJ, emTransportSourceK]
    apply (add_le_add (htriangle _ _ _ _) (htriangle _ _ _ _)).trans
    dsimp only [X] at *
    nlinarith only [hJbound, hKbound, hEbound]
  have harea := incoming_area_le_of_uniform_bound hs₂.pos.le
    (by positivity : 0 ≤ (Cj + Ck + Ce) * e ^ 2 * M ^ 2 * X)
    (F := fun p => ‖emTransportSourceJ e S₁ p.1 p.2 - emTransportSourceJ e S₂ p.1 p.2‖ₑ +
      ‖emTransportSourceK e S₁ p.1 p.2 - emTransportSourceK e S₂ p.1 p.2‖ₑ)
    (fun p hp => by
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hpoint p.1 p.2 hp))
  apply harea.trans_eq
  congr 1
  dsimp only [sigma, X]
  ring

end EmcsfAcExtension.Local.Stab
