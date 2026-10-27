module

public import EmcsfAcExtension.Local.Stability.MainRecords
import EmcsfAcExtension.Local.Stability.MainLipschitzRecords
import EmcsfAcExtension.Local.Stability.SourceDifferenceEM
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMFactors
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMSourceJ
import EmcsfAcExtension.Local.Stability.SourceDifferenceEMSourceK

/-! # Four separate electromagnetic source differences

The explicit sources and charged curvature sources are each differenced
before taking their norms, as in internal project record L1137–L1140 and
`charged_SF_new_version.tex:L5345`–L5346. The first-half comparison records are produced
inside the proof. Integration supplies the full length square.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local.Stab

/-- [node restart-sec-bv-stability-independent#electromagnetic-source-difference]
The sum of the four separate source difference norms on the §4.4 small-data
scope. Threshold `η` and constant `C` depend only on `A` and the fixed box,
before all physical parameters, data and solution pairs, uniformly in
derivative suprema and the minimum radius. -/
theorem electromagnetic_source_components_difference (A : ℝ) (hA : 0 < A) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
    ∀ (T e ε M : ℝ) (S₁ S₂ : Fields) (h₁ h₂ : ℝ → ℂ),
      StabSetting e T ε M A S₁ h₁ → StabSetting e T ε M A S₂ h₂ →
      ε ^ 2 + sigma e M T ≤ η →
      (∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v,
        ‖(S₁.nu u v : ℂ) * S₁.theta u v / (S₁.r u v : ℂ) ^ 2 *
            (curvEM e S₁ u v + 2 * starRingEnd ℂ (curvEM e S₁ u v)) -
          (S₂.nu u v : ℂ) * S₂.theta u v / (S₂.r u v : ℂ) ^ 2 *
            (curvEM e S₂ u v + 2 * starRingEnd ℂ (curvEM e S₂ u v))‖ₑ +
        ‖emSourceJ e S₁ u v - emSourceJ e S₂ u v‖ₑ +
        ‖(S₁.lam u v : ℂ) * S₁.xi u v / (S₁.r u v : ℂ) ^ 2 *
            (curvEMIn e S₁ u v + 2 * starRingEnd ℂ (curvEMIn e S₁ u v)) -
          (S₂.lam u v : ℂ) * S₂.xi u v / (S₂.r u v : ℂ) ^ 2 *
            (curvEMIn e S₂ u v + 2 * starRingEnd ℂ (curvEMIn e S₂ u v))‖ₑ +
        ‖emSourceK e S₁ u v - emSourceK e S₂ u v‖ₑ) ≤
        ENNReal.ofReal (C * sigma e M T * (dataDist h₁ h₂ T +
          (jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal +
          ε * (geomDist T S₁ S₂).toReal)) := by
  obtain ⟨ηr, D, hηr, hD, hrecords⟩ := difference_records A hA
  obtain ⟨Cj, hCj, hj⟩ := em_curvature_source_j_difference_of_differences D hD
  obtain ⟨Ck, hCk, hk⟩ := em_curvature_source_k_difference_of_differences D hD
  obtain ⟨Ce, hCe, he⟩ := explicit_em_source_difference_of_differences D hD
  refine ⟨min ηr (1 / 4), 4 * (Cj + Ck + Ce),
    lt_min hηr (by norm_num), by positivity, ?_⟩
  intro T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂ hsmall
  rcases hrecords T e ε M S₁ S₂ h₁ h₂ hs₁ hs₂
    (hsmall.trans (min_le_left _ _)) with ⟨hratio, hfield, hcharge, _⟩
  have hsmall₁ := hsmall.trans (min_le_right _ _)
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hε : 0 ≤ ε := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (hs₂.box.2 (0, 0) ⟨le_rfl, le_rfl, hs₂.pos.le⟩).2.2.2.2.2.1
  have hε₁ : ε ≤ 1 := by nlinarith only [hsmall₁, hσ]
  have hσ₁ : sigma e M T ≤ 1 := by nlinarith only [hsmall₁, sq_nonneg ε]
  have hM : 0 < M := zero_lt_one.trans_le hs₂.box.1
  have hδ : 0 ≤ dataDist h₁ h₂ T := add_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  let X := (jDist T S₁ S₂).toReal + (kDist e T S₁ S₂).toReal +
    ε * (geomDist T S₁ S₂).toReal + ε * dataDist h₁ h₂ T / M
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  let Pj := fun (S : Fields) (u v : ℝ) =>
    (S.nu u v : ℂ) * S.theta u v / (S.r u v : ℂ) ^ 2 *
      (curvEM e S u v + 2 * starRingEnd ℂ (curvEM e S u v))
  let Pk := fun (S : Fields) (u v : ℝ) =>
    (S.lam u v : ℂ) * S.xi u v / (S.r u v : ℂ) ^ 2 *
      (curvEMIn e S u v + 2 * starRingEnd ℂ (curvEMIn e S u v))
  have hpoint (u v : ℝ) (hp : (u, v) ∈ triangle 0 T) :
      ‖Pj S₁ u v - Pj S₂ u v‖ + ‖emSourceJ e S₁ u v - emSourceJ e S₂ u v‖ +
        ‖Pk S₁ u v - Pk S₂ u v‖ + ‖emSourceK e S₁ u v - emSourceK e S₂ u v‖ ≤
          (Cj + Ck + Ce) * e ^ 2 * M ^ 2 * X := by
    rcases hp.2.1.eq_or_lt with heq | hlt
    · change u = v at heq
      subst v
      have hr₁ := (hs₁.c1.axis u hp).1
      have hr₂ := (hs₂.c1.axis u hp).1
      simp only [Pj, Pk, emSourceJ, emSourceK, hr₁, hr₂]
      norm_num
      positivity
    have hJbound := hj T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁
      hratio hfield hcharge u v hp.1 hlt hp.2.2
    have hKbound := hk T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁
      hratio hfield hcharge u v hp.1 hlt hp.2.2
    have hEbound := he T e ε M A S₁ S₂ h₁ h₂ hs₁ hs₂ hε₁ hσ₁
      hratio hfield hcharge (u, v) hp hlt
    calc
      _ = (‖Pj S₁ u v - Pj S₂ u v‖ + ‖Pk S₁ u v - Pk S₂ u v‖) +
          (‖emSourceJ e S₁ u v - emSourceJ e S₂ u v‖ +
            ‖emSourceK e S₁ u v - emSourceK e S₂ u v‖) := by ring
      _ ≤ (Cj * e ^ 2 * M ^ 2 * X + Ck * e ^ 2 * M ^ 2 * X) +
          Ce * e ^ 2 * M ^ 2 * X := add_le_add (add_le_add hJbound hKbound) hEbound
      _ = _ := by ring
  have harea := incoming_area_le_of_uniform_bound hs₂.pos.le
    (by positivity : 0 ≤ (Cj + Ck + Ce) * e ^ 2 * M ^ 2 * X)
    (F := fun p => ‖Pj S₁ p.1 p.2 - Pj S₂ p.1 p.2‖ₑ +
      ‖emSourceJ e S₁ p.1 p.2 - emSourceJ e S₂ p.1 p.2‖ₑ +
      ‖Pk S₁ p.1 p.2 - Pk S₂ p.1 p.2‖ₑ +
      ‖emSourceK e S₁ p.1 p.2 - emSourceK e S₂ p.1 p.2‖ₑ)
    (fun p hp => by
      have h := ENNReal.ofReal_le_ofReal (hpoint p.1 p.2 hp)
      rw [ENNReal.ofReal_add (by positivity) (norm_nonneg _),
        ENNReal.ofReal_add (by positivity) (norm_nonneg _),
        ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
        ofReal_norm, ofReal_norm, ofReal_norm, ofReal_norm] at h
      exact h)
  have hdata : ε * dataDist h₁ h₂ T / M ≤ dataDist h₁ h₂ T := by
    apply (div_le_iff₀ hM).2
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right (hε₁.trans hs₂.box.1) hδ
  calc
    _ ≤ ENNReal.ofReal (T ^ 2 * ((Cj + Ck + Ce) * e ^ 2 * M ^ 2 * X)) := harea
    _ = ENNReal.ofReal (4 * (Cj + Ck + Ce) * sigma e M T * X) := by
      congr 1
      dsimp only [sigma]
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      dsimp only [X]
      linarith only [hdata]

end EmcsfAcExtension.Local.Stab
