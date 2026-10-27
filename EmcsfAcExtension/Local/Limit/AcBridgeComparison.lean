module

public import EmcsfAcExtension.Local.Limit.StabilitySettings
public import EmcsfAcExtension.Local.Limit.StabilityPassage
public import EmcsfAcExtension.Local.Limit.Inputs
import EmcsfAcExtension.Local.Stability.MainFinite
import EmcsfAcExtension.Local.Limit.ExistencePointwise

/-! # Extended comparisons of constructed AC pairs

internal project record item 7.5–6: retain the comparison size explicitly when passing the
classical potential, charge, and mass-ratio estimates. No strong derivative
conclusion for the potential or mass ratio is asserted here.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Retain the extended pointwise comparisons after construction. The positive
thresholds and coefficient are universal, before all data, time, and coupling.
The explicit size is twice the maximum of the two literal datum sizes; it is
not an estimate constant. Only the authorized classical comparison is pending. -/
theorem constructed_extended_comparison_of_inputs (hstab : StabExtendedStmt) :
    ∃ ε δ C : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < C ∧
      ∀ (T e : ℝ) (h₁ h₂ : ℝ → ℂ) (S₁ S₂ : Fields), 0 < T →
        AbsolutelyContinuousOnInterval h₁ 0 T → datumVar h₁ T ≤ ε → chargedScale e h₁ T ≤ δ →
        AbsolutelyContinuousOnInterval h₂ 0 T → datumVar h₂ T ≤ ε → chargedScale e h₂ T ≤ δ →
        IsConstructedLimit e T h₁ S₁ → IsConstructedLimit e T h₂ S₂ →
        StabConclusion C e T h₁ h₂ S₁ S₂ ∧
        supDist T S₁.A S₂.A ≤ ENNReal.ofReal
          (C * |e| * T * (2 * max (datumM h₁ T) (datumM h₂ T)) * dataDist h₁ h₂ T) ∧
        supDist T S₁.mu S₂.mu ≤ ENNReal.ofReal (C * dataDist h₁ h₂ T) ∧
        (∀ p ∈ triangle 0 T, p.1 < p.2 →
          |S₁.Q p.1 p.2 - S₂.Q p.1 p.2| / S₁.r p.1 p.2 ^ 2 ≤
            C * |e| * (2 * max (datumM h₁ T) (datumM h₂ T)) * dataDist h₁ h₂ T) := by
  obtain ⟨η, C, hη, hC, hcomp⟩ := hstab 1 (by norm_num)
  obtain ⟨ε, δ, q, hε, hδ, _, ht⟩ := comparison_tails_with_size_of_constructed_limits η hη
  refine ⟨ε, δ, C, hε, hδ, hC, ?_⟩
  intro T e h₁ h₂ S₁ S₂ hT hac₁ hd₁ he₁ hac₂ hd₂ he₂ hc₁ hc₂
  obtain ⟨Sn₁, Sn₂, hn₁, hn₂, M, hs₁, hs₂, hl₁, hl₂, hd, hsmall, hM⟩ :=
    ht T e h₁ h₂ S₁ S₂ hT hac₁ hd₁ he₁ hac₂ hd₂ he₂ hc₁ hc₂
  have hb n := hcomp T e q M (Sn₁ n) (Sn₂ n) (hn₁ n) (hn₂ n) (hs₁ n) (hs₂ n) hsmall
  have hA : supDist T S₁.A S₂.A ≤ ENNReal.ofReal (C * |e| * T * M * dataDist h₁ h₂ T) := by
    apply iSup₂_le
    intro p hp
    have hn n : ENNReal.ofReal |(Sn₁ n).A p.1 p.2 - (Sn₂ n).A p.1 p.2| ≤
        ENNReal.ofReal (C * |e| * T * M * dataDist (hn₁ n) (hn₂ n) T) := by
      simpa only [← ofReal_norm, Real.norm_eq_abs] using (le_iSup₂ p hp).trans (hb n).extra_A
    have hleft := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((hl₁.unif_A.tendsto_at hp).sub (hl₂.unif_A.tendsto_at hp)).abs)
    have hright := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hd.const_mul (C * |e| * T *
        M))
    simpa only [ofReal_norm, Real.enorm_eq_ofReal_abs, Function.uncurry_def] using
      le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hn)
  have hg₁ := hl₁.lower_geometry_of_settings hs₁
  have hg₂ := hl₂.lower_geometry_of_settings hs₂
  have hr₁ (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) (hlt : p.1 < p.2) : 0 < S₁.r p.1 p.2 :=
    (div_pos (sub_pos.2 hlt) (by norm_num : (0 : ℝ) < 4)).trans_le (hg₁ p hp).2.2
  have hr₂ (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) (hlt : p.1 < p.2) : 0 < S₂.r p.1 p.2 :=
    (div_pos (sub_pos.2 hlt) (by norm_num : (0 : ℝ) < 4)).trans_le (hg₂ p hp).2.2
  have hm₁ (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) :=
    hl₁.tendsto_mu_of_radius_pos (fun n => (hs₁ n).c1) hr₁ hp
  have hm₂ (p : ℝ × ℝ) (hp : p ∈ triangle 0 T) :=
    hl₂.tendsto_mu_of_radius_pos (fun n => (hs₂ n).c1) hr₂ hp
  refine ⟨stab_conclusion_of_smooth_bounds hC.le hl₁ hl₂ hs₁ hs₂ hd hb, hM ▸ hA, ?_, ?_⟩
  · apply iSup₂_le
    intro p hp
    have hn n : ENNReal.ofReal |(Sn₁ n).mu p.1 p.2 - (Sn₂ n).mu p.1 p.2| ≤
        ENNReal.ofReal (C * dataDist (hn₁ n) (hn₂ n) T) := by
      simpa only [← ofReal_norm, Real.norm_eq_abs] using (le_iSup₂ p hp).trans (hb n).extra_mu
    have hleft := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hm₁ p hp).sub (hm₂ p
        hp)).abs
    have hright := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hd.const_mul C)
    simpa only [ofReal_norm, Real.enorm_eq_ofReal_abs, Function.uncurry_def] using
      le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hn)
  · intro p hp hlt
    have hleft := (((hl₁.unif_Q.tendsto_at hp).sub (hl₂.unif_Q.tendsto_at hp)).abs).div
      ((hl₁.unif_r.tendsto_at hp).pow 2) (pow_ne_zero 2 (hr₁ p hp hlt).ne')
    have hright := hd.const_mul (C * |e| * M)
    have hh := le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall fun n => (hb n).extra_Q p
        hp hlt)
    simpa only [hM, Function.uncurry_def] using hh

end EmcsfAcExtension.Local
