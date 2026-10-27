module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Apriori.GeometryBox
import EmcsfAcExtension.Local.Apriori.BootstrapScalar
import EmcsfAcExtension.Local.Apriori.Charge

/-! # Common parameters for strict bootstrap improvement

A finite minimum of positive thresholds is chosen before every datum.
The improved numerical box has fixed margins and is independent of the
smooth initial derivative (`charged_SF_new_version.tex:L4805–L4838`, approved
internal project record (29)–(30)).
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- [node restart-sec-independent-area#bootstrap-parameter-choice]
Universal positive thresholds simultaneously improve both geometric and
scalar bootstrap bounds. They are chosen before the coupling, triangle,
background and data, uniformly in higher initial derivatives. The source
constants four and ten are retained. For positive `ε`, the ratio bounds
also have a strict margin; the scalar margin holds even at zero. -/
theorem bootstrap_parameter_choice : ∃ ε₀ δ₀ : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
    ∀ u v, (u, v) ∈ triangle 0 T →
      3 / 8 ≤ S.lam u v ∧ S.lam u v ≤ 5 / 8 ∧
      3 / 8 ≤ -S.nu u v ∧ -S.nu u v ≤ 5 / 8 ∧
      7 / 8 ≤ 1 - S.mu u v ∧ ‖S.theta u v / S.lam u v‖ ≤ 3 * ε ∧
      ‖S.xi u v / S.nu u v‖ ≤ 3 * ε ∧
      ‖S.phi u v‖ ≤ ‖h 0‖ + 33 / 8 * ε ∧ ‖S.phi u v‖ < M := by
  obtain ⟨εg, δg, Cg, hεg, hδg, hCg, hgeom⟩ := geometry_bootstrap_improvement
  obtain ⟨εs, δs, hεs, hδs, hscalar⟩ := scalar_bootstrap_improvement
  have hden : 0 < 128 * (Cg + 1) := by positivity
  refine ⟨min εg (min εs (min 1 (1 / (128 * (Cg + 1))))), min δg δs,
    lt_min hεg (lt_min hεs (lt_min (by norm_num) (div_pos (by norm_num) hden))),
    lt_min hδg hδs, ?_⟩
  intro e T ε M S h hset hε hδ u v hp
  have heG := hε.trans (min_le_left _ _)
  have heS := (hε.trans (min_le_right _ _)).trans (min_le_left _ _)
  have heRest := (hε.trans (min_le_right _ _)).trans (min_le_right _ _)
  have he1 := heRest.trans (min_le_left _ _)
  have heDiv := heRest.trans (min_le_right _ _)
  have hε0 := hset.eps_nonneg
  have heSq : ε ^ 2 ≤ ε := by nlinarith only [hε0, he1]
  have hprod := (le_div_iff₀ hden).mp heDiv
  have heC : Cg * ε ≤ 1 / 128 := by nlinarith only [hprod, hε0]
  have hi := mul_le_mul_of_nonneg_left heSq hCg.le
  have hsmall : Cg * ε ^ 2 ≤ 1 / 8 := by linarith only [hi, heC]
  have hg := hgeom e T ε M S h hset heG (hδ.trans (min_le_left _ _)) u v hp
  obtain ⟨ho, hi, _, hφ, hφM⟩ := hscalar e T ε M S h hset heS
    (hδ.trans (min_le_right _ _)) u v hp
  have hlam : |S.lam u v - 1 / 2| ≤ 1 / 8 := by
    linarith only [hg, hsmall, abs_nonneg (-S.nu u v - 1 / 2), abs_nonneg (S.mu u v)]
  have hnu : |-S.nu u v - 1 / 2| ≤ 1 / 8 := by
    linarith only [hg, hsmall, abs_nonneg (S.lam u v - 1 / 2), abs_nonneg (S.mu u v)]
  have hmu : |S.mu u v| ≤ 1 / 8 := by
    linarith only [hg, hsmall, abs_nonneg (S.lam u v - 1 / 2),
      abs_nonneg (-S.nu u v - 1 / 2)]
  have hl := abs_le.mp hlam
  have hn := abs_le.mp hnu
  have hm := (le_abs_self (S.mu u v)).trans hmu
  refine ⟨?_, ?_, ?_, ?_, ?_, ho, hi, hφ, hφM⟩ <;> linarith only [hl.1, hl.2, hn.1, hn.2, hm]

end EmcsfAcExtension.Local
