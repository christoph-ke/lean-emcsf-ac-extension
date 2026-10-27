module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Bounds
public import EmcsfAcExtension.Local.Defs.Params
import EmcsfAcExtension.Local.Apriori.BootstrapBox
import EmcsfAcExtension.Local.Apriori.BootstrapBounds
import EmcsfAcExtension.Local.Apriori.BootstrapMargin
import EmcsfAcExtension.Local.Apriori.Hardy
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Infra.Calculus.TriangleDiff

/-! # The smooth a priori box on complete triangles

Universal thresholds are chosen before the datum. The continuity bootstrap
runs with a positive excess over its actual variation; the uniform bounds
then pass to the datum variation by the approved N3 margin helper.
Only complete constructed subtriangles are used
(`charged_SF_new_version.tex:L6201–L6208`, approved internal project record).
-/

public section

open Set MeasureTheory Complex

namespace EmcsfAcExtension.Local.Null

/-- [node restart-sec-independent-null-construction#smooth-apriori-box]
Every small-BV classical restart solution on a complete triangle satisfies
all smooth a priori bounds, with no temporary bootstrap box premise.
Positive thresholds and the conclusion constant precede every datum and
depend only on the fixed box, uniformly in higher initial derivatives.
The bootstrap uses `ε' > datumVar` and passes to the actual variation. -/
theorem smooth_apriori_box : ∃ ε₁ δ₁ C₁ : ℝ, 0 < ε₁ ∧ 0 < δ₁ ∧ 0 < C₁ ∧
    ∀ (T e : ℝ) (S : Fields) (h : ℝ → ℂ), 0 < T →
      IsC1Solution e S (triangle 0 T) → IsRestartData S h T →
      datumVar h T ≤ ε₁ → chargedScale e h T ≤ δ₁ →
      SmoothBounds C₁ e T (datumVar h T) (datumM h T) S := by
  obtain ⟨εb, δb, hεb, hδb, hbox⟩ := bootBox_of_positive_margin
  obtain ⟨εc, δc, C, hεc, hδc, hC, hbounds⟩ := smoothBounds_of_apriori_setting
  let εu := min εb εc
  let δu := min δb δc
  have hεu : 0 < εu := lt_min hεb hεc
  have hδu : 0 < δu := lt_min hδb hδc
  refine ⟨εu / 4, δu / 4, C, by positivity, by positivity, hC, ?_⟩
  intro T e S h hT hS hdata hε hδ
  let d := datumVar h T
  let M := datumM h T
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hM : M = 1 + ‖h 0‖ + 10 * d := rfl
  have hM1 : 1 ≤ M := by
    rw [hM]
    have hn := norm_nonneg (h 0)
    linarith only [hd, hn]
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hM1
  change d ≤ εu / 4 at hε
  change |e| * (T / 2) * M ≤ δu / 4 at hδ
  let η := min (εu / 4) (1 / 20)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  apply smoothBounds_of_margin hη
  intro ε' hlo hhi
  let M' := 1 + ‖h 0‖ + 10 * ε'
  have hε' : ε' ≤ εu := by
    have hηu : η ≤ εu / 4 := min_le_left _ _
    change ε' < d + η at hhi
    linarith only [hhi, hηu, hε, hεu]
  have hM' : M' ≤ 2 * M := by
    have hη20 : η ≤ 1 / 20 := min_le_right _ _
    change ε' < d + η at hhi
    dsimp only [M']
    rw [hM] at hM1 ⊢
    linarith only [hhi, hη20, hM1]
  have hδ' : |e| * (T / 2) * M' ≤ δu := by
    have hscale := mul_le_mul_of_nonneg_left hM'
      (show 0 ≤ |e| * (T / 2) by positivity)
    nlinarith only [hscale, hδ, hδu]
  have hB := hbox e T ε' M' S h hT hS hdata hlo rfl
    (hε'.trans (min_le_left _ _)) (hδ'.trans (min_le_left _ _))
  have hset : AprioriSetting e T ε' M' S h := ⟨hT, hS, hdata, hlo.le, rfl, hB⟩
  exact hbounds e T ε' M' S h hset (hε'.trans (min_le_right _ _))
    (hδ'.trans (min_le_right _ _))

/-- [node restart-sec-independent-null-construction#complete-triangle-bootstrap]
The same universal smooth bounds apply on every positive complete
constructed subtriangle. Its incoming Hardy representation uses the actual
axis endpoint in that subtriangle. Thresholds and the conclusion constant
precede all data, uniformly in the constructed apex and higher derivatives.
This theorem applies bounds to existing solutions and asserts no existence
route on an unfinished carrier. -/
theorem complete_triangle_bootstrap : ∃ ε₁ δ₁ C₁ : ℝ,
    0 < ε₁ ∧ 0 < δ₁ ∧ 0 < C₁ ∧
    ∀ (T e : ℝ) (S : Fields) (h : ℝ → ℂ), 0 < T →
      IsC1Solution e S (triangle 0 T) → IsRestartData S h T →
      datumVar h T ≤ ε₁ → chargedScale e h T ≤ δ₁ →
      ∀ s, 0 < s → s ≤ T →
        SmoothBounds C₁ e s (datumVar h s) (datumM h s) S ∧
        ∀ u v, 0 ≤ u → u < v → v ≤ s →
          inSeg u v v ⊆ triangle 0 s ∧
          ‖S.xi u v / S.nu u v‖ ≤ (S.r u v)⁻¹ * ∫ x in u..v, S.r x v *
            ‖pdU (triangle 0 s) S.b x v + I * e * S.A x v * S.b x v‖ := by
  obtain ⟨ε₁, δ₁, C₁, hε₁, hδ₁, hC₁, hmain⟩ := smooth_apriori_box
  refine ⟨ε₁, δ₁, C₁, hε₁, hδ₁, hC₁, ?_⟩
  intro T e S h hT hS hdata hε hδ s hs hsT
  have hsub := triangle_subset_triangle hsT
  have hS' := hS.mono hsub (uniqueDiffOn_triangle hs)
  have hdata' := isRestartData_mono hdata hsT
  have hfinite := datum_variation_ne_top_of_classical_data hT hS hdata
  have hvar : datumVar h s ≤ datumVar h T := ENNReal.toReal_mono hfinite
    (eVariationOn.mono h (Icc_subset_Icc le_rfl hsT))
  have hM : datumM h s ≤ datumM h T := by
    dsimp only [datumM]
    linarith only [hvar]
  have hdS : 0 ≤ datumVar h s := ENNReal.toReal_nonneg
  have hM0 : 0 ≤ datumM h s := by
    dsimp only [datumM]
    have hn := norm_nonneg (h 0)
    linarith only [hdS, hn]
  have hscale : chargedScale e h s ≤ chargedScale e h T := by
    dsimp only [chargedScale]
    exact mul_le_mul (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hsT (by norm_num)) (abs_nonneg e)) hM hM0
        (by positivity : 0 ≤ |e| * (T / 2))
  refine ⟨hmain s e S h hs hS' hdata' (hvar.trans hε) (hscale.trans hδ), ?_⟩
  intro u v hu huv hvs
  refine ⟨?_, bv_hardy_in hS' hu huv hvs⟩
  rintro p ⟨hux, hxv, rfl⟩
  exact ⟨hu.trans hux, hxv, hvs⟩

end EmcsfAcExtension.Local.Null
