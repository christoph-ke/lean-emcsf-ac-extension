module

public import EmcsfAcExtension.Local.Limit.AcBridgeSmallness
public import EmcsfAcExtension.Local.Limit.AcBridgeIdentity

/-! # Broad identification under the original common AC box

The construction thresholds are fixed first. Smallness in the original
box then makes each actual AC datum admissible, as in internal project record item 7.2–4.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Make a broad common-box datum admissible for any prescribed positive
construction thresholds. The threshold depends only on `c,H,ε,δ`, before
`T,e,η,M,Cb`, the datum, solution, and envelope. The size bound retains the
original common-box `M`. This is internal project record item 7.2–3. -/
theorem ac_data_admissible_of_initial_envelope (c H ε δ : ℝ)
    (hc : 0 < c) (hH : 0 < H) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ s : ℝ, 0 < s ∧
      ∀ (T e η M Cb : ℝ) (h : ℝ → ℂ) (S : Fields) (J : ℝ → ℝ),
        0 < T → 0 ≤ η → AbsolutelyContinuousOnInterval h 0 T →
        IsSolution e S (triangle 0 T) → IsRestartData S h T →
        StabBox S c Cb η M (triangle 0 T) →
        IntervalIntegrable J volume 0 T →
        (∀ᵐ v ∂volume.restrict (Icc 0 T), ‖jOut S 0 v‖ ≤ J v) →
        (∫ v in (0 : ℝ)..T, J v) ≤ H * η → η ^ 2 + sigma e M T ≤ s →
        datumVar h T ≤ ε ∧ chargedScale e h T ≤ δ ∧ datumM h T ≤ 3 * M := by
  let D := 2 * H / c
  have hD : 0 < D := div_pos (mul_pos (by norm_num) hH) hc
  let s := min (1 / 4) (min ((1 / (10 * D)) ^ 2)
    (min ((ε / D) ^ 2) (δ ^ 2 / 9)))
  have hs : 0 < s := by
    dsimp only [s]
    exact lt_min (by norm_num) (lt_min (sq_pos_of_pos (by positivity))
      (lt_min (sq_pos_of_pos (div_pos hε hD)) (by positivity)))
  refine ⟨s, hs, ?_⟩
  intro T e η M Cb h S J hT hη hac hS hd hbox hJ hdom hmass hsmall
  have hσ : 0 ≤ sigma e M T := by unfold sigma; positivity
  have hηs : η ^ 2 ≤ s := le_trans (le_add_of_nonneg_right hσ) hsmall
  have hσs : sigma e M T ≤ s := le_trans (le_add_of_nonneg_left (sq_nonneg η)) hsmall
  have hs1 : s ≤ 1 / 4 := min_le_left _ _
  have hs2 : s ≤ (1 / (10 * D)) ^ 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hs3 : s ≤ (ε / D) ^ 2 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hs4 : s ≤ δ ^ 2 / 9 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hηhalf : η ≤ 1 / 2 := by nlinarith [hηs.trans hs1]
  have hηten : η ≤ 1 / (10 * D) := by
    have hh : 0 < 1 / (10 * D) := by positivity
    nlinarith [hηs.trans hs2]
  have hηeps : η ≤ ε / D := by nlinarith [hηs.trans hs3, div_pos hε hD]
  have hvar : datumVar h T ≤ D * η :=
    datumVar_le_of_initial_envelope hT hc hη hηhalf hS hd hac hbox hJ hdom hmass
  have heps : datumVar h T ≤ ε := hvar.trans ((le_div_iff₀' hD).1 hηeps)
  have hten : 10 * datumVar h T ≤ 1 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 10) hD)).1 hηten
    nlinarith only [hvar, hh]
  have hp0 : (0, 0) ∈ triangle 0 T := ⟨le_rfl, le_rfl, hT.le⟩
  have hv0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hvertex : ‖h 0‖ ≤ M := by
    rw [← (hd.1 0 hv0).2, (hS.axis 0 hp0).2.2.2.2.1]
    exact (hbox.2 (0, 0) hp0).2.2.2.2.2.2
  have hM : 0 ≤ M := le_trans (by norm_num : (0 : ℝ) ≤ 1) hbox.1
  have hdatumM : datumM h T ≤ 3 * M := by
    unfold datumM
    linarith only [hvertex, hten, hbox.1]
  have hcharged : chargedScale e h T ≤ δ := by
    let q := |e| * (T / 2) * M
    have hq : 0 ≤ q := by dsimp only [q]; positivity
    have hq2 : q ^ 2 = sigma e M T := by dsimp only [q, sigma]; rw [mul_pow, mul_pow, sq_abs]; ring
    have hqδ : 3 * q ≤ δ := by nlinarith [hσs.trans hs4, hq2]
    calc
      chargedScale e h T ≤ |e| * (T / 2) * (3 * M) :=
        mul_le_mul_of_nonneg_left hdatumM (by positivity)
      _ = 3 * q := by dsimp only [q]; ring
      _ ≤ δ := hqδ
  exact ⟨heps, hcharged, hdatumM⟩

/-- Identify any general AC solution in a sufficiently small common box,
using its original envelope and size parameters. The positive smallness
threshold depends only on the fixed gap `c` and envelope coefficient `H`.
The bound coefficient is universal, before `T,e,η,M`, datum and competitor.
There is no explicit construction-smallness hypothesis on the datum. -/
theorem ac_identification_of_envelope_inputs
    (hex : WholeTriangleExistenceStmt) (hstab : StabExtendedStmt)
    (c H : ℝ) (hc : 0 < c) (hH : 0 < H) :
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧
      ∀ (T e η M Cb : ℝ) (h : ℝ → ℂ) (S : Fields) (J : ℝ → ℝ),
        0 < T → 0 ≤ η → AbsolutelyContinuousOnInterval h 0 T →
        IsSolution e S (triangle 0 T) → IsRestartData S h T →
        StabBox S c Cb η M (triangle 0 T) →
        IntervalIntegrable J volume 0 T →
        (∀ᵐ v ∂volume.restrict (Icc 0 T), ‖jOut S 0 v‖ ≤ J v) →
        (∫ v in (0 : ℝ)..T, J v) ≤ H * η → η ^ 2 + sigma e M T ≤ s →
        IsConstructedLimit e T h S ∧ ExistenceBounds C e T h S := by
  obtain ⟨ε, δ, C, hε, hδ, hC, hid⟩ := ac_identification_of_inputs hex hstab
  obtain ⟨s, hs, hadm⟩ := ac_data_admissible_of_initial_envelope c H ε δ hc hH hε hδ
  refine ⟨s, C, hs, hC, ?_⟩
  intro T e η M Cb h S J hT hη hac hS hd hbox hJ hdom hmass hsmall
  obtain ⟨heps, hcharged, _⟩ := hadm T e η M Cb h S J hT hη hac hS hd hbox hJ hdom hmass hsmall
  exact hid T e h S hT hac heps hcharged hS hd

end EmcsfAcExtension.Local
