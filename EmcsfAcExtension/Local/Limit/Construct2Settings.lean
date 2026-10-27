module

public import EmcsfAcExtension.Local.Limit.Construct2
import EmcsfAcExtension.Local.Limit.Construct2Cauchy

/-! # Common comparison settings for the actual constructed sequence

The universal comparison threshold is selected before the datum. The
common scalar size is twice the original datum size, and all dimensional
factors remain explicit. The final root constants may subsequently shrink.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- Convert supplied smooth bounds into the fixed comparison box.
The supplied constant `C` retains its original scope; the numerical
quarter margin and the common scalar size are explicit premises of this helper. -/
theorem setting_of_smooth_bounds {C e T d M q : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hT : 0 < T) (hc1 : IsC1Solution e S (triangle 0 T)) (hd : IsRestartData S h T)
    (hb : SmoothBounds C e T d (datumM h T) S)
    (hgeom : C * d ^ 2 ≤ 1 / 4) (hscalar : C * d ≤ q)
    (hM : datumM h T ≤ M) (hM1 : 1 ≤ M) : StabSetting e T q M 1 S h := by
  refine ⟨hT, hc1, hd, ⟨hM1, ?_⟩, ?_⟩
  · intro p hp
    have hg := (hb.geom p hp).trans hgeom
    have hm := hb.mu_nonneg p hp
    have hl := abs_le.mp (show |S.lam p.1 p.2 - 1 / 2| ≤ 1 / 4 by
      linarith only [hg, hm, abs_nonneg (S.nu p.1 p.2 + 1 / 2)])
    have hn := abs_le.mp (show |S.nu p.1 p.2 + 1 / 2| ≤ 1 / 4 by
      linarith only [hg, hm, abs_nonneg (S.lam p.1 p.2 - 1 / 2)])
    have hmu : S.mu p.1 p.2 ≤ 1 / 4 := by
      linarith only [hg, abs_nonneg (S.lam p.1 p.2 - 1 / 2),
        abs_nonneg (S.nu p.1 p.2 + 1 / 2)]
    refine ⟨?_, ?_, ?_, ?_, ?_, (hb.ratio p hp).trans hscalar, (hb.phi_le p hp).trans hM⟩ <;>
      linarith only [hl.1, hl.2, hn.1, hn.2, hmu]
  · simpa only [one_mul] using hb.env.trans (ENNReal.ofReal_le_ofReal hscalar)

/-- Choose whole-triangle approximants in one admissible comparison setting.
All three positive thresholds and the common comparison parameter `q` are
selected before the datum; their dependence is only on the two producer
contracts and the fixed numerical box. The common size is `2 * datumM h T`.
Neither a mixed Cauchy estimate nor a limiting-field conclusion is a premise. -/
theorem Null.comparison_approximants_of_inputs (hex : WholeTriangleExistenceStmt)
    (η : ℝ) (hη : 0 < η) :
    ∃ ε δ q : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < q ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T →
        AbsolutelyContinuousOnInterval h 0 T → datumVar h T ≤ ε →
        chargedScale e h T ≤ δ →
        ∃ (hn : ℕ → ℝ → ℂ) (Sn : ℕ → Fields),
          (∀ n, ContDiffOn ℝ 1 (hn n) (Icc 0 T)) ∧ (∀ n, hn n 0 = h 0) ∧
          Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) ∧
          Tendsto (fun n => eVariationOn (hn n - h) (Icc 0 T)) atTop (𝓝 0) ∧
          Tendsto (fun n => datumVar (hn n) T) atTop (𝓝 (datumVar h T)) ∧
          (∀ n, StabSetting e T q (2 * datumM h T) 1 (Sn n) (hn n)) ∧
          q ^ 2 + sigma e (2 * datumM h T) T ≤ η := by
  obtain ⟨εa, δa, C, hεa, hδa, hC, ha⟩ := Null.whole_triangle_approximants_of_inputs hex
  let B := max 1 C
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hCB : C ≤ B := le_max_right _ _
  let q := min η (1 / 16)
  have hq : 0 < q := lt_min hη (by norm_num)
  have hqη : q ≤ η := min_le_left _ _
  have hq16 : q ≤ 1 / 16 := min_le_right _ _
  let ε := min εa (min (1 / 2) (q / (4 * B)))
  let δ := min δa (q / 4)
  have hε : 0 < ε := lt_min hεa (lt_min (by norm_num) (by positivity))
  have hδ : 0 < δ := lt_min hδa (by positivity)
  have hεa' : ε ≤ εa := min_le_left _ _
  have hεhalf : ε ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεq : ε ≤ q / (4 * B) := (min_le_right _ _).trans (min_le_right _ _)
  have hδq : δ ≤ q / 4 := min_le_right _ _
  refine ⟨ε, δ, q, hε, hδ, hq, ?_⟩
  intro T e h hT hac hsmall hscale
  obtain ⟨hn, Sn, hs, hv, herr, hevar, hvar, hc1, hb⟩ :=
    ha T e h hT hac (hsmall.trans hεa') (hscale.trans (min_le_left _ _))
  have hMlim : Tendsto (fun n => datumM (hn n) T) atTop (𝓝 (datumM h T)) := by
    unfold datumM
    simpa only [hv] using tendsto_const_nhds.add (hvar.const_mul 10)
  have hM1 : 1 ≤ datumM h T := by
    unfold datumM
    have hv0 : 0 ≤ datumVar h T := ENNReal.toReal_nonneg
    linarith only [norm_nonneg (h 0), hv0]
  have hM0 : 0 < datumM h T := zero_lt_one.trans_le hM1
  have hev := (tendsto_order.1 hvar).2 (2 * ε) (by linarith only [hsmall, hε])
  have heM := (tendsto_order.1 hMlim).2 (2 * datumM h T) (by linarith only [hM0])
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev.and heM)
  have hsetting n : StabSetting e T q (2 * datumM h T) 1 (Sn (n + N)) (hn (n + N)) := by
    have hvn : datumVar (hn (n + N)) T ≤ 2 * ε := (hN _ (Nat.le_add_left _ _)).1.le
    have hv0 : 0 ≤ datumVar (hn (n + N)) T := ENNReal.toReal_nonneg
    have hv1 : datumVar (hn (n + N)) T ≤ 1 := by linarith only [hvn, hεhalf]
    have hBε : B * (2 * ε) ≤ q / 2 := by
      have hh := (le_div_iff₀ (show 0 < 4 * B by positivity)).1 hεq
      nlinarith only [hh]
    have hCv : C * datumVar (hn (n + N)) T ≤ q / 2 :=
      (mul_le_mul_of_nonneg_right hCB hv0).trans
        ((mul_le_mul_of_nonneg_left hvn hB.le).trans hBε)
    have hgeom : C * datumVar (hn (n + N)) T ^ 2 ≤ 1 / 4 := by
      have hh := mul_le_mul_of_nonneg_left hv1 (mul_nonneg hC.le hv0)
      nlinarith only [hh, hCv, hq16]
    exact setting_of_smooth_bounds hT (hc1 _).1 (hc1 _).2 (hb _) hgeom
      (hCv.trans (by linarith only [hq])) (hN _ (Nat.le_add_left _ _)).2.le
      (by linarith only [hM1])
  refine ⟨fun n => hn (n + N), fun n => Sn (n + N), fun n => hs _, fun n => hv _,
    herr.comp (tendsto_add_atTop_nat N), hevar.comp (tendsto_add_atTop_nat N),
    hvar.comp (tendsto_add_atTop_nat N), hsetting, ?_⟩
  have hscale0 : 0 ≤ chargedScale e h T := by unfold chargedScale datumM; positivity
  have hscaleq : chargedScale e h T ≤ q / 4 := hscale.trans hδq
  have hσ : sigma e (2 * datumM h T) T = 4 * chargedScale e h T ^ 2 := by
    simp only [sigma, chargedScale, mul_pow, sq_abs]
    ring
  rw [hσ]
  nlinarith only [hscale0, hscaleq, hq16, hqη, sq_nonneg (q / 4 - chargedScale e h T),
    mul_nonneg (sub_nonneg.mpr hscaleq) (add_nonneg (by linarith only [hq]) hscale0),
    mul_nonneg hq.le (sub_nonneg.mpr hq16)]

end EmcsfAcExtension.Local
