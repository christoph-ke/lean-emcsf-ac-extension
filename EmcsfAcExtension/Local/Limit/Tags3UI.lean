module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Infra.UnifIntegrable
import EmcsfAcExtension.Local.Limit.UIRoute
import EmcsfAcExtension.Local.Limit.Construct2UI
import EmcsfAcExtension.Local.Construction.WireC1Bound
import EmcsfAcExtension.Local.Stability.ExtendedLipschitz
import EmcsfAcExtension.Local.Stability.FieldDifferenceInitial
import EmcsfAcExtension.Local.Apriori.Bootstrap
import EmcsfAcExtension.Infra.W11.Approximation

/-! # Unconditional strong-comparison uniform integrability

The classical comparison theorem supplies mixed Cauchy control from strong
representative W¹¹ data convergence. The coefficient-one envelope inequalities
and both UI conclusions cover every admissible family, including families with
varying vertex values. The construction export also supplies such a family.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-bv-stability-independent#envelope-ui-via-strong-comparison]
[node restart-sec-independent-area#approximation-envelope-uniform-integrability]
Both coefficient-one comparisons, mixed Cauchy control and uniform integrability
for every classical approximation in the fixed box, charged_SF_new_version.tex:L5567–L5576.
The positive threshold depends only on the envelope coefficient `A`, before
time, coupling, size, datum and family; no derivative supremum enters.
Strong data convergence includes convergent, possibly unequal vertex values. -/
theorem Stab.envelope_ui_via_strong_comparison (A : ℝ) (hA : 0 < A) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (T e ε M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ),
        (∀ n, StabSetting e T ε M A (Sn n) (hn n)) →
        AbsolutelyContinuousOnInterval h 0 T →
        Tendsto (fun n => dataDist (hn n) h T) atTop (𝓝 0) →
        ε ^ 2 + sigma e M T ≤ η →
        (∀ n m,
          (∫⁻ v in Icc 0 T, ENNReal.ofReal
            |(outEnv 0 (jC1 (triangle 0 T) (Sn n)) v).toReal -
              (outEnv 0 (jC1 (triangle 0 T) (Sn m)) v).toReal|) ≤
                jDist T (Sn n) (Sn m) ∧
          (∫⁻ u in Icc 0 T, ENNReal.ofReal
            |(inEnv T (kC1 e (triangle 0 T) (Sn n)) u).toReal -
              (inEnv T (kC1 e (triangle 0 T) (Sn m)) u).toReal|) ≤
                kDist e T (Sn n) (Sn m)) ∧
        (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
          jDist T (Sn n) (Sn m) + kDist e T (Sn n) (Sn m) < ENNReal.ofReal ρ) ∧
        UnifIntegrable (fun n v => (outEnv 0 (jC1 (triangle 0 T) (Sn n)) v).toReal)
          1 (volume.restrict (Icc 0 T)) ∧
        UnifIntegrable (fun n u => (inEnv T (kC1 e (triangle 0 T) (Sn n)) u).toReal)
          1 (volume.restrict (Icc 0 T)) := by
  obtain ⟨η, C, hη, hC, hcomp⟩ := stab_extended A hA
  refine ⟨η, hη, ?_⟩
  intro T e ε M Sn hn h hs hac hd hsmall
  have hT := (hs 0).pos
  have hb n := (stab_initial_datum_ac (hs n)).boundedVariationOn_Icc hT.le
  have hh := hac.boundedVariationOn_Icc hT.le
  have hdata : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      dataDist (hn n) (hn m) T < ρ := by
    intro ρ hρ
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hd).2 (ρ / 2) (by positivity))
    refine ⟨N, fun n hn' m hm' => ?_⟩
    calc
      dataDist (hn n) (hn m) T ≤ dataDist (hn n) h T + dataDist (hn m) h T := by
        change W11.intervalDist 0 T (hn n) (hn m) ≤
          W11.intervalDist 0 T (hn n) h + W11.intervalDist 0 T (hn m) h
        rw [W11.intervalDist_comm 0 T (hn m) h]
        exact W11.intervalDist_triangle (hb n) hh (hb m)
      _ < ρ := by linarith only [hN n hn', hN m hm']
  have hc : ∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      jDist T (Sn n) (Sn m) + kDist e T (Sn n) (Sn m) < ENNReal.ofReal ρ := by
    intro ρ hρ
    obtain ⟨N, hN⟩ := hdata (ρ / C) (div_pos hρ hC)
    refine ⟨N, fun n hn' m hm' => ?_⟩
    have hb := (hcomp T e ε M (Sn n) (Sn m) (hn n) (hn m)
      (hs n) (hs m) hsmall).main
    have hjk : jDist T (Sn n) (Sn m) + kDist e T (Sn n) (Sn m) ≤
        ENNReal.ofReal (C * dataDist (hn n) (hn m) T) :=
      (le_self_add.trans (le_self_add.trans (le_self_add.trans le_self_add))).trans hb
    apply hjk.trans_lt
    apply (ENNReal.ofReal_lt_ofReal_iff hρ).2
    exact (lt_div_iff₀' hC).1 (hN n hn' m hm')
  refine ⟨fun n m => Stab.envelope_difference_le hT (hs n).c1 (hs m).c1, hc, ?_⟩
  apply Null.envelope_uniform_integrability_of_cauchy hT (fun n => (hs n).c1)
  · intro ρ hρ
    obtain ⟨N, hN⟩ := hc ρ hρ
    exact ⟨N, fun n hn' m hm' => le_self_add.trans_lt (hN n hn' m hm')⟩
  · intro ρ hρ
    obtain ⟨N, hN⟩ := hc ρ hρ
    exact ⟨N, fun n hn' m hm' => le_add_self.trans_lt (hN n hn' m hm')⟩

/-- [node restart-sec-independent-null-construction#envelope-uniform-integrability]
Construct full-triangle approximants with both uniformly integrable envelopes,
charged_SF_new_version.tex:L6371–L6449. Both positive thresholds are universal, before
time, coupling, AC datum and every approximation derivative. Existence,
comparison settings and mixed Cauchy control are all discharged. -/
theorem Null.constructed_envelope_ui :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T →
        AbsolutelyContinuousOnInterval h 0 T → datumVar h T ≤ ε →
        chargedScale e h T ≤ δ →
        ∃ (hn : ℕ → ℝ → ℂ) (Sn : ℕ → Fields),
          (∀ n, ContDiffOn ℝ 1 (hn n) (Icc 0 T)) ∧ (∀ n, hn n 0 = h 0) ∧
          Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) ∧
          Tendsto (fun n => eVariationOn (hn n - h) (Icc 0 T)) atTop (𝓝 0) ∧
          (∀ n, IsC1Solution e (Sn n) (triangle 0 T) ∧ IsRestartData (Sn n) (hn n) T) ∧
          UnifIntegrable (fun n v => (outEnv 0 (jC1 (triangle 0 T) (Sn n)) v).toReal)
            1 (volume.restrict (Icc 0 T)) ∧
          UnifIntegrable (fun n u => (inEnv T (kC1 e (triangle 0 T) (Sn n)) u).toReal)
            1 (volume.restrict (Icc 0 T)) :=
  Null.constructed_envelope_ui_of_inputs whole_triangle_existence stab_extended

/-- [node restart-sec-independent-area#approximation-envelope-uniform-integrability]
[node restart-sec-bv-stability-independent#envelope-ui-via-strong-comparison]
Uniform integrability for every approximation family with uniformly small
initial variation and charged scale, charged_SF_new_version.tex:L4946–L4946,L5567–L5576.
The positive thresholds are universal, before time, coupling, the common
datum-size bound `M`, the limiting AC datum and the family. Every comparison
box and envelope-bound premise is discharged by the smooth a priori theorem.
No initial derivative bound or common-vertex equality is assumed. -/
theorem Area.approximation_envelope_uniform_integrability :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (T e M : ℝ) (Sn : ℕ → Fields) (hn : ℕ → ℝ → ℂ) (h : ℝ → ℂ),
        0 < T → 1 ≤ M → AbsolutelyContinuousOnInterval h 0 T →
        (∀ n, IsC1Solution e (Sn n) (triangle 0 T) ∧ IsRestartData (Sn n) (hn n) T) →
        (∀ n, datumVar (hn n) T ≤ ε ∧ datumM (hn n) T ≤ M) →
        |e| * (T / 2) * M ≤ δ →
        Tendsto (fun n => dataDist (hn n) h T) atTop (𝓝 0) →
        UnifIntegrable (fun n v => (outEnv 0 (jC1 (triangle 0 T) (Sn n)) v).toReal)
          1 (volume.restrict (Icc 0 T)) ∧
        UnifIntegrable (fun n u => (inEnv T (kC1 e (triangle 0 T) (Sn n)) u).toReal)
          1 (volume.restrict (Icc 0 T)) := by
  obtain ⟨η, hη, hui⟩ := Stab.envelope_ui_via_strong_comparison 1 (by norm_num)
  obtain ⟨εa, δa, C, hεa, hδa, hC, hap⟩ := Null.smooth_apriori_box
  let B := max 1 C
  let q := min η (1 / 16)
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hq : 0 < q := lt_min hη (by norm_num)
  have hqη : q ≤ η := min_le_left _ _
  have hq16 : q ≤ 1 / 16 := min_le_right _ _
  refine ⟨min εa (min 1 (q / (2 * B))), min δa q,
    lt_min hεa (lt_min zero_lt_one (by positivity)), lt_min hδa hq, ?_⟩
  intro T e M Sn hn h hT hM hac hs hd he hlim
  have hcoef : 0 ≤ |e| * (T / 2) := mul_nonneg (abs_nonneg _) (by positivity)
  have hsetting n : StabSetting e T q M 1 (Sn n) (hn n) := by
    have hd0 : 0 ≤ datumVar (hn n) T := ENNReal.toReal_nonneg
    have hd1 : datumVar (hn n) T ≤ 1 :=
      ((hd n).1.trans (min_le_right _ _)).trans (min_le_left _ _)
    have hdq : datumVar (hn n) T ≤ q / (2 * B) :=
      ((hd n).1.trans (min_le_right _ _)).trans (min_le_right _ _)
    have hBd := (le_div_iff₀ (show 0 < 2 * B by positivity)).1 hdq
    have hCd : C * datumVar (hn n) T ≤ q / 2 := by
      have hCB := mul_le_mul_of_nonneg_right (le_max_right 1 C) hd0
      change C * datumVar (hn n) T ≤ B * datumVar (hn n) T at hCB
      linarith only [hCB, hBd]
    have hgeom : C * datumVar (hn n) T ^ 2 ≤ 1 / 4 := by
      have hh := mul_le_mul_of_nonneg_left hd1 (mul_nonneg hC.le hd0)
      nlinarith only [hh, hCd, hq16]
    have hscale : chargedScale e (hn n) T ≤ δa :=
      (mul_le_mul_of_nonneg_left (hd n).2 hcoef).trans (he.trans (min_le_left _ _))
    exact setting_of_smooth_bounds hT (hs n).1 (hs n).2
      (hap T e (Sn n) (hn n) hT (hs n).1 (hs n).2
        ((hd n).1.trans (min_le_left _ _)) hscale) hgeom
      (hCd.trans (by linarith only [hq])) (hd n).2 hM
  have hσ : sigma e M T = (|e| * (T / 2) * M) ^ 2 := by
    simp only [sigma, mul_pow, sq_abs]
    ring
  have hscale0 : 0 ≤ |e| * (T / 2) * M := mul_nonneg hcoef (zero_le_one.trans hM)
  have hscaleq := he.trans (min_le_right _ _)
  have hsmall : q ^ 2 + sigma e M T ≤ η := by
    rw [hσ]
    nlinarith only [hq16, hqη, hscale0, hscaleq,
      mul_nonneg (sub_nonneg.mpr hscaleq) (add_nonneg hq.le hscale0),
      mul_nonneg hq.le (sub_nonneg.mpr hq16)]
  exact (hui T e q M Sn hn h hsetting hac hlim hsmall).2.2

end EmcsfAcExtension.Local
