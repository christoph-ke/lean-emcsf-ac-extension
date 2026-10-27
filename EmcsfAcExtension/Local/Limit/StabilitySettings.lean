module

public import EmcsfAcExtension.Local.Limit.Construct2Settings
public import EmcsfAcExtension.Local.Limit.Construct2Tail
import EmcsfAcExtension.Local.Limit.Construct2Cauchy
import EmcsfAcExtension.Local.Apriori.Bootstrap
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.W11.Approximation

/-! # A common classical comparison setting for two constructed witnesses

The provenance predicate already supplies the approximants. A single common
tail and universal margins put both witnesses in the same fixed box, with
common size twice the maximum of the two original datum sizes.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

private theorem datum_variation_finite {e T : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hT : 0 < T) (hS : IsC1Solution e S (triangle 0 T)) (hd : IsRestartData S h T) :
    eVariationOn h (Icc 0 T) ≠ ⊤ := by
  have ca : ContDiffOn ℝ 1 (S.a 0) (Icc 0 T) :=
    hS.c1_a.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  have ch : ContDiffOn ℝ 1 h (Icc 0 T) :=
    ca.congr (fun v hv => (hd.1 v hv).2.symm)
  have hac : AbsolutelyContinuousOnInterval h 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hT.le] using ch
  exact hac.boundedVariationOn_Icc hT.le

private theorem datum_size_pos (h : ℝ → ℂ) (T : ℝ) : 0 < datumM h T := by
  unfold datumM
  have hv : 0 ≤ datumVar h T := ENNReal.toReal_nonneg
  have hn := norm_nonneg (h 0)
  linarith only [hv, hn]

/-- Select common comparison tails from two existing constructed limits.
The positive thresholds and comparison parameter `q` precede time, coupling,
data, configurations, and their witnesses; they depend only on the requested
fixed threshold `η` and the universal a priori constants. The common `M` is
an ordinary comparison size parameter, explicitly `2 * max (datumM h₁ T)
(datumM h₂ T)`, rather than a new estimate constant. Both individual
approximation data sequences retain their representative W¹¹ Cauchy control. -/
theorem comparison_tails_with_cauchy_of_constructed_limits (η : ℝ) (hη : 0 < η) :
    ∃ ε δ q : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < q ∧
      ∀ (T e : ℝ) (h₁ h₂ : ℝ → ℂ) (S₁ S₂ : Fields), 0 < T →
        AbsolutelyContinuousOnInterval h₁ 0 T → datumVar h₁ T ≤ ε → chargedScale e h₁ T ≤ δ →
        AbsolutelyContinuousOnInterval h₂ 0 T → datumVar h₂ T ≤ ε → chargedScale e h₂ T ≤ δ →
        IsConstructedLimit e T h₁ S₁ → IsConstructedLimit e T h₂ S₂ →
        ∃ (Sn₁ Sn₂ : ℕ → Fields) (hn₁ hn₂ : ℕ → ℝ → ℂ) (M : ℝ),
          (∀ n, StabSetting e T q M 1 (Sn₁ n) (hn₁ n)) ∧
          (∀ n, StabSetting e T q M 1 (Sn₂ n) (hn₂ n)) ∧
          StrongLimit e T Sn₁ S₁ ∧ StrongLimit e T Sn₂ S₂ ∧
          Tendsto (fun n => dataDist (hn₁ n) (hn₂ n) T) atTop (𝓝 (dataDist h₁ h₂ T)) ∧
          q ^ 2 + sigma e M T ≤ η ∧ M = 2 * max (datumM h₁ T) (datumM h₂ T) ∧
          (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, dataDist (hn₁ n) (hn₁ m) T < ρ) ∧
          (∀ ρ > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N, dataDist (hn₂ n) (hn₂ m) T < ρ) := by
  obtain ⟨εa, δa, C, hεa, hδa, hC, hap⟩ := Null.smooth_apriori_box
  let B := max 1 C
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hCB : C ≤ B := le_max_right _ _
  let q := min η (1 / 16)
  have hq : 0 < q := lt_min hη (by norm_num)
  have hqη : q ≤ η := min_le_left _ _
  have hq16 : q ≤ 1 / 16 := min_le_right _ _
  let ε := min (εa / 2) (min (1 / 2) (q / (4 * B)))
  let δ := min (δa / 2) (q / 4)
  have hε : 0 < ε := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hεa' : 2 * ε ≤ εa := by have := min_le_left (εa / 2) (min (1 / 2) (q / (4 * B))); linarith
  have hδa' : 2 * δ ≤ δa := by have := min_le_left (δa / 2) (q / 4); linarith
  have hεhalf : ε ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεq : ε ≤ q / (4 * B) := (min_le_right _ _).trans (min_le_right _ _)
  have hδq : δ ≤ q / 4 := min_le_right _ _
  refine ⟨ε, δ, q, hε, hδ, hq, ?_⟩
  intro T e h₁ h₂ S₁ S₂ hT hac₁ hd₁ he₁ hac₂ hd₂ he₂ hc₁ hc₂
  obtain ⟨Sn₁, hn₁, hv₁, herr₁, hs₁, hl₁⟩ := hc₁.exists_classical_sequence
  obtain ⟨Sn₂, hn₂, hv₂, herr₂, hs₂, hl₂⟩ := hc₂.exists_classical_sequence
  have hbv₁ n : BoundedVariationOn (hn₁ n) (Icc 0 T) :=
    datum_variation_finite hT (hs₁ n).1 (hs₁ n).2
  have hbv₂ n : BoundedVariationOn (hn₂ n) (Icc 0 T) :=
    datum_variation_finite hT (hs₂ n).1 (hs₂ n).2
  have her₁ : Tendsto (fun n => datumVar (hn₁ n - h₁) T) atTop (𝓝 0) := by
    simpa only [datumVar, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp herr₁
  have her₂ : Tendsto (fun n => datumVar (hn₂ n - h₂) T) atTop (𝓝 0) := by
    simpa only [datumVar, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp herr₂
  have hvlim₁ : Tendsto (fun n => datumVar (hn₁ n) T) atTop (𝓝 (datumVar h₁ T)) := by
    simpa only [datumVar] using W11.tendsto_variation_of_sub hbv₁ (hac₁.boundedVariationOn_Icc
        hT.le) her₁
  have hvlim₂ : Tendsto (fun n => datumVar (hn₂ n) T) atTop (𝓝 (datumVar h₂ T)) := by
    simpa only [datumVar] using W11.tendsto_variation_of_sub hbv₂ (hac₂.boundedVariationOn_Icc
        hT.le) her₂
  have hMlim₁ : Tendsto (fun n => datumM (hn₁ n) T) atTop (𝓝 (datumM h₁ T)) := by
    simpa only [datumM, hv₁] using tendsto_const_nhds.add (hvlim₁.const_mul 10)
  have hMlim₂ : Tendsto (fun n => datumM (hn₂ n) T) atTop (𝓝 (datumM h₂ T)) := by
    simpa only [datumM, hv₂] using tendsto_const_nhds.add (hvlim₂.const_mul 10)
  have helim₁ : Tendsto (fun n => chargedScale e (hn₁ n) T) atTop (𝓝 (chargedScale e h₁ T)) :=
    hMlim₁.const_mul (|e| * (T / 2))
  have helim₂ : Tendsto (fun n => chargedScale e (hn₂ n) T) atTop (𝓝 (chargedScale e h₂ T)) :=
    hMlim₂.const_mul (|e| * (T / 2))
  have hg₁ : ∀ᶠ n in atTop, datumVar (hn₁ n) T ≤ 2 * ε ∧
      chargedScale e (hn₁ n) T ≤ 2 * δ ∧ datumM (hn₁ n) T ≤ 2 * datumM h₁ T := by
    filter_upwards [(tendsto_order.1 hvlim₁).2 (2 * ε) (by linarith only [hd₁, hε]),
      (tendsto_order.1 helim₁).2 (2 * δ) (by linarith only [he₁, hδ]),
      (tendsto_order.1 hMlim₁).2 (2 * datumM h₁ T) (by have := datum_size_pos h₁ T; linarith)] with
          n hn he hM
    exact ⟨hn.le, he.le, hM.le⟩
  have hg₂ : ∀ᶠ n in atTop, datumVar (hn₂ n) T ≤ 2 * ε ∧
      chargedScale e (hn₂ n) T ≤ 2 * δ ∧ datumM (hn₂ n) T ≤ 2 * datumM h₂ T := by
    filter_upwards [(tendsto_order.1 hvlim₂).2 (2 * ε) (by linarith only [hd₂, hε]),
      (tendsto_order.1 helim₂).2 (2 * δ) (by linarith only [he₂, hδ]),
      (tendsto_order.1 hMlim₂).2 (2 * datumM h₂ T) (by have := datum_size_pos h₂ T; linarith)] with
          n hn he hM
    exact ⟨hn.le, he.le, hM.le⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hg₁.and hg₂)
  let M := 2 * max (datumM h₁ T) (datumM h₂ T)
  have hM1 : 1 ≤ M := by
    have hMi : 1 ≤ datumM h₁ T :=
        by unfold datumM; have hv : 0 ≤ datumVar h₁ T := ENNReal.toReal_nonneg; linarith
             [norm_nonneg (h₁ 0)]
    have hmax := le_max_left (datumM h₁ T) (datumM h₂ T)
    dsimp only [M]
    linarith only [hMi, hmax]
  have hmake (S : Fields) (k : ℝ → ℂ)
      (hS : IsC1Solution e S (triangle 0 T) ∧ IsRestartData S k T)
      (hk : datumVar k T ≤ 2 * ε) (he : chargedScale e k T ≤ 2 * δ) (hMk : datumM k T ≤ M) :
      StabSetting e T q M 1 S k := by
    have hv0 : 0 ≤ datumVar k T := ENNReal.toReal_nonneg
    have hv1 : datumVar k T ≤ 1 := by linarith only [hk, hεhalf]
    have hBε : B * (2 * ε) ≤ q / 2 := by
      have hh := (le_div_iff₀ (show 0 < 4 * B by positivity)).1 hεq
      nlinarith only [hh]
    have hCv : C * datumVar k T ≤ q / 2 :=
      (mul_le_mul_of_nonneg_right hCB hv0).trans
        ((mul_le_mul_of_nonneg_left hk hB.le).trans hBε)
    have hgeom : C * datumVar k T ^ 2 ≤ 1 / 4 := by
      have hh := mul_le_mul_of_nonneg_left hv1 (mul_nonneg hC.le hv0)
      nlinarith only [hh, hCv, hq16]
    exact setting_of_smooth_bounds hT hS.1 hS.2
      (hap T e S k hT hS.1 hS.2 (hk.trans hεa') (he.trans hδa')) hgeom
      (hCv.trans (by linarith only [hq])) hMk hM1
  have ht₁ n := hmake (Sn₁ (n + N)) (hn₁ (n + N)) (hs₁ _)
    (hN _ (Nat.le_add_left _ _)).1.1 (hN _ (Nat.le_add_left _ _)).1.2.1
    ((hN _ (Nat.le_add_left _ _)).1.2.2.trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num : (0 : ℝ) ≤ 2)))
  have ht₂ n := hmake (Sn₂ (n + N)) (hn₂ (n + N)) (hs₂ _)
    (hN _ (Nat.le_add_left _ _)).2.1 (hN _ (Nat.le_add_left _ _)).2.2.1
    ((hN _ (Nat.le_add_left _ _)).2.2.2.trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num : (0 : ℝ) ≤ 2)))
  have hdist := W11.tendsto_datum_distance_of_vertex_eq hbv₁ hbv₂
    (hac₁.boundedVariationOn_Icc hT.le) (hac₂.boundedVariationOn_Icc hT.le) hv₁ hv₂ her₁ her₂
  have hC₁ := data_dist_cauchy_of_stabSetting ht₁ hac₁ (fun n => hv₁ (n + N))
    (her₁.comp (tendsto_add_atTop_nat N))
  have hC₂ := data_dist_cauchy_of_stabSetting ht₂ hac₂ (fun n => hv₂ (n + N))
    (her₂.comp (tendsto_add_atTop_nat N))
  refine ⟨fun n => Sn₁ (n + N), fun n => Sn₂ (n + N), fun n => hn₁ (n + N),
    fun n => hn₂ (n + N), M, ht₁, ht₂, hl₁.reindex_of_tendsto (tendsto_add_atTop_nat N),
    hl₂.reindex_of_tendsto (tendsto_add_atTop_nat N), hdist.comp (tendsto_add_atTop_nat N), ?_, rfl,
        hC₁, hC₂⟩
  have hnum (s : ℝ) (hs0 : 0 ≤ s) (hsq : s ≤ q / 4) : q ^ 2 + 4 * s ^ 2 ≤ η := by
    nlinarith only [hs0, hsq, hq16, hqη,
      mul_nonneg (sub_nonneg.2 hsq) (add_nonneg (by linarith only [hq]) hs0),
      mul_nonneg hq.le (sub_nonneg.2 hq16)]
  have hσ (h : ℝ → ℂ) : sigma e (2 * datumM h T) T = 4 * chargedScale e h T ^ 2 := by
    simp only [sigma, chargedScale, mul_pow, sq_abs]
    ring
  rcases le_total (datumM h₁ T) (datumM h₂ T) with hle | hle
  · dsimp only [M]
    rw [max_eq_right hle, hσ]
    exact hnum _ (mul_nonneg (by positivity) (datum_size_pos h₂ T).le) (he₂.trans hδq)
  · dsimp only [M]
    rw [max_eq_left hle, hσ]
    exact hnum _ (mul_nonneg (by positivity) (datum_size_pos h₁ T).le) (he₁.trans hδq)

/-- Select common comparison tails from two existing constructed limits.
The positive thresholds and comparison parameter `q` precede time, coupling,
data, configurations, and their witnesses; they depend only on the requested
fixed threshold `η` and the universal a priori constants. The common `M` is
an ordinary comparison size parameter, explicitly `2 * max (datumM h₁ T)
(datumM h₂ T)`, rather than a new estimate constant. -/
theorem comparison_tails_with_size_of_constructed_limits (η : ℝ) (hη : 0 < η) :
    ∃ ε δ q : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < q ∧
      ∀ (T e : ℝ) (h₁ h₂ : ℝ → ℂ) (S₁ S₂ : Fields), 0 < T →
        AbsolutelyContinuousOnInterval h₁ 0 T → datumVar h₁ T ≤ ε → chargedScale e h₁ T ≤ δ →
        AbsolutelyContinuousOnInterval h₂ 0 T → datumVar h₂ T ≤ ε → chargedScale e h₂ T ≤ δ →
        IsConstructedLimit e T h₁ S₁ → IsConstructedLimit e T h₂ S₂ →
        ∃ (Sn₁ Sn₂ : ℕ → Fields) (hn₁ hn₂ : ℕ → ℝ → ℂ) (M : ℝ),
          (∀ n, StabSetting e T q M 1 (Sn₁ n) (hn₁ n)) ∧
          (∀ n, StabSetting e T q M 1 (Sn₂ n) (hn₂ n)) ∧
          StrongLimit e T Sn₁ S₁ ∧ StrongLimit e T Sn₂ S₂ ∧
          Tendsto (fun n => dataDist (hn₁ n) (hn₂ n) T) atTop (𝓝 (dataDist h₁ h₂ T)) ∧
          q ^ 2 + sigma e M T ≤ η ∧ M = 2 * max (datumM h₁ T) (datumM h₂ T) := by
  obtain ⟨ε, δ, q, hε, hδ, hq, ht⟩ := comparison_tails_with_cauchy_of_constructed_limits η hη
  refine ⟨ε, δ, q, hε, hδ, hq, ?_⟩
  intro T e h₁ h₂ S₁ S₂ hT hac₁ hd₁ he₁ hac₂ hd₂ he₂ hc₁ hc₂
  obtain ⟨Sn₁, Sn₂, hn₁, hn₂, M, hs₁, hs₂, hl₁, hl₂, hd, hsmall, hM, _, _⟩ :=
    ht T e h₁ h₂ S₁ S₂ hT hac₁ hd₁ he₁ hac₂ hd₂ he₂ hc₁ hc₂
  exact ⟨Sn₁, Sn₂, hn₁, hn₂, M, hs₁, hs₂, hl₁, hl₂, hd, hsmall, hM⟩

/-- Select common comparison tails from two existing constructed limits.
The positive thresholds and comparison parameter `q` precede time, coupling,
data, configurations, and their witnesses; they depend only on the requested
fixed threshold `η` and the universal a priori constants. The common `M` is
an ordinary comparison size parameter, explicitly `2 * max (datumM h₁ T)
(datumM h₂ T)`, rather than a new estimate constant. -/
theorem comparison_tails_of_constructed_limits (η : ℝ) (hη : 0 < η) :
    ∃ ε δ q : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < q ∧
      ∀ (T e : ℝ) (h₁ h₂ : ℝ → ℂ) (S₁ S₂ : Fields), 0 < T →
        AbsolutelyContinuousOnInterval h₁ 0 T → datumVar h₁ T ≤ ε → chargedScale e h₁ T ≤ δ →
        AbsolutelyContinuousOnInterval h₂ 0 T → datumVar h₂ T ≤ ε → chargedScale e h₂ T ≤ δ →
        IsConstructedLimit e T h₁ S₁ → IsConstructedLimit e T h₂ S₂ →
        ∃ (Sn₁ Sn₂ : ℕ → Fields) (hn₁ hn₂ : ℕ → ℝ → ℂ) (M : ℝ),
          (∀ n, StabSetting e T q M 1 (Sn₁ n) (hn₁ n)) ∧
          (∀ n, StabSetting e T q M 1 (Sn₂ n) (hn₂ n)) ∧
          StrongLimit e T Sn₁ S₁ ∧ StrongLimit e T Sn₂ S₂ ∧
          Tendsto (fun n => dataDist (hn₁ n) (hn₂ n) T) atTop (𝓝 (dataDist h₁ h₂ T)) ∧
          q ^ 2 + sigma e M T ≤ η := by
  obtain ⟨ε, δ, q, hε, hδ, hq, ht⟩ := comparison_tails_with_size_of_constructed_limits η hη
  refine ⟨ε, δ, q, hε, hδ, hq, ?_⟩
  intro T e h₁ h₂ S₁ S₂ hT hac₁ hd₁ he₁ hac₂ hd₂ he₂ hc₁ hc₂
  obtain ⟨Sn₁, Sn₂, hn₁, hn₂, M, hs₁, hs₂, hl₁, hl₂, hd, hsmall, _⟩ :=
    ht T e h₁ h₂ S₁ S₂ hT hac₁ hd₁ he₁ hac₂ hd₂ he₂ hc₁ hc₂
  exact ⟨Sn₁, Sn₂, hn₁, hn₂, M, hs₁, hs₂, hl₁, hl₂, hd, hsmall⟩

end EmcsfAcExtension.Local
