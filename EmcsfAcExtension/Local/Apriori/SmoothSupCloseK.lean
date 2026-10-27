module

public import EmcsfAcExtension.Local.Apriori.SmoothSupOrderedIn
public import EmcsfAcExtension.Local.Apriori.SmoothSupCloseJ
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseFields
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseSourcePointwise
import EmcsfAcExtension.Local.Apriori.EnvelopeCloseFinal
import EmcsfAcExtension.Local.Calculus.AxisMatch
import EmcsfAcExtension.Local.Api.Finite
import EmcsfAcExtension.Local.Apriori.Charge
import EmcsfAcExtension.Local.Calculus.RenormalizedContinuity

/-! # Closing the incoming renormalized supremum

The outgoing transport has no real amplification. Its boundary value is
the actual matching axis value `k = j`; the outgoing envelope stays in L¹
until the finite incoming supremum has been absorbed.
-/

public section

open Set MeasureTheory Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

/-- The full outgoing forcing in the `k` equation is bounded by
`C ε ‖J‖₁ ‖K‖∞ + C e² M² T ε`. The universal constant is chosen before
all parameters and data, uniformly in all initial derivative norms. -/
theorem smooth_k_forcing_sup_aux :
    ∃ C : ℝ, 0 < C ∧ ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      AprioriSetting e T ε M S h → ε ≤ 1 / 8 → ∀ u ∈ Icc 0 T,
      (∫⁻ v in Icc u T,
        ‖S.lam u v * S.xi u v / S.r u v ^ 2 *
          (starRingEnd ℂ (curv S u v) + 2 * curv S u v) + emSourceK e S u v‖ₑ) ≤
        ENNReal.ofReal (C * ε) *
          (∫⁻ a in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) a) *
          (⨆ q ∈ triangle 0 T, ‖kC1 e (triangle 0 T) S q.1 q.2‖ₑ) +
        ENNReal.ofReal (C * e ^ 2 * M ^ 2 * T * ε) := by
  obtain ⟨B, hB, hb⟩ := characteristic_forcing_scalar_majorants
  refine ⟨3072 + B, by positivity, ?_⟩
  intro e T ε M S h hset hε u hu
  have hε0 := hset.eps_nonneg
  have hp : (1 : ℝ) / 2 ≤ 1 - 16 * ε ^ 2 := by nlinarith only [hε0, hε]
  let F := fun v => ‖S.lam u v * S.xi u v / S.r u v ^ 2 *
    curvScalarIn e (triangle 0 T) S u v‖ₑ
  have hpoint (v : ℝ) (hv : v ∈ Icc u T) :
      ‖S.lam u v * S.xi u v / S.r u v ^ 2 *
        (starRingEnd ℂ (curv S u v) + 2 * curv S u v) + emSourceK e S u v‖ₑ ≤
        3 * F v + ENNReal.ofReal (B * e ^ 2 * M ^ 2 * ε) := by
    have hpuv : (u, v) ∈ triangle 0 T := ⟨hu.1, hv.1, hv.2⟩
    have hs := (hb e T ε M S h hset (hε.trans (by norm_num)) u v hpuv).2
    have hbox := hset.box (u, v) hpuv
    have hgeom : (-S.nu u v) * S.lam u v ≤ 1 :=
      (mul_le_mul hbox.2.2.2.1 hbox.2.1
        (hset.c1.lam_pos _ hpuv).le (by norm_num)).trans_eq (one_mul _)
    have he := mul_le_mul_of_nonneg_left hgeom
      (show 0 ≤ B * e ^ 2 * M ^ 2 * ε by positivity)
    have hs' : ‖S.lam u v * S.xi u v / S.r u v ^ 2 *
        (starRingEnd ℂ (curv S u v) + 2 * curv S u v) + emSourceK e S u v‖ ≤
        3 * ‖S.lam u v * S.xi u v / S.r u v ^ 2 *
          curvScalarIn e (triangle 0 T) S u v‖ + B * e ^ 2 * M ^ 2 * ε := by
      nlinarith only [hs, he]
    have hh := ENNReal.ofReal_le_ofReal hs'
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)] at hh
    simpa only [F, ENNReal.ofReal_ofNat, ofReal_norm] using hh
  have hF := smooth_incoming_curvature_sup_aux hset (by norm_num : (0 : ℝ) < 1 / 2) hp hu
  change (∫⁻ v in Icc u T, F v) ≤ _ at hF
  calc
    _ ≤ ∫⁻ v in Icc u T, 3 * F v + ENNReal.ofReal (B * e ^ 2 * M ^ 2 * ε) :=
      setLIntegral_mono' measurableSet_Icc hpoint
    _ ≤ 3 * (∫⁻ v in Icc u T, F v) +
        ENNReal.ofReal (B * e ^ 2 * M ^ 2 * T * ε) := by
      rw [lintegral_add_right _ measurable_const,
        lintegral_const_mul' _ _ (by finiteness), setLIntegral_const, Real.volume_Icc]
      apply add_le_add le_rfl
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ B * e ^ 2 * M ^ 2 * ε)]
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left (sub_le_self T hu.1)
        (show 0 ≤ B * e ^ 2 * M ^ 2 * ε by positivity)
      nlinarith only [hh]
    _ ≤ 3 * (ENNReal.ofReal (1024 * ε / (1 + 1 / 2)) *
          (∫⁻ a in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) a) *
          (⨆ q ∈ triangle 0 T, ‖kC1 e (triangle 0 T) S q.1 q.2‖ₑ)) +
        ENNReal.ofReal (B * e ^ 2 * M ^ 2 * T * ε) :=
      add_le_add (mul_le_mul' le_rfl hF) le_rfl
    _ ≤ _ := by
      have hc : (3 : ℝ≥0∞) * ENNReal.ofReal (1024 * ε / (1 + 1 / 2)) ≤
          ENNReal.ofReal ((3072 + B) * ε) := by
        rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        apply ENNReal.ofReal_le_ofReal
        have hh := div_le_self (show 0 ≤ 1024 * ε by positivity)
          (by norm_num : (1 : ℝ) ≤ 1 + 1 / 2)
        nlinarith only [hh, mul_nonneg hB.le hε0]
      rw [← mul_assoc, ← mul_assoc]
      apply add_le_add (mul_le_mul' (mul_le_mul' hc le_rfl) le_rfl)
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_right
        (show B ≤ 3072 + B by linarith)
        (show 0 ≤ e ^ 2 * M ^ 2 * T * ε by have := hset.pos; positivity)
      simpa only [mul_assoc] using hh

private theorem finite_sup {e T : ℝ} {S : Fields}
    (hT : 0 < T) (hS : IsC1Solution e S (triangle 0 T)) :
    (⨆ q ∈ triangle 0 T, ‖jC1 (triangle 0 T) S q.1 q.2‖ₑ) ≠ ⊤ ∧
      (⨆ q ∈ triangle 0 T, ‖kC1 e (triangle 0 T) S q.1 q.2‖ₑ) ≠ ⊤ := by
  constructor
  · obtain ⟨C, hC⟩ := (isCompact_triangle 0 T).bddAbove_image
      (continuousOn_jC1_aux hT hS).norm
    apply ne_top_of_le_ne_top (show ENNReal.ofReal C ≠ ⊤ from ENNReal.ofReal_ne_top)
    apply iSup₂_le
    intro q hq
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC (mem_image_of_mem _ hq))
  · obtain ⟨C, hC⟩ := (isCompact_triangle 0 T).bddAbove_image
      (continuousOn_kC1_aux hT hS).norm
    apply ne_top_of_le_ne_top (show ENNReal.ofReal C ≠ ⊤ from ENNReal.ofReal_ne_top)
    apply iSup₂_le
    intro q hq
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC (mem_image_of_mem _ hq))

/-- [node restart-sec-independent-null-construction#k-sup-closure]
The reflected outgoing calculation bounds the incoming supremum by twice
the outgoing supremum plus `C e² M² T ε`. All three positive constants
precede the data and are independent of initial derivative norms and apex.
The matching boundary datum is the actual axis value, including endpoints. -/
theorem Null.k_sup_closure : ∃ ε₀ δ₀ C : ℝ, 0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
      AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
      (⨆ q ∈ triangle 0 T, ‖kC1 e (triangle 0 T) S q.1 q.2‖ₑ) ≤
        2 * (⨆ q ∈ triangle 0 T, ‖jC1 (triangle 0 T) S q.1 q.2‖ₑ) +
        ENNReal.ofReal (C * e ^ 2 * M ^ 2 * T * ε) := by
  obtain ⟨D, hD, hforcing⟩ := smooth_k_forcing_sup_aux
  obtain ⟨εb, δb, hεb, hδb, henvelopes⟩ := closed_envelopes_sharp
  let ε₀ := min εb (min (1 / 8) (1 / (100 * D)))
  refine ⟨ε₀, δb, 2 * D,
    lt_min hεb (lt_min (by norm_num) (by positivity)), hδb, by positivity, ?_⟩
  intro e T ε M S h hset hε hδ
  have hε0 := hset.eps_nonneg
  have hεb' : ε ≤ εb := hε.trans (min_le_left _ _)
  have hε8 : ε ≤ 1 / 8 := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεD : ε ≤ 1 / (100 * D) :=
    hε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hDε : D * ε ≤ 1 / 100 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 100 * D)).mp hεD
    nlinarith only [hh]
  let J := ⨆ q ∈ triangle 0 T, ‖jC1 (triangle 0 T) S q.1 q.2‖ₑ
  let K := ⨆ q ∈ triangle 0 T, ‖kC1 e (triangle 0 T) S q.1 q.2‖ₑ
  let L := ∫⁻ a in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) S) a
  have hfinite := finite_sup hset.pos hset.c1
  have hJ : J ≠ ⊤ := hfinite.1
  have hK : K ≠ ⊤ := hfinite.2
  have hLbound : L ≤ ENNReal.ofReal (9 / 8 * ε) :=
    (henvelopes e T ε M S h hset hεb' hδ).1
  have hL : L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hLbound
  have hLr : L.toReal ≤ 9 / 8 * ε := by
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 9 / 8 * ε)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hLbound
  have hfeedback : D * ε * L.toReal ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hLr (mul_nonneg hD.le hε0)
    have hh' := mul_le_mul_of_nonneg_right hDε hε0
    nlinarith only [hh, hh', hε8, hε0]
  have hsup : K ≤ J + ENNReal.ofReal (D * ε) * L * K +
      ENNReal.ofReal (D * e ^ 2 * M ^ 2 * T * ε) := by
    apply iSup₂_le
    intro q hq
    have ht := k_characteristic_enorm_bound hset hq.1 hq.2.1 hq.2.2
    have hf := hforcing e T ε M S h hset hε8 q.1 ⟨hq.1, hq.2.1.trans hq.2.2⟩
    have ha := (Null.smooth_axis_matching hset.pos hset.c1 hset.data.2
      ⟨hq.1, hq.2.1.trans hq.2.2⟩)
    have haxis : ‖kC1 e (triangle 0 T) S q.1 q.1‖ₑ ≤ J := by
      rw [ha.1]
      exact le_iSup₂_of_le (q.1, q.1) ⟨hq.1, le_rfl, hq.2.1.trans hq.2.2⟩ le_rfl
    exact ht.trans ((add_le_add haxis hf).trans_eq (add_assoc _ _ _).symm)
  have hr := ENNReal.toReal_mono (show J + ENNReal.ofReal (D * ε) * L * K +
      ENNReal.ofReal (D * e ^ 2 * M ^ 2 * T * ε) ≠ ⊤ by finiteness) hsup
  rw [ENNReal.toReal_add (by finiteness) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add hJ (by finiteness), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ D * ε),
    ENNReal.toReal_ofReal (by have := hset.pos; positivity :
      0 ≤ D * e ^ 2 * M ^ 2 * T * ε)] at hr
  have hfb := mul_le_mul_of_nonneg_right hfeedback (show 0 ≤ K.toReal from
    ENNReal.toReal_nonneg)
  have hr' : K.toReal ≤ 2 * J.toReal + (2 * D) * e ^ 2 * M ^ 2 * T * ε := by
    nlinarith only [hr, hfb]
  have hh := ENNReal.ofReal_le_ofReal hr'
  rwa [ENNReal.ofReal_toReal hK, ENNReal.ofReal_add (by positivity :
    0 ≤ 2 * J.toReal) (by have := hset.pos; positivity :
    0 ≤ (2 * D) * e ^ 2 * M ^ 2 * T * ε),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_toReal hJ, ENNReal.ofReal_ofNat] at hh

end EmcsfAcExtension.Local
