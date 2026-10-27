module

public import EmcsfAcExtension.Local.Defs.Limit
public import EmcsfAcExtension.Local.Defs.Envelope
import EmcsfAcExtension.Local.Limit.UIEnvelopeReal
import EmcsfAcExtension.Local.Limit.Construct2Tail
import EmcsfAcExtension.Local.Limit.Tags
import EmcsfAcExtension.Local.Apriori.Bootstrap
import EmcsfAcExtension.Local.Calculus.Partials
import EmcsfAcExtension.Infra.W11.Approximation

/-! # Unconditional envelopes of the actual limiting derivatives

Every constructed limit inherits the universal smooth envelope coefficient
at the variation of its limiting datum. The source provenance supplies the
actual frozen derivative identification; the existence companion constructs
that provenance with both producers discharged. No estimate or strong-limit
record is an additional hypothesis of either export.
-/

public section

open Set Filter MeasureTheory Complex
open scoped Topology ENNReal

namespace EmcsfAcExtension.Local

/-- [node restart-sec-independent-null-construction#limit-renormalized-envelope-bound]
Every fixed-label constructed limit admits nonnegative integrable envelopes
of its actual frozen `jOut,kIn`, charged_SF_new_version.tex:L6477–L6482, internal project record
(L.2).
The positive thresholds and coefficient are universal, before time, coupling,
datum, limit and approximation choice; there is no derivative-supremum
dependence. The sole provenance premise is the source's constructed limit.
The approximation and its retained smooth bound are obtained internally. -/
theorem Null.limit_renormalized_envelope_bound :
    ∃ ε δ C : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < C ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ) (S : Fields), 0 < T →
        AbsolutelyContinuousOnInterval h 0 T → datumVar h T ≤ ε →
        chargedScale e h T ≤ δ → IsConstructedLimit e T h S →
        ∃ J K : ℝ → ℝ, Measurable J ∧ Measurable K ∧
          (∀ x, 0 ≤ J x) ∧ (∀ x, 0 ≤ K x) ∧
          IntegrableOn J (Icc 0 T) ∧ IntegrableOn K (Icc 0 T) ∧
          (∀ u ∈ Icc 0 T, ∀ᵐ v ∂volume.restrict (Icc u T), ‖jOut S u v‖ ≤ J v) ∧
          (∀ v ∈ Icc 0 T, ∀ᵐ u ∂volume.restrict (Icc 0 v), ‖kIn e S u v‖ ≤ K u) ∧
          (∫ v in Icc 0 T, J v) + (∫ u in Icc 0 T, K u) ≤ C * datumVar h T := by
  obtain ⟨ε, δ, C, hε, hδ, hC, hap⟩ := Null.smooth_apriori_box
  refine ⟨ε / 2, δ / 2, C, by positivity, by positivity, hC, ?_⟩
  intro T e h S hT hac hsmall hscale hconstructed
  obtain ⟨Sn, hn, hv, herr, hs, hlim⟩ := hconstructed.exists_classical_sequence
  have hacn n : AbsolutelyContinuousOnInterval (hn n) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hT.le]
    exact ((hs n).1.c1_a.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun v hv => ⟨le_rfl, hv.1, hv.2⟩)).congr
        (fun v hv => ((hs n).2.1 v hv).2.symm)
  have her : Tendsto (fun n => datumVar (hn n - h) T) atTop (𝓝 0) := by
    simpa only [datumVar, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp herr
  have hvar : Tendsto (fun n => datumVar (hn n) T) atTop (𝓝 (datumVar h T)) :=
    W11.tendsto_variation_of_sub (fun n => (hacn n).boundedVariationOn_Icc hT.le)
      (hac.boundedVariationOn_Icc hT.le) her
  have hsc : Tendsto (fun n => chargedScale e (hn n) T) atTop (𝓝 (chargedScale e h T)) := by
    unfold chargedScale datumM
    simpa only [hv] using
      ((tendsto_const_nhds.add (hvar.const_mul 10)).const_mul (|e| * (T / 2)))
  have hbound : ∀ᶠ n in atTop,
      (∫⁻ v in Icc 0 T, outEnv 0 (jC1 (triangle 0 T) (Sn n)) v) +
        (∫⁻ u in Icc 0 T, inEnv T (kC1 e (triangle 0 T) (Sn n)) u) ≤
          ENNReal.ofReal (C * datumVar (hn n) T) := by
    filter_upwards [(tendsto_order.1 hvar).2 ε (by linarith only [hsmall, hε]),
      (tendsto_order.1 hsc).2 δ (by linarith only [hscale, hδ])] with n hnε hnδ
    exact (hap T e (Sn n) (hn n) hT (hs n).1 (hs n).2 hnε.le hnδ.le).env
  exact Null.limit_renormalized_real_envelope_bound_of_strongLimit hC.le
    ENNReal.toReal_nonneg hT (fun n => (hs n).1) hlim hvar hbound

/-- [node restart-sec-independent-null-construction#limit-renormalized-envelope-bound]
Construct an actual frozen AC solution and its dominating real L¹ envelopes,
with exact restart data and constructed provenance, charged_SF_new_version.tex:L6350–L6482.
Existence and actual derivative identification come from the unconditional
full-triangle and comparison producers. All three positive constants are
universal, before time, coupling, AC datum and approximation derivatives. -/
theorem Null.constructed_limit_renormalized_envelope_bound :
    ∃ ε δ C : ℝ, 0 < ε ∧ 0 < δ ∧ 0 < C ∧
      ∀ (T e : ℝ) (h : ℝ → ℂ), 0 < T →
        AbsolutelyContinuousOnInterval h 0 T → datumVar h T ≤ ε →
        chargedScale e h T ≤ δ →
        ∃ S : Fields, IsSolution e S (triangle 0 T) ∧ IsRestartData S h T ∧
          IsConstructedLimit e T h S ∧
          ∃ J K : ℝ → ℝ, Measurable J ∧ Measurable K ∧
            (∀ x, 0 ≤ J x) ∧ (∀ x, 0 ≤ K x) ∧
            IntegrableOn J (Icc 0 T) ∧ IntegrableOn K (Icc 0 T) ∧
            (∀ u ∈ Icc 0 T, ∀ᵐ v ∂volume.restrict (Icc u T), ‖jOut S u v‖ ≤ J v) ∧
            (∀ v ∈ Icc 0 T, ∀ᵐ u ∂volume.restrict (Icc 0 v), ‖kIn e S u v‖ ≤ K u) ∧
            (∫ v in Icc 0 T, J v) + (∫ u in Icc 0 T, K u) ≤ C * datumVar h T := by
  obtain ⟨ε, δ, C, hε, hδ, hC, henv⟩ := Null.limit_renormalized_envelope_bound
  obtain ⟨εx, δx, _, hεx, hδx, _, hex⟩ := Null.ac_data_existence
  refine ⟨min ε εx, min δ δx, C, lt_min hε hεx, lt_min hδ hδx, hC, ?_⟩
  intro T e h hT hac hd he
  obtain ⟨S, hS, hr, hc, _⟩ := hex T e h hT hac
    (hd.trans (min_le_right _ _)) (he.trans (min_le_right _ _))
  exact ⟨S, hS, hr, hc, henv T e h S hT hac
    (hd.trans (min_le_left _ _)) (he.trans (min_le_left _ _)) hc⟩

end EmcsfAcExtension.Local
