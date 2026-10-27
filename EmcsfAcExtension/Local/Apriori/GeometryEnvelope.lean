module

public import EmcsfAcExtension.Local.Defs.Setting
public import EmcsfAcExtension.Local.Defs.Renormalized
import EmcsfAcExtension.Local.Apriori.GeometryEnvelopeRegular
import EmcsfAcExtension.Local.Apriori.GeometryEnvelopeTransport
import EmcsfAcExtension.Local.Apriori.GeometryEnvelopeSource
import EmcsfAcExtension.Local.Apriori.GeometryEnvelopeInitial
import EmcsfAcExtension.Local.Api.Finite

/-! # Closed geometric derivative envelopes

The outgoing derivative starts at the initial cone; the incoming derivative
starts at its matching axis value. The common absolute source area is
integrated before taking either label envelope
(`charged_SF_new_version.tex:L4888–L4894`, approved internal project record (34)–(36)).
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- The outgoing geometric envelope is bounded by the initial geometric
budget and the incoming order of the absolute source area. The exact
coefficients are one, uniformly in all data and derivative norms. -/
theorem outgoing_geometric_envelope_with_source {e T ε M : ℝ}
    {S : Fields} {h : ℝ → ℂ} (hset : AprioriSetting e T ε M S h) :
    (∫⁻ v in Icc 0 T, outEnv 0 (geomL (triangle 0 T) S) v) ≤
      (∫⁻ v in Icc 0 T, ‖geomL (triangle 0 T) S 0 v‖ₑ) +
        ∫⁻ v in Icc 0 T, ∫⁻ u in Icc 0 v, ‖geomSource S u v‖ₑ := by
  have ci : ContinuousOn (fun v => geomL (triangle 0 T) S 0 v) (Icc 0 T) :=
    (continuousOn_geomL hset.pos hset.c1).comp (f := fun v : ℝ => (0, v))
      (continuous_const.prodMk continuous_id).continuousOn
      (fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  calc
    _ ≤ ∫⁻ v in Icc 0 T, ‖geomL (triangle 0 T) S 0 v‖ₑ +
        ∫⁻ u in Icc 0 v, ‖geomSource S u v‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro v hv
      apply iSup₂_le
      intro u hu
      exact geomL_characteristic_bound hset hu.1 hu.2 hv.2
    _ = _ := lintegral_add_left' (ci.enorm.aemeasurable measurableSet_Icc) _

/-- The incoming geometric envelope is bounded by the outgoing geometric
envelope and the outgoing order of the source area. The coefficient one
is universal; matching on the axis supplies the boundary budget. -/
theorem incoming_geometric_envelope_with_source {e T ε M : ℝ}
    {S : Fields} {h : ℝ → ℂ} (hset : AprioriSetting e T ε M S h) :
    (∫⁻ u in Icc 0 T, inEnv T (geomN (triangle 0 T) S) u) ≤
      (∫⁻ u in Icc 0 T, outEnv 0 (geomL (triangle 0 T) S) u) +
        ∫⁻ u in Icc 0 T, ∫⁻ v in Icc u T, ‖geomSource S u v‖ₑ := by
  calc
    _ ≤ ∫⁻ u in Icc 0 T, outEnv 0 (geomL (triangle 0 T) S) u +
        ∫⁻ v in Icc u T, ‖geomSource S u v‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro u hu
      apply iSup₂_le
      intro v hv
      have hdiag : ‖geomL (triangle 0 T) S u u‖ₑ ≤ outEnv 0 (geomL (triangle 0 T) S) u :=
        le_iSup₂_of_le u (show u ∈ Icc 0 u from ⟨hu.1, le_rfl⟩) le_rfl
      exact (geomN_characteristic_bound hset hu.1 hv.1 hv.2).trans
        (add_le_add hdiag le_rfl)
    _ = _ := lintegral_add_left'
      (aemeasurable_outEnv (continuousOn_geomL hset.pos hset.c1)) _

/-- [node restart-sec-independent-area#outgoing-geometric-envelope]
The integrated outgoing label envelope of the geometric derivative is
at most `C ε²`. The positive thresholds and `C` precede every datum,
depend only on the fixed box, and are uniform in higher derivatives. -/
theorem outgoing_geometric_envelope : ∃ ε₀ δ₀ C : ℝ,
    0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
      (∫⁻ v in Icc 0 T, outEnv 0 (geomL (triangle 0 T) S) v) ≤
        ENNReal.ofReal (C * ε ^ 2) := by
  obtain ⟨ε₀, δ₀, Cs, hε₀, hδ₀, hCs, hsource⟩ := geometric_source_area
  obtain ⟨Ci, hCi, hinitial⟩ := initial_geometric_derivative_budget
  refine ⟨ε₀, δ₀, Ci + Cs, hε₀, hδ₀, add_pos hCi hCs, ?_⟩
  intro e T ε M S h hset hε hδ
  apply (outgoing_geometric_envelope_with_source hset).trans
  have hb := add_le_add (hinitial e T ε M S h hset).2
    (hsource e T ε M S h hset hε hδ).2
  apply hb.trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- [node restart-sec-independent-area#incoming-geometric-envelope]
The integrated incoming label envelope of the geometric derivative is
at most `C ε²`. The thresholds and `C` are positive, precede all data,
and depend only on the fixed box, uniformly in higher derivatives. -/
theorem incoming_geometric_envelope : ∃ ε₀ δ₀ C : ℝ,
    0 < ε₀ ∧ 0 < δ₀ ∧ 0 < C ∧
    ∀ (e T ε M : ℝ) (S : Fields) (h : ℝ → ℂ),
    AprioriSetting e T ε M S h → ε ≤ ε₀ → |e| * (T / 2) * M ≤ δ₀ →
      (∫⁻ u in Icc 0 T, inEnv T (geomN (triangle 0 T) S) u) ≤
        ENNReal.ofReal (C * ε ^ 2) := by
  obtain ⟨ε₁, δ₁, Co, hε₁, hδ₁, hCo, hout⟩ := outgoing_geometric_envelope
  obtain ⟨ε₂, δ₂, Cs, hε₂, hδ₂, hCs, hsource⟩ := geometric_source_area
  refine ⟨min ε₁ ε₂, min δ₁ δ₂, Co + Cs, lt_min hε₁ hε₂, lt_min hδ₁ hδ₂,
    add_pos hCo hCs, ?_⟩
  intro e T ε M S h hset hε hδ
  apply (incoming_geometric_envelope_with_source hset).trans
  have hb := add_le_add (hout e T ε M S h hset
    (hε.trans (min_le_left _ _)) (hδ.trans (min_le_left _ _)))
    (hsource e T ε M S h hset
      (hε.trans (min_le_right _ _)) (hδ.trans (min_le_right _ _))).1
  apply hb.trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end EmcsfAcExtension.Local
