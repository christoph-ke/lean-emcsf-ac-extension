module

public import EmcsfAcExtension.Local.Defs.Envelope

/-! # Continuous characteristic envelopes

Continuity is only required on the compact triangle. Envelopes and their label
integrals are finite there, so downstream `.toReal` operations have no junk value.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace EmcsfAcExtension.Local

variable {E : Type*} [NormedAddCommGroup E] {f : ℝ → ℝ → E} {a b : ℝ}

/-- Reversing and exchanging the labels turns the incoming into the outgoing envelope. -/
theorem inEnv_eq_outEnv_neg (b : ℝ) (f : ℝ → ℝ → E) (u : ℝ) :
    inEnv b f u = outEnv (-b) (fun x y => f (-y) (-x)) (-u) := by
  apply le_antisymm
  · apply iSup₂_le
    intro v hv
    have hm : -v ∈ Icc (-b) (-u) := ⟨neg_le_neg hv.2, neg_le_neg hv.1⟩
    simpa only [neg_neg] using
      (enorm_le_normEnvelope (fun x y => f (-y) (-x)) hm)
  · change (⨆ x ∈ Icc (-b) (-u), ‖f (-(-u)) (-x)‖ₑ) ≤
      ⨆ v ∈ Icc u b, ‖f u v‖ₑ
    apply iSup₂_le
    intro x hx
    have hm : -x ∈ Icc u b := by constructor <;> linarith [hx.1, hx.2]
    simpa only [neg_neg] using
      (le_iSup₂_of_le (-x) hm (le_rfl : ‖f u (-x)‖ₑ ≤ ‖f u (-x)‖ₑ))

/-- A continuous field has a continuous outgoing envelope on the controlled labels. -/
theorem continuousOn_outEnv (hf : ContinuousOn (Function.uncurry f) (triangle a b)) :
    ContinuousOn (outEnv a f) (Icc a b) := continuousOn_normEnvelope hf

/-- A continuous field has a continuous incoming envelope on the controlled labels. -/
theorem continuousOn_inEnv (hf : ContinuousOn (Function.uncurry f) (triangle a b)) :
    ContinuousOn (inEnv b f) (Icc a b) := by
  have hr : ContinuousOn (Function.uncurry (fun x y => f (-y) (-x)))
      (triangle (-b) (-a)) := by
    apply hf.comp (continuous_snd.neg.prodMk continuous_fst.neg).continuousOn
    rintro ⟨x, y⟩ ⟨hx, hxy, hy⟩
    change a ≤ -y ∧ -y ≤ -x ∧ -x ≤ b
    constructor
    · linarith
    constructor <;> linarith
  have hc := (continuousOn_outEnv hr).comp continuous_neg.continuousOn
    (show MapsTo (fun x : ℝ => -x) (Icc a b) (Icc (-b) (-a)) from
      fun x hx => ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩)
  simpa only [Function.comp_def, ← inEnv_eq_outEnv_neg] using hc

/-- The outgoing envelope is measurable for the restricted label measure. -/
theorem aemeasurable_outEnv (hf : ContinuousOn (Function.uncurry f) (triangle a b)) :
    AEMeasurable (outEnv a f) (volume.restrict (Icc a b)) :=
  (continuousOn_outEnv hf).aemeasurable measurableSet_Icc

/-- The incoming envelope is measurable for the restricted label measure. -/
theorem aemeasurable_inEnv (hf : ContinuousOn (Function.uncurry f) (triangle a b)) :
    AEMeasurable (inEnv b f) (volume.restrict (Icc a b)) :=
  (continuousOn_inEnv hf).aemeasurable measurableSet_Icc

/-- The outgoing envelope, extended by zero off the controlled labels, is measurable. -/
theorem measurable_indicator_outEnv
    (hf : ContinuousOn (Function.uncurry f) (triangle a b)) :
    Measurable ((Icc a b).indicator (outEnv a f)) := measurable_indicator_normEnvelope hf

/-- The incoming envelope, extended by zero off the controlled labels, is measurable. -/
theorem measurable_indicator_inEnv
    (hf : ContinuousOn (Function.uncurry f) (triangle a b)) :
    Measurable ((Icc a b).indicator (inEnv b f)) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact (continuousOn_inEnv hf).measurable_piecewise
    (continuousOn_const (c := (0 : ℝ≥0∞))) measurableSet_Icc

/-- The outgoing envelope is finite on each controlled label. -/
theorem outEnv_ne_top_of_continuousOn
    (hf : ContinuousOn (Function.uncurry f) (triangle a b)) {v : ℝ} (hv : v ∈ Icc a b) :
    outEnv a f v ≠ ⊤ := normEnvelope_ne_top hf hv

/-- The incoming envelope is finite on each controlled label. -/
theorem inEnv_ne_top_of_continuousOn
    (hf : ContinuousOn (Function.uncurry f) (triangle a b)) {u : ℝ} (hu : u ∈ Icc a b) :
    inEnv b f u ≠ ⊤ := by
  obtain ⟨C, hC⟩ := (isCompact_triangle a b).bddAbove_image hf.norm
  apply ne_top_of_le_ne_top (show ENNReal.ofReal C ≠ ⊤ from ENNReal.ofReal_ne_top)
  apply iSup₂_le
  intro v hv
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hC (mem_image_of_mem _
    (show (u, v) ∈ triangle a b from ⟨hu.1, hv.1, hv.2⟩)))

/-- The outgoing envelope has a finite label integral for a continuous field. -/
theorem outEnv_lintegral_ne_top_of_continuousOn
    (hf : ContinuousOn (Function.uncurry f) (triangle a b)) :
    (∫⁻ v in Icc a b, outEnv a f v) ≠ ⊤ := by
  obtain ⟨C, hC⟩ := (isCompact_triangle a b).bddAbove_image hf.norm
  have hb : (∫⁻ v in Icc a b, outEnv a f v) ≤
      ∫⁻ _ in Icc a b, ENNReal.ofReal C := by
    apply setLIntegral_mono' measurableSet_Icc
    intro v hv
    apply iSup₂_le
    intro u hu
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC (mem_image_of_mem _
      (show (u, v) ∈ triangle a b from ⟨hu.1, hu.2, hv.2⟩)))
  apply ne_top_of_le_ne_top _ hb
  simp only [setLIntegral_const, Real.volume_Icc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- The incoming envelope has a finite label integral for a continuous field. -/
theorem inEnv_lintegral_ne_top_of_continuousOn
    (hf : ContinuousOn (Function.uncurry f) (triangle a b)) :
    (∫⁻ u in Icc a b, inEnv b f u) ≠ ⊤ := by
  obtain ⟨C, hC⟩ := (isCompact_triangle a b).bddAbove_image hf.norm
  have hb : (∫⁻ u in Icc a b, inEnv b f u) ≤
      ∫⁻ _ in Icc a b, ENNReal.ofReal C := by
    apply setLIntegral_mono' measurableSet_Icc
    intro u hu
    apply iSup₂_le
    intro v hv
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hC (mem_image_of_mem _
      (show (u, v) ∈ triangle a b from ⟨hu.1, hv.1, hv.2⟩)))
  apply ne_top_of_le_ne_top _ hb
  simp only [setLIntegral_const, Real.volume_Icc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- The uniform distance of two continuous fields on a closed triangle is finite. -/
theorem supDist_ne_top_of_continuousOn {T : ℝ} {g : ℝ → ℝ → E}
    (hf : ContinuousOn (Function.uncurry f) (triangle 0 T))
    (hg : ContinuousOn (Function.uncurry g) (triangle 0 T)) : supDist T f g ≠ ⊤ := by
  obtain ⟨C, hC⟩ := (isCompact_triangle 0 T).bddAbove_image (hf.sub hg).norm
  apply ne_top_of_le_ne_top (show ENNReal.ofReal C ≠ ⊤ from ENNReal.ofReal_ne_top)
  apply iSup₂_le
  intro p hp
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hC (mem_image_of_mem _ hp))

end EmcsfAcExtension.Local
