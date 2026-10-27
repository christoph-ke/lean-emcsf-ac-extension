/- Copyright (c) 2026. All rights reserved. -/

module

public import EmcsfAcExtension.Infra.Null.Parametric

/-! # Norm envelopes on incoming sections

The extended envelope is defined without boundedness assumptions. Its real
counterpart is used only with an explicit boundedness proof. Continuity and
measurability are asserted on `[a,b]`, the range controlled by the triangle.
-/

public section

open Set MeasureTheory Filter
open scoped ENNReal

namespace EmcsfAcExtension

variable {E : Type*} [NormedAddCommGroup E]

/-- Extended norm envelope over the closed incoming section. -/
@[expose] noncomputable def normEnvelope (f : ℝ → ℝ → E) (a v : ℝ) : ℝ≥0∞ :=
  ⨆ u ∈ Icc a v, ‖f u v‖ₑ

/-- Real supremum of section norms; estimates require boundedness of the image. -/
@[expose] noncomputable def normEnvelopeReal (f : ℝ → ℝ → E) (a v : ℝ) : ℝ :=
  sSup ((fun u => ‖f u v‖) '' Icc a v)

/-- The extended envelope dominates every value, without exceptional sets. -/
theorem enorm_le_normEnvelope (f : ℝ → ℝ → E) {a u v : ℝ} (hu : u ∈ Icc a v) :
    ‖f u v‖ₑ ≤ normEnvelope f a v := le_iSup₂_of_le u hu le_rfl

/-- A uniform bound on one section bounds its extended envelope. -/
theorem normEnvelope_le {f : ℝ → ℝ → E} {a v : ℝ} {C : ℝ≥0∞}
    (h : ∀ u ∈ Icc a v, ‖f u v‖ₑ ≤ C) : normEnvelope f a v ≤ C :=
  iSup₂_le h

/-- With a bounded section, the real envelope dominates each value. -/
theorem norm_le_normEnvelopeReal {f : ℝ → ℝ → E} {a u v : ℝ}
    (hb : BddAbove ((fun u => ‖f u v‖) '' Icc a v)) (hu : u ∈ Icc a v) :
    ‖f u v‖ ≤ normEnvelopeReal f a v := le_csSup hb (mem_image_of_mem _ hu)

/-- The real and extended envelopes agree on any nonempty bounded section. -/
theorem normEnvelope_eq_ofReal {f : ℝ → ℝ → E} {a v : ℝ} (hav : a ≤ v)
    (hb : BddAbove ((fun u => ‖f u v‖) '' Icc a v)) :
    normEnvelope f a v = ENNReal.ofReal (normEnvelopeReal f a v) := by
  apply le_antisymm
  · apply normEnvelope_le
    intro u hu
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (norm_le_normEnvelopeReal hb hu)
  · obtain ⟨C, hC⟩ := hb
    have hbound : normEnvelope f a v ≤ ENNReal.ofReal C := by
      apply normEnvelope_le
      intro u hu
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hC (mem_image_of_mem _ hu))
    have hfinite : normEnvelope f a v ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
    have hs : normEnvelopeReal f a v ≤ (normEnvelope f a v).toReal := by
      apply csSup_le ((nonempty_Icc.mpr hav).image _)
      rintro y ⟨u, hu, rfl⟩
      simpa only [toReal_enorm] using
        ENNReal.toReal_mono hfinite (enorm_le_normEnvelope f hu)
    rw [← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal hs

variable {f : ℝ → ℝ → E} {a b : ℝ}

/-- Every incoming section of a continuous field on the triangle has bounded norms. -/
theorem bddAbove_norm_incoming (hf : ContinuousOn (Function.uncurry f) (triangle a b))
    {v : ℝ} (hv : v ∈ Icc a b) : BddAbove ((fun u => ‖f u v‖) '' Icc a v) :=
  isCompact_Icc.bddAbove_image (continuousOn_incoming hf
    ((inSeg_subset_triangle_iff hv.1).mpr ⟨le_rfl, le_rfl, hv.2⟩)).norm

private theorem normEnvelopeReal_eq_fixed_sup
    {v : ℝ} (hv : v ∈ Icc a b) :
    normEnvelopeReal f a v = sSup ((fun u =>
      ‖Function.uncurry f (triangleProj a b (min u v, v))‖) '' Icc a b) := by
  unfold normEnvelopeReal
  congr 1
  apply Subset.antisymm
  · rintro y ⟨u, hu, rfl⟩
    refine ⟨u, ⟨hu.1, hu.2.trans hv.2⟩, ?_⟩
    dsimp only
    rw [min_eq_left hu.2, triangleProj_of_mem (p := (u, v)) ⟨hu.1, hu.2, hv.2⟩]
    rfl
  · rintro y ⟨u, hu, rfl⟩
    have hm : a ≤ min u v := le_min hu.1 hv.1
    refine ⟨min u v, ⟨hm, min_le_right _ _⟩, ?_⟩
    dsimp only
    rw [triangleProj_of_mem (p := (min u v, v)) ⟨hm, min_le_right _ _, hv.2⟩]
    rfl

/-- The bounded real envelope of a continuous field is continuous on `[a,b]`. -/
theorem continuousOn_normEnvelopeReal
    (hf : ContinuousOn (Function.uncurry f) (triangle a b)) :
    ContinuousOn (normEnvelopeReal f a) (Icc a b) := by
  by_cases hab : a ≤ b
  · have hc : Continuous (fun p : ℝ × ℝ =>
        ‖Function.uncurry f (triangleProj a b (min p.2 p.1, p.1))‖) :=
      ((hf.comp_continuous (continuous_triangleProj a b) (triangleProj_mem hab)).comp
        ((continuous_snd.min continuous_fst).prodMk continuous_fst)).norm
    have hsup := isCompact_Icc.continuous_sSup (K := Icc a b)
      (f := fun v u : ℝ => ‖Function.uncurry f (triangleProj a b (min u v, v))‖) hc
    apply hsup.continuousOn.congr
    intro v hv
    exact normEnvelopeReal_eq_fixed_sup hv
  · rw [Icc_eq_empty hab]
    exact continuousOn_empty _

/-- The extended envelope is continuous on `[a,b]` for continuous fields on the triangle. -/
theorem continuousOn_normEnvelope
    (hf : ContinuousOn (Function.uncurry f) (triangle a b)) :
    ContinuousOn (normEnvelope f a) (Icc a b) := by
  apply (ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_normEnvelopeReal hf)).congr
  intro v hv
  exact normEnvelope_eq_ofReal hv.1 (bddAbove_norm_incoming hf hv)

/-- The zero extension of the extended envelope is a globally measurable function. -/
theorem measurable_indicator_normEnvelope
    (hf : ContinuousOn (Function.uncurry f) (triangle a b)) :
    Measurable ((Icc a b).indicator (normEnvelope f a)) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact (continuousOn_normEnvelope hf).measurable_piecewise
    (continuousOn_const (c := (0 : ℝ≥0∞))) measurableSet_Icc

/-- The extended envelope is finite on each section of a continuous field. -/
theorem normEnvelope_ne_top
    (hf : ContinuousOn (Function.uncurry f) (triangle a b))
    {v : ℝ} (hv : v ∈ Icc a b) : normEnvelope f a v ≠ ⊤ := by
  rw [normEnvelope_eq_ofReal hv.1 (bddAbove_norm_incoming hf hv)]
  exact ENNReal.ofReal_ne_top

end EmcsfAcExtension
