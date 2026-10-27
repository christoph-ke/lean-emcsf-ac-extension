module

public import EmcsfAcExtension.Infra.Null.Envelope

/-!
# Stability of existing section envelopes

Auxiliary analysis A5 of internal project record. Measurability and
continuity are supplied by `Infra.Null.Envelope`; this module adds the
coefficient-one difference estimate and affine reparametrization of the fibers.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Mixed

/-- A5: the difference of the real envelopes is bounded by the envelope of the
difference. The exact coefficient one is uniform over all bounded nonempty fibers. -/
theorem abs_normEnvelopeReal_sub_le {E : Type*} [NormedAddCommGroup E]
    {f g : ℝ → ℝ → E} {a v : ℝ} (hav : a ≤ v)
    (hf : BddAbove ((fun u => ‖f u v‖) '' Icc a v))
    (hg : BddAbove ((fun u => ‖g u v‖) '' Icc a v))
    (hd : BddAbove ((fun u => ‖f u v - g u v‖) '' Icc a v)) :
    |normEnvelopeReal f a v - normEnvelopeReal g a v| ≤
      normEnvelopeReal (fun u v => f u v - g u v) a v := by
  have hs : (Icc a v).Nonempty := nonempty_Icc.mpr hav
  have h₁ : normEnvelopeReal f a v ≤
      normEnvelopeReal g a v + normEnvelopeReal (fun u v => f u v - g u v) a v := by
    apply csSup_le (hs.image _)
    rintro y ⟨u, hu, rfl⟩
    calc
      ‖f u v‖ ≤ ‖g u v‖ + ‖f u v - g u v‖ := by
        simpa only [add_sub_cancel] using norm_add_le (g u v) (f u v - g u v)
      _ ≤ _ := add_le_add (norm_le_normEnvelopeReal hg hu)
        (norm_le_normEnvelopeReal (f := fun u v => f u v - g u v) hd hu)
  have h₂ : normEnvelopeReal g a v ≤
      normEnvelopeReal f a v + normEnvelopeReal (fun u v => f u v - g u v) a v := by
    apply csSup_le (hs.image _)
    rintro y ⟨u, hu, rfl⟩
    calc
      ‖g u v‖ ≤ ‖f u v‖ + ‖f u v - g u v‖ := by
        have heq : f u v - (f u v - g u v) = g u v := by abel
        simpa only [heq] using norm_sub_le (f u v) (f u v - g u v)
      _ ≤ _ := add_le_add (norm_le_normEnvelopeReal hf hu)
        (norm_le_normEnvelopeReal (f := fun u v => f u v - g u v) hd hu)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- An affine parametrization of a closed fiber preserves its extended norm
supremum. The degenerate fiber is included; no continuity or boundedness is needed. -/
theorem iSup_enorm_affine_eq {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    (⨆ q : Icc (0 : ℝ) 1, ‖f (a + q.1 * (b - a))‖ₑ) =
      ⨆ u ∈ Icc a b, ‖f u‖ₑ := by
  apply le_antisymm
  · apply iSup_le
    intro q
    have hmem : a + q.1 * (b - a) ∈ Icc a b :=
      ⟨by nlinarith [q.property.1], by nlinarith [q.property.2]⟩
    exact le_iSup₂_of_le (a + q.1 * (b - a)) hmem le_rfl
  · apply iSup₂_le
    intro u hu
    rcases hab.eq_or_lt with h | h
    · have hua : u = a := by grind
      subst b
      subst u
      exact le_iSup_of_le ⟨0, by norm_num⟩ (by simp)
    · let q : Icc (0 : ℝ) 1 := ⟨(u - a) / (b - a),
        ⟨div_nonneg (sub_nonneg.mpr hu.1) (sub_pos.mpr h).le,
          (div_le_one (sub_pos.mpr h)).mpr (sub_le_sub_right hu.2 a)⟩⟩
      apply le_iSup_of_le q
      have harg : a + q.1 * (b - a) = u := by
        dsimp only [q]
        rw [div_mul_cancel₀ _ (sub_pos.mpr h).ne']
        ring
      rw [harg]

end EmcsfAcExtension.Mixed
