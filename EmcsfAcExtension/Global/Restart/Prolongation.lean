module

public import EmcsfAcExtension.Global.Defs.Relabel
public import EmcsfAcExtension.Frozen.DatumVar
import EmcsfAcExtension.Infra.AC.Relabel

/-! # Constant prolongation of the normalized cone datum

Only the datum is prolonged. The outgoing constraint reconstruction is explicitly
unconsumed in the graph record for `sec:charged-closure#prolong-cone`.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Restart

/-- [internal] Constant prolongation agrees with the original datum before the join. -/
theorem extendDatum_eq_of_le (h : ℝ → ℂ) {L t : ℝ} (ht : t ≤ L) :
    extendDatum h L t = h t := by
  simp [extendDatum, min_eq_left ht]

/-- [node sec:charged-closure#prolong-cone]
Constant prolongation preserves AC and exactly preserves variation
(`charged_SF_new_version.tex:L4181`–L4184). The constraint-reconstruction clause of the
source record is unconsumed. No estimate constant is introduced. -/
theorem constant_prolongation (h : ℝ → ℂ) (L Δ : ℝ) (hL : 0 < L)
    (hΔ : 0 < Δ ∧ Δ ≤ L) (hac : AbsolutelyContinuousOnInterval h 0 L) :
    AbsolutelyContinuousOnInterval (extendDatum h L) 0 (L + Δ) ∧
      eVariationOn (extendDatum h L) (Icc 0 (L + Δ)) = eVariationOn h (Icc 0 L) := by
  have hlabel : LipschitzWith 1 (fun t : ℝ => min t L) := LipschitzWith.id.min_const L
  have hmono : Monotone (fun t : ℝ => min t L) := fun _ _ hst => min_le_min_right L hst
  have hzero : min (0 : ℝ) L = 0 := min_eq_left hL.le
  have hend : min (L + Δ) L = L := min_eq_right (by linarith only [hΔ.1])
  have hlen : (0 : ℝ) ≤ L + Δ := by linarith only [hL, hΔ.1]
  have haclabel : AbsolutelyContinuousOnInterval (fun t : ℝ => min t L) 0 (L + Δ) :=
    hlabel.lipschitzOnWith.absolutelyContinuousOnInterval
  have hmap : MapsTo (fun t : ℝ => min t L) (uIcc 0 (L + Δ)) (uIcc 0 L) := by
    rw [uIcc_of_le hlen, uIcc_of_le hL.le]
    intro t ht
    exact ⟨le_min ht.1 hL.le, min_le_right _ _⟩
  have haccomp := hac.comp_monotoneOn_mapsTo haclabel (hmono.monotoneOn _) hmap
  have himage : (fun t : ℝ => min t L) '' Icc 0 (L + Δ) = Icc 0 L := by
    rw [hlabel.continuous.continuousOn.image_Icc_of_monotoneOn hlen (hmono.monotoneOn _),
      hzero, hend]
  have hvar := eVariationOn.comp_Icc_eq_of_monotoneOn h (hmono.monotoneOn _) himage
  have heq : (h ∘ fun t : ℝ => min t L) = extendDatum h L := rfl
  rw [← heq]
  exact ⟨haccomp, hvar⟩

/-- [internal] The frozen datum variation is unchanged by constant prolongation. -/
theorem datumVar_extendDatum (h : ℝ → ℂ) (L Δ : ℝ) (hL : 0 < L)
    (hΔ : 0 < Δ ∧ Δ ≤ L) (hac : AbsolutelyContinuousOnInterval h 0 L) :
    datumVar (extendDatum h L) (L + Δ) = datumVar h L := by
  simp only [datumVar, (constant_prolongation h L Δ hL hΔ hac).2]

end EmcsfAcExtension.Global.Restart
