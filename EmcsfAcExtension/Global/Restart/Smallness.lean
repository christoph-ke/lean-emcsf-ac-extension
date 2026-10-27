module

public import EmcsfAcExtension.Global.Defs.Relabel
public import EmcsfAcExtension.Local.Defs.Params
import EmcsfAcExtension.Global.Restart.Prolongation

/-! # The two frozen restart thresholds

The cone estimate is `eq:cc-complete-cone` (`charged_SF_new_version.tex:L4129`–L4131).
This arithmetic interface consumes its arbitrarily small complete-cone output.
The enlargement is exactly Δ = L and the canonical scalar bound retains 10.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Restart

/-- [internal]
A normalized complete cone meeting the two thresholds supplies the prolonged
AC datum at length `2 * L`. The thresholds are arbitrary positive local-theorem
witnesses; no new estimate constant is selected. -/
theorem restart_smallness_of_cone (e ε δ L : ℝ) (h : ℝ → ℂ)
    (hε : 0 < ε) (hL : 0 < L)
    (hac : AbsolutelyContinuousOnInterval h 0 L)
    (hvar : eVariationOn h (Icc 0 L) ≤ ENNReal.ofReal ε)
    (hscale : |e| * L * (1 + ‖h 0‖ + 10 * (eVariationOn h (Icc 0 L)).toReal) ≤ δ) :
    AbsolutelyContinuousOnInterval (extendDatum h L) 0 (2 * L) ∧
      datumVar (extendDatum h L) (2 * L) ≤ ε ∧
      Local.chargedScale e (extendDatum h L) (2 * L) ≤ δ := by
  have hlen : L + L = 2 * L := by ring
  have hv : datumVar (extendDatum h L) (2 * L) =
      (eVariationOn h (Icc 0 L)).toReal := by
    rw [← hlen, datumVar_extendDatum h L L hL ⟨hL, le_rfl⟩ hac]
    rfl
  refine ⟨by simpa only [hlen] using
    (constant_prolongation h L L hL ⟨hL, le_rfl⟩ hac).1, ?_, ?_⟩
  · rw [hv]
    exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar)
      ENNReal.ofReal_ne_top).2 hvar |>.trans_eq (ENNReal.toReal_ofReal hε.le)
  · simpa only [Local.chargedScale, Local.datumM, hv,
      extendDatum_eq_of_le h hL.le, mul_div_cancel_left₀ L (by norm_num : (2 : ℝ) ≠ 0)]
      using hscale

end EmcsfAcExtension.Global.Restart
