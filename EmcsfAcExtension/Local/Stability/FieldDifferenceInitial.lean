module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Stability.MomentsSections
import EmcsfAcExtension.Infra.AC.Variation

/-! # Datum difference on the common initial cone

Classical normalized scalar traces make the literal datum absolutely
continuous. Its finite variation therefore controls every initial
value by the exact distance appearing in the architecture.
-/

public section

open Set MeasureTheory

namespace EmcsfAcExtension.Local

/-- The literal initial datum is AC as the restriction of the
classical normalized scalar. This exact regularity fact has no
constant, smallness hypothesis or derivative bound. -/
theorem stab_initial_datum_ac
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h) :
    AbsolutelyContinuousOnInterval h 0 T := by
  have ha : AbsolutelyContinuousOnInterval (S.a 0) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le hset.pos.le]
    exact (stab_normalized_out_c1 hset.c1).comp
      (contDiffOn_const.prodMk contDiffOn_id)
      (fun v hv => ⟨le_rfl, hv.1, hv.2⟩)
  apply ha.congr
  intro v hv
  rw [uIcc_of_le hset.pos.le] at hv
  exact (hset.data.1 v hv).2

/-- Every initial datum difference is bounded by the vertex
difference plus its finite total variation, with universal constant
`1`. This uses the literal `dataDist` without replacing its norm. -/
theorem stab_initial_data_difference_le
    {e T ε M A : ℝ} {S₁ S₂ : Fields} {h₁ h₂ : ℝ → ℂ}
    (h₁s : StabSetting e T ε M A S₁ h₁)
    (h₂s : StabSetting e T ε M A S₂ h₂)
    {v : ℝ} (hv : v ∈ Icc 0 T) : ‖h₁ v - h₂ v‖ ≤ dataDist h₁ h₂ T := by
  have hBV := ((stab_initial_datum_ac h₁s).sub
    (stab_initial_datum_ac h₂s)).boundedVariationOn_Icc h₁s.pos.le
  have hd := hBV.dist_le hv (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, h₁s.pos.le⟩)
  have htriangle : ‖h₁ v - h₂ v‖ ≤
      ‖(h₁ v - h₂ v) - (h₁ 0 - h₂ 0)‖ + ‖h₁ 0 - h₂ 0‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      ((h₁ v - h₂ v) - (h₁ 0 - h₂ 0)) (h₁ 0 - h₂ 0)
  have hd' : ‖(h₁ v - h₂ v) - (h₁ 0 - h₂ 0)‖ ≤ datumVar (h₁ - h₂) T := by
    simpa only [dist_eq_norm, Pi.sub_apply, datumVar] using! hd
  dsimp only [dataDist]
  linarith only [htriangle, hd']

end EmcsfAcExtension.Local
