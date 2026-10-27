module

public import EmcsfAcExtension.Local.Defs.Setting
import EmcsfAcExtension.Local.Calculus.RelativeCharge
import EmcsfAcExtension.Local.Calculus.C1ToSolution2

/-! # Individual charge bound in the stability box

The oscillatory Maxwell primitive gives the radius squared weight
with no coupling smallness condition.
-/

public section

open Set

namespace EmcsfAcExtension.Local

/-- The individual charge divided by radius squared is at most
`|e|Mε`, with universal coefficient `1`, before all parameters and the
solution. The underlying primitive has the sharper coefficient `1/2`. -/
theorem stab_charge_ratio_le
    {e T ε M A : ℝ} {S : Fields} {h : ℝ → ℂ}
    (hset : StabSetting e T ε M A S h)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvT : v ≤ T) :
    |S.Q u v| / S.r u v ^ 2 ≤ |e| * M * ε := by
  have hseg : outSeg u u v ⊆ triangle 0 T := by
    rintro ⟨a, b⟩ ⟨rfl, hs⟩
    exact ⟨hu, hs.1, hs.2.trans hvT⟩
  have hb := Stab.oscillatory_charge_bound (hset.c1.toIsSolution hset.pos) huv.le hseg
    (fun s hs => (hset.box.2 (u, s) ⟨hu, hs.1, hs.2.trans hvT⟩).2.2.2.2.2.2)
    (fun s hs => (le_add_of_nonneg_right (norm_nonneg (S.xi u s / (S.nu u s : ℂ)))).trans
      (hset.box.2 (u, s) ⟨hu, hs.1, hs.2.trans hvT⟩).2.2.2.2.2.1)
  have hr := hset.c1.r_pos (u, v) ⟨hu, huv.le, hvT⟩ huv
  rw [div_le_iff₀ (sq_pos_of_pos hr)]
  nlinarith only [hb, abs_nonneg (S.Q u v)]

end EmcsfAcExtension.Local
