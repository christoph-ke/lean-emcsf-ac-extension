module

public import EmcsfAcExtension.Frozen.IsSolution
public import EmcsfAcExtension.Frozen.Fields.EqOn
public import EmcsfAcExtension.Global.Api.Domains
import EmcsfAcExtension.Global.Calculus.Sections
import EmcsfAcExtension.Local.Api.EqOn
import EmcsfAcExtension.Infra.AC.Quotient

/-! # Terminal variation from the continued solution class

internal project record (internal project record) obtains the three exact terminal
variation clauses of `charged_SF_new_version.tex:L4194`–L4196 from the frozen class on
the continuation. The closed terminal segment is now a compact section.
No complete-cone input or local-existence statement is assumed here.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

/-- Ordinary scalar, normalized incoming scalar, and logarithmic expansion
have finite variation on every compact incoming section of a solution.
The positive lower expansion bound is derived on this very section. -/
theorem incoming_variation_of_solution {e a b v : ℝ} {S : Fields}
    {D : Set (ℝ × ℝ)} (hS : IsSolution e S D) (hab : a ≤ b)
    (hs : inSeg a b v ⊆ D) :
    eVariationOn (fun u => S.phi u v) (Icc a b) < ⊤ ∧
    eVariationOn (fun u => S.b u v) (Icc a b) < ⊤ ∧
    eVariationOn (fun u => Real.log (-S.nu u v)) (Icc a b) < ⊤ := by
  have hp := (hS.ac_in a b v hab hs).2.2.2.boundedVariationOn
  rw [uIcc_of_le hab] at hp
  have hbvs := Calculus.bv_in_section hS hs
  have cn := (Calculus.continuousOn_in_section hS.cont_nu hs).neg
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) cn
  have hpos : 0 < -S.nu x v := neg_pos.mpr (hS.nu_neg (x, v) (hs ⟨hx.1, hx.2, rfl⟩))
  have hlog := hbvs.2.1.neg.log_of_pos_le hpos hmin
  exact ⟨hp.lt_top, hbvs.2.2.2.lt_top, hlog.lt_top⟩

private theorem terminal_segment_subset {ui us vp : ℝ} (hus : us < 0) (hvp : 0 < vp) :
    inSeg ui 0 0 ⊆ origDomain ui ∪ triangle us vp := by
  rintro ⟨u, v⟩ ⟨hu, hu0, rfl⟩
  rcases hu0.eq_or_lt with rfl | hu0
  · exact Or.inr ⟨hus.le, le_rfl, hvp.le⟩
  · exact Or.inl ⟨hu, hu0, hu0.le, le_rfl⟩

/-- All three exact frozen terminal-TV clauses follow from the existential
conclusion of regular-center continuation. This internal project record helper is untagged:
internal project record must still discharge the cone input of the continuation producer. -/
theorem terminal_variation_of_continuation (ui e : ℝ) (S : Fields)
    (hcont : ∃ us vp : ℝ, ∃ S' : Fields, ui < us ∧ us < 0 ∧ 0 < vp ∧
      IsSolution e S' (origDomain ui ∪ triangle us vp) ∧
      (∀ t ∈ Icc us vp, S'.A t t = 0) ∧ S'.EqOn S (origDomain ui)) :
    eVariationOn (fun u => S.phi u 0) (Ico ui 0) < ⊤ ∧
    eVariationOn (fun u => S.b u 0) (Ico ui 0) < ⊤ ∧
    eVariationOn (fun u => Real.log (-S.nu u 0)) (Ico ui 0) < ⊤ := by
  obtain ⟨us, vp, S', hi, hus, hvp, hS', _, heq⟩ := hcont
  obtain ⟨hp, hb, hn⟩ := incoming_variation_of_solution hS' (hi.trans hus).le
    (terminal_segment_subset hus hvp)
  have mem (u : ℝ) (hu : u ∈ Ico ui 0) : (u, 0) ∈ origDomain ui :=
    ⟨hu.1, hu.2, hu.2.le, le_rfl⟩
  have ep : eVariationOn (fun u => S.phi u 0) (Ico ui 0) =
      eVariationOn (fun u => S'.phi u 0) (Ico ui 0) :=
    eVariationOn.eq_of_eqOn (fun u hu => (heq.phi (mem u hu)).symm)
  have eb : eVariationOn (fun u => S.b u 0) (Ico ui 0) =
      eVariationOn (fun u => S'.b u 0) (Ico ui 0) :=
    eVariationOn.eq_of_eqOn (fun u hu => (heq.b (mem u hu)).symm)
  have en : eVariationOn (fun u => Real.log (-S.nu u 0)) (Ico ui 0) =
      eVariationOn (fun u => Real.log (-S'.nu u 0)) (Ico ui 0) :=
    eVariationOn.eq_of_eqOn (fun u hu => by rw [heq.nu (mem u hu)])
  rw [ep, eb, en]
  exact ⟨(eVariationOn.mono _ Ico_subset_Icc_self).trans_lt hp,
    (eVariationOn.mono _ Ico_subset_Icc_self).trans_lt hb,
    (eVariationOn.mono _ Ico_subset_Icc_self).trans_lt hn⟩

end EmcsfAcExtension.Global.Closure
