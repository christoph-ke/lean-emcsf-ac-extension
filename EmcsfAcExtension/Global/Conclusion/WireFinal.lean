module

public import EmcsfAcExtension.Global.Assembly.Inputs
import EmcsfAcExtension.Global.Closure.WireContinuation
import EmcsfAcExtension.Global.Conclusion.TerminalTV
import EmcsfAcExtension.Global.Conclusion.WireCompactAxis
import EmcsfAcExtension.Local.Api.Mono
import EmcsfAcExtension.Local.Api.EqOn

/-! # Final internal project record estimates conditional only on closure

The exact terminal-TV and uniform positive-exponent clauses are obtained from
the continued frozen class. The latter uses the single compact triangle
`triangle ui 0`, as specified by the internal project record route, without a ray split.
Source: charged_SF_new_version.tex:L4194–4215; approved internal project record.
-/

public section

open Set MeasureTheory
open scoped ENNReal

namespace EmcsfAcExtension.Global.Closure

/-- [internal]
Conditional export of the three frozen terminal-TV clauses for
`sec:charged-closure#terminal-variation` through its internal project record continuation-class
route. Source: charged_SF_new_version.tex:L4194–4196, approved internal project record:L118–139.
There is no additional estimate constant or continuation premise. -/
theorem terminal_variation_of_closure (h : ClosureObligations)
    (ui e : ℝ) (S : Fields) (hold : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) :
    eVariationOn (fun u => S.phi u 0) (Ico ui 0) < ⊤ ∧
    eVariationOn (fun u => S.b u 0) (Ico ui 0) < ⊤ ∧
    eVariationOn (fun u => Real.log (-S.nu u 0)) (Ico ui 0) < ⊤ :=
  terminal_variation_of_continuation ui e S
    (regular_center_continuation_of_closure h ui e S hold hs)

/-- [internal]
The literal summed-TV graph conclusion of
`sec:charged-closure#terminal-variation#route-ga1-continuation-class`, hence
of `sec:charged-closure#terminal-variation`, from source hypotheses and closure.
Source: charged_SF_new_version.tex:L4194–4196; approved internal project record:L118–139. -/
theorem terminal_variation_ga1_of_closure (h : ClosureObligations)
    (ui e : ℝ) (S : Fields) (hold : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) :
    eVariationOn (fun u => S.phi u 0) (Ico ui 0) +
      eVariationOn (fun u => S.b u 0) (Ico ui 0) +
      eVariationOn (fun u => Real.log (-S.nu u 0)) (Ico ui 0) < ⊤ := by
  obtain ⟨hp, hb, hn⟩ := terminal_variation_of_closure h ui e S hold hs
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hp, hb⟩, hn⟩

/-- [internal]
Conditional export for `sec:charged-closure#uniform-positive-exponents` and
`sec:charged-closure#uniform-positive-exponents#route-ga1-compact-axis`.
One bound on the continued compact triangle precedes every varying ray;
it may depend on the fixed continuation. Only finiteness is asserted.
Source: charged_SF_new_version.tex:L4205–4215; approved internal project record:L144–155. -/
theorem uniform_positive_exponents_of_closure (h : ClosureObligations)
    (ui e : ℝ) (S : Fields) (hold : OriginalData ui e S)
    (hs : SignedTerminalBound ui S) :
    (⨆ v ∈ Ioo ui 0,
      ∫⁻ u in Ico ui v, ENNReal.ofReal (positiveExpIntegrand S u v)) < ⊤ := by
  obtain ⟨us, vp, S', _hi, hus, hvp, hS', _hg, heq⟩ :=
    regular_center_continuation_of_closure h ui e S hold hs
  have htri : IsSolution e S' (triangle ui 0) := Local.isSolution_mono hS' (by
    rintro ⟨u, v⟩ ⟨hu, huv, hv⟩
    rcases (huv.trans hv).eq_or_lt with hu0 | hu0
    · change u = 0 at hu0
      have hv0 : v = 0 := le_antisymm hv (hu0 ▸ huv)
      subst u
      subst v
      exact Or.inr ⟨hus.le, le_rfl, hvp.le⟩
    · exact Or.inl ⟨hu, hu0, huv, hv⟩)
  obtain ⟨ℓ, Λ, Φ, R, δ, _hℓ, _hδ, _hle, _hΛ, _hΦ, _hR, _hgap,
      hbound, _hsup, _hfinite⟩ :=
    (compact_axis_exponent (c := ui) (a := 0) (d := 0)
      htri hold.ui_neg.le le_rfl inter_subset_left).2.2
  apply lt_of_le_of_lt (b := ENNReal.ofReal
    (Real.log (Λ / ℓ) + e ^ 2 * Φ ^ 2 * R ^ 2 / (6 * δ ^ 2))) ?_
      ENNReal.ofReal_lt_top
  refine iSup_le fun v => iSup_le fun hv => ?_
  have he : (∫⁻ u in Ico ui v, ENNReal.ofReal (positiveExpIntegrand S u v)) =
      ∫⁻ u in Ico ui v, ENNReal.ofReal (positiveExpIntegrand S' u v) := by
    apply setLIntegral_congr_fun measurableSet_Ico
    intro u hu
    have hp : (u, v) ∈ origDomain ui :=
      ⟨hu.1, hu.2.trans hv.2, hu.2.le, hv.2.le⟩
    dsimp [positiveExpIntegrand]
    rw [heq.nu hp, heq.mu hp, heq.r hp]
  rw [he]
  exact hbound v ⟨hv.1.le, hv.2.le⟩ v
    ⟨hv.1.le, by simpa only [min_eq_right hv.2.le] using (le_rfl : v ≤ v)⟩

end EmcsfAcExtension.Global.Closure
