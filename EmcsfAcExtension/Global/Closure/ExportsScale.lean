module

public import EmcsfAcExtension.Global.Defs.Original
public import EmcsfAcExtension.Global.Defs.Interaction
public import EmcsfAcExtension.Global.Defs.Stages
public import EmcsfAcExtension.Global.Interaction.ClosuresScalar
import EmcsfAcExtension.Global.Closure.Windows
import Mathlib.Tactic

/-! # Canonical quantitative physical scale and eventual observation smallness

The central normalized scalar is bounded using the actual stopped profile
and the literal canonical background. Its charged comparison coefficient
is universal and distinct from the development-dependent logarithmic
amplitude coefficient in the eventual smallness statement.
Source: `charged_SF_new_version.tex:L4086–L4091`; internal project record.
-/

public section

open Set Filter Topology

namespace EmcsfAcExtension.Global.Closure

/-- [node sec:charged-closure#observation-physical-scale]
The canonical quantitative bounds and uniform eventual observation
smallness, with no scalar translation. The comparison coefficient `Cscale`
is universal (the proof gives `3`), chosen before the development, coupling,
stops, radius, stage count and duration. The separate logarithmic amplitude
coefficient `Camp` may depend on the fixed development and `c,F,Jstop`,
but precedes the tolerance and entry row. The scalar profile is produced
from actual finite stops, rather than assumed.
Source: charged_SF_new_version.tex:L4086–L4091. -/
theorem observation_physical_scale_complete :
    ∃ Cscale > 0, ∀ (ui e c F Jstop : ℝ) (S : Fields),
      OriginalData ui e S → SignedTerminalBound ui S →
      0 < c → 0 ≤ F → F < 1 → 0 ≤ Jstop →
      (∀ (a b v₀ ρ δ Λ ε : ℝ) (vb : ℝ → ℝ) (N : ℕ)
          (_B : FiniteBoundary S ui a b v₀ ρ vb N),
        ExteriorBox δ c Λ F ε ρ →
        ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F ε →
        (∀ u ∈ Icc a b, S.r a 0 / 2 ≤ S.r u 0) →
        (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal ≤ Jstop →
        ∀ u ∈ Icc a b, ∀ v ∈ Icc (vb u) 0, ∀ r ∈ Icc 0 (S.r a 0),
          ‖S.a u v‖ ≤ Interaction.scalarBackground ui (S.r a 0) c F Jstop S + F ∧
          |e| * r * (1 + ‖S.a u v‖) ≤
            Cscale * (|e| * Interaction.scalarBackground ui (S.r a 0) c F Jstop S *
              S.r a 0)) ∧
      (∃ Camp > 0, 1 ≤ Camp ∧ ∀ η > 0, ∀ᶠ a in 𝓝[<] (0 : ℝ),
        ∀ (b v₀ ρ δ Λ ε : ℝ) (vb : ℝ → ℝ) (N : ℕ)
          (_B : FiniteBoundary S ui a b v₀ ρ vb N),
        ExteriorStops S (exteriorDomain ui a b vb) δ c Λ F ε →
        (∀ u ∈ Icc a b, S.r a 0 / 2 ≤ S.r u 0) →
        (interactionNorm e S (exteriorDomain ui a b vb) a v₀).toReal ≤ Jstop →
        let M := Camp * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r a 0)))
        1 ≤ M ∧ ∀ u ∈ Icc a b, ∀ v ∈ Icc (vb u) 0, ∀ r ∈ Icc 0 (S.r a 0),
          ‖S.phi u v‖ ≤ M ∧ |e| * r * (1 + ‖S.a u v‖) < η) := by
  refine ⟨3, by norm_num, ?_⟩
  intro ui e c F Jstop S h hs hc hF hF1 hJstop
  refine ⟨?_, observation_physical_scale ui e c F Jstop S h hs hc hF hF1 hJstop⟩
  intro a b v₀ ρ δ Λ ε vb N B hbox hstop hhalf hJ
  have hab : a ≤ b := by
    simpa only [B.first, B.last] using B.ordered (Fin.zero_le (Fin.last N))
  have ha := B.mem a (left_mem_Icc.mpr hab)
  have hR : 0 < S.r a 0 := h.solution.r_pos (a, 0)
    ⟨ha.1, ha.2.1, ha.2.1.le, le_rfl⟩ ha.2.1
  have hsup : 0 ≤ Interaction.terminalScalarSup ui (S.r a 0) S :=
    (norm_nonneg _).trans (Interaction.terminal_scalar_le_sup h hR
      ⟨ha.1, ha.2.1⟩ ⟨half_le_self hR.le, le_rfl⟩)
  have hden : 0 < 1 - F ^ 2 := by
    nlinarith only [hF, hF1, sq_nonneg (F - 1)]
  have hterm : 0 ≤ (F + c⁻¹ * Jstop) / (1 - F ^ 2) :=
    div_nonneg (add_nonneg hF (mul_nonneg (inv_nonneg.mpr hc.le) hJstop)) hden.le
  have hM : 1 ≤ Interaction.scalarBackground ui (S.r a 0) c F Jstop S := by
    unfold Interaction.scalarBackground
    linarith only [hsup, hterm]
  have hprofile := stopped_radial_variation h B hbox hstop rfl hhalf hJ
  intro u hu v hv r hr
  have hp : (u, v) ∈ exteriorDomain ui a b vb :=
    ⟨⟨(B.mem u hu).1, (B.mem u hu).2.1,
      (B.off_axis u hu).le.trans hv.1, hv.2⟩, hu.1, hu.2, hv.1⟩
  exact observation_physical_scale_of_profile hr.1 hr.2 hM hF1.le
    ((hprofile u hu).2.2 v hv) (hstop (u, v) hp).2.2.2.2.1

end EmcsfAcExtension.Global.Closure
