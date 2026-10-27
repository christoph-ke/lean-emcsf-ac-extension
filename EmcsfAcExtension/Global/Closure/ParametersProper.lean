module

public import EmcsfAcExtension.Global.Closure.Entry
import EmcsfAcExtension.Global.Exterior.OpticsFrontier
import EmcsfAcExtension.Global.Terminal.OpticalUpper
import EmcsfAcExtension.Global.Gap.Application
import EmcsfAcExtension.Local.Api.Mono

/-! # Fixed stopping bounds on one proper entry family

The common family from `cc_entry` retains its proper roots and all entry
limits when the weak stopping bounds are fixed. The terminal radius image
also gives proper radius bounds and the radius-variable tail limit.
Source: charged_SF_new_version.tex:L3854–L3886 and approved internal project record.
-/

public section

open Set Filter Topology MeasureTheory

namespace EmcsfAcExtension.Global.Closure

private theorem terminal_radius_tail_image {ui e a : ℝ} {S : Fields}
    (h : OriginalData ui e S) (ha : a ∈ Ico ui 0) :
    (fun u => S.r u 0) '' Ioo a 0 = Ioo 0 (S.r a 0) := by
  have hsub : origDomain a ⊆ origDomain ui := fun p hp => ⟨ha.1.trans hp.1, hp.2⟩
  exact Terminal.terminal_radius_image_Ioo ha.2 (Local.isSolution_mono h.solution hsub)
    (fun p hp => h.mu p (hsub hp))

private theorem eventually_radius_of_terminal {ui e : ℝ} {S : Fields}
    (h : OriginalData ui e S) (P : ℝ → Prop)
    (hP : ∀ᶠ u in 𝓝[<] (0 : ℝ), P (S.r u 0)) :
    ∀ᶠ R in 𝓝[>] (0 : ℝ), P R := by
  obtain ⟨b, hb, hPb⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hP
  obtain ⟨a, ha, ha0⟩ := exists_between (max_lt h.ui_neg hb)
  have hai : a ∈ Ico ui 0 := ⟨(le_max_left ui b).trans ha.le, ha0⟩
  have hR : 0 < S.r a 0 :=
    h.solution.r_pos (a, 0) ⟨hai.1, ha0, ha0.le, le_rfl⟩ ha0
  filter_upwards [Ioo_mem_nhdsGT hR] with R hR'
  rw [← terminal_radius_tail_image h hai] at hR'
  obtain ⟨u, hu, rfl⟩ := hR'
  exact hPb ⟨(le_max_right ui b).trans_lt (ha.trans hu.1), hu.2⟩

/-- [node sec:charged-closure#fixed-stopping-parameters]
Fix all weak stops on the same proper family as `cc_entry`, retaining its
root, radius tail, real interaction and normalized energy limits. The late
adaptive exterior has expansion strictly above `2c`. The profile, labels and
expansion constants may depend on the fixed development and signed bound;
`F, ε` and the late expansion cutoff may also depend on the two supplied fixed
positive thresholds. These choices precede every entry tolerance, entry row, shrinking
scale, connector ratio, stage count and duration (internal project record).
Source: charged_SF_new_version.tex:L3854–L3860, L3872–L3886. -/
theorem fixed_stopping_parameters_proper (ui e ηobs ηcool : ℝ) (S : Fields)
    (h : OriginalData ui e S) (hs : SignedTerminalBound ui S)
    (ho : 0 < ηobs) (hh : 0 < ηcool) :
    ∃ ell V : ℝ → ℝ, ∃ a ∈ Ioo ui 0, ∃ c Λ F ε : ℝ,
      0 < c ∧ 0 < Λ ∧ c ≤ Λ ∧ 0 < F ∧ 0 < ε ∧
      (∀ p ∈ origDomain ui, S.lam p.1 p.2 ≤ Λ) ∧
      (∀ u ∈ Ico a 0, u < V u ∧ V u < 0 ∧
        S.r u (V u) = ell (S.r u 0) ∧
        0 < ell (S.r u 0) ∧ ell (S.r u 0) < S.r u 0) ∧
      0 < S.r a 0 ∧
      (∀ R ∈ Ioo 0 (S.r a 0), 0 < ell R ∧ ell R < R) ∧
      Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0) ∧
      (∃ b ∈ Ioo a 0, ∀ p ∈ adaptiveExterior S ui b ell,
        2 * c < S.lam p.1 p.2) ∧
      (∀ ρ : ℝ, 0 < ρ ∧ ρ < 1 → ExteriorBox (gapConstant / 2) c Λ F ε ρ) ∧
      (∀ μ x : ℝ, 0 ≤ μ → μ < 1 → μ / (1 - μ) ≤ ε →
        x ≤ F → μ + x < ηobs ∧ μ + x < ηcool) ∧
      Tendsto (fun u => ∫ v in V u..0, ‖weightedJ S u v‖) (𝓝[<] 0) (𝓝 0) ∧
      (∀ εentry > 0, Tendsto (fun u => ell (S.r u 0) / (εentry * S.r u 0))
        (𝓝[<] 0) (𝓝 0)) ∧
      Tendsto (fun u => cylinderEnergy S (ell (S.r u 0)) u (V u) / ell (S.r u 0))
        (𝓝[<] 0) (𝓝 0) ∧
      ∀ Fentry > 0, ∀ εentry > 0, ∀ᶠ u in 𝓝[<] (0 : ℝ), ∀ v ∈ Icc (V u) 0,
        2 * c < S.lam u v ∧ S.lam u v ≤ Λ ∧
        ‖S.theta u v / (S.lam u v : ℂ)‖ < Fentry ∧
        S.mu u v / (1 - S.mu u v) < εentry := by
  obtain ⟨ell, V, a, ha, c, hc, Λ, hΛ, hcΛ, hupper, hroot, hD, hratio, henergy,
    hentry⟩ := cc_entry ui e S h hs
  have hδ : 0 < gapConstant / 2 ∧ gapConstant / 2 ≤ 1 :=
    ⟨half_pos LateGap.gapConstant_bounds.1,
      by linarith only [LateGap.gapConstant_bounds.2]⟩
  obtain ⟨F, ε, hF, hε, hbox, hweak⟩ :=
    weak_stopping_parameters (gapConstant / 2) c Λ ηobs ηcool hδ hc hcΛ ho hh
  have hproper (u : ℝ) (hu : u ∈ Ico a 0) :
      0 < ell (S.r u 0) ∧ ell (S.r u 0) < S.r u 0 := by
    obtain ⟨huV, hV0, hr⟩ := hroot u hu
    have hui : u ∈ Ico ui 0 := ⟨ha.1.le.trans hu.1, hu.2⟩
    rw [← hr]
    exact ⟨h.solution.r_pos (u, V u) ⟨hui.1, hui.2, huV.le, hV0.le⟩ huV,
      Exterior.outgoing_radius_strictMono h hui ⟨huV.le, hV0.le⟩
        ⟨hu.2.le, le_rfl⟩ hV0⟩
  have hradius : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0) := by
    apply Filter.tendsto_def.mpr
    intro s hs'
    apply eventually_radius_of_terminal h (fun R => ell R / R ∈ s)
    filter_upwards [(hratio 1 zero_lt_one).eventually_mem hs'] with u hu
    simpa only [one_mul] using hu
  obtain ⟨b, hb, hbound⟩ :=
    mem_nhdsLT_iff_exists_Ioo_subset.mp (hentry F hF ε hε)
  obtain ⟨d, hd, hd0⟩ := exists_between (max_lt ha.2 hb)
  refine ⟨ell, V, a, ha, c, Λ, F, ε, hc, hΛ, hcΛ, hF, hε, hupper,
    (fun u hu => ?_), ?_, ?_, hradius, ⟨d, ⟨lt_of_le_of_lt (le_max_left a b) hd, hd0⟩,
      ?_⟩, hbox, hweak, hD, hratio, henergy, hentry⟩
  · exact ⟨(hroot u hu).1, (hroot u hu).2.1, (hroot u hu).2.2, hproper u hu⟩
  · exact h.solution.r_pos (a, 0) ⟨ha.1.le, ha.2, ha.2.le, le_rfl⟩ ha.2
  · intro R hR
    rw [← terminal_radius_tail_image h ⟨ha.1.le, ha.2⟩] at hR
    obtain ⟨u, hu, rfl⟩ := hR
    exact hproper u ⟨hu.1.le, hu.2⟩
  · intro p hp
    have hu : p.1 ∈ Ico a 0 :=
      ⟨(le_max_left a b).trans (hd.le.trans hp.2.1), hp.1.2.1⟩
    have hv : V p.1 ≤ p.2 := by
      by_contra hv
      have hlt := Exterior.outgoing_radius_strictMono h
        ⟨hp.1.1, hp.1.2.1⟩ ⟨hp.1.2.2.1, hp.1.2.2.2⟩
        ⟨(hroot p.1 hu).1.le, (hroot p.1 hu).2.1.le⟩ (lt_of_not_ge hv)
      rw [(hroot p.1 hu).2.2] at hlt
      exact (not_lt_of_ge hp.2.2) hlt
    exact (hbound ⟨(le_max_right a b).trans_lt (hd.trans_le hp.2.1),
      hp.1.2.1⟩ p.2 ⟨hv, hp.1.2.2.2⟩).1

end EmcsfAcExtension.Global.Closure
