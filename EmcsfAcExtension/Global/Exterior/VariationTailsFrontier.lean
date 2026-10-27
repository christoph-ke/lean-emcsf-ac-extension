module

public import EmcsfAcExtension.Global.Exterior.VariationTailsTerminal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The complete frontier exit cost in one fixed representative

Proper estimates based at the fixed entry row give a finite complete
nonnegative exit integral. Absolute continuity of that L¹ integral gives
its vanishing terminal tail. The representative is anchored once at the
entry row; it does not vary with a truncation. Source:
`charged_SF_new_version.tex:L1342–L1355`, L1381–L1382; internal project record (D3).
-/

public section

open Set MeasureTheory Filter Topology
open scoped NNReal

namespace EmcsfAcExtension.Global.Exterior

/-- [internal]
Uniformly bounded nonnegative proper integrals yield a finite complete
integral and vanishing tails. The bound precedes every truncation. -/
theorem integrable_terminal_of_nonneg_proper_bound {f : ℝ → ℝ} {c B : ℝ}
    (hc : c < 0) (hi : ∀ b ∈ Ico c 0, IntervalIntegrable f volume c b)
    (hn : ∀ᵐ u ∂volume.restrict (Ico c 0), 0 ≤ f u)
    (hB : ∀ b ∈ Ico c 0, (∫ u in c..b, f u) ≤ B) :
    IntegrableOn f (Ico c 0) ∧
      Tendsto (fun a => ∫ u in a..0, f u) (𝓝[<] 0) (𝓝 0) := by
  obtain ⟨z, hzmono, hzmem, hzt⟩ := exists_seq_strictMono_tendsto' hc
  have hcover : AECover (volume.restrict (Ico c 0)) atTop (fun n => Icc c (z n)) :=
    aecover_Ico_of_Icc tendsto_const_nhds hzt
  have hsub (n : ℕ) : Icc c (z n) ⊆ Ico c 0 :=
    fun u hu => ⟨hu.1, hu.2.trans_lt (hzmem n).2⟩
  have hfi (n : ℕ) : IntegrableOn f (Icc c (z n)) (volume.restrict (Ico c 0)) := by
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Icc,
      inter_eq_left.mpr (hsub n)]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (hzmem n).1.le).1
      (hi (z n) ⟨(hzmem n).1.le, (hzmem n).2⟩)
  have hbounded (n : ℕ) : (∫ u in Icc c (z n), f u ∂volume.restrict (Ico c 0)) ≤ B := by
    rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr (hsub n),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hzmem n).1.le]
    exact hB (z n) ⟨(hzmem n).1.le, (hzmem n).2⟩
  have hfull := hcover.integrable_of_integral_bounded_of_nonneg_ae B hfi hn
    (Eventually.of_forall hbounded)
  exact ⟨hfull, time_integral_tail_tendsto hc
    ((intervalIntegrable_iff_integrableOn_Ico_of_le hc.le).2 hfull)⟩

/-- [internal]
The frontier exit density based at the single row `c` is L¹ on the
complete late frontier and has a vanishing tail. The entry bound is
uniform in proper truncations; local inverse constants are derived only
on their corresponding proper intervals. -/
theorem frontier_exit_integrable_of_uniform_proper_bound
    {ui e c B : ℝ} {S : Fields} {t : ℝ → ℝ}
    (hS : IsSolution e S (origDomain ui)) (hc : c < 0)
    (hmem : ∀ u ∈ Ico c 0, (u, t u) ∈ origDomain ui)
    (hproper : ∀ u ∈ Ico c 0, u < t u)
    (hm : StrictMonoOn t (Ico c 0))
    (hsegments : ∀ b ∈ Ico c 0, ∃ K L : ℝ≥0,
      LipschitzOnWith K t (uIcc c b) ∧
        AntilipschitzWith L ((uIcc c b).domRestrict t))
    (hB : ∀ b ∈ Ico c 0,
      (∫ u in c..b, deriv t u * ‖densityRepresentative e S c u (t u)‖) ≤ B) :
    IntegrableOn (fun u => deriv t u * ‖densityRepresentative e S c u (t u)‖) (Ico c 0) ∧
      Tendsto (fun a => ∫ u in a..0, deriv t u * ‖densityRepresentative e S c u (t u)‖)
        (𝓝[<] 0) (𝓝 0) := by
  apply integrable_terminal_of_nonneg_proper_bound hc ?_ ?_ hB
  · intro b hb
    obtain ⟨K, L, hL, hA⟩ := hsegments b hb
    have hsub : Icc c b ⊆ Ico c 0 := fun u hu => ⟨hu.1, hu.2.trans_lt hb.2⟩
    have htc : ContinuousOn t (Icc c b) := by
      simpa only [uIcc_of_le hb.1] using hL.continuousOn
    have hs := hm.mono hsub
    obtain ⟨τ, hτ, hτm, hτinv, hτexit, hτK⟩ := exists_variation_swept_exit hb.1 htc hs
    have htb : t b ≤ 0 := (hmem b hb).2.2.2
    exact (swept_density_boundary_norm_eq_exit hS hb.1 hL
      (by simpa only [uIcc_of_le hb.1] using hs.monotoneOn) hA
      (by simpa only [uIcc_of_le hb.1] using fun u hu => hmem u (hsub hu))
      (by simpa only [uIcc_of_le hb.1] using fun u hu => hproper u (hsub hu)) hτ.measurable
      (fun v hv => hτK v ⟨hv.1, hv.2.trans htb⟩)
      (by simpa only [uIcc_of_le hb.1] using hτinv)).1
  · rw [restrict_Ico_eq_restrict_Icc, ← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hn : 0 ≤ deriv t u := by
      rw [← derivWithin_of_mem_nhds
        (mem_of_superset (Ioo_mem_nhds hu.1 hu.2) Ioo_subset_Ico_self)]
      exact hm.monotoneOn.derivWithin_nonneg
    exact mul_nonneg hn (norm_nonneg _)

/-- [internal]
The complete exit integral is finite for the actual adaptive frontier,
and its terminal tail vanishes in the single representative anchored at
the fixed entry row. All source, geometry and variation inputs are
discharged from the approved terminal adaptive outputs. Constants may
depend on the fixed data and profile, uniformly in terminal truncations. -/
theorem frontier_exit_tail_of_terminal {ui e C k₀ R₀ : ℝ} {S : Fields}
    (h : OriginalData ui e S) (M ell : ℝ → ℝ) (hR : 0 < R₀) (hC : 0 < C)
    (hk₀ : 0 < k₀ ∧ k₀ < 1 / 8)
    (hLip : LipschitzOnWith (Real.toNNReal k₀) ell (Ioc 0 R₀))
    (hMc : ContinuousOn M (Ioc 0 R₀)) (hM : ∀ R ∈ Ioc 0 R₀, 0 ≤ M R)
    (hAfinite : (∫⁻ R in Ioc 0 R₀, ENNReal.ofReal (M R / ell R ^ 2)) < ⊤)
    (hcollapse : Tendsto (fun u => S.r u 0) (𝓝[<] 0) (𝓝 0))
    (hmass : ∀ u ∈ Ico ui 0, M (S.r u 0) = S.m u 0)
    (hell : ∀ R ∈ Ioc 0 R₀, 0 < ell R)
    (hellsmall : Tendsto (fun R => ell R / R) (𝓝[>] 0) (𝓝 0))
    (hsmall : Tendsto (fun R => M R / ell R) (𝓝[>] 0) (𝓝 0))
    (hphi : ∀ u ∈ Ico ui 0, ‖S.phi u 0‖ ≤
      C * (1 + Real.sqrt (Real.log (S.r ui 0 / S.r u 0)))) :
    ∃ c ∈ Ioo ui 0, ∃ t : ℝ → ℝ,
      (∀ u ∈ Ico c 0, u < t u ∧ t u < 0 ∧ S.r u (t u) = ell (S.r u 0)) ∧
      IntegrableOn (fun u => deriv t u * ‖densityRepresentative e S c u (t u)‖) (Ico c 0) ∧
      Tendsto (fun a => ∫ u in a..0, deriv t u * ‖densityRepresentative e S c u (t u)‖)
        (𝓝[<] 0) (𝓝 0) := by
  obtain ⟨c, hc, t, E, hroot, hm, htt, hV, hF, hsegments, hE, hexit⟩ :=
    variation_and_boundary_exit_tails_of_terminal h M ell hR hC hk₀ hLip hMc hM hAfinite
      hcollapse hmass hell hellsmall hsmall hphi
  refine ⟨c, hc, t, hroot, ?_⟩
  apply frontier_exit_integrable_of_uniform_proper_bound h.solution hc.2
    (fun u hu => ⟨hc.1.le.trans hu.1, hu.2, (hroot u hu).1.le, (hroot u hu).2.1.le⟩)
    (fun u hu => (hroot u hu).1) hm (fun b hb => hsegments c b le_rfl hb.1 hb.2)
  · intro b hb
    obtain ⟨K, L, hL, hA⟩ := hsegments c b le_rfl hb.1 hb.2
    apply hexit c b t K L le_rfl hb.1 hb.2 hL
      (by
        rw [uIcc_of_le hb.1]
        exact hm.monotoneOn.mono (fun u hu => ⟨hu.1, hu.2.trans_lt hb.2⟩)) hA
    exact fun u hu => ⟨le_rfl, (hroot u ⟨hu.1, hu.2.trans_lt hb.2⟩).2.1.le⟩

end EmcsfAcExtension.Global.Exterior
